/-
Fingerprint every theorem and definition of the project.

A restyle may change names and layout, never the mathematics. This tool
prints one line per declaration with a hash of its statement, computed after
removing everything a restyle is allowed to change:

* `let`s are substituted in, and the result is beta- and eta-reduced;
* binder names, binder kinds and the names of universe levels are ignored;
* the project's own abbreviations are unfolded;
* a renamed definition is mapped back to its old name (`RENAMES.txt`).

Run it before and after a restyle and compare the two outputs. A line that
differs is a statement whose mathematics changed.

    cd lean
    lake build
    lake env lean tools/StatementFingerprint.lean   # writes FINGERPRINT.txt

The rollout of the style in November 2026 was checked this way: every
declaration that existed before has the same fingerprint after, except
`GET_LABEL`, which was deliberately generalised from real inputs to any
input type.
-/
import SquigglyLine

open Lean Meta

/-- Definitions that are not `abbrev`s but only wrap a statement. -/
def alsoUnfold : List Name := [`SquigglyLine.HOLDS_FOR_EVERY_SINE]

def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `SquigglyLine
  | none => false

def shouldUnfold (env : Environment) (n : Name) : Bool :=
  alsoUnfold.contains n ||
    (isOurs env n && (getReducibilityStatusCore env n == .reducible ||
      (match n with | .str _ s => s.startsWith "_proof_" | _ => false)))

/-- Map a name back to its old form, also when a renamed definition is a prefix of it. -/
def mapBack (back : Std.HashMap Name Name) (n : Name) : Name :=
  match back.get? n with
  | some old => old
  | none =>
    match n with
    | .str p s => .str (mapBack back p) s
    | .num p k => .num (mapBack back p) k
    | .anonymous => .anonymous

partial def norm (env : Environment) (back : Std.HashMap Name Name) (e : Expr) : Expr :=
  match e with
  | .mdata _ b => norm env back b
  | .letE _ _ v b _ => norm env back (b.instantiate1 v)
  | .lam _ t b _ => (Expr.lam `x (norm env back t) (norm env back b) .default).eta
  | .forallE _ t b _ => .forallE `x (norm env back t) (norm env back b) .default
  | .proj s i b => .proj (mapBack back s) i (norm env back b)
  | .const .. | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n ls =>
      match (if shouldUnfold env n then env.find? n else none) with
      | some info =>
        match (match info with
            | .thmInfo t => some t.value | .defnInfo d => some d.value | _ => none) with
        | some v => norm env back ((v.instantiateLevelParams info.levelParams ls).beta args)
        | none => mkAppN (.const (mapBack back n) ls) (args.map (norm env back))
      | none => mkAppN (.const (mapBack back n) ls) (args.map (norm env back))
    | .lam .. => norm env back (f.beta args)
    | .letE .. | .mdata .. => norm env back (mkAppN (norm env back f) args)
    | _ =>
      let f' := norm env back f
      let e' := mkAppN f' (args.map (norm env back))
      if f'.isLambda then norm env back e'.headBeta else e'
  | other => other

def skipName (n : Name) : Bool :=
  let user := (privateToUserName? n).getD n
  match user with
  | .str _ s =>
    s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" ||
      s.startsWith "eq_" || s.startsWith "sizeOf" || s.startsWith "inj" ||
      s.startsWith "noConfusion" || s.startsWith "ctorIdx" || s == "rec" ||
      s == "recOn" || s == "casesOn" || s == "below" || s == "brecOn" ||
      s == "ext" || s == "ext_iff" || s.startsWith "congr_simp" ||
      user.isInternal
  | _ => true

def readRenames (path : System.FilePath) : IO (Std.HashMap Name Name) := do
  let mut back : Std.HashMap Name Name := {}
  if ← path.pathExists then
    for line in (← IO.FS.lines path) do
      match line.splitOn " " with
      | [old, new] =>
        back := back.insert (`SquigglyLine ++ new.toName) (`SquigglyLine ++ old.toName)
      | _ => pure ()
  return back

run_cmd do
  let env ← getEnv
  let back ← readRenames "RENAMES.txt"
  let mut lines : Array String := #[]
  for (n, info) in env.constants.toList do
    if !isOurs env n || skipName n then continue
    let name := mapBack back n
    -- Universe levels are named after the type variables, so give them fixed names.
    let canon := (List.range info.levelParams.length).map fun i => Level.param (Name.mkNum `u i)
    let fixLevels := fun (e : Expr) => e.instantiateLevelParams info.levelParams canon
    match info with
    | .thmInfo t =>
      lines := lines.push s!"theorem {name} {(norm env back (fixLevels t.type)).hash}"
    | .defnInfo d =>
      lines := lines.push
        s!"def {name} {(norm env back (fixLevels d.type)).hash} {(norm env back (fixLevels d.value)).hash}"
    | _ => pure ()
  IO.FS.writeFile "FINGERPRINT.txt" ("\n".intercalate (lines.qsort (· < ·)).toList ++ "\n")
  logInfo m!"{lines.size} declarations fingerprinted"
