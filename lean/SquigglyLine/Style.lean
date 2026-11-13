/-
Tools for writing a statement as a short script.

Every statement in this project names its pieces with `let`, one per line,
and ends with a line that only combines those names. `lean/STYLE.md` sets
out the rules. This file holds the two things every other file needs for it:

* `unfold_named_pieces`  a proof step that replaces each named piece of the
                         statement by what it stands for;
* `RealFunction`         the name for `ℝ → ℝ`;
* `PI`                   the circle constant.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Lean Elab Tactic Meta in
/-- Replace every named piece (`let`) of the goal by what it stands for.

A statement is written for the reader, with a name for each piece. A proof
works on the pieces themselves. This step goes from the one to the other,
and it is the first line of most proofs here. It changes nothing but the
layout: the goal before and after are the same statement.

    theorem double_is_bigger (amount : ℝ) (amount_nonneg : 0 ≤ amount) :
        let doubled := 2 * amount
        amount ≤ doubled := by
      unfold_named_pieces   -- the goal is now `amount ≤ 2 * amount`
      linarith
-/
elab "unfold_named_pieces" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let unfolded ← Core.transform target (pre := fun expression =>
    match expression with
    | .letE _ _ value body _ => return .visit (body.instantiate1 value)
    | _ => return .continue)
  replaceMainGoal [← goal.replaceTargetDefEq unfolded]

namespace SquigglyLine

/-- A function from real numbers to real numbers.
Python: `Callable[[float], float]`. -/
abbrev RealFunction := ℝ → ℝ

/-- The circle constant, 3.14159...
Python: `math.pi`. -/
noncomputable abbrev PI : ℝ := Real.pi

end SquigglyLine
