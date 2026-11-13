# Porting a proof to the project style

This is the standing brief for a helper that ports Lean files written in
typical Mathlib style to the style of this project. The message that starts
you gives only what changes from one job to the next: your list of files, in
order, and the finished files they build on. Everything else is here.

The proofs already work. This is a restyle. Only names and layout change.
The mathematics must not change at all.

## Read first, and only these

1. [`STYLE.md`](STYLE.md): the rules.
2. [`SquigglyLine/Theorem/Sandwich.lean`](SquigglyLine/Theorem/Sandwich.lean):
   a finished lemma file to copy the look from.
3. The finished files named in your message. Your files build on them, so
   reuse their names and type aliases.

## What to do in each file

- **Names.** Rename every local name (binders, hypotheses, `variable`s,
  names inside proofs, `have`s) to descriptive `snake_case`, and type
  variables to `PascalCase`. Use the glossary in `STYLE.md`. No single
  letters and no Greek. `i`, `j`, `k` are fine as indices of a sum.
- **Statements.** Rewrite every theorem statement and definition signature:
  one binder per line; each quantity a `let` on its own line; each side of
  ∧ / ∨ / ↔ and the hypothesis of a → gets a named `let`; the last line only
  combines names. One-line lemmas too.
- **Types.** When a nested type shows in a signature, reuse an existing
  alias (`RealFunction`, `Model Inputs`, `SlopeLimit`, and those in the files
  you build on) or add an `abbrev` at the top of the file.
- **Comments.** Add a short trailing comment on a line whose formula or
  number would look like magic, saying where it comes from. The draft may
  carry notes from the author on this; turn them into those comments. Skip
  obvious lines: about half the lines get none. Code stays within 80
  columns. A trailing comment may run to about 130.
- **Proofs.** Keep the tactics. A tactic proof of a statement that starts
  with `let`s begins with `unfold_named_pieces` (add `beta_reduce` after it
  if a `rw` then fails to match). Rename hypotheses in the proof to match.
  Add a plain-words comment above a step that carries the idea.
- **Docs in the file.** Keep the opening summary comment, updated to the new
  names, with a short list of the file's definitions and theorems. Every
  theorem and definition keeps a plain-words docstring. A definition's
  docstring ends with a one-line Python reading where it helps.

## Hard constraints

- Do NOT rename any theorem, lemma, definition, structure or namespace.
  Definitions already have their final names.
- Do NOT change binder order, binder kind `( )` / `{ }` / `[ ]`, or any
  hypothesis. Do not add, drop or reorder arguments or declarations.
- Do NOT change what a definition computes. Keep any proof term or lambda
  passed as an argument exactly as written: do not move it into a `let`.
  Leave a definition's body without `let`s when other files `rw` or `simp`
  with it.
- A new helper must be an `abbrev` with a verb-like `SCREAMING_SNAKE_CASE`
  name.
- No `sorry`. A misspelt name is an error. Write `PI`, never a bare `pi`.

## Building

- From the `lean` directory run only `lake build <your module>`, for
  example `lake build SquigglyLine.Networks.Lift`. Never a bare
  `lake build`, and never build a module that is not yours: other helpers
  are working on other files at the same time.
- A file of yours may fail at first because a file it imports was ported.
  Fix the use in your file.

Known pitfalls:

- `rw [lemma]` rejects an ↔ lemma whose statement is behind `let`s. Use
  `simp only [lemma]`, `(lemma ..).mp` / `.mpr`, or
  `rw [propext (lemma ..)]`.
- A lemma whose statement starts with `let`s works more reliably in `rw` and
  `linarith` through `have step : <plain statement> := lemma ..`.
- If a term-mode proof stops elaborating against a `let` statement, write
  `by unfold_named_pieces; exact ...`.
- A last line that starts with `-1` right after a `let` parses as a
  subtraction. Name the `-1` with a `let`.
- Naming part of an expression with its own `let` can make Lean fill in a
  hidden argument differently. If a statement mixes `∘L`, `adjoint` or
  coercions, keep the expression whole.

## To keep this cheap

- Do not write your own checking scripts and do not compare against git
  history. The author runs the statement check afterwards.
- Do not read files other than the ones named here and in your message.
- Do not commit, push or change anything with git. Do not edit the notes or
  the README.

## Record, then report

For each file, write `lean/port-log/<FileName>.txt` with: whether it built,
the full text of any build error you could not fix, and each place you
could not follow a rule and why. That folder is not committed.

Then reply in at most six lines: for each file, built or not, and whether
its log has anything the author must look at.
