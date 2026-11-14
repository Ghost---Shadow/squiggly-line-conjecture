# 2. How to read a proof here

**In the repository:**
[`STYLE.md`](../lean/STYLE.md),
[`Vocabulary.lean`](../lean/SquigglyLine/Theorem/Vocabulary.lean),
[`Style.lean`](../lean/SquigglyLine/Style.lean).
**You need:** chapter 1.

A Lean theorem has two halves. The **statement** says what is true. The
**proof** convinces the checker. To know what the repository claims, you
only need to read statements, and the statements here are written like
short Python scripts.

## A whole theorem, read line by line

This is the first theorem of chapter 3, copied from
[`Sandwich.lean`](../lean/SquigglyLine/Theorem/Sandwich.lean).

```lean
/-- The line is never further away than the vertical error. -/
theorem nearestDist_le_verticalDist
    (model : Model Inputs)
    (data_point : DataPoint Inputs) :
    let nearest_distance := GET_NEAREST_DISTANCE model data_point
    let vertical_error   := GET_VERTICAL_ERROR model data_point  -- straight up or down is one way to reach the line
    nearest_distance ≤ vertical_error := by
```

- `/-- ... -/` is the statement in plain words. Read this first.
- `theorem nearestDist_le_verticalDist` gives the theorem its name. Other
  proofs call it by that name, the way code calls a function.
- Each line in round brackets is a **given**: a name, a colon, and what
  kind of thing it is. Here we are given any model and any data point.
- Each `let` names one quantity. Nothing is claimed yet.
- The last line before `:= by` is the **claim**. It only combines names.
- A comment after `--` says why, where a line needs a reason.
- Everything after `:= by` is the proof. You may stop reading here.

Read aloud: *for any model and any data point, the nearest distance is at
most the vertical error.*

## The three kinds of names

| Looks like | It is | Example |
|---|---|---|
| `snake_case` | a local name: a given, or a quantity named by `let` | `data_point`, `slope_limit` |
| `SCREAMING_SNAKE_CASE` | a function or constant defined once for the whole project | `GET_NEAREST_DISTANCE`, `PI` |
| `PascalCase` | a type: a kind of thing | `Model`, `DataPoint`, `SlopeLimit` |

Functions are verbs. `GET_…` returns a value, `IS_…` and `HAS_…` answer yes
or no, `MAKE_…` and `DRAW_…` build something. Theorem names are older and
shorter (`nearestDist_le_verticalDist`); read them as labels.

## The symbols you will meet

| Symbol | Read it as | In Python |
|---|---|---|
| `f x` | `f` applied to `x` | `f(x)` |
| `fun x => ...` | the function that sends `x` to `...` | `lambda x: ...` |
| `∀ x, ...` | for every `x` | `all(... for x in ...)` |
| `∃ x, ...` | there is an `x` with | `any(... for x in ...)` |
| `A → B` | if `A` then `B` | |
| `A ∧ B`, `A ∨ B` | `A` and `B`; `A` or `B` | `and`, `or` |
| `ℝ`, `ℕ` | a real number; a counting number | `float`, `int` |
| `‖v‖` | the length of the vector `v` | `np.linalg.norm(v)` |
| `c • v` | the vector `v` scaled by `c` | `c * v` |
| `dist a b` | the distance from `a` to `b` | |
| `LipschitzWith K f` | `f` has slope at most `K` everywhere | |

Two kinds of brackets are safe to skim. Curly brackets `{...}` hold givens
that Lean works out by itself. Square brackets `[...]` hold fine print
about a type, such as "these vectors can be added and measured".

## If you do read a proof

The proofs are written as a list of named steps. Six words cover most of
them.

| In the proof | What it does |
|---|---|
| `unfold_named_pieces` | replaces every `let` name by what it stands for |
| `have name : claim := reason` | proves a small fact and gives it a name |
| `calc a ≤ b := ... _ ≤ c := ...` | a chain: `a ≤ b`, and `b ≤ c`, so `a ≤ c` |
| `rw [fact]` | rewrites the goal using an equation |
| `exact fact` | this fact is the goal; done |
| `linarith`, `nlinarith`, `ring`, `simp`, `positivity` | arithmetic the checker finishes by itself |

A good way to read a proof is to read only the names after `have`. They
are the outline of the argument.

## What the checker guarantees

- If the project builds, every theorem follows from its givens.
- The word `sorry` marks an unproved step. The build fails if it appears
  anywhere.
- A misspelt name is an error, not a new variable.

To run the checker yourself, install Lean and run `lake exe cache get` and
then `lake build` in the `lean` folder. Nothing in this book needs that.

## Check yourself

Here is a statement from chapter 15.

```lean
theorem one_le_slope_mul_dist_of_count
    {Inputs : Type*} [PseudoMetricSpace Inputs]
    {model : Model Inputs}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    {input other_input : Inputs}
    {count : ℝ}
    (model_at_input : model input = count)
    (model_at_other_input : model other_input = count + 1) :
    let count_jump           := (1 : ℝ)  -- from `count` to `count + 1`
    let slope_times_distance := slope_limit * dist input other_input
    count_jump ≤ slope_times_distance := by
```

1. What are the three givens in round brackets, in plain words?
2. What is claimed?
3. If the two inputs are 0.1 apart, how steep must the model be?

**Answers.** (1) The model has slope at most `slope_limit`; it says `count`
at one input; it says `count + 1` at another. (2) One is at most the slope
limit times the distance between the two inputs. (3) At least 10.

Previous: [1. Two distances](01-two-distances.md) · Next: [3. Slope](03-slope.md)
