/-
AdamW: weight decay inside Adam's rescaling, and outside it.

Adam divides each gradient by its own size. Put the pull of weight decay into
the gradient first and it is divided too: every weight then moves by the same
amount, whatever its size and whatever the strength of the decay. Apply the
decay after the rescaling (AdamW) and every weight shrinks at the same rate,
`1 - η μ` a step, as with plain weight decay.

As in `StepRules.lean`, this is one coordinate of Adam with no memory of
earlier steps.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `TAKE_ADAM_STEP_WITH_L2`, `TAKE_ADAMW_STEP`.

Theorems: `abs_adamL2Step_sub`, `adamL2Step_of_no_gradient`, `adamL2Step_mul`,
`adamWStep_eq`, `adamWStep_of_no_gradient`, `iterate_adamWStep_of_no_gradient`,
`adamWStep_mul`.
-/
import SquigglyLine.Supporting.Training.StepRules

namespace SquigglyLine

variable {η μ g θ c : ℝ}

/-- Adam with the decay inside the loss: the pull `μ θ` toward zero is added to the gradient
before Adam rescales it.
Python: `θ - η * TAKE_ADAM_STEP(g + μ * θ)`. -/
noncomputable def TAKE_ADAM_STEP_WITH_L2 (η μ g θ : ℝ) : ℝ :=
  θ - η * TAKE_ADAM_STEP (g + μ * θ)

/-- AdamW: Adam's step on the gradient alone, then the decay, not rescaled.
Python: `θ - η * TAKE_ADAM_STEP(g) - η * μ * θ`. -/
noncomputable def TAKE_ADAMW_STEP (η μ g θ : ℝ) : ℝ :=
  θ - η * TAKE_ADAM_STEP g - η * μ * θ

/-- **Inside Adam, the strength of the decay is rescaled away.** The weight moves by exactly
`η`, whatever `μ` is. -/
theorem abs_adamL2Step_sub (hη : 0 ≤ η) (h : g + μ * θ ≠ 0) :
    |TAKE_ADAM_STEP_WITH_L2 η μ g θ - θ| = η := by
  have h1 : |TAKE_ADAM_STEP (g + μ * θ)| = 1 := abs_adamStep h
  rw [TAKE_ADAM_STEP_WITH_L2, sub_sub_cancel_left, abs_neg, abs_mul, h1, mul_one,
    abs_of_nonneg hη]

/-- With no gradient from the loss, decay inside Adam moves every weight toward zero by the
same amount: a large weight and a small one both lose `η`. -/
theorem adamL2Step_of_no_gradient (hμ : 0 < μ) (η θ : ℝ) :
    TAKE_ADAM_STEP_WITH_L2 η μ 0 θ = θ - η * TAKE_ADAM_STEP θ := by
  have h : TAKE_ADAM_STEP (μ * θ) = TAKE_ADAM_STEP θ := adamStep_mul hμ θ
  rw [TAKE_ADAM_STEP_WITH_L2, zero_add, h]

/-- Inside Adam, making the loss `c` times larger is the same as making the decay `c` times
weaker. The decay has no strength of its own. -/
theorem adamL2Step_mul (hc : 0 < c) (η μ g θ : ℝ) :
    TAKE_ADAM_STEP_WITH_L2 η μ (c * g) θ = TAKE_ADAM_STEP_WITH_L2 η (μ / c) g θ := by
  have h : TAKE_ADAM_STEP (c * (g + μ / c * θ)) = TAKE_ADAM_STEP (g + μ / c * θ) :=
    adamStep_mul hc _
  have h2 : c * (g + μ / c * θ) = c * g + μ * θ := by
    field_simp
  rw [TAKE_ADAM_STEP_WITH_L2, TAKE_ADAM_STEP_WITH_L2, ← h, h2]

/-- **AdamW shrinks, then steps.** The decay is the factor `1 - η μ` on the weight, exactly as
in plain weight decay. -/
theorem adamWStep_eq (η μ g θ : ℝ) :
    TAKE_ADAMW_STEP η μ g θ = (1 - η * μ) * θ - η * TAKE_ADAM_STEP g := by
  rw [TAKE_ADAMW_STEP]
  ring

/-- With no gradient from the loss, AdamW shrinks every weight at the same rate. -/
theorem adamWStep_of_no_gradient (η μ θ : ℝ) :
    TAKE_ADAMW_STEP η μ 0 θ = (1 - η * μ) * θ := by
  have h0 : TAKE_ADAM_STEP 0 = 0 := by simp [TAKE_ADAM_STEP]
  rw [adamWStep_eq, h0]
  ring

/-- After `n` such steps a weight is `(1 - η μ) ^ n` of what it was. -/
theorem iterate_adamWStep_of_no_gradient (η μ θ : ℝ) (n : ℕ) :
    (TAKE_ADAMW_STEP η μ 0)^[n] θ = (1 - η * μ) ^ n * θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, adamWStep_of_no_gradient]
    ring

/-- AdamW does not care how large the loss is: its decay keeps its strength. -/
theorem adamWStep_mul (hc : 0 < c) (η μ g θ : ℝ) :
    TAKE_ADAMW_STEP η μ (c * g) θ = TAKE_ADAMW_STEP η μ g θ := by
  have h : TAKE_ADAM_STEP (c * g) = TAKE_ADAM_STEP g := adamStep_mul hc g
  rw [TAKE_ADAMW_STEP, TAKE_ADAMW_STEP, h]

end SquigglyLine
