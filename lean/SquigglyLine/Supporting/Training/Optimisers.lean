/-
Optimisers: schedules, the condition number, momentum, and steps on part of
the data.

`SpectralBias.lean` shows that gradient descent multiplies the error in a
direction of strength `strength` by `1 - learning_rate * strength` at every
step. This file follows that one number through four common changes to the
step.

* **A schedule.** With a step size that changes, what is left of the error
  is the product of the factors `1 - learning_rates step * strength`. A factor
  is at most one in size exactly while `learning_rates step * strength` is
  between zero and two, which is what warmup protects.
* **The condition number.** With strengths between `weakest` and `strongest`,
  the step `2 / (weakest + strongest)` shrinks every direction by at least
  `(strongest - weakest) / (strongest + weakest)`, and the weakest direction
  by exactly that.
* **Momentum.** With momentum `momentum` the oscillation that never dies sits
  at `learning_rate * strength = 2 * (1 + momentum)`, not at
  `learning_rate * strength = 2`.
* **Steps on part of the data.** An average of steps, each on one client's or
  one example's gradient, is one step on the averaged gradient. That covers
  stochastic gradient descent on average, and federated averaging after one
  local step.

Definitions: `RUN_SCHEDULE`, `TAKE_MOMENTUM_STEP`.

Theorems:

* `runSchedule_eq`                 a schedule multiplies its factors;
* `abs_runSchedule_le`             while every factor is at most one in size,
                                   the error never grows;
* `one_lt_abs_one_sub`             a step that is too large makes the error
                                   grow (why warmup);
* `abs_one_sub_best_step_le`       the condition number sets the speed;
* `one_sub_best_step_at_weakest`   and the weakest direction hits that speed
                                   exactly;
* `momentumStep_of_no_momentum`    with no momentum it is the plain step;
* `momentumStep_alternating`       momentum moves the edge of stability;
* `iterate_momentumStep_alternating`  at that edge the flipping error never
                                   dies and never grows;
* `sum_smul_step_eq_step`          an average of steps is a step on the
                                   average;
* `mean_step_eq_step`              a step on a random example is the full step
                                   on average.
-/
import SquigglyLine.Supporting.Training.StepRules

namespace SquigglyLine

/-- One step size for each step of training.
Python: `list[float]`. -/
abbrev LearningRatePerStep := ℕ → ℝ

/-- The error now and the error one step ago, in one direction.
Python: `tuple[float, float]`. -/
abbrev MomentumState := ℝ × ℝ

/-- What is left of the error in a direction of strength `strength` after
`step_count` steps, when step number `step` has size `learning_rates step`.
Python: `for step in range(step_count):
error = (1 - learning_rates[step] * strength) * error`. -/
def RUN_SCHEDULE
    (learning_rates : LearningRatePerStep)
    (strength : ℝ) : ℕ → ℝ → ℝ
  | 0, error => error
  | step_count + 1, error =>
    (1 - learning_rates step_count * strength)
      * RUN_SCHEDULE learning_rates strength step_count error

/-- **A schedule multiplies its factors.** -/
theorem runSchedule_eq
    (learning_rates : LearningRatePerStep)
    (strength : ℝ)
    (step_count : ℕ)
    (error : ℝ) :
    let remaining_error :=
      RUN_SCHEDULE learning_rates strength step_count error
    let factors := ∏ step ∈ Finset.range step_count,
      (1 - learning_rates step * strength)  -- each step shrinks the error by one factor
    remaining_error = factors * error := by
  unfold_named_pieces
  induction step_count with
  | zero => simp [RUN_SCHEDULE]
  | succ step_count ih =>
    rw [RUN_SCHEDULE, ih, Finset.prod_range_succ]
    ring

/-- While every `learning_rates step * strength` is between zero and two, the
error never grows. -/
theorem abs_runSchedule_le
    {learning_rates : LearningRatePerStep}
    {strength : ℝ}
    (steps_are_stable : ∀ step,
      0 ≤ learning_rates step * strength
        ∧ learning_rates step * strength ≤ 2)
    (step_count : ℕ)
    (error : ℝ) :
    let remaining_error :=
      |RUN_SCHEDULE learning_rates strength step_count error|
    let starting_error  := |error|
    remaining_error ≤ starting_error := by
  unfold_named_pieces
  induction step_count with
  | zero => simp [RUN_SCHEDULE]
  | succ step_count ih =>
    -- A factor between -1 and 1 cannot make the error larger.
    have factor_le_one : |1 - learning_rates step_count * strength| ≤ 1 := by
      rw [abs_le]
      constructor <;>
        linarith [(steps_are_stable step_count).1,
          (steps_are_stable step_count).2]
    rw [RUN_SCHEDULE, abs_mul]
    calc |1 - learning_rates step_count * strength|
          * |RUN_SCHEDULE learning_rates strength step_count error|
        ≤ 1 * |error| :=
          mul_le_mul factor_le_one ih (abs_nonneg _) zero_le_one
      _ = |error| := one_mul _

/-- **Why warmup.** A step that is too large for a direction makes its error
grow. -/
theorem one_lt_abs_one_sub
    {learning_rate strength : ℝ}
    (step_too_large : 2 < learning_rate * strength) :
    let factor_size := |1 - learning_rate * strength|
    1 < factor_size := by
  unfold_named_pieces
  rw [abs_of_neg (by linarith)]
  linarith

/-- **The condition number sets the speed.** With strengths between `weakest`
and `strongest` and the step `2 / (weakest + strongest)`, every direction
shrinks by at least `(strongest - weakest) / (strongest + weakest)` a step. -/
theorem abs_one_sub_best_step_le
    {weakest strongest strength : ℝ}
    (weakest_pos : 0 < weakest)
    (weakest_le_strongest : weakest ≤ strongest)
    (weakest_le_strength : weakest ≤ strength)
    (strength_le_strongest : strength ≤ strongest) :
    let best_step := 2 / (weakest + strongest)  -- balances the two ends of the range
    let factor_size := |1 - best_step * strength|
    let speed := (strongest - weakest) / (strongest + weakest)
    factor_size ≤ speed := by
  unfold_named_pieces
  have sum_pos : 0 < weakest + strongest := by linarith
  have factor_eq :
      1 - 2 / (weakest + strongest) * strength
        = (weakest + strongest - 2 * strength) / (weakest + strongest) := by
    field_simp
  rw [factor_eq, abs_div, abs_of_pos sum_pos, add_comm strongest weakest]
  refine div_le_div_of_nonneg_right ?_ sum_pos.le
  rw [abs_le]
  constructor <;> linarith

/-- The weakest direction shrinks by exactly that factor, so no direction can
be promised more. -/
theorem one_sub_best_step_at_weakest
    {weakest strongest : ℝ}
    (weakest_pos : 0 < weakest)
    (weakest_le_strongest : weakest ≤ strongest) :
    let best_step := 2 / (weakest + strongest)
    let weakest_factor := 1 - best_step * weakest
    let speed := (strongest - weakest) / (strongest + weakest)
    weakest_factor = speed := by
  unfold_named_pieces
  have sum_ne_zero : weakest + strongest ≠ 0 := by linarith
  have swapped_sum_ne_zero : strongest + weakest ≠ 0 := by linarith
  have cleared :
      2 / (weakest + strongest) * weakest * (strongest + weakest)
        = 2 * weakest := by
    rw [add_comm strongest weakest, mul_assoc,
      mul_comm weakest (weakest + strongest), ← mul_assoc,
      div_mul_cancel₀ _ sum_ne_zero]
  rw [eq_div_iff swapped_sum_ne_zero]
  linear_combination -cleared

/-- One step of gradient descent with momentum `momentum`, in a direction of
strength `strength`. The state is the error now and the error one step ago.
Python: `(error + momentum * (error - error_before)
- learning_rate * strength * error, error)`. -/
def TAKE_MOMENTUM_STEP
    (learning_rate momentum strength : ℝ)
    (state : MomentumState) : MomentumState :=
  ((1 + momentum - learning_rate * strength) * state.1
      - momentum * state.2, state.1)

/-- With no momentum it is the plain step. -/
theorem momentumStep_of_no_momentum
    (learning_rate strength : ℝ)
    (state : MomentumState) :
    let momentum_step :=
      TAKE_MOMENTUM_STEP learning_rate 0 strength state
    let plain_step : MomentumState :=
      ((1 - learning_rate * strength) * state.1, state.1)
    momentum_step = plain_step := by
  unfold_named_pieces
  simp [TAKE_MOMENTUM_STEP]

/-- **Momentum moves the edge of stability.** At
`learning_rate * strength = 2 * (1 + momentum)` an error that flips sign at
every step is carried forward at full size. -/
theorem momentumStep_alternating
    {learning_rate momentum strength : ℝ}
    (at_edge : learning_rate * strength = 2 * (1 + momentum))
    (amplitude : ℝ) :
    let flipping_state : MomentumState := (amplitude, -amplitude)
    let next_state :=
      TAKE_MOMENTUM_STEP learning_rate momentum strength flipping_state
    let flipped_state : MomentumState := (-amplitude, amplitude)
    next_state = flipped_state := by
  unfold_named_pieces
  refine Prod.ext ?_ rfl
  show (1 + momentum - learning_rate * strength) * amplitude
      - momentum * -amplitude = -amplitude
  rw [at_edge]
  ring

/-- At that edge the flipping error never dies and never grows. -/
theorem iterate_momentumStep_alternating
    {learning_rate momentum strength : ℝ}
    (at_edge : learning_rate * strength = 2 * (1 + momentum))
    (amplitude : ℝ)
    (step_count : ℕ) :
    let flipping_state : MomentumState := (amplitude, -amplitude)
    let trained_state :=
      (TAKE_MOMENTUM_STEP learning_rate momentum strength)^[step_count]
        flipping_state
    let sign_flip : ℝ := (-1) ^ step_count  -- one sign change per step
    let flipped_amplitude := sign_flip * amplitude
    let expected_state : MomentumState :=
      (flipped_amplitude, -flipped_amplitude)
    trained_state = expected_state := by
  unfold_named_pieces
  induction step_count with
  | zero => simp
  | succ step_count ih =>
    have one_flip (value : ℝ) :
        TAKE_MOMENTUM_STEP learning_rate momentum strength (value, -value)
          = (-value, value) :=
      momentumStep_alternating at_edge value
    rw [Function.iterate_succ_apply', ih, one_flip]
    ext <;> simp [pow_succ]

variable {Parts Weights : Type*} [Fintype Parts] [AddCommGroup Weights]
  [Module ℝ Weights]

/-- **An average of steps is a step on the average.** Let each client `k`,
holding the share `shares k` of the data, take one step from the same weights
on its own gradient. The average of where they land is one step on the
gradient of all the data. -/
theorem sum_smul_step_eq_step
    {shares : Parts → ℝ}
    (shares_sum_to_one : ∑ k, shares k = 1)
    (learning_rate : ℝ)
    (weights : Weights)
    (gradients : Parts → Weights) :
    let averaged_step : Weights :=
      ∑ k, shares k • (weights - learning_rate • gradients k)
    let step_on_average : Weights :=
      weights - learning_rate • ∑ k, shares k • gradients k
    averaged_step = step_on_average := by
  unfold_named_pieces
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    shares_sum_to_one, one_smul, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

/-- **A step on a random example is the full step on average.** -/
theorem mean_step_eq_step
    [Nonempty Parts]
    (learning_rate : ℝ)
    (weights : Weights)
    (gradients : Parts → Weights) :
    let mean_of_steps : Weights :=
      (Fintype.card Parts : ℝ)⁻¹
        • ∑ i, (weights - learning_rate • gradients i)
    let step_on_mean : Weights :=
      weights - learning_rate
        • ((Fintype.card Parts : ℝ)⁻¹ • ∑ i, gradients i)
    mean_of_steps = step_on_mean := by
  unfold_named_pieces
  have card_ne_zero : (Fintype.card Parts : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  -- Equal shares `1 / card` sum to one.
  have equal_shares_sum_to_one :
      ∑ _k : Parts, (Fintype.card Parts : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ card_ne_zero]
  have averaged :
      ∑ k, (Fintype.card Parts : ℝ)⁻¹
          • (weights - learning_rate • gradients k)
        = weights - learning_rate
          • ∑ k, (Fintype.card Parts : ℝ)⁻¹ • gradients k :=
    sum_smul_step_eq_step equal_shares_sum_to_one learning_rate weights
      gradients
  rwa [← Finset.smul_sum, ← Finset.smul_sum] at averaged

end SquigglyLine
