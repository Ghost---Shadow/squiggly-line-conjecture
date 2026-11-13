/-
Optimisers: schedules, the condition number, momentum, and steps on part of the data.

`SpectralBias.lean` shows that gradient descent multiplies the error in a
direction of strength `lam` by `1 - η lam` at every step. This file follows
that one number through four common changes to the step.

* **A schedule.** With a step size that changes, what is left of the error
  is the product of the factors `1 - η t * lam`. A factor is at most one in
  size exactly while `η t * lam` is between zero and two, which is what
  warmup protects.
* **The condition number.** With strengths between `m` and `M`, the step
  `2 / (m + M)` shrinks every direction by at least `(M - m) / (M + m)`, and
  the weakest direction by exactly that.
* **Momentum.** With momentum `β` the oscillation that never dies sits at
  `η lam = 2 (1 + β)`, not at `η lam = 2`.
* **Steps on part of the data.** An average of steps, each on one client's or
  one example's gradient, is one step on the averaged gradient. That covers
  stochastic gradient descent on average, and federated averaging after one
  local step.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `RUN_SCHEDULE`, `TAKE_MOMENTUM_STEP`.

Theorems: `runSchedule_eq`, `abs_runSchedule_le`, `one_lt_abs_one_sub`,
`abs_one_sub_best_step_le`, `one_sub_best_step_at_weakest`,
`momentumStep_of_no_momentum`, `momentumStep_alternating`,
`iterate_momentumStep_alternating`, `sum_smul_step_eq_step`,
`mean_step_eq_step`.
-/
import SquigglyLine.Supporting.Training.StepRules

namespace SquigglyLine

/-- What is left of the error in a direction of strength `lam` after `n` steps, when step `t`
has size `η t`.
Python: `for t in range(n): e = (1 - η[t] * lam) * e`. -/
def RUN_SCHEDULE (η : ℕ → ℝ) (lam : ℝ) : ℕ → ℝ → ℝ
  | 0, e => e
  | n + 1, e => (1 - η n * lam) * RUN_SCHEDULE η lam n e

/-- **A schedule multiplies its factors.** -/
theorem runSchedule_eq (η : ℕ → ℝ) (lam : ℝ) (n : ℕ) (e : ℝ) :
    RUN_SCHEDULE η lam n e = (∏ t ∈ Finset.range n, (1 - η t * lam)) * e := by
  induction n with
  | zero => simp [RUN_SCHEDULE]
  | succ n ih =>
    rw [RUN_SCHEDULE, ih, Finset.prod_range_succ]
    ring

/-- While every `η t * lam` is between zero and two, the error never grows. -/
theorem abs_runSchedule_le {η : ℕ → ℝ} {lam : ℝ}
    (h : ∀ t, 0 ≤ η t * lam ∧ η t * lam ≤ 2) (n : ℕ) (e : ℝ) :
    |RUN_SCHEDULE η lam n e| ≤ |e| := by
  induction n with
  | zero => simp [RUN_SCHEDULE]
  | succ n ih =>
    have hf : |1 - η n * lam| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(h n).1, (h n).2]
    rw [RUN_SCHEDULE, abs_mul]
    calc |1 - η n * lam| * |RUN_SCHEDULE η lam n e|
        ≤ 1 * |e| := mul_le_mul hf ih (abs_nonneg _) zero_le_one
      _ = |e| := one_mul _

/-- **Why warmup.** A step that is too large for a direction makes its error grow. -/
theorem one_lt_abs_one_sub {η lam : ℝ} (h : 2 < η * lam) : 1 < |1 - η * lam| := by
  rw [abs_of_neg (by linarith)]
  linarith

/-- **The condition number sets the speed.** With strengths between `m` and `M` and the step
`2 / (m + M)`, every direction shrinks by at least `(M - m) / (M + m)` a step. -/
theorem abs_one_sub_best_step_le {m M lam : ℝ} (hm : 0 < m) (hmM : m ≤ M) (h1 : m ≤ lam)
    (h2 : lam ≤ M) :
    |1 - 2 / (m + M) * lam| ≤ (M - m) / (M + m) := by
  have hs : 0 < m + M := by linarith
  have h : 1 - 2 / (m + M) * lam = (m + M - 2 * lam) / (m + M) := by
    field_simp
  rw [h, abs_div, abs_of_pos hs, add_comm M m]
  refine div_le_div_of_nonneg_right ?_ hs.le
  rw [abs_le]
  constructor <;> linarith

/-- The weakest direction shrinks by exactly that factor, so no direction can be promised
more. -/
theorem one_sub_best_step_at_weakest {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    1 - 2 / (m + M) * m = (M - m) / (M + m) := by
  have hs : m + M ≠ 0 := by linarith
  have hs' : M + m ≠ 0 := by linarith
  have h : 2 / (m + M) * m * (M + m) = 2 * m := by
    rw [add_comm M m, mul_assoc, mul_comm m (m + M), ← mul_assoc, div_mul_cancel₀ _ hs]
  rw [eq_div_iff hs']
  linear_combination -h

/-- One step of gradient descent with momentum `β`, in a direction of strength `lam`. The
state is the error now and the error one step ago.
Python: `(e + β * (e - e_before) - η * lam * e, e)`. -/
def TAKE_MOMENTUM_STEP (η β lam : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  ((1 + β - η * lam) * s.1 - β * s.2, s.1)

/-- With no momentum it is the plain step. -/
theorem momentumStep_of_no_momentum (η lam : ℝ) (s : ℝ × ℝ) :
    TAKE_MOMENTUM_STEP η 0 lam s = ((1 - η * lam) * s.1, s.1) := by
  simp [TAKE_MOMENTUM_STEP]

/-- **Momentum moves the edge of stability.** At `η lam = 2 (1 + β)` an error that flips sign
at every step is carried forward at full size. -/
theorem momentumStep_alternating {η β lam : ℝ} (h : η * lam = 2 * (1 + β)) (a : ℝ) :
    TAKE_MOMENTUM_STEP η β lam (a, -a) = (-a, a) := by
  refine Prod.ext ?_ rfl
  show (1 + β - η * lam) * a - β * -a = -a
  rw [h]
  ring

/-- At that edge the flipping error never dies and never grows. -/
theorem iterate_momentumStep_alternating {η β lam : ℝ} (h : η * lam = 2 * (1 + β)) (a : ℝ)
    (n : ℕ) :
    (TAKE_MOMENTUM_STEP η β lam)^[n] (a, -a) = ((-1) ^ n * a, -((-1) ^ n * a)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, momentumStep_alternating h]
    ext <;> simp [pow_succ]

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- **An average of steps is a step on the average.** Let each client `k`, holding the share
`p k` of the data, take one step from the same weights on its own gradient. The average of
where they land is one step on the gradient of all the data. -/
theorem sum_smul_step_eq_step {p : ι → ℝ} (hp : ∑ k, p k = 1) (η : ℝ) (θ : E) (g : ι → E) :
    ∑ k, p k • (θ - η • g k) = θ - η • ∑ k, p k • g k := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hp, one_smul,
    Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

/-- **A step on a random example is the full step on average.** -/
theorem mean_step_eq_step [Nonempty ι] (η : ℝ) (θ : E) (g : ι → E) :
    (Fintype.card ι : ℝ)⁻¹ • ∑ i, (θ - η • g i)
      = θ - η • ((Fintype.card ι : ℝ)⁻¹ • ∑ i, g i) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp : ∑ _k : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  have h := sum_smul_step_eq_step hp η θ g
  rwa [← Finset.smul_sum, ← Finset.smul_sum] at h

end SquigglyLine
