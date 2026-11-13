/-
Regularisers, each as a charge on slope or a floor on travel.

* **Lasso.** A penalty on the size of a weight sets a weak direction to
  exactly zero. Weight decay only shrinks it.
* **Noise on the input.** For a linear model, noise of variance `σ²` adds
  `σ²` times the squared slope to the expected loss.
* **Adversarial training.** For a linear model, the worst nudge of size `ε`
  lowers the score by exactly `ε` times the summed sizes of the weights.
* **Stochastic depth.** A branch kept with chance `p` is, on average, the
  branch at strength `p`.
* **Mixup.** A model that fits every blend of two examples has, between
  them, the least slope any line through both can have.
* **Distillation.** A teacher's soft label gives the student a finite best
  score: the teacher's own.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `GET_LASSO_COST`, `GET_RIDGE_COST`.

Theorems: `lassoCost_zero_le`, `lassoCost_sub_le`, `ridgeCost_div_le`,
`sum_mul_sq_sub_noisy_eq`, `sub_le_score_add`, `score_add_worst_nudge`,
`mean_stochasticDepth`, `abs_sub_le_of_lipschitz_fit`, `mixup_fit_gap`,
`logLoss_teacher_le`.
-/
import SquigglyLine.Supporting.NetworkShape.NetworkSlope

namespace SquigglyLine

open Real

/-- The lasso cost of one weight: half the squared miss of the target `a`, plus `μ` times the
size of the weight.
Python: `(θ - a) ** 2 / 2 + μ * abs(θ)`. -/
noncomputable def GET_LASSO_COST (μ a θ : ℝ) : ℝ :=
  (θ - a) ^ 2 / 2 + μ * |θ|

/-- The weight-decay cost of one weight: the same, with the square of the weight.
Python: `(θ - a) ** 2 / 2 + μ * θ ** 2 / 2`. -/
noncomputable def GET_RIDGE_COST (μ a θ : ℝ) : ℝ :=
  (θ - a) ^ 2 / 2 + μ * θ ^ 2 / 2

/-- **Lasso sets a weak direction to exactly zero.** If the target is no larger than the
penalty, the best weight is zero. -/
theorem lassoCost_zero_le {μ a : ℝ} (h : |a| ≤ μ) (θ : ℝ) :
    GET_LASSO_COST μ a 0 ≤ GET_LASSO_COST μ a θ := by
  have h1 : a * θ ≤ μ * |θ| :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right h (abs_nonneg θ))
  simp only [GET_LASSO_COST, abs_zero, mul_zero, add_zero, zero_sub]
  nlinarith [sq_nonneg θ]

/-- A direction stronger than the penalty is kept, shortened by exactly the penalty. -/
theorem lassoCost_sub_le {μ a : ℝ} (hμ : 0 ≤ μ) (h : μ < a) (θ : ℝ) :
    GET_LASSO_COST μ a (a - μ) ≤ GET_LASSO_COST μ a θ := by
  have h1 : μ * θ ≤ μ * |θ| := mul_le_mul_of_nonneg_left (le_abs_self θ) hμ
  simp only [GET_LASSO_COST]
  rw [abs_of_pos (by linarith : 0 < a - μ)]
  nlinarith [sq_nonneg (θ - a + μ)]

/-- **Weight decay only shrinks.** Its best weight is the target divided by `1 + μ`, which is
zero only if the target is. -/
theorem ridgeCost_div_le {μ a : ℝ} (hμ : 0 ≤ μ) (θ : ℝ) :
    GET_RIDGE_COST μ a (a / (1 + μ)) ≤ GET_RIDGE_COST μ a θ := by
  have hpos : 0 < 1 + μ := by linarith
  have h : GET_RIDGE_COST μ a θ - GET_RIDGE_COST μ a (a / (1 + μ))
      = (1 + μ) / 2 * (θ - a / (1 + μ)) ^ 2 := by
    simp only [GET_RIDGE_COST]
    field_simp
    ring
  have hnonneg : 0 ≤ (1 + μ) / 2 * (θ - a / (1 + μ)) ^ 2 := by positivity
  linarith

variable {ι : Type*} [Fintype ι]

/-- **Noise on the input is a charge on slope.** Average the squared error of the line
`w * x` over input noise of mean zero and variance `σ²`. The result is the plain squared error
plus `σ² * w²`. -/
theorem sum_mul_sq_sub_noisy_eq {p ε : ι → ℝ} {σ : ℝ} (hp : ∑ j, p j = 1)
    (hmean : ∑ j, p j * ε j = 0) (hvar : ∑ j, p j * ε j ^ 2 = σ ^ 2) (w x y : ℝ) :
    ∑ j, p j * (y - w * (x + ε j)) ^ 2 = (y - w * x) ^ 2 + σ ^ 2 * w ^ 2 := by
  have hterm : ∀ j, p j * (y - w * (x + ε j)) ^ 2
      = (y - w * x) ^ 2 * p j - 2 * (y - w * x) * w * (p j * ε j)
        + w ^ 2 * (p j * ε j ^ 2) := fun j => by ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp,
    hmean, hvar]
  ring

/-- **The worst nudge costs at most `ε` times the summed weights.** No nudge of size at most
`ε` on each input lowers the score by more. -/
theorem sub_le_score_add (w x δ : ι → ℝ) {ε : ℝ} (hδ : ∀ i, |δ i| ≤ ε) :
    GET_LINEAR_SCORE w x - ε * ∑ i, |w i| ≤ GET_LINEAR_SCORE w fun i => x i + δ i := by
  have h : |GET_LINEAR_SCORE w (fun i => x i + δ i) - GET_LINEAR_SCORE w x|
      ≤ ε * ∑ i, |w i| := abs_score_add_sub_le w x δ hδ
  linarith [neg_abs_le (GET_LINEAR_SCORE w (fun i => x i + δ i) - GET_LINEAR_SCORE w x)]

/-- **And one nudge costs exactly that.** So training against the worst nudge is training with
a penalty of `ε` times the summed sizes of the weights. -/
theorem score_add_worst_nudge (w x : ι → ℝ) (ε : ℝ) :
    GET_LINEAR_SCORE w (fun i => x i + -ε * SignType.sign (w i))
      = GET_LINEAR_SCORE w x - ε * ∑ i, |w i| := by
  have h : GET_LINEAR_SCORE w (fun i => x i + -ε * SignType.sign (w i))
      = GET_LINEAR_SCORE w x + -ε * ∑ i, |w i| := score_add_sign w x (-ε)
  rw [h]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Stochastic depth.** Keep a branch with chance `p` and drop it otherwise. On average the
layer is the input plus `p` times the branch. -/
theorem mean_stochasticDepth (p : ℝ) (x b : E) :
    p • (x + b) + (1 - p) • x = x + p • b := by
  module

omit [NormedSpace ℝ E] in
/-- Any line through two examples has slope at least their gap in labels over their
distance. -/
theorem abs_sub_le_of_lipschitz_fit {f : E → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (x x' : E) :
    |f x' - f x| ≤ K * dist x' x := by
  have h := hf.dist_le_mul x' x
  rwa [Real.dist_eq] at h

/-- **Mixup asks for the least slope.** A model that fits every blend of two examples is
straight between them: the gap in its output between two blends is the gap in labels times the
share of the way between them. -/
theorem mixup_fit_gap {f : E → ℝ} {x x' : E} {y y' : ℝ}
    (hfit : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → f (x + t • (x' - x)) = y + t * (y' - y))
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |f (x + s • (x' - x)) - f (x + t • (x' - x))| * ‖x' - x‖
      = |y' - y| * dist (x + s • (x' - x)) (x + t • (x' - x)) := by
  have hdist : dist (x + s • (x' - x)) (x + t • (x' - x)) = |s - t| * ‖x' - x‖ := by
    rw [dist_eq_norm, show x + s • (x' - x) - (x + t • (x' - x)) = (s - t) • (x' - x) by module,
      norm_smul, Real.norm_eq_abs]
  rw [hfit s hs0 hs1, hfit t ht0 ht1, hdist,
    show y + s * (y' - y) - (y + t * (y' - y)) = (s - t) * (y' - y) by ring, abs_mul]
  ring

/-- **Distillation gives the student a finite target.** Against the teacher's soft label, the
teacher's own score is a best score. -/
theorem logLoss_teacher_le (teacher_score score : ℝ) :
    GET_LOG_LOSS (sigmoid teacher_score) teacher_score
      ≤ GET_LOG_LOSS (sigmoid teacher_score) score :=
  logLoss_le_of_sigmoid_eq rfl score

end SquigglyLine
