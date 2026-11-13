/-
Regularisers, each as a charge on slope or a floor on travel.

* **Lasso.** A penalty on the size of a weight sets a weak direction to
  exactly zero. Weight decay only shrinks it.
* **Noise on the input.** For a linear model, noise of spread `noise_spread`
  adds `noise_spread²` times the squared slope to the expected loss.
* **Adversarial training.** For a linear model, the worst nudge of size
  `size_limit` lowers the score by exactly `size_limit` times the summed sizes
  of the weights.
* **Stochastic depth.** A branch kept with chance `keep_chance` is, on
  average, the branch at strength `keep_chance`.
* **Mixup.** A model that fits every blend of two examples has, between
  them, the least slope any line through both can have.
* **Distillation.** A teacher's soft label gives the student a finite best
  score: the teacher's own.

Definitions: `GET_LASSO_COST`, `GET_RIDGE_COST`.

Theorems:

* `lassoCost_zero_le`          a target no larger than the penalty gives the
                               best weight zero;
* `lassoCost_sub_le`           a stronger target is kept, shortened by the
                               penalty;
* `ridgeCost_div_le`           weight decay only shrinks;
* `sum_mul_sq_sub_noisy_eq`    noise on the input is a charge on slope;
* `sub_le_score_add`           the worst nudge costs at most the summed
                               weights times its size;
* `score_add_worst_nudge`      and one nudge costs exactly that;
* `mean_stochasticDepth`       on average a kept branch is the branch at
                               strength `keep_chance`;
* `abs_sub_le_of_lipschitz_fit`  a line through two examples has slope at least
                               the label gap over the distance;
* `mixup_fit_gap`              a model fitting every blend is straight between
                               the two examples;
* `logLoss_teacher_le`         the teacher's own score is a best score.
-/
import SquigglyLine.Supporting.NetworkShape.NetworkSlope

namespace SquigglyLine

open Real

/-- The lasso cost of one weight: half the squared miss of the target, plus
`penalty` times the size of the weight.
Python: `(weight - target) ** 2 / 2 + penalty * abs(weight)`. -/
noncomputable def GET_LASSO_COST
    (penalty target weight : ℝ) : ℝ :=
  (weight - target) ^ 2 / 2 + penalty * |weight|

/-- The weight-decay cost of one weight: the same, with the square of the
weight.
Python: `(weight - target) ** 2 / 2 + penalty * weight ** 2 / 2`. -/
noncomputable def GET_RIDGE_COST
    (penalty target weight : ℝ) : ℝ :=
  (weight - target) ^ 2 / 2 + penalty * weight ^ 2 / 2

/-- **Lasso sets a weak direction to exactly zero.** If the target is no larger
than the penalty, the best weight is zero. -/
theorem lassoCost_zero_le
    {penalty target : ℝ}
    (target_within_penalty : |target| ≤ penalty)
    (weight : ℝ) :
    let zero_cost := GET_LASSO_COST penalty target 0
    let cost      := GET_LASSO_COST penalty target weight
    zero_cost ≤ cost := by
  unfold_named_pieces
  have pull_le_penalty : target * weight ≤ penalty * |weight| :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right target_within_penalty
        (abs_nonneg weight))
  simp only [GET_LASSO_COST, abs_zero, mul_zero, add_zero, zero_sub]
  nlinarith [sq_nonneg weight]

/-- A direction stronger than the penalty is kept, shortened by exactly the
penalty. -/
theorem lassoCost_sub_le
    {penalty target : ℝ}
    (penalty_nonneg : 0 ≤ penalty)
    (penalty_lt_target : penalty < target)
    (weight : ℝ) :
    let shortened_cost := GET_LASSO_COST penalty target (target - penalty)
    let cost           := GET_LASSO_COST penalty target weight
    shortened_cost ≤ cost := by
  unfold_named_pieces
  have pull_le_penalty : penalty * weight ≤ penalty * |weight| :=
    mul_le_mul_of_nonneg_left (le_abs_self weight) penalty_nonneg
  simp only [GET_LASSO_COST]
  rw [abs_of_pos (by linarith : 0 < target - penalty)]
  nlinarith [sq_nonneg (weight - target + penalty)]

/-- **Weight decay only shrinks.** Its best weight is the target divided by
`1 + penalty`, which is zero only if the target is. -/
theorem ridgeCost_div_le
    {penalty target : ℝ}
    (penalty_nonneg : 0 ≤ penalty)
    (weight : ℝ) :
    let shrunk_cost := GET_RIDGE_COST penalty target (target / (1 + penalty))  -- the minimum of the quadratic
    let cost        := GET_RIDGE_COST penalty target weight
    shrunk_cost ≤ cost := by
  unfold_named_pieces
  have one_add_penalty_pos : 0 < 1 + penalty := by linarith
  -- The excess over the minimum is a square, so it is not negative.
  have excess_eq :
      GET_RIDGE_COST penalty target weight
          - GET_RIDGE_COST penalty target (target / (1 + penalty))
        = (1 + penalty) / 2 * (weight - target / (1 + penalty)) ^ 2 := by
    simp only [GET_RIDGE_COST]
    field_simp
    ring
  have excess_nonneg :
      0 ≤ (1 + penalty) / 2 * (weight - target / (1 + penalty)) ^ 2 := by
    positivity
  linarith

variable {Outcomes : Type*} [Fintype Outcomes]

/-- **Noise on the input is a charge on slope.** Average the squared error of
the line `slope * input` over input noise of mean zero and spread
`noise_spread`. The result is the plain squared error plus
`noise_spread² * slope²`. -/
theorem sum_mul_sq_sub_noisy_eq
    {chances noises : Outcomes → ℝ}
    {noise_spread : ℝ}
    (chances_sum_to_one : ∑ j, chances j = 1)
    (noise_has_mean_zero : ∑ j, chances j * noises j = 0)
    (noise_has_variance :
      ∑ j, chances j * noises j ^ 2 = noise_spread ^ 2)
    (slope input label : ℝ) :
    let noisy_error := ∑ j,
      chances j * (label - slope * (input + noises j)) ^ 2
    let plain_error := (label - slope * input) ^ 2
    let noise_charge := noise_spread ^ 2 * slope ^ 2
    noisy_error = plain_error + noise_charge := by
  unfold_named_pieces
  -- Expand the square; the cross term vanishes since the noise has mean zero.
  have expand_term : ∀ j, chances j * (label - slope * (input + noises j)) ^ 2
      = (label - slope * input) ^ 2 * chances j
        - 2 * (label - slope * input) * slope * (chances j * noises j)
        + slope ^ 2 * (chances j * noises j ^ 2) := fun j => by ring
  simp only [expand_term, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, chances_sum_to_one, noise_has_mean_zero,
    noise_has_variance]
  ring

variable {Coordinates : Type*} [Fintype Coordinates]

/-- **The worst nudge costs at most `size_limit` times the summed weights.** No
nudge of size at most `size_limit` on each input lowers the score by more. -/
theorem sub_le_score_add
    (weights input nudge : Coordinates → ℝ)
    {size_limit : ℝ}
    (nudge_is_small : ∀ i, |nudge i| ≤ size_limit) :
    let nudged_input : Coordinates → ℝ := fun i => input i + nudge i
    let score_before      := GET_LINEAR_SCORE weights input
    let score_after       := GET_LINEAR_SCORE weights nudged_input
    let total_weight_size := ∑ i, |weights i|
    let lowest_score      := score_before - size_limit * total_weight_size
    lowest_score ≤ score_after := by
  unfold_named_pieces
  have change_is_small :
      |GET_LINEAR_SCORE weights (fun i => input i + nudge i)
          - GET_LINEAR_SCORE weights input|
        ≤ size_limit * ∑ i, |weights i| :=
    abs_score_add_sub_le weights input nudge nudge_is_small
  linarith [neg_abs_le (GET_LINEAR_SCORE weights (fun i => input i + nudge i)
    - GET_LINEAR_SCORE weights input)]

/-- **And one nudge costs exactly that.** So training against the worst nudge
is training with a penalty of `nudge_size` times the summed sizes of the
weights. -/
theorem score_add_worst_nudge
    (weights input : Coordinates → ℝ)
    (nudge_size : ℝ) :
    let nudged_input : Coordinates → ℝ :=
      fun i => input i + -nudge_size * SignType.sign (weights i)  -- against the sign of each weight
    let score_after       := GET_LINEAR_SCORE weights nudged_input
    let score_before      := GET_LINEAR_SCORE weights input
    let total_weight_size := ∑ i, |weights i|
    let lowered_score     := score_before - nudge_size * total_weight_size
    score_after = lowered_score := by
  unfold_named_pieces
  have nudge_against_sign :
      GET_LINEAR_SCORE weights
          (fun i => input i + -nudge_size * SignType.sign (weights i))
        = GET_LINEAR_SCORE weights input
          + -nudge_size * ∑ i, |weights i| :=
    score_add_sign weights input (-nudge_size)
  rw [nudge_against_sign]
  ring

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

/-- **Stochastic depth.** Keep a branch with chance `keep_chance` and drop it
otherwise. On average the layer is the input plus `keep_chance` times the
branch. -/
theorem mean_stochasticDepth
    (keep_chance : ℝ)
    (input branch : Space) :
    let average_layer : Space :=
      keep_chance • (input + branch) + (1 - keep_chance) • input  -- kept with chance `keep_chance`, else skipped
    let weighted_branch_layer : Space := input + keep_chance • branch
    average_layer = weighted_branch_layer := by
  unfold_named_pieces
  module

omit [NormedSpace ℝ Space] in
/-- Any line through two examples has slope at least their gap in labels over
their distance. -/
theorem abs_sub_le_of_lipschitz_fit
    {model : Model Space}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    (input other_input : Space) :
    let output_gap  := |model other_input - model input|
    let allowed_gap : ℝ := slope_limit * dist other_input input
    output_gap ≤ allowed_gap := by
  unfold_named_pieces
  have distance_bound := slope_is_bounded.dist_le_mul other_input input
  rwa [Real.dist_eq] at distance_bound

/-- **Mixup asks for the least slope.** A model that fits every blend of two
examples is straight between them: the gap in its output between two blends is
the gap in labels times the share of the way between them. -/
theorem mixup_fit_gap
    {model : Model Space}
    {start_point end_point : Space}
    {start_label end_label : ℝ}
    (model_fits_blends :
      ∀ fraction : ℝ, 0 ≤ fraction → fraction ≤ 1 →
      model (start_point + fraction • (end_point - start_point))
        = start_label + fraction * (end_label - start_label))
    {first_fraction second_fraction : ℝ}
    (first_fraction_nonneg : 0 ≤ first_fraction)
    (first_fraction_le_one : first_fraction ≤ 1)
    (second_fraction_nonneg : 0 ≤ second_fraction)
    (second_fraction_le_one : second_fraction ≤ 1) :
    let first_blend : Space :=
      start_point + first_fraction • (end_point - start_point)
    let second_blend : Space :=
      start_point + second_fraction • (end_point - start_point)
    let output_gap     := |model first_blend - model second_blend|
    let span           := ‖end_point - start_point‖
    let label_gap      := |end_label - start_label|
    let blend_distance := dist first_blend second_blend
    output_gap * span = label_gap * blend_distance := by
  unfold_named_pieces
  -- Blends are spaced along the segment, so their distance is the gap in
  -- fractions times the length of the segment.
  have blend_distance_eq :
      dist (start_point + first_fraction • (end_point - start_point))
          (start_point + second_fraction • (end_point - start_point))
        = |first_fraction - second_fraction|
          * ‖end_point - start_point‖ := by
    rw [dist_eq_norm,
      show start_point + first_fraction • (end_point - start_point)
          - (start_point + second_fraction • (end_point - start_point))
        = (first_fraction - second_fraction) • (end_point - start_point)
        by module,
      norm_smul, Real.norm_eq_abs]
  rw [model_fits_blends first_fraction first_fraction_nonneg
      first_fraction_le_one,
    model_fits_blends second_fraction second_fraction_nonneg
      second_fraction_le_one,
    blend_distance_eq,
    show start_label + first_fraction * (end_label - start_label)
        - (start_label + second_fraction * (end_label - start_label))
      = (first_fraction - second_fraction) * (end_label - start_label)
      by ring,
    abs_mul]
  ring

/-- **Distillation gives the student a finite target.** Against the teacher's
soft label, the teacher's own score is a best score. -/
theorem logLoss_teacher_le
    (teacher_score score : ℝ) :
    let best_loss := GET_LOG_LOSS (sigmoid teacher_score) teacher_score
    let loss      := GET_LOG_LOSS (sigmoid teacher_score) score
    best_loss ≤ loss := by
  unfold_named_pieces
  exact logLoss_le_of_sigmoid_eq rfl score

end SquigglyLine
