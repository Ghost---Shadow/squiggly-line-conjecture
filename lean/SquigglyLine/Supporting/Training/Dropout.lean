/-
Dropout is weight decay.

Dropout multiplies each feature by a random mask during training. The mask
is one on average, so the model's answer is right on average and noisy
around that.

| Name                       | Meaning                                    |
|----------------------------|--------------------------------------------|
| `RandomMask`               | a random multiplier for each feature       |
| `FeatureTable`             | the value of each feature on each example  |
| `GET_AVERAGE`              | the average of a random quantity           |
| `ARE_MASKS_INDEPENDENT`    | each feature is masked on its own          |
| `ARE_MASKS_ONE_ON_AVERAGE` | every mask averages to one                 |
| `ARE_MASKS_OF_VARIANCE`    | every mask has the given variance          |

* `expected_dropout_loss` : for one example, the expected squared error under
  dropout is the plain squared error plus a penalty: the variance of the mask
  times the sum of the squared shares "feature times weight".
* `expected_dropout_loss_dataset` : over a set of examples the penalty on
  one weight is its square times the total squared size of its feature.
* `expected_dropout_loss_of_equal_features` : when every feature has the same
  total squared size `feature_size`, the penalty is
  `mask_variance * feature_size` times the squared length of the weights.
  That is weight decay.
* `keepMask_variance` : the usual mask, kept with probability
  `keep_probability` and scaled by `1 / keep_probability`, has variance
  `(1 - keep_probability) / keep_probability`.
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import SquigglyLine.Style

namespace SquigglyLine

open MeasureTheory ProbabilityTheory

/-! ## Types -/

/-- A random multiplier for each feature: `mask feature outcome` is what the
feature is multiplied by when the random draw comes out as `outcome`.
Python: `Callable[[Feature, Outcome], float]`. -/
abbrev RandomMask (Features Outcomes : Type*) := Features → Outcomes → ℝ

/-- The data, as a table: `feature_values example feature` is the value of
one feature on one example.
Python: `Callable[[Example, Feature], float]`, a 2-D array. -/
abbrev FeatureTable (Examples Features : Type*) := Examples → Features → ℝ

/-! ## The usual mask -/

/-- The usual dropout mask is `1 / keep_probability` with probability
`keep_probability` and `0` otherwise. Its mean is one and its variance,
written out over the two outcomes, is
`(1 - keep_probability) / keep_probability`. -/
theorem keepMask_variance
    {keep_probability : ℝ}
    (keep_probability_ne_zero : keep_probability ≠ 0) :
    let kept_part :=
      keep_probability * (1 / keep_probability - 1) ^ 2       -- kept: the mask is 1 / keep_probability; take off the mean, 1
    let dropped_part := (1 - keep_probability) * (0 - 1) ^ 2  -- dropped: the mask is 0; take off the mean, 1
    let mask_variance := kept_part + dropped_part             -- variance: the average squared distance from the mean
    let drop_to_keep_ratio :=
      (1 - keep_probability) / keep_probability               -- chance of dropping over chance of keeping
    mask_variance = drop_to_keep_ratio := by
  unfold_named_pieces
  field_simp
  ring

section Expectation

-- Given, for everything below: the outcomes of the random draw of the masks,
-- how likely each outcome is, and finitely many features.
variable
  {Outcomes : Type*} [MeasurableSpace Outcomes]
  (probability : Measure Outcomes) [IsProbabilityMeasure probability]  -- the chances add up to 1
  {Features : Type*} [Fintype Features]

/-! ## Helper functions

`probability` says how likely each outcome of the random draw is. It is the
first argument of every function and theorem from here on. -/

/-- The average of a random quantity.
Python: `mean(quantity(outcome) for outcome in random_draws)`. -/
noncomputable abbrev GET_AVERAGE (quantity : Outcomes → ℝ) : ℝ :=
  integral probability quantity

/-- The masks of two different features are drawn independently: knowing one
says nothing about the other. -/
abbrev ARE_MASKS_INDEPENDENT
    (mask : RandomMask Features Outcomes) : Prop :=
  Pairwise fun feature other_feature =>
    mask feature ⟂ᵢ[probability] mask other_feature

/-- Every mask is one on average, so dropout does not change the answer on
average.
Python: `all(mean(mask[feature]) == 1 for feature in features)`. -/
abbrev ARE_MASKS_ONE_ON_AVERAGE
    (mask : RandomMask Features Outcomes) : Prop :=
  ∀ feature, ∫ outcome, mask feature outcome ∂probability = 1

/-- Every mask has the same variance, `mask_variance`.
Python: `all(var(mask[feature]) == mask_variance for feature in features)`. -/
abbrev ARE_MASKS_OF_VARIANCE
    (mask : RandomMask Features Outcomes)
    (mask_variance : ℝ) : Prop :=
  ∀ feature, variance (mask feature) probability = mask_variance

/-! ## The theorems -/

/-- **Dropout adds a penalty.** One example with label `label`. Feature `j`
contributes the share `shares j` (the feature times its weight) to the
answer, and dropout multiplies it by `mask j`. If the masks are independent,
one on average and of variance `mask_variance`, the expected squared error is
the plain squared error plus `mask_variance` times the sum of the squared
shares. -/
theorem expected_dropout_loss
    {mask : RandomMask Features Outcomes}
    (masks_are_square_integrable :
      ∀ feature, MemLp (mask feature) 2 probability)  -- each mask has a finite average and variance, so the averages below exist
    (masks_are_independent : ARE_MASKS_INDEPENDENT probability mask)  -- so that the variances of the shares add up
    (masks_are_one_on_average : ARE_MASKS_ONE_ON_AVERAGE probability mask)
    {mask_variance : ℝ}
    (masks_have_this_variance :
      ARE_MASKS_OF_VARIANCE probability mask mask_variance)
    (label : ℝ)
    (shares : Features → ℝ) :
    let expected_dropout_loss :=
      GET_AVERAGE probability fun outcome =>
        let noisy_answer := ∑ j, mask j outcome * shares j  -- each share, multiplied by its mask
        (label - noisy_answer) ^ 2
    let plain_loss := (label - ∑ j, shares j) ^ 2           -- the squared error with no dropout
    let penalty    := mask_variance * ∑ j, shares j ^ 2     -- the variance of the noisy answer: independent variances add
    expected_dropout_loss = plain_loss + penalty := by      -- mean of a square = square of the mean + variance
  unfold_named_pieces
  unfold GET_AVERAGE
  have share_is_square_integrable (feature : Features) :
      MemLp (fun outcome => mask feature outcome * shares feature) 2
        probability :=
    (masks_are_square_integrable feature).mul_const (shares feature)
  have answer_is_a_sum_of_functions :
      (fun outcome => ∑ j, mask j outcome * shares j)
        = ∑ j, fun outcome => mask j outcome * shares j := by
    ext outcome
    simp
  have answer_is_square_integrable :
      MemLp (fun outcome => ∑ j, mask j outcome * shares j) 2 probability :=
    memLp_finsetSum _ fun j _ => share_is_square_integrable j
  -- The noisy answer is right on average, because each mask averages to one.
  have mean_of_answer :
      ∫ outcome, ∑ j, mask j outcome * shares j ∂probability
        = ∑ j, shares j := by
    rw [integral_finsetSum _ fun j _ =>
      (share_is_square_integrable j).integrable one_le_two]
    simp [integral_mul_const, masks_are_one_on_average]
  -- Its variance is the sum of the variances of the shares, because the
  -- masks are independent.
  have variance_of_answer :
      variance (fun outcome => ∑ j, mask j outcome * shares j) probability
        = mask_variance * ∑ j, shares j ^ 2 := by
    rw [answer_is_a_sum_of_functions,
      IndepFun.variance_sum (fun j _ => share_is_square_integrable j)
        fun feature _ other_feature _ features_differ =>
          (masks_are_independent features_differ).comp
            (measurable_id.mul_const (shares feature))
            (measurable_id.mul_const (shares other_feature))]
    simp [variance_mul_const, masks_have_this_variance, Finset.mul_sum]
  have error_is_square_integrable :
      MemLp (fun outcome => label - ∑ j, mask j outcome * shares j) 2
        probability :=
    (memLp_const label).sub answer_is_square_integrable
  have mean_of_error :
      ∫ outcome, label - ∑ j, mask j outcome * shares j ∂probability
        = label - ∑ j, shares j := by
    rw [integral_sub (integrable_const label)
      (answer_is_square_integrable.integrable one_le_two), mean_of_answer]
    simp
  -- The variance of the error is the mean of its square minus the square
  -- of its mean. Rearranged, that is the claim.
  have variance_of_error := variance_eq_sub error_is_square_integrable
  rw [variance_const_sub answer_is_square_integrable.aestronglyMeasurable
    label, variance_of_answer, mean_of_error] at variance_of_error
  have loss_is_the_square_of_the_error :
      ∫ outcome, (label - ∑ j, mask j outcome * shares j) ^ 2 ∂probability
        = ∫ outcome,
            ((fun outcome => label - ∑ j, mask j outcome * shares j) ^ 2)
              outcome ∂probability :=
    rfl
  rw [loss_is_the_square_of_the_error]
  linarith

-- Given, from here on: finitely many examples.
variable {Examples : Type*} [Fintype Examples]

/-- **Over a set of examples.** Example `i` has features `feature_values i`
and label `labels i`, the weights are `weights`. The penalty on weight `j` is
its square times the total squared size of feature `j` over the examples. -/
theorem expected_dropout_loss_dataset
    {mask : RandomMask Features Outcomes}
    (masks_are_square_integrable :
      ∀ feature, MemLp (mask feature) 2 probability)
    (masks_are_independent : ARE_MASKS_INDEPENDENT probability mask)
    (masks_are_one_on_average : ARE_MASKS_ONE_ON_AVERAGE probability mask)
    {mask_variance : ℝ}
    (masks_have_this_variance :
      ARE_MASKS_OF_VARIANCE probability mask mask_variance)
    (labels : Examples → ℝ)
    (feature_values : FeatureTable Examples Features)
    (weights : Features → ℝ) :
    let total_expected_dropout_loss :=
      ∑ i, GET_AVERAGE probability fun outcome =>
        (labels i - ∑ j, mask j outcome * (feature_values i j * weights j)) ^ 2  -- share of feature j: value times weight
    let total_plain_loss :=
      ∑ i, (labels i - ∑ j, feature_values i j * weights j) ^ 2
    let penalty :=
      mask_variance * ∑ j, (∑ i, feature_values i j ^ 2) * weights j ^ 2  -- (value * weight)² = value² * weight², per example
    total_expected_dropout_loss = total_plain_loss + penalty := by
  unfold_named_pieces
  -- Use the one-example result on each example, then add up feature by
  -- feature instead of example by example.
  simp only [expected_dropout_loss probability masks_are_square_integrable
      masks_are_independent masks_are_one_on_average masks_have_this_variance,
    Finset.sum_add_distrib, ← Finset.mul_sum, mul_pow, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **Dropout is weight decay.** If every feature has the same total squared
size `feature_size`, the penalty is `mask_variance * feature_size` times the
squared length of the weights. -/
theorem expected_dropout_loss_of_equal_features
    {mask : RandomMask Features Outcomes}
    (masks_are_square_integrable :
      ∀ feature, MemLp (mask feature) 2 probability)
    (masks_are_independent : ARE_MASKS_INDEPENDENT probability mask)
    (masks_are_one_on_average : ARE_MASKS_ONE_ON_AVERAGE probability mask)
    {mask_variance : ℝ}
    (masks_have_this_variance :
      ARE_MASKS_OF_VARIANCE probability mask mask_variance)
    (labels : Examples → ℝ)
    (feature_values : FeatureTable Examples Features)
    (weights : Features → ℝ)
    {feature_size : ℝ}
    (features_have_equal_size :
      ∀ feature, ∑ i, feature_values i feature ^ 2 = feature_size) :  -- true after the usual normalisation of the inputs
    let total_expected_dropout_loss :=
      ∑ i, GET_AVERAGE probability fun outcome =>
        (labels i - ∑ j, mask j outcome * (feature_values i j * weights j)) ^ 2
    let total_plain_loss :=
      ∑ i, (labels i - ∑ j, feature_values i j * weights j) ^ 2
    let decay_strength           := mask_variance * feature_size  -- more dropout or larger features: stronger decay
    let squared_length_of_weights := ∑ j, weights j ^ 2           -- what weight decay penalises
    let weight_decay := decay_strength * squared_length_of_weights
    total_expected_dropout_loss = total_plain_loss + weight_decay := by
  unfold_named_pieces
  rw [expected_dropout_loss_dataset probability masks_are_square_integrable
    masks_are_independent masks_are_one_on_average masks_have_this_variance]
  -- Every feature has the same size, so it comes out of the sum.
  simp only [features_have_equal_size, ← Finset.mul_sum, mul_assoc]

end Expectation

end SquigglyLine
