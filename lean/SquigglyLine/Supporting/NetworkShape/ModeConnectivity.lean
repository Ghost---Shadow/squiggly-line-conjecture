/-
Mode connectivity: when two fits are joined by a straight line.

For a model that is linear in its weights:
* `residual_along_between` : on the straight line between two settings of the
  weights, the error is the matching blend of the two errors.
* `fit_along` : the line between two fits is all fits.
* `no_barrier` : the error on the line is never larger than at the worse end.

For the smallest model with depth, output `first_weight * second_weight`:
* `twoLayer_along` : on the line between two fits the output is off by
  exactly `fraction * (1 - fraction)
  * ((first_a - second_a) * (first_b - second_b))`.
* `twoLayer_flip` : flipping both signs gives the same function.
* `twoLayer_midpoint_mirror` : halfway between a fit and its mirror image the
  output is zero. The hill comes from writing one function in two ways.
-/
import Mathlib.Tactic.LinearCombination
import SquigglyLine.Networks.LinearModel

namespace SquigglyLine

/-! ### Linear in the weights: one flat valley -/

section Linear

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [NormedSpace ℝ Weights]
  [NormedAddCommGroup Outputs] [NormedSpace ℝ Outputs]
  (predict : LinearPredictor Weights Outputs) (labels : Outputs)
  (start_weights end_weights : Weights)

/-- On the straight line between two settings of the weights, the error is the
matching blend of the two errors. -/
theorem residual_along_between
    (fraction : ℝ) :
    let weights_on_path  := MOVE_ALONG start_weights end_weights fraction
    let residual_on_path := GET_RESIDUAL predict labels weights_on_path
    let start_residual   := GET_RESIDUAL predict labels start_weights
    let end_residual     := GET_RESIDUAL predict labels end_weights
    let blended_residual :=
      (1 - fraction) • start_residual + fraction • end_residual  -- the same shares of the path, now of the two errors
    residual_on_path = blended_residual := by
  unfold_named_pieces
  -- The model is linear, so its outputs blend like the weights do.
  simp only [GET_RESIDUAL, MOVE_ALONG, map_add, map_smul, map_sub]
  module

/-- **The line between two fits is all fits.** -/
theorem fit_along
    (start_fits : predict start_weights = labels)
    (end_fits : predict end_weights = labels)
    (fraction : ℝ) :
    let weights_on_path := MOVE_ALONG start_weights end_weights fraction
    let output_on_path  := predict weights_on_path
    output_on_path = labels := by
  unfold_named_pieces
  simp only [MOVE_ALONG, map_add, map_smul, map_sub, start_fits, end_fits,
    sub_self, smul_zero, add_zero]

/-- **There is never a hill.** Anywhere on the line, the error is no larger
than at the worse of the two ends. -/
theorem no_barrier
    {fraction : ℝ}
    (fraction_nonneg : 0 ≤ fraction)
    (fraction_le_one : fraction ≤ 1) :
    let weights_on_path := MOVE_ALONG start_weights end_weights fraction
    let error_on_path   := ‖GET_RESIDUAL predict labels weights_on_path‖
    let start_error     := ‖GET_RESIDUAL predict labels start_weights‖
    let end_error       := ‖GET_RESIDUAL predict labels end_weights‖
    let worse_end_error := max start_error end_error
    error_on_path ≤ worse_end_error := by
  unfold_named_pieces
  have error_is_blend :
      GET_RESIDUAL predict labels
          (MOVE_ALONG start_weights end_weights fraction)
        = (1 - fraction) • GET_RESIDUAL predict labels start_weights
          + fraction • GET_RESIDUAL predict labels end_weights :=
    residual_along_between predict labels start_weights end_weights fraction
  rw [error_is_blend]
  -- The size of a blend is at most the blend of the sizes, and a blend of two
  -- numbers is at most the larger of them.
  calc ‖(1 - fraction) • GET_RESIDUAL predict labels start_weights
        + fraction • GET_RESIDUAL predict labels end_weights‖
      ≤ ‖(1 - fraction) • GET_RESIDUAL predict labels start_weights‖
        + ‖fraction • GET_RESIDUAL predict labels end_weights‖ :=
        norm_add_le _ _
    _ = (1 - fraction) * ‖GET_RESIDUAL predict labels start_weights‖
        + fraction * ‖GET_RESIDUAL predict labels end_weights‖ := by
        rw [norm_smul, norm_smul,
          Real.norm_of_nonneg (sub_nonneg.mpr fraction_le_one),
          Real.norm_of_nonneg fraction_nonneg]
    _ ≤ (1 - fraction) * max ‖GET_RESIDUAL predict labels start_weights‖
            ‖GET_RESIDUAL predict labels end_weights‖
        + fraction * max ‖GET_RESIDUAL predict labels start_weights‖
            ‖GET_RESIDUAL predict labels end_weights‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _)
            (sub_nonneg.mpr fraction_le_one))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) fraction_nonneg)
    _ = max ‖GET_RESIDUAL predict labels start_weights‖
          ‖GET_RESIDUAL predict labels end_weights‖ := by ring

end Linear

/-! ### Two weights multiplied: the smallest hill -/

section TwoLayer

/-- **The hill, exactly.** Take two fits `(first_a, first_b)` and
`(second_a, second_b)` of the target `target` by the model `a * b`. A
fraction `fraction` of the way along the straight line between them, the
output is off by
`fraction * (1 - fraction) * ((first_a - second_a) * (first_b - second_b))`.
-/
theorem twoLayer_along
    {first_a first_b second_a second_b target : ℝ}
    (first_fits : first_a * first_b = target)
    (second_fits : second_a * second_b = target)
    (fraction : ℝ) :
    let blended_a      := (1 - fraction) * first_a + fraction * second_a
    let blended_b      := (1 - fraction) * first_b + fraction * second_b
    let output         := blended_a * blended_b
    let hill           :=
      fraction * (1 - fraction)
        * ((first_a - second_a) * (first_b - second_b))  -- largest halfway along, zero at both fits
    let expected_output := target - hill
    output = expected_output := by
  unfold_named_pieces
  linear_combination (1 - fraction) * first_fits + fraction * second_fits

/-- **A mirror image is the same function.** -/
theorem twoLayer_flip
    (first_weight : ℝ)
    (second_weight : ℝ) :
    let flipped_output := -first_weight * -second_weight  -- both signs flipped
    let output         := first_weight * second_weight
    flipped_output = output := by
  unfold_named_pieces
  exact neg_mul_neg first_weight second_weight

/-- **Halfway to the mirror image, everything is lost.** The output is zero,
whatever the target was. -/
theorem twoLayer_midpoint_mirror
    (first_weight : ℝ)
    (second_weight : ℝ) :
    let fraction : ℝ := 1 / 2  -- halfway along the line
    let first_at_midpoint  :=
      (1 - fraction) * first_weight + fraction * -first_weight    -- the weight and its mirror image, blended
    let second_at_midpoint :=
      (1 - fraction) * second_weight + fraction * -second_weight
    let output := first_at_midpoint * second_at_midpoint
    output = 0 := by
  unfold_named_pieces
  ring

end TwoLayer

end SquigglyLine
