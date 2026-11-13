/-
The perceptron, XOR, and no free lunch: nearness to a boundary.

The theorem is about the distance from the data to a line. For a classifier
the line is its boundary, and the distance from the data to the boundary is
called the margin.

Throughout, `inner ℝ direction point` is the dot product of two vectors
(Python: `dot(direction, point)`) and `‖point‖` is the length of a vector.

The margin is a nearest-point distance:
* `abs_inner_le_infDist_flatBoundary` : a point whose score against a unit
  direction is `score` is at least `|score|` from the flat boundary
  (`GET_FLAT_BOUNDARY`).

The perceptron (`GET_PERCEPTRON_WEIGHTS`), which adds each example it gets
wrong:
* `mul_margin_le_inner` : each mistake moves the weights at least `margin`
  along the true direction.
* `norm_sq_perceptronWeights_le` : each mistake adds at most `radius²` to the
  squared size of the weights.
* `perceptron_mistake_bound` : so there are at most `(radius / margin)²`
  mistakes.

XOR (`SEPARATES_XOR`):
* `not_separatesXor_flat` : no flat boundary splits it.
* `separatesXor_lift` : one lifted feature, the product, does.
* `separatesXor_fold` : so does one fold.
* `not_separatesXor_twoScores` : two classes with a softmax are still flat.
* `oneHot_fits` : with one feature per input, any labels are flat. A table
  lookup is a lift.
* `anchorScore_le_iff`, `anchorScore_lt_self` : a flat layer with one score
  per class (`GET_ANCHOR_SCORE`) names the nearest anchor, so it tells any
  distinct points apart.

No free lunch (`FLIP_LABEL_AT`):
* `card_agree_eq_card_disagree` : at an unseen input, any prediction is right
  on exactly half of all possible labellings.
* `mean_sq_error_unseen` : for labels `±1` with no pattern, a prediction
  costs `prediction² + 1` on average, so the flat line at zero is best.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.MetricSpace.HausdorffDistance
import SquigglyLine.Style

namespace SquigglyLine

/-! ### Types -/

/-- A score for each point `(first, second)` of the plane. A classifier
answers by the sign of the score.
Python: `Callable[[float, float], float]`. -/
abbrev ScoreFunction := ℝ → ℝ → ℝ

/-- A yes-or-no label for every input.
Python: `dict[Input, bool]`. -/
abbrev Labelling (Inputs : Type*) := Inputs → Bool

/-! ### The margin is a nearest-point distance -/

section Margin

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

/-- The flat boundary through the origin at right angles to `direction`.
Python: `{point for point in space if dot(direction, point) == 0}`. -/
def GET_FLAT_BOUNDARY
    (direction : Space) : Set Space :=
  {point | inner ℝ direction point = 0}  -- score zero: neither side of the boundary

/-- A point's score is at most its distance to any one point of the
boundary. -/
theorem abs_inner_le_dist_of_mem_flatBoundary
    {direction : Space}
    (direction_is_short : ‖direction‖ ≤ 1)  -- a longer direction would make every score larger
    (point : Space)
    {boundary_point : Space}
    (is_on_boundary : boundary_point ∈ GET_FLAT_BOUNDARY direction) :
    let score    := inner ℝ direction point  -- how far the point reaches along the direction
    let distance := dist point boundary_point
    |score| ≤ distance := by
  unfold_named_pieces
  -- The boundary point has score zero, so taking it away changes nothing.
  have score_ignores_boundary_point :
      inner ℝ direction point
        = inner ℝ direction (point - boundary_point) := by
    rw [inner_sub_right,
      show inner ℝ direction boundary_point = 0 from is_on_boundary, sub_zero]
  rw [score_ignores_boundary_point, dist_eq_norm]
  -- A dot product is at most the two lengths multiplied.
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) direction_is_short)

/-- **The margin is a distance to the boundary.** A point whose score against
a direction of length at most one is `score` lies at least `|score|` from the
flat boundary. -/
theorem abs_inner_le_infDist_flatBoundary
    {direction : Space}
    (direction_is_short : ‖direction‖ ≤ 1)
    (point : Space) :
    let score := inner ℝ direction point
    let distance_to_boundary :=
      Metric.infDist point (GET_FLAT_BOUNDARY direction)  -- to the nearest point of the boundary
    |score| ≤ distance_to_boundary :=
  -- The boundary is not empty (it holds the origin), and the bound holds
  -- against each of its points.
  (Metric.le_infDist ⟨0, by simp [GET_FLAT_BOUNDARY]⟩).2
    fun _ is_on_boundary =>
      abs_inner_le_dist_of_mem_flatBoundary direction_is_short point
        is_on_boundary

end Margin

/-! ### The perceptron -/

section Perceptron

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

/-- The perceptron's weights after `mistake_count` mistakes. `mistakes i` is
the `i`-th example it got wrong, multiplied by its label `±1`. The rule is:
on a mistake, add that to the weights.
Python: `sum(mistakes[i] for i in range(mistake_count))`. -/
def GET_PERCEPTRON_WEIGHTS
    (mistakes : ℕ → Space)
    (mistake_count : ℕ) : Space :=
  ∑ i ∈ Finset.range mistake_count, mistakes i

omit [InnerProductSpace ℝ Space] in
/-- One more mistake adds that example to the weights. -/
theorem perceptronWeights_succ
    (mistakes : ℕ → Space)
    (mistake_count : ℕ) :
    let weights_before := GET_PERCEPTRON_WEIGHTS mistakes mistake_count
    let weights_after  := GET_PERCEPTRON_WEIGHTS mistakes (mistake_count + 1)
    let new_mistake    := mistakes mistake_count  -- counting starts at 0, so this is the next one
    weights_after = weights_before + new_mistake :=
  Finset.sum_range_succ _ _

/-- Each mistake moves the weights at least `margin` along the true
direction. -/
theorem mul_margin_le_inner
    {mistakes : ℕ → Space}
    {true_direction : Space}
    {margin : ℝ}
    {mistake_count : ℕ}
    (every_example_clears_the_margin :
      ∀ index < mistake_count,
        margin ≤ inner ℝ true_direction (mistakes index)) :  -- each example is at least `margin` on its correct side
    ∀ mistakes_so_far ≤ mistake_count,
      let weights  := GET_PERCEPTRON_WEIGHTS mistakes mistakes_so_far
      let progress := inner ℝ true_direction weights  -- how far the weights have moved along the true direction
      mistakes_so_far * margin ≤ progress := by       -- at least `margin` per mistake
  unfold_named_pieces
  intro mistakes_so_far
  induction mistakes_so_far with
  | zero => intro _; simp [GET_PERCEPTRON_WEIGHTS]
  | succ mistakes_so_far progress_until_now =>
    intro within_count
    have earlier_progress :=
      progress_until_now (Nat.le_of_succ_le within_count)
    have new_mistake_clears_the_margin :=
      every_example_clears_the_margin mistakes_so_far within_count
    -- The new weights are the old weights plus the new mistake, and the
    -- score of a sum is the sum of the scores.
    rw [perceptronWeights_succ, inner_add_right]
    push_cast
    linarith

/-- Each mistake adds at most `radius²` to the squared size of the weights,
because the example was on the wrong side. -/
theorem norm_sq_perceptronWeights_le
    {mistakes : ℕ → Space}
    {radius : ℝ}
    {mistake_count : ℕ}
    (every_example_was_a_mistake :
      ∀ index < mistake_count,
        inner ℝ (GET_PERCEPTRON_WEIGHTS mistakes index) (mistakes index) ≤ 0)  -- the weights of that moment got it wrong
    (every_example_is_within_radius :
      ∀ index < mistake_count, ‖mistakes index‖ ≤ radius) :
    ∀ mistakes_so_far ≤ mistake_count,
      let weights      := GET_PERCEPTRON_WEIGHTS mistakes mistakes_so_far
      let squared_size := ‖weights‖ ^ 2
      let size_limit   := mistakes_so_far * radius ^ 2  -- at most `radius²` per mistake
      squared_size ≤ size_limit := by
  unfold_named_pieces
  intro mistakes_so_far
  induction mistakes_so_far with
  | zero => intro _; simp [GET_PERCEPTRON_WEIGHTS]
  | succ mistakes_so_far size_until_now =>
    intro within_count
    have earlier_size := size_until_now (Nat.le_of_succ_le within_count)
    have new_mistake_was_wrong :=
      every_example_was_a_mistake mistakes_so_far within_count
    have new_mistake_is_small :
        ‖mistakes mistakes_so_far‖ ^ 2 ≤ radius ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (every_example_is_within_radius mistakes_so_far within_count) 2
    -- ‖old + new‖² = ‖old‖² + 2 * dot(old, new) + ‖new‖². The middle term
    -- is not positive, because the example was a mistake.
    rw [perceptronWeights_succ, norm_add_sq_real]
    push_cast
    linarith

/-- **The perceptron makes at most `(radius / margin)²` mistakes.** The
examples lie within `radius` of the origin, and some direction of length at
most one scores every one of them at least `margin` on its correct side. -/
theorem perceptron_mistake_bound
    {mistakes : ℕ → Space}
    {true_direction : Space}
    {margin radius : ℝ}
    {mistake_count : ℕ}
    (true_direction_is_short : ‖true_direction‖ ≤ 1)  -- so that `margin` is a distance, not a rescaled one
    (margin_pos : 0 < margin)
    (every_example_clears_the_margin :
      ∀ index < mistake_count,
        margin ≤ inner ℝ true_direction (mistakes index))
    (every_example_was_a_mistake :
      ∀ index < mistake_count,
        inner ℝ (GET_PERCEPTRON_WEIGHTS mistakes index) (mistakes index) ≤ 0)
    (every_example_is_within_radius :
      ∀ index < mistake_count, ‖mistakes index‖ ≤ radius) :
    let mistake_limit := (radius / margin) ^ 2  -- squared: progress grows like the count, size only like its square root
    (mistake_count : ℝ) ≤ mistake_limit := by
  unfold_named_pieces
  rcases Nat.eq_zero_or_pos mistake_count with rfl | mistake_count_pos
  · rw [Nat.cast_zero]
    positivity
  have mistake_count_pos_real : (0 : ℝ) < mistake_count := by
    exact_mod_cast mistake_count_pos
  -- The weights have moved far along the true direction ...
  have progress_is_large :
      mistake_count * margin
        ≤ inner ℝ true_direction
            (GET_PERCEPTRON_WEIGHTS mistakes mistake_count) :=
    mul_margin_le_inner every_example_clears_the_margin mistake_count le_rfl
  -- ... but they are not long ...
  have size_is_small :
      ‖GET_PERCEPTRON_WEIGHTS mistakes mistake_count‖ ^ 2
        ≤ mistake_count * radius ^ 2 :=
    norm_sq_perceptronWeights_le every_example_was_a_mistake
      every_example_is_within_radius mistake_count le_rfl
  -- ... and they cannot have moved further than their own length.
  have progress_le_size :
      inner ℝ true_direction (GET_PERCEPTRON_WEIGHTS mistakes mistake_count)
        ≤ ‖GET_PERCEPTRON_WEIGHTS mistakes mistake_count‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) true_direction_is_short)
  have squares_compare :
      (mistake_count * margin) ^ 2 ≤ mistake_count * radius ^ 2 :=
    (pow_le_pow_left₀ (by positivity)
      (progress_is_large.trans progress_le_size) 2).trans size_is_small
  -- Divide by `mistake_count * margin²`.
  rw [div_pow, le_div_iff₀ (by positivity)]
  refine le_of_mul_le_mul_left ?_ mistake_count_pos_real
  rw [show (mistake_count : ℝ) * (mistake_count * margin ^ 2)
    = (mistake_count * margin) ^ 2 by ring]
  exact squares_compare

end Perceptron

/-! ### XOR -/

section Xor

/-- A score splits XOR when it is negative at `(0, 0)` and `(1, 1)` and
positive at `(0, 1)` and `(1, 0)`.
Python: `score(0, 0) < 0 and score(1, 1) < 0 and score(0, 1) > 0 and
score(1, 0) > 0`. -/
def SEPARATES_XOR
    (score : ScoreFunction) : Prop :=
  let is_negative_at_0_0 := score 0 0 < 0  -- XOR of equal inputs is 0: the negative class
  let is_negative_at_1_1 := score 1 1 < 0
  let is_positive_at_0_1 := 0 < score 0 1  -- XOR of different inputs is 1: the positive class
  let is_positive_at_1_0 := 0 < score 1 0
  is_negative_at_0_0 ∧ is_negative_at_1_1 ∧
    is_positive_at_0_1 ∧ is_positive_at_1_0

/-- **No flat boundary splits XOR.** -/
theorem not_separatesXor_flat
    (first_weight second_weight bias : ℝ) :
    let flat_score : ScoreFunction := fun first second =>
      first_weight * first + second_weight * second + bias  -- zero along a straight line
    ¬SEPARATES_XOR flat_score := by
  unfold_named_pieces
  intro separates
  obtain ⟨negative_at_0_0, negative_at_1_1, positive_at_0_1, positive_at_1_0⟩ :=
    separates
  norm_num at negative_at_0_0 negative_at_1_1 positive_at_0_1 positive_at_1_0
  -- The scores at (0, 0) and (1, 1) add up to the same number as the scores
  -- at (0, 1) and (1, 0). One sum is negative and the other positive.
  linarith

/-- **One lifted feature is enough.** With the product `first * second` as a
third feature, the boundary is flat. -/
theorem separatesXor_lift :
    let lifted_score : ScoreFunction := fun first second =>
      let product := first * second          -- the lifted feature: 1 only at (1, 1)
      first + second - 2 * product - 1 / 2   -- 0, 1, 1, 0 at the four corners, then 1/2 taken off
    SEPARATES_XOR lifted_score := by
  unfold_named_pieces
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **One fold is enough.** Fold the plane along the line `first = second`. -/
theorem separatesXor_fold :
    let folded_score : ScoreFunction := fun first second =>
      |first - second| - 1 / 2  -- the fold `|·|` is 0 on equal inputs and 1 on different ones
    SEPARATES_XOR folded_score := by
  unfold_named_pieces
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **Two classes with a softmax are still flat.** With one flat score per
class, the answer changes where the two scores are equal, and that is again a
flat boundary. -/
theorem not_separatesXor_twoScores
    (first_weight_0 second_weight_0 bias_0 : ℝ)
    (first_weight_1 second_weight_1 bias_1 : ℝ) :
    let score_difference : ScoreFunction := fun first second =>
      let score_of_class_1 :=
        first_weight_1 * first + second_weight_1 * second + bias_1
      let score_of_class_0 :=
        first_weight_0 * first + second_weight_0 * second + bias_0
      score_of_class_1 - score_of_class_0  -- softmax picks class 1 exactly when this is positive
    ¬SEPARATES_XOR score_difference := by
  unfold_named_pieces
  intro separates
  obtain ⟨negative_at_0_0, negative_at_1_1, positive_at_0_1, positive_at_1_0⟩ :=
    separates
  norm_num at negative_at_0_0 negative_at_1_1 positive_at_0_1 positive_at_1_0
  linarith

/-- **A table lookup is a lift that fits anything.** Give every input its own
feature, one for that input and zero for the rest. Then any labels at all are
a flat function of the features: the weights are the labels. -/
theorem oneHot_fits
    {Inputs : Type*}
    [Fintype Inputs]
    [DecidableEq Inputs]
    (labels : Inputs → ℝ)
    (input : Inputs) :
    let one_hot_features : Inputs → ℝ := Pi.single input (1 : ℝ)  -- 1 at `input`, 0 at every other input
    let flat_output := ∑ i, labels i * one_hot_features i         -- weight `labels i` on feature `i`
    flat_output = labels input := by
  unfold_named_pieces
  simp [Pi.single_apply]

end Xor

/-! ### Naming the nearest anchor -/

section Anchors

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

/-- A flat score for the anchor point `anchor`, read at the input `input`.
Python: `2 * dot(anchor, input) - norm(anchor) ** 2`. -/
def GET_ANCHOR_SCORE
    (anchor input : Space) : ℝ :=
  2 * inner ℝ anchor input - ‖anchor‖ ^ 2  -- flat in `input`; equal to ‖input‖² - ‖input - anchor‖² (`anchorScore_eq`)

/-- The anchor score is the squared size of the input minus the squared
distance from the input to the anchor. -/
theorem anchorScore_eq
    (anchor input : Space) :
    let score              := GET_ANCHOR_SCORE anchor input
    let input_size_squared := ‖input‖ ^ 2           -- the same for every anchor, so it does not change which score is highest
    let distance_squared   := ‖input - anchor‖ ^ 2
    score = input_size_squared - distance_squared := by
  unfold_named_pieces
  rw [GET_ANCHOR_SCORE, norm_sub_sq_real, real_inner_comm input anchor]
  ring

/-- **A flat layer with one score per class names the nearest anchor.** The
anchor with the highest score is the one nearest to the input. -/
theorem anchorScore_le_iff
    (anchor other_anchor input : Space) :
    let anchor_scores_at_least_as_high :=
      GET_ANCHOR_SCORE other_anchor input ≤ GET_ANCHOR_SCORE anchor input
    let anchor_is_at_least_as_near :=
      ‖input - anchor‖ ≤ ‖input - other_anchor‖
    anchor_scores_at_least_as_high ↔ anchor_is_at_least_as_near := by
  unfold_named_pieces
  rw [anchorScore_eq, anchorScore_eq, sub_le_sub_iff_left,
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]

/-- So it tells any set of distinct points apart: at an anchor, its own score
is the highest. This names the point. It does not compute anything about
it. -/
theorem anchorScore_lt_self
    {anchor other_anchor : Space}
    (anchors_differ : other_anchor ≠ anchor) :
    let score_of_other_anchor := GET_ANCHOR_SCORE other_anchor anchor  -- both scores are read at the point `anchor` itself
    let score_of_own_anchor   := GET_ANCHOR_SCORE anchor anchor
    score_of_other_anchor < score_of_own_anchor := by
  unfold_named_pieces
  have anchors_are_apart : 0 < ‖anchor - other_anchor‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr anchors_differ.symm)
  -- The own anchor is at distance zero. The other one is further away.
  rw [anchorScore_eq, anchorScore_eq, sub_self, norm_zero,
    zero_pow two_ne_zero, sub_zero]
  linarith [pow_pos anchors_are_apart 2]

end Anchors

/-! ### No free lunch -/

section NoFreeLunch

variable {Inputs : Type*} [Fintype Inputs] [DecidableEq Inputs]

/-- Change a labelling at the one input `input`.
Python: `{**labels, input: not labels[input]}`. -/
def FLIP_LABEL_AT
    (input : Inputs)
    (labels : Labelling Inputs) : Labelling Inputs :=
  Function.update labels input !labels input

omit [Fintype Inputs] in
/-- After the flip, the label at that input is the opposite. -/
theorem flipAt_apply_self
    (input : Inputs)
    (labels : Labelling Inputs) :
    let flipped_labels := FLIP_LABEL_AT input labels
    flipped_labels input = !labels input := by
  unfold_named_pieces
  simp [FLIP_LABEL_AT]

omit [Fintype Inputs] in
/-- Flipping twice gives back the labelling you started with. -/
theorem flipAt_flipAt
    (input : Inputs)
    (labels : Labelling Inputs) :
    let flipped_once  := FLIP_LABEL_AT input labels
    let flipped_twice := FLIP_LABEL_AT input flipped_once
    flipped_twice = labels := by
  unfold_named_pieces
  simp [FLIP_LABEL_AT]

/-- **No free lunch.** Fix an unseen input `input` and any guess for its
label. Of all the ways to label the inputs, exactly as many agree with the
guess at `input` as disagree. -/
theorem card_agree_eq_card_disagree
    (input : Inputs)
    (guess : Bool) :
    let labellings_that_agree :=
      Finset.univ.filter fun labels : Labelling Inputs => labels input = guess
    let labellings_that_disagree :=
      Finset.univ.filter fun labels : Labelling Inputs => labels input ≠ guess
    labellings_that_agree.card = labellings_that_disagree.card := by  -- `.card` counts: Python `len`
  unfold_named_pieces
  -- Flipping the label at `input` turns each labelling that agrees into one
  -- that disagrees, and back. So the two groups pair up.
  refine Finset.card_nbij' (FLIP_LABEL_AT input) (FLIP_LABEL_AT input)
    ?_ ?_ ?_ ?_
  · intro labels labels_in_agreeing_group
    have labels_agree : labels input = guess := by
      simpa using labels_in_agreeing_group
    simp [flipAt_apply_self, labels_agree]
  · intro labels labels_in_disagreeing_group
    have labels_disagree : labels input ≠ guess := by
      simpa using labels_in_disagreeing_group
    cases label_here : labels input <;> cases guess <;>
      simp_all [flipAt_apply_self]
  · intro labels _
    exact flipAt_flipAt input labels
  · intro labels _
    exact flipAt_flipAt input labels

/-- **With no pattern in the labels, flat is best.** If an unseen label is
`+1` or `-1` with equal chance, a prediction `prediction` has mean squared
error `prediction² + 1`. Any move away from zero, in either direction, only
adds. -/
theorem mean_sq_error_unseen
    (prediction : ℝ) :
    let error_if_label_is_plus_1  := (prediction - 1) ^ 2
    let error_if_label_is_minus_1 := (prediction + 1) ^ 2  -- prediction - (-1)
    let mean_squared_error :=
      (error_if_label_is_plus_1 + error_if_label_is_minus_1) / 2  -- each label has chance 1/2
    let cost_of_prediction := prediction ^ 2 + 1  -- smallest at prediction = 0, where it is 1
    mean_squared_error = cost_of_prediction := by
  unfold_named_pieces
  ring

end NoFreeLunch

end SquigglyLine
