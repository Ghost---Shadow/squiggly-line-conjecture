/-
Neural collapse: why the classes end up on a simplex.

`arrows i` is the arrow for class `i`, of length one. `class_count` is the
number of classes. The overlap of two arrows is their dot product, written
`inner ℝ`. For arrows of length one it is the cosine of the angle between
them.

* `norm_sum_sq_eq_sum_inner` : the squared length of the sum of the arrows is
  the sum of all their overlaps.
* `neg_one_le_of_inner_le` : if every pair of arrows has overlap at most
  `overlap_limit`, then `(class_count - 1) * overlap_limit ≥ -1`. No
  arrangement is farther apart than the simplex.
* `norm_sum_sq_of_equiangular` : if every pair has overlap exactly `overlap`,
  the squared length of the sum is
  `class_count * (1 + (class_count - 1) * overlap)`.
* `sum_eq_zero_iff_of_equiangular` : so evenly spread arrows reach the limit
  exactly when they add up to zero.

| Name                         | Meaning                                    |
|------------------------------|--------------------------------------------|
| `ClassArrows Classes Space`  | one arrow for each class                   |
| `inner ℝ arrow other_arrow`  | the overlap (dot product) of two arrows    |
| `Fintype.card Classes`       | the number of classes                      |
| `(univ).erase this_class`    | all the classes but this one               |
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import SquigglyLine.Style

namespace SquigglyLine

open Finset

/-- One arrow for each class.
Python: `dict[Class, Vector]`. -/
abbrev ClassArrows (Classes Space : Type*) := Classes → Space

variable {Space Classes : Type*}
  [NormedAddCommGroup Space] [InnerProductSpace ℝ Space] [Fintype Classes]

/-- The squared length of a sum is the sum of all the overlaps. -/
theorem norm_sum_sq_eq_sum_inner
    (arrows : ClassArrows Classes Space) :
    let sum_of_arrows         := ∑ i, arrows i
    let squared_length_of_sum := ‖sum_of_arrows‖ ^ 2
    let sum_of_all_overlaps   :=
      ∑ i, ∑ j, inner ℝ (arrows i) (arrows j)                      -- every pair `(i, j)`, an arrow with itself included
    squared_length_of_sum = sum_of_all_overlaps := by              -- `(a + b) · (a + b)` multiplied out, for any number of arrows
  unfold_named_pieces
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum]

variable [DecidableEq Classes]

/-- All the classes but one: there are `class_count - 1` of them. -/
theorem card_erase_univ_add_one
    (this_class : Classes) :
    let other_classes     := (univ : Finset Classes).erase this_class
    let other_class_count : ℝ := other_classes.card
    let class_count : ℝ   := Fintype.card Classes
    other_class_count + 1 = class_count := by
  unfold_named_pieces
  exact_mod_cast card_erase_add_one (mem_univ this_class)

/-- One arrow's overlaps with all the arrows: its own length, then the
others. -/
theorem sum_inner_eq_one_add
    {arrows : ClassArrows Classes Space}
    (arrows_have_length_one : ∀ this_class, ‖arrows this_class‖ = 1)
    (this_class : Classes) :
    let other_classes       := (univ : Finset Classes).erase this_class
    let overlap_with_all    :=
      ∑ j, inner ℝ (arrows this_class) (arrows j)
    let overlap_with_others :=
      ∑ j ∈ other_classes, inner ℝ (arrows this_class) (arrows j)
    overlap_with_all = 1 + overlap_with_others := by               -- the 1 is the arrow's overlap with itself: its length squared
  unfold_named_pieces
  rw [← add_sum_erase _ _ (mem_univ this_class),
    real_inner_self_eq_norm_sq, arrows_have_length_one this_class, one_pow]

/-- If every pair of arrows has overlap at most `overlap_limit`, their sum is
short. -/
theorem norm_sum_sq_le_of_inner_le
    {arrows : ClassArrows Classes Space}
    (arrows_have_length_one : ∀ this_class, ‖arrows this_class‖ = 1)
    {overlap_limit : ℝ}
    (overlaps_at_most_limit :
      ∀ this_class other_class, this_class ≠ other_class →
        inner ℝ (arrows this_class) (arrows other_class) ≤ overlap_limit) :
    let class_count : ℝ       := Fintype.card Classes
    let squared_length_of_sum := ‖∑ i, arrows i‖ ^ 2
    let overlaps_of_one_arrow :=
      1 + (class_count - 1) * overlap_limit                        -- 1 with itself, at most the limit with each of the others
    squared_length_of_sum ≤ class_count * overlaps_of_one_arrow := by  -- the same bound for each of the `class_count` arrows
  unfold_named_pieces
  rw [norm_sum_sq_eq_sum_inner]
  calc ∑ i, ∑ j, inner ℝ (arrows i) (arrows j)
      ≤ ∑ _i : Classes,
          (1 + (Fintype.card Classes - 1) * overlap_limit) := by
        -- Bound the overlaps of one arrow at a time.
        refine sum_le_sum fun this_class _ => ?_
        have others_at_most_limit :
            ∑ j ∈ (univ : Finset Classes).erase this_class,
                inner ℝ (arrows this_class) (arrows j)
              ≤ ∑ _j ∈ (univ : Finset Classes).erase this_class,
                  overlap_limit :=
          sum_le_sum fun other_class other_class_is_another =>
            overlaps_at_most_limit this_class other_class
              (ne_of_mem_erase other_class_is_another).symm
        have other_count_add_one :
            (((univ : Finset Classes).erase this_class).card : ℝ) + 1
              = Fintype.card Classes :=
          card_erase_univ_add_one this_class
        rw [sum_const, nsmul_eq_mul,
          show (((univ : Finset Classes).erase this_class).card : ℝ)
              = Fintype.card Classes - 1 by linarith]
          at others_at_most_limit
        rw [sum_inner_eq_one_add arrows_have_length_one this_class]
        linarith
    _ = Fintype.card Classes
          * (1 + (Fintype.card Classes - 1) * overlap_limit) := by
        rw [sum_const, card_univ, nsmul_eq_mul]

/-- **The simplex is as far apart as arrows can get.** For `class_count`
arrows of length one, if every pair has overlap at most `overlap_limit`, then
`(class_count - 1) * overlap_limit ≥ -1`. -/
theorem neg_one_le_of_inner_le
    [Nonempty Classes]
    {arrows : ClassArrows Classes Space}
    (arrows_have_length_one : ∀ this_class, ‖arrows this_class‖ = 1)
    {overlap_limit : ℝ}
    (overlaps_at_most_limit :
      ∀ this_class other_class, this_class ≠ other_class →
        inner ℝ (arrows this_class) (arrows other_class) ≤ overlap_limit) :
    let class_count : ℝ   := Fintype.card Classes
    let other_class_count := class_count - 1
    let lowest_possible : ℝ := -1                                  -- the simplex: every overlap is `-1 / other_class_count`
    lowest_possible ≤ other_class_count * overlap_limit := by      -- a squared length is never negative
  unfold_named_pieces
  have class_count_pos : (0 : ℝ) < Fintype.card Classes := by
    exact_mod_cast Fintype.card_pos
  have sum_is_short :
      ‖∑ i, arrows i‖ ^ 2 ≤ Fintype.card Classes
        * (1 + (Fintype.card Classes - 1) * overlap_limit) :=
    norm_sum_sq_le_of_inner_le arrows_have_length_one overlaps_at_most_limit
  -- Below -1, the bound on the squared length of the sum would be negative.
  by_contra limit_is_below
  have overlaps_of_one_arrow_neg :
      1 + (Fintype.card Classes - 1) * overlap_limit < 0 := by
    linarith [not_le.mp limit_is_below]
  have bound_is_negative :=
    mul_neg_of_pos_of_neg class_count_pos overlaps_of_one_arrow_neg
  linarith [sq_nonneg ‖∑ i, arrows i‖]

/-- If every pair of arrows has overlap exactly `overlap`, the squared length
of their sum is `class_count * (1 + (class_count - 1) * overlap)`. -/
theorem norm_sum_sq_of_equiangular
    {arrows : ClassArrows Classes Space}
    (arrows_have_length_one : ∀ this_class, ‖arrows this_class‖ = 1)
    {overlap : ℝ}
    (overlaps_all_equal :
      ∀ this_class other_class, this_class ≠ other_class →
        inner ℝ (arrows this_class) (arrows other_class) = overlap) :
    let class_count : ℝ       := Fintype.card Classes
    let squared_length_of_sum := ‖∑ i, arrows i‖ ^ 2
    let overlaps_of_one_arrow :=
      1 + (class_count - 1) * overlap                              -- 1 with itself, `overlap` with each of the others
    squared_length_of_sum = class_count * overlaps_of_one_arrow := by
  unfold_named_pieces
  rw [norm_sum_sq_eq_sum_inner]
  calc ∑ i, ∑ j, inner ℝ (arrows i) (arrows j)
      = ∑ _i : Classes, (1 + (Fintype.card Classes - 1) * overlap) := by
        -- Add up the overlaps of one arrow at a time.
        refine sum_congr rfl fun this_class _ => ?_
        have others_all_equal :
            ∑ j ∈ (univ : Finset Classes).erase this_class,
                inner ℝ (arrows this_class) (arrows j)
              = ∑ _j ∈ (univ : Finset Classes).erase this_class,
                  overlap :=
          sum_congr rfl fun other_class other_class_is_another =>
            overlaps_all_equal this_class other_class
              (ne_of_mem_erase other_class_is_another).symm
        have other_count_add_one :
            (((univ : Finset Classes).erase this_class).card : ℝ) + 1
              = Fintype.card Classes :=
          card_erase_univ_add_one this_class
        rw [sum_const, nsmul_eq_mul,
          show (((univ : Finset Classes).erase this_class).card : ℝ)
              = Fintype.card Classes - 1 by linarith]
          at others_all_equal
        rw [sum_inner_eq_one_add arrows_have_length_one this_class,
          others_all_equal]
    _ = Fintype.card Classes
          * (1 + (Fintype.card Classes - 1) * overlap) := by
        rw [sum_const, card_univ, nsmul_eq_mul]

/-- **The farthest-apart arrangement is the centred one.** Evenly spread
arrows of length one reach the limit `(class_count - 1) * overlap = -1`
exactly when they add up to zero. -/
theorem sum_eq_zero_iff_of_equiangular
    [Nonempty Classes]
    {arrows : ClassArrows Classes Space}
    (arrows_have_length_one : ∀ this_class, ‖arrows this_class‖ = 1)
    {overlap : ℝ}
    (overlaps_all_equal :
      ∀ this_class other_class, this_class ≠ other_class →
        inner ℝ (arrows this_class) (arrows other_class) = overlap) :
    let class_count : ℝ          := Fintype.card Classes
    let arrows_add_up_to_zero    := ∑ i, arrows i = 0              -- the arrows are centred: they balance around the origin
    let overlap_is_at_the_limit  := (class_count - 1) * overlap = -1  -- the simplex: `overlap = -1 / (class_count - 1)`
    arrows_add_up_to_zero ↔ overlap_is_at_the_limit := by
  unfold_named_pieces
  have class_count_pos : (0 : ℝ) < Fintype.card Classes := by
    exact_mod_cast Fintype.card_pos
  have squared_length_of_sum :
      ‖∑ i, arrows i‖ ^ 2 = Fintype.card Classes
        * (1 + (Fintype.card Classes - 1) * overlap) :=
    norm_sum_sq_of_equiangular arrows_have_length_one overlaps_all_equal
  constructor
  · -- A zero sum has zero length, and `class_count` is not zero.
    intro sum_is_zero
    rw [sum_is_zero, norm_zero] at squared_length_of_sum
    have overlaps_of_one_arrow_zero :
        1 + (Fintype.card Classes - 1) * overlap = 0 := by
      rcases mul_eq_zero.mp
        (by linarith : (Fintype.card Classes : ℝ)
          * (1 + (Fintype.card Classes - 1) * overlap) = 0)
        with class_count_zero | overlaps_zero
      · linarith
      · exact overlaps_zero
    linarith
  · -- At the limit the squared length of the sum is zero.
    intro overlap_at_limit
    have squared_length_zero : ‖∑ i, arrows i‖ ^ 2 = 0 := by
      rw [squared_length_of_sum,
        show 1 + (Fintype.card Classes - 1) * overlap = 0 by linarith,
        mul_zero]
    exact norm_eq_zero.mp
      ((pow_eq_zero_iff two_ne_zero).mp squared_length_zero)

end SquigglyLine
