/-
Two facts about averages: the median, and random directions.

* **The median.** Squared error is least at the mean (`Averaging.lean`).
  Absolute error is least at a median: a value with at most half the points
  below it and at most half above.
* **Random directions are nearly at right angles, on average.** If the
  coordinates of a random direction are uncorrelated, each with mean square
  `mean_square`, its overlap with a fixed direction has mean square
  `mean_square` times the squared length of that direction. With
  `mean_square = 1 / dimension` and a direction of length one that is
  `1 / dimension`: the more dimensions, the smaller the overlap.

Theorems:
* `sum_abs_sub_le_of_le`   moving a centre up from a value with at most half
                           the points above it does not lower the error;
* `sum_abs_sub_median_le`  absolute error is least at a median;
* `sum_mul_sq_overlap`     the mean square overlap of a random direction.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import SquigglyLine.Style

namespace SquigglyLine

/-- A random vector: for each outcome, one number per coordinate.
Python: `vector[outcome][coordinate]`. -/
abbrev RandomVector (Outcomes Coordinates : Type*) :=
  Outcomes → Coordinates → ℝ

variable {Points : Type*} [Fintype Points]

/-- Moving a centre up, away from a value that has at most half the points
above it, does not lower the summed absolute error. -/
theorem sum_abs_sub_le_of_le
    (values : Points → ℝ)
    {centre other_centre : ℝ}
    (few_above :
      2 * (Finset.univ.filter fun i => centre < values i).card
        ≤ Fintype.card Points)  -- at most half the points lie above the centre
    (centre_le_other : centre ≤ other_centre) :
    let centre_error := ∑ i, |values i - centre|
    let other_error  := ∑ i, |values i - other_centre|
    centre_error ≤ other_error := by
  unfold_named_pieces
  -- A point at or below `centre` ends up `other_centre - centre` further; a
  -- point above ends up at most that much nearer.
  have shift_effect : ∀ i,
      |values i - centre|
          + (other_centre - centre)
            * (1 - 2 * (if centre < values i then (1 : ℝ) else 0))
        ≤ |values i - other_centre| := by
    intro i
    split_ifs with is_above <;>
      rcases abs_cases (values i - centre) with ⟨centre_cases, _⟩
        | ⟨centre_cases, _⟩ <;>
      rcases abs_cases (values i - other_centre) with ⟨other_cases, _⟩
        | ⟨other_cases, _⟩ <;>
      linarith
  have summed_effect :=
    Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => shift_effect i
  have above_count :
      ∑ i, (if centre < values i then (1 : ℝ) else 0)
        = ((Finset.univ.filter fun i => centre < values i).card : ℝ) := by
    rw [Finset.sum_boole]
  have shift_sum :
      ∑ i, (other_centre - centre)
          * (1 - 2 * (if centre < values i then (1 : ℝ) else 0))
        = (other_centre - centre)
          * (Fintype.card Points
            - 2 * (Finset.univ.filter fun i => centre < values i).card) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
      above_count]
    simp
  rw [Finset.sum_add_distrib, shift_sum] at summed_effect
  have few_above_real :
      (2 * (Finset.univ.filter fun i => centre < values i).card : ℝ)
        ≤ Fintype.card Points := by
    exact_mod_cast few_above
  have shift_sum_nonneg :
      0 ≤ (other_centre - centre)
        * ((Fintype.card Points : ℝ)
          - 2 * (Finset.univ.filter fun i => centre < values i).card) :=
    mul_nonneg (sub_nonneg.mpr centre_le_other)
      (sub_nonneg.mpr few_above_real)
  linarith

/-- **Absolute error is least at a median.** If at most half the points are
below `centre` and at most half are above it, no other centre has a smaller
summed absolute error. -/
theorem sum_abs_sub_median_le
    (values : Points → ℝ)
    {centre : ℝ}
    (few_below :
      2 * (Finset.univ.filter fun i => values i < centre).card
        ≤ Fintype.card Points)  -- at most half the points lie below the centre
    (few_above :
      2 * (Finset.univ.filter fun i => centre < values i).card
        ≤ Fintype.card Points)  -- at most half the points lie above the centre
    (other_centre : ℝ) :
    let centre_error := ∑ i, |values i - centre|
    let other_error  := ∑ i, |values i - other_centre|
    centre_error ≤ other_error := by
  unfold_named_pieces
  rcases le_total centre other_centre with centre_le_other | other_le_centre
  · exact sum_abs_sub_le_of_le values few_above centre_le_other
  · -- Turn the line over: "below" becomes "above".
    have flipped_few_above :
        2 * (Finset.univ.filter fun i => -centre < -values i).card
          ≤ Fintype.card Points := by
      simpa using few_below
    have flipped_bound :
        ∑ i, |(fun i => -values i) i - -centre|
          ≤ ∑ i, |(fun i => -values i) i - -other_centre| :=
      sum_abs_sub_le_of_le (fun i => -values i) flipped_few_above
        (neg_le_neg other_le_centre)
    have flip_invariant : ∀ any_centre : ℝ,
        ∑ i, |-values i - -any_centre| = ∑ i, |values i - any_centre| :=
      fun any_centre => Finset.sum_congr rfl fun i _ => by
        rw [← abs_neg]
        ring_nf
    simp only [] at flipped_bound
    rwa [flip_invariant, flip_invariant] at flipped_bound

variable {Coordinates : Type*} [Fintype Coordinates]
  {Outcomes : Type*} [Fintype Outcomes] [DecidableEq Coordinates]

/-- **Random directions are nearly at right angles, on average.** Let
`vector` be a random vector, taking the value `vector outcome` with chance
`chance outcome`, whose coordinates are uncorrelated with mean square
`mean_square`. Its overlap with a fixed vector `direction` has mean square
`mean_square` times the squared length of `direction`. -/
theorem sum_mul_sq_overlap
    {chance : Outcomes → ℝ}
    {vector : RandomVector Outcomes Coordinates}
    {mean_square : ℝ}
    (uncorrelated :
      ∀ i j, ∑ outcome, chance outcome * (vector outcome i * vector outcome j)
        = if i = j then mean_square else 0)  -- each coordinate has mean square `mean_square`; distinct ones average to zero
    (direction : Coordinates → ℝ) :
    let overlap_mean_square :=
      ∑ outcome, chance outcome
        * (∑ i, direction i * vector outcome i) ^ 2
    let predicted := mean_square * ∑ i, direction i ^ 2
    overlap_mean_square = predicted := by
  unfold_named_pieces
  -- Squaring the overlap gives one term for every pair of coordinates.
  have square_expands : ∀ outcome,
      chance outcome * (∑ i, direction i * vector outcome i) ^ 2
        = ∑ i, ∑ j, direction i * direction j
          * (chance outcome * (vector outcome i * vector outcome j)) := by
    intro outcome
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  calc ∑ outcome, chance outcome
        * (∑ i, direction i * vector outcome i) ^ 2
      = ∑ outcome, ∑ i, ∑ j, direction i * direction j
          * (chance outcome * (vector outcome i * vector outcome j)) :=
        Finset.sum_congr rfl fun outcome _ => square_expands outcome
    _ = ∑ i, ∑ j, ∑ outcome, direction i * direction j
          * (chance outcome * (vector outcome i * vector outcome j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, direction i * direction j
          * (if i = j then mean_square else 0) := by
        simp only [← Finset.mul_sum, uncorrelated]
    _ = mean_square * ∑ i, direction i ^ 2 := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

end SquigglyLine
