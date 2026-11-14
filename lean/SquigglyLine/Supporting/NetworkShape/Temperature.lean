/-
Temperature trades quality for diversity; a codebook snaps to the nearest code.

* **Temperature.** Sample from a softmax of the scores times
  `inverse_temperature`, which is one over the temperature. The average score
  of a sample never falls as `inverse_temperature` rises. So a colder sampler
  picks better-scoring answers on average. `one_sub_softmax_div_le` in
  `HardChoices.lean` is the other half: a cold softmax puts nearly all its
  share on the top score, so its samples are nearly all the same. Below,
  `lower` and `higher` are two values of `inverse_temperature`, with `lower`
  the smaller.
* **Codebook.** A codebook autoencoder replaces a code by the nearest entry
  of its codebook. The decoder's output moves by at most its slope times the
  distance to that entry, and no other entry would have moved it less far in
  the code. Snapping a second time changes nothing.

Theorems:

* `sum_mul_exp_mul_sum_exp_le`  the cross-multiplied form of "the average
                                score rises with `inverse_temperature`";
* `expectedScore_softmax_mono`  a colder sampler picks better answers on
                                average;
* `dist_decode_snap_le`         snapping moves the output by at most slope
                                times distance;
* `dist_snap_le_of_nearest`     the nearest entry is the gentlest snap.
-/
import SquigglyLine.Supporting.Training.CrossEntropy
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open Real

variable {Answers : Type*} [Fintype Answers]

/-- The cross-multiplied form of "the average score rises with
`inverse_temperature`". -/
theorem sum_mul_exp_mul_sum_exp_le
    (scores : Answers → ℝ)
    {lower higher : ℝ}
    (lower_le_higher : lower ≤ higher) :
    let lower_side :=
      (∑ i, scores i * exp (lower * scores i))
        * (∑ j, exp (higher * scores j))  -- score total at `lower`, times weight total at `higher`
    let higher_side :=
      (∑ i, scores i * exp (higher * scores i))
        * (∑ j, exp (lower * scores j))  -- score total at `higher`, times weight total at `lower`
    lower_side ≤ higher_side := by
  unfold_named_pieces
  -- Pair every two answers. The better one gains more from a larger
  -- `inverse_temperature`.
  have pair_gain : ∀ i j, 0 ≤ (scores i - scores j)
      * (exp (higher * scores i + lower * scores j)
        - exp (lower * scores i + higher * scores j)) := by
    intro i j
    rcases le_total (scores j) (scores i) with j_le_i | i_le_j
    · refine mul_nonneg (sub_nonneg.mpr j_le_i)
        (sub_nonneg.mpr (exp_le_exp.mpr ?_))
      nlinarith [mul_nonneg (sub_nonneg.mpr lower_le_higher)
        (sub_nonneg.mpr j_le_i)]
    · refine mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr i_le_j)
        (sub_nonpos.mpr (exp_le_exp.mpr ?_))
      nlinarith [mul_nonneg (sub_nonneg.mpr lower_le_higher)
        (sub_nonneg.mpr i_le_j)]
  have pair_sum_nonneg : 0 ≤ ∑ i, ∑ j, (scores i - scores j)
      * (exp (higher * scores i + lower * scores j)
        - exp (lower * scores i + higher * scores j)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => pair_gain i j
  have higher_side_expand :
      (∑ i, scores i * exp (higher * scores i)) * (∑ j, exp (lower * scores j))
        = ∑ i, ∑ j,
            scores i * exp (higher * scores i) * exp (lower * scores j) :=
    Finset.sum_mul_sum _ _ _ _
  have lower_side_expand :
      (∑ i, scores i * exp (lower * scores i)) * (∑ j, exp (higher * scores j))
        = ∑ i, ∑ j,
            scores i * exp (lower * scores i) * exp (higher * scores j) :=
    Finset.sum_mul_sum _ _ _ _
  have higher_side_swapped :
      (∑ i, scores i * exp (higher * scores i)) * (∑ j, exp (lower * scores j))
        = ∑ i, ∑ j,
            scores j * exp (higher * scores j) * exp (lower * scores i) := by
    rw [higher_side_expand, Finset.sum_comm]
  have lower_side_swapped :
      (∑ i, scores i * exp (lower * scores i)) * (∑ j, exp (higher * scores j))
        = ∑ i, ∑ j,
            scores j * exp (lower * scores j) * exp (higher * scores i) := by
    rw [lower_side_expand, Finset.sum_comm]
  have pair_sum_expand :
      ∑ i, ∑ j, (scores i - scores j)
          * (exp (higher * scores i + lower * scores j)
            - exp (lower * scores i + higher * scores j))
        = ∑ i, ∑ j,
            (scores i * exp (higher * scores i) * exp (lower * scores j)
              - scores i * exp (lower * scores i) * exp (higher * scores j)
              - scores j * exp (lower * scores j) * exp (higher * scores i)
              + scores j * exp (higher * scores j)
                * exp (lower * scores i)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [exp_add, exp_add]
    ring
  rw [pair_sum_expand] at pair_sum_nonneg
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    at pair_sum_nonneg
  rw [← higher_side_expand, ← lower_side_expand, ← lower_side_swapped,
    ← higher_side_swapped] at pair_sum_nonneg
  linarith

/-- **A colder sampler picks better answers on average.** With
`inverse_temperature` one over the temperature, the average score of a sample
from the softmax never falls as `inverse_temperature` rises. -/
theorem expectedScore_softmax_mono [Nonempty Answers]
    (scores : Answers → ℝ)
    {lower higher : ℝ}
    (lower_le_higher : lower ≤ higher) :
    let lower_average :=
      ∑ i, APPLY_SOFTMAX (fun j => lower * scores j) i * scores i
    let higher_average :=
      ∑ i, APPLY_SOFTMAX (fun j => higher * scores j) i * scores i
    lower_average ≤ higher_average := by
  unfold_named_pieces
  have total_pos (inverse_temperature : ℝ) :
      0 < ∑ j, exp (inverse_temperature * scores j) :=
    Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty
  -- The average score is a ratio: weighted scores over total weight.
  have average_form (inverse_temperature : ℝ) :
      ∑ i, APPLY_SOFTMAX (fun j => inverse_temperature * scores j) i * scores i
        = (∑ i, scores i * exp (inverse_temperature * scores i))
          / ∑ j, exp (inverse_temperature * scores j) := by
    simp only [APPLY_SOFTMAX]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [average_form lower, average_form higher,
    div_le_div_iff₀ (total_pos lower) (total_pos higher)]
  exact sum_mul_exp_mul_sum_exp_le scores lower_le_higher

variable {Entries Codes Outputs : Type*} [PseudoMetricSpace Codes]
  [PseudoMetricSpace Outputs]

/-- **Snapping moves the output by at most slope times distance.** Replace a
code by a codebook entry. The decoder's output moves by at most its slope times
how far the entry is. -/
theorem dist_decode_snap_le
    {decoder : Codes → Outputs}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit decoder)
    (code : Codes)
    (book : Entries → Codes)
    (entry : Entries) :
    let output_change := dist (decoder code) (decoder (book entry))
    let max_output_change := slope_limit * dist code (book entry)
    output_change ≤ max_output_change := by
  unfold_named_pieces
  exact slope_is_bounded.dist_le_mul _ _

/-- **The nearest entry is the gentlest snap.** If `nearest_entry` is the
nearest, the output moves by at most the slope times the distance to any
entry. -/
theorem dist_snap_le_of_nearest
    {decoder : Codes → Outputs}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit decoder)
    (code : Codes)
    (book : Entries → Codes)
    {nearest_entry : Entries}
    (entry_is_nearest : ∀ other_entry,
      dist code (book nearest_entry) ≤ dist code (book other_entry))
    (other_entry : Entries) :
    let output_change := dist (decoder code) (decoder (book nearest_entry))
    let max_output_change := slope_limit * dist code (book other_entry)
    output_change ≤ max_output_change := by
  unfold_named_pieces
  exact (slope_is_bounded.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (entry_is_nearest other_entry)
      slope_limit.coe_nonneg)

end SquigglyLine
