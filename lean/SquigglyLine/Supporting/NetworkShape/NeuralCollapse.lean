/-
Neural collapse: why the classes end up on a simplex.

`v i` is the arrow for class `i`, of length one. `K` is the number of classes.

* `norm_sum_sq_eq_sum_inner` : the squared length of the sum of the arrows is
  the sum of all their overlaps.
* `neg_one_le_of_inner_le` : if every pair of arrows has overlap at most `c`,
  then `(K - 1) * c ≥ -1`. No arrangement is farther apart than the simplex.
* `norm_sum_sq_of_equiangular` : if every pair has overlap exactly `c`, the
  squared length of the sum is `K * (1 + (K - 1) * c)`.
* `sum_eq_zero_iff_of_equiangular` : so evenly spread arrows reach the limit
  exactly when they add up to zero.
-/
import Mathlib.Analysis.InnerProductSpace.Basic

namespace SquigglyLine

open Finset

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- The squared length of a sum is the sum of all the overlaps. -/
theorem norm_sum_sq_eq_sum_inner (v : ι → E) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ∑ j, inner ℝ (v i) (v j) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum]

variable [DecidableEq ι]

/-- All the classes but `i`: there are `K - 1` of them. -/
theorem card_erase_univ_add_one (i : ι) :
    (((univ : Finset ι).erase i).card : ℝ) + 1 = Fintype.card ι := by
  exact_mod_cast card_erase_add_one (mem_univ i)

/-- One arrow's overlaps with all the arrows: its own length, then the others. -/
theorem sum_inner_eq_one_add {v : ι → E} (hunit : ∀ i, ‖v i‖ = 1) (i : ι) :
    ∑ j, inner ℝ (v i) (v j) = 1 + ∑ j ∈ (univ : Finset ι).erase i, inner ℝ (v i) (v j) := by
  rw [← add_sum_erase _ _ (mem_univ i), real_inner_self_eq_norm_sq, hunit i, one_pow]

/-- If every pair of arrows has overlap at most `c`, their sum is short. -/
theorem norm_sum_sq_le_of_inner_le {v : ι → E} (hunit : ∀ i, ‖v i‖ = 1) {c : ℝ}
    (hc : ∀ i j, i ≠ j → inner ℝ (v i) (v j) ≤ c) :
    ‖∑ i, v i‖ ^ 2 ≤ Fintype.card ι * (1 + (Fintype.card ι - 1) * c) := by
  rw [norm_sum_sq_eq_sum_inner]
  calc ∑ i, ∑ j, inner ℝ (v i) (v j)
      ≤ ∑ _i : ι, (1 + (Fintype.card ι - 1) * c) := by
        refine sum_le_sum fun i _ => ?_
        have hle : ∑ j ∈ (univ : Finset ι).erase i, inner ℝ (v i) (v j)
            ≤ ∑ _j ∈ (univ : Finset ι).erase i, c :=
          sum_le_sum fun j hj => hc i j (ne_of_mem_erase hj).symm
        have hcard := card_erase_univ_add_one i
        rw [sum_const, nsmul_eq_mul,
          show (((univ : Finset ι).erase i).card : ℝ) = Fintype.card ι - 1 by linarith] at hle
        rw [sum_inner_eq_one_add hunit i]
        linarith
    _ = Fintype.card ι * (1 + (Fintype.card ι - 1) * c) := by
        rw [sum_const, card_univ, nsmul_eq_mul]

/-- **The simplex is as far apart as arrows can get.** For `K` arrows of length one, if
every pair has overlap at most `c`, then `(K - 1) * c ≥ -1`. -/
theorem neg_one_le_of_inner_le [Nonempty ι] {v : ι → E} (hunit : ∀ i, ‖v i‖ = 1) {c : ℝ}
    (hc : ∀ i j, i ≠ j → inner ℝ (v i) (v j) ≤ c) : -1 ≤ (Fintype.card ι - 1) * c := by
  have hK : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsum := norm_sum_sq_le_of_inner_le hunit hc
  by_contra hcon
  have hneg : 1 + (Fintype.card ι - 1) * c < 0 := by linarith [not_le.mp hcon]
  have := mul_neg_of_pos_of_neg hK hneg
  linarith [sq_nonneg ‖∑ i, v i‖]

/-- If every pair of arrows has overlap exactly `c`, the squared length of their sum is
`K * (1 + (K - 1) * c)`. -/
theorem norm_sum_sq_of_equiangular {v : ι → E} (hunit : ∀ i, ‖v i‖ = 1) {c : ℝ}
    (hc : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = c) :
    ‖∑ i, v i‖ ^ 2 = Fintype.card ι * (1 + (Fintype.card ι - 1) * c) := by
  rw [norm_sum_sq_eq_sum_inner]
  calc ∑ i, ∑ j, inner ℝ (v i) (v j)
      = ∑ _i : ι, (1 + (Fintype.card ι - 1) * c) := by
        refine sum_congr rfl fun i _ => ?_
        have heq : ∑ j ∈ (univ : Finset ι).erase i, inner ℝ (v i) (v j)
            = ∑ _j ∈ (univ : Finset ι).erase i, c :=
          sum_congr rfl fun j hj => hc i j (ne_of_mem_erase hj).symm
        have hcard := card_erase_univ_add_one i
        rw [sum_const, nsmul_eq_mul,
          show (((univ : Finset ι).erase i).card : ℝ) = Fintype.card ι - 1 by linarith] at heq
        rw [sum_inner_eq_one_add hunit i, heq]
    _ = Fintype.card ι * (1 + (Fintype.card ι - 1) * c) := by
        rw [sum_const, card_univ, nsmul_eq_mul]

/-- **The farthest-apart arrangement is the centred one.** Evenly spread arrows of length
one reach the limit `(K - 1) * c = -1` exactly when they add up to zero. -/
theorem sum_eq_zero_iff_of_equiangular [Nonempty ι] {v : ι → E} (hunit : ∀ i, ‖v i‖ = 1)
    {c : ℝ} (hc : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = c) :
    ∑ i, v i = 0 ↔ (Fintype.card ι - 1) * c = -1 := by
  have hK : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsq := norm_sum_sq_of_equiangular hunit hc
  constructor
  · intro hzero
    rw [hzero, norm_zero] at hsq
    have hfactor : 1 + (Fintype.card ι - 1) * c = 0 := by
      rcases mul_eq_zero.mp (by linarith : (Fintype.card ι : ℝ) * (1 + (Fintype.card ι - 1) * c) = 0)
        with h | h
      · linarith
      · exact h
    linarith
  · intro hlimit
    have hzero : ‖∑ i, v i‖ ^ 2 = 0 := by
      rw [hsq, show 1 + (Fintype.card ι - 1) * c = 0 by linarith, mul_zero]
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hzero)

end SquigglyLine
