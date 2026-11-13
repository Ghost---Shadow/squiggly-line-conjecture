/-
Radial basis functions: the width of a bump is its slope.

A radial basis network is a sum of Gaussian bumps of one width. A bump of
width `width` is the unit bump squeezed sideways by `1 / width`, so the
squiggly line theorem for squeezed functions applies with `1 / width` in the
place of the frequency: narrow bumps reach every label and are steep, wide
bumps are gentle and cannot reach.

Definitions:

* `GET_BUMP`               the Gaussian bump of a given width;
* `EVALUATE_BUMP_NETWORK`  bumps of one width at the centres, with heights;
* `LIFT_BY_BUMPS`          the list of bump values at an input.

Theorems:

* `bump_pos`, `bump_le_one`, `bump_zero`, `bump_neg`, `bump_shift` : the
  bump is positive, at most one, one at its centre, and depends only on the
  distance to its centre;
* `bump_eq_compress` : a bump is the unit bump squeezed by `1 / width`;
* `lipschitzWith_unitBump`, `lipschitzWith_bump` : the slope of a bump is
  at most one over its width;
* `lipschitzWith_bumpNetwork`, `verticalDist_bumpNetwork_le` : so a network
  is no steeper than its heights over its width, and the slope sandwich
  applies;
* `bumpNetwork_eq_liftedModel` : a network is a flat model on the lift by
  bumps;
* `bump_le_of_gap`, `exists_heights_of_small_overlap`,
  `exists_heights_of_gap` : narrow enough bumps fit any labels exactly.
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import SquigglyLine.Networks.Lift
import SquigglyLine.Theorem.Compression

namespace SquigglyLine

open Real NNReal

/-- The Gaussian bump of the given width, at an offset from its centre.
Python: `exp(-(offset / width) ** 2 / 2)`. -/
noncomputable def GET_BUMP
    (width : ℝ)
    (offset : ℝ) : ℝ :=
  exp (-(offset / width) ^ 2 / 2)  -- the Gaussian: minus half the squared offset, counted in widths

/-- A bump is always above zero. -/
theorem bump_pos
    (width : ℝ)
    (offset : ℝ) :
    let bump := GET_BUMP width offset
    0 < bump := by
  unfold_named_pieces
  exact exp_pos _

/-- A bump is never higher than one. -/
theorem bump_le_one
    (width : ℝ)
    (offset : ℝ) :
    let bump := GET_BUMP width offset
    let highest : ℝ := 1  -- the exponent is never positive, and `exp 0 = 1`
    bump ≤ highest := by
  unfold_named_pieces
  rw [GET_BUMP, ← exp_zero]
  exact exp_le_exp.mpr (by nlinarith [sq_nonneg (offset / width)])

/-- At its centre a bump is one. -/
theorem bump_zero
    (width : ℝ) :
    let bump_at_centre := GET_BUMP width 0
    let full_height : ℝ := 1
    bump_at_centre = full_height := by
  unfold_named_pieces
  simp [GET_BUMP]

/-- A bump is the same on both sides of its centre. -/
theorem bump_neg
    (width : ℝ)
    (offset : ℝ) :
    let mirrored_bump := GET_BUMP width (-offset)
    let bump          := GET_BUMP width offset
    mirrored_bump = bump := by
  unfold_named_pieces
  simp [GET_BUMP, neg_div]

/-- A bump sees only the distance between input and centre: shifting both
changes nothing. -/
theorem bump_shift
    (width : ℝ)
    (input : ℝ)
    (centre : ℝ)
    (shift : ℝ) :
    let shifted_bump := GET_BUMP width ((input + shift) - (centre + shift))
    let bump         := GET_BUMP width (input - centre)
    shifted_bump = bump := by
  unfold_named_pieces
  rw [add_sub_add_right_eq_sub]

/-- **A bump of width `width` is the unit bump, squeezed by `1 / width`.** -/
theorem bump_eq_compress
    (width : ℝ) :
    let bump          := GET_BUMP width
    let squeezed_bump :=COMPRESS (1 / width) (GET_BUMP 1)  -- the unit bump, squeezed sideways
    bump = squeezed_bump := by
  unfold_named_pieces
  funext offset
  simp [GET_BUMP, COMPRESS, div_eq_inv_mul]

/-- The unit bump never climbs faster than one. -/
theorem lipschitzWith_unitBump :
    let unit_bump := GET_BUMP 1
    let slope_limit : SlopeLimit := 1  -- true steepest slope is 1 / √e; one is a bound that is easy to prove
    LipschitzWith slope_limit unit_bump := by
  unfold_named_pieces
  have unit_bump_formula :
      GET_BUMP 1 = fun offset : ℝ => exp (-offset ^ 2 / 2) := by
    funext offset
    simp [GET_BUMP]
  rw [unit_bump_formula]
  have bump_derivative :
      ∀ offset : ℝ,
        HasDerivAt (fun offset : ℝ => exp (-offset ^ 2 / 2))
          (exp (-offset ^ 2 / 2) * (-(2 * offset) / 2)) offset := by
    intro offset
    have chain_rule := ((hasDerivAt_pow 2 offset).neg.div_const 2).exp
    simpa using chain_rule
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun offset => (bump_derivative offset).differentiableAt)
    fun offset => ?_
  rw [(bump_derivative offset).deriv, ← NNReal.coe_le_coe, coe_nnnorm,
    NNReal.coe_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (exp_pos _)]
  have abs_derivative_factor : |-(2 * offset) / 2| = |offset| := by
    rw [show -(2 * offset) / 2 = -offset by ring, abs_neg]
  rw [abs_derivative_factor]
  -- `|offset| ≤ offset² / 2 + 1 ≤ exp (offset² / 2)`
  have abs_le_quadratic : |offset| ≤ offset ^ 2 / 2 + 1 := by
    nlinarith [sq_abs offset, sq_nonneg (|offset| - 1)]
  have quadratic_le_exp : offset ^ 2 / 2 + 1 ≤ exp (offset ^ 2 / 2) :=
    add_one_le_exp _
  calc exp (-offset ^ 2 / 2) * |offset|
      ≤ exp (-offset ^ 2 / 2) * exp (offset ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (abs_le_quadratic.trans quadratic_le_exp)
          (exp_pos _).le
    _ = 1 := by rw [← exp_add]; simp [neg_div]

/-- **A narrow bump is a steep one.** A bump of width `width` has slope at
most `1 / width`. -/
theorem lipschitzWith_bump
    (width : ℝ≥0) :
    let bump := GET_BUMP (width : ℝ)
    let squeeze_factor : ℝ≥0 := width⁻¹     -- the unit bump is squeezed by one over the width
    let unit_slope_limit : SlopeLimit := 1  -- the unit bump's slope bound
    let slope_limit := squeeze_factor * unit_slope_limit  -- squeezing multiplies the slope by the factor
    LipschitzWith slope_limit bump := by
  unfold_named_pieces
  have bump_is_squeezed :
      GET_BUMP (width : ℝ) = COMPRESS (1 / (width : ℝ)) (GET_BUMP 1) :=
    bump_eq_compress width
  have unit_bump_slope : LipschitzWith 1 (GET_BUMP 1) :=
    lipschitzWith_unitBump
  rw [bump_is_squeezed]
  have squeezed_slope :=
    lipschitzWith_compress unit_bump_slope width⁻¹
  simpa using squeezed_slope

variable {Examples : Type*} [Fintype Examples]

/-- A radial basis network: bumps of one width at the centres, with the given
heights.
Python: `sum(heights[i] * GET_BUMP(width, input - centres[i])
for i in centres)`. -/
noncomputable def EVALUATE_BUMP_NETWORK
    (width : ℝ)
    (centres : InputPerExample Examples ℝ)
    (heights : NumberPerExample Examples)
    (input : ℝ) : ℝ :=
  ∑ i, heights i * GET_BUMP width (input - centres i)

/-- **The network is no steeper than its heights over its width.** -/
theorem lipschitzWith_bumpNetwork
    (width : ℝ≥0)
    (centres : InputPerExample Examples ℝ)
    (heights : NumberPerExample Examples) :
    let network := EVALUATE_BUMP_NETWORK (width : ℝ) centres heights
    let total_height : ℝ≥0 := ∑ i, ‖heights i‖₊
    let slope_limit := total_height * width⁻¹  -- each bump has slope `width⁻¹`, scaled by its height
    LipschitzWith slope_limit network := by
  unfold_named_pieces
  refine LipschitzWith.of_dist_le_mul fun input other_input => ?_
  have bump_slope : LipschitzWith (width⁻¹ * 1) (GET_BUMP (width : ℝ)) :=
    lipschitzWith_bump width
  have bump_change_le :
      ∀ i,
        |GET_BUMP (width : ℝ) (input - centres i)
            - GET_BUMP (width : ℝ) (other_input - centres i)|
          ≤ (width⁻¹ : ℝ≥0) * |input - other_input| := by
    intro i
    have step :=
      bump_slope.dist_le_mul (input - centres i) (other_input - centres i)
    simpa [Real.dist_eq] using step
  simp only [Real.dist_eq, EVALUATE_BUMP_NETWORK, NNReal.coe_mul,
    NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
  rw [← Finset.sum_sub_distrib]
  -- The change of the sum is the sum of the changes, each at most its
  -- height times the slope of a bump.
  calc |∑ i, (heights i * GET_BUMP (width : ℝ) (input - centres i)
          - heights i * GET_BUMP (width : ℝ) (other_input - centres i))|
      ≤ ∑ i, |heights i * GET_BUMP (width : ℝ) (input - centres i)
          - heights i * GET_BUMP (width : ℝ) (other_input - centres i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |heights i| * ((width⁻¹ : ℝ≥0) * |input - other_input|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (bump_change_le i) (abs_nonneg _)
    _ = (∑ i, |heights i|) * (width⁻¹ : ℝ≥0) * |input - other_input| := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **Near needs narrow or tall.** The vertical error of a radial basis
network is at most `√(1 + (heights / width)²)` times its distance to the data
point. -/
theorem verticalDist_bumpNetwork_le
    (width : ℝ≥0)
    (centres : InputPerExample Examples ℝ)
    (heights : NumberPerExample Examples)
    (data_point : DataPoint ℝ) :
    let network          := EVALUATE_BUMP_NETWORK (width : ℝ) centres heights
    let vertical_error   := GET_VERTICAL_ERROR network data_point
    let nearest_distance := GET_NEAREST_DISTANCE network data_point
    let total_height : ℝ≥0 := ∑ i, ‖heights i‖₊
    let slope_limit : SlopeLimit := total_height * width⁻¹  -- heights over width
    let stretch := √(1 + (slope_limit : ℝ) ^ 2)  -- Pythagoras: 1 across, slope_limit up
    vertical_error ≤ stretch * nearest_distance := by
  unfold_named_pieces
  have network_slope :
      LipschitzWith ((∑ i, ‖heights i‖₊) * width⁻¹)
        (EVALUATE_BUMP_NETWORK (width : ℝ) centres heights) :=
    lipschitzWith_bumpNetwork width centres heights
  exact verticalDist_le_of_lipschitz network_slope data_point

/-- The lift of a radial basis network: the list of bump values at an input.
Python: `[GET_BUMP(width, input - centres[i]) for i in centres]`. -/
noncomputable def LIFT_BY_BUMPS
    (width : ℝ)
    (centres : InputPerExample Examples ℝ)
    (input : ℝ) : EuclideanSpace ℝ Examples :=
  WithLp.toLp 2 fun i => GET_BUMP width (input - centres i)

/-- **A radial basis network is a flat model on the lift by bumps.** -/
theorem bumpNetwork_eq_liftedModel
    (width : ℝ)
    (centres : InputPerExample Examples ℝ)
    (heights : NumberPerExample Examples)
    (input : ℝ) :
    let network_value := EVALUATE_BUMP_NETWORK width centres heights input
    let features : FeatureMap ℝ (EuclideanSpace ℝ Examples) :=
      LIFT_BY_BUMPS width centres
    let height_vector : EuclideanSpace ℝ Examples := WithLp.toLp 2 heights
    let lifted_value := EVALUATE_LIFTED_MODEL features height_vector input
    network_value = lifted_value := by
  unfold_named_pieces
  simp [EVALUATE_BUMP_NETWORK, EVALUATE_LIFTED_MODEL, LIFT_BY_BUMPS,
    PiLp.inner_apply, mul_comm]

/-- Away from its centre by at least `gap`, a bump is at most
`exp (-(gap / width)² / 2)`. -/
theorem bump_le_of_gap
    {width gap offset : ℝ}
    (gap_nonneg : 0 ≤ gap)
    (gap_le_offset : gap ≤ |offset|) :
    let bump  := GET_BUMP width offset
    let bound := exp (-(gap / width) ^ 2 / 2)  -- the bump value at distance exactly `gap`
    bump ≤ bound := by
  unfold_named_pieces
  rw [GET_BUMP]
  refine exp_le_exp.mpr ?_
  have gap_sq_le_offset_sq : (gap / width) ^ 2 ≤ (offset / width) ^ 2 := by
    rw [div_pow, div_pow]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg width)
    calc gap ^ 2 ≤ |offset| ^ 2 := pow_le_pow_left₀ gap_nonneg gap_le_offset 2
      _ = offset ^ 2 := sq_abs offset
  linarith

/-- **Narrow bumps fit anything.** Put a bump on every data point. If at each
point the other bumps together are worth less than one, some heights fit any
labels exactly. -/
theorem exists_heights_of_small_overlap
    [DecidableEq Examples]
    (width : ℝ)
    (inputs : InputPerExample Examples ℝ)
    (labels : NumberPerExample Examples)
    (overlaps_are_small :
      ∀ i,
        let overlap_with_others :=
          ∑ j ∈ Finset.univ.erase i, GET_BUMP width (inputs i - inputs j)
        overlap_with_others < 1) :  -- the bump at its own point is worth exactly one
    ∃ heights : NumberPerExample Examples,
      ∀ i,
        let network_value :=
          EVALUATE_BUMP_NETWORK width inputs heights (inputs i)
        network_value = labels i := by
  -- The table of overlaps has ones on its diagonal and small entries off it,
  -- so it can be inverted.
  let overlap_table : Matrix Examples Examples ℝ :=
    Matrix.of fun i j => GET_BUMP width (inputs i - inputs j)
  have table_det_ne_zero : overlap_table.det ≠ 0 := by
    refine det_ne_zero_of_sum_row_lt_diag fun i => ?_
    have bump_at_centre : GET_BUMP width 0 = 1 := bump_zero width
    have diagonal_is_one : ‖overlap_table i i‖ = 1 := by  -- a bump at its own centre
      simp [overlap_table, bump_at_centre]
    rw [diagonal_is_one]
    calc ∑ j ∈ Finset.univ.erase i, ‖overlap_table i j‖
        = ∑ j ∈ Finset.univ.erase i, GET_BUMP width (inputs i - inputs j) :=
          Finset.sum_congr rfl fun j _ => by
            have bump_positive : 0 < GET_BUMP width (inputs i - inputs j) :=
              bump_pos _ _
            simp [overlap_table, Real.norm_eq_abs, abs_of_pos bump_positive]
      _ < 1 := overlaps_are_small i
  refine ⟨overlap_table⁻¹.mulVec labels, fun i => ?_⟩
  unfold_named_pieces
  have table_times_inverse :
      overlap_table.mulVec (overlap_table⁻¹.mulVec labels) = labels := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr table_det_ne_zero),
      Matrix.one_mulVec]
  have row_equation := congrFun table_times_inverse i
  simpa [EVALUATE_BUMP_NETWORK, Matrix.mulVec, dotProduct, overlap_table,
    mul_comm] using row_equation

/-- **How narrow is narrow enough.** If every two inputs are at least `gap`
apart and the bumps are narrow enough that `count - 1` of them at that
distance are together worth less than one, the network with a bump on every
input fits any labels exactly. -/
theorem exists_heights_of_gap
    [DecidableEq Examples]
    {width gap : ℝ}
    (gap_nonneg : 0 ≤ gap)
    (inputs : InputPerExample Examples ℝ)
    (labels : NumberPerExample Examples)
    (inputs_are_apart :
      ∀ i j,
        let are_different := i ≠ j
        let distance      := |inputs i - inputs j|
        let is_far_enough := gap ≤ distance
        are_different → is_far_enough)
    (bumps_are_narrow :
      let other_count : ℝ := ((Fintype.card Examples - 1 : ℕ) : ℝ)  -- the other bumps at one input
      let worst_bump := exp (-(gap / width) ^ 2 / 2)  -- no other bump is higher than at distance `gap`
      other_count * worst_bump < 1) :
    ∃ heights : NumberPerExample Examples,
      ∀ i,
        let network_value :=
          EVALUATE_BUMP_NETWORK width inputs heights (inputs i)
        network_value = labels i := by
  refine exists_heights_of_small_overlap width inputs labels fun i => ?_
  unfold_named_pieces
  -- Each other bump is at most the bump at distance `gap`, and there are
  -- `count - 1` of them.
  calc ∑ j ∈ Finset.univ.erase i, GET_BUMP width (inputs i - inputs j)
      ≤ ∑ _j ∈ Finset.univ.erase i, exp (-(gap / width) ^ 2 / 2) :=
        Finset.sum_le_sum fun j other_mem =>
          bump_le_of_gap gap_nonneg
            (inputs_are_apart i j (Finset.ne_of_mem_erase other_mem).symm)
    _ = ((Fintype.card Examples - 1 : ℕ) : ℝ)
          * exp (-(gap / width) ^ 2 / 2) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, nsmul_eq_mul]
    _ < 1 := bumps_are_narrow

end SquigglyLine
