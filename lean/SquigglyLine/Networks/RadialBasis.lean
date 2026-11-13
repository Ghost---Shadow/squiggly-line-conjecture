/-
Radial basis functions: the width of a bump is its slope.

A radial basis network is a sum of Gaussian bumps of one width. A bump of
width `σ` is the unit bump squeezed sideways by `1 / σ`, so the squiggly line
theorem for squeezed functions applies with `1 / σ` in the place of the
frequency: narrow bumps reach every label and are steep, wide bumps are
gentle and cannot reach.

Definitions: `GET_BUMP`, `EVALUATE_BUMP_NETWORK`, `LIFT_BY_BUMPS`.

Theorems: `bump_pos`, `bump_le_one`, `bump_zero`, `bump_neg`, `bump_shift`,
`bump_eq_compress`, `lipschitzWith_unitBump`, `lipschitzWith_bump`,
`lipschitzWith_bumpNetwork`, `verticalDist_bumpNetwork_le`,
`bumpNetwork_eq_liftedModel`, `bump_le_of_gap`,
`exists_heights_of_small_overlap`.
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

/-- The Gaussian bump of width `σ`, at offset `t` from its centre.
Python: `exp(-(t / σ) ** 2 / 2)`. -/
noncomputable def GET_BUMP (σ t : ℝ) : ℝ :=
  exp (-(t / σ) ^ 2 / 2)

theorem bump_pos (σ t : ℝ) : 0 < GET_BUMP σ t :=
  exp_pos _

/-- A bump is never higher than one. -/
theorem bump_le_one (σ t : ℝ) : GET_BUMP σ t ≤ 1 := by
  rw [GET_BUMP, ← exp_zero]
  exact exp_le_exp.mpr (by nlinarith [sq_nonneg (t / σ)])

/-- At its centre a bump is one. -/
theorem bump_zero (σ : ℝ) : GET_BUMP σ 0 = 1 := by
  simp [GET_BUMP]

/-- A bump is the same on both sides of its centre. -/
theorem bump_neg (σ t : ℝ) : GET_BUMP σ (-t) = GET_BUMP σ t := by
  simp [GET_BUMP, neg_div]

/-- A bump sees only the distance between input and centre: shifting both changes
nothing. -/
theorem bump_shift (σ x c s : ℝ) : GET_BUMP σ ((x + s) - (c + s)) = GET_BUMP σ (x - c) := by
  rw [add_sub_add_right_eq_sub]

/-- **A bump of width `σ` is the unit bump, squeezed by `1 / σ`.** -/
theorem bump_eq_compress (σ : ℝ) : GET_BUMP σ = COMPRESS (1 / σ) (GET_BUMP 1) := by
  funext t
  simp [GET_BUMP, COMPRESS, div_eq_inv_mul]

/-- The unit bump never climbs faster than one. -/
theorem lipschitzWith_unitBump : LipschitzWith 1 (GET_BUMP 1) := by
  have hfun : GET_BUMP 1 = fun u : ℝ => exp (-u ^ 2 / 2) := by
    funext u; simp [GET_BUMP]
  rw [hfun]
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => exp (-u ^ 2 / 2))
      (exp (-u ^ 2 / 2) * (-(2 * u) / 2)) u := by
    intro u
    have h := ((hasDerivAt_pow 2 u).neg.div_const 2).exp
    simpa using h
  refine lipschitzWith_of_nnnorm_deriv_le (fun u => (hderiv u).differentiableAt) fun u => ?_
  rw [(hderiv u).deriv, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  have hu : |-(2 * u) / 2| = |u| := by
    rw [show -(2 * u) / 2 = -u by ring, abs_neg]
  rw [hu]
  -- `|u| ≤ u² / 2 + 1 ≤ exp (u² / 2)`
  have h1 : |u| ≤ u ^ 2 / 2 + 1 := by nlinarith [sq_abs u, sq_nonneg (|u| - 1)]
  have h2 : u ^ 2 / 2 + 1 ≤ exp (u ^ 2 / 2) := add_one_le_exp _
  calc exp (-u ^ 2 / 2) * |u|
      ≤ exp (-u ^ 2 / 2) * exp (u ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (exp_pos _).le
    _ = 1 := by rw [← exp_add]; simp [neg_div]

/-- **A narrow bump is a steep one.** A bump of width `σ` has slope at most `1 / σ`. -/
theorem lipschitzWith_bump (σ : ℝ≥0) : LipschitzWith (σ⁻¹ * 1) (GET_BUMP (σ : ℝ)) := by
  rw [bump_eq_compress]
  have h := lipschitzWith_compress lipschitzWith_unitBump σ⁻¹
  simpa using h

variable {ι : Type*} [Fintype ι]

/-- A radial basis network: bumps of one width `σ` at the centres `c`, with heights `a`.
Python: `sum(a[i] * GET_BUMP(σ, x - c[i]) for i in centres)`. -/
noncomputable def EVALUATE_BUMP_NETWORK (σ : ℝ) (c a : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, a i * GET_BUMP σ (x - c i)

/-- **The network is no steeper than its heights over its width.** -/
theorem lipschitzWith_bumpNetwork (σ : ℝ≥0) (c a : ι → ℝ) :
    LipschitzWith ((∑ i, ‖a i‖₊) * σ⁻¹) (EVALUATE_BUMP_NETWORK (σ : ℝ) c a) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hb : ∀ i, |GET_BUMP (σ : ℝ) (x - c i) - GET_BUMP (σ : ℝ) (y - c i)|
      ≤ (σ⁻¹ : ℝ≥0) * |x - y| := by
    intro i
    have h := (lipschitzWith_bump σ).dist_le_mul (x - c i) (y - c i)
    simpa [Real.dist_eq] using h
  simp only [Real.dist_eq, EVALUATE_BUMP_NETWORK, NNReal.coe_mul, NNReal.coe_sum, coe_nnnorm,
    Real.norm_eq_abs]
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, (a i * GET_BUMP (σ : ℝ) (x - c i) - a i * GET_BUMP (σ : ℝ) (y - c i))|
      ≤ ∑ i, |a i * GET_BUMP (σ : ℝ) (x - c i) - a i * GET_BUMP (σ : ℝ) (y - c i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * ((σ⁻¹ : ℝ≥0) * |x - y|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
    _ = (∑ i, |a i|) * (σ⁻¹ : ℝ≥0) * |x - y| := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **Near needs narrow or tall.** The vertical error of a radial basis network is at most
`√(1 + (heights / width)²)` times its distance to the data point. -/
theorem verticalDist_bumpNetwork_le (σ : ℝ≥0) (c a : ι → ℝ) (p : DataPoint ℝ) :
    GET_VERTICAL_ERROR (EVALUATE_BUMP_NETWORK (σ : ℝ) c a) p
      ≤ √(1 + (((∑ i, ‖a i‖₊) * σ⁻¹ : ℝ≥0) : ℝ) ^ 2)
        * GET_NEAREST_DISTANCE (EVALUATE_BUMP_NETWORK (σ : ℝ) c a) p :=
  verticalDist_le_of_lipschitz (lipschitzWith_bumpNetwork σ c a) p

/-- The lift of a radial basis network: the list of bump values at an input.
Python: `[GET_BUMP(σ, x - c[i]) for i in centres]`. -/
noncomputable def LIFT_BY_BUMPS (σ : ℝ) (c : ι → ℝ) (x : ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => GET_BUMP σ (x - c i)

/-- **A radial basis network is a flat model on the lift by bumps.** -/
theorem bumpNetwork_eq_liftedModel (σ : ℝ) (c a : ι → ℝ) (x : ℝ) :
    EVALUATE_BUMP_NETWORK σ c a x
      = EVALUATE_LIFTED_MODEL (LIFT_BY_BUMPS σ c) (WithLp.toLp 2 a) x := by
  simp [EVALUATE_BUMP_NETWORK, EVALUATE_LIFTED_MODEL, LIFT_BY_BUMPS, PiLp.inner_apply, mul_comm]

/-- Away from its centre by at least `δ`, a bump is at most `exp (-(δ / σ)² / 2)`. -/
theorem bump_le_of_gap {σ δ t : ℝ} (hδ : 0 ≤ δ) (ht : δ ≤ |t|) :
    GET_BUMP σ t ≤ exp (-(δ / σ) ^ 2 / 2) := by
  rw [GET_BUMP]
  refine exp_le_exp.mpr ?_
  have h1 : (δ / σ) ^ 2 ≤ (t / σ) ^ 2 := by
    rw [div_pow, div_pow]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg σ)
    calc δ ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ hδ ht 2
      _ = t ^ 2 := sq_abs t
  linarith

/-- **Narrow bumps fit anything.** Put a bump on every data point. If at each point the other
bumps together are worth less than one, some heights fit any labels exactly. -/
theorem exists_heights_of_small_overlap [DecidableEq ι] (σ : ℝ) (x y : ι → ℝ)
    (h : ∀ i, ∑ j ∈ Finset.univ.erase i, GET_BUMP σ (x i - x j) < 1) :
    ∃ a : ι → ℝ, ∀ i, EVALUATE_BUMP_NETWORK σ x a (x i) = y i := by
  -- The table of overlaps has ones on its diagonal and small entries off it, so it can be
  -- inverted.
  let G : Matrix ι ι ℝ := Matrix.of fun i j => GET_BUMP σ (x i - x j)
  have hdet : G.det ≠ 0 := by
    refine det_ne_zero_of_sum_row_lt_diag fun i => ?_
    have hdiag : ‖G i i‖ = 1 := by simp [G, bump_zero]
    rw [hdiag]
    calc ∑ j ∈ Finset.univ.erase i, ‖G i j‖
        = ∑ j ∈ Finset.univ.erase i, GET_BUMP σ (x i - x j) :=
          Finset.sum_congr rfl fun j _ => by
            simp [G, Real.norm_eq_abs, abs_of_pos (bump_pos _ _)]
      _ < 1 := h i
  refine ⟨G⁻¹.mulVec y, fun i => ?_⟩
  have hmul : G.mulVec (G⁻¹.mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hi := congrFun hmul i
  simpa [EVALUATE_BUMP_NETWORK, Matrix.mulVec, dotProduct, G, mul_comm] using hi

end SquigglyLine
