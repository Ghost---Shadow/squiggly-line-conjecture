/-
The dimpled manifold, in the squiggly line picture.

An input is a position `u` on the data manifold together with a height off it.
Real data has height zero. A function that is `g` along the manifold and has
slope `K` across it is

    dimpled g K (u, height) = g u + K * height.

* `residualLoss_dimpled_onManifold`: on real data every loss is that of `g`.
  Training cannot see `K`.
* `dimpled_dimple`, `dist_onManifold_dimple`: for any data point and any label,
  the step `(label - g u) / K` straight off the manifold gives that label.
* `nearestDist_dimpled_bounds`: so the nearest-point distance lies between
  `vertical / √(1 + (L + K)²)` and `vertical / K`.

The price of being close to the data is slope, and it can be paid entirely in
the direction that real data never visits. After Shamir, Melamed and
BenShmuel, "The Dimpled Manifold Model of Adversarial Examples" (2021).
-/
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open NNReal

variable {U : Type*} [SeminormedAddCommGroup U] {g : U → ℝ} {K : ℝ}

/-- A real data input: a position on the manifold, at height zero. -/
def PLACE_ON_MANIFOLD (u : U) : U × ℝ :=
  (u, 0)

/-- A function that is `g` along the manifold and has slope `K` across it. -/
def EVALUATE_DIMPLED_MODEL (g : U → ℝ) (K : ℝ) : U × ℝ → ℝ :=
  fun p => g p.1 + K * p.2

/-- The adversarial input for the label `y`: step straight off the manifold. -/
noncomputable def MAKE_DIMPLE (g : U → ℝ) (K : ℝ) (u : U) (y : ℝ) : U × ℝ :=
  (u, (y - g u) / K)

omit [SeminormedAddCommGroup U] in
@[simp]
theorem dimpled_onManifold (g : U → ℝ) (K : ℝ) (u : U) : EVALUATE_DIMPLED_MODEL g K (PLACE_ON_MANIFOLD u) = g u := by
  simp [EVALUATE_DIMPLED_MODEL, PLACE_ON_MANIFOLD]

omit [SeminormedAddCommGroup U] in
/-- **Training cannot see the slope off the manifold.** On real data, every loss of the
dimpled function is the loss of `g`, whatever `K` is. -/
theorem residualLoss_dimpled_onManifold (ℓ : ℝ → ℝ) (g : U → ℝ) (K : ℝ) (u : U) (y : ℝ) :
    GET_RESIDUAL_LOSS ℓ (EVALUATE_DIMPLED_MODEL g K) (PLACE_ON_MANIFOLD u, y) = ℓ (y - g u) := by
  simp [GET_RESIDUAL_LOSS]

omit [SeminormedAddCommGroup U] in
/-- The adversarial step does not move along the manifold. -/
theorem dimple_fst (g : U → ℝ) (K : ℝ) (u : U) (y : ℝ) : (MAKE_DIMPLE g K u y).1 = u :=
  rfl

omit [SeminormedAddCommGroup U] in
/-- **Any label is one step off the manifold.** -/
theorem dimpled_dimple (hK : K ≠ 0) (u : U) (y : ℝ) : EVALUATE_DIMPLED_MODEL g K (MAKE_DIMPLE g K u y) = y := by
  simp only [EVALUATE_DIMPLED_MODEL, MAKE_DIMPLE]
  field_simp
  ring

/-- The length of the adversarial step is the error divided by the slope. -/
theorem dist_onManifold_dimple (hK : 0 < K) (u : U) (y : ℝ) :
    dist (PLACE_ON_MANIFOLD u) (MAKE_DIMPLE g K u y) = |y - g u| / K := by
  simp [PLACE_ON_MANIFOLD, MAKE_DIMPLE, Prod.dist_eq, Real.dist_eq, abs_div, abs_of_pos hK]
  exact div_nonneg (abs_nonneg _) hK.le

/-- A dimpled function is `(L + K)`-Lipschitz when `g` is `L`-Lipschitz. -/
theorem lipschitzWith_dimpled {L Kn : ℝ≥0} (hg : LipschitzWith L g) :
    LipschitzWith (L + Kn) (EVALUATE_DIMPLED_MODEL g Kn) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h1 : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h2 : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  calc dist (EVALUATE_DIMPLED_MODEL g Kn p) (EVALUATE_DIMPLED_MODEL g Kn q)
      = |(g p.1 - g q.1) + Kn * (p.2 - q.2)| := by
        rw [Real.dist_eq]
        congr 1
        simp only [EVALUATE_DIMPLED_MODEL]
        ring
    _ ≤ |g p.1 - g q.1| + |(Kn : ℝ) * (p.2 - q.2)| := abs_add_le _ _
    _ = dist (g p.1) (g q.1) + Kn * dist p.2 q.2 := by
        rw [abs_mul, abs_of_nonneg Kn.coe_nonneg, Real.dist_eq, Real.dist_eq]
    _ ≤ L * dist p q + Kn * dist p q :=
        add_le_add ((hg.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left h1 L.coe_nonneg))
          (mul_le_mul_of_nonneg_left h2 Kn.coe_nonneg)
    _ = ((L + Kn : ℝ≥0) : ℝ) * dist p q := by
        push_cast
        ring

/-- **The adversarial distance is the error over the slope.** For a real data point, the
nearest-point distance of a dimpled function lies between the vertical error divided by
`√(1 + (L + K)²)` and the vertical error divided by `K`. -/
theorem nearestDist_dimpled_bounds {L Kn : ℝ≥0} (hg : LipschitzWith L g) (hK : 0 < (Kn : ℝ))
    (u : U) (y : ℝ) :
    GET_VERTICAL_ERROR (EVALUATE_DIMPLED_MODEL g Kn) (PLACE_ON_MANIFOLD u, y) / √(1 + ((L + Kn : ℝ≥0) : ℝ) ^ 2)
        ≤ GET_NEAREST_DISTANCE (EVALUATE_DIMPLED_MODEL g Kn) (PLACE_ON_MANIFOLD u, y) ∧
      GET_NEAREST_DISTANCE (EVALUATE_DIMPLED_MODEL g Kn) (PLACE_ON_MANIFOLD u, y)
        ≤ GET_VERTICAL_ERROR (EVALUATE_DIMPLED_MODEL g Kn) (PLACE_ON_MANIFOLD u, y) / Kn := by
  constructor
  · rw [div_le_iff₀' (by positivity)]
    exact verticalDist_le_of_lipschitz (lipschitzWith_dimpled hg) _
  · calc GET_NEAREST_DISTANCE (EVALUATE_DIMPLED_MODEL g Kn) (PLACE_ON_MANIFOLD u, y)
        ≤ dist (EMBED_DATA_POINT (PLACE_ON_MANIFOLD u, y))
            (EMBED_DATA_POINT (MAKE_DIMPLE g Kn u y, EVALUATE_DIMPLED_MODEL g Kn (MAKE_DIMPLE g Kn u y))) :=
          Metric.infDist_le_dist_of_mem (footpoint_mem_curve _ (MAKE_DIMPLE g Kn u y, y))
      _ = dist (PLACE_ON_MANIFOLD u) (MAKE_DIMPLE g (Kn : ℝ) u y) := by
          simp [dist_embed, dimpled_dimple hK.ne', Real.sqrt_sq dist_nonneg]
      _ = |y - g u| / Kn := dist_onManifold_dimple hK u y
      _ = GET_VERTICAL_ERROR (EVALUATE_DIMPLED_MODEL g Kn) (PLACE_ON_MANIFOLD u, y) / Kn := by simp [GET_RESIDUAL_LOSS]

end SquigglyLine
