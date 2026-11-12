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
def onManifold (u : U) : U × ℝ :=
  (u, 0)

/-- A function that is `g` along the manifold and has slope `K` across it. -/
def dimpled (g : U → ℝ) (K : ℝ) : U × ℝ → ℝ :=
  fun p => g p.1 + K * p.2

/-- The adversarial input for the label `y`: step straight off the manifold. -/
noncomputable def dimple (g : U → ℝ) (K : ℝ) (u : U) (y : ℝ) : U × ℝ :=
  (u, (y - g u) / K)

omit [SeminormedAddCommGroup U] in
@[simp]
theorem dimpled_onManifold (g : U → ℝ) (K : ℝ) (u : U) : dimpled g K (onManifold u) = g u := by
  simp [dimpled, onManifold]

omit [SeminormedAddCommGroup U] in
/-- **Training cannot see the slope off the manifold.** On real data, every loss of the
dimpled function is the loss of `g`, whatever `K` is. -/
theorem residualLoss_dimpled_onManifold (ℓ : ℝ → ℝ) (g : U → ℝ) (K : ℝ) (u : U) (y : ℝ) :
    residualLoss ℓ (dimpled g K) (onManifold u, y) = ℓ (y - g u) := by
  simp [residualLoss]

omit [SeminormedAddCommGroup U] in
/-- The adversarial step does not move along the manifold. -/
theorem dimple_fst (g : U → ℝ) (K : ℝ) (u : U) (y : ℝ) : (dimple g K u y).1 = u :=
  rfl

omit [SeminormedAddCommGroup U] in
/-- **Any label is one step off the manifold.** -/
theorem dimpled_dimple (hK : K ≠ 0) (u : U) (y : ℝ) : dimpled g K (dimple g K u y) = y := by
  simp only [dimpled, dimple]
  field_simp
  ring

/-- The length of the adversarial step is the error divided by the slope. -/
theorem dist_onManifold_dimple (hK : 0 < K) (u : U) (y : ℝ) :
    dist (onManifold u) (dimple g K u y) = |y - g u| / K := by
  simp [onManifold, dimple, Prod.dist_eq, Real.dist_eq, abs_div, abs_of_pos hK]
  exact div_nonneg (abs_nonneg _) hK.le

/-- A dimpled function is `(L + K)`-Lipschitz when `g` is `L`-Lipschitz. -/
theorem lipschitzWith_dimpled {L Kn : ℝ≥0} (hg : LipschitzWith L g) :
    LipschitzWith (L + Kn) (dimpled g Kn) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h1 : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h2 : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  calc dist (dimpled g Kn p) (dimpled g Kn q)
      = |(g p.1 - g q.1) + Kn * (p.2 - q.2)| := by
        rw [Real.dist_eq]
        congr 1
        simp only [dimpled]
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
    verticalDist (dimpled g Kn) (onManifold u, y) / √(1 + ((L + Kn : ℝ≥0) : ℝ) ^ 2)
        ≤ nearestDist (dimpled g Kn) (onManifold u, y) ∧
      nearestDist (dimpled g Kn) (onManifold u, y)
        ≤ verticalDist (dimpled g Kn) (onManifold u, y) / Kn := by
  constructor
  · rw [div_le_iff₀' (by positivity)]
    exact verticalDist_le_of_lipschitz (lipschitzWith_dimpled hg) _
  · calc nearestDist (dimpled g Kn) (onManifold u, y)
        ≤ dist (embed (onManifold u, y))
            (embed (dimple g Kn u y, dimpled g Kn (dimple g Kn u y))) :=
          Metric.infDist_le_dist_of_mem (footpoint_mem_curve _ (dimple g Kn u y, y))
      _ = dist (onManifold u) (dimple g (Kn : ℝ) u y) := by
          simp [dist_embed, dimpled_dimple hK.ne', Real.sqrt_sq dist_nonneg]
      _ = |y - g u| / Kn := dist_onManifold_dimple hK u y
      _ = verticalDist (dimpled g Kn) (onManifold u, y) / Kn := by simp [residualLoss]

end SquigglyLine
