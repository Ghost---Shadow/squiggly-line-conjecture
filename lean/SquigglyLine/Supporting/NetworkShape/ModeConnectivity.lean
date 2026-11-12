/-
Mode connectivity: when two fits are joined by a straight line.

For a model that is linear in its weights:
* `residual_along_between` : on the straight line between two settings of the
  weights, the error is the matching blend of the two errors.
* `fit_along` : the line between two fits is all fits.
* `no_barrier` : the error on the line is never larger than at the worse end.

For the smallest model with depth, output `a * b`:
* `twoLayer_along` : on the line between two fits the output is off by
  exactly `t * (1 - t) * ((a₁ - a₂) * (b₁ - b₂))`.
* `twoLayer_flip` : flipping both signs gives the same function.
* `twoLayer_midpoint_mirror` : halfway between a fit and its mirror image the
  output is zero. The hill comes from writing one function in two ways.
-/
import Mathlib.Tactic.LinearCombination
import SquigglyLine.Networks.LinearModel

namespace SquigglyLine

/-! ### Linear in the weights: one flat valley -/

section Linear

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (A : Θ →ₗ[ℝ] Y) (y : Y) (θ₀ θ₁ : Θ)

/-- On the straight line between two settings of the weights, the error is the matching
blend of the two errors. -/
theorem residual_along_between (t : ℝ) :
    residual A y (along θ₀ θ₁ t) = (1 - t) • residual A y θ₀ + t • residual A y θ₁ := by
  simp only [residual, along, map_add, map_smul, map_sub]
  module

/-- **The line between two fits is all fits.** -/
theorem fit_along (hfit₀ : A θ₀ = y) (hfit₁ : A θ₁ = y) (t : ℝ) : A (along θ₀ θ₁ t) = y := by
  simp only [along, map_add, map_smul, map_sub, hfit₀, hfit₁, sub_self, smul_zero, add_zero]

/-- **There is never a hill.** Anywhere on the line, the error is no larger than at the
worse of the two ends. -/
theorem no_barrier {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖residual A y (along θ₀ θ₁ t)‖ ≤ max ‖residual A y θ₀‖ ‖residual A y θ₁‖ := by
  rw [residual_along_between]
  calc ‖(1 - t) • residual A y θ₀ + t • residual A y θ₁‖
      ≤ ‖(1 - t) • residual A y θ₀‖ + ‖t • residual A y θ₁‖ := norm_add_le _ _
    _ = (1 - t) * ‖residual A y θ₀‖ + t * ‖residual A y θ₁‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr h1),
          Real.norm_of_nonneg h0]
    _ ≤ (1 - t) * max ‖residual A y θ₀‖ ‖residual A y θ₁‖
          + t * max ‖residual A y θ₀‖ ‖residual A y θ₁‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr h1))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) h0)
    _ = max ‖residual A y θ₀‖ ‖residual A y θ₁‖ := by ring

end Linear

/-! ### Two weights multiplied: the smallest hill -/

section TwoLayer

/-- **The hill, exactly.** Take two fits `(a₁, b₁)` and `(a₂, b₂)` of the target `y` by the
model `a * b`. A fraction `t` of the way along the straight line between them, the output
is off by `t * (1 - t) * ((a₁ - a₂) * (b₁ - b₂))`. -/
theorem twoLayer_along {a₁ b₁ a₂ b₂ y : ℝ} (h₁ : a₁ * b₁ = y) (h₂ : a₂ * b₂ = y) (t : ℝ) :
    ((1 - t) * a₁ + t * a₂) * ((1 - t) * b₁ + t * b₂)
      = y - t * (1 - t) * ((a₁ - a₂) * (b₁ - b₂)) := by
  linear_combination (1 - t) * h₁ + t * h₂

/-- **A mirror image is the same function.** -/
theorem twoLayer_flip (a b : ℝ) : -a * -b = a * b :=
  neg_mul_neg a b

/-- **Halfway to the mirror image, everything is lost.** The output is zero, whatever the
target was. -/
theorem twoLayer_midpoint_mirror (a b : ℝ) :
    ((1 - 1 / 2) * a + 1 / 2 * -a) * ((1 - 1 / 2) * b + 1 / 2 * -b) = 0 := by
  ring

end TwoLayer

end SquigglyLine
