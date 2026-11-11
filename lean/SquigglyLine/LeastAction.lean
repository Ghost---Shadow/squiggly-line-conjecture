/-
The trained path as a path of least action.

Through training (a model linear in its weights):
* `exists_iterate_gradientStep` : gradient descent moves only along the
  features. It never spends movement on a direction that leaves the outputs
  unchanged.
* `gradientDescent_fit_is_nearest` : so whenever it arrives at a fit, that fit
  is the nearest one to the start. Training takes the least travel.

Through the layers (the polarizer chain):
* `cos_mul_cos_le_cos_half_sq` : two turns `a`, `b` never keep more than two
  turns of their average. Evening out a pair of steps never loses.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SquigglyLine.Kernel

namespace SquigglyLine

/-! ### Through training: the nearest fit -/

section Training

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- **Moving only along the features is moving least.** A fit reached from `θ₀` by a move of
the form `A† v` is at least as near to `θ₀` as any other fit. -/
theorem norm_sub_le_of_fit_along_features (A : Θ →L[ℝ] Y) {y : Y} {θ₀ θ θ' : Θ} {v : Y}
    (hθ : θ = θ₀ + adjoint A v) (hfit : A θ = y) (hfit' : A θ' = y) :
    ‖θ - θ₀‖ ≤ ‖θ' - θ₀‖ := by
  have hδ : θ - θ₀ = adjoint A v := by rw [hθ, add_sub_cancel_left]
  have hA : A (θ - θ₀) = A (θ' - θ₀) := by rw [map_sub, map_sub, hfit, hfit']
  have key : ‖θ - θ₀‖ ^ 2 = inner ℝ (θ - θ₀) (θ' - θ₀) := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [hδ]
    rw [adjoint_inner_left, hA, ← adjoint_inner_left, ← hδ]
  have hle : ‖θ - θ₀‖ * ‖θ - θ₀‖ ≤ ‖θ - θ₀‖ * ‖θ' - θ₀‖ := by
    rw [← sq, key]
    exact real_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (θ - θ₀)) with h0 | hpos
  · rw [← h0]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left hle hpos

/-- **Gradient descent never wastes movement.** After any number of steps the parameters
differ from the start by a move along the features. -/
theorem exists_iterate_gradientStep (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ₀ : Θ) (t : ℕ) :
    ∃ v : Y, (gradientStep A y η)^[t] θ₀ = θ₀ + adjoint A v := by
  induction t with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨v + η • residual (A : Θ →ₗ[ℝ] Y) y ((gradientStep A y η)^[n] θ₀), ?_⟩
    rw [Function.iterate_succ_apply', gradientStep, map_add, map_smul, ← add_assoc, ← hv]

/-- **Training takes the least travel.** If gradient descent arrives at a fit, no other fit
is nearer to the start. -/
theorem gradientDescent_fit_is_nearest (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ₀ : Θ) (t : ℕ)
    (hfit : A ((gradientStep A y η)^[t] θ₀) = y) {θ' : Θ} (hfit' : A θ' = y) :
    ‖(gradientStep A y η)^[t] θ₀ - θ₀‖ ≤ ‖θ' - θ₀‖ := by
  obtain ⟨v, hv⟩ := exists_iterate_gradientStep A y η θ₀ t
  exact norm_sub_le_of_fit_along_features A hv hfit hfit'

end Training

/-! ### Through the layers: the evenest path -/

section Layers

open Real

/-- **Even steps lose least.** Two turns of `a` and `b` never keep more than two turns of
their average. -/
theorem cos_mul_cos_le_cos_half_sq (a b : ℝ) : cos a * cos b ≤ cos ((a + b) / 2) ^ 2 := by
  have h1 : cos a * cos b = (cos (a - b) + cos (a + b)) / 2 := by
    rw [cos_sub, cos_add]
    ring
  have h2 : cos ((a + b) / 2) ^ 2 = 1 / 2 + cos (a + b) / 2 := by
    rw [cos_sq, show 2 * ((a + b) / 2) = a + b by ring]
  rw [h1, h2]
  linarith [cos_le_one (a - b)]

/-- Evening out two neighbouring plates never loses length. -/
theorem even_turns_keep_more {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) :
    r * (cos a * cos b) ≤ r * cos ((a + b) / 2) ^ 2 :=
  mul_le_mul_of_nonneg_left (cos_mul_cos_le_cos_half_sq a b) hr

end Layers

end SquigglyLine
