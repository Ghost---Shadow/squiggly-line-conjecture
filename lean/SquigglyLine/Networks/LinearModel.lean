/-
Where "a bigger model starts closer" is true: parameter space.

Take a model whose outputs on the data are linear in its parameters, such as
a Fourier series in its coefficients: `A θ` is the vector of outputs, `y` the
vector of labels, `residual A y θ = y - A θ` what is left to fit.

In the terms of statistics this is a generalized linear model with no link
function and squared error, that is, linear regression on the features `A`.

* `residual_along`: on the straight path from a start `θ₀` to a fit `θ₁`, the
  residual shrinks in proportion. Every model walks the same loss curve.
* `exists_within_budget`: so moving a distance `ε` from the start removes the
  fraction `ε / ‖θ₁ - θ₀‖` of the residual. Loss gap = distance × steepness:
  the nearer the fit, the more a fixed budget of movement buys.
* `travel_coprod_le`: adding parameters never moves the nearest fit further
  away. A bigger model can always do what the smaller one did.

Together with `Marginal.lean`: at budget zero a bigger random model is no
closer to the data, and at every positive budget it is at least as close.
How much closer (measured: travel falls like `1 / √parameters`) is not proved here.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Module

namespace SquigglyLine

variable {Θ Θ' Y : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Θ'] [NormedSpace ℝ Θ']
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- What is left to fit: the labels minus the model's outputs. -/
def GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) (y : Y) (θ : Θ) : Y :=
  y - A θ

/-- The parameters a fraction `t` of the way from `θ₀` to `θ₁`. -/
def MOVE_ALONG (θ₀ θ₁ : Θ) (t : ℝ) : Θ :=
  θ₀ + t • (θ₁ - θ₀)

variable (A : Θ →ₗ[ℝ] Y) (y : Y) (θ₀ θ₁ : Θ)

/-- **Every model walks the same loss curve.** On the straight path to a fit, the residual
is the starting residual scaled by `1 - t`. -/
theorem residual_along (hfit : A θ₁ = y) (t : ℝ) :
    GET_RESIDUAL A y (MOVE_ALONG θ₀ θ₁ t) = (1 - t) • GET_RESIDUAL A y θ₀ := by
  simp only [GET_RESIDUAL, MOVE_ALONG, map_add, map_smul, map_sub, hfit]
  module

theorem norm_residual_along (hfit : A θ₁ = y) {t : ℝ} (ht : t ≤ 1) :
    ‖GET_RESIDUAL A y (MOVE_ALONG θ₀ θ₁ t)‖ = (1 - t) * ‖GET_RESIDUAL A y θ₀‖ := by
  rw [residual_along A y θ₀ θ₁ hfit, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht)]

theorem norm_along_sub {t : ℝ} (ht : 0 ≤ t) : ‖MOVE_ALONG θ₀ θ₁ t - θ₀‖ = t * ‖θ₁ - θ₀‖ := by
  simp [MOVE_ALONG, norm_smul, abs_of_nonneg ht]

/-- **Loss gap = distance × steepness.** If a fit lies at distance `d` from the start, then
moving a distance `ε ≤ d` removes the fraction `ε / d` of the residual. -/
theorem exists_within_budget (hfit : A θ₁ = y) (hne : θ₁ ≠ θ₀) {ε : ℝ} (hε : 0 ≤ ε)
    (hle : ε ≤ ‖θ₁ - θ₀‖) :
    ∃ θ, ‖θ - θ₀‖ = ε ∧
      ‖GET_RESIDUAL A y θ‖ = (1 - ε / ‖θ₁ - θ₀‖) * ‖GET_RESIDUAL A y θ₀‖ := by
  have hd : 0 < ‖θ₁ - θ₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  refine ⟨MOVE_ALONG θ₀ θ₁ (ε / ‖θ₁ - θ₀‖), ?_, ?_⟩
  · rw [norm_along_sub _ _ (div_nonneg hε hd.le), div_mul_cancel₀ _ hd.ne']
  · exact norm_residual_along A y θ₀ θ₁ hfit ((div_le_one hd).mpr hle)

/-- The distances from the start to the parameter vectors that fit the data. -/
def GET_FIT_DISTANCES : Set ℝ :=
  {d | ∃ θ, A θ = y ∧ ‖θ - θ₀‖ = d}

/-- The distance in parameter space from the start to the nearest fit. -/
noncomputable def GET_TRAVEL : ℝ :=
  sInf (GET_FIT_DISTANCES A y θ₀)

/-- **More parameters never move the fit away.** Extend the model with new parameters, with
their own features `B`, starting at zero. The nearest fit is then no further than before. -/
theorem travel_coprod_le (B : Θ' →ₗ[ℝ] Y) (hfit : ∃ θ, A θ = y) :
    GET_TRAVEL (A.coprod B) y (θ₀, 0) ≤ GET_TRAVEL A y θ₀ := by
  refine csInf_le_csInf ⟨0, ?_⟩ ?_ ?_
  · rintro d ⟨θ, -, rfl⟩
    exact norm_nonneg _
  · obtain ⟨θ, hθ⟩ := hfit
    exact ⟨_, θ, hθ, rfl⟩
  · rintro d ⟨θ, hθ, rfl⟩
    exact ⟨(θ, 0), by simp [hθ], by simp [Prod.norm_def]⟩

end SquigglyLine
