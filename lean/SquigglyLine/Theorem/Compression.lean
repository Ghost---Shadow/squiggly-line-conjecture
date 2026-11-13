/-
The squiggly line theorem, for any function.

"Squigglier" needs no sine. Squeeze any function sideways by a factor `w`:
`compress w f x = f (w • x)`. Then, exactly:

* closer   : it covers the labels within `ρ / w` if `f` covered them within `ρ`;
* steeper  : it is `w * K`-Lipschitz if `f` was `K`-Lipschitz;
* no better: if a random function has the same one-point marginal at every
             input, squeezing it changes no expected regression loss.

`squiggly_line_theorem_general` collects these, with the warp. The inputs may
have any dimension. The sine theorem is the case of a sine with a random phase.
-/
import SquigglyLine.Theorem.Marginal
import SquigglyLine.Theorem.Oscillation

namespace SquigglyLine

open MeasureTheory Filter Topology NNReal

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  {f : X → ℝ} {ρ w : ℝ} {s : Set ℝ}

/-- Squeeze a function sideways by the factor `w`. -/
def COMPRESS (w : ℝ) (f : X → ℝ) : X → ℝ :=
  fun x => f (w • x)

/-- **Closer.** Squeezing by `w` divides the oscillation scale by `w`. -/
theorem COVERS_WITHIN.compress (h : COVERS_WITHIN f ρ s) (hw : 0 < w) :
    COVERS_WITHIN (COMPRESS w f) (ρ / w) s := by
  intro x y hy
  obtain ⟨z, hz, hfz⟩ := h (w • x) y hy
  refine ⟨w⁻¹ • z, ?_, ?_⟩
  · have hx : x = w⁻¹ • (w • x) := by rw [smul_smul, inv_mul_cancel₀ hw.ne', one_smul]
    calc dist x (w⁻¹ • z)
        = dist (w⁻¹ • (w • x)) (w⁻¹ • z) := by rw [← hx]
      _ = w⁻¹ * dist (w • x) z := by
          rw [dist_smul₀, Real.norm_of_nonneg (inv_nonneg.mpr hw.le)]
      _ ≤ w⁻¹ * ρ := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hw.le)
      _ = ρ / w := by rw [div_eq_inv_mul]
  · show f (w • w⁻¹ • z) = y
    rw [smul_smul, mul_inv_cancel₀ hw.ne', one_smul, hfz]

/-- **Steeper.** Squeezing by `w` multiplies the slope by `w`. -/
theorem lipschitzWith_compress {K : ℝ≥0} (hf : LipschitzWith K f) (w : ℝ≥0) :
    LipschitzWith (w * K) (COMPRESS (w : ℝ) f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  calc dist (f ((w : ℝ) • x)) (f ((w : ℝ) • y))
      ≤ K * dist ((w : ℝ) • x) ((w : ℝ) • y) := hf.dist_le_mul _ _
    _ = ((w * K : ℝ≥0) : ℝ) * dist x y := by
        rw [dist_smul₀, Real.norm_of_nonneg w.coe_nonneg, NNReal.coe_mul]
        ring

section Random

variable [MeasurableSpace X]

/-- A random function, squeezed sideways by `w`. -/
def RandomFunction.compress (F : RandomFunction X) (w : ℝ) : RandomFunction X where
  Param := F.Param
  prior := F.prior
  eval θ := SquigglyLine.COMPRESS w (F.eval θ)
  measurable_eval x := F.measurable_eval (w • x)

/-- The output of the random function has the same distribution at every input. -/
def HAS_HOMOGENEOUS_MARGINALS (F : RandomFunction X) : Prop :=
  ∀ x x', F.marginal x = F.marginal x'

omit [MeasurableSpace X] in
/-- **No better.** Squeezing a random function with homogeneous marginals changes none of
its one-point marginals. -/
theorem marginal_compress_eq (F : RandomFunction X) (h : HAS_HOMOGENEOUS_MARGINALS F) (w w' : ℝ) :
    (F.compress w).marginal = (F.compress w').marginal := by
  funext x
  exact h (w • x) (w' • x)

/-- **The squiggly line theorem.** Squeeze a random function by `w`. If every draw covers the
labels within `ρ` and is `K`-Lipschitz, and its one-point marginal is the same at every input,
then: the nearest-point distance lies between the vertical error divided by `√(1 + (w K)²)`
and `ρ / w`; its expectation tends to zero as `w` grows; no expected regression loss
changes; and a warp of the input of size at most `ρ / w` fits any target. -/
theorem squiggly_line_theorem_general (F : RandomFunction X) {K : ℝ≥0}
    (hcov : ∀ θ, COVERS_WITHIN (F.eval θ) ρ s) (hlip : ∀ θ, LipschitzWith K (F.eval θ))
    (hhom : HAS_HOMOGENEOUS_MARGINALS F) {ℓ : ℝ → ℝ} (hℓ : Measurable ℓ)
    (μ : Measure (DataPoint X)) [IsProbabilityMeasure μ] (hμ : ∀ᵐ p ∂μ, p.2 ∈ s) :
    (∀ {w : ℝ}, 0 < w → ∀ (θ : F.Param) (p : DataPoint X), p.2 ∈ s →
        GET_VERTICAL_ERROR ((F.compress w).eval θ) p / √(1 + (w * K) ^ 2)
            ≤ GET_NEAREST_DISTANCE ((F.compress w).eval θ) p ∧
          GET_NEAREST_DISTANCE ((F.compress w).eval θ) p ≤ ρ / w) ∧
      Tendsto (fun w : ℝ => (F.compress w).expected GET_NEAREST_DISTANCE μ) atTop (𝓝 0) ∧
      (∀ w w' : ℝ, (F.compress w).expected (GET_RESIDUAL_LOSS ℓ) μ
        = (F.compress w').expected (GET_RESIDUAL_LOSS ℓ) μ) ∧
      ∀ {w : ℝ}, 0 < w → ∀ (θ : F.Param) (target : X → ℝ), (∀ x, target x ∈ s) →
        ∃ warp : X → X, (∀ x, dist x (warp x) ≤ ρ / w) ∧
          ∀ x, (F.compress w).eval θ (warp x) = target x := by
  refine ⟨fun {w} hw θ p hp => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have hK := verticalDist_le_of_lipschitz (lipschitzWith_compress (hlip θ) ⟨w, hw.le⟩) p
    change GET_VERTICAL_ERROR (COMPRESS w (F.eval θ)) p
      ≤ √(1 + (w * (K : ℝ)) ^ 2) * GET_NEAREST_DISTANCE (COMPRESS w (F.eval θ)) p at hK
    rw [div_le_iff₀' (by positivity)]
    exact hK
  · exact nearestDist_le_of_coversWithin ((hcov θ).compress hw) p hp
  · refine squeeze_zero' (Eventually.of_forall fun _ => expected_nearestDist_nonneg _ μ)
      ((eventually_gt_atTop 0).mono fun w hw =>
        expected_nearestDist_le (F.compress w) (fun θ => (hcov θ).compress hw) μ hμ)
      (tendsto_const_nhds.div_atTop tendsto_id)
  · exact fun w w' => expected_residualLoss_congr hℓ (marginal_compress_eq F hhom w w') μ
  · exact fun {w} hw θ target ht =>
      exists_warp_of_coversWithin ((hcov θ).compress hw) target ht

end Random

end SquigglyLine
