/-
The conjecture, settled for sines.

A sine of frequency `w` takes every value of its band within `π / w` of every
input. So its nearest-point distance to in-band data is at most `π / w`, for
every phase, and tends to zero as the frequency grows. That is the geometric
half of the conjecture, as a theorem.

`closer_but_no_better` puts it next to `Verdict.lean`: along the same family
the nearest-point distance goes to zero while every regression loss stays
exactly where it was.
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import SquigglyLine.Theorem.Oscillation
import SquigglyLine.Theorem.Verdict

namespace SquigglyLine

open MeasureTheory Filter Topology Real

/-- A real sine of frequency `w` takes every value in `[-|A|, |A|]` within `π / w` of
every input. -/
theorem sin_coversWithin (A φ : ℝ) {w : ℝ} (hw : 0 < w) :
    COVERS_WITHIN (fun x : ℝ => A * sin (w * x + φ)) (π / w) (Set.Icc (-|A|) |A|) := by
  intro x y hy
  rcases eq_or_ne A 0 with rfl | hA
  · have hy0 : y = 0 := by
      have := hy.1; have := hy.2; simp at *; linarith
    exact ⟨x, by simpa using (div_pos pi_pos hw).le, by simp [hy0]⟩
  have hratio : |y / A| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr hA)]
    exact abs_le.mpr hy
  obtain ⟨hlo, hhi⟩ := abs_le.mp hratio
  set t := arcsin (y / A) with ht
  set θ₀ := w * x + φ with hθ₀
  set k : ℤ := round ((θ₀ - t) / (2 * π)) with hk
  set θ := t + k * (2 * π) with hθ
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hclose : |θ₀ - θ| ≤ π := by
    have hround := abs_sub_round ((θ₀ - t) / (2 * π))
    have hsplit : θ₀ - θ = (2 * π) * ((θ₀ - t) / (2 * π) - k) := by
      rw [hθ]; field_simp; ring
    rw [hsplit, abs_mul, abs_of_pos hπ]
    nlinarith [abs_nonneg ((θ₀ - t) / (2 * π) - k)]
  refine ⟨(θ - φ) / w, ?_, ?_⟩
  · have hdist : x - (θ - φ) / w = (θ₀ - θ) / w := by
      rw [hθ₀]; field_simp; ring
    rw [Real.dist_eq, hdist, abs_div, abs_of_pos hw]
    exact div_le_div_of_nonneg_right hclose hw.le
  · have harg : w * ((θ - φ) / w) + φ = t + k * (2 * π) := by
      rw [hθ]; field_simp; ring
    show A * sin (w * ((θ - φ) / w) + φ) = y
    rw [harg, sin_add_int_mul_two_pi, ht, sin_arcsin hlo hhi]
    field_simp

/-- **Once the phase matches.** For any data point with its label in the band, a change of
phase of at most half a turn makes the sine pass through it. The change needed does not
shrink with the frequency: a squigglier sine is closer in the input and exactly as far in
the phase. -/
theorem sin_exists_phaseShift (A φ : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ) {y : ℝ}
    (hy : y ∈ Set.Icc (-|A|) |A|) : ∃ δ : ℝ, |δ| ≤ π ∧ A * sin (w * x + (φ + δ)) = y := by
  obtain ⟨x', hx', hfit⟩ := sin_coversWithin A φ hw x y hy
  refine ⟨w * (x' - x), ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hw, abs_sub_comm, ← Real.dist_eq]
    calc w * dist x x' ≤ w * (π / w) := mul_le_mul_of_nonneg_left hx' hw.le
      _ = π := by field_simp
  · rw [← hfit]
    congr 2
    ring

/-- With the phase written as a real number, the random-phase sine is the usual sine. -/
theorem sineWave_eval_coe (A w φ : ℝ) :
    (MAKE_RANDOM_PHASE_SINE A w).eval (φ : AddCircle (2 * π)) = fun x => A * sin (w * x + φ) := by
  funext x
  show A * Angle.sin ((↑(w * x) : Angle) + (↑φ : Angle)) = _
  rw [← Angle.coe_add, Angle.sin_coe]

/-- Every draw of the random-phase sine covers its band within `π / w`. -/
theorem sineWave_coversWithin (A : ℝ) {w : ℝ} (hw : 0 < w) (φ : (MAKE_RANDOM_PHASE_SINE A w).Param) :
    COVERS_WITHIN ((MAKE_RANDOM_PHASE_SINE A w).eval φ) (π / w) (Set.Icc (-|A|) |A|) := by
  obtain ⟨φ', rfl⟩ : ∃ φ' : ℝ, (φ' : AddCircle (2 * π)) = φ := QuotientAddGroup.mk_surjective φ
  rw [sineWave_eval_coe]
  exact sin_coversWithin A φ' hw

/-- A sine of amplitude `A` and frequency `w` has slope at most `|A| * |w|`. -/
theorem lipschitzWith_sine (A w φ : ℝ) :
    LipschitzWith (‖A‖₊ * ‖w‖₊) (fun x : ℝ => A * sin (w * x + φ)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := abs_sin_sub_sin_le (w * x + φ) (w * y + φ)
  have hw : w * x + φ - (w * y + φ) = w * (x - y) := by ring
  rw [hw, abs_mul] at h
  simp only [Real.dist_eq, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  rw [← mul_sub, abs_mul]
  calc |A| * |sin (w * x + φ) - sin (w * y + φ)|
      ≤ |A| * (|w| * |x - y|) := mul_le_mul_of_nonneg_left h (abs_nonneg A)
    _ = |A| * |w| * |x - y| := by ring

/-- **Claim G for sines, pinned from both sides, at every data point and every phase.**
For a label in the band, the nearest-point distance lies between the vertical error divided
by `√(1 + (A w)²)` and `π / w`. Both ends fall like `1 / w`. -/
theorem sineWave_nearestDist_bounds (A : ℝ) {w : ℝ} (hw : 0 < w) (φ : (MAKE_RANDOM_PHASE_SINE A w).Param)
    (p : DataPoint ℝ) (hp : p.2 ∈ Set.Icc (-|A|) |A|) :
    GET_VERTICAL_ERROR ((MAKE_RANDOM_PHASE_SINE A w).eval φ) p / √(1 + (A * w) ^ 2)
        ≤ GET_NEAREST_DISTANCE ((MAKE_RANDOM_PHASE_SINE A w).eval φ) p ∧
      GET_NEAREST_DISTANCE ((MAKE_RANDOM_PHASE_SINE A w).eval φ) p ≤ π / w := by
  refine ⟨?_, nearestDist_le_of_coversWithin (sineWave_coversWithin A hw φ) p hp⟩
  obtain ⟨φ', rfl⟩ : ∃ φ' : ℝ, (φ' : AddCircle (2 * π)) = φ := QuotientAddGroup.mk_surjective φ
  rw [sineWave_eval_coe, div_le_iff₀' (by positivity)]
  have h := verticalDist_le_of_lipschitz (lipschitzWith_sine A w φ') p
  have hK : ((‖A‖₊ * ‖w‖₊ : NNReal) : ℝ) ^ 2 = (A * w) ^ 2 := by simp [mul_pow]
  rwa [hK] at h

/-- **A sine fits anything in its band, after a small warp.** Any target with values in the
band is matched exactly by the sine of frequency `w` after moving each input by at most
`π / w`. For a single data point this is a shift of the phase. -/
theorem sineWave_exists_warp (A : ℝ) {w : ℝ} (hw : 0 < w) (φ : (MAKE_RANDOM_PHASE_SINE A w).Param)
    (target : ℝ → ℝ) (ht : ∀ x, target x ∈ Set.Icc (-|A|) |A|) :
    ∃ warp : ℝ → ℝ, (∀ x, dist x (warp x) ≤ π / w) ∧
      ∀ x, (MAKE_RANDOM_PHASE_SINE A w).eval φ (warp x) = target x :=
  exists_warp_of_coversWithin (sineWave_coversWithin A hw φ) target ht

variable {μ : Measure (DataPoint ℝ)} [IsProbabilityMeasure μ]

/-- **Claim G for sines, with a rate.** On data whose labels lie in the band, the expected
nearest-point distance of a random-phase sine of frequency `w` is at most `π / w`. -/
theorem expected_nearestDist_sineWave_le (A : ℝ) {w : ℝ} (hw : 0 < w)
    (hμ : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (-|A|) |A|) :
    (MAKE_RANDOM_PHASE_SINE A w).expected GET_NEAREST_DISTANCE μ ≤ π / w :=
  expected_nearestDist_le _ (sineWave_coversWithin A hw) μ hμ

/-- **Claim G for sines, in the limit.** The expected nearest-point distance tends to zero as
the frequency grows. -/
theorem tendsto_expected_nearestDist_sineWave (A : ℝ)
    (hμ : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (-|A|) |A|) :
    Tendsto (fun w : ℝ => (MAKE_RANDOM_PHASE_SINE A w).expected GET_NEAREST_DISTANCE μ) atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun _ => expected_nearestDist_nonneg _ μ)
    ((eventually_gt_atTop 0).mono fun _ hw => expected_nearestDist_sineWave_le A hw hμ)
    (tendsto_const_nhds.div_atTop tendsto_id)

/-- **Closer, but no better.** As the frequency of a random-phase sine grows, its expected
distance to the nearest point of the data tends to zero, and its expected loss, for every
regression loss, does not change at all. -/
theorem closer_but_no_better (A : ℝ) {ℓ : ℝ → ℝ} (hℓ : Measurable ℓ)
    (hμ : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (-|A|) |A|) :
    Tendsto (fun w : ℝ => (MAKE_RANDOM_PHASE_SINE A w).expected GET_NEAREST_DISTANCE μ) atTop (𝓝 0) ∧
      ∀ w w' : ℝ, (MAKE_RANDOM_PHASE_SINE A w).expected (GET_RESIDUAL_LOSS ℓ) μ
        = (MAKE_RANDOM_PHASE_SINE A w').expected (GET_RESIDUAL_LOSS ℓ) μ :=
  ⟨tendsto_expected_nearestDist_sineWave A hμ,
    fun w w' => expected_residualLoss_congr hℓ (marginal_sineWave_eq A w w') μ⟩

end SquigglyLine
