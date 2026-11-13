/-
What "squiggly" has to mean for the conjecture to hold.

Say that `f` covers the label range `s` within `ρ` when, near every input and
for every label in `s`, some input at distance at most `ρ` is sent exactly to
that label. The smallest such `ρ` is the oscillation scale of `f`: how far one
has to walk along the input to see every label.

Two bounds pin the nearest-point distance to this scale:

    nearest ≤ ρ                       (covering, this file)
    vertical ≤ √(1 + K²) * nearest    (slope, `Sandwich.lean`)

So "closer to the data" is the same thing as "small oscillation scale", and a
small oscillation scale forces a large slope: `vertical ≤ √(1 + K²) * ρ`.
The conjecture is therefore a statement about how the oscillation scale of a
random function depends on the size of the model, and about nothing else.
-/
import SquigglyLine.Theorem.RandomFunction
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open MeasureTheory NNReal

variable {X : Type*} [SeminormedAddCommGroup X] {f : X → ℝ} {ρ : ℝ} {s : Set ℝ}

/-- Near every input, within distance `ρ`, the function takes every label in `s`. -/
def COVERS_WITHIN (f : X → ℝ) (ρ : ℝ) (s : Set ℝ) : Prop :=
  ∀ x, ∀ y ∈ s, ∃ x', dist x x' ≤ ρ ∧ f x' = y

theorem nearestDist_nonneg (f : X → ℝ) (p : DataPoint X) : 0 ≤ GET_NEAREST_DISTANCE f p :=
  Metric.infDist_nonneg

/-- **Covering bound.** A function that covers the labels within `ρ` is within `ρ` of every
data point whose label is in range. -/
theorem nearestDist_le_of_coversWithin (h : COVERS_WITHIN f ρ s) (p : DataPoint X)
    (hp : p.2 ∈ s) : GET_NEAREST_DISTANCE f p ≤ ρ := by
  obtain ⟨x', hx', hy⟩ := h p.1 p.2 hp
  calc GET_NEAREST_DISTANCE f p
      ≤ dist (EMBED_DATA_POINT p) (EMBED_DATA_POINT (x', f x')) :=
        Metric.infDist_le_dist_of_mem (footpoint_mem_curve f (x', f x'))
    _ = dist p.1 x' := by simp [dist_embed, hy, Real.sqrt_sq dist_nonneg]
    _ ≤ ρ := hx'

/-- **The slope tax.** Covering the labels within a short distance needs a steep function:
the vertical error is at most `√(1 + K²)` times the oscillation scale. -/
theorem verticalDist_le_of_lipschitz_of_coversWithin {K : ℝ≥0} (hf : LipschitzWith K f)
    (h : COVERS_WITHIN f ρ s) (p : DataPoint X) (hp : p.2 ∈ s) :
    GET_VERTICAL_ERROR f p ≤ √(1 + (K : ℝ) ^ 2) * ρ :=
  (verticalDist_le_of_lipschitz hf p).trans
    (mul_le_mul_of_nonneg_left (nearestDist_le_of_coversWithin h p hp) (Real.sqrt_nonneg _))

/-- **Nearness can be used, by moving the input.** If `f` covers the labels within `ρ`, then
any target with labels in range is fitted exactly by `f` after a warp of the input that moves
no point by more than `ρ`. The loss at the start does not see the nearness; a small shift of
the input cashes it in. -/
theorem exists_warp_of_coversWithin (h : COVERS_WITHIN f ρ s) (target : X → ℝ)
    (ht : ∀ x, target x ∈ s) :
    ∃ warp : X → X, (∀ x, dist x (warp x) ≤ ρ) ∧ ∀ x, f (warp x) = target x := by
  choose warp hwarp using fun x => h x (target x) (ht x)
  exact ⟨warp, fun x => (hwarp x).1, fun x => (hwarp x).2⟩

section Expected

variable [MeasurableSpace X]

theorem expected_nearestDist_nonneg (F : RandomFunction X) (μ : Measure (DataPoint X)) :
    0 ≤ F.expected GET_NEAREST_DISTANCE μ :=
  integral_nonneg fun _ => integral_nonneg fun _ => nearestDist_nonneg _ _

/-- **Covering bound, in expectation.** If every draw of a random function covers the labels
within `ρ`, its expected nearest-point distance is at most `ρ`, on any data whose labels are
in range. -/
theorem expected_nearestDist_le (F : RandomFunction X)
    (hcov : ∀ θ, COVERS_WITHIN (F.eval θ) ρ s) (μ : Measure (DataPoint X))
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ p ∂μ, p.2 ∈ s) : F.expected GET_NEAREST_DISTANCE μ ≤ ρ := by
  have inner : ∀ p : DataPoint X, p.2 ∈ s → ∫ θ, GET_NEAREST_DISTANCE (F.eval θ) p ∂F.prior ≤ ρ :=
    fun p hp =>
      calc ∫ θ, GET_NEAREST_DISTANCE (F.eval θ) p ∂F.prior
          ≤ ∫ _, ρ ∂F.prior :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => nearestDist_nonneg _ _)
              (integrable_const ρ)
              (ae_of_all _ fun θ => nearestDist_le_of_coversWithin (hcov θ) p hp)
        _ = ρ := by simp
  calc F.expected GET_NEAREST_DISTANCE μ
      ≤ ∫ _, ρ ∂μ :=
        integral_mono_of_nonneg
          (ae_of_all _ fun _ => integral_nonneg fun _ => nearestDist_nonneg _ _)
          (integrable_const ρ) (hμ.mono inner)
    _ = ρ := by simp

end Expected

end SquigglyLine
