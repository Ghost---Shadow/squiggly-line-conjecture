/-
Waves with a random phase.

`randomPhaseWave g w` is the random function `x ↦ g (w * x + φ)`, where `g` is
any profile of period `T` and the phase `φ` is uniform on the circle. With
`g = A * sin` this is the curve family of `scripts/frequency_isolation.py`.

The frequency `w` changes how squiggly the wave is. It does not change the
one-point marginal, because a uniform phase stays uniform after a shift.
-/
import Mathlib.Analysis.Fourier.AddCircle
import SquigglyLine.Theorem.RandomFunction

namespace SquigglyLine

open MeasureTheory

variable {T : ℝ} [Fact (0 < T)] {g : AddCircle T → ℝ}

/-- The wave `x ↦ g (w * x + φ)` with a uniformly random phase `φ`. -/
noncomputable def randomPhaseWave (g : AddCircle T → ℝ) (hg : Measurable g) (w : ℝ) :
    RandomFunction ℝ where
  Param := AddCircle T
  prior := AddCircle.haarAddCircle
  eval φ x := g (↑(w * x) + φ)
  measurable_eval _ := hg.comp (measurable_const_add _)

/-- At every input, the wave's output is distributed as the profile at a uniform phase. -/
theorem marginal_randomPhaseWave (hg : Measurable g) (w x : ℝ) :
    (randomPhaseWave g hg w).marginal x = Measure.map g AddCircle.haarAddCircle :=
  calc (randomPhaseWave g hg w).marginal x
      = Measure.map g (Measure.map (↑(w * x) + ·) AddCircle.haarAddCircle) :=
        (Measure.map_map hg (measurable_const_add _)).symm
    _ = Measure.map g AddCircle.haarAddCircle := by rw [map_add_left_eq_self]

/-- **Frequency is invisible in the marginals.** -/
theorem marginal_randomPhaseWave_eq (hg : Measurable g) (w w' : ℝ) :
    (randomPhaseWave g hg w).marginal = (randomPhaseWave g hg w').marginal := by
  funext x
  rw [marginal_randomPhaseWave, marginal_randomPhaseWave]

section Sine

open Real

instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The sine as a function on the circle of circumference `2π`. -/
theorem continuous_circleSin : Continuous fun θ : AddCircle (2 * π) => Angle.sin θ :=
  Angle.continuous_sin

/-- The sine `A * sin (w * x + φ)` with a uniformly random phase `φ`: the curve family of
`scripts/frequency_isolation.py`. -/
noncomputable def sineWave (A w : ℝ) : RandomFunction ℝ :=
  randomPhaseWave (fun θ => A * Angle.sin θ) (continuous_circleSin.measurable.const_mul A) w

/-- The frequency of a random-phase sine does not change its one-point marginals. -/
theorem marginal_sineWave_eq (A w w' : ℝ) : (sineWave A w).marginal = (sineWave A w').marginal :=
  marginal_randomPhaseWave_eq _ w w'

end Sine

end SquigglyLine
