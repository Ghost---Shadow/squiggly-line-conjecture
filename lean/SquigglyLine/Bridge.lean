/-
The bridge, part 1: a fold is a frequency doubling.

Look at the output of the wind tunnel through the fixed lens `sin² (π/2 · y)`.
One `tent` layer then doubles the angle inside the sine:

    sin² (π/2 · tent x) = sin² (π · x)

and `L` layers double it `L` times:

    sin² (π/2 · tent^[L] x) = sin² (2 ^ L · (π/2 · x))

The right side is a single Fourier term, of frequency `2 ^ L` once the square
is written as a cosine. So depth in the ReLU model is the logarithm of
frequency in the Fourier model.
-/
import SquigglyLine.Depth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace SquigglyLine

open Real

variable {x : ℝ}

theorem tent_mem_Icc (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ tent x ∧ tent x ≤ 1 := by
  rcases le_total x (1 / 2) with h | h
  · rw [tent_of_le_half h0 h]
    constructor <;> linarith
  · rw [tent_of_half_le h]
    constructor <;> linarith

/-- The wind tunnel keeps the unit interval inside the unit interval. -/
theorem iterate_tent_mem_Icc (h0 : 0 ≤ x) (h1 : x ≤ 1) (L : ℕ) :
    0 ≤ tent^[L] x ∧ tent^[L] x ≤ 1 := by
  induction L with
  | zero => exact ⟨h0, h1⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact tent_mem_Icc ih.1 ih.2

/-- **One fold doubles the angle.** -/
theorem sin_sq_tent (h0 : 0 ≤ x) : sin (π / 2 * tent x) ^ 2 = sin (π * x) ^ 2 := by
  rcases le_total x (1 / 2) with h | h
  · rw [tent_of_le_half h0 h, show π / 2 * (2 * x) = π * x by ring]
  · rw [tent_of_half_le h, show π / 2 * (2 - 2 * x) = π - π * x by ring, sin_pi_sub]

theorem sin_sq_two_mul (t : ℝ) : sin (2 * t) ^ 2 = 4 * sin t ^ 2 * (1 - sin t ^ 2) := by
  rw [sin_two_mul, ← cos_sq']
  ring

/-- **`L` folds are one Fourier term of frequency `2 ^ L`.** Seen through the lens
`sin² (π/2 · y)`, the wind tunnel of depth `L` is `sin²` of `2 ^ L` times the input angle. -/
theorem sin_sq_iterate_tent (h0 : 0 ≤ x) (h1 : x ≤ 1) (L : ℕ) :
    sin (π / 2 * tent^[L] x) ^ 2 = sin (2 ^ L * (π / 2 * x)) ^ 2 := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', sin_sq_tent (iterate_tent_mem_Icc h0 h1 n).1,
      show π * tent^[n] x = 2 * (π / 2 * tent^[n] x) by ring,
      show (2 : ℝ) ^ (n + 1) * (π / 2 * x) = 2 * (2 ^ n * (π / 2 * x)) by ring,
      sin_sq_two_mul, sin_sq_two_mul, ih]

end SquigglyLine
