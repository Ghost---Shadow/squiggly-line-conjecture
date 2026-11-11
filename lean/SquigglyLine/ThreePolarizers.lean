/-
Three polarizers, and the photon's squiggly line.

`light a ψ` is an arrow of length `a` pointing at angle `ψ`: light of strength
`a` vibrating along `ψ`. A `polarizer φ` replaces an arrow by its shadow on
the direction `φ`.

* `malus`: the shadow has length `a * cos (φ - ψ)` and points along `φ`.
* `polarizer_crossed`: a plate at 90° to the arrow blocks it.
* `throughPlates_light`: after `k` plates, each turned by `θ` from the last,
  the arrow has length `a * cos θ ^ k` and angle `k * θ`. The tips of these
  arrows are the photon's squiggly line.
* `three_polarizers`: a plate at 45° and then one at 90° pass half the
  length, where the 90° plate alone passes none.
* `quarter_turn_arrives`: a quarter turn in `N ≥ 2` plates delivers at least
  `1 - π² / (8N)` of the length. More plates, a squigglier path, a closer end.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace SquigglyLine

open Real

/-- An arrow of length `a` at angle `ψ`: light of strength `a` vibrating along `ψ`. -/
noncomputable def light (a ψ : ℝ) : ℝ × ℝ :=
  (a * cos ψ, a * sin ψ)

/-- A polarizer with its axis at angle `φ`: the shadow of the arrow on that direction. -/
noncomputable def polarizer (φ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((v.1 * cos φ + v.2 * sin φ) * cos φ, (v.1 * cos φ + v.2 * sin φ) * sin φ)

/-- **Malus's law.** The shadow has `cos` of the angle between arrow and axis. -/
theorem malus (a ψ φ : ℝ) : polarizer φ (light a ψ) = light (a * cos (φ - ψ)) φ := by
  ext <;> simp only [polarizer, light, cos_sub] <;> ring

theorem light_zero (ψ : ℝ) : light 0 ψ = (0, 0) := by
  simp [light]

/-- **Crossed plates block.** -/
theorem polarizer_crossed (a ψ : ℝ) : polarizer (ψ + π / 2) (light a ψ) = (0, 0) := by
  rw [malus, add_sub_cancel_left, cos_pi_div_two, mul_zero, light_zero]

/-- A stack of `k` plates, the `j`-th with its axis at `j * θ`. -/
noncomputable def throughPlates (θ : ℝ) : ℕ → ℝ × ℝ → ℝ × ℝ
  | 0, v => v
  | k + 1, v => polarizer (((k + 1 : ℕ) : ℝ) * θ) (throughPlates θ k v)

/-- **The photon's path.** After `k` plates the arrow has length `a * cos θ ^ k` and
angle `k * θ`. -/
theorem throughPlates_light (a θ : ℝ) (k : ℕ) :
    throughPlates θ k (light a 0) = light (a * cos θ ^ k) (k * θ) := by
  induction k with
  | zero => simp [throughPlates]
  | succ n ih =>
    rw [throughPlates, ih, malus,
      show ((n + 1 : ℕ) : ℝ) * θ - n * θ = θ by push_cast; ring, pow_succ, mul_assoc]

/-- **Three polarizers.** With a plate at 45° in between, half the length reaches the
vertical. -/
theorem three_polarizers : throughPlates (π / 4) 2 (light 1 0) = (0, 1 / 2) := by
  rw [throughPlates_light, light, one_mul, cos_pi_div_four,
    show ((2 : ℕ) : ℝ) * (π / 4) = π / 2 by push_cast; ring, cos_pi_div_two, sin_pi_div_two,
    mul_zero, mul_one, div_pow, sq_sqrt (by norm_num)]
  norm_num

/-- Without the plate in between, nothing reaches the vertical. -/
theorem two_polarizers : polarizer (π / 2) (light 1 0) = (0, 0) := by
  simpa using polarizer_crossed 1 0

/-- A small turn loses little: `cos x ^ N` is at least `1 - N * (x² / 2)`. -/
theorem one_sub_mul_le_cos_pow {x : ℝ} (hx : x ^ 2 ≤ 2) (N : ℕ) :
    1 - N * (x ^ 2 / 2) ≤ cos x ^ N :=
  calc 1 - N * (x ^ 2 / 2)
      = 1 + N * (-(x ^ 2 / 2)) := by ring
    _ ≤ (1 + -(x ^ 2 / 2)) ^ N := one_add_mul_le_pow (by nlinarith [sq_nonneg x]) N
    _ ≤ cos x ^ N :=
        pow_le_pow_left₀ (by linarith) (by linarith [one_sub_sq_div_two_le_cos (x := x)]) N

/-- **More plates, closer.** A quarter turn in `N ≥ 2` plates arrives pointing straight up,
with at least `1 - π² / (8N)` of its length. -/
theorem quarter_turn_arrives {N : ℕ} (hN : 2 ≤ N) :
    throughPlates (π / (2 * N)) N (light 1 0) = (0, cos (π / (2 * N)) ^ N) ∧
      1 - π ^ 2 / (8 * N) ≤ cos (π / (2 * N)) ^ N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  constructor
  · rw [throughPlates_light, light, one_mul,
      show (N : ℝ) * (π / (2 * N)) = π / 2 by field_simp, cos_pi_div_two, sin_pi_div_two,
      mul_zero, mul_one]
  · have hx0 : 0 ≤ π / (2 * N) := by positivity
    have hx1 : π / (2 * N) ≤ 0.7875 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pi_lt_d2]
    have h := one_sub_mul_le_cos_pow (x := π / (2 * N)) (by nlinarith) N
    calc 1 - π ^ 2 / (8 * N)
        = 1 - N * ((π / (2 * N)) ^ 2 / 2) := by field_simp; ring
      _ ≤ cos (π / (2 * N)) ^ N := h

end SquigglyLine
