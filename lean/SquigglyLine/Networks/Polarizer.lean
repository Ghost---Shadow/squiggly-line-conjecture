/-
ReLU as a polarizer with a wide opening.

In the plane, ReLU sends each point to the nearest point of the positive
quadrant. A layer that rotates and then applies ReLU (a `APPLY_FAN`) therefore acts
on a bird sitting on the edge of the quadrant like a polarizer on light:

* turn by `θ ≤ 90°`  : the bird is pressed back onto the edge and keeps the
                       fraction `cos θ` of its length (Malus's law);
* turn by `θ ≥ 90°`  : the bird is blocked.

So `N` small turns keep `cos θ ^ N`, and a half turn split into `N` steps
keeps at least `1 - π² / (2N)`, which tends to 1. One big turn loses
everything; many small ones lose almost nothing. This is the three-polarizer
effect.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace SquigglyLine

open Real

/-- ReLU on the plane. -/
def APPLY_RELU_TO_PAIR (p : ℝ × ℝ) : ℝ × ℝ :=
  (max p.1 0, max p.2 0)

/-- Rotation of the plane by the angle `θ`. -/
noncomputable def ROTATE (θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cos θ * p.1 - sin θ * p.2, sin θ * p.1 + cos θ * p.2)

/-- One layer of the wind tunnel: rotate, then ReLU. -/
noncomputable def APPLY_FAN (θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  APPLY_RELU_TO_PAIR (ROTATE θ p)

theorem abs_sub_relu_le (x : ℝ) {u : ℝ} (hu : 0 ≤ u) : |x - max x 0| ≤ |x - u| := by
  rcases le_total 0 x with hx | hx
  · simp [max_eq_left hx]
  · rw [max_eq_right hx, sub_zero, abs_of_nonpos hx, abs_of_nonpos (by linarith)]
    linarith

/-- **ReLU is a projection.** It sends a point to the nearest point of the positive quadrant. -/
theorem relu2_nearest (p u : ℝ × ℝ) (hu₁ : 0 ≤ u.1) (hu₂ : 0 ≤ u.2) :
    (p.1 - (APPLY_RELU_TO_PAIR p).1) ^ 2 + (p.2 - (APPLY_RELU_TO_PAIR p).2) ^ 2 ≤ (p.1 - u.1) ^ 2 + (p.2 - u.2) ^ 2 :=
  add_le_add (sq_le_sq.mpr (abs_sub_relu_le p.1 hu₁)) (sq_le_sq.mpr (abs_sub_relu_le p.2 hu₂))

variable {r θ : ℝ}

/-- **Malus's law.** A bird on the edge, turned out of the quadrant by `θ ≤ 90°`, is pressed
back onto the edge and keeps the fraction `cos θ` of its length. -/
theorem fan_of_le_pi_div_two (hr : 0 ≤ r) (h0 : 0 ≤ θ) (hθ : θ ≤ π / 2) :
    APPLY_FAN (-θ) (r, 0) = (r * cos θ, 0) := by
  have hc : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hθ⟩
  have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
  ext
  · show max (cos (-θ) * r - sin (-θ) * 0) 0 = r * cos θ
    rw [cos_neg, mul_zero, sub_zero, max_eq_left (mul_nonneg hc hr), mul_comm]
  · show max (sin (-θ) * r + cos (-θ) * 0) 0 = 0
    rw [sin_neg, mul_zero, add_zero, max_eq_right]
    nlinarith [mul_nonneg hs hr]

/-- **Crossed polarizers.** A bird turned by between 90° and 180° in one step is blocked. -/
theorem fan_of_pi_div_two_le (hr : 0 ≤ r) (hθ : π / 2 ≤ θ) (hπ : θ ≤ π) :
    APPLY_FAN (-θ) (r, 0) = (0, 0) := by
  have hc : cos θ ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hθ (by linarith [pi_pos])
  have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi (by linarith [pi_pos]) hπ
  ext
  · show max (cos (-θ) * r - sin (-θ) * 0) 0 = 0
    rw [cos_neg, mul_zero, sub_zero, max_eq_right (mul_nonpos_of_nonpos_of_nonneg hc hr)]
  · show max (sin (-θ) * r + cos (-θ) * 0) 0 = 0
    rw [sin_neg, mul_zero, add_zero, max_eq_right]
    nlinarith [mul_nonneg hs hr]

/-- **Many small turns.** `N` layers, each turning by `θ ≤ 90°`, keep `cos θ ^ N`. -/
theorem iterate_fan (hr : 0 ≤ r) (h0 : 0 ≤ θ) (hθ : θ ≤ π / 2) (N : ℕ) :
    (APPLY_FAN (-θ))^[N] (r, 0) = (r * cos θ ^ N, 0) := by
  have hc : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hθ⟩
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      fan_of_le_pi_div_two (mul_nonneg hr (pow_nonneg hc n)) h0 hθ, pow_succ, mul_assoc]

/-- **The three-polarizer effect.** A half turn split into `N ≥ 3` equal steps keeps at
least `1 - π² / (2N)` of the length. Split into one step it keeps nothing. -/
theorem one_sub_le_cos_pow {N : ℕ} (hN : 3 ≤ N) : 1 - π ^ 2 / (2 * N) ≤ cos (π / N) ^ N := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set x := π / N with hx
  have hx0 : 0 ≤ x := div_nonneg pi_pos.le hNpos.le
  have hx1 : x ≤ 1.05 := by
    rw [hx, div_le_iff₀ hNpos]
    nlinarith [pi_lt_d2]
  have hbase : 0 ≤ 1 - x ^ 2 / 2 := by nlinarith
  calc 1 - π ^ 2 / (2 * N)
      = 1 + N * (-(x ^ 2 / 2)) := by rw [hx]; field_simp; ring
    _ ≤ (1 + -(x ^ 2 / 2)) ^ N := one_add_mul_le_pow (by nlinarith) N
    _ ≤ cos x ^ N :=
        pow_le_pow_left₀ (by linarith) (by linarith [one_sub_sq_div_two_le_cos (x := x)]) N

end SquigglyLine
