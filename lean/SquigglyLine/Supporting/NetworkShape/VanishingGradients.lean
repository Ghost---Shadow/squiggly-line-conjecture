/-
Vanishing and exploding signals.

If each layer multiplies the size of the signal by a gain `g`, then `L` layers
multiply it by `g ^ L`.

* `gain_pow_le_exp` : below one it dies, at least as fast as
  `exp (-(L * (1 - g)))`.
* `one_add_mul_le_gain_pow` : above one it grows, at least as fast as
  `1 + L * (g - 1)`.
* `norm_plate_le`, `plates_vanish` : a polarizer plate never lengthens the
  light, and a stack with a fixed turn dims it exponentially.
* `inner_plate_comm`, `inner_runPlates` : the gradient is the read-out sent
  back through the same plates in the opposite order, so it is dimmed by the
  same plates.
* `le_norm_iterate_skipPlate` : plates with a bypass make the light at least
  `2 ^ k` times as long as its first overlap with the axis.
-/
import SquigglyLine.Networks.MarkovChains
import SquigglyLine.Supporting.NetworkShape.SkipAndNorm
import SquigglyLine.Supporting.Training.SpectralBias

namespace SquigglyLine

/-! ### One number per layer -/

section Gain

/-- **A gain below one dies.** The loss is exponential in the depth. -/
theorem gain_pow_le_exp {g : ℝ} (h0 : 0 ≤ g) (L : ℕ) : g ^ L ≤ Real.exp (-(L * (1 - g))) := by
  have h := pow_one_sub_le_exp (show 1 - g ≤ 1 by linarith) L
  rwa [sub_sub_cancel] at h

/-- **A gain above one blows up.** -/
theorem one_add_mul_le_gain_pow {g : ℝ} (h1 : 1 ≤ g) (L : ℕ) : 1 + L * (g - 1) ≤ g ^ L := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ g - 1 by linarith) L
  rwa [add_sub_cancel] at h

/-- **A stack of plates with a fixed turn dims the light exponentially.** -/
theorem plates_vanish {θ : ℝ} (hcos : 0 ≤ Real.cos θ) (L : ℕ) :
    Real.cos θ ^ L ≤ Real.exp (-(L * (1 - Real.cos θ))) :=
  gain_pow_le_exp hcos L

end Gain

/-! ### Plates, forwards and backwards -/

section Plates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E}

/-- **A plate never lengthens the light.** -/
theorem norm_plate_le (he : ‖e‖ = 1) (v : E) : ‖plate e v‖ ≤ ‖v‖ := by
  rw [norm_plate he]
  calc |inner ℝ e v| ≤ ‖e‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = ‖v‖ := by rw [he, one_mul]

/-- **A plate acts the same way forwards and backwards.** -/
theorem inner_plate_comm (e v w : E) : inner ℝ (plate e v) w = inner ℝ v (plate e w) := by
  rw [plate, plate, real_inner_smul_left, real_inner_smul_right, real_inner_comm e v]
  ring

/-- **The gradient comes back through the same plates.** Reading the output of a stack of
plates along `w` is the same as reading the input along `w` sent through the plates in the
opposite order. -/
theorem inner_runPlates (axes : List E) (v w : E) :
    inner ℝ (runLayers (axes.map plate) v) w
      = inner ℝ v (runLayers (axes.reverse.map plate) w) := by
  induction axes generalizing v with
  | nil => rfl
  | cons e rest ih =>
    have hback : runLayers ((e :: rest).reverse.map plate) w
        = plate e (runLayers (rest.reverse.map plate) w) := by
      simp [runLayers, runLayers_append]
    have hfwd : runLayers ((e :: rest).map plate) v = runLayers (rest.map plate) (plate e v) := by
      simp [runLayers]
    rw [hback, hfwd, ih, inner_plate_comm]

/-- **Plates with a bypass blow up.** After `k` of them on one axis the light is at least
`2 ^ k` times as long as its first overlap with the axis. -/
theorem le_norm_iterate_skipPlate (he : ‖e‖ = 1) (v : E) (k : ℕ) :
    2 ^ k * |inner ℝ e v| ≤ ‖(skipPlate e)^[k] v‖ := by
  calc 2 ^ k * |inner ℝ e v| = |inner ℝ e ((skipPlate e)^[k] v)| := by
        rw [inner_iterate_skipPlate he, abs_mul,
          abs_of_nonneg (pow_nonneg (zero_le_two (α := ℝ)) k)]
    _ ≤ ‖e‖ * ‖(skipPlate e)^[k] v‖ := abs_real_inner_le_norm _ _
    _ = ‖(skipPlate e)^[k] v‖ := by rw [he, one_mul]

end Plates

end SquigglyLine
