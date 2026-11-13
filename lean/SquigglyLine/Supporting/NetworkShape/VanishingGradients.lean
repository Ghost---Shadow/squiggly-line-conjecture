/-
Vanishing and exploding signals.

If each layer multiplies the size of the signal by a gain, then `layer_count`
layers multiply it by `gain ^ layer_count`.

* `gain_pow_le_exp` : below one it dies, at least as fast as
  `exp (-(layer_count * (1 - gain)))`.
* `one_add_mul_le_gain_pow` : above one it grows, at least as fast as
  `1 + layer_count * (gain - 1)`.
* `norm_plate_le`, `plates_vanish` : a polarizer plate never lengthens the
  light, and a stack with a fixed turn dims it exponentially.
* `inner_plate_comm`, `inner_runPlates` : the gradient is the read-out sent
  back through the same plates in the opposite order, so it is dimmed by the
  same plates.
* `le_norm_iterate_skipPlate` : plates with a bypass make the light at least
  `2 ^ plate_count` times as long as its first overlap with the axis.
-/
import SquigglyLine.Networks.MarkovChains
import SquigglyLine.Supporting.NetworkShape.SkipAndNorm
import SquigglyLine.Supporting.Training.SpectralBias

namespace SquigglyLine

/-! ### One number per layer -/

section Gain

/-- **A gain below one dies.** The loss is exponential in the depth. -/
theorem gain_pow_le_exp
    {gain : ℝ}
    (gain_nonneg : 0 ≤ gain)
    (layer_count : ℕ) :
    let signal_after_layers := gain ^ layer_count
    let decay_bound := Real.exp (-(layer_count * (1 - gain)))  -- 1 - gain <= exp (-gain), raised to the depth
    signal_after_layers ≤ decay_bound := by
  unfold_named_pieces
  have step := pow_one_sub_le_exp (show 1 - gain ≤ 1 by linarith) layer_count
  rwa [sub_sub_cancel] at step

/-- **A gain above one blows up.** -/
theorem one_add_mul_le_gain_pow
    {gain : ℝ}
    (gain_at_least_one : 1 ≤ gain)
    (layer_count : ℕ) :
    let growth_bound : ℝ := 1 + layer_count * (gain - 1)  -- Bernoulli's inequality
    let signal_after_layers := gain ^ layer_count
    growth_bound ≤ signal_after_layers := by
  unfold_named_pieces
  have step := one_add_mul_le_pow (show (-2 : ℝ) ≤ gain - 1 by linarith) layer_count
  rwa [add_sub_cancel] at step

/-- **A stack of plates with a fixed turn dims the light exponentially.** -/
theorem plates_vanish
    {turn_angle : ℝ}
    (cos_nonneg : 0 ≤ Real.cos turn_angle)
    (layer_count : ℕ) :
    let pass_fraction := Real.cos turn_angle
    let signal_after_layers := pass_fraction ^ layer_count
    let decay_bound := Real.exp (-(layer_count * (1 - pass_fraction)))
    signal_after_layers ≤ decay_bound := by
  unfold_named_pieces
  exact gain_pow_le_exp cos_nonneg layer_count

end Gain

/-! ### Plates, forwards and backwards -/

section Plates

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
  {axis : Space}

/-- **A plate never lengthens the light.** -/
theorem norm_plate_le
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space) :
    let strength_after  := ‖PASS_THROUGH_PLATE axis light‖
    let strength_before := ‖light‖
    strength_after ≤ strength_before := by
  unfold_named_pieces
  have plate_strength :
      ‖PASS_THROUGH_PLATE axis light‖ = |inner ℝ axis light| :=
    norm_plate axis_has_length_one light
  rw [plate_strength]
  -- Cauchy-Schwarz: the overlap is at most the product of the lengths.
  calc |inner ℝ axis light| ≤ ‖axis‖ * ‖light‖ := abs_real_inner_le_norm _ _
    _ = ‖light‖ := by rw [axis_has_length_one, one_mul]

/-- **A plate acts the same way forwards and backwards.** -/
theorem inner_plate_comm
    (axis light other_light : Space) :
    let plate_on_left  := inner ℝ (PASS_THROUGH_PLATE axis light) other_light
    let plate_on_right := inner ℝ light (PASS_THROUGH_PLATE axis other_light)
    plate_on_left = plate_on_right := by
  unfold_named_pieces
  rw [PASS_THROUGH_PLATE, PASS_THROUGH_PLATE, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm axis light]
  ring

/-- **The gradient comes back through the same plates.** Reading the output of a
stack of plates along `other_light` is the same as reading the input along
`other_light` sent through the plates in the opposite order. -/
theorem inner_runPlates
    (axes : List Space)
    (light other_light : Space) :
    let forward_plates  := axes.map PASS_THROUGH_PLATE
    let backward_plates := axes.reverse.map PASS_THROUGH_PLATE
    let forward_reading :=
      inner ℝ (RUN_LAYERS forward_plates light) other_light
    let backward_reading :=
      inner ℝ light (RUN_LAYERS backward_plates other_light)
    forward_reading = backward_reading := by
  unfold_named_pieces
  induction axes generalizing light with
  | nil => rfl
  | cons first_axis later_axes ih =>
    -- Going back, the first plate is the last one the light meets.
    have backward_step :
        RUN_LAYERS ((first_axis :: later_axes).reverse.map PASS_THROUGH_PLATE)
            other_light
          = PASS_THROUGH_PLATE first_axis
              (RUN_LAYERS (later_axes.reverse.map PASS_THROUGH_PLATE)
                other_light) := by
      simp [RUN_LAYERS, runLayers_append]
    have forward_step :
        RUN_LAYERS ((first_axis :: later_axes).map PASS_THROUGH_PLATE) light
          = RUN_LAYERS (later_axes.map PASS_THROUGH_PLATE)
              (PASS_THROUGH_PLATE first_axis light) := by
      simp [RUN_LAYERS]
    rw [backward_step, forward_step, ih, inner_plate_comm]

/-- **Plates with a bypass blow up.** After `plate_count` of them on one axis the
light is at least `2 ^ plate_count` times as long as its first overlap with the
axis. -/
theorem le_norm_iterate_skipPlate
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space)
    (plate_count : ℕ) :
    let overlap_size := |inner ℝ axis light|
    let light_after  := (PASS_THROUGH_SKIP_PLATE axis)^[plate_count] light
    let growth_bound : ℝ := 2 ^ plate_count * overlap_size  -- each bypass plate doubles the overlap
    growth_bound ≤ ‖light_after‖ := by
  unfold_named_pieces
  have overlap_after :
      inner ℝ axis ((PASS_THROUGH_SKIP_PLATE axis)^[plate_count] light)
        = 2 ^ plate_count * inner ℝ axis light :=
    inner_iterate_skipPlate axis_has_length_one light plate_count
  -- The overlap with the axis is a lower bound for the length (Cauchy-Schwarz).
  calc 2 ^ plate_count * |inner ℝ axis light|
      = |inner ℝ axis ((PASS_THROUGH_SKIP_PLATE axis)^[plate_count] light)| := by
        rw [overlap_after, abs_mul,
          abs_of_nonneg (pow_nonneg (zero_le_two (α := ℝ)) plate_count)]
    _ ≤ ‖axis‖ * ‖(PASS_THROUGH_SKIP_PLATE axis)^[plate_count] light‖ :=
        abs_real_inner_le_norm _ _
    _ = ‖(PASS_THROUGH_SKIP_PLATE axis)^[plate_count] light‖ := by
        rw [axis_has_length_one, one_mul]

end Plates

end SquigglyLine
