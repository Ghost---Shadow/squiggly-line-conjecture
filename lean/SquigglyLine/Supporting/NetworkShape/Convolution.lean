/-
Convolution, stride and upsampling.

* **Slope.** A convolution layer is no steeper than the summed sizes of its
  kernel weights, whatever the length of the signal.
* **Locality.** An output depends only on the inputs under the kernel. After
  `layer_count` layers with a kernel of width `kernel_width`, it depends only
  on the inputs within `layer_count * kernel_width` of it.
* **Stride.** Reading every second position is squeezing by two, in the sense
  of `Compression.lean`, so it doubles the slope. Upsampling is squeezing by
  one half, and undoes it.

| Name                  | Meaning                                           |
|-----------------------|---------------------------------------------------|
| `Signal`              | a signal: one number for each position            |
| `Kernel`              | the weights of a convolution: one for each offset |
| `APPLY_CONVOLUTION`   | one convolution layer on a signal                 |

Theorems: `abs_convolution_sub_le`, `convolution_congr`,
`iterate_convolution_congr`, `stride_eq_compress`, `upsample_eq_compress`,
`compress_compress`, `stride_upsample`, `lipschitzWith_stride`.
-/
import SquigglyLine.Theorem.Compression

namespace SquigglyLine

open NNReal

/-- A signal: one number for each position.
Python: `list[float]`, read as a function of the position. -/
abbrev Signal := ℕ → ℝ

/-- The weights of a convolution: one number for each offset under the
kernel.
Python: `list[float]`. -/
abbrev Kernel := ℕ → ℝ

/-- One convolution layer on a signal: each output is the kernel times the
`kernel_width` inputs that start at its position.
Python: `[sum(kernel[j] * signal[position + j] for j in range(kernel_width))
for position in positions]`. -/
def APPLY_CONVOLUTION
    (kernel_width : ℕ)
    (kernel : Kernel)
    (signal : Signal) : Signal :=
  fun position => ∑ j ∈ Finset.range kernel_width,
    kernel j * signal (position + j)

/-- **A convolution is no steeper than its summed kernel.** If two signals
differ by at most `max_gap` everywhere, their outputs differ by at most
`max_gap` times the summed sizes of the kernel weights. The length of the
signal does not enter. -/
theorem abs_convolution_sub_le
    (kernel_width : ℕ)
    (kernel : Kernel)
    {signal : Signal}
    {other_signal : Signal}
    {max_gap : ℝ}
    (signals_are_close :
      ∀ position, |signal position - other_signal position| ≤ max_gap)
    (position : ℕ) :
    let output_gap  :=
      |APPLY_CONVOLUTION kernel_width kernel signal position
        - APPLY_CONVOLUTION kernel_width kernel other_signal position|
    let kernel_size := ∑ j ∈ Finset.range kernel_width, |kernel j|
    let gap_limit   := kernel_size * max_gap
    output_gap ≤ gap_limit := by
  unfold_named_pieces
  simp only [APPLY_CONVOLUTION]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  calc |∑ j ∈ Finset.range kernel_width,
        (kernel j * signal (position + j)
          - kernel j * other_signal (position + j))|
      ≤ ∑ j ∈ Finset.range kernel_width,
          |kernel j * signal (position + j)
            - kernel j * other_signal (position + j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range kernel_width, |kernel j| * max_gap := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (signals_are_close (position + j)) (abs_nonneg _)

/-- **A convolution is local.** An output depends only on the `kernel_width`
inputs under the kernel. -/
theorem convolution_congr
    (kernel_width : ℕ)
    (kernel : Kernel)
    {signal : Signal}
    {other_signal : Signal}
    {position : ℕ}
    (signals_agree : ∀ index, position ≤ index →
      index < position + kernel_width → signal index = other_signal index) :
    let output       :=
      APPLY_CONVOLUTION kernel_width kernel signal position
    let other_output :=
      APPLY_CONVOLUTION kernel_width kernel other_signal position
    output = other_output := by
  unfold_named_pieces
  refine Finset.sum_congr rfl fun j j_in_range => ?_
  rw [signals_agree (position + j) (Nat.le_add_right position j)
    (Nat.add_lt_add_left (Finset.mem_range.mp j_in_range) position)]

/-- **After `layer_count` layers an output sees only the inputs within
`layer_count * kernel_width` of it.** Two signals that agree on that window
give the same output there, whatever they do elsewhere. -/
theorem iterate_convolution_congr
    (kernel_width : ℕ)
    (kernel : Kernel)
    (layer_count : ℕ) :
    let window_size := layer_count * kernel_width  -- each layer reaches `kernel_width` further
    ∀ {signal : Signal} {other_signal : Signal} {position : ℕ},
      let signals_agree := ∀ index, position ≤ index →
        index ≤ position + window_size → signal index = other_signal index
      let output       :=
        (APPLY_CONVOLUTION kernel_width kernel)^[layer_count] signal position
      let other_output :=
        (APPLY_CONVOLUTION kernel_width kernel)^[layer_count] other_signal
          position
      signals_agree → output = other_output := by
  unfold_named_pieces
  induction layer_count with
  | zero =>
    intro signal other_signal position signals_agree
    exact signals_agree position le_rfl (by omega)
  | succ layer_count earlier_layers_congr =>
    intro signal other_signal position signals_agree
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine convolution_congr kernel_width kernel
      fun index index_ge index_lt => ?_
    -- The window of one more layer is the earlier window plus the kernel.
    have window_split :
        (layer_count + 1) * kernel_width
          = layer_count * kernel_width + kernel_width := by
      ring
    exact earlier_layers_congr fun other_index other_ge other_le =>
      signals_agree other_index (by omega) (by omega)

variable {model : RealFunction}

/-- **Stride is squeezing.** Reading a signal at every second position is
squeezing it sideways by two. -/
theorem stride_eq_compress
    (model : RealFunction) :
    let strided_model : RealFunction := fun input => model (2 * input)  -- every second position
    let squeezed_model := COMPRESS 2 model
    strided_model = squeezed_model := by
  unfold_named_pieces
  funext input
  simp [COMPRESS]

/-- Upsampling is squeezing by one half: a stretch. -/
theorem upsample_eq_compress
    (model : RealFunction) :
    let upsampled_model : RealFunction := fun input => model (input / 2)  -- each position read twice
    let squeezed_model := COMPRESS (1 / 2) model
    upsampled_model = squeezed_model := by
  unfold_named_pieces
  funext input
  simp [COMPRESS, div_eq_inv_mul]

/-- Squeezing twice multiplies the factors. -/
theorem compress_compress
    (outer_factor : ℝ)
    (inner_factor : ℝ)
    (model : RealFunction) :
    let squeezed_twice := COMPRESS outer_factor (COMPRESS inner_factor model)
    let squeezed_once  := COMPRESS (inner_factor * outer_factor) model
    squeezed_twice = squeezed_once := by
  unfold_named_pieces
  funext input
  simp [COMPRESS, mul_assoc]

/-- A stride of two after an upsampling by two gives the signal back. -/
theorem stride_upsample
    (model : RealFunction) :
    let upsampled_model := COMPRESS (1 / 2) model
    let restored_model  := COMPRESS 2 upsampled_model
    restored_model = model := by
  unfold_named_pieces
  -- The two factors multiply to one.
  have squeezed_twice :
      COMPRESS 2 (COMPRESS (1 / 2) model) = COMPRESS (1 / 2 * 2) model :=
    compress_compress 2 (1 / 2) model
  rw [squeezed_twice]
  funext input
  simp [COMPRESS]

/-- **Each stride doubles the slope** of what the later layers see. -/
theorem lipschitzWith_stride
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model) :
    let strided_slope_limit := 2 * slope_limit  -- the same climb over half the run
    let strided_model : RealFunction := fun input => model (2 * input)
    LipschitzWith strided_slope_limit strided_model := by
  unfold_named_pieces
  have as_compress :
      (fun input => model (2 * input)) = COMPRESS 2 model :=
    stride_eq_compress model
  rw [as_compress]
  have compressed_bound := lipschitzWith_compress slope_is_bounded 2
  simpa using compressed_bound

end SquigglyLine
