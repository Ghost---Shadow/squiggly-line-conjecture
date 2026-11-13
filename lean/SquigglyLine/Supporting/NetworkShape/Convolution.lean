/-
Convolution, stride and upsampling.

* **Slope.** A convolution layer is no steeper than the summed sizes of its
  kernel weights, whatever the length of the signal.
* **Locality.** An output depends only on the inputs under the kernel. After
  `L` layers with a kernel of width `n`, it depends only on the inputs within
  `L * n` of it.
* **Stride.** Reading every second position is squeezing by two, in the sense
  of `Compression.lean`, so it doubles the slope. Upsampling is squeezing by
  one half, and undoes it.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `APPLY_CONVOLUTION`.

Theorems: `abs_convolution_sub_le`, `convolution_congr`,
`iterate_convolution_congr`, `stride_eq_compress`, `upsample_eq_compress`,
`compress_compress`, `stride_upsample`, `lipschitzWith_stride`.
-/
import SquigglyLine.Theorem.Compression

namespace SquigglyLine

open NNReal

/-- One convolution layer on a signal: each output is the kernel times the `n` inputs that
start at its position.
Python: `[sum(k[j] * x[i + j] for j in range(n)) for i in positions]`. -/
def APPLY_CONVOLUTION (n : ℕ) (k : ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun i => ∑ j ∈ Finset.range n, k j * x (i + j)

/-- **A convolution is no steeper than its summed kernel.** If two signals differ by at most
`d` everywhere, their outputs differ by at most `d` times the summed sizes of the kernel
weights. The length of the signal does not enter. -/
theorem abs_convolution_sub_le (n : ℕ) (k : ℕ → ℝ) {x y : ℕ → ℝ} {d : ℝ}
    (h : ∀ i, |x i - y i| ≤ d) (i : ℕ) :
    |APPLY_CONVOLUTION n k x i - APPLY_CONVOLUTION n k y i|
      ≤ (∑ j ∈ Finset.range n, |k j|) * d := by
  simp only [APPLY_CONVOLUTION]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  calc |∑ j ∈ Finset.range n, (k j * x (i + j) - k j * y (i + j))|
      ≤ ∑ j ∈ Finset.range n, |k j * x (i + j) - k j * y (i + j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, |k j| * d := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (h (i + j)) (abs_nonneg _)

/-- **A convolution is local.** An output depends only on the `n` inputs under the kernel. -/
theorem convolution_congr (n : ℕ) (k : ℕ → ℝ) {x y : ℕ → ℝ} {i : ℕ}
    (h : ∀ t, i ≤ t → t < i + n → x t = y t) :
    APPLY_CONVOLUTION n k x i = APPLY_CONVOLUTION n k y i := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h (i + j) (Nat.le_add_right i j) (Nat.add_lt_add_left (Finset.mem_range.mp hj) i)]

/-- **After `L` layers an output sees only the inputs within `L * n` of it.** Two signals that
agree on that window give the same output there, whatever they do elsewhere. -/
theorem iterate_convolution_congr (n : ℕ) (k : ℕ → ℝ) (L : ℕ) :
    ∀ {x y : ℕ → ℝ} {i : ℕ}, (∀ t, i ≤ t → t ≤ i + L * n → x t = y t) →
      (APPLY_CONVOLUTION n k)^[L] x i = (APPLY_CONVOLUTION n k)^[L] y i := by
  induction L with
  | zero =>
    intro x y i h
    exact h i le_rfl (by omega)
  | succ L ih =>
    intro x y i h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine convolution_congr n k fun t ht1 ht2 => ?_
    have hwindow : (L + 1) * n = L * n + n := by ring
    exact ih fun s hs1 hs2 => h s (by omega) (by omega)

variable {f : ℝ → ℝ}

/-- **Stride is squeezing.** Reading a signal at every second position is squeezing it
sideways by two. -/
theorem stride_eq_compress (f : ℝ → ℝ) : (fun t => f (2 * t)) = COMPRESS 2 f := by
  funext t
  simp [COMPRESS]

/-- Upsampling is squeezing by one half: a stretch. -/
theorem upsample_eq_compress (f : ℝ → ℝ) : (fun t => f (t / 2)) = COMPRESS (1 / 2) f := by
  funext t
  simp [COMPRESS, div_eq_inv_mul]

/-- Squeezing twice multiplies the factors. -/
theorem compress_compress (a b : ℝ) (f : ℝ → ℝ) :
    COMPRESS a (COMPRESS b f) = COMPRESS (b * a) f := by
  funext t
  simp [COMPRESS, mul_assoc]

/-- A stride of two after an upsampling by two gives the signal back. -/
theorem stride_upsample (f : ℝ → ℝ) : COMPRESS 2 (COMPRESS (1 / 2) f) = f := by
  rw [compress_compress]
  funext t
  simp [COMPRESS]

/-- **Each stride doubles the slope** of what the later layers see. -/
theorem lipschitzWith_stride {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith (2 * K) fun t => f (2 * t) := by
  rw [stride_eq_compress]
  have h := lipschitzWith_compress hf 2
  simpa using h

end SquigglyLine
