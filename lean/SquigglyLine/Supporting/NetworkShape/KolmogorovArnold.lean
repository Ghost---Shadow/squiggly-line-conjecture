/-
Kolmogorov–Arnold networks: a learnable curve on an edge is a few folds.

A node of a Kolmogorov–Arnold network adds up one learnable curve per input:
`node(x) = Σ φ i (x i)`. `UniversalApproximation.lean` says a curve of slope
at most `K` on `[0, 1]` is within `2 K / n` of a ReLU network with `n`
pieces. Do that on every edge and the node is within `2 (Σ K i) / n` of a
plain ReLU layer. So the number of folds a node needs goes as the total
slope of its curves over the error allowed.

Theorems: `abs_kanNode_sub_le`, `exists_pieces_kanNode_close`.
-/
import SquigglyLine.Supporting.NetworkShape.UniversalApproximation

namespace SquigglyLine

variable {ι : Type*} [Fintype ι]

/-- **An edge curve is a few folds.** Replace every edge curve of a node by its ReLU network
with `n` pieces. On the unit cube the node changes by at most `2 (Σ K i) / n`. -/
theorem abs_kanNode_sub_le {φ : ι → ℝ → ℝ} {K : ι → ℝ}
    (hφ : ∀ i x y, |φ i x - φ i y| ≤ K i * |x - y|) {n : ℕ} (hn : (0 : ℝ) < n)
    {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    |∑ i, INTERPOLATE_WITH_RELU (φ i) n n (x i) - ∑ i, φ i (x i)|
      ≤ 2 * (∑ i, K i) / n := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, (INTERPOLATE_WITH_RELU (φ i) n n (x i) - φ i (x i))|
      ≤ ∑ i, |INTERPOLATE_WITH_RELU (φ i) n n (x i) - φ i (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * K i / n :=
        Finset.sum_le_sum fun i _ => relu_network_close (hφ i) hn (hx0 i) (hx1 i)
    _ = 2 * (∑ i, K i) / n := by
        simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]

/-- **Folds needed go as total slope over error.** For any tolerance there is a number of
pieces, the same on every edge, that brings the ReLU version of the node within the tolerance
everywhere on the unit cube. -/
theorem exists_pieces_kanNode_close {φ : ι → ℝ → ℝ} {K : ι → ℝ}
    (hφ : ∀ i x y, |φ i x - φ i y| ≤ K i * |x - y|) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → (∀ i, x i ≤ 1) →
      |∑ i, INTERPOLATE_WITH_RELU (φ i) n n (x i) - ∑ i, φ i (x i)| ≤ ε := by
  have hK : 0 ≤ ∑ i, K i := Finset.sum_nonneg fun i _ => slope_nonneg (hφ i)
  -- Enough pieces: one more than `2 (Σ K i) / ε`.
  refine ⟨⌈2 * (∑ i, K i) / ε⌉₊ + 1, fun x hx0 hx1 => ?_⟩
  have hn : (0 : ℝ) < ((⌈2 * (∑ i, K i) / ε⌉₊ + 1 : ℕ) : ℝ) := by positivity
  refine (abs_kanNode_sub_le hφ hn hx0 hx1).trans ?_
  rw [div_le_iff₀ hn]
  have hceil : 2 * (∑ i, K i) / ε ≤ ((⌈2 * (∑ i, K i) / ε⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  calc 2 * (∑ i, K i) = 2 * (∑ i, K i) / ε * ε := by field_simp
    _ ≤ ((⌈2 * (∑ i, K i) / ε⌉₊ + 1 : ℕ) : ℝ) * ε := mul_le_mul_of_nonneg_right hceil hε.le
    _ = ε * ((⌈2 * (∑ i, K i) / ε⌉₊ + 1 : ℕ) : ℝ) := mul_comm _ _

end SquigglyLine
