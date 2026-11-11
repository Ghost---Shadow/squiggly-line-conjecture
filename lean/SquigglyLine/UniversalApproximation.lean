/-
Universal approximation, and what it costs.

Cut the interval `[0, 1]` into `n` pieces. A `ramp` is flat, then rises across
one piece, then is flat again: two ReLU units. `reluInterp f n k` is the
network made of the first `k` ramps, each scaled to follow `f` across its
piece. It has one hidden layer of `2 k` units.

* `ramp_of_le`, `ramp_of_mem`, `ramp_of_ge` : the three stretches of a ramp.
* `reluInterp_spec` : after `k` ramps the network is within `2 K / n` of `f`
  on the first `k` pieces, and sits exactly on `f (k / n)` beyond them.
* `relu_network_close` : so `2 n` units are within `2 K / n` of `f` on the
  whole interval.
* `universal_approximation` : for any `ε > 0` there is such a network within
  `ε` of `f`.
-/
import SquigglyLine.DepthSeparation

namespace SquigglyLine

/-! ### One ramp: two ReLU units -/

section Ramp

/-- A ramp across the `k`-th of `n` pieces: flat at zero, rising with slope one, then flat
at `1 / n`. It is the difference of two ReLU units. -/
noncomputable def ramp (n k : ℕ) (x : ℝ) : ℝ :=
  max (x - k / n) 0 - max (x - (k + 1) / n) 0

variable {n k : ℕ} {x : ℝ}

/-- Before its piece, a ramp is zero. -/
theorem ramp_of_le (hn : (0 : ℝ) < n) (hx : x ≤ k / n) : ramp n k x = 0 := by
  have h1n : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn
  rw [ramp, add_div, max_eq_right (by linarith), max_eq_right (by linarith), sub_self]

/-- Inside its piece, a ramp rises with slope one. -/
theorem ramp_of_mem (h1 : (k : ℝ) / n ≤ x) (h2 : x ≤ (k + 1) / n) :
    ramp n k x = x - k / n := by
  rw [ramp, max_eq_left (by linarith), max_eq_right (by linarith), sub_zero]

/-- After its piece, a ramp stays at its full height. -/
theorem ramp_of_ge (hn : (0 : ℝ) < n) (hx : ((k : ℝ) + 1) / n ≤ x) : ramp n k x = 1 / n := by
  have h1n : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn
  rw [add_div] at hx
  rw [ramp, add_div, max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

end Ramp

/-! ### The network that follows `f` -/

section Network

/-- The network made of the first `k` ramps, each scaled to follow `f` across its piece. -/
noncomputable def reluInterp (f : ℝ → ℝ) (n k : ℕ) (x : ℝ) : ℝ :=
  f 0 + ∑ i ∈ Finset.range k, n * (f (((i : ℝ) + 1) / n) - f ((i : ℝ) / n)) * ramp n i x

variable {f : ℝ → ℝ} {K : ℝ} {n : ℕ}

/-- A slope bound is never negative. -/
theorem slope_nonneg (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) : 0 ≤ K := by
  have h01 := hf 0 1
  rw [zero_sub, abs_neg, abs_one, mul_one] at h01
  exact (abs_nonneg _).trans h01

/-- Adding one more ramp. -/
theorem reluInterp_succ (f : ℝ → ℝ) (n k : ℕ) (x : ℝ) :
    reluInterp f n (k + 1) x
      = reluInterp f n k x + n * (f (((k : ℝ) + 1) / n) - f ((k : ℝ) / n)) * ramp n k x := by
  rw [reluInterp, Finset.sum_range_succ, reluInterp, add_assoc]

/-- **Piece by piece.** After `k` ramps the network is within `2 K / n` of `f` on the first
`k` pieces, and sits exactly on `f (k / n)` beyond them. -/
theorem reluInterp_spec (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) (hn : (0 : ℝ) < n) (k : ℕ) :
    (∀ x : ℝ, 0 ≤ x → x ≤ k / n → |reluInterp f n k x - f x| ≤ 2 * K / n)
      ∧ ∀ x, (k : ℝ) / n ≤ x → reluInterp f n k x = f (k / n) := by
  have hK := slope_nonneg hf
  have h1n : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn
  induction k with
  | zero =>
    constructor
    · intro x h0 hx
      have hx0 : x = 0 := le_antisymm (by simpa using hx) h0
      subst hx0
      rw [show reluInterp f n 0 0 - f 0 = 0 by simp [reluInterp], abs_zero]
      exact div_nonneg (by linarith) hn.le
    · intro x _
      simp [reluInterp]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · intro x h0 hx
      rw [Nat.cast_succ] at hx
      rcases le_total x (k / n) with hle | hge
      · rw [reluInterp_succ, ramp_of_le hn hle, mul_zero, add_zero]
        exact ih1 x h0 hle
      · have hd0 : 0 ≤ x - k / n := by linarith
        have hd1 : x - k / n ≤ 1 / n := by
          rw [add_div] at hx
          linarith
        have hA : |f (k / n) - f x| ≤ K * (1 / n) :=
          calc |f (k / n) - f x| ≤ K * |(k : ℝ) / n - x| := hf _ _
            _ = K * (x - k / n) := by rw [abs_sub_comm, abs_of_nonneg hd0]
            _ ≤ K * (1 / n) := mul_le_mul_of_nonneg_left hd1 hK
        have hF : |f (((k : ℝ) + 1) / n) - f (k / n)| ≤ K * (1 / n) :=
          calc |f (((k : ℝ) + 1) / n) - f (k / n)|
              ≤ K * |((k : ℝ) + 1) / n - k / n| := hf _ _
            _ = K * (1 / n) := by rw [add_div, add_sub_cancel_left, abs_of_pos h1n]
        have hB : |n * (f (((k : ℝ) + 1) / n) - f (k / n)) * (x - k / n)| ≤ K * (1 / n) := by
          rw [abs_mul, abs_mul, abs_of_pos hn, abs_of_nonneg hd0]
          calc n * |f (((k : ℝ) + 1) / n) - f (k / n)| * (x - k / n)
              ≤ n * (K * (1 / n)) * (1 / n) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hF hn.le) hd1 hd0
                  (mul_nonneg hn.le (mul_nonneg hK h1n.le))
            _ = K * (1 / n) := by
                field_simp
        rw [reluInterp_succ, ih2 x hge, ramp_of_mem hge hx]
        calc |f (k / n) + n * (f (((k : ℝ) + 1) / n) - f (k / n)) * (x - k / n) - f x|
            = |(f (k / n) - f x) + n * (f (((k : ℝ) + 1) / n) - f (k / n)) * (x - k / n)| := by
              congr 1
              ring
          _ ≤ |f (k / n) - f x| + |n * (f (((k : ℝ) + 1) / n) - f (k / n)) * (x - k / n)| :=
              abs_add_le _ _
          _ ≤ K * (1 / n) + K * (1 / n) := add_le_add hA hB
          _ = 2 * K / n := by ring
    · intro x hx
      rw [Nat.cast_succ] at hx ⊢
      have hprev : (k : ℝ) / n ≤ x := by
        rw [add_div] at hx
        linarith
      rw [reluInterp_succ, ih2 x hprev, ramp_of_ge hn hx]
      field_simp
      ring

/-- **A network of `2 n` units is within `2 K / n` of `f`.** -/
theorem relu_network_close (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) (hn : (0 : ℝ) < n) {x : ℝ}
    (h0 : 0 ≤ x) (h1 : x ≤ 1) : |reluInterp f n n x - f x| ≤ 2 * K / n :=
  (reluInterp_spec hf hn n).1 x h0 (by rwa [div_self hn.ne'])

/-- **Universal approximation.** A function on `[0, 1]` with slope at most `K` is within any
`ε > 0` of a ReLU network with one hidden layer. -/
theorem universal_approximation (hf : ∀ x y, |f x - f y| ≤ K * |x - y|) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |reluInterp f n n x - f x| ≤ ε := by
  have hK := slope_nonneg hf
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K / ε)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (by linarith) hε.le) hn
  refine ⟨n, fun x hx => ?_⟩
  calc |reluInterp f n n x - f x| ≤ 2 * K / n := relu_network_close hf hnpos hx.1 hx.2
    _ ≤ ε := by
        rw [div_lt_iff₀ hε] at hn
        rw [div_le_iff₀ hnpos]
        linarith

end Network

end SquigglyLine
