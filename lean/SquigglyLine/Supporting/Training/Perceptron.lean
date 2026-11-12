/-
The perceptron, XOR, and no free lunch: nearness to a boundary.

The theorem is about the distance from the data to a line. For a classifier
the line is its boundary, and the distance from the data to the boundary is
called the margin.

The margin is a nearest-point distance:
* `abs_inner_le_infDist_flatBoundary` : a point whose score against a unit
  direction is `s` is at least `|s|` from the flat boundary.

The perceptron (`perceptronWeights`), which adds each example it gets wrong:
* `mul_margin_le_inner` : each mistake moves the weights at least `γ` along
  the true direction.
* `norm_sq_perceptronWeights_le` : each mistake adds at most `R²` to the
  squared size of the weights.
* `perceptron_mistake_bound` : so there are at most `(R / γ)²` mistakes.

XOR (`SeparatesXor`):
* `not_separatesXor_flat` : no flat boundary splits it.
* `separatesXor_lift` : one lifted feature, the product, does.
* `separatesXor_fold` : so does one fold.

No free lunch:
* `card_agree_eq_card_disagree` : at an unseen input, any prediction is right
  on exactly half of all possible labellings.
* `mean_sq_error_unseen` : for labels `±1` with no pattern, a prediction `h`
  costs `h² + 1` on average, so the flat line at zero is best.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace SquigglyLine

/-! ### The margin is a nearest-point distance -/

section Margin

variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

/-- The flat boundary through the origin at right angles to `u`. -/
def flatBoundary (u : Θ) : Set Θ :=
  {v | inner ℝ u v = 0}

theorem abs_inner_le_dist_of_mem_flatBoundary {u : Θ} (hu : ‖u‖ ≤ 1) (x : Θ) {v : Θ}
    (hv : v ∈ flatBoundary u) : |inner ℝ u x| ≤ dist x v := by
  have hshift : inner ℝ u x = inner ℝ u (x - v) := by
    rw [inner_sub_right, show inner ℝ u v = 0 from hv, sub_zero]
  rw [hshift, dist_eq_norm]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu)

/-- **The margin is a distance to the boundary.** A point whose score against a direction of
length at most one is `s` lies at least `|s|` from the flat boundary. -/
theorem abs_inner_le_infDist_flatBoundary {u : Θ} (hu : ‖u‖ ≤ 1) (x : Θ) :
    |inner ℝ u x| ≤ Metric.infDist x (flatBoundary u) :=
  (Metric.le_infDist ⟨0, by simp [flatBoundary]⟩).2 fun _ hv =>
    abs_inner_le_dist_of_mem_flatBoundary hu x hv

end Margin

/-! ### The perceptron -/

section Perceptron

variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

/-- The perceptron's weights after `k` mistakes. `z i` is the `i`-th example it got wrong,
multiplied by its label `±1`. The rule is: on a mistake, add that to the weights. -/
def perceptronWeights (z : ℕ → Θ) (k : ℕ) : Θ :=
  ∑ i ∈ Finset.range k, z i

omit [InnerProductSpace ℝ Θ] in
theorem perceptronWeights_succ (z : ℕ → Θ) (k : ℕ) :
    perceptronWeights z (k + 1) = perceptronWeights z k + z k :=
  Finset.sum_range_succ _ _

variable {z : ℕ → Θ} {u : Θ} {γ R : ℝ} {n : ℕ}

/-- Each mistake moves the weights at least `γ` along the true direction `u`. -/
theorem mul_margin_le_inner (hmargin : ∀ k < n, γ ≤ inner ℝ u (z k)) :
    ∀ k ≤ n, k * γ ≤ inner ℝ u (perceptronWeights z k) := by
  intro k
  induction k with
  | zero => intro _; simp [perceptronWeights]
  | succ k ih =>
    intro hk
    have hprev := ih (Nat.le_of_succ_le hk)
    have hstep := hmargin k hk
    rw [perceptronWeights_succ, inner_add_right]
    push_cast
    linarith

/-- Each mistake adds at most `R²` to the squared size of the weights, because the example was
on the wrong side. -/
theorem norm_sq_perceptronWeights_le
    (hmistake : ∀ k < n, inner ℝ (perceptronWeights z k) (z k) ≤ 0)
    (hradius : ∀ k < n, ‖z k‖ ≤ R) :
    ∀ k ≤ n, ‖perceptronWeights z k‖ ^ 2 ≤ k * R ^ 2 := by
  intro k
  induction k with
  | zero => intro _; simp [perceptronWeights]
  | succ k ih =>
    intro hk
    have hprev := ih (Nat.le_of_succ_le hk)
    have hwrong := hmistake k hk
    have hsize : ‖z k‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hradius k hk) 2
    rw [perceptronWeights_succ, norm_add_sq_real]
    push_cast
    linarith

/-- **The perceptron makes at most `(R / γ)²` mistakes.** The examples lie within `R` of the
origin, and some direction `u` of length at most one scores every one of them at least `γ` on
its correct side. -/
theorem perceptron_mistake_bound (hu : ‖u‖ ≤ 1) (hγ : 0 < γ)
    (hmargin : ∀ k < n, γ ≤ inner ℝ u (z k))
    (hmistake : ∀ k < n, inner ℝ (perceptronWeights z k) (z k) ≤ 0)
    (hradius : ∀ k < n, ‖z k‖ ≤ R) : (n : ℝ) ≤ (R / γ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero]
    positivity
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlow := mul_margin_le_inner hmargin n le_rfl
  have hhigh := norm_sq_perceptronWeights_le hmistake hradius n le_rfl
  have hlength : inner ℝ u (perceptronWeights z n) ≤ ‖perceptronWeights z n‖ :=
    (real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu)
  have hsquare : (n * γ) ^ 2 ≤ n * R ^ 2 :=
    (pow_le_pow_left₀ (by positivity) (hlow.trans hlength) 2).trans hhigh
  rw [div_pow, le_div_iff₀ (by positivity)]
  refine le_of_mul_le_mul_left ?_ hpos
  rw [show (n : ℝ) * (n * γ ^ 2) = (n * γ) ^ 2 by ring]
  exact hsquare

end Perceptron

/-! ### XOR -/

section Xor

/-- A score splits XOR when it is negative at `(0, 0)` and `(1, 1)` and positive at `(0, 1)`
and `(1, 0)`. -/
def SeparatesXor (score : ℝ → ℝ → ℝ) : Prop :=
  score 0 0 < 0 ∧ score 1 1 < 0 ∧ 0 < score 0 1 ∧ 0 < score 1 0

/-- **No flat boundary splits XOR.** -/
theorem not_separatesXor_flat (a b c : ℝ) : ¬SeparatesXor fun x y => a * x + b * y + c := by
  intro h
  obtain ⟨h00, h11, h01, h10⟩ := h
  norm_num at h00 h11 h01 h10
  linarith

/-- **One lifted feature is enough.** With the product `x * y` as a third feature, the
boundary is flat. -/
theorem separatesXor_lift : SeparatesXor fun x y => x + y - 2 * (x * y) - 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **One fold is enough.** Fold the plane along the line `x = y`. -/
theorem separatesXor_fold : SeparatesXor fun x y => |x - y| - 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

end Xor

/-! ### No free lunch -/

section NoFreeLunch

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Change a labelling at the one input `x`. -/
def flipAt (x : X) (labels : X → Bool) : X → Bool :=
  Function.update labels x !labels x

omit [Fintype X] in
theorem flipAt_apply_self (x : X) (labels : X → Bool) : flipAt x labels x = !labels x := by
  simp [flipAt]

omit [Fintype X] in
theorem flipAt_flipAt (x : X) (labels : X → Bool) : flipAt x (flipAt x labels) = labels := by
  simp [flipAt]

/-- **No free lunch.** Fix an unseen input `x` and any guess for its label. Of all the ways to
label the inputs, exactly as many agree with the guess at `x` as disagree. -/
theorem card_agree_eq_card_disagree (x : X) (guess : Bool) :
    (Finset.univ.filter fun labels : X → Bool => labels x = guess).card
      = (Finset.univ.filter fun labels : X → Bool => labels x ≠ guess).card := by
  refine Finset.card_nbij' (flipAt x) (flipAt x) ?_ ?_ ?_ ?_
  · intro labels hlabels
    have hagree : labels x = guess := by simpa using hlabels
    simp [flipAt_apply_self, hagree]
  · intro labels hlabels
    have hdisagree : labels x ≠ guess := by simpa using hlabels
    cases hl : labels x <;> cases guess <;> simp_all [flipAt_apply_self]
  · intro labels _
    exact flipAt_flipAt x labels
  · intro labels _
    exact flipAt_flipAt x labels

/-- **With no pattern in the labels, flat is best.** If an unseen label is `+1` or `-1` with
equal chance, a prediction `h` has mean squared error `h² + 1`. Any move away from zero, in
either direction, only adds. -/
theorem mean_sq_error_unseen (h : ℝ) : ((h - 1) ^ 2 + (h + 1) ^ 2) / 2 = h ^ 2 + 1 := by
  ring

end NoFreeLunch

end SquigglyLine
