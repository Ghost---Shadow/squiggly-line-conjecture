/-
Mixing: five more things that are averages, and one that is not.

* **Graph networks.** A message-passing layer replaces each node by an average
  over nodes. If every weight is at least `m`, a layer shrinks the spread of
  the nodes by `1 - n m`, and `L` layers by that to the power `L`.
* **The diffusion noising schedule.** Each step keeps the share `1 - β` of the
  signal and of the old noise and adds `β` of fresh noise. Signal plus noise
  stays one, and the signal's share is the product of the `1 - β t`.
* **Data augmentation.** Averaging a model over a group of moves that keep
  distances gives a model that ignores those moves and is no steeper.
* **The baseline.** Subtracting a baseline from the reward does not change the
  average push on the scores of a softmax policy.
* **Classifier-free guidance is not an average.** Its weights are `1 + w` and
  `-w`. It moves `1 + w` times as far as the plain step, and for `w > 0` it
  leaves the stretch between the two predictions.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `APPLY_MESSAGE_PASSING`, `TAKE_NOISING_STEP`,
`AVERAGE_OVER_MOVES`, `APPLY_GUIDANCE`.

Theorems: `abs_messagePassing_sub_le`, `abs_iterate_messagePassing_sub_le`,
`noisingStep_sum`, `iterate_noisingStep_signal`, `averageOverMoves_smul`,
`lipschitzWith_averageOverMoves`, `sum_mul_baseline_eq_zero`,
`sum_mul_sub_baseline`, `guidance_sub`, `norm_guidance_sub`,
`guidance_notMem_segment`.
-/
import Mathlib.Analysis.Convex.Segment
import SquigglyLine.Supporting.NetworkShape.AttentionRate

namespace SquigglyLine

open Real NNReal

variable {ι : Type*} [Fintype ι]

/-- One layer of message passing: each node becomes a weighted sum of the nodes, with the
weights `P i j` that node `i` gives to node `j`.
Python: `[sum(P[i][j] * v[j] for j in nodes) for i in nodes]`. -/
def APPLY_MESSAGE_PASSING (P : ι → ι → ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j, P i j * v j

/-- **A message-passing layer shrinks the spread.** If every row of weights adds to one and
every weight is at least `m`, two nodes end no further apart than `1 - n m` times the range of
the values. -/
theorem abs_messagePassing_sub_le {P : ι → ι → ℝ} {m lo hi : ℝ} (hP : ∀ i j, m ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1) {v : ι → ℝ} (hlo : ∀ j, lo ≤ v j) (hhi : ∀ j, v j ≤ hi)
    (i k : ι) :
    |APPLY_MESSAGE_PASSING P v i - APPLY_MESSAGE_PASSING P v k|
      ≤ (1 - Fintype.card ι * m) * (hi - lo) := by
  have h : |∑ j, P i j * v j - ∑ j, P k j * v j| ≤ (1 - Fintype.card ι * m) * (hi - lo) :=
    abs_sum_mul_sub_sum_mul_le (hP i) (hP k) (hrow i) (hrow k) hlo hhi
  exact h

/-- **Depth blurs the nodes.** After `L` layers any two nodes differ by at most
`(1 - n m) ^ L` times the range they started in. -/
theorem abs_iterate_messagePassing_sub_le [Nonempty ι] {P : ι → ι → ℝ} {m lo hi : ℝ}
    (hm : 0 ≤ 1 - Fintype.card ι * m) (hP : ∀ i j, m ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    {v : ι → ℝ} (hlo : ∀ j, lo ≤ v j) (hhi : ∀ j, v j ≤ hi) (L : ℕ) (i k : ι) :
    |(APPLY_MESSAGE_PASSING P)^[L] v i - (APPLY_MESSAGE_PASSING P)^[L] v k|
      ≤ (1 - Fintype.card ι * m) ^ L * (hi - lo) := by
  have key : ∀ L : ℕ, ∃ lo' hi' : ℝ,
      (∀ j, lo' ≤ (APPLY_MESSAGE_PASSING P)^[L] v j) ∧
      (∀ j, (APPLY_MESSAGE_PASSING P)^[L] v j ≤ hi') ∧
      hi' - lo' ≤ (1 - Fintype.card ι * m) ^ L * (hi - lo) := by
    intro L
    induction L with
    | zero => exact ⟨lo, hi, hlo, hhi, by simp⟩
    | succ L ih =>
      obtain ⟨lo', hi', hlo', hhi', hwidth⟩ := ih
      set x := (APPLY_MESSAGE_PASSING P)^[L] v with hx
      obtain ⟨imin, -, hmin⟩ := Finset.exists_min_image Finset.univ
        (fun j => APPLY_MESSAGE_PASSING P x j) Finset.univ_nonempty
      obtain ⟨imax, -, hmax⟩ := Finset.exists_max_image Finset.univ
        (fun j => APPLY_MESSAGE_PASSING P x j) Finset.univ_nonempty
      refine ⟨APPLY_MESSAGE_PASSING P x imin, APPLY_MESSAGE_PASSING P x imax, ?_, ?_, ?_⟩
      · intro j; rw [Function.iterate_succ_apply']; exact hmin j (Finset.mem_univ j)
      · intro j; rw [Function.iterate_succ_apply']; exact hmax j (Finset.mem_univ j)
      · have hgap := abs_messagePassing_sub_le hP hrow hlo' hhi' imax imin
        calc APPLY_MESSAGE_PASSING P x imax - APPLY_MESSAGE_PASSING P x imin
            ≤ (1 - Fintype.card ι * m) * (hi' - lo') := (le_abs_self _).trans hgap
          _ ≤ (1 - Fintype.card ι * m) * ((1 - Fintype.card ι * m) ^ L * (hi - lo)) :=
              mul_le_mul_of_nonneg_left hwidth hm
          _ = (1 - Fintype.card ι * m) ^ (L + 1) * (hi - lo) := by ring
  obtain ⟨lo', hi', hlo', hhi', hwidth⟩ := key L
  rw [abs_le]
  constructor <;> linarith [hlo' i, hhi' i, hlo' k, hhi' k]

/-- One noising step, on the pair (share of signal, share of noise) of the variance: keep
`1 - β` of each and add `β` of fresh noise.
Python: `((1 - β) * signal, (1 - β) * noise + β)`. -/
def TAKE_NOISING_STEP (β : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - β) * s.1, (1 - β) * s.2 + β)

/-- **The schedule keeps the total variance at one.** -/
theorem noisingStep_sum (β : ℝ) {s : ℝ × ℝ} (h : s.1 + s.2 = 1) :
    (TAKE_NOISING_STEP β s).1 + (TAKE_NOISING_STEP β s).2 = 1 := by
  simp only [TAKE_NOISING_STEP]
  linear_combination (1 - β) * h

/-- **The signal's share is the product of the factors `1 - β`.** With the same `β` at every
step it is `(1 - β) ^ n` of what it was. -/
theorem iterate_noisingStep_signal (β : ℝ) (s : ℝ × ℝ) (n : ℕ) :
    ((TAKE_NOISING_STEP β)^[n] s).1 = (1 - β) ^ n * s.1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [TAKE_NOISING_STEP]
    rw [ih]
    ring

variable {G E : Type*} [Group G] [Fintype G] [MulAction G E]

/-- A model averaged over a group of moves of the input.
Python: `mean(f(move(x)) for move in moves)`. -/
noncomputable def AVERAGE_OVER_MOVES (G : Type*) [Group G] [Fintype G] [MulAction G E]
    (f : E → ℝ) (x : E) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f (g • x)

/-- **The averaged model ignores the moves.** -/
theorem averageOverMoves_smul (f : E → ℝ) (h : G) (x : E) :
    AVERAGE_OVER_MOVES G f (h • x) = AVERAGE_OVER_MOVES G f x := by
  simp only [AVERAGE_OVER_MOVES, smul_smul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => rfl

/-- **And it is no steeper**, when the moves keep distances. -/
theorem lipschitzWith_averageOverMoves [PseudoMetricSpace E] {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hmove : ∀ (g : G) (x y : E), dist (g • x) (g • y) ≤ dist x y) :
    LipschitzWith K (AVERAGE_OVER_MOVES G f) := by
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hterm : ∀ g : G, |f (g • x) - f (g • y)| ≤ K * dist x y := fun g => by
    have h := hf.dist_le_mul (g • x) (g • y)
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hmove g x y) K.coe_nonneg)
  rw [Real.dist_eq, AVERAGE_OVER_MOVES, AVERAGE_OVER_MOVES, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul, abs_of_pos (inv_pos.mpr hcard)]
  calc (Fintype.card G : ℝ)⁻¹ * |∑ g : G, (f (g • x) - f (g • y))|
      ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, |f (g • x) - f (g • y)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.mpr hcard).le
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _g : G, (K * dist x y) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hterm g)
          (inv_pos.mpr hcard).le
    _ = K * dist x y := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hcard.ne', one_mul]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **A baseline pushes nothing on average.** For a policy over actions, the push on the
score of action `j` from "action taken minus prediction", averaged over the action taken, is
zero. -/
theorem sum_mul_baseline_eq_zero {policy : α → ℝ} (hpolicy : ∑ a, policy a = 1) (j : α) :
    ∑ a, policy a * ((if a = j then 1 else 0) - policy j) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul, hpolicy, one_mul, sub_self]

/-- So subtracting a baseline `b` from every reward leaves the average push as it was. -/
theorem sum_mul_sub_baseline {policy : α → ℝ} (hpolicy : ∑ a, policy a = 1) (R : α → ℝ) (b : ℝ) (j : α) :
    ∑ a, policy a * (R a - b) * ((if a = j then 1 else 0) - policy j)
      = ∑ a, policy a * R a * ((if a = j then 1 else 0) - policy j) := by
  have h := sum_mul_baseline_eq_zero hpolicy j
  have hsplit : ∀ a, policy a * (R a - b) * ((if a = j then 1 else 0) - policy j)
      = policy a * R a * ((if a = j then 1 else 0) - policy j)
        - b * (policy a * ((if a = j then 1 else 0) - policy j)) := fun a => by ring
  simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, h, mul_zero, sub_zero]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Classifier-free guidance with strength `w`: `1 + w` of the prediction with the prompt,
minus `w` of the prediction without it.
Python: `(1 + w) * with_prompt - w * without_prompt`. -/
def APPLY_GUIDANCE (w : ℝ) (without_prompt with_prompt : V) : V :=
  (1 + w) • with_prompt - w • without_prompt

/-- Guidance moves from the plain prediction in the direction of the prompt, `1 + w` times as
far as the prompt alone does. -/
theorem guidance_sub (w : ℝ) (u c : V) :
    APPLY_GUIDANCE w u c - u = (1 + w) • (c - u) := by
  rw [APPLY_GUIDANCE]
  module

theorem norm_guidance_sub {w : ℝ} (hw : 0 ≤ 1 + w) (u c : V) :
    ‖APPLY_GUIDANCE w u c - u‖ = (1 + w) * ‖c - u‖ := by
  rw [guidance_sub, norm_smul, Real.norm_of_nonneg hw]

/-- **Guidance is not an average.** For `w > 0` the guided prediction is not on the stretch
between the two predictions it is made from. -/
theorem guidance_notMem_segment {w : ℝ} (hw : 0 < w) {u c : V} (huc : c ≠ u) :
    APPLY_GUIDANCE w u c ∉ segment ℝ u c := by
  rintro ⟨a, b, ha0, -, hab, hz⟩
  -- On the stretch the point is `u + b • (c - u)` with `b ≤ 1`; guidance has `1 + w` there.
  have h1 : (1 + w - b) • (c - u) = 0 := by
    have ha : a = 1 - b := by linarith
    have h2 : APPLY_GUIDANCE w u c - u = b • (c - u) := by
      rw [← hz, ha]
      module
    rw [guidance_sub] at h2
    rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h1 with h | h
  · have hb : b ≤ 1 := by linarith
    linarith
  · exact huc (sub_eq_zero.mp h)

end SquigglyLine
