/-
Compression: folds, code length and travel.

Counting:
* `card_le_two_pow_of_code` : `b` binary digits name at most `2 ^ b` things.
* `tent_one_sub`, `eq_or_eq_one_sub_of_tent_eq` : a fold merges an input with
  its mirror image and with nothing else. It throws away one bit.
* `card_le_two_pow_of_iterate_tent_eq` : `L` folds send at most `2 ^ L` inputs
  to the same output.

Loss:
* `gibbs` : the average log-loss of any model is at least the entropy of the
  data.
* `expected_length_ge_entropy` : so is the average length of any code whose
  lengths satisfy Kraft's inequality.

Distance (description length taken as squared distance over `2 σ²`):
* `descriptionLength_gradientDescent_le` : gradient descent reaches the fit
  that is cheapest to describe.
* `travel_sq_div_eq_of_tight` : with orthogonal features of strength `c` that
  cost is the squared error at the start over `2 σ² c`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import SquigglyLine.Networks.Bridge
import SquigglyLine.Supporting.Training.LeastAction

namespace SquigglyLine

/-! ### Counting: bits and folds -/

section Counting

/-- **`b` binary digits name at most `2 ^ b` things.** -/
theorem card_le_two_pow_of_code {α : Type*} (S : Finset α) {b : ℕ} (code : α → Fin b → Bool)
    (hinj : Set.InjOn code S) : S.card ≤ 2 ^ b := by
  classical
  calc S.card = (S.image code).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin b → Bool) := Finset.card_le_univ _
    _ = 2 ^ b := by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **A fold merges an input with its mirror image.** -/
theorem tent_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : APPLY_TENT (1 - x) = APPLY_TENT x := by
  rcases le_total x (1 / 2) with h | h
  · rw [tent_of_le_half h0 h, tent_of_half_le (by linarith)]
    ring
  · rw [tent_of_half_le h, tent_of_le_half (by linarith) (by linarith)]
    ring

/-- **And with nothing else.** Two inputs with the same output are equal or are mirror
images. -/
theorem eq_or_eq_one_sub_of_tent_eq {x x' : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hx' : x' ∈ Set.Icc (0 : ℝ) 1) (h : APPLY_TENT x' = APPLY_TENT x) : x' = x ∨ x' = 1 - x := by
  rcases le_total x (1 / 2) with hl | hr <;> rcases le_total x' (1 / 2) with hl' | hr'
  · rw [tent_of_le_half hx'.1 hl', tent_of_le_half hx.1 hl] at h
    exact Or.inl (by linarith)
  · rw [tent_of_half_le hr', tent_of_le_half hx.1 hl] at h
    exact Or.inr (by linarith)
  · rw [tent_of_le_half hx'.1 hl', tent_of_half_le hr] at h
    exact Or.inr (by linarith)
  · rw [tent_of_half_le hr', tent_of_half_le hr] at h
    exact Or.inl (by linarith)

/-- **`L` folds throw away at most `L` bits.** At most `2 ^ L` inputs are sent to the same
output. -/
theorem card_le_two_pow_of_iterate_tent_eq (L : ℕ) (S : Finset ℝ)
    (hS : ∀ x ∈ S, x ∈ Set.Icc (0 : ℝ) 1) (c : ℝ) (hconst : ∀ x ∈ S, APPLY_TENT^[L] x = c) :
    S.card ≤ 2 ^ L := by
  classical
  induction L generalizing S c with
  | zero =>
    rw [pow_zero, Finset.card_le_one]
    intro a ha b hb
    have h1 : a = c := by simpa using hconst a ha
    have h2 : b = c := by simpa using hconst b hb
    rw [h1, h2]
  | succ L ih =>
    have himage : (S.image APPLY_TENT).card ≤ 2 ^ L := by
      refine ih (S.image APPLY_TENT) (fun y hy => ?_) c (fun y hy => ?_)
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact tent_mem_Icc (hS x hx).1 (hS x hx).2
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        rw [← Function.iterate_succ_apply]
        exact hconst x hx
    have hfiber : ∀ a ∈ S.image APPLY_TENT, (S.filter fun x => APPLY_TENT x = a).card ≤ 2 := by
      intro a ha
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp ha
      have hsub : (S.filter fun x => APPLY_TENT x = APPLY_TENT x₀) ⊆ {x₀, 1 - x₀} := by
        intro x hx
        obtain ⟨hxS, hxa⟩ := Finset.mem_filter.mp hx
        rcases eq_or_eq_one_sub_of_tent_eq (hS x₀ hx₀) (hS x hxS) hxa with h | h
        · rw [h]
          exact Finset.mem_insert_self _ _
        · rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    calc S.card ≤ 2 * (S.image APPLY_TENT).card := Finset.card_le_mul_card_image S 2 hfiber
      _ ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 himage
      _ = 2 ^ (L + 1) := by rw [pow_succ, mul_comm]

end Counting

/-! ### Loss: the entropy limit -/

section Entropy

variable {ι : Type*} [Fintype ι]

/-- **No model beats the entropy.** If the data has probabilities `p` and the model gives
probabilities `q`, the average log-loss is at least the entropy of the data. -/
theorem gibbs (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hsum : ∑ i, q i ≤ ∑ i, p i) :
    ∑ i, p i * -Real.log (p i) ≤ ∑ i, p i * -Real.log (q i) := by
  have hterm : ∀ i, p i * Real.log (q i) - p i * Real.log (p i) ≤ q i - p i := by
    intro i
    rcases (hp i).eq_or_lt with h0 | hpos
    · rw [← h0]
      simpa using (hq i).le
    · have hlog := Real.log_le_sub_one_of_pos (div_pos (hq i) hpos)
      rw [Real.log_div (hq i).ne' hpos.ne'] at hlog
      have hscaled := mul_le_mul_of_nonneg_left hlog hpos.le
      have hcancel : p i * (q i / p i - 1) = q i - p i := by
        field_simp
      linarith
  have htotal : ∑ i, (p i * Real.log (q i) - p i * Real.log (p i)) ≤ ∑ i, (q i - p i) :=
    Finset.sum_le_sum fun i _ => hterm i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at htotal
  simp_rw [mul_neg, Finset.sum_neg_distrib]
  linarith

/-- **No code beats the entropy.** If the code lengths satisfy Kraft's inequality (here in
natural units), the average length is at least the entropy. -/
theorem expected_length_ge_entropy (p len : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hone : ∑ i, p i = 1)
    (hkraft : ∑ i, Real.exp (-len i) ≤ 1) :
    ∑ i, p i * -Real.log (p i) ≤ ∑ i, p i * len i := by
  have h := gibbs p (fun i => Real.exp (-len i)) hp (fun i => Real.exp_pos _)
    (by rw [hone]; exact hkraft)
  simpa [Real.log_exp] using h

end Entropy

/-! ### Distance: travel is description length -/

section Description

/-- The cost of describing weights `θ` to someone who has the starting weights `θ₀`, at
precision `σ`: the squared distance over `2 σ²`. -/
noncomputable def GET_DESCRIPTION_LENGTH {Θ : Type*} [NormedAddCommGroup Θ] (σ : ℝ) (θ₀ θ : Θ) : ℝ :=
  ‖θ - θ₀‖ ^ 2 / (2 * σ ^ 2)

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- **Gradient descent finds the fit that is cheapest to describe.** -/
theorem descriptionLength_gradientDescent_le (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ₀ : Θ) (t : ℕ)
    (hfit : A ((TAKE_GRADIENT_STEP A y η)^[t] θ₀) = y) {θ' : Θ} (hfit' : A θ' = y) (σ : ℝ) :
    GET_DESCRIPTION_LENGTH σ θ₀ ((TAKE_GRADIENT_STEP A y η)^[t] θ₀) ≤ GET_DESCRIPTION_LENGTH σ θ₀ θ' :=
  div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (gradientDescent_fit_is_nearest A y η θ₀ t hfit hfit') 2)
    (by positivity)

/-- **A bigger model's fit is cheaper to describe.** With orthogonal features of strength
`c`, the description length of the nearest fit is the squared error at the start over
`2 σ² c`. -/
theorem travel_sq_div_eq_of_tight {A : Θ →L[ℝ] Y} {c : ℝ} (h : HAS_TIGHT_FEATURES A c) (hc : 0 < c)
    (y : Y) (θ₀ : Θ) (σ : ℝ) :
    GET_TRAVEL (A : Θ →ₗ[ℝ] Y) y θ₀ ^ 2 / (2 * σ ^ 2)
      = ‖GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀‖ ^ 2 / (2 * σ ^ 2 * c) := by
  rw [h.travel_eq hc, div_pow, Real.sq_sqrt hc.le, div_div, mul_comm c]

end Description

end SquigglyLine
