/-
Depth separation: a shallow network pays one unit per turn.

* `affineOn_reluUnit` : a ReLU unit is a straight line on any stretch that
  does not contain its kink.
* `AffineOn.not_zigzag` : a straight line cannot be lower at both ends of a
  stretch than in the middle.
* `exists_kink_of_zigzag` : so if a one-hidden-layer network goes up and comes
  back down, some unit has its kink in between.
* `card_ge_of_zigzag` : a zigzag with `m` ups and downs needs `m` units.
* `depth_separation` : `L + 1` tent layers (`2 (L + 1)` neurons) draw a zigzag
  that no one-hidden-layer network with fewer than `2 ^ L` units can follow,
  even to within one half at the grid points.
-/
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import SquigglyLine.Depth

namespace SquigglyLine

/-! ### Straight lines -/

/-- `f` is a straight line on the set `s`. -/
def AffineOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ p q : ℝ, ∀ x ∈ s, f x = p * x + q

namespace AffineOn

variable {f : ℝ → ℝ} {s : Set ℝ}

/-- A multiple of a straight line is a straight line. -/
theorem const_mul (k : ℝ) (h : AffineOn f s) : AffineOn (fun x => k * f x) s := by
  obtain ⟨p, q, h⟩ := h
  refine ⟨k * p, k * q, fun x hx => ?_⟩
  show k * f x = k * p * x + k * q
  rw [h x hx]
  ring

/-- **A straight line cannot go up and come back down.** -/
theorem not_zigzag {l m r : ℝ} (h : AffineOn f (Set.Icc l r)) (hlm : l < m) (hmr : m < r)
    (hl : f l < f m) (hr : f r < f m) : False := by
  obtain ⟨p, q, h⟩ := h
  rw [h l ⟨le_rfl, by linarith⟩, h m ⟨hlm.le, hmr.le⟩] at hl
  rw [h r ⟨by linarith, le_rfl⟩, h m ⟨hlm.le, hmr.le⟩] at hr
  have hp : 0 < p := by
    by_contra hp0
    push Not at hp0
    have := mul_nonneg (neg_nonneg.mpr hp0) (sub_pos.mpr hlm).le
    linarith
  have := mul_pos hp (sub_pos.mpr hmr)
  linarith

end AffineOn

/-- A sum of straight lines is a straight line. -/
theorem affineOn_sum {ι : Type*} (J : Finset ι) (f : ι → ℝ → ℝ) {s : Set ℝ}
    (h : ∀ j ∈ J, AffineOn (f j) s) : AffineOn (fun x => ∑ j ∈ J, f j x) s := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨0, 0, fun x _ => by simp⟩
  | insert j J hj ih =>
    obtain ⟨p₁, q₁, h₁⟩ := h j (Finset.mem_insert_self j J)
    obtain ⟨p₂, q₂, h₂⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨p₁ + p₂, q₁ + q₂, fun x hx => ?_⟩
    have h₂' : ∑ i ∈ J, f i x = p₂ * x + q₂ := h₂ x hx
    show ∑ i ∈ insert j J, f i x = (p₁ + p₂) * x + (q₁ + q₂)
    rw [Finset.sum_insert hj, h₁ x hx, h₂']
    ring

/-! ### One ReLU unit bends once -/

/-- A line that is below zero at `x` and above zero at `m` is zero somewhere strictly inside
any stretch that holds `x` and has `m` in its interior. -/
theorem exists_zero_between {w b l r x m : ℝ} (hlx : l ≤ x) (hxr : x ≤ r) (hlm : l < m)
    (hmr : m < r) (hx : w * x + b < 0) (hm : 0 < w * m + b) :
    ∃ z, l < z ∧ z < r ∧ w * z + b = 0 := by
  have hd : 0 < (w * m + b) - (w * x + b) := by linarith
  obtain ⟨s, hs⟩ : ∃ s, s = -(w * x + b) / ((w * m + b) - (w * x + b)) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs]
    exact div_pos (by linarith) hd
  have hs1 : s < 1 := by
    rw [hs, div_lt_one hd]
    linarith
  have hsd : s * ((w * m + b) - (w * x + b)) = -(w * x + b) := by
    rw [hs, div_mul_cancel₀ _ hd.ne']
  refine ⟨(1 - s) * x + s * m, ?_, ?_, ?_⟩
  · have h1 := mul_nonneg (sub_nonneg.mpr hs1.le) (sub_nonneg.mpr hlx)
    have h2 := mul_pos hs0 (sub_pos.mpr hlm)
    nlinarith
  · have h1 := mul_nonneg (sub_nonneg.mpr hs1.le) (sub_nonneg.mpr hxr)
    have h2 := mul_pos hs0 (sub_pos.mpr hmr)
    nlinarith
  · linear_combination hsd

/-- **A ReLU unit is straight away from its kink.** If `w * t + b` is never zero strictly
inside a stretch, the unit `max (w * x + b) 0` is a straight line on the whole stretch. -/
theorem affineOn_reluUnit {w b l r : ℝ} (hlr : l < r)
    (h : ∀ t, l < t → t < r → w * t + b ≠ 0) :
    AffineOn (fun x => max (w * x + b) 0) (Set.Icc l r) := by
  have hlm : l < (l + r) / 2 := by linarith
  have hmr : (l + r) / 2 < r := by linarith
  rcases lt_or_gt_of_ne (h _ hlm hmr) with hneg | hpos
  · refine ⟨0, 0, fun x hx => ?_⟩
    have hle : w * x + b ≤ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨z, hz1, hz2, hz⟩ := exists_zero_between (w := -w) (b := -b) hx.1 hx.2 hlm hmr
        (by linarith) (by linarith)
      exact h z hz1 hz2 (by linarith)
    show max (w * x + b) 0 = 0 * x + 0
    rw [max_eq_right hle]
    ring
  · refine ⟨w, b, fun x hx => ?_⟩
    have hge : 0 ≤ w * x + b := by
      by_contra hcon
      push Not at hcon
      obtain ⟨z, hz1, hz2, hz⟩ := exists_zero_between hx.1 hx.2 hlm hmr hcon hpos
      exact h z hz1 hz2 hz
    exact max_eq_left hge

/-! ### A network with one hidden layer -/

section Shallow

variable {ι : Type*}

/-- A network with one hidden layer of ReLU units, indexed by `J`: unit `j` has input weight
`w j`, bias `b j` and output weight `a j`. -/
noncomputable def shallow (J : Finset ι) (a w b : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ J, a j * max (w j * x + b j) 0

/-- **Every up-and-down holds a kink.** If the network is lower at both ends of a stretch
than at a point inside it, some unit has its kink strictly inside the stretch. -/
theorem exists_kink_of_zigzag (J : Finset ι) (a w b : ι → ℝ) {l m r : ℝ} (hlm : l < m)
    (hmr : m < r) (hl : shallow J a w b l < shallow J a w b m)
    (hr : shallow J a w b r < shallow J a w b m) :
    ∃ j ∈ J, w j ≠ 0 ∧ ∃ t, l < t ∧ t < r ∧ w j * t + b j = 0 := by
  by_contra hcon
  push Not at hcon
  have haff : AffineOn (shallow J a w b) (Set.Icc l r) := by
    show AffineOn (fun x => ∑ j ∈ J, a j * max (w j * x + b j) 0) (Set.Icc l r)
    refine affineOn_sum J (fun j x => a j * max (w j * x + b j) 0) (fun j hj => ?_)
    refine AffineOn.const_mul (f := fun x => max (w j * x + b j) 0) (a j) ?_
    by_cases hw : w j = 0
    · exact ⟨0, max (b j) 0, fun x _ => by simp [hw]⟩
    · exact affineOn_reluUnit (hlm.trans hmr) (hcon j hj hw)
  exact haff.not_zigzag hlm hmr hl hr

/-- **One unit per turn.** If the network goes up and comes back down `m` times along an
increasing run of inputs, it has at least `m` units. -/
theorem card_ge_of_zigzag (J : Finset ι) (a w b : ι → ℝ) {x : ℕ → ℝ} (hx : StrictMono x)
    {m : ℕ}
    (hzig : ∀ i < m, shallow J a w b (x (2 * i)) < shallow J a w b (x (2 * i + 1))
      ∧ shallow J a w b (x (2 * i + 2)) < shallow J a w b (x (2 * i + 1))) :
    m ≤ J.card := by
  have hkink : ∀ i ∈ Finset.range m, ∃ j ∈ J, w j ≠ 0 ∧
      ∃ t, x (2 * i) < t ∧ t < x (2 * i + 2) ∧ w j * t + b j = 0 := by
    intro i hi
    obtain ⟨hup, hdown⟩ := hzig i (Finset.mem_range.mp hi)
    exact exists_kink_of_zigzag J a w b (hx (by omega)) (hx (by omega)) hup hdown
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Nat.zero_le _
  obtain ⟨j₀, -⟩ := hkink 0 (Finset.mem_range.mpr hm)
  have : Nonempty ι := ⟨j₀⟩
  choose! unit hunit using hkink
  have hinj : Set.InjOn unit (Finset.range m : Set ℕ) := by
    intro i hi i' hi' heq
    obtain ⟨-, hw, t, ht1, ht2, ht⟩ := hunit i (Finset.mem_coe.mp hi)
    obtain ⟨-, -, t', ht1', ht2', ht'⟩ := hunit i' (Finset.mem_coe.mp hi')
    rw [← heq] at ht'
    have htt : t = t' := mul_left_cancel₀ hw (by linarith)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := hx.monotone (show 2 * i + 2 ≤ 2 * i' by omega)
      linarith
    · have := hx.monotone (show 2 * i' + 2 ≤ 2 * i by omega)
      linarith
  calc m = (Finset.range m).card := (Finset.card_range m).symm
    _ ≤ J.card := Finset.card_le_card_of_injOn unit (fun i hi => (hunit i hi).1) hinj

/-- **Depth separation.** `L + 1` tent layers use `2 (L + 1)` neurons. A network with one
hidden layer that stays within one half of them at the `2 ^ (L + 1) + 1` grid points has at
least `2 ^ L` units. -/
theorem depth_separation (J : Finset ι) (a w b : ι → ℝ) (L : ℕ)
    (hclose : ∀ k : ℕ, k ≤ 2 ^ (L + 1) →
      |shallow J a w b ((k : ℝ) / 2 ^ (L + 1)) - tent^[L + 1] ((k : ℝ) / 2 ^ (L + 1))|
        < 1 / 2) :
    2 ^ L ≤ J.card := by
  have hlow : ∀ k : ℕ, k ≤ 2 ^ (L + 1) → Even k → shallow J a w b ((k : ℝ) / 2 ^ (L + 1)) < 1 / 2 := by
    intro k hk hev
    have h := hclose k hk
    rw [iterate_tent_dyadic (L + 1) k hk, ite_eq_left hev, sub_zero] at h
    exact (abs_lt.mp h).2
  have hhigh : ∀ k : ℕ, k ≤ 2 ^ (L + 1) → ¬ Even k →
      1 / 2 < shallow J a w b ((k : ℝ) / 2 ^ (L + 1)) := by
    intro k hk hodd
    have h := hclose k hk
    rw [iterate_tent_dyadic (L + 1) k hk, ite_eq_right hodd] at h
    have := (abs_lt.mp h).1
    linarith
  have hpow : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ, mul_comm]
  refine card_ge_of_zigzag J a w b (x := fun n : ℕ => (n : ℝ) / 2 ^ (L + 1)) ?_ ?_
  · intro i j hij
    show (i : ℝ) / 2 ^ (L + 1) < (j : ℝ) / 2 ^ (L + 1)
    gcongr
  · intro i hi
    have h0 := hlow (2 * i) (by omega) (even_two_mul i)
    have h1 := hhigh (2 * i + 1) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one i)
    have h2 := hlow (2 * i + 2) (by omega) ⟨i + 1, by ring⟩
    exact ⟨h0.trans h1, h2.trans h1⟩

end Shallow

end SquigglyLine
