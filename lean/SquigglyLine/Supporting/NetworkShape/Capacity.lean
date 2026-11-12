/-
Storage capacity: what a network can memorise.

* `finrank_le_of_fits_all` : a model linear in its weights that can fit every
  set of labels has at least as many weights as data points.
* `exists_unfittable` : with fewer weights than data points, some set of
  labels cannot be fitted.
* `two_pow_card_le_of_memorises` : a family of networks that realises every
  yes-or-no labelling of `n` inputs has at least `2 ^ n` settings of its
  weights.
* `card_le_bits_of_memorises` : so with `b` bits of weights, `n ≤ b`.

The third count, one ReLU unit for each turn, is `card_ge_of_zigzag` in
`DepthSeparation.lean`.
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace SquigglyLine

/-! ### One parameter for each stored number -/

section Parameters

open Module

variable {Θ Y : Type*} [AddCommGroup Θ] [Module ℝ Θ] [Module.Finite ℝ Θ]
  [AddCommGroup Y] [Module ℝ Y]

/-- **One parameter for each stored number.** If a model that is linear in its weights can
fit every set of labels, it has at least as many weights as data points. -/
theorem finrank_le_of_fits_all (A : Θ →ₗ[ℝ] Y) (hfit : ∀ y, ∃ θ, A θ = y) :
    finrank ℝ Y ≤ finrank ℝ Θ := by
  have hrange : LinearMap.range A = ⊤ := LinearMap.range_eq_top.mpr hfit
  calc finrank ℝ Y = finrank ℝ (LinearMap.range A) := by rw [hrange, finrank_top]
    _ ≤ finrank ℝ Θ := LinearMap.finrank_range_le A

/-- **Too few weights: something cannot be fitted.** -/
theorem exists_unfittable (A : Θ →ₗ[ℝ] Y) (hfew : finrank ℝ Θ < finrank ℝ Y) :
    ∃ y, ∀ θ, A θ ≠ y := by
  by_contra hcon
  push Not at hcon
  exact absurd (finrank_le_of_fits_all A hcon) (not_le.mpr hfew)

end Parameters

/-! ### One bit for each stored bit -/

section Bits

variable {W X : Type*} [Fintype W]

/-- **Memorising `n` answers takes `2 ^ n` settings.** If some setting of the weights
realises every yes-or-no labelling of the inputs in `S`, there are at least `2 ^ |S|`
settings. -/
theorem two_pow_card_le_of_memorises (net : W → X → Bool) (S : Finset X)
    (hmem : ∀ label : S → Bool, ∃ w, ∀ x : S, net w x = label x) :
    2 ^ S.card ≤ Fintype.card W := by
  classical
  have hsurj : Function.Surjective fun (w : W) (x : S) => net w x := by
    intro label
    obtain ⟨w, hw⟩ := hmem label
    exact ⟨w, funext hw⟩
  calc 2 ^ S.card = Fintype.card (S → Bool) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    _ ≤ Fintype.card W := Fintype.card_le_of_surjective _ hsurj

/-- **One bit for each stored bit.** A network whose weights take `b` bits cannot memorise
every labelling of more than `b` inputs. -/
theorem card_le_bits_of_memorises (net : W → X → Bool) (S : Finset X) {b : ℕ}
    (hbits : Fintype.card W ≤ 2 ^ b)
    (hmem : ∀ label : S → Bool, ∃ w, ∀ x : S, net w x = label x) : S.card ≤ b :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp
    ((two_pow_card_le_of_memorises net S hmem).trans hbits)

end Bits

end SquigglyLine
