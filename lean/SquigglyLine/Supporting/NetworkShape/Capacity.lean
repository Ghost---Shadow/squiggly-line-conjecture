/-
Storage capacity: what a network can memorise.

* `finrank_le_of_fits_all` : a model linear in its weights that can fit every
  set of labels has at least as many weights as data points.
* `exists_unfittable` : with fewer weights than data points, some set of
  labels cannot be fitted.
* `two_pow_card_le_of_memorises` : a family of networks that realises every
  yes-or-no labelling of `input_count` inputs has at least `2 ^ input_count`
  settings of its weights.
* `card_le_bits_of_memorises` : so with `bit_count` bits of weights,
  `input_count ≤ bit_count`.

The third count, one ReLU unit for each turn, is `card_ge_of_zigzag` in
`DepthSeparation.lean`.

| Name                           | Meaning                                  |
|--------------------------------|------------------------------------------|
| `Weights →ₗ[ℝ] Outputs`        | a model that is linear in its weights    |
| `finrank ℝ Weights`            | how many numbers the weights hold        |
| `YesNoNetwork Settings Inputs` | a setting and an input give yes or no    |
| `YesNoLabelling chosen_inputs` | a yes or a no for each chosen input      |
| `Fintype.card Settings`        | how many settings of the weights exist   |
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import SquigglyLine.Style

namespace SquigglyLine

/-! ### Types -/

/-- A family of yes-or-no networks: a setting of the weights and an input
give a yes or a no.
Python: `Callable[[Setting, Input], bool]`. -/
abbrev YesNoNetwork (Settings Inputs : Type*) := Settings → Inputs → Bool

/-- A yes or a no for each of the chosen inputs.
Python: `dict[Input, bool]`, with the chosen inputs as keys. -/
abbrev YesNoLabelling {Inputs : Type*} (chosen_inputs : Finset Inputs) :=
  chosen_inputs → Bool

/-! ### One parameter for each stored number -/

section Parameters

open Module

variable {Weights Outputs : Type*}
  [AddCommGroup Weights] [Module ℝ Weights] [Module.Finite ℝ Weights]
  [AddCommGroup Outputs] [Module ℝ Outputs]

/-- **One parameter for each stored number.** If a model that is linear in
its weights can fit every set of labels, it has at least as many weights as
data points. -/
theorem finrank_le_of_fits_all
    (predict : Weights →ₗ[ℝ] Outputs)                              -- `→ₗ[ℝ]`: linear, so twice the weights give twice the outputs
    (fits_every_labels : ∀ labels, ∃ weights, predict weights = labels) :
    let label_count  := finrank ℝ Outputs                          -- one label for each data point: the number of data points
    let weight_count := finrank ℝ Weights                          -- `finrank`: how many numbers the weights hold
    label_count ≤ weight_count := by
  unfold_named_pieces
  -- The predictions reach every set of labels, and a linear map cannot
  -- reach more dimensions than it starts from.
  have predictions_reach_everything : LinearMap.range predict = ⊤ :=
    LinearMap.range_eq_top.mpr fits_every_labels
  calc finrank ℝ Outputs
      = finrank ℝ (LinearMap.range predict) := by
        rw [predictions_reach_everything, finrank_top]
    _ ≤ finrank ℝ Weights := LinearMap.finrank_range_le predict

/-- **Too few weights: something cannot be fitted.** -/
theorem exists_unfittable
    (predict : Weights →ₗ[ℝ] Outputs)
    (too_few_weights : finrank ℝ Weights < finrank ℝ Outputs) :    -- fewer weights than data points
    ∃ labels : Outputs,
      let no_weights_fit_them := ∀ weights, predict weights ≠ labels
      no_weights_fit_them := by
  unfold_named_pieces
  -- Otherwise every set of labels is fitted, and the count above applies.
  by_contra every_labels_fitted
  push Not at every_labels_fitted
  exact absurd (finrank_le_of_fits_all predict every_labels_fitted)
    (not_le.mpr too_few_weights)

end Parameters

/-! ### One bit for each stored bit -/

section Bits

variable {Settings Inputs : Type*} [Fintype Settings]

/-- **Memorising `input_count` answers takes `2 ^ input_count` settings.** If
some setting of the weights realises every yes-or-no labelling of the chosen
inputs, there are at least `2 ^ input_count` settings. -/
theorem two_pow_card_le_of_memorises
    (network : YesNoNetwork Settings Inputs)
    (chosen_inputs : Finset Inputs)
    (memorises_every_labelling :
      ∀ labelling : YesNoLabelling chosen_inputs,
        ∃ setting, ∀ input : chosen_inputs,
          network setting input = labelling input) :
    let input_count     := chosen_inputs.card
    let labelling_count := 2 ^ input_count                         -- a yes or a no for each input: 2 * 2 * ... * 2 labellings
    let setting_count   := Fintype.card Settings
    labelling_count ≤ setting_count := by
  unfold_named_pieces
  classical
  -- Two labellings cannot share a setting, so "the labelling a setting
  -- realises" reaches every labelling.
  have every_labelling_is_reached :
      Function.Surjective
        fun (setting : Settings) (input : chosen_inputs) =>
          network setting input := by
    intro labelling
    obtain ⟨setting, setting_realises_it⟩ :=
      memorises_every_labelling labelling
    exact ⟨setting, funext setting_realises_it⟩
  calc 2 ^ chosen_inputs.card
      = Fintype.card (chosen_inputs → Bool) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    _ ≤ Fintype.card Settings :=
        Fintype.card_le_of_surjective _ every_labelling_is_reached

/-- **One bit for each stored bit.** A network whose weights take `bit_count`
bits cannot memorise every labelling of more than `bit_count` inputs. -/
theorem card_le_bits_of_memorises
    (network : YesNoNetwork Settings Inputs)
    (chosen_inputs : Finset Inputs)
    {bit_count : ℕ}
    (settings_fit_in_bits : Fintype.card Settings ≤ 2 ^ bit_count)  -- `bit_count` bits spell out at most `2 ^ bit_count` settings
    (memorises_every_labelling :
      ∀ labelling : YesNoLabelling chosen_inputs,
        ∃ setting, ∀ input : chosen_inputs,
          network setting input = labelling input) :
    let input_count := chosen_inputs.card
    input_count ≤ bit_count := by
  unfold_named_pieces
  -- `2 ^ input_count ≤ setting_count ≤ 2 ^ bit_count`, then compare powers.
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp
    ((two_pow_card_le_of_memorises network chosen_inputs
      memorises_every_labelling).trans settings_fit_in_bits)

end Bits

end SquigglyLine
