/-
Compression: folds, code length and travel.

Counting:
* `card_le_two_pow_of_code` : `digit_count` binary digits name at most
  `2 ^ digit_count` things.
* `tent_one_sub`, `eq_or_eq_one_sub_of_tent_eq` : a fold merges an input with
  its mirror image and with nothing else. It throws away one bit.
* `card_le_two_pow_of_iterate_tent_eq` : `fold_count` folds send at most
  `2 ^ fold_count` inputs to the same output.

Loss:
* `gibbs` : the average log-loss of any model is at least the entropy of the
  data.
* `expected_length_ge_entropy` : so is the average length of any code whose
  lengths satisfy Kraft's inequality.

Distance (description length taken as squared distance over
`2 * noise_scale ^ 2`):
* `GET_DESCRIPTION_LENGTH` : the cost of describing the weights to someone who
  has the starting weights.
* `descriptionLength_gradientDescent_le` : gradient descent reaches the fit
  that is cheapest to describe.
* `travel_sq_div_eq_of_tight` : with orthogonal features of strength
  `strength` that cost is the squared error at the start over
  `2 * noise_scale ^ 2 * strength`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import SquigglyLine.Networks.Bridge
import SquigglyLine.Supporting.Training.LeastAction

namespace SquigglyLine

/-! ### Counting: bits and folds -/

section Counting

/-- **`digit_count` binary digits name at most `2 ^ digit_count` things.** -/
theorem card_le_two_pow_of_code
    {Items : Type*}
    (items : Finset Items)
    {digit_count : ℕ}
    (code : Items → Fin digit_count → Bool)
    (code_is_injective : Set.InjOn code items) :
    let item_count := items.card
    let name_count := 2 ^ digit_count  -- each digit is one of two values
    item_count ≤ name_count := by
  unfold_named_pieces
  classical
  -- Distinct items get distinct names, so the names are as many as the items.
  calc items.card = (items.image code).card :=
        (Finset.card_image_of_injOn code_is_injective).symm
    _ ≤ Fintype.card (Fin digit_count → Bool) := Finset.card_le_univ _
    _ = 2 ^ digit_count := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **A fold merges an input with its mirror image.** -/
theorem tent_one_sub
    {input : ℝ}
    (input_nonneg : 0 ≤ input)
    (input_le_one : input ≤ 1) :
    let mirror_output := APPLY_TENT (1 - input)  -- the mirror image of the input
    let output        := APPLY_TENT input
    mirror_output = output := by
  unfold_named_pieces
  rcases le_total input (1 / 2) with in_left_half | in_right_half
  · rw [tent_of_le_half input_nonneg in_left_half,
      tent_of_half_le (by linarith)]
    ring
  · rw [tent_of_half_le in_right_half,
      tent_of_le_half (by linarith) (by linarith)]
    ring

/-- **And with nothing else.** Two inputs with the same output are equal or
are mirror images. -/
theorem eq_or_eq_one_sub_of_tent_eq
    {input other_input : ℝ}
    (input_mem : input ∈ Set.Icc (0 : ℝ) 1)
    (other_input_mem : other_input ∈ Set.Icc (0 : ℝ) 1)
    (same_output : APPLY_TENT other_input = APPLY_TENT input) :
    let are_equal  := other_input = input
    let are_mirror := other_input = 1 - input
    are_equal ∨ are_mirror := by
  unfold_named_pieces
  rcases le_total input (1 / 2) with in_left | in_right <;>
    rcases le_total other_input (1 / 2) with other_left | other_right
  · rw [tent_of_le_half other_input_mem.1 other_left,
      tent_of_le_half input_mem.1 in_left] at same_output
    exact Or.inl (by linarith)
  · rw [tent_of_half_le other_right,
      tent_of_le_half input_mem.1 in_left] at same_output
    exact Or.inr (by linarith)
  · rw [tent_of_le_half other_input_mem.1 other_left,
      tent_of_half_le in_right] at same_output
    exact Or.inr (by linarith)
  · rw [tent_of_half_le other_right, tent_of_half_le in_right] at same_output
    exact Or.inl (by linarith)

/-- **`fold_count` folds throw away at most `fold_count` bits.** At most
`2 ^ fold_count` inputs are sent to the same output. -/
theorem card_le_two_pow_of_iterate_tent_eq
    (fold_count : ℕ)
    (inputs : Finset ℝ)
    (inputs_in_unit : ∀ input ∈ inputs, input ∈ Set.Icc (0 : ℝ) 1)
    (common_output : ℝ)
    (all_same_output :
      ∀ input ∈ inputs, APPLY_TENT^[fold_count] input = common_output) :
    let input_count := inputs.card
    let input_limit := 2 ^ fold_count  -- each fold at most halves the inputs
    input_count ≤ input_limit := by
  unfold_named_pieces
  classical
  induction fold_count generalizing inputs common_output with
  | zero =>
    rw [pow_zero, Finset.card_le_one]
    intro first first_mem second second_mem
    have first_eq : first = common_output := by
      simpa using all_same_output first first_mem
    have second_eq : second = common_output := by
      simpa using all_same_output second second_mem
    rw [first_eq, second_eq]
  | succ previous_count ih =>
    -- After one fold, `previous_count` folds are left to do.
    have image_card_le : (inputs.image APPLY_TENT).card ≤ 2 ^ previous_count := by
      refine ih (inputs.image APPLY_TENT) (fun folded folded_mem => ?_)
        common_output (fun folded folded_mem => ?_)
      · obtain ⟨input, input_mem, rfl⟩ := Finset.mem_image.mp folded_mem
        exact tent_mem_Icc (inputs_in_unit input input_mem).1
          (inputs_in_unit input input_mem).2
      · obtain ⟨input, input_mem, rfl⟩ := Finset.mem_image.mp folded_mem
        rw [← Function.iterate_succ_apply]
        exact all_same_output input input_mem
    -- One fold sends at most two inputs (an input and its mirror) to a value.
    have fiber_card_le : ∀ output ∈ inputs.image APPLY_TENT,
        (inputs.filter fun input => APPLY_TENT input = output).card ≤ 2 := by
      intro output output_mem
      obtain ⟨base_input, base_mem, rfl⟩ := Finset.mem_image.mp output_mem
      have fiber_sub :
          (inputs.filter fun input => APPLY_TENT input = APPLY_TENT base_input)
            ⊆ {base_input, 1 - base_input} := by
        intro input input_mem
        obtain ⟨input_in_inputs, same_output⟩ := Finset.mem_filter.mp input_mem
        rcases eq_or_eq_one_sub_of_tent_eq (inputs_in_unit base_input base_mem)
            (inputs_in_unit input input_in_inputs) same_output with equal | mirror
        · rw [equal]
          exact Finset.mem_insert_self _ _
        · rw [mirror]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (Finset.card_le_card fiber_sub).trans Finset.card_le_two
    calc inputs.card ≤ 2 * (inputs.image APPLY_TENT).card :=
          Finset.card_le_mul_card_image inputs 2 fiber_card_le
      _ ≤ 2 * 2 ^ previous_count := Nat.mul_le_mul_left 2 image_card_le
      _ = 2 ^ (previous_count + 1) := by rw [pow_succ, mul_comm]

end Counting

/-! ### Loss: the entropy limit -/

section Entropy

variable {Outcomes : Type*} [Fintype Outcomes]

/-- **No model beats the entropy.** If the data has probabilities `data_prob`
and the model gives probabilities `model_prob`, the average log-loss is at
least the entropy of the data. -/
theorem gibbs
    (data_prob : Outcomes → ℝ)
    (model_prob : Outcomes → ℝ)
    (data_prob_nonneg : ∀ i, 0 ≤ data_prob i)
    (model_prob_pos : ∀ i, 0 < model_prob i)
    (model_total_le : ∑ i, model_prob i ≤ ∑ i, data_prob i) :
    let entropy  := ∑ i, data_prob i * -Real.log (data_prob i)
    let log_loss := ∑ i, data_prob i * -Real.log (model_prob i)
    entropy ≤ log_loss := by
  unfold_named_pieces
  -- Termwise, `log x ≤ x - 1` applied to `model_prob / data_prob`.
  have term_bound : ∀ i, data_prob i * Real.log (model_prob i)
      - data_prob i * Real.log (data_prob i) ≤ model_prob i - data_prob i := by
    intro i
    rcases (data_prob_nonneg i).eq_or_lt with prob_zero | prob_pos
    · rw [← prob_zero]
      simpa using (model_prob_pos i).le
    · have log_bound :=
        Real.log_le_sub_one_of_pos (div_pos (model_prob_pos i) prob_pos)
      rw [Real.log_div (model_prob_pos i).ne' prob_pos.ne'] at log_bound
      have scaled_bound := mul_le_mul_of_nonneg_left log_bound prob_pos.le
      have cancelled : data_prob i * (model_prob i / data_prob i - 1)
          = model_prob i - data_prob i := by
        field_simp
      linarith
  have total_bound : ∑ i, (data_prob i * Real.log (model_prob i)
      - data_prob i * Real.log (data_prob i)) ≤ ∑ i, (model_prob i - data_prob i) :=
    Finset.sum_le_sum fun i _ => term_bound i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at total_bound
  simp_rw [mul_neg, Finset.sum_neg_distrib]
  linarith

/-- **No code beats the entropy.** If the code lengths satisfy Kraft's
inequality (here in natural units), the average length is at least the
entropy. -/
theorem expected_length_ge_entropy
    (data_prob : Outcomes → ℝ)
    (code_length : Outcomes → ℝ)
    (data_prob_nonneg : ∀ i, 0 ≤ data_prob i)
    (data_total_is_one : ∑ i, data_prob i = 1)
    (kraft_holds : ∑ i, Real.exp (-code_length i) ≤ 1) :
    let entropy         := ∑ i, data_prob i * -Real.log (data_prob i)
    let expected_length := ∑ i, data_prob i * code_length i
    entropy ≤ expected_length := by
  unfold_named_pieces
  -- Treat `exp (-length)` as the model's probabilities and use `gibbs`.
  have gibbs_bound := gibbs data_prob (fun i => Real.exp (-code_length i))
    data_prob_nonneg (fun i => Real.exp_pos _)
    (by rw [data_total_is_one]; exact kraft_holds)
  simpa [Real.log_exp] using gibbs_bound

end Entropy

/-! ### Distance: travel is description length -/

section Description

/-- The cost of describing `weights` to someone who has the `start_weights`,
at precision `noise_scale`: the squared distance over `2 * noise_scale ^ 2`. -/
noncomputable def GET_DESCRIPTION_LENGTH
    {Weights : Type*} [NormedAddCommGroup Weights]
    (noise_scale : ℝ)
    (start_weights weights : Weights) : ℝ :=
  ‖weights - start_weights‖ ^ 2 / (2 * noise_scale ^ 2)  -- Gaussian code: squared distance over 2 variances

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- **Gradient descent finds the fit that is cheapest to describe.** -/
theorem descriptionLength_gradientDescent_le
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (step_count : ℕ)
    (trained_fits :
      predict ((TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights) = labels)
    {other_weights : Weights}
    (other_fits : predict other_weights = labels)
    (noise_scale : ℝ) :
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let trained_length :=
      GET_DESCRIPTION_LENGTH noise_scale start_weights trained_weights
    let other_length :=
      GET_DESCRIPTION_LENGTH noise_scale start_weights other_weights
    trained_length ≤ other_length := by
  unfold_named_pieces
  -- The trained fit is the nearest, and the cost grows with the distance.
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _)
      (gradientDescent_fit_is_nearest predict labels learning_rate
        start_weights step_count trained_fits other_fits) 2)
    (by positivity)

/-- **A bigger model's fit is cheaper to describe.** With orthogonal features
of strength `strength`, the description length of the nearest fit is the
squared error at the start over `2 * noise_scale ^ 2 * strength`. -/
theorem travel_sq_div_eq_of_tight
    {predict : Weights →L[ℝ] Outputs}
    {strength : ℝ}
    (features_are_tight : HAS_TIGHT_FEATURES predict strength)
    (strength_pos : 0 < strength)
    (labels : Outputs)
    (start_weights : Weights)
    (noise_scale : ℝ) :
    let travel := GET_TRAVEL (predict : Weights →ₗ[ℝ] Outputs) labels start_weights
    let residual :=
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels start_weights
    let travel_cost := travel ^ 2 / (2 * noise_scale ^ 2)
    let error_cost  := ‖residual‖ ^ 2 / (2 * noise_scale ^ 2 * strength)
    travel_cost = error_cost := by
  unfold_named_pieces
  rw [features_are_tight.travel_eq strength_pos, div_pow,
    Real.sq_sqrt strength_pos.le, div_div, mul_comm strength]

end Description

end SquigglyLine
