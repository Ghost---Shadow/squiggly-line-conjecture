/-
The squiggly line theorem, for any function.

Nothing in the sine case used the sine. Take any model and squeeze it
sideways by a factor: `input ↦ model(squeeze_factor * input)`. Then

* it is **closer**: the oscillation scale is divided by the factor;
* it is **steeper**: the slope is multiplied by the factor;
* it is **no better**: if the output has the same distribution at every
  input, no expected regression loss changes.

`squiggly_line_theorem_general` collects the three, with the warp, as one
statement in any number of input dimensions. The sine case is the special
case of a sine squeezed by its frequency.

| Name                        | Meaning                                    |
|-----------------------------|--------------------------------------------|
| `COMPRESS factor model`     | the model, squeezed sideways by the factor |
| `.compress factor`          | the same for a random model                |
| `HAS_HOMOGENEOUS_MARGINALS` | same output distribution at every input    |

Theorems: `COVERS_WITHIN.compress`, `lipschitzWith_compress`,
`marginal_compress_eq`, `squiggly_line_theorem_general`.
-/
import SquigglyLine.Theorem.Marginal
import SquigglyLine.Theorem.Oscillation

namespace SquigglyLine

open MeasureTheory Filter Topology NNReal

variable {Inputs : Type*} [SeminormedAddCommGroup Inputs] [NormedSpace ℝ Inputs]
  {model : Model Inputs} {reach squeeze_factor : ℝ} {label_range : Set ℝ}

/-- Squeeze a model sideways by the factor `squeeze_factor`.
Python: `lambda input: model(squeeze_factor * input)`. -/
def COMPRESS (squeeze_factor : ℝ) (model : Model Inputs) : Model Inputs :=
  fun input => model (squeeze_factor • input)

/-- **Closer.** Squeezing by a factor divides the oscillation scale by that
factor. -/
theorem COVERS_WITHIN.compress
    (model_covers : COVERS_WITHIN model reach label_range)
    (squeeze_pos : 0 < squeeze_factor) :
    let squeezed_model := COMPRESS squeeze_factor model
    let squeezed_reach := reach / squeeze_factor  -- every distance along the input shrinks by the factor
    COVERS_WITHIN squeezed_model squeezed_reach label_range := by
  unfold_named_pieces
  intro input label label_in_range
  -- The unsqueezed model reaches the label near the stretched input.
  obtain ⟨stretched_hit, hit_is_near, hit_has_label⟩ :=
    model_covers (squeeze_factor • input) label label_in_range
  -- Squeeze that input back.
  refine ⟨squeeze_factor⁻¹ • stretched_hit, ?_, ?_⟩
  · have input_round_trip :
        input = squeeze_factor⁻¹ • (squeeze_factor • input) := by
      rw [smul_smul, inv_mul_cancel₀ squeeze_pos.ne', one_smul]
    calc dist input (squeeze_factor⁻¹ • stretched_hit)
        = dist (squeeze_factor⁻¹ • (squeeze_factor • input))
            (squeeze_factor⁻¹ • stretched_hit) := by rw [← input_round_trip]
      _ = squeeze_factor⁻¹ * dist (squeeze_factor • input) stretched_hit := by
          rw [dist_smul₀,
            Real.norm_of_nonneg (inv_nonneg.mpr squeeze_pos.le)]
      _ ≤ squeeze_factor⁻¹ * reach :=
          mul_le_mul_of_nonneg_left hit_is_near
            (inv_nonneg.mpr squeeze_pos.le)
      _ = reach / squeeze_factor := by rw [div_eq_inv_mul]
  · show model (squeeze_factor • squeeze_factor⁻¹ • stretched_hit) = label
    rw [smul_smul, mul_inv_cancel₀ squeeze_pos.ne', one_smul, hit_has_label]

/-- **Steeper.** Squeezing by a factor multiplies the slope by that
factor. -/
theorem lipschitzWith_compress
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    (squeeze : ℝ≥0) :
    let squeezed_model       := COMPRESS (squeeze : ℝ) model
    let squeezed_slope_limit := squeeze * slope_limit  -- the same climb over a shorter run
    LipschitzWith squeezed_slope_limit squeezed_model := by
  unfold_named_pieces
  refine LipschitzWith.of_dist_le_mul fun input other_input => ?_
  calc dist (model ((squeeze : ℝ) • input))
        (model ((squeeze : ℝ) • other_input))
      ≤ slope_limit
          * dist ((squeeze : ℝ) • input) ((squeeze : ℝ) • other_input) :=
        slope_is_bounded.dist_le_mul _ _
    _ = ((squeeze * slope_limit : ℝ≥0) : ℝ) * dist input other_input := by
        rw [dist_smul₀, Real.norm_of_nonneg squeeze.coe_nonneg,
          NNReal.coe_mul]
        ring

section Random

variable [MeasurableSpace Inputs]

/-- A random model, squeezed sideways by the factor `squeeze_factor`. -/
def RandomFunction.compress
    (random_model : RandomFunction Inputs)
    (squeeze_factor : ℝ) : RandomFunction Inputs where
  Param := random_model.Param
  prior := random_model.prior
  eval parameters :=
    SquigglyLine.COMPRESS squeeze_factor (random_model.eval parameters)
  measurable_eval input :=
    random_model.measurable_eval (squeeze_factor • input)

/-- The output of the random model has the same distribution at every
input. A random-phase wave is like this. -/
def HAS_HOMOGENEOUS_MARGINALS (random_model : RandomFunction Inputs) : Prop :=
  ∀ input other_input,
    random_model.marginal input = random_model.marginal other_input

omit [MeasurableSpace Inputs] in
/-- **No better.** Squeezing a random model with homogeneous marginals
changes none of its one-point marginals. -/
theorem marginal_compress_eq
    (random_model : RandomFunction Inputs)
    (marginals_are_homogeneous : HAS_HOMOGENEOUS_MARGINALS random_model)
    (squeeze_factor other_factor : ℝ) :
    let squeezed       := random_model.compress squeeze_factor
    let other_squeezed := random_model.compress other_factor
    squeezed.marginal = other_squeezed.marginal := by
  unfold_named_pieces
  funext input
  -- Squeezing only changes which input is read, and every input has the
  -- same output distribution.
  exact marginals_are_homogeneous
    (squeeze_factor • input) (other_factor • input)

/-- **The squiggly line theorem.** Squeeze a random model by a factor. If
every draw covers the labels within `reach` and has slope at most
`slope_limit`, and its one-point marginal is the same at every input, then:
the nearest-point distance lies between the vertical error divided by
`√(1 + (squeeze_factor * slope_limit)²)` and `reach / squeeze_factor`; its
expectation goes to zero as the factor grows; no expected regression loss
changes; and a warp of the input of size at most `reach / squeeze_factor`
fits any target. -/
theorem squiggly_line_theorem_general
    -- Given: a random model.
    (random_model : RandomFunction Inputs)
    -- Given: every draw reaches every label within `reach`.
    {slope_limit : SlopeLimit}
    (every_draw_covers :
      ∀ parameters,
        COVERS_WITHIN (random_model.eval parameters) reach label_range)
    -- Given: no draw is steeper than `slope_limit`.
    (every_slope_is_bounded :
      ∀ parameters,
        LipschitzWith slope_limit (random_model.eval parameters))
    -- Given: the output has the same distribution at every input.
    (marginals_are_homogeneous : HAS_HOMOGENEOUS_MARGINALS random_model)
    -- Given: a loss on the residual, such as `r ^ 2` or `|r|`.
    {loss_fn : RealFunction}
    (loss_is_measurable : Measurable loss_fn)  -- so its average exists; every loss in common use passes
    -- Given: the data, with labels in the range the model covers.
    (data_distribution : DataDistributionOver Inputs)
    [IsProbabilityMeasure data_distribution]   -- the probabilities add up to 1
    (labels_in_range :
      ∀ᵐ data_point ∂data_distribution,
        GET_LABEL data_point ∈ label_range) :

    -- Claim 1: the distance is squeezed between two bounds.
    let claim_1_distance_is_squeezed : Prop :=
      ∀ {squeeze_factor : ℝ}, 0 < squeeze_factor →
        ∀ (parameters : random_model.Param) (data_point : DataPoint Inputs),
          let squeezed_model :=
            (random_model.compress squeeze_factor).eval parameters
          let vertical_error   := GET_VERTICAL_ERROR squeezed_model data_point
          let nearest_distance := GET_NEAREST_DISTANCE squeezed_model data_point
          let slope_bound      := √(1 + (squeeze_factor * slope_limit) ^ 2)  -- Pythagoras: 1 across, squeeze_factor * slope_limit up
          let lower_bound      := vertical_error / slope_bound               -- a curve no steeper than that cannot pass any closer
          let upper_bound      := reach / squeeze_factor                     -- the covering distance, squeezed
          let label_is_in_range :=
            GET_LABEL data_point ∈ label_range
          let is_above_lower_bound := lower_bound ≤ nearest_distance
          let is_below_upper_bound := nearest_distance ≤ upper_bound
          label_is_in_range →
            is_above_lower_bound ∧ is_below_upper_bound

    -- Claim 2: the average distance goes to zero.
    let claim_2_distance_vanishes : Prop :=
      GOES_TO_ZERO_AS_INPUT_GROWS fun squeeze_factor =>  -- it is at most reach / squeeze_factor
        (random_model.compress squeeze_factor).expected
          GET_NEAREST_DISTANCE data_distribution

    -- Claim 3: the average loss is the same at every squeeze factor.
    let claim_3_loss_is_flat : Prop :=
      ∀ squeeze_factor other_factor : ℝ,
        let loss_here :=
          (random_model.compress squeeze_factor).expected
            (GET_RESIDUAL_LOSS loss_fn) data_distribution
        let loss_there :=
          (random_model.compress other_factor).expected
            (GET_RESIDUAL_LOSS loss_fn) data_distribution
        loss_here = loss_there  -- squeezing only changes which input is read

    -- Claim 4: a small shift of the input fits any target in range.
    let claim_4_warp_fits_any_target : Prop :=
      ∀ {squeeze_factor : ℝ}, 0 < squeeze_factor →
        ∀ (parameters : random_model.Param) (target : Model Inputs),
          let squeezed_model :=
            (random_model.compress squeeze_factor).eval parameters
          let max_shift := reach / squeeze_factor
          let target_stays_in_range :=
            ∀ input, target input ∈ label_range
          target_stays_in_range → ∃ warp : WarpOver Inputs,
            let moves_each_input_a_little :=
              ∀ input, dist input (warp input) ≤ max_shift
            let hits_the_target :=
              ∀ input, squeezed_model (warp input) = target input
            moves_each_input_a_little ∧ hits_the_target

    -- The theorem: all four claims hold.
    claim_1_distance_is_squeezed ∧
    claim_2_distance_vanishes ∧
    claim_3_loss_is_flat ∧
    claim_4_warp_fits_any_target := by

  -- Bring the four claims into scope.
  intro claim_1_distance_is_squeezed claim_2_distance_vanishes
    claim_3_loss_is_flat claim_4_warp_fits_any_target

  -- Proof of claim 1: the slope sandwich below, the covering bound above.
  have proof_of_claim_1 : claim_1_distance_is_squeezed := by
    intro squeeze_factor squeeze_pos parameters data_point
    unfold_named_pieces
    intro label_in_range
    refine ⟨?_, ?_⟩
    · have sandwich :=
        verticalDist_le_of_lipschitz
          (lipschitzWith_compress (every_slope_is_bounded parameters)
            ⟨squeeze_factor, squeeze_pos.le⟩)
          data_point
      change GET_VERTICAL_ERROR
            (COMPRESS squeeze_factor (random_model.eval parameters)) data_point
          ≤ √(1 + (squeeze_factor * (slope_limit : ℝ)) ^ 2)
            * GET_NEAREST_DISTANCE
              (COMPRESS squeeze_factor (random_model.eval parameters))
              data_point
        at sandwich
      rw [div_le_iff₀' (by positivity)]
      exact sandwich
    · exact nearestDist_le_of_coversWithin
        ((every_draw_covers parameters).compress squeeze_pos)
        data_point label_in_range

  -- Proof of claim 2: squeezed between zero and `reach / squeeze_factor`.
  have proof_of_claim_2 : claim_2_distance_vanishes :=
    squeeze_zero'
      (Eventually.of_forall fun _ =>
        expected_nearestDist_nonneg _ data_distribution)
      ((eventually_gt_atTop 0).mono fun squeeze_factor squeeze_pos =>
        expected_nearestDist_le (random_model.compress squeeze_factor)
          (fun parameters =>
            (every_draw_covers parameters).compress squeeze_pos)
          data_distribution labels_in_range)
      (tendsto_const_nhds.div_atTop tendsto_id)

  -- Proof of claim 3: the marginals do not change, so no loss does.
  have proof_of_claim_3 : claim_3_loss_is_flat :=
    fun squeeze_factor other_factor =>
      expected_residualLoss_congr loss_is_measurable
        (marginal_compress_eq random_model marginals_are_homogeneous
          squeeze_factor other_factor)
        data_distribution

  -- Proof of claim 4: a model that covers its range can be warped to fit.
  have proof_of_claim_4 : claim_4_warp_fits_any_target :=
    fun {squeeze_factor} squeeze_pos parameters target target_in_range =>
      exists_warp_of_coversWithin
        ((every_draw_covers parameters).compress squeeze_pos)
        target target_in_range

  -- All four together.
  exact ⟨proof_of_claim_1, proof_of_claim_2,
    proof_of_claim_3, proof_of_claim_4⟩

end Random

end SquigglyLine
