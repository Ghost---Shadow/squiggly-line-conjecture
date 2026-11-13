/-
A regression loss sees only one-point marginals.

The expected loss of a random model at initialisation depends on the
distribution of its output at each single input, and on nothing else. How
the outputs at two different inputs move together (which is what "squiggly"
means) does not enter.

Theorems:

* `integral_residualLoss_eq_integral_marginal`  the loss on one data point,
  averaged over the draw, is an average over the output at that input;
* `expected_residualLoss_congr`                 equal one-point marginals
  give equal expected loss, on any data.
-/
import SquigglyLine.Theorem.RandomFunction

namespace SquigglyLine

open MeasureTheory

variable {Inputs : Type*} {random_model other_model : RandomFunction Inputs}
  {loss_fn : RealFunction}

/-- The expected loss on one data point is an integral against the one-point
marginal. -/
theorem integral_residualLoss_eq_integral_marginal
    (random_model : RandomFunction Inputs)
    (loss_is_measurable : Measurable loss_fn)  -- so the averages below exist
    (data_point : DataPoint Inputs) :
    let input := GET_INPUT data_point
    let label := GET_LABEL data_point
    let loss_averaged_over_draws :=
      ∫ parameters,
        GET_RESIDUAL_LOSS loss_fn (random_model.eval parameters) data_point
        ∂random_model.prior
    let loss_averaged_over_outputs :=
      ∫ output, loss_fn (label - output) ∂random_model.marginal input  -- only the output at this one input is used
    loss_averaged_over_draws = loss_averaged_over_outputs :=
  (integral_map
    (random_model.measurable_eval data_point.1).aemeasurable
    (loss_is_measurable.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable).symm

/-- **Marginal lemma.** Equal one-point marginals give equal expected loss,
on any data. -/
theorem expected_residualLoss_congr [MeasurableSpace Inputs]
    (loss_is_measurable : Measurable loss_fn)
    (same_marginals : random_model.marginal = other_model.marginal)
    (data_distribution : DataDistributionOver Inputs) :
    let expected_loss :=
      random_model.expected (GET_RESIDUAL_LOSS loss_fn) data_distribution
    let other_expected_loss :=
      other_model.expected (GET_RESIDUAL_LOSS loss_fn) data_distribution
    expected_loss = other_expected_loss := by
  unfold_named_pieces
  -- Write both sides through the marginals; then they are the same integral.
  simp only [RandomFunction.expected,
    integral_residualLoss_eq_integral_marginal _ loss_is_measurable,
    same_marginals]

end SquigglyLine
