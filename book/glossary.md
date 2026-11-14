# Glossary

Every name the book uses, in plain words. The chapter is where it is
introduced.

## Ideas

| Word | Meaning | Chapter |
|---|---|---|
| model | a function from inputs to numbers; its graph is the squiggly line | 1 |
| data point | a pair of an input and a label | 1 |
| nearest distance | from a data point to the nearest point of the curve, in any direction | 1 |
| vertical error | from a data point straight up or down to the curve | 1 |
| residual | label minus prediction; what is left to fit | 1, 9 |
| slope limit | a number the model's slope never goes above | 3 |
| slope sandwich | `vertical / √(1 + slope²) ≤ nearest ≤ vertical` | 3 |
| reach | how far you must walk sideways before the curve has passed every label | 4 |
| covers within | the model hits every label of a range within `reach` of every input | 4 |
| oscillation scale | the smallest reach that works | 4 |
| warp | a way to move each input a little | 4 |
| random model | a model whose parameters are drawn at random | 5 |
| marginal | the distribution of the output at one single input | 5 |
| squeeze | make every wiggle of a function narrower by a factor | 7 |
| fold | a layer that bends the line back on itself, such as the tent | 8 |
| linear in its weights | the outputs on the data are a matrix times the weights | 9 |
| fit | weights that match every label | 9 |
| travel | distance in weight space from the start to the nearest fit | 9 |
| tight features | features at right angles on the data side, all of one squared length | 9 |
| exchange rate | `√squared_length`: how much error one unit of travel removes | 9 |
| kernel | the table of overlaps between the features of the data points | 10 |
| strength | how much the kernel scales a pattern of error | 10 |
| lift | the map from an input to its list of features | 11 |
| stretch | how much a lift can pull two nearby inputs apart | 11 |
| bump | a bell-shaped feature with a centre and a width | 11 |
| gain | the factor one layer multiplies the size of a signal by | 13, 14 |
| skip | a connection that adds a layer's input to its output | 14 |
| gate | a blend whose weights depend on the input | 14 |

## Names in the Lean files

| Name | Meaning | File |
|---|---|---|
| `Model`, `DataPoint` | a model; a data point | [`Defs.lean`](../lean/SquigglyLine/Theorem/Defs.lean) |
| `GET_INPUT`, `GET_LABEL` | the two parts of a data point | [`Defs.lean`](../lean/SquigglyLine/Theorem/Defs.lean) |
| `GET_NEAREST_DISTANCE` | the nearest distance | [`Defs.lean`](../lean/SquigglyLine/Theorem/Defs.lean) |
| `GET_VERTICAL_ERROR` | the vertical error | [`Defs.lean`](../lean/SquigglyLine/Theorem/Defs.lean) |
| `GET_RESIDUAL_LOSS` | a loss that reads only the residual | [`Defs.lean`](../lean/SquigglyLine/Theorem/Defs.lean) |
| `SlopeLimit` | a slope limit: a number that is not negative | [`Sandwich.lean`](../lean/SquigglyLine/Theorem/Sandwich.lean) |
| `LipschitzWith` | "has slope at most"; from Lean's mathematics library | |
| `COVERS_WITHIN` | covers a label range within a reach | [`Oscillation.lean`](../lean/SquigglyLine/Theorem/Oscillation.lean) |
| `Warp`, `WarpOver` | a warp | [`Vocabulary.lean`](../lean/SquigglyLine/Theorem/Vocabulary.lean) |
| `DataDistribution` | the data, as a distribution over data points | [`Vocabulary.lean`](../lean/SquigglyLine/Theorem/Vocabulary.lean) |
| `RandomFunction` | a random model | [`RandomFunction.lean`](../lean/SquigglyLine/Theorem/RandomFunction.lean) |
| `DRAW_SINE_CURVE` | the sine with a given amplitude, frequency and phase | [`SquigglyLineTheorem.lean`](../lean/SquigglyLine/Theorem/SquigglyLineTheorem.lean) |
| `HOLDS_FOR_EVERY_SINE` | for every frequency above zero and every phase | [`RandomPhase.lean`](../lean/SquigglyLine/Theorem/RandomPhase.lean) |
| `IS_IN_SINE_BAND` | the value is one a sine of that amplitude takes | [`RandomPhase.lean`](../lean/SquigglyLine/Theorem/RandomPhase.lean) |
| `COMPRESS` | a model, squeezed sideways | [`Compression.lean`](../lean/SquigglyLine/Theorem/Compression.lean) |
| `HAS_HOMOGENEOUS_MARGINALS` | same output distribution at every input | [`Compression.lean`](../lean/SquigglyLine/Theorem/Compression.lean) |
| `APPLY_TENT` | the two-neuron fold | [`Depth.lean`](../lean/SquigglyLine/Networks/Depth.lean) |
| `NEVER_TURNS` | the function only rises, or only falls | [`NarrowChain.lean`](../lean/SquigglyLine/Networks/NarrowChain.lean) |
| `GET_RESIDUAL` | labels minus the model's outputs | [`LinearModel.lean`](../lean/SquigglyLine/Networks/LinearModel.lean) |
| `GET_TRAVEL` | the travel | [`LinearModel.lean`](../lean/SquigglyLine/Networks/LinearModel.lean) |
| `HAS_TIGHT_FEATURES` | the features are tight | [`ExchangeRate.lean`](../lean/SquigglyLine/Networks/ExchangeRate.lean) |
| `TAKE_GRADIENT_STEP` | one step of gradient descent | [`Kernel.lean`](../lean/SquigglyLine/Networks/Kernel.lean) |
| `EVALUATE_LIFTED_MODEL` | lift, then dot with the weights | [`Lift.lean`](../lean/SquigglyLine/Networks/Lift.lean) |
| `GET_LIFT_KERNEL` | the overlap of two inputs after the lift | [`Lift.lean`](../lean/SquigglyLine/Networks/Lift.lean) |
| `LIFT_BY_FOURIER` | wind the input round a circle | [`FourierLift.lean`](../lean/SquigglyLine/Networks/FourierLift.lean) |
| `GET_BUMP` | the bell-shaped bump | [`RadialBasis.lean`](../lean/SquigglyLine/Networks/RadialBasis.lean) |
| `PASS_THROUGH_POLARIZER` | the shadow of an arrow of light on one direction | [`ThreePolarizers.lean`](../lean/SquigglyLine/Networks/ThreePolarizers.lean) |
| `ATTEND` | an attention head: a weighted average by softmax of the scores | [`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean) |
| `APPLY_SOFTMAX` | scores turned into shares that add up to one | [`CrossEntropy.lean`](../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean) |
| `DENOISE_IDEALLY` | the best possible denoiser for a set of examples | [`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean) |

The names of older definitions, for readers who come from the paper, are
listed in [`lean/RENAMES.txt`](../lean/RENAMES.txt).

Previous: [17. What is not here](17-what-is-not-here.md) · Next: [How to cite this book](how-to-cite.md)
