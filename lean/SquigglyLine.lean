/-
The Squiggly Line Theorem, formalised.

The files come in three groups, one folder each. The first proves the
theorem. The second carries it to networks and to parameter space. The third
is supporting material: the same tools pointed at known puzzles, none of it
needed for the theorem. The README lists the files in the same groups.

## 0. Style

`SquigglyLine/Style.lean` holds the proof step `unfold_named_pieces` and
the names `RealFunction` and `PI`. `STYLE.md` sets out how every statement
is written.

## 1. The theorem

In `SquigglyLine/Theorem/`.

| File                  | Contents                                                       |
|-----------------------|----------------------------------------------------------------|
| `Defs`                | the curve, the data, the two costs                             |
| `RandomFunction`      | a randomly initialised model, its marginals, its expected cost |
| `Conjecture`          | the original conjecture and the learning claim, as statements  |
| `Sandwich`            | `vertical / √(1 + K²) ≤ nearest ≤ vertical`                    |
| `Coverage`            | mean distance = uncovered mass integrated over tube radii      |
| `Marginal`            | a regression loss sees only one-point marginals                |
| `Oscillation`         | `nearest ≤ ρ` when `f` covers the labels within `ρ`; the warp  |
| `RandomPhase`         | frequency does not change the marginals of a random-phase wave |
| `SineCloser`          | sines: `vertical / √(1 + (A w)²) ≤ nearest ≤ π / w`            |
| `Verdict`             | so the learning claim fails for random-phase waves             |
| `SquigglyLineTheorem` | the four statements for sines, as one theorem                  |
| `Compression`         | any function squeezed by `w`: closer, steeper, no better       |
| `Vocabulary`          | readable second names for the above; proves nothing            |

`SquigglyLine/Tests/` checks that each restyled statement says what its
original said.

| File                        | Contents                                         |
|-----------------------------|--------------------------------------------------|
| `Tests/StatementsUnchanged` | restyled statements against their original text  |

## 2. Networks and parameter space

In `SquigglyLine/Networks/`.

| File              | Contents                                                              |
|-------------------|-----------------------------------------------------------------------|
| `NarrowChain`     | one neuron per layer: the network never turns                         |
| `Depth`           | `L` two-neuron layers turn `2 ^ L - 1` times                          |
| `TentCloser`      | and pass within `1 / 2 ^ L` of every point of the unit square         |
| `Bridge`          | `L` folds are one Fourier term of frequency `2 ^ L`                   |
| `Polarizer`       | ReLU is a projection; a turn keeps `cos θ`; small turns survive       |
| `ThreePolarizers` | Malus's law, the plate chain, and more plates arriving closer         |
| `MarkovChains`    | merged stays merged; the photon's chain; training with tight features |
| `LinearModel`     | parameter space: a budget of movement buys `ε / d` of the loss        |
| `ExchangeRate`    | tight features: `travel = ‖residual‖ / √c`                            |
| `Kernel`          | same kernel: same gradient-descent path and same travel               |
| `DoubleDescent`   | a near fit is tame; travel is large only where the kernel is weak     |
| `Lift`            | squiggly below is flat above; slope ≤ tilt × stretch; kernel trick   |
| `FourierLift`     | the Fourier lift stretches by at most `w`; its kernel sees only gaps  |
| `RadialBasis`     | a bump of width `σ` has slope ≤ `1 / σ`; narrow bumps fit anything   |
| `Positions`       | sinusoidal overlap sees only the gap; rotary; relative bias; table   |

## 3. Supporting material

### How training moves

In `SquigglyLine/Supporting/Training/`.

| File              | Contents                                                         |
|-------------------|------------------------------------------------------------------|
| `LeastAction`     | gradient descent reaches the nearest fit; even steps lose least  |
| `SpectralBias`    | each kernel direction shrinks by `(1 - η lam)^t`; strong first   |
| `EdgeOfStability` | that error shrinks iff `η lam < 2`, and grows past it            |
| `Reparam`         | rescaling: same function, flatter by `c²`, farther by `|c|`      |
| `SmallSteps`      | a square-law loss over `N` steps is at most `c D² / N`           |
| `WeightDecay`     | weight decay leaves `mu / (lam + mu)`; early stopping matches it |
| `BatchSize`       | two small steps = one big step minus an `η²` cross-kernel term   |
| `ComputeBudget`   | `A / N + B / D` with `N D` fixed is least when the terms balance |
| `CrossEntropy`    | softmax loss pushes by prediction minus label; same kernel       |
| `GanGame`         | the best critic predicts the real share; the players spiral      |
| `Dropout`         | expected dropout loss = loss + `v` × squared shares: weight decay |
| `Perceptron`      | margin is nearness; at most `(R / γ)²` mistakes; XOR; no free lunch |
| `Symmetry`        | rescaling: gradient ⟂ weights, they only grow; `a² − b²` is kept    |
| `StepRules`       | Adam's step is a sign; clipping caps travel; subspaces; rounding    |
| `AdamW`           | decay inside Adam is rescaled away; outside it shrinks by `1 − η μ` |
| `Optimisers`      | schedules multiply; condition number; momentum's edge; SGD on average |
| `Regularisers`    | lasso zeroes; input noise and adversarial training charge slope; mixup |

### What a fit does to new inputs

In `SquigglyLine/Supporting/NewInputs/`.

| File                | Contents                                                         |
|---------------------|------------------------------------------------------------------|
| `SameKernel`        | same kernel and test row: same prediction at every step          |
| `BenignOverfitting` | the nearest fit swallows noise; junk features cap the damage     |
| `BiasVariance`      | expected squared error = bias² + variance; the floor is the dial |
| `Forgetting`        | a new task changes old errors through the cross kernel only      |
| `Pruning`           | pruning subtracts a kernel: slower, farther; when a ticket wins  |
| `Dimple`            | gentle on the data manifold, steep off it: loss blind, fragile   |
| `Averaging`         | ensemble error = mean error − spread; the ideal denoiser averages |

### The shape of a network

In `SquigglyLine/Supporting/NetworkShape/`.

| File                     | Contents                                                            |
|--------------------------|---------------------------------------------------------------------|
| `DepthSeparation`        | one hidden layer needs `2^L` units to follow `L + 1` tent layers    |
| `UniversalApproximation` | `2n` ReLU units in one layer are within `2K / n` of `f`             |
| `Capacity`               | storing arbitrary labels costs a parameter, or a bit, for each      |
| `SkipAndNorm`            | a skip is a bypass (never dims); a norm is an amplifier             |
| `VanishingGradients`     | a gain below one dies, above one blows up; gradients likewise       |
| `Bottleneck`             | labels ≤ places after any layer ≤ inputs; full compression          |
| `CodeLength`             | a fold loses one bit; loss ≥ entropy; travel² is description length |
| `NeuralCollapse`         | `K` unit arrows: every pair ≤ `c` forces `(K - 1) c ≥ -1`           |
| `ModeConnectivity`       | linear in weights: no hill between fits; `a * b`: the hill          |
| `Attention`              | attention averages, so it never spreads tokens; one head = one step |
| `SignedDistance`         | the theorem's distance is a distance field: slope ≤ 1; safe steps   |
| `NetworkSlope`           | slope ≤ product of layers; flipping costs score / slope; temperature |
| `Gain`                   | a fold keeps half (He initialisation); a Bellman sweep has slope `γ` |
| `Eikonal`                | toward the nearest point the distance falls at rate exactly one     |
| `AttentionRate`          | bounded scores: each layer shrinks the spread by `1 − exp(−2B)`     |
| `KolmogorovArnold`       | a node of edge curves is within `2 × slope / n` of a ReLU layer     |
| `RmsNorm`                | RMSNorm forgets the scale; pre-norm leaves the skip path alone     |
| `Residual`               | a skip keeps points apart; turns are bought in the branch; LSTM cell |
| `Activations`            | sigmoid slope ≤ 1/4; leaky ReLU; max pooling; spectral normalisation |
-/
-- 0. How statements are written
import SquigglyLine.Style
-- 1. The theorem
import SquigglyLine.Theorem.Defs
import SquigglyLine.Theorem.RandomFunction
import SquigglyLine.Theorem.Conjecture
import SquigglyLine.Theorem.Sandwich
import SquigglyLine.Theorem.Coverage
import SquigglyLine.Theorem.Marginal
import SquigglyLine.Theorem.Oscillation
import SquigglyLine.Theorem.RandomPhase
import SquigglyLine.Theorem.SineCloser
import SquigglyLine.Theorem.Verdict
import SquigglyLine.Theorem.SquigglyLineTheorem
import SquigglyLine.Theorem.Compression
import SquigglyLine.Theorem.Vocabulary
import SquigglyLine.Tests.StatementsUnchanged
-- 2. Networks and parameter space
import SquigglyLine.Networks.NarrowChain
import SquigglyLine.Networks.Depth
import SquigglyLine.Networks.TentCloser
import SquigglyLine.Networks.Bridge
import SquigglyLine.Networks.Polarizer
import SquigglyLine.Networks.ThreePolarizers
import SquigglyLine.Networks.MarkovChains
import SquigglyLine.Networks.LinearModel
import SquigglyLine.Networks.ExchangeRate
import SquigglyLine.Networks.Kernel
import SquigglyLine.Networks.DoubleDescent
import SquigglyLine.Networks.Lift
import SquigglyLine.Networks.FourierLift
import SquigglyLine.Networks.RadialBasis
import SquigglyLine.Networks.Positions
-- 3. Supporting material: how training moves
import SquigglyLine.Supporting.Training.LeastAction
import SquigglyLine.Supporting.Training.SpectralBias
import SquigglyLine.Supporting.Training.EdgeOfStability
import SquigglyLine.Supporting.Training.Reparam
import SquigglyLine.Supporting.Training.SmallSteps
import SquigglyLine.Supporting.Training.WeightDecay
import SquigglyLine.Supporting.Training.BatchSize
import SquigglyLine.Supporting.Training.ComputeBudget
import SquigglyLine.Supporting.Training.CrossEntropy
import SquigglyLine.Supporting.Training.GanGame
import SquigglyLine.Supporting.Training.Dropout
import SquigglyLine.Supporting.Training.Perceptron
import SquigglyLine.Supporting.Training.Symmetry
import SquigglyLine.Supporting.Training.StepRules
import SquigglyLine.Supporting.Training.AdamW
import SquigglyLine.Supporting.Training.Optimisers
import SquigglyLine.Supporting.Training.Regularisers
import SquigglyLine.Supporting.NetworkShape.RmsNorm
import SquigglyLine.Supporting.NetworkShape.Residual
import SquigglyLine.Supporting.NetworkShape.Activations
-- 3. Supporting material: what a fit does to new inputs
import SquigglyLine.Supporting.NewInputs.SameKernel
import SquigglyLine.Supporting.NewInputs.BenignOverfitting
import SquigglyLine.Supporting.NewInputs.BiasVariance
import SquigglyLine.Supporting.NewInputs.Forgetting
import SquigglyLine.Supporting.NewInputs.Pruning
import SquigglyLine.Supporting.NewInputs.Dimple
import SquigglyLine.Supporting.NewInputs.Averaging
-- 3. Supporting material: the shape of a network
import SquigglyLine.Supporting.NetworkShape.DepthSeparation
import SquigglyLine.Supporting.NetworkShape.UniversalApproximation
import SquigglyLine.Supporting.NetworkShape.Capacity
import SquigglyLine.Supporting.NetworkShape.SkipAndNorm
import SquigglyLine.Supporting.NetworkShape.VanishingGradients
import SquigglyLine.Supporting.NetworkShape.Bottleneck
import SquigglyLine.Supporting.NetworkShape.CodeLength
import SquigglyLine.Supporting.NetworkShape.NeuralCollapse
import SquigglyLine.Supporting.NetworkShape.ModeConnectivity
import SquigglyLine.Supporting.NetworkShape.Attention
import SquigglyLine.Supporting.NetworkShape.SignedDistance
import SquigglyLine.Supporting.NetworkShape.NetworkSlope
import SquigglyLine.Supporting.NetworkShape.Gain
import SquigglyLine.Supporting.NetworkShape.Eikonal
import SquigglyLine.Supporting.NetworkShape.AttentionRate
import SquigglyLine.Supporting.NetworkShape.KolmogorovArnold
