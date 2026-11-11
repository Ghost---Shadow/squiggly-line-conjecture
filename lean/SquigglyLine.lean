/-
The Squiggly Line Theorem, formalised.

The files come in three groups. The first proves the theorem. The second
carries it to networks and to parameter space. The third is supporting
material: the same tools pointed at known puzzles, none of it needed for the
theorem.

## 1. The theorem

| File                  | Contents                                                         |
|-----------------------|------------------------------------------------------------------|
| `Defs`                | the curve, the data, the two costs                               |
| `RandomFunction`      | a randomly initialised model, its marginals, its expected cost   |
| `Conjecture`          | the 2022 conjecture and the learning claim, as statements        |
| `Sandwich`            | `vertical / √(1 + K²) ≤ nearest ≤ vertical`                      |
| `Coverage`            | mean distance = uncovered mass integrated over tube radii        |
| `Marginal`            | a regression loss sees only one-point marginals                  |
| `Oscillation`         | `nearest ≤ ρ` when `f` covers the labels within `ρ`; the warp    |
| `RandomPhase`         | frequency does not change the marginals of a random-phase wave   |
| `SineCloser`          | sines: `vertical / √(1 + (A w)²) ≤ nearest ≤ π / w`              |
| `Verdict`             | so the learning claim fails for random-phase waves               |
| `SquigglyLineTheorem` | the four statements for sines, as one theorem                    |
| `Compression`         | any function squeezed by `w`: closer, steeper, no better         |

## 2. Networks and parameter space

| File              | Contents                                                             |
|-------------------|----------------------------------------------------------------------|
| `NarrowChain`     | one neuron per layer: the network never turns                        |
| `Depth`           | `L` two-neuron layers turn `2 ^ L - 1` times                         |
| `TentCloser`      | and pass within `1 / 2 ^ L` of every point of the unit square        |
| `Bridge`          | `L` folds are one Fourier term of frequency `2 ^ L`                  |
| `Polarizer`       | ReLU is a projection; a turn keeps `cos θ`; small turns survive      |
| `ThreePolarizers` | Malus's law, the plate chain, and more plates arriving closer        |
| `MarkovChains`    | merged stays merged; the photon's chain; training with tight features|
| `LinearModel`     | parameter space: a budget of movement buys `ε / d` of the loss       |
| `ExchangeRate`    | tight features: `travel = ‖residual‖ / √c`                           |
| `Kernel`          | same kernel: same gradient-descent path and same travel              |
| `DoubleDescent`   | a near fit is tame; travel is large only where the kernel is weak    |

## 3. Supporting material

| File                | Contents                                                           |
|---------------------|--------------------------------------------------------------------|
| `LeastAction`       | gradient descent reaches the nearest fit; even steps lose least    |
| `SpectralBias`      | each kernel direction shrinks by `(1 - η lam)^t`; strong first     |
| `EdgeOfStability`   | that error shrinks iff `η lam < 2`, and grows past it              |
| `Reparam`           | rescaling: same function, flatter by `c²`, farther by `|c|`        |
| `SmallSteps`        | a square-law loss over `N` steps is at most `c D² / N`             |
| `SameKernel`        | same kernel and test row: same prediction at every step            |
| `BenignOverfitting` | the nearest fit swallows noise; junk features cap the damage       |
| `Forgetting`        | a new task changes old errors through the cross kernel only        |
| `Pruning`           | pruning subtracts a kernel: slower, farther; when a ticket wins    |
| `Dimple`            | gentle on the data manifold, steep off it: loss blind, fragile     |
| `DepthSeparation`   | one hidden layer needs `2^L` units to follow `L + 1` tent layers   |
| `SkipAndNorm`       | a skip is a bypass (never dims); a norm is an amplifier            |
| `Bottleneck`        | labels ≤ places after any layer ≤ inputs; full compression         |
| `NeuralCollapse`    | `K` unit arrows: every pair ≤ `c` forces `(K - 1) c ≥ -1`          |
| `ModeConnectivity`  | linear in weights: no hill between fits; `a * b`: the hill         |
| `WeightDecay`       | weight decay leaves `mu / (lam + mu)`; early stopping matches it   |
| `BiasVariance`      | expected squared error = bias² + variance; the floor is the dial   |
| `VanishingGradients`| a gain below one dies, above one blows up; gradients likewise      |
-/
-- 1. The theorem
import SquigglyLine.Defs
import SquigglyLine.RandomFunction
import SquigglyLine.Conjecture
import SquigglyLine.Sandwich
import SquigglyLine.Coverage
import SquigglyLine.Marginal
import SquigglyLine.Oscillation
import SquigglyLine.RandomPhase
import SquigglyLine.SineCloser
import SquigglyLine.Verdict
import SquigglyLine.SquigglyLineTheorem
import SquigglyLine.Compression
-- 2. Networks and parameter space
import SquigglyLine.NarrowChain
import SquigglyLine.Depth
import SquigglyLine.TentCloser
import SquigglyLine.Bridge
import SquigglyLine.Polarizer
import SquigglyLine.ThreePolarizers
import SquigglyLine.MarkovChains
import SquigglyLine.LinearModel
import SquigglyLine.ExchangeRate
import SquigglyLine.Kernel
import SquigglyLine.DoubleDescent
-- 3. Supporting material
import SquigglyLine.LeastAction
import SquigglyLine.SpectralBias
import SquigglyLine.EdgeOfStability
import SquigglyLine.Reparam
import SquigglyLine.SmallSteps
import SquigglyLine.SameKernel
import SquigglyLine.BenignOverfitting
import SquigglyLine.Forgetting
import SquigglyLine.Pruning
import SquigglyLine.Dimple
import SquigglyLine.DepthSeparation
import SquigglyLine.SkipAndNorm
import SquigglyLine.Bottleneck
import SquigglyLine.NeuralCollapse
import SquigglyLine.ModeConnectivity
import SquigglyLine.WeightDecay
import SquigglyLine.BiasVariance
import SquigglyLine.VanishingGradients
