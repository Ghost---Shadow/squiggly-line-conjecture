/-
The squiggly line conjecture, formalised.

| File             | Contents                                                        | Status    |
|------------------|-----------------------------------------------------------------|-----------|
| `Defs`           | the line, the data, the two costs                               | —         |
| `RandomFunction` | a randomly initialised model, its marginals, its expected cost  | —         |
| `Conjecture`     | the conjecture and the learning claim                           | stated    |
| `Sandwich`       | `vertical / √(1 + K²) ≤ nearest ≤ vertical`                     | proved    |
| `Coverage`       | mean distance = uncovered mass integrated over tube radii       | proved    |
| `Marginal`       | a regression loss sees only one-point marginals                 | proved    |
| `RandomPhase`    | frequency does not change the marginals of a random-phase wave  | proved    |
| `Verdict`        | so the learning claim fails for random-phase waves              | proved    |
| `Oscillation`    | `nearest ≤ ρ` when `f` covers the labels within `ρ`; slope tax  | proved    |
| `SineCloser`     | sines: `vertical / √(1 + (A w)²) ≤ nearest ≤ π / w`; limit zero | proved    |
| `LinearModel`    | parameter space: a budget of movement buys `ε / d` of the loss  | proved    |
| `ExchangeRate`   | tight features: `travel = ‖residual‖ / √c`                      | proved    |
| `NarrowChain`    | one neuron per layer: the network never turns                   | proved    |
| `Polarizer`      | ReLU is a projection; a turn keeps `cos θ`; small turns survive | proved    |
| `Depth`          | `L` two-neuron layers turn `2 ^ L - 1` times                    | proved    |
| `Bridge`         | `L` folds are one Fourier term of frequency `2 ^ L`             | proved    |
| `Kernel`         | same kernel: same gradient-descent path and same travel         | proved    |
| `ThreePolarizers`| Malus's law, the plate chain, and more plates arriving closer   | proved    |
| `MarkovChains`   | merged stays merged; the photon's chain; training solved        | proved    |
| `Compression`    | any function squeezed by `w`: closer, steeper, no better        | proved    |
| `TentCloser`     | `L` two-neuron layers pass within `1 / 2 ^ L` of the unit square | proved    |
| `DoubleDescent`  | a near fit is tame; travel is large only where the kernel is weak | proved  |
| `Dimple`         | gentle on the data manifold, steep off it: loss blind, fragile   | proved    |
| `LeastAction`    | gradient descent reaches the nearest fit; even steps lose least  | proved    |
| `SpectralBias`   | each kernel direction shrinks by `(1 - η lam)^t`; strong first   | proved    |
| `Reparam`        | rescaling: same function, flatter by `c²`, farther by `|c|`      | proved    |
-/
import SquigglyLine.Defs
import SquigglyLine.RandomFunction
import SquigglyLine.Conjecture
import SquigglyLine.Sandwich
import SquigglyLine.Coverage
import SquigglyLine.Marginal
import SquigglyLine.RandomPhase
import SquigglyLine.Verdict
import SquigglyLine.Oscillation
import SquigglyLine.SineCloser
import SquigglyLine.LinearModel
import SquigglyLine.ExchangeRate
import SquigglyLine.NarrowChain
import SquigglyLine.Polarizer
import SquigglyLine.Depth
import SquigglyLine.Bridge
import SquigglyLine.Kernel
import SquigglyLine.ThreePolarizers
import SquigglyLine.MarkovChains
import SquigglyLine.SquigglyLineTheorem
import SquigglyLine.Compression
import SquigglyLine.TentCloser
import SquigglyLine.DoubleDescent
import SquigglyLine.Dimple
import SquigglyLine.LeastAction
import SquigglyLine.SpectralBias
import SquigglyLine.Reparam
