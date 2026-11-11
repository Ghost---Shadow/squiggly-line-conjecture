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
