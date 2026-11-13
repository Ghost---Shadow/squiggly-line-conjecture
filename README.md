# The Squiggly Line Theorem

**A squigglier curve passes closer to the data. It is steeper by the same
factor. And the loss at the start cannot tell the difference.** What the
nearness buys is a short distance to move, not a head start.

![The same 16 points beside a smooth curve and a squiggly curve. The lines to the nearest point of the curve get much shorter on the squiggly curve. The vertical lines do not.](graphs/readme_two_distances.png)

This repository holds an idea about why large neural networks learn
fast, the experiments that tested it, and a machine-checked proof of what
turned out to be true.

**What it connects to.** The tools behind the theorem also give short,
machine-checked statements about well-known puzzles of deep learning:
[double descent](docs/networks/double-descent.md),
[lottery tickets](docs/supporting/new-inputs/lottery-ticket.md),
[adversarial examples and the dimpled manifold](docs/supporting/new-inputs/dimpled-manifold.md),
[benign overfitting](docs/supporting/new-inputs/benign-overfitting.md),
[spectral bias, early stopping and grokking](docs/supporting/training/spectral-bias.md),
[the edge of stability](docs/supporting/training/edge-of-stability.md),
[flat minima](docs/supporting/training/flat-minima.md),
[catastrophic forgetting](docs/supporting/new-inputs/forgetting.md),
[mode connectivity](docs/supporting/network-shape/mode-connectivity.md),
[neural collapse](docs/supporting/network-shape/neural-collapse.md),
[the information bottleneck](docs/supporting/network-shape/information-bottleneck.md),
[the platonic representation hypothesis](docs/supporting/new-inputs/same-kernel.md),
[depth separation](docs/supporting/network-shape/depth-separation.md),
[universal approximation](docs/supporting/network-shape/universal-approximation.md),
[vanishing and exploding gradients](docs/supporting/network-shape/vanishing-gradients.md),
[skip connections and normalisation](docs/supporting/network-shape/skip-and-norm.md),
[weight decay](docs/supporting/training/weight-decay.md),
[bias and variance](docs/supporting/new-inputs/bias-variance.md),
[the linear scaling rule for batch size](docs/supporting/training/batch-size.md),
[storage capacity](docs/supporting/network-shape/capacity.md),
[compression and code length](docs/supporting/network-shape/code-length.md),
[the Chinchilla scaling rule](docs/supporting/training/compute-budget.md),
[softmax and cross-entropy](docs/supporting/training/cross-entropy.md),
[the GAN game](docs/supporting/training/gan-game.md),
[dropout](docs/supporting/training/dropout.md),
[attention and in-context learning](docs/supporting/network-shape/attention.md),
[signed distance functions](docs/supporting/network-shape/signed-distance.md),
[the kernel trick](docs/networks/kernel-trick.md),
[Fourier features and position signals](docs/networks/fourier-lift.md),
[radial basis functions](docs/networks/radial-basis.md),
[the perceptron, XOR and no free lunch](docs/supporting/training/perceptron.md),
[adversarial examples and temperature](docs/supporting/network-shape/network-slope.md),
[ensembles and diffusion](docs/supporting/new-inputs/averaging.md),
[normalisation](docs/supporting/training/symmetry.md),
[Adam, clipping and low-rank training](docs/supporting/training/step-rules.md), and
[He initialisation](docs/supporting/network-shape/gain.md).
Each is proved for a simplified model, most often a fixed kernel (the
lazy-training, or neural tangent kernel, regime), and none is needed for the
theorem. They are collected under [supporting material](#8-supporting-material).

- Proofs: [`lean/`](lean), rebuilt on every push [![Lean proofs](https://github.com/Ghost---Shadow/squiggly-line-theorem/actions/workflows/lean.yml/badge.svg)](https://github.com/Ghost---Shadow/squiggly-line-theorem/actions/workflows/lean.yml)
- Paper (draft of 11 Nov 2026): [`paper/main.pdf`](paper/main.pdf)
- Write-up: [ad-absurdum.me/blog/squiggly-line-conjecture](https://ad-absurdum.me/blog/squiggly-line-conjecture)
- Slides: [Google Slides](https://docs.google.com/presentation/d/1xFoVq8pzuHHCICbLZh_NTZbHF80gQJMp8VbFF8Pzskc/edit?usp=sharing)
- Findings in full: [`docs/RESOLUTION.md`](docs/RESOLUTION.md)

> **Looking for an arXiv endorsement.** I would like to post the paper on arXiv
> and I am not affiliated with an institution, so I need an endorsement for
> `cs.LG`. If you are an arXiv endorser and are willing to look at it, please
> open an issue on this repository or write to the address on the first page
> of the paper.

> **A side idea: a neural network made of polarizers.** A layer of a network
> turns its input and keeps part of it. A polarizer plate does the same to
> light. So a stack of printed plates, with the angle of each plate as a
> weight, would be a network that computes as the light passes through. It is
> an idea and not a device. See [a network made of polarizers](#a-network-made-of-polarizers).

Start with [how this helps you](#how-does-this-help-me), or read the argument
in order: [the idea](#1-the-idea), [the theorem](#2-the-theorem),
[why it is true](#3-why-it-is-true), [what it does to the idea](#4-what-it-does-to-the-idea),
[where the idea is right](#5-where-the-idea-is-right), [the evidence](#6-the-evidence),
[the proofs](#7-the-proofs). After that come
[a network made of polarizers](#a-network-made-of-polarizers) and the
[supporting material](#8-supporting-material).

## The style philosophy: readable, pythonic, "enterprise_grade"

A proof is code. It is read far more often than it is written, it gets
changed, and other proofs come to depend on it. So this project writes its
theorems the way a careful engineer writes software, and not in the
traditional notation of mathematics.

Traditional notation was made for a blackboard: single letters, Greek, and
as much as possible on one line. That is quick to write and slow to read,
because the reader has to carry what `A`, `w`, `φ`, `ℓ` and `μ` stand for.
It is also hard to maintain, because nobody can safely change a line they
cannot read. The position taken here is that named, chunked statements beat
it: they are easier to check, easier to change and open to far more readers.

![The squiggly line theorem side by side. On the left, the statement as first written, with 13 single-letter and Greek names marked. On the right, the same statement with named givens, one quantity per line and one named claim per block.](graphs/readme_before_and_after.png)

The picture shows the first restyle (commit `edbec22`). The global names
have since become verbs, as in the second block below; the layout is the
same.

Here is one claim of the theorem, in traditional notation and in this
style. Lean checks that the two say the same thing.

```lean
-- Traditional
GET_VERTICAL_ERROR ((MAKE_RANDOM_PHASE_SINE A w).eval φ) p / √(1 + (A * w) ^ 2)
    ≤ GET_NEAREST_DISTANCE ((MAKE_RANDOM_PHASE_SINE A w).eval φ) p ∧
  GET_NEAREST_DISTANCE ((MAKE_RANDOM_PHASE_SINE A w).eval φ) p ≤ π / w
```

```lean
-- Here
let GET_GRAPH            := DRAW_SINE_CURVE amplitude frequency phase
let vertical_error   := GET_VERTICAL_ERROR GET_GRAPH data_point    -- orange line in the graph: what training sees
let nearest_distance := GET_NEAREST_DISTANCE GET_GRAPH data_point  -- blue line in the graph: what the eye sees
let slope_bound      := √(1 + (amplitude * frequency) ^ 2)     -- Pythagoras: 1 across, amplitude * frequency up (steepest slope)
let lower_bound      := vertical_error / slope_bound           -- a curve no steeper than that cannot pass any closer
let upper_bound      := PI / frequency                         -- half a wave: within it the sine passes every height
let is_above_lower_bound := lower_bound ≤ nearest_distance
let is_below_upper_bound := nearest_distance ≤ upper_bound
is_above_lower_bound ∧ is_below_upper_bound
```

The rules:

- **Names, not letters.** No single letters and no Greek. Local names are
  `snake_case`, globals are `SCREAMING_SNAKE_CASE`, and types are
  `PascalCase`, as in Python.
- **Functions are verbs.** `GET_NEAREST_DISTANCE` returns a value,
  `DRAW_SINE_CURVE` builds a curve, and `IS_IN_SINE_BAND` answers yes or no.
- **No type inside a type.** `Measure (DataPoint ℝ)` is written
  `DataDistribution`. The names are listed in
  [`Vocabulary.lean`](lean/SquigglyLine/Theorem/Vocabulary.lean).
- **Helpers live outside the theorem.** A quantity the statement needs more
  than once is a function defined above it and called where it is used.
- **One idea per line.** Each quantity gets a `let`. Each claim gets a name.
  Both sides of every "and" get a name, and the last line only combines
  names.
- **Comments say why.** A comment at the end of a line explains a number
  or a formula that would otherwise look like magic. A line that explains
  itself gets none. Code stays within 80 columns; a comment may run past.
- **Python beside the Lean.** Each statement comes with the same thing
  written as plain Python.
- **Tested.** The move to this style was checked by fingerprint: every
  theorem and definition is hashed with names, `let`s and layout ignored,
  and the hash before and after must agree
  ([`StatementFingerprint.lean`](lean/tools/StatementFingerprint.lean)). The
  headline theorem is also checked against its original text in
  [`Tests/`](lean/SquigglyLine/Tests). A misspelt name is a build error.

Every Lean file in the project is written this way. The rules are in
[`lean/STYLE.md`](lean/STYLE.md), the model file is
[`SquigglyLineTheorem.lean`](lean/SquigglyLine/Theorem/SquigglyLineTheorem.lean),
and [`lean/RENAMES.txt`](lean/RENAMES.txt) lists the old and new name of
every definition, for readers who come from the paper.

## How does this help me?

### If you are curious about AI

- **A big model does not start out knowing more.** Before training, a big
  model is exactly as wrong as a small one. This was measured and, for a
  simple model, proved.
- **It learns faster because a right answer is nearby.** A bigger model has
  to change itself less to get there. Think of a bigger toolbox. The job is
  not half done, but the right tool is within reach.
- **That closeness has a price.** A model that is one small nudge away from
  the right answer is also one small nudge away from a wrong one. This is one
  reason an AI system can be fooled by a tiny change to its input.
- **"Just big enough" is the worst size.** A model with barely enough room to
  memorise its examples does badly on new ones. A much bigger model does well
  again.
- **What this does not say.** It is about simple mathematical models of
  learning. It does not tell you what a large AI system will do, or whether
  it is safe.

The claims marked "proved" were checked line by line by a computer program
built for checking proofs, not only argued in words.

### If you train models

You already know most of this. It is the working knowledge of the field,
learned by trial and passed on by word of mouth. What this repository adds is
a short proof behind each habit, so a suspicion becomes something you can
point to.

| What practitioners do or suspect | What is proved here | Where |
|---|---|---|
| The loss at step zero is a sanity check and tells you nothing else. | The expected loss at the start depends only on the outputs one input at a time. It cannot see structure. | [section 3](#3-why-it-is-true) |
| Bigger models are easier to train. | The loss at the start is the same, but the nearest fit is closer, by `‖residual‖ / √c`. | [section 5](#5-where-the-idea-is-right) |
| Do not size the model to just fit the data. Go much bigger. | The distance to a fit is largest with just enough parameters, and so is the test error. | [double descent](docs/networks/double-descent.md) |
| Fitting noisy labels exactly is often harmless in a big model. | Spare features take over the noise and cap what it does to new inputs. | [benign overfitting](docs/supporting/new-inputs/benign-overfitting.md) |
| Go deeper, not only wider. | A layer can double the turns of the curve. A neuron in one hidden layer adds one. | [depth separation](docs/supporting/network-shape/depth-separation.md) |
| Deep networks need skip connections and normalisation. | A skip keeps any layer from dimming or blocking the signal. A normalisation restores its strength. | [skip and norm](docs/supporting/network-shape/skip-and-norm.md) |
| Change things gradually: warm up, small steps, easy examples first. | If a step's cost goes as the square of its size, `N` small steps cost `1 / N` of one big one. | [small steps](docs/supporting/training/small-steps.md) |
| Weight decay, early stopping and a bigger model all fight overfitting. | All three add a floor to the strength of every direction. Stopping after `t` steps cuts at least as hard as weight decay `1 / (step size × t)`. | [weight decay](docs/supporting/training/weight-decay.md) |
| Regularise more and you underfit, less and you overfit. | Expected squared error is bias² plus variance. Raising the floor raises the first and lowers the second. | [bias and variance](docs/supporting/new-inputs/bias-variance.md) |
| With a compute budget and data to spare, grow the model and the data together. | If the loss above its floor is `A / parameters + B / data`, the best split of a fixed budget has the two terms equal. | [compute budget](docs/supporting/training/compute-budget.md) |
| Double the batch size, double the learning rate. | Two small steps equal one big step up to a term of order `step size²`. | [batch size](docs/supporting/training/batch-size.md) |
| Start the weights so the signal keeps its size from layer to layer. | A per-layer gain below one dies with depth and above one blows up, and the gradient follows the signal. | [vanishing gradients](docs/supporting/network-shape/vanishing-gradients.md) |
| There is a largest learning rate, and sharper loss means a smaller one. | A direction is stable exactly when the step size is below `2 / sharpness`. | [edge of stability](docs/supporting/training/edge-of-stability.md) |
| Networks learn the coarse pattern first. Stopping early keeps out noise. | Each direction is learned on its own clock, `1 / (step size × strength)`, strong ones first. | [spectral bias](docs/supporting/training/spectral-bias.md) |
| Flat minima are good, but sharpness numbers are slippery. | Rescaling the weights changes the flatness and not the model. Flatter always means farther. | [flat minima](docs/supporting/training/flat-minima.md) |
| Most weights can be pruned. | Pruning costs nothing along directions where the dropped weights had no strength. | [lottery tickets](docs/supporting/new-inputs/lottery-ticket.md) |
| Fine-tune gently, or the model forgets. | What is forgotten is at most the distance moved, and it goes through inputs the model treats as alike. | [forgetting](docs/supporting/new-inputs/forgetting.md) |
| Tiny changes to an input can fool a model, and robustness costs accuracy. | Nearness to the data is bought with slope and with nothing else. | [section 3](#3-why-it-is-true), [dimpled manifold](docs/supporting/new-inputs/dimpled-manifold.md) |
| Well-trained models of different designs end up alike. | Two models with the same kernel make the same predictions at every step, whatever their weights. | [same kernel](docs/supporting/new-inputs/same-kernel.md) |

**How far to trust it.** Each proof is for a simplified model, most often one
whose features do not change during training. So it confirms the direction of
each habit. It does not give numbers for your model, and nothing here was
tested on a production system.

**Two habits it suggests adding.** Compare setups by how far the weights move
to reach a fit, `‖θ_final − θ_start‖`, since that is the quantity model size
changes. And read sharpness against the step size, as the product
`step size × sharpness`, since that is the number rescaling leaves alone.

**A rule of thumb for size.** To be clear of the double-descent peak, use at
least

```
3 × samples × (classes − 1)
```

trainable parameters, or keep weight decay on and stop worrying. The peak
sits where the model can just barely fit its training labels. That takes one
parameter for each number to be fitted (**proved** for a model linear in its
weights: [capacity](docs/supporting/network-shape/capacity.md)), and a sample with `k` classes has
`k − 1` free numbers. The factor of 3 comes from one experiment here: with 20
points the error was still bad at 1.65 times the threshold and had settled by
3.25 times ([double descent](docs/networks/double-descent.md)). So the rule is a
guide and not a theorem. It counts samples, not megabytes. With clean labels
the peak is small anyway, and the rule matters most when the labels are
noisy. It applies to the part of the model you train: a single layer on top
of a frozen network has only that layer's parameters.

This rule is for a fixed set of data. If you can always get more data and
are limited by compute, the rule is different: grow the model and the data
together ([compute budget](docs/supporting/training/compute-budget.md)). The two rules agree in
staying away from the peak, one from above and one from below.

### If you study learning

**What you can take away**

- **Say which distance.** "Closer to the data" is two different quantities.
  The distance to the nearest point of the graph and the vertical error are
  tied by slope alone: `vertical / √(1 + K²) ≤ nearest ≤ vertical`.
- **The loss at initialisation is blind to structure.** The expected loss of
  a random function depends only on its one-point marginals. Anything about
  how the function varies between inputs needs a two-point object: a kernel,
  or a distance in parameter space.
- **Overparameterisation pays in travel, not in initial loss.** With
  orthogonal features of strength `c`, the distance to the nearest fit is
  exactly `‖residual‖ / √c`.
- **A new quantity to compute.** The oscillation scale `ρ` of a function is
  enough for nearness (`nearest ≤ ρ`) and for an exact fit after moving each
  input by at most `ρ`. Its value for a network with random weights is open.
- **Statements you can build on.** Every result is a Lean theorem with its
  assumptions written out ([section 7](#7-the-proofs)).

**What is settled**

- Why the original picture looks right and tests wrong: the geometry holds, and
  the loss cannot see it.
- Why double descent peaks at the interpolation threshold, for a model linear
  in its weights: that is where the nearest fit is farthest away, exactly
  `‖residual‖ / √λ` along a direction of strength `λ`.
- For a fixed kernel, several separate observations come from one factor,
  `1 − ηλ` per step: [spectral bias](docs/supporting/training/spectral-bias.md), the threshold
  `2 / η` at the [edge of stability](docs/supporting/training/edge-of-stability.md), and the long
  wait before a weak direction is learned.
- For a fixed kernel, kernels add when features are put side by side, which
  gives what [pruning](docs/supporting/new-inputs/lottery-ticket.md) costs and when
  [overfitting is harmless](docs/supporting/new-inputs/benign-overfitting.md).

**What is not settled.** Every one of these for a network whose kernel moves
during training, and the size of `ρ` for random weights. See
[open questions](#open-questions).

## 1. The idea

Scatter random points on a plane. Draw two curves without looking at the
points: one smooth, one squiggly. The squiggly one passes closer to the points
on average, because it visits more of the plane.

A network computes a function, and the graph of that function is such a curve.
The original conjecture said:

> A network with more parameters draws a squigglier curve before training. So
> it starts closer to its data. So it learns faster.

That is three claims in a chain. Each can be tested on its own.

## 2. The theorem

Take any function, of any number of inputs, and squeeze it sideways by a
factor `w`, so that every wiggle is `w` times narrower. Then:

1. **Closer.** If the function reached every label within a distance `ρ` of
   every input, the squeezed one is within `ρ / w` of every data point.
2. **Steeper.** Its slope is `w` times larger, and its distance to a data point
   is at least `vertical / √(1 + (w·K)²)`.
3. **No better at the start.** If the function is random, with the same
   distribution of outputs at every input, squeezing it leaves the expected
   loss unchanged, for every regression loss.
4. **A small shift cashes it in.** Any target is fitted exactly after moving
   each input by at most `ρ / w`.

So the nearness is real, and training can use it by moving the input. It is a
distance to move. It is not a lower loss at the start, and its price is slope.

This is `squiggly_line_theorem_general` in
[`lean/SquigglyLine/Theorem/Compression.lean`](lean/SquigglyLine/Theorem/Compression.lean). A
sine with a random phase is the standard example (`squiggly_line_theorem`, with
`ρ / w = π / w`). Plain-language accounts:
[`docs/theorem/general-theorem.md`](docs/theorem/general-theorem.md) and
[`docs/theorem/phase-matching.md`](docs/theorem/phase-matching.md).

## 3. Why it is true

The picture measures the distance from a data point to the nearest point of
the curve, in any direction. Training measures the vertical error
`|y − f(x)|`. These are different, and three short results say how.

**The slope sandwich.** If `f` has slope at most `K`, then at every data point

```
vertical / √(1 + K²)  ≤  nearest  ≤  vertical
```

A curve can be much nearer than its vertical error only if it is steep.
Squiggliness buys nearness with slope and with nothing else.

**The oscillation scale.** Say `f` covers the labels within `ρ` when, near
every input, some input at most `ρ` away is sent to any label you ask for.
Then `nearest ≤ ρ` at every data point. Squeezing by `w` divides `ρ` by `w`.
That is the "closer" half, and the same fact gives the small shift.

**The marginal lemma.** The expected loss of a random function depends only on
the distribution of `f(x)` at each single `x`. How `f` moves between two
inputs, which is what "squiggly" means, does not enter. So no measurement of
the loss at the start can detect squiggliness.

## 4. What it does to the idea

| # | Claim | Verdict |
|---|---|---|
| 1 | **Geometry.** A squigglier curve has a smaller distance to the nearest point of the curve. | True. Proved for any squeezed function, with a rate. |
| 2 | **Parameters.** More parameters give a squigglier random function. | Mixed. True for depth by construction. Not for width with random weights. |
| 3 | **Learning.** A smaller nearest-point distance means a smaller loss at the start. | False. Proved. |

**For networks.** Depth can buy squiggliness. `L` layers of two ReLU neurons
fold the line `L` times and draw a curve that passes within `1 / 2^L` of every
point of the unit square (`nearestDist_iterate_tent_le`). A network with one
neuron per layer never turns at all, and a network with one hidden layer needs
`2^L` neurons to follow what `2(L + 1)` neurons do in depth. Width with random
weights does not buy it: the loss at the start is the same at every width,
and the curve is no longer (see [the evidence](#6-the-evidence)).

What is still open is how squiggly a network with **random** weights is as it
grows. [`docs/open-problems.md`](docs/open-problems.md) says what that reduces
to. The pictures used for networks, a wind tunnel and a stack of polarizers,
are in [`docs/networks/wind-tunnel-and-polarizers.md`](docs/networks/wind-tunnel-and-polarizers.md)
and [`docs/networks/three-polarizers.md`](docs/networks/three-polarizers.md).

## 5. Where the idea is right

The theorem says nearness is a distance to move. In parameter space that
distance can be measured, and there the original idea holds.

[`scripts/fourier_params.py`](scripts/fourier_params.py) uses a family where
the number of parameters is the only dial: a Fourier series with random
coefficients, scaled so the output has the same variance at every size. There
are 20 points with random labels.

In the terms of statistics this is a generalized linear model in its plainest
case: fixed features (the sines and cosines), no link function, and squared
error. That is linear regression. Every proof in this section uses that the
output is linear in the parameters.

| parameters | loss at start | travel to a fit | gradient-descent steps |
|---|---|---|---|
| 9 | 0.65 | no fit | never |
| 21 | 0.65 | 448 | 188 000 000 |
| 25 | 0.64 | 35.5 | 79 300 |
| 65 | 0.71 | 1.61 | 166 |
| 129 | 0.66 | 0.48 | 13 |
| 513 | 0.63 | 0.23 | 3 |

"Travel" is the distance in parameter space from the random start to the
nearest parameters that fit every point. A bigger model does not start with a
lower loss. It starts nearer to a fit, and it trains in far fewer steps. This
is the known lazy-training picture, not a new result.

**The exchange rate.** When the features are orthogonal on the data side with
squared length `c`, the travel is exactly `‖residual‖ / √c`
(`ExchangeRate.lean`). For the Fourier model `c` is about the number of
parameters, which predicts 0.45, 0.32 and 0.22 for 129, 257 and 513
parameters, against 0.48, 0.34 and 0.23 measured. Loss and distance are one
quantity at an exchange rate that grows like the root of the parameter count.

**Double descent is the far side of the same fact.** Fit the same model to
noisy points and score it on fresh ones
([`scripts/double_descent.py`](scripts/double_descent.py)).

| parameters | test error | travel to the fit |
|---|---|---|
| 5 | 0.094 | 0.75 |
| 21 | 83 800 | 409 |
| 65 | 0.31 | 0.56 |
| 513 | 0.31 | 0.17 |

![Test error and travel against the number of parameters. Both peak where the model has as many parameters as training points.](graphs/double_descent.png)

The test error and the travel peak at the same place: where the model has just
enough parameters to fit. Along a direction of the labels where the model has
strength `λ`, no fit exists if `λ = 0`, and the travel is exactly the size of
that part divided by `√λ` if `λ > 0` (`DoubleDescent.lean`). Unable to fit the
noise is safe, barely able is the worst case, and easily able is safe again.
That the test error peaks there is measured, not proved. More in
[`docs/networks/fourier-parameters.md`](docs/networks/fourier-parameters.md) and
[`docs/networks/double-descent.md`](docs/networks/double-descent.md).

## 6. The evidence

**Frequency, with everything else held fixed.**
[`scripts/frequency_isolation.py`](scripts/frequency_isolation.py) uses sines
of one amplitude and a random phase. Only the frequency changes.

| frequency | arc length | nearest-point distance | vertical error |
|---|---|---|---|
| 0.25 | 2.19 | 0.6129 | 0.6672 |
| 1 | 3.96 | 0.3095 | 0.6649 |
| 4 | 13.32 | 0.0928 | 0.6663 |
| 16 | 52.31 | 0.0338 | 0.6665 |
| 64 | 208.92 | 0.0207 | 0.6688 |

![Mean nearest-point distance and mean vertical error against frequency. The nearest-point distance falls 30 times and stays above the lower bound of the slope sandwich. The vertical error is flat.](graphs/readme_frequency.png)

The nearest-point distance falls by a factor of 30. The vertical error does not
move. The distance stops falling at 0.0169 only because this sine sweeps the
band `|y| ≤ 0.816` and some points lie outside it. With an amplitude that
covers the data there is no floor, and the distance follows
`0.2974 / frequency` ([`scripts/saturation_scaling.py`](scripts/saturation_scaling.py);
the constant is `(2 − 8/π²) / 4`, derived in `docs/RESOLUTION.md` §6).

![Nearest-point distance against frequency for two amplitudes. With the narrow band the curve levels off at the floor. With the band that covers the data it keeps falling along the closed form.](graphs/readme_floor.png)

**Length alone is not enough.** A straight line as long as the frequency-64
sine has a nearest-point distance of 0.50, against 0.02 for the sine. About 99%
of that line lies above or below the data. Length inside the data region is
needed. Length outside it is worth nothing.

**Random networks.** [`scripts/initial_mse.py`](scripts/initial_mse.py): 10
inputs, 200 points, two hidden layers, 200 untrained ReLU networks per width.

| width | 4 | 16 | 64 | 256 | 1024 |
|---|---|---|---|---|---|
| He initialisation, measured | 1.07 | 1.02 | 1.07 | 1.10 | 1.03 |
| He initialisation, predicted | 1.03 | 1.03 | 1.03 | 1.03 | 1.03 |
| Unscaled weights, measured | 15 | 220 | 3 450 | 60 200 | 823 000 |

![Initial MSE of untrained ReLU networks at five widths. Every width sits on the predicted value.](graphs/readme_initial_mse.png)

A wider network does not start closer. With unscaled weights it starts much
further away, because the output grows with width. For a 1-D input, width does
not add arc length (3.4 to 3.6 from width 2 to 512) and depth adds some (3.4
to 5.1 from 1 to 16 layers;
[`scripts/random_relu_length.py`](scripts/random_relu_length.py)).

## 7. The proofs

[`lean/`](lean) is a Lean 4 project on Mathlib. There is no `sorry`, and each
theorem depends only on Lean's three standard axioms. The files are in one
folder for each group below, and the notes in [`docs/`](docs) are grouped the
same way.

The Lean code is written to be read: readable, pythonic and "enterprise
grade". [The style philosophy](#the-style-philosophy-readable-pythonic-enterprise_grade) is set
out near the top. In every file it means:

- every file opens with a summary in plain words that lists its theorems;
- names say what a thing is (`GET_TRAVEL`, `GET_RESIDUAL`, `GET_NEAREST_DISTANCE`,
  `perceptron_mistake_bound`), and every main theorem has a one-line
  statement in plain words above it;
- a definition is written once and reused, so later files build on earlier
  ones and repeat nothing;
- proofs are short, and each named step says what it establishes;
- every push is built from scratch by CI, which fails on any `sorry`.

You should be able to open a file and follow what is claimed without knowing
Lean.

**The theorem.** Proofs in
[`lean/SquigglyLine/Theorem/`](lean/SquigglyLine/Theorem), notes in
[`docs/theorem/`](docs/theorem).

| File | What it proves |
|---|---|
| [`SquigglyLineTheorem`](lean/SquigglyLine/Theorem/SquigglyLineTheorem.lean) | **the theorem for sines**, as one statement of four claims: the distance is squeezed between `vertical / √(1 + (A·w)²)` and `π / w`, it goes to zero, the loss does not depend on the frequency, and a small shift of the input fits any target in the band |
| [`Vocabulary`](lean/SquigglyLine/Theorem/Vocabulary.lean) | nothing: the readable names used in restyled statements, each a second name for something defined elsewhere |
| [`Defs`](lean/SquigglyLine/Theorem/Defs.lean), [`RandomFunction`](lean/SquigglyLine/Theorem/RandomFunction.lean), [`Conjecture`](lean/SquigglyLine/Theorem/Conjecture.lean) | definitions: the curve, the data, the two costs, a randomly initialised model, and the original conjecture as a statement |
| [`Sandwich`](lean/SquigglyLine/Theorem/Sandwich.lean) | `vertical / √(1 + K²) ≤ nearest ≤ vertical` |
| [`Marginal`](lean/SquigglyLine/Theorem/Marginal.lean) | a regression loss sees only one-point marginals |
| [`Coverage`](lean/SquigglyLine/Theorem/Coverage.lean) | the mean distance to a set is its uncovered mass, integrated over the radius |
| [`Oscillation`](lean/SquigglyLine/Theorem/Oscillation.lean) | `nearest ≤ ρ` when `f` covers the labels within `ρ`; any target in range is fitted after moving each input by at most `ρ` |
| [`RandomPhase`](lean/SquigglyLine/Theorem/RandomPhase.lean), [`SineCloser`](lean/SquigglyLine/Theorem/SineCloser.lean), [`Verdict`](lean/SquigglyLine/Theorem/Verdict.lean) | the sine case, lemma by lemma: `vertical / √(1 + (A·w)²) ≤ nearest ≤ π / w`, the loss does not depend on the frequency, and so the learning claim fails |
| [`Compression`](lean/SquigglyLine/Theorem/Compression.lean) | **the theorem for any function**: squeezing by `w` divides the oscillation scale by `w`, multiplies the slope by `w`, and leaves the expected loss unchanged |

[`Tests/StatementsUnchanged`](lean/SquigglyLine/Tests/StatementsUnchanged.lean)
checks that each restyled statement says what its original said.

**Networks and parameter space.** Proofs in
[`lean/SquigglyLine/Networks/`](lean/SquigglyLine/Networks), notes in
[`docs/networks/`](docs/networks).

| File | What it proves |
|---|---|
| [`NarrowChain`](lean/SquigglyLine/Networks/NarrowChain.lean) | a ReLU network with one neuron per layer never turns, at any depth |
| [`Depth`](lean/SquigglyLine/Networks/Depth.lean), [`TentCloser`](lean/SquigglyLine/Networks/TentCloser.lean) | `L` layers of two neurons make `2^L` straight pieces and pass within `1 / 2^L` of every point of the unit square |
| [`Bridge`](lean/SquigglyLine/Networks/Bridge.lean) | one fold doubles a frequency, so `L` folds seen through a fixed lens are one Fourier term of frequency `2^L` |
| [`Polarizer`](lean/SquigglyLine/Networks/Polarizer.lean), [`ThreePolarizers`](lean/SquigglyLine/Networks/ThreePolarizers.lean) | ReLU sends a point to the nearest point of the positive quadrant; Malus's law; a quarter turn in `N` plates delivers at least `1 − π²/(8N)` |
| [`MarkovChains`](lean/SquigglyLine/Networks/MarkovChains.lean) | through the layers: merged stays merged, dead stays dead; through training with orthogonal features: the error after `t` steps is `(1 − η·c)ᵗ` times the start |
| [`LinearModel`](lean/SquigglyLine/Networks/LinearModel.lean), [`ExchangeRate`](lean/SquigglyLine/Networks/ExchangeRate.lean) | on the straight path to a fit the error shrinks in proportion; adding parameters never moves the nearest fit away; with orthogonal features the travel is `‖residual‖ / √c` |
| [`Kernel`](lean/SquigglyLine/Networks/Kernel.lean) | a gradient step sends the error `r` to `r − η·K·r`; two models with the same kernel have the same training path and the same travel |
| [`DoubleDescent`](lean/SquigglyLine/Networks/DoubleDescent.lean) | a fit near the start is tame everywhere; along a direction of strength `λ` the travel is exactly `‖residual‖ / √λ` |
| [`Lift`](lean/SquigglyLine/Networks/Lift.lean) | a model linear in its weights is a flat plane seen through a lift: a point is on the squiggly line exactly when its lift is on the plane; the slope is at most the size of the weights times the stretch of the lift; weights moved along the lifted data predict through the kernel alone ([note](docs/networks/kernel-trick.md)) |
| [`FourierLift`](lean/SquigglyLine/Networks/FourierLift.lean) | winding the input round a circle at frequency `w` stretches distances by at most `w`, so a wave is no steeper than its weights times its frequency; the kernel is `cos(w(x − x′))`, which sees only the gap, so shifting data and question together changes no answer ([note](docs/networks/fourier-lift.md)) |
| [`RadialBasis`](lean/SquigglyLine/Networks/RadialBasis.lean) | a Gaussian bump of width `σ` is the unit bump squeezed by `1 / σ`, so it has slope at most `1 / σ`; a network of bumps is no steeper than its heights over its width, is a flat model on the lift by bumps, and fits any labels once the bumps hardly overlap |

**Not formalised:** the constant `0.2974` for sines, the length bound
`V / (4·l)`, the rate at which travel falls with parameter count, that the
test error peaks at the threshold, and every statement about networks with
random weights.

To build (the first build downloads Mathlib):

```bash
cd lean
lake exe cache get
lake build
```

`lake build` passes with Lean 4.36.0-rc1 and the Mathlib commit pinned in
[`lean/lake-manifest.json`](lean/lake-manifest.json).

## A network made of polarizers

This idea fell out of the picture used for networks. It is not part of the
theorem, and nothing has been built or simulated.

**The picture.** A dense layer does two things: it turns its input, then it
keeps part of it. A polarizer plate turns nothing itself, but it keeps only
the part of the light that lines up with its axis, and the angle of the axis
decides which part. Light after a plate at angle `θ` to it keeps `cos θ` of
its length. That is a layer whose weight is an angle. A stack of plates is a
stack of layers, and the light computes the answer on its way through, at the
speed of light and with no power spent on the plates.

**What is proved here.** Only the arithmetic, not the hardware.

- A plate is a projection, and Malus's law follows (`malus` in
  [`ThreePolarizers`](lean/SquigglyLine/Networks/ThreePolarizers.lean)). In the plane,
  ReLU is also a projection, onto a quadrant where the plate's is onto a line
  (`relu2_nearest` in [`Polarizer`](lean/SquigglyLine/Networks/Polarizer.lean)).
- Depth is affordable. A quarter turn spread over `N` plates loses at most
  `π² / (8N)` of the light (`quarter_turn_arrives`), and any turn `φ` loses at
  most `φ² / (2N)` once each step is small (`turn_in_steps_keeps`).
- The two tricks of deep networks have optical parts. A skip connection is a
  beam that goes around the plate and rejoins. A normalisation is an amplifier
  after it ([`SkipAndNorm`](lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean)).

**What is missing.** The nonlinearity. A stack of polarizers is one linear
map, however many plates it has, so on its own it is a network with no
activation function. Two partial ways around it:

- A detector reads brightness, which is the square of the length. That is one
  nonlinear step, at the end only.
- Store a value as the angle of the light. What passes a plate then goes as
  `cos²` of the stored value, which is nonlinear in it. One layer works.
  Chaining layers needs something that turns brightness back into an angle.

Also, polarization has two dimensions, so one beam is a layer of width two.
More width needs more beams.

**What already exists.** Optical neural networks are not new. Layers have been
built from printed diffracting plates and from meshes of interferometers
(recalled: Lin et al. 2018; Shen et al. 2017). What this adds is the reading
of a weight as the angle of a plate, with the loss worked out. I have not
checked whether that reading is in the literature.

More in [`docs/networks/wind-tunnel-and-polarizers.md`](docs/networks/wind-tunnel-and-polarizers.md)
and [`docs/networks/three-polarizers.md`](docs/networks/three-polarizers.md). The open question
is item 18 of [`docs/open-problems.md`](docs/open-problems.md): what can a
network whose activation is a polarizer compute?

## 8. Supporting material

Nothing in this section is needed for the theorem. It is the same handful of
tools (slope, nearness, travel and the kernel) pointed at puzzles that are
already known in deep learning. Each row is a statement about a simplified
model, most often one that is linear in its weights, with a plain-language
note and a Lean proof. Each note also says what it does **not** show. None of
them proves the phenomenon for real networks.

**How training moves.** Proofs in
[`lean/SquigglyLine/Supporting/Training/`](lean/SquigglyLine/Supporting/Training), notes in
[`docs/supporting/training/`](docs/supporting/training).

| Topic | What is shown | Note | Proof |
|---|---|---|---|
| Least action | Gradient descent moves only along the features, so any fit it reaches is the nearest one. | [note](docs/supporting/training/least-action.md) | [`LeastAction`](lean/SquigglyLine/Supporting/Training/LeastAction.lean) |
| Spectral bias | The error along a direction of strength `λ` shrinks by `1 − ηλ` per step. Strong directions are learned first. | [note](docs/supporting/training/spectral-bias.md) | [`SpectralBias`](lean/SquigglyLine/Supporting/Training/SpectralBias.lean) |
| Edge of stability | That error shrinks when `ηλ < 2`, holds its size at `ηλ = 2`, and grows past it. | [note](docs/supporting/training/edge-of-stability.md) | [`EdgeOfStability`](lean/SquigglyLine/Supporting/Training/EdgeOfStability.lean) |
| Flat minima | Rescaling the parameters by `c` keeps every output, makes the loss flatter by `c²` and the fit farther by `\|c\|`. | [note](docs/supporting/training/flat-minima.md) | [`Reparam`](lean/SquigglyLine/Supporting/Training/Reparam.lean) |
| Many small steps | A square-law loss over `N` steps is at most `c·D² / N`. A loss in proportion to the step gains nothing. | [note](docs/supporting/training/small-steps.md) | [`SmallSteps`](lean/SquigglyLine/Supporting/Training/SmallSteps.lean) |
| Weight decay and early stopping | Weight decay `μ` leaves the share `μ / (λ + μ)` of the error. Stopping after `t` steps cuts at least as hard as `μ = 1 / (ηt)`. Spare features act the same way. | [note](docs/supporting/training/weight-decay.md) | [`WeightDecay`](lean/SquigglyLine/Supporting/Training/WeightDecay.lean) |
| Batch size and learning rate | Two steps on two batches equal one step on both, minus `η²` times a term through the kernel between the batches. With averaged gradients that is the linear scaling rule. | [note](docs/supporting/training/batch-size.md) | [`BatchSize`](lean/SquigglyLine/Supporting/Training/BatchSize.lean) |
| Chinchilla scaling | If the loss above its floor is `A / N + B / D` and compute fixes `N × D`, the best split has the two terms equal, so parameters and data grow together in the ratio `A / B`. The form itself is a measurement. | [note](docs/supporting/training/compute-budget.md) | [`ComputeBudget`](lean/SquigglyLine/Supporting/Training/ComputeBudget.lean) |
| Softmax and cross-entropy | The loss pushes each score by prediction minus label, the same form as squared error. So a classifier moves through the same kernel, travels least, and has no hill between two settings. For a yes-or-no label no finite score is best. | [note](docs/supporting/training/cross-entropy.md) | [`CrossEntropy`](lean/SquigglyLine/Supporting/Training/CrossEntropy.lean) |
| Dropout | With independent masks of variance `v`, the expected squared error is the plain squared error plus `v` times the squared shares "feature times weight". Over the data that is weight decay with a rate per feature, and plain weight decay when the features are equally large. | [note](docs/supporting/training/dropout.md) | [`Dropout`](lean/SquigglyLine/Supporting/Training/Dropout.lean) |
| Perceptron, XOR, no free lunch | The margin is the distance from the data to the boundary, and the perceptron makes at most `(R / γ)²` mistakes. No flat boundary splits XOR; one lifted feature or one fold does. With no pattern in the labels, any guess at an unseen input is right on half of all labellings, and the flat line is best. | [note](docs/supporting/training/perceptron.md) | [`Perceptron`](lean/SquigglyLine/Supporting/Training/Perceptron.lean) |
| Normalisation, deep linear networks, relabelling units | If rescaling the weights leaves the loss alone, the gradient is at right angles to them and every step makes them longer. For two weights multiplied, a step changes `a² − b²` only at second order, so the layers share the slope. Shuffling hidden units gives the same function. | [note](docs/supporting/training/symmetry.md) | [`Symmetry`](lean/SquigglyLine/Supporting/Training/Symmetry.lean) |
| Adam, clipping, low-rank training, quantisation | Adam with no memory steps by the sign of the gradient, so a gap closes by `η` per step whatever the strength of the direction. Clipping caps travel at `t·η·c`. Confining the weights to a subspace never shortens the trip to a fit. Rounding the weights by `δ` moves an output by at most `‖δ‖` times the size of the features. | [note](docs/supporting/training/step-rules.md) | [`StepRules`](lean/SquigglyLine/Supporting/Training/StepRules.lean) |

**What a fit does to new inputs.** Proofs in
[`lean/SquigglyLine/Supporting/NewInputs/`](lean/SquigglyLine/Supporting/NewInputs), notes in
[`docs/supporting/new-inputs/`](docs/supporting/new-inputs).

| Topic | What is shown | Note | Proof |
|---|---|---|---|
| Same kernel, same predictions | Two models with the same kernel give the same answer at a test point after every step, whatever their weights. | [note](docs/supporting/new-inputs/same-kernel.md) | [`SameKernel`](lean/SquigglyLine/Supporting/NewInputs/SameKernel.lean) |
| Benign overfitting | The nearest fit swallows the noise. With junk features of strength `c'` the damage at a new input is capped by `1 / c'`. | [note](docs/supporting/new-inputs/benign-overfitting.md) | [`BenignOverfitting`](lean/SquigglyLine/Supporting/NewInputs/BenignOverfitting.lean) |
| Bias and variance | With noise that is zero on average, the expected squared error at a new input is bias² plus variance. A floor `μ` on every direction raises the first and lowers the second. | [note](docs/supporting/new-inputs/bias-variance.md) | [`BiasVariance`](lean/SquigglyLine/Supporting/NewInputs/BiasVariance.lean) |
| Catastrophic forgetting | A step on a new task changes the old errors through the cross kernel only, and by at most the new task's travel. | [note](docs/supporting/new-inputs/forgetting.md) | [`Forgetting`](lean/SquigglyLine/Supporting/NewInputs/Forgetting.lean) |
| Lottery tickets | Pruning subtracts a kernel: slower and farther. It costs nothing where the dropped weights had no strength. | [note](docs/supporting/new-inputs/lottery-ticket.md) | [`Pruning`](lean/SquigglyLine/Supporting/NewInputs/Pruning.lean) |
| Dimpled manifold | A function can keep its loss on real data and still be one small step from any label, straight off the data manifold. | [note](docs/supporting/new-inputs/dimpled-manifold.md) | [`Dimple`](lean/SquigglyLine/Supporting/NewInputs/Dimple.lean) |
| Ensembles, weight averaging, diffusion | The squared error of an average is the average error minus the spread of its members, and the average is no steeper than the steepest member. For a model linear in its weights, averaging weights is averaging lines. The ideal denoiser is an attention head over the training examples, so it never leaves the region they span. | [note](docs/supporting/new-inputs/averaging.md) | [`Averaging`](lean/SquigglyLine/Supporting/NewInputs/Averaging.lean) |

**The shape of a network.** Proofs in
[`lean/SquigglyLine/Supporting/NetworkShape/`](lean/SquigglyLine/Supporting/NetworkShape), notes in
[`docs/supporting/network-shape/`](docs/supporting/network-shape).

| Topic | What is shown | Note | Proof |
|---|---|---|---|
| Depth separation | A network with one hidden layer needs `2^L` units to stay within one half of `L + 1` tent layers. | [note](docs/supporting/network-shape/depth-separation.md) | [`DepthSeparation`](lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean) |
| Universal approximation | A one-hidden-layer ReLU network with `2n` units is within `2K / n` of any function on `[0, 1]` with slope at most `K`. The cost in units goes as slope over error. | [note](docs/supporting/network-shape/universal-approximation.md) | [`UniversalApproximation`](lean/SquigglyLine/Supporting/NetworkShape/UniversalApproximation.lean) |
| Storage capacity | A model linear in `m` weights fits arbitrary labels on at most `m` points. A network with `b` bits of weights memorises every labelling of at most `b` inputs. Depth buys pattern, not storage. | [note](docs/supporting/network-shape/capacity.md) | [`Capacity`](lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean) |
| Skip connections and normalisation | As optics: a skip is a bypass that never dims or blocks; a normalisation is an amplifier that restores full strength. | [note](docs/supporting/network-shape/skip-and-norm.md) | [`SkipAndNorm`](lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean) |
| Vanishing and exploding gradients | A per-layer gain `g` gives `g^L`: it dies below one and blows up above. The gradient comes back through the same plates, so it is dimmed the same way. | [note](docs/supporting/network-shape/vanishing-gradients.md) | [`VanishingGradients`](lean/SquigglyLine/Supporting/NetworkShape/VanishingGradients.lean) |
| Information bottleneck | After any layer of a network that is right on every input: labels ≤ places occupied ≤ inputs. | [note](docs/supporting/network-shape/information-bottleneck.md) | [`Bottleneck`](lean/SquigglyLine/Supporting/NetworkShape/Bottleneck.lean) |
| Compression | A fold throws away one bit, so `L` folds merge at most `2^L` inputs. The average log-loss of any model, and the average length of any code, is at least the entropy. With description length as squared travel, gradient descent finds the fit that is cheapest to describe. | [note](docs/supporting/network-shape/code-length.md) | [`CodeLength`](lean/SquigglyLine/Supporting/NetworkShape/CodeLength.lean) |
| Neural collapse | `K` unit vectors cannot all be farther apart than a simplex, and the simplex is the centred arrangement. | [note](docs/supporting/network-shape/neural-collapse.md) | [`NeuralCollapse`](lean/SquigglyLine/Supporting/NetworkShape/NeuralCollapse.lean) |
| Mode connectivity | Linear in the weights: no hill between two fits. Two weights multiplied: the hill is exactly `t(1 − t)(a₁ − a₂)(b₁ − b₂)`. | [note](docs/supporting/network-shape/mode-connectivity.md) | [`ModeConnectivity`](lean/SquigglyLine/Supporting/NetworkShape/ModeConnectivity.lean) |
| Attention and in-context learning | An attention head is a weighted average, so any stack of them keeps every token inside the region the tokens started in. One head without the softmax, reading examples as tokens, gives the prediction of one step of gradient descent on those examples. | [note](docs/supporting/network-shape/attention.md) | [`Attention`](lean/SquigglyLine/Supporting/NetworkShape/Attention.lean) |
| Signed distance functions | The theorem's distance is the distance field of the line, read at the data. The field never changes faster than one, however steep the line. A step shorter than the field cannot reach the line. The height above the line overstates the signed distance by at most `√(1 + K²)`. | [note](docs/supporting/network-shape/signed-distance.md) | [`SignedDistance`](lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean) |
| Slope of a network, adversarial examples, temperature | A network is no steeper than the product of its layers, and the gradient comes back through the same product. Flipping a classifier of slope `K` takes a move of at least `score / K`. Temperature changes the slope of the scores and never their order. A critic of slope one reports at most the distance. | [note](docs/supporting/network-shape/network-slope.md) | [`NetworkSlope`](lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean) |
| He initialisation, the Bellman update | A fold keeps exactly half the mean squared size of a signal that is as often negative as positive, which is the factor two in He initialisation. One sweep of value updates has slope at most the discount `γ`, so `n` sweeps bring any two guesses within `γ^n`. | [note](docs/supporting/network-shape/gain.md) | [`Gain`](lean/SquigglyLine/Supporting/NetworkShape/Gain.lean) |
| The eikonal equation | Walking straight to a nearest point of the line, the distance field falls by exactly the distance walked. So the slope limit of one cannot be improved, whatever the line. | [note](docs/supporting/network-shape/signed-distance.md) | [`Eikonal`](lean/SquigglyLine/Supporting/NetworkShape/Eikonal.lean) |
| The GAN game | At one input the critic's loss is a cross-entropy whose label is the share of real data there. Where real and made data overlap, the best critic predicts that share; where they do not, no score is best and the critic is asked to be steeper forever. For the payoff `x * y`, each simultaneous step multiplies the squared distance from the resting point by `1 + η²`. | [note](docs/supporting/training/gan-game.md) | [`GanGame`](lean/SquigglyLine/Supporting/Training/GanGame.lean) |
| AdamW | Weight decay put inside Adam's rescaling moves every weight by the same amount `η`, whatever the strength of the decay, and making the loss larger makes the decay weaker. Applied outside the rescaling it shrinks every weight by `1 − η μ` a step, as plain weight decay does. | [note](docs/supporting/training/step-rules.md) | [`AdamW`](lean/SquigglyLine/Supporting/Training/AdamW.lean) |
| RMSNorm and pre-norm | Dividing by the root mean square forgets the scale, so a loss read through it is scale invariant and its gradient is at right angles to the weights. A pre-norm branch adds the same whatever the size of the stream; a post-norm block always outputs root mean square one. | [note](docs/supporting/training/symmetry.md) | [`RmsNorm`](lean/SquigglyLine/Supporting/NetworkShape/RmsNorm.lean) |
| Attention loses rank with depth | With scores at most `B` in size, every token gets a share of at least `exp(−2B) / n`, so one layer of attention alone shrinks the spread of the tokens by `1 − exp(−2B)` and `L` layers by that to the power `L`. | [note](docs/supporting/network-shape/attention.md) | [`AttentionRate`](lean/SquigglyLine/Supporting/NetworkShape/AttentionRate.lean) |
| Kolmogorov–Arnold networks | A node that adds one learnable curve per input is within `2 × total slope / n` of a ReLU layer with `n` pieces per edge. | [note](docs/supporting/network-shape/universal-approximation.md) | [`KolmogorovArnold`](lean/SquigglyLine/Supporting/NetworkShape/KolmogorovArnold.lean) |

**Known results that are here under another name**

| Usual name | Where it is |
|---|---|
| Neural tangent kernel, lazy training | The fixed-kernel setting of most rows above. [`Kernel`](lean/SquigglyLine/Networks/Kernel.lean) is the statement that training sees only the kernel. |
| Implicit bias of gradient descent | It reaches the nearest fit: `gradientDescent_fit_is_nearest` in [`LeastAction`](lean/SquigglyLine/Supporting/Training/LeastAction.lean). |
| Robustness against accuracy | The slope sandwich of [section 3](#3-why-it-is-true), and the [dimpled manifold](docs/supporting/new-inputs/dimpled-manifold.md). |
| Memorising random labels | The travel table of [section 5](#5-where-the-idea-is-right) uses random labels, and [benign overfitting](docs/supporting/new-inputs/benign-overfitting.md) says when that is harmless. |
| Kernel trick, support vector machines | A squiggly line or boundary is a flat plane after a lift, and prediction needs only the kernel: [`Lift`](lean/SquigglyLine/Networks/Lift.lean), [note](docs/networks/kernel-trick.md). |
| Random Fourier features | The model of [section 5](#5-where-the-idea-is-right). |
| Dying ReLU | "Dead stays dead" in [`MarkovChains`](lean/SquigglyLine/Networks/MarkovChains.lean). |
| Grokking, and double descent over training time | Argued from the clocks in [spectral bias](docs/supporting/training/spectral-bias.md). Not proved. |

Two more notes give the pictures behind these:
[`docs/networks/fourier-and-relu-bridge.md`](docs/networks/fourier-and-relu-bridge.md) (why the
Fourier model and the ReLU model are the same learner) and
[`docs/networks/chain-of-markov-chains.md`](docs/networks/chain-of-markov-chains.md) (training
as a chain through the layers inside a chain through the steps).

## Running the experiments

```bash
pip install -r requirements.txt
cd scripts

python frequency_isolation.py    # the main experiment, ~10 s
python saturation_scaling.py     # what sets the floor, several minutes
python initial_mse.py            # random networks at five widths, ~1 min
python fourier_params.py         # what adding parameters changes, ~1 min
python double_descent.py         # test error and travel against model size, ~1 min
python random_relu_length.py     # arc length of random ReLU curves
python audit_legacy_metrics.py   # reproduces the defects listed below
python readme_figures.py         # redraws the figures on this page, ~2 min
```

## Repository layout

| Path | Contents |
|---|---|
| `lean/SquigglyLine/Theorem/` | the proof of the theorem |
| `lean/SquigglyLine/Tests/` | checks that each restyled statement says what its original said |
| `lean/STYLE.md` | how every statement is written |
| `lean/SquigglyLine/Style.lean` | the proof step `unfold_named_pieces`, and the names `RealFunction` and `PI` |
| `lean/tools/StatementFingerprint.lean` | the check that a restyle changed no statement |
| `lean/RENAMES.txt` | old and new names of the definitions |
| `lean/SquigglyLine/Networks/` | the proofs for networks and parameter space |
| `lean/SquigglyLine/Supporting/` | the proofs of the supporting material, in `Training/`, `NewInputs/` and `NetworkShape/` |
| `paper/` | a NeurIPS-format draft of the paper |
| `docs/RESOLUTION.md` | the findings in full |
| `docs/theorem/` | the theorem in plain words |
| `docs/networks/` | the pictures used for networks; parameter space, travel and double descent |
| `docs/supporting/` | the notes for the supporting material, in `training/`, `new-inputs/` and `network-shape/` |
| `docs/open-problems.md` | what this repository leaves open, each item marked open, known but not formalised, or measured |
| `docs/EXPERIMENT_LOG.md`, `docs/literature-survey.md` | a re-run of every script with raw output; related work |
| `scripts/curves.py` | shared sine-curve geometry, with an exact point-to-curve distance |
| `scripts/` (experiments) | the scripts listed above |
| `scripts/` (other) | the first exploratory code, kept as a record |
| `graphs/` | figures |
| `handoff.md` | open experiments, with a prediction and a stop rule for each |

## What went wrong the first time

The first scripts appeared to support the idea. Three of their
measurements were not what they claimed to be.
[`scripts/audit_legacy_metrics.py`](scripts/audit_legacy_metrics.py) reproduces
each one.

1. **The "distance" was a neuron count.** `utils.measure_coverage` compared the
   label with the number of active neurons, about half the width.
2. **The scaling law was the output fading.** `relu_chain.py` measured
   `‖net(x) − x‖`. Under Xavier initialisation the output shrinks as the width
   grows, so the value converged to `‖x‖`, the score of a network that returns
   nothing.
3. **The 1-D case measured against a diagonal.** One coordinate was used twice,
   which put every "random" point on the line `y = x`.

These scripts are kept unfixed, with a warning at the top of each, because the
audit depends on them. Do not cite their output.

Two later corrections were numerical. A fixed sampling grid overestimated
distances for steep curves (fixed 19 Sep 2026). The replacement still chose
the wrong stroke of the curve once the strokes were closer together than the
sample spacing, which overestimated one control by 11% at frequency 1000
(fixed 11 Nov 2026). Both are described in `docs/RESOLUTION.md` §2.

## Open questions

The full list, with a status for each, is in
[`docs/open-problems.md`](docs/open-problems.md). The main ones:

- How does the oscillation scale of a network with random weights depend on
  width, depth and weight scale? This is what the "parameters" claim reduces
  to.
- Does gradient descent find the small shift of the inputs that the theorem
  says exists?
- Do the fixed-kernel results in section 8 survive when the kernel moves
  during training?

Experiments that are specified and not yet run are in
[`handoff.md`](handoff.md).

## Wishlist

The aim is to say all of deep learning in the terms of the squiggly line
(slope, nearness, travel, the kernel and the lift, folds, and averages) with
every step machine-checked. [`docs/wishlist.md`](docs/wishlist.md) lists
well-known papers under whichever of those they connect through, says each
in those terms, and marks it proved, next, or out of reach. It also lists the
proofs I want and cannot get yet, with what is in the way.

## Citing

```bibtex
@misc{nanda2026squiggly,
  title        = {The Squiggly Line Theorem},
  author       = {Nanda, Souradeep},
  year         = {2026},
  howpublished = {\url{https://github.com/Ghost---Shadow/squiggly-line-theorem}},
  note         = {Preprint, with machine-checked proofs in Lean 4}
}
```

GitHub's "Cite this repository" button gives the same entry in other formats
(from [`CITATION.cff`](CITATION.cff)).

## License

MIT. See [`LICENSE`](LICENSE).
