# Wishlist

Written 12 Nov 2026. The aim is to say all of deep learning in the terms of
the squiggly line, with every step machine-checked. This file lists
well-known papers and ideas, says each one in those terms, and says where it
stands.

Nothing goes on the worklist unless it connects to the squiggly line through
one of six things. The list is grouped by them.

- **Slope.** How steep the line is. The theorem: nearness is bought with
  slope and with nothing else.
- **Nearness.** The distance from a data point to the line, or to a boundary.
- **Travel.** The distance the weights move to reach a fit.
- **The kernel and the lift.** A squiggly line is a flat plane seen through a
  lift, and training sees only the kernel.
- **Folds.** A ReLU layer folds the line. Folds are how depth makes squiggle.
- **Averages.** An average is never squigglier than what it averages.

Each row has a status.

- **proved**: a statement of it, for a simplified model, is in `lean/`.
- **next**: looks within reach of the tools already here. Worked through in
  order.
- **out of reach**: needs mathematics or library support that is missing.
  The last two sections say what is in the way.

The papers and years are recalled from memory and have not been checked.

## Slope

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Robustness against accuracy (Tsipras et al. 2019) | `vertical / √(1 + K²) ≤ nearest ≤ vertical`: a line can be near the data only by being steep. | **proved**: `Sandwich.lean` |
| Slope of a network (Szegedy et al. 2014; Bartlett et al. 2017; Miyato et al. 2018) | A network is no steeper than the product of the slopes of its layers. So its nearness to the data has to be paid for in that product. | **proved**: `NetworkSlope.lean` |
| Backpropagation (Rumelhart, Hinton and Williams 1986) | The gradient comes back through the same layers in reverse, so it is bounded by the same product. | **proved**: `NetworkSlope.lean`, `VanishingGradients.lean` |
| Vanishing gradients and the LSTM (Hochreiter and Schmidhuber 1997) | A slope below one per layer dies out with depth, above one blows up. | **proved**: `VanishingGradients.lean` |
| Adversarial examples (Szegedy et al. 2014; Goodfellow et al. 2015) | To flip a classifier of slope `K` you must move the input at least `score / K`. For a linear model, nudging every input by `ε` moves the score by `ε` times the sum of the sizes of the weights. | **proved**: `NetworkSlope.lean` |
| Dimpled manifold (Shamir et al. 2021) | Gentle along the data, steep straight off it. | **proved**: `Dimple.lean` |
| Wasserstein GAN (Arjovsky et al. 2017) | The critic is held to slope one. The gap it reports between two points is then at most their distance, and a distance field is such a critic. | **proved**: `NetworkSlope.lean` |
| Temperature and calibration (Guo et al. 2017; Holtzman et al. 2020) | Dividing the scores by a temperature divides their slope and never changes their order. | **proved**: `NetworkSlope.lean` |
| Softmax and cross-entropy | For a yes-or-no label no finite score is best, so the loss keeps asking for a steeper line. | **proved**: `CrossEntropy.lean` |
| Label smoothing (Szegedy et al. 2016) | With a soft label the best score is finite, so the slope can stop growing. | **next** |
| Reinforcement learning (Bellman 1957; Mnih et al. 2015) | One sweep of value updates is a map of slope `γ < 1`, so repeated sweeps pull every guess to one answer. | **next** |
| Signed distance networks (Park et al. 2019) | The distance field of any line has slope at most one. | **proved**: `SignedDistance.lean` |

## Nearness

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| The 2022 conjecture | A squigglier line is nearer to the data. | **proved** for sines and for any squeezed function: `SquigglyLineTheorem.lean`, `Compression.lean` |
| No free lunch (Wolpert 1996) | Averaged over every labelling of the unseen inputs, no line is nearer than any other. Squiggle helps only when labels vary gently. | **next** |
| Perceptron (Rosenblatt 1958; Novikoff 1962) | If the data is at least `γ` from a flat boundary and inside radius `R`, the perceptron makes at most `(R / γ)²` mistakes. Nearness of the data to the boundary sets the number of steps. | **next** |
| XOR (Minsky and Papert 1969) | The smallest data that no flat boundary fits. One lift, or one fold, fixes it. | **next** |
| Sphere tracing (Hart 1996) | A step shorter than the distance field cannot reach the line. | **proved**: `SignedDistance.lean` |

## Travel

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Lazy training (Chizat and Bach 2019) | A bigger model starts no nearer in loss and much nearer in travel. | **proved**: `LinearModel.lean`, `ExchangeRate.lean` |
| Double descent (Belkin et al. 2019; Nakkiran et al. 2020) | Travel peaks where the model can just fit. | **proved** for travel: `DoubleDescent.lean` |
| Implicit bias (Gunasekar et al. 2017; Soudry et al. 2018) | Gradient descent takes the least travel. | **proved**: `LeastAction.lean`, `CrossEntropy.lean` |
| Gradient descent happens in a tiny subspace (Gur-Ari et al. 2018) | Training travels only along the features of the data. | **proved**: `LeastAction.lean` |
| Weight decay, early stopping (Krogh and Hertz 1992) | A floor on travel: directions weaker than the floor are not learned. | **proved**: `WeightDecay.lean` |
| Dropout (Srivastava et al. 2014) | The same floor, set by the dropout rate. | **proved**: `Dropout.lean` |
| Loss along a line (Goodfellow et al. 2015) | From the start to the fit in a straight line, the loss only falls. | **proved** for linear models: `LinearModel.lean`, `CrossEntropy.lean` |
| Mode connectivity (Garipov et al. 2018; Draxler et al. 2018) | No hill on the straight path between two fits. | **proved** for linear models: `ModeConnectivity.lean` |
| Flat minima (Keskar et al. 2017; Dinh et al. 2017) | Rescaling changes flatness and travel and leaves the line alone. | **proved**: `Reparam.lean` |
| Normalisation (Ioffe and Szegedy 2015; Ba et al. 2016) | Weights that feed a normalisation can be rescaled freely, so the gradient is at right angles to them and each step makes them longer. Their size stops setting the slope. | **next**. One example at a time: **proved**, `SkipAndNorm.lean` |
| Adam (Kingma and Ba 2015) | Adam travels the same distance per step along a strong direction and a weak one. It removes the "strong first" clock of spectral bias, so squiggles are fitted sooner. | **next** |
| Gradient clipping (Pascanu et al. 2013) | A cap on travel per step. | **next**, with Adam |
| Low-rank adaptation, intrinsic dimension (Li et al. 2018; Hu et al. 2021) | Training only some directions never shortens the travel. | **next** |
| Quantisation (Courbariaux et al. 2015 and after) | Moving the weights by a rounding error moves each output by at most that error times the stretch of the lift. | **next** |
| Relabelling neurons (Entezari et al. 2022) | Shuffling the hidden units gives the same line at a different place in weight space. Travel is to the nearest copy. | **next**. No hill after shuffling: **out of reach** |
| Deep linear networks (Saxe et al. 2014; Arora et al. 2018) | For two weights multiplied, training keeps `a² − b²` almost fixed, so the slope is shared between the layers. | **next** |
| Linear scaling rule (Goyal et al. 2017) | Two small steps are one big step, up to a term through the kernel. | **proved**: `BatchSize.lean` |
| Scaling laws (Kaplan et al. 2020; Hoffmann et al. 2022) | The best split of a budget balances the two terms of the loss. | **proved**: `ComputeBudget.lean` |
| Lottery ticket (Frankle and Carbin 2019) | Pruning subtracts a kernel: slower and farther. | **proved** for a fixed kernel: `Pruning.lean` |

## The kernel and the lift

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Kernel trick, support vector machines (Boser, Guyon and Vapnik 1992) | Squiggly below is flat above. | **proved**: `Lift.lean` |
| Neural tangent kernel (Jacot et al. 2018) | For training, a model is its kernel. | **proved** for a fixed kernel: `Kernel.lean` |
| Spectral bias (Rahaman et al. 2019) | Gentle directions of the kernel are learned first. | **proved**: `SpectralBias.lean` |
| Edge of stability (Cohen et al. 2021) | A direction is stable up to strength `2 / η`. | **proved**: `EdgeOfStability.lean` |
| Fourier features and NeRF (Tancik et al. 2020; Mildenhall et al. 2020) | A Fourier lift of frequency `w` stretches distances by exactly up to `w`. That stretch is where the fine detail comes from. | **next** |
| Position signals (Vaswani et al. 2017; Su et al. 2021) | The same lift applied to position. Moving along the sequence is a fixed turn, so the kernel of two positions depends only on how far apart they are. | **next**, with the row above |
| Convolution (LeCun et al. 1989) | A kernel that depends only on how far apart two inputs are gives the same line when the data is shifted. | **next**, with the row above |
| Platonic representations (Huh et al. 2024) | Same kernel, same learner. | **proved**: `SameKernel.lean` |
| Catastrophic forgetting (Kirkpatrick et al. 2017) | A new task moves an old one through the kernel between them. | **proved**: `Forgetting.lean` |
| Benign overfitting (Bartlett et al. 2020) | Junk directions of the kernel swallow the noise. | **proved** for one junk direction: `BenignOverfitting.lean` |
| Rethinking generalisation (Zhang et al. 2017) | A lift into `m` dimensions fits any labels on `m` points. | **proved**: `Capacity.lean` |
| In-context learning (von Oswald et al. 2023) | One attention head scoring by the kernel is one step of travel on the prompt. | **proved**: `Attention.lean` |

## Folds

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| ReLU and depth (Nair and Hinton 2010; Telgarsky 2016) | `L` folds make `2^L` pieces and pass within `1 / 2^L` of every point. | **proved**: `Depth.lean`, `TentCloser.lean`, `DepthSeparation.lean` |
| Universal approximation (Cybenko 1989) | Units needed go as slope over error. | **proved** in one dimension: `UniversalApproximation.lean` |
| Initialisation (Glorot and Bengio 2010; He et al. 2015) | A fold keeps half the squared size of a signal that is as often negative as positive. That is the factor two in He initialisation. | **next** |
| Residual networks (He et al. 2016) | A skip is a bypass: nothing is fully blocked. | **proved** for plates: `SkipAndNorm.lean` |
| Dying ReLU | Dead stays dead. | **proved**: `MarkovChains.lean` |
| Information bottleneck (Shwartz-Ziv and Tishby 2017) | A fold merges inputs and merged stays merged. | **proved**: `Bottleneck.lean`, `CodeLength.lean` |
| Neural ODEs (Chen et al. 2018) | Many small turns lose almost nothing. | **proved**: `SmallSteps.lean` |
| Kolmogorov–Arnold networks (Liu et al. 2024) | A learnable curve on an edge is a few folds. | Argued from `UniversalApproximation.lean` |

## Averages

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Attention (Vaswani et al. 2017) | A weighted average. It cannot spread the tokens, so it cannot add squiggle. | **proved**: `Attention.lean` |
| Ensembles (Krogh and Vedelsby 1995; Lakshminarayanan et al. 2017) | The average of several lines is no steeper than the steepest, and its squared error is the average error minus the spread of the lines. | **next** |
| Model soups and weight averaging (Izmailov et al. 2018; Wortsman et al. 2022) | For a model linear in its weights, averaging weights is averaging lines. | **next**, with ensembles |
| Diffusion models (Ho et al. 2020; Song et al. 2021) | The best denoiser is an attention head over the training set: a weighted average of the clean examples. So it never leaves the region the examples span. | **next** |
| Bias and variance (Geman et al. 1992) | The noise an average removes is the variance. | **proved**: `BiasVariance.lean` |
| Neural collapse (Papyan et al. 2020) | Class averages can be no farther apart than a simplex. | **proved**: `NeuralCollapse.lean` |

## No link to the squiggly line yet

These are famous and I have not found the connection. They stay off the
worklist until there is one.

| Paper or idea | Why not yet |
|---|---|
| Variational autoencoders (Kingma and Welling 2014) | The bound is a code-length fact. `CodeLength.lean` has the tools, but nothing ties it to slope or travel. |
| Generative adversarial networks, the original game (Goodfellow et al. 2014) | The best critic and the spiralling of the two players are provable, but only the slope-one critic of the Wasserstein version connects. |
| Word vectors (Mikolov et al. 2013) | "King minus man plus woman" is flatness upstairs. Nothing more to say than `Lift.lean` says. |
| Contrastive learning (Chen et al. 2020; Radford et al. 2021) | The loss is a cross-entropy, covered by `CrossEntropy.lean`. What it does to the lift is the open part. |
| Policy gradient (Williams 1992) | No link found. |
| Knowledge distillation (Hinton et al. 2015) | Prediction minus the teacher's prediction, a case of `CrossEntropy.lean`. Why a student learns a gentler line is open. |
| Chain of thought; the bitter lesson; "X is all you need" | No statement to prove. |

## Out of reach: the mathematics is known

A machine-checked proof is out of reach here for now. Most of these need
facts about large random matrices, which the proof library does not have yet.
The rest are long.

| What I want proved | What exists | What is in the way |
|---|---|---|
| A wide network trains like a model linear in its weights: its kernel hardly moves. This one result would carry every fixed-kernel proof to real, wide networks. | Jacot et al. 2018; Lee et al. 2019 | Limits of wide random layers, and control of the kernel along the whole training path. |
| Random features are nearly orthogonal, so travel falls like one over the root of the parameter count. | Measured in section 5 of the README | A concentration bound for random matrices. |
| The height of the double-descent peak, and that the test error peaks where the travel does. | Hastie et al. 2022; here only the travel is proved | The spectrum of a large random matrix. |
| Fitting noise is harmless exactly when the weak directions are many and even. | Bartlett et al. 2020; here one junk direction | The same. |
| Cross-entropy on separable data sends the weights toward the widest-margin direction. | Soudry et al. 2018; here only that no finite score is best | A long limit argument on the training path. |
| A big enough random network already contains a small one that fits (the strong lottery ticket). | Malach et al. 2020; here pruning for a fixed kernel | Counting arguments with chance in them. |
| Depth beats width for networks of any depth. | Telgarsky 2016; here one hidden layer against a deep one | The general bound on how many straight pieces a network draws. |
| Approximation with a rate in many dimensions. | Barron 1993; here one dimension | Fourier analysis in many dimensions. |
| Neural collapse comes out of training. | Proved for a simplified model in the literature; here only that the simplex is the limit | The training path, even for the simplified model. |
| A distance field changes at rate exactly one away from the shape (the eikonal equation). | Classical; here only "at most one" | Geometry of nearest points; not attempted yet. |
| Dropout and weight decay under cross-entropy. | Wager, Wang and Liang 2013, to second order | The error is no longer linear in the outputs. |
| How fast attention alone merges the tokens. | Dong et al. 2021; here only that it cannot spread them | Products of many random averaging tables. |

## Out of reach: nobody knows yet

These need new mathematics, or a statement precise enough to prove.

| What I want proved | What exists | What is in the way |
|---|---|---|
| How squiggly a network with random weights is, as a function of width, depth and weight scale. This is the original conjecture for networks. | `docs/open-problems.md`, item 1 | No known formula for the oscillation scale. |
| What happens when the lift moves. A network that learns features is choosing its own upstairs. Every fixed-kernel proof would need a version for it. | Theories for special cases | No general theory of feature learning. |
| Why the sharpness of a real network rises to `2 / η` and then stays there. | Observed: Cohen et al. 2021; here only the threshold | The kernel moves, and why it stops at the edge is not understood. |
| Grokking: why a network can start to generalise long after it fits. | Observed: Power et al. 2022; argued here from the clocks of spectral bias | No agreed statement to prove. |
| Why Adam beats plain gradient descent on transformers. | Observed | Not understood. |
| Whether flat minima generalise, and in what sense of flat. | `Reparam.lean` shows plain flatness cannot be the reason | No measure of flatness that survives rescaling and still predicts. |
| No hill between two trained networks once the neurons of one are relabelled. | Conjectured: Entezari et al. 2022; here the linear case | Open even for small networks. |
| That training a transformer finds heads that run gradient descent on the prompt, and what softmax attention with feed-forward layers computes. | Proved for linear attention in the literature; here only that one head can be one step | The softmax and the other layers. |
| Why the loss falls as a power of parameters and of data, and what sets the powers. | Measured: Kaplan et al. 2020; Hoffmann et al. 2022; here only the balance rule | The form of the loss is a measurement with no derivation. |
| A bound on test error that is tight enough to mean something for a real network. | Bounds exist and are mostly far too loose | Not known what quantity to bound with. |
| Why a network trained to remove noise makes new images and does not copy its training set. | Observed in diffusion models | Not understood. The ideal denoiser only averages its training set. |
| How many features a layer can hold in fewer dimensions, and how training lays them out (superposition). | Observed: Elhage et al. 2022; here the opposite bound for well-separated directions | No theory of the training side. |
| What normalising across a batch does. | `docs/open-problems.md`, item 21; here one example at a time | Each example's path depends on the others. |

At the far end is the question of why predicting the next word gives a model
that can do so much else. There is not yet a statement of it to prove.
