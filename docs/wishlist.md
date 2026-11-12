# Wishlist, paper by paper

Written 12 Nov 2026. The aim is to say all of deep learning in the terms of
this repository (slope, nearness, travel, the kernel and the lift) with every
step machine-checked. This is the list of well-known papers and ideas, and
where each one stands.

The papers and years are recalled from memory and have not been checked.

Each row has a status.

- **proved**: a statement of it, for a simplified model, is in `lean/`. The
  file is named.
- **next**: a statement that looks within reach of the tools already here.
  The statement is given. These are worked through in order.
- **out of reach**: needs mathematics or library support that is missing.
  The README wishlist says what is in the way.
- **no statement**: there is nothing precise to prove yet.

## Foundations

| Paper or idea | In plain words | Status |
|---|---|---|
| Perceptron (Rosenblatt 1958; Novikoff 1962) | On data that a flat boundary can split with margin `γ`, inside a ball of radius `R`, the perceptron makes at most `(R / γ)²` mistakes. | **next** |
| XOR (Minsky and Papert 1969) | No flat boundary computes XOR. One extra feature, the product of the inputs, makes it flat. | **next** |
| Backpropagation (Rumelhart, Hinton and Williams 1986) | The gradient comes back through the layers in reverse order, each layer applying its transpose. | **next** |
| Universal approximation (Cybenko 1989; Hornik 1991) | One hidden layer can draw any curve. | **proved** in one dimension with a rate: `UniversalApproximation.lean`. Many dimensions: **out of reach** |
| No free lunch (Wolpert 1996) | Averaged over every possible labelling of the unseen inputs, every learner is right half the time. | **next** |
| Convolution and weight sharing (LeCun et al. 1989) | A convolution gives the same answer, shifted, when its input is shifted. | **next** |
| Vanishing gradients and the LSTM (Hochreiter and Schmidhuber 1997) | A gain below one per step dies out, above one blows up. | **proved**: `VanishingGradients.lean` |
| Kernel trick, support vector machines (Boser, Guyon and Vapnik 1992) | A squiggly boundary is a flat one after a lift. | **proved**: `Lift.lean` |
| Reinforcement learning (Bellman 1957; Mnih et al. 2015) | One sweep of value updates shrinks the error by the discount factor, so the values settle. | **next** |
| Policy gradient (Williams 1992) | Subtracting a baseline from the reward does not change the average gradient. | **next** |
| Bias and variance (Geman et al. 1992) | Error is bias squared plus variance. | **proved**: `BiasVariance.lean` |
| Ensembles (Krogh and Vedelsby 1995; Lakshminarayanan et al. 2017) | The average of several models has squared error no worse than the average model, and better by exactly their spread. | **next** |

## Making deep networks train

| Paper or idea | In plain words | Status |
|---|---|---|
| ReLU and AlexNet (Nair and Hinton 2010; Krizhevsky et al. 2012) | A ReLU layer folds space. Folds stack. | **proved**: `Depth.lean`, `Polarizer.lean` |
| Initialisation (Glorot and Bengio 2010; He et al. 2015) | A ReLU keeps half the squared size of a signal that is as often negative as positive. That is the factor two in He initialisation. | **next** |
| Dropout (Srivastava et al. 2014) | Dropout is weight decay with a rate per feature. | **proved** for a linear model: `Dropout.lean` |
| Adam (Kingma and Ba 2015) | Adam's steps do not change when the loss is multiplied by a constant. | **next** |
| Batch and layer normalisation (Ioffe and Szegedy 2015; Ba et al. 2016) | Weights that feed a normalisation can be rescaled freely. So their gradient is at right angles to them, and plain gradient descent only makes them longer. | **next**. One example at a time: **proved**, `SkipAndNorm.lean` |
| Residual networks (He et al. 2016) | A skip is a bypass. Nothing is ever fully blocked. | **proved** for plates: `SkipAndNorm.lean` |
| Gradient clipping (Pascanu et al. 2013) | A clipped step is never longer than the limit, and keeps its direction. | **next** |
| Weight decay and AdamW (Loshchilov and Hutter 2019) | Weight decay leaves the share `μ / (λ + μ)` of the error. | **proved** for gradient descent: `WeightDecay.lean`. With Adam: **out of reach** |
| Linear scaling rule (Goyal et al. 2017; Smith et al. 2018) | Double the batch, double the learning rate. | **proved**: `BatchSize.lean` |
| Label smoothing (Szegedy et al. 2016) | With a soft label the best score is finite. | **next** |
| Knowledge distillation (Hinton et al. 2015) | The student is pushed by its own shares minus the teacher's. | **proved** as a case of `hasDerivAt_crossEntropy` in `CrossEntropy.lean` |
| Temperature and calibration (Guo et al. 2017) | Dividing the scores by a temperature changes confidence and never the ranking. | **next** |
| Slope of a network (Szegedy et al. 2014; Bartlett et al. 2017; Miyato et al. 2018) | A network is no steeper than the product of the sizes of its layers. So nearness has to be paid for in that product. | **next** |
| Deep linear networks (Saxe et al. 2014; Arora et al. 2018) | With two weights multiplied, `a·b`, the difference `a² − b²` hardly changes in training. | **next** |

## What training finds

| Paper or idea | In plain words | Status |
|---|---|---|
| Rethinking generalisation (Zhang et al. 2017) | Networks fit random labels. | **proved** as capacity and travel: `Capacity.lean`, section 5 of the README |
| Neural tangent kernel, lazy training (Jacot et al. 2018; Chizat and Bach 2019) | A very wide network trains like a linear model. | The linear model: **proved**, `Kernel.lean`. That wide networks are one: **out of reach** |
| Gradient descent happens in a tiny subspace (Gur-Ari et al. 2018) | Training moves only along the features of the data. | **proved**: `LeastAction.lean`, `CrossEntropy.lean` |
| Implicit bias (Gunasekar et al. 2017; Soudry et al. 2018) | Gradient descent picks the nearest fit. | Squared error and any loss, nearest among equal outputs: **proved**. Widest margin: **out of reach** |
| Double descent (Belkin et al. 2019; Nakkiran et al. 2020) | Test error peaks where the model can just fit. | **proved** for travel: `DoubleDescent.lean`. Test error: **out of reach** |
| Benign overfitting (Bartlett et al. 2020) | Fitting noise can be harmless. | **proved** for one junk direction: `BenignOverfitting.lean` |
| Spectral bias (Rahaman et al. 2019) | Gentle functions are learned first. | **proved**: `SpectralBias.lean` |
| Edge of stability (Cohen et al. 2021) | Training is stable up to sharpness `2 / η`. | The threshold: **proved**, `EdgeOfStability.lean`. Why networks sit at it: **out of reach** |
| Flat minima (Hochreiter and Schmidhuber 1997; Keskar et al. 2017; Dinh et al. 2017) | Flatness can be changed by rescaling without changing the function. | **proved**: `Reparam.lean` |
| Loss along a line (Goodfellow et al. 2015) | From the start to the solution in a straight line, the loss only falls. | **proved** for linear models: `LinearModel.lean`, `CrossEntropy.lean` |
| Mode connectivity (Garipov et al. 2018; Draxler et al. 2018) | Two solutions are joined by a path with no hill. | **proved** for linear models: `ModeConnectivity.lean` |
| Relabelling neurons (Entezari et al. 2022; Ainsworth et al. 2023) | Shuffling the hidden units does not change the function. | **next**. No hill after shuffling: **out of reach** |
| Model soups and weight averaging (Izmailov et al. 2018; Wortsman et al. 2022) | Averaging the weights of several models is no worse than the average model. | **next** |
| Lottery ticket (Frankle and Carbin 2019) | A small part of the network would have been enough. | **proved** for a fixed kernel: `Pruning.lean`. Strong form: **out of reach** |
| Neural collapse (Papyan et al. 2020) | Class means end up as far apart as they can be. | The limit: **proved**, `NeuralCollapse.lean`. That training reaches it: **out of reach** |
| Information bottleneck (Shwartz-Ziv and Tishby 2017) | Layers keep what the label needs and drop the rest. | **proved** as a count: `Bottleneck.lean` |
| Platonic representations (Huh et al. 2024) | Different models agree when their kernels agree. | **proved**: `SameKernel.lean` |
| Catastrophic forgetting (Kirkpatrick et al. 2017) | A new task disturbs an old one through their shared kernel. | **proved**: `Forgetting.lean` |
| Grokking (Power et al. 2022) | Generalisation long after fitting. | Argued. **out of reach** |
| Scaling laws (Kaplan et al. 2020; Hoffmann et al. 2022) | Loss falls as a power of size and data. | The balance rule: **proved**, `ComputeBudget.lean`. The powers: **out of reach** |
| Low-rank adaptation, intrinsic dimension (Li et al. 2018; Hu et al. 2021) | Training only some directions can still fit, at the cost of more travel. | **next** |
| Quantisation (Courbariaux et al. 2015 and after) | Rounding the weights moves each output by at most the rounding error times the size of the features. | **next** |

## Robustness

| Paper or idea | In plain words | Status |
|---|---|---|
| Adversarial examples (Szegedy et al. 2014; Goodfellow et al. 2015) | For a linear model, nudging every input a little, each in the worst direction, moves the score by the nudge times the sum of the sizes of the weights. In many dimensions that is large. | **next** |
| Dimpled manifold (Shamir et al. 2021) | A function can be right on the data and one small step from wrong beside it. | **proved**: `Dimple.lean` |
| Robustness against accuracy (Tsipras et al. 2019) | Nearness is bought with slope. | **proved**: the slope sandwich, `Sandwich.lean` |

## Transformers and language

| Paper or idea | In plain words | Status |
|---|---|---|
| Attention (Bahdanau et al. 2015; Vaswani et al. 2017) | Attention is a weighted average. | **proved**: `Attention.lean` |
| Position signals (Vaswani et al. 2017; Su et al. 2021) | With sine and cosine position signals, moving along the sequence is a fixed turn. So the overlap of two positions depends only on how far apart they are. | **next** |
| Softmax and cross-entropy (the loss of every classifier and language model) | The push is prediction minus label. | **proved**: `CrossEntropy.lean` |
| Next-word prediction and perplexity (Shannon 1948; GPT, Radford et al. 2018) | No model's average log-loss is below the entropy of the text. | **proved**: `CodeLength.lean` |
| Sampling with temperature, top-k and nucleus (Holtzman et al. 2020) | Temperature never changes which word is most likely. | **next** (with temperature above) |
| In-context learning (Brown et al. 2020; von Oswald et al. 2023) | One attention head can be one step of gradient descent on the prompt. | **proved**: `Attention.lean`. That training finds it: **out of reach** |
| Rank collapse (Dong et al. 2021) | Attention alone pulls tokens together. | That it cannot spread them: **proved**, `Attention.lean`. The rate: **out of reach** |
| Word vectors (Mikolov et al. 2013) | King minus man plus woman is queen, when a word's vector is the sum of the vectors of its features. | **next** |
| Contrastive learning (van den Oord et al. 2018; Chen et al. 2020; Radford et al. 2021) | The contrastive loss is a cross-entropy over the batch. Guessing blindly costs the log of the batch size. | **next** |
| Superposition, sparse autoencoders (Elhage et al. 2022; Bricken et al. 2023) | A layer stores more features than it has dimensions. | **out of reach** |
| Chain of thought, emergent abilities | A model that predicts words can reason in steps. | **no statement** |

## Generative models

| Paper or idea | In plain words | Status |
|---|---|---|
| Variational autoencoder (Kingma and Welling 2014) | The training target is never above the true log-likelihood. | **next** |
| Generative adversarial networks (Goodfellow et al. 2014) | The best critic outputs `p / (p + q)`. And two players taking gradient steps against each other can spiral outward instead of settling. | **next** |
| Diffusion models (Sohl-Dickstein et al. 2015; Ho et al. 2020; Song et al. 2021) | The best denoiser returns the average of the clean images that could have led to the noisy one. | **next**. Why they generalise: **out of reach** |
| Classifier-free guidance (Ho and Salimans 2022) | Guidance pushes past the conditional answer, away from the unconditional one. | **no statement** beyond the formula |

## Shapes and signals

| Paper or idea | In plain words | Status |
|---|---|---|
| Signed distance networks (Park et al. 2019) | A shape as a distance field. | **proved**: `SignedDistance.lean` |
| Fourier features and NeRF (Tancik et al. 2020; Mildenhall et al. 2020) | Feeding sines of the input lets a network draw fine detail. The detail comes from the stretch of the lift. | The lift: **proved**, `Lift.lean`, `Bridge.lean`. The stretch of the Fourier lift: **next** |
| Neural ODEs (Chen et al. 2018) | Many small layers act like one smooth flow. | **proved** as many small steps: `SmallSteps.lean` |
| Kolmogorov–Arnold networks (Liu et al. 2024) | A learnable curve on each edge. Each such curve is a small ReLU network. | Argued from `UniversalApproximation.lean`. The representation theorem: **out of reach** |

## Sayings

| Saying | Status |
|---|---|
| The bitter lesson (Sutton 2019): methods that use more compute win. | **no statement** |
| "X is all you need." | **no statement** |
| Stochastic parrots; sparks of general intelligence. | **no statement** |
