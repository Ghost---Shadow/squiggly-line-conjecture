# Wishlist

**Proofs:** [`Compression.lean`](../lean/SquigglyLine/Theorem/Compression.lean), [`Depth.lean`](../lean/SquigglyLine/Networks/Depth.lean), [`Lift.lean`](../lean/SquigglyLine/Networks/Lift.lean), [`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean), [`Capacity.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean), [`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean), [`Perceptron.lean`](../lean/SquigglyLine/Supporting/Training/Perceptron.lean), [`Reparam.lean`](../lean/SquigglyLine/Supporting/Training/Reparam.lean).

Written 12 Nov 2026. The aim is to say all of deep learning in the terms of
the squiggly line, with every step machine-checked. This file lists
well-known papers and ideas, says each one in those terms, and says where it
stands.

Nothing goes on the worklist unless it connects to the squiggly line through
one of six things. The list is grouped by them. It keeps to ideas that are
well established and in common use. Niche results and rarely used
optimisers are left to others.

- **Slope.** How steep the line is. The theorem: nearness is bought with
  slope and with nothing else.
- **Nearness.** The distance from a data point to the line, or to a boundary.
- **Travel.** The distance the weights move to reach a fit.
- **The kernel and the lift.** A squiggly line is a flat plane seen through a
  lift, and training sees only the kernel.
- **Folds.** A ReLU layer folds the line. Folds are how depth makes squiggle.
- **Averages.** An average is never squigglier than what it averages.

What is proved is not listed here. It is in the
[README](../README.md#proved-paper-by-paper), paper by paper. Each row here
has a status.

- **next**: looks within reach of the tools already here. Worked through in
  order. 29 are marked as of 14 Nov 2026, from a second pass over the list
  made once the first one was finished. AdamW and RMSNorm go first. The
  list is frozen for this round.
- **out of reach**: needs mathematics or library support that is missing.
  The last two sections say what is in the way.

The papers and years are recalled from memory and have not been checked.

## Slope

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Adversarial training (Madry et al. 2018) | For a linear model, training against the worst nudge of size `ε` is training with a penalty of `ε` times the summed sizes of the weights. The defence is a charge on slope. | **next** |
| Training with noise on the input (Bishop 1995) | For a linear model, noise of variance `σ²` on the input adds `σ²` times the squared slope to the expected loss. Noise is a charge on slope. | **next** |
| Mixup (Zhang et al. 2018) | A model that fits every blend of two examples is straight between them. Its slope there is the gap in labels over the distance, the least any line through both can have. | **next** |
| Knowledge distillation (Hinton et al. 2015) | A teacher's soft label gives the student a finite best score, the teacher's own. A hard label gives none. So a student is never asked for more slope than its teacher has. | **next** |
| Convolution, slope (LeCun et al. 1989) | A convolution layer is no steeper than the summed sizes of its kernel weights, whatever the size of the image. | **next** |
| Convolution, locality (LeCun et al. 1989) | After `L` layers of kernel radius `r`, an output depends only on inputs within `L × r` of it. Squiggles are made locally and shared across positions. | **next** |
| Stride and downsampling | Reading every second input is squeezing by two, in the sense of [`Compression.lean`](../lean/SquigglyLine/Theorem/Compression.lean). Each stride doubles the frequency of what the later layers see. | **next** |
| Upsampling (Ronneberger et al. 2015) | The mirror of stride: stretching by two halves the frequency. | **next** |
| Mixture of experts and gating (Jacobs et al. 1991) | A gate that blends experts adds slope only through how far apart the experts are. Where the experts agree, a gate adds none. | **next** |

## Nearness

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Nearest neighbours (Cover and Hart 1967) | Copying the label of the nearest training input is wrong by at most the slope of the truth times the distance to that input. | **next** |
| k-means and vector quantisation (Lloyd 1982; van den Oord et al. 2017) | Each half of a step brings the data nearer to its codes: moving a point to its nearest code, and moving a code to the average of its points. The cost never rises. | **next** |
| Contrastive learning (Chen et al. 2020; Radford et al. 2021) | For vectors of length one, a softmax over cosine similarity is a softmax over squared distance. So the loss scores pairs by nearness upstairs, with the same weights as the ideal denoiser of [`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean). | **next** |

## Travel

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Lasso, the penalty on summed sizes (Tibshirani 1996) | Weight decay shrinks a weak direction. This penalty sets it to exactly zero: a direction weaker than the penalty is not travelled at all. | **next** |
| Stochastic depth (Huang et al. 2016) | Dropping a branch at random is, on average, the branch at part strength. The same floor as dropout, on whole layers. | **next** |
| Variational autoencoders (Kingma and Welling 2014) | The penalty on the code is half its squared travel from the origin plus a term in its width. It is zero only for a code that ignores the input. | **next** |
| Random features are nearly at right angles, on average | Two random directions in `d` dimensions have expected squared overlap `1 / d`. This is the on-average form of the fact that makes travel fall with size. | **next** |

## The kernel and the lift

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Sinusoidal positions, all frequencies together (Vaswani et al. 2017) | With many frequencies the overlap of two positions is a sum of cosines of the gap between them. It still depends only on the gap, and it is largest at gap zero. | **next** |
| Rotary positions (Su et al. 2021) | Turn the query and the key by angles set by their positions. The score then depends on the two positions only through the gap, and no vector changes length. | **next** |
| Relative position bias (Shaw et al. 2018; Raffel et al. 2020) | Add to each score a number that depends only on the gap. Shifting the whole sequence then changes no attention weight. | **next** |
| Learned position table (Devlin et al. 2019; Radford et al. 2019) | One free vector per position is a lookup: a lift that can give any position anything. It ties no two positions together and says nothing about a position it has not seen. | **next** |
| Softmax bottleneck (Yang et al. 2018) | With `d` hidden numbers the table of scores over contexts and words has rank at most `d`. A lift that small cannot give every next-word distribution. | **next** |
| Random Fourier features (Rahimi and Recht 2007) | Average the Fourier-lift kernel over frequencies drawn from a bell curve and the result is the Gaussian bump. The Fourier lift and the radial basis kernel are one thing. | **next** |
| Policy gradient (Williams 1992) | The push on the scores is the action taken minus the prediction, times the reward. That is the cross-entropy push, so the same kernel carries it. | **next** |

## Folds

| Paper or idea | In squiggly terms | Status |
|---|---|---|

## Averages

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Graph networks blur their nodes with depth (Kipf and Welling 2017; Li et al. 2018) | A message-passing layer is an average over neighbours, so the spread of the nodes shrinks at a geometric rate. | **next** |
| The diffusion noising schedule (Ho et al. 2020) | Each noising step blends the signal with fresh noise so the total variance stays fixed while the signal's share shrinks geometrically. | **next** |
| Where a transformer makes its squiggle | Attention only averages, so it adds no turn. Every turn comes from the folds of the feed-forward block. | Argued from [`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean) and [`Depth.lean`](../lean/SquigglyLine/Networks/Depth.lean) |
| Squared error fits the mean, absolute error the median | The loss chooses which average the line goes through. | Mean **proved**: [`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean). Median **next** |
| The actor-critic baseline (Sutton and Barto 1998) | Subtracting a baseline from the reward leaves the average push unchanged. | **next** |
| Data augmentation and invariance | Averaging a model over a set of moves that keep distances gives a model that ignores those moves and is no steeper. | **next** |
| Classifier-free guidance (Ho and Salimans 2022) | Guidance is the one step of a diffusion sampler that is not an average: its weights are `1 + w` and `−w`. It moves `1 + w` times as far as the plain step, and can leave the region the examples span. | **next** |
| Averaging the weights over time (Polyak and Juditsky 1992) | A running average of the weights is an average of lines, for a model linear in its weights. | Argued from [`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean) |

## No link to the squiggly line yet

These are famous and I have not found the connection. They stay off the
worklist until there is one.

| Paper or idea | Why not yet |
|---|---|
| Word vectors (Mikolov et al. 2013) | "King minus man plus woman" is flatness upstairs. Nothing more to say than [`Lift.lean`](../lean/SquigglyLine/Networks/Lift.lean) says. |
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
| A linear autoencoder learns the principal directions of the data. | Baldi and Hornik 1989; Eckart and Young 1936 | The best low-rank approximation of a matrix, which needs more of the theory of singular values than the library has. |
| Neural collapse comes out of training. | Proved for a simplified model in the literature; here only that the simplex is the limit | The training path, even for the simplified model. |
| Dropout and weight decay under cross-entropy. | Wager, Wang and Liang 2013, to second order | The error is no longer linear in the outputs. |
| The error on new data is close to the error on the training data, for a model picked from a finite set. | Valiant 1984; the classical counting bound | A tail bound for a sum of independent terms, used once for every model in the set. The library has the pieces; not attempted. |
| The ideal denoiser points up the slope of the log of the data's density (Tweedie's formula). | Classical; here only that it is an average | Derivatives of a mixture of bell curves. |
| A wide random network, before training, is a Gaussian process. | Neal 1996; Lee et al. 2018 | Limits of wide random layers. |
| A few random directions keep all the distances between many points (Johnson–Lindenstrauss). | Classical | A concentration bound for random matrices. |

## Out of reach: nobody knows yet

These need new mathematics, or a statement precise enough to prove.

| What I want proved | What exists | What is in the way |
|---|---|---|
| How squiggly a network with random weights is, as a function of width, depth and weight scale. This is the original conjecture for networks. | `docs/open-problems.md`, item 1 | No known formula for the oscillation scale. |
| What happens when the lift moves. A network that learns features is choosing its own upstairs. Every fixed-kernel proof would need a version for it. | Theories for special cases | No general theory of feature learning. |
| Why the sharpness of a real network rises to `2 / η` and then stays there. | Observed: Cohen et al. 2021; here only the threshold | The kernel moves, and why it stops at the edge is not understood. |
| Grokking: why a network can start to generalise long after it fits. | Observed: Power et al. 2022; argued here from the clocks of spectral bias | No agreed statement to prove. |
| Why Adam beats plain gradient descent on transformers. | Observed | Not understood. |
| Whether flat minima generalise, and in what sense of flat. | [`Reparam.lean`](../lean/SquigglyLine/Supporting/Training/Reparam.lean) shows plain flatness cannot be the reason | No measure of flatness that survives rescaling and still predicts. |
| No hill between two trained networks once the neurons of one are relabelled. | Conjectured: Entezari et al. 2022; here the linear case | Open even for small networks. |
| That training a transformer finds heads that run gradient descent on the prompt, and what softmax attention with feed-forward layers computes. | Proved for linear attention in the literature; here only that one head can be one step | The softmax and the other layers. |
| Why the loss falls as a power of parameters and of data, and what sets the powers. | Measured: Kaplan et al. 2020; Hoffmann et al. 2022; here only the balance rule | The form of the loss is a measurement with no derivation. |
| A bound on test error that is tight enough to mean something for a real network. | Bounds exist and are mostly far too loose | Not known what quantity to bound with. |
| Why a network trained to remove noise makes new images and does not copy its training set. | Observed in diffusion models | Not understood. The ideal denoiser only averages its training set. |
| How many features a layer can hold in fewer dimensions, and how training lays them out (superposition). | Observed: Elhage et al. 2022; here the opposite bound for well-separated directions | No theory of the training side. |
| What normalising across a batch does. | `docs/open-problems.md`, item 21; here one example at a time | Each example's path depends on the others. |
| **Generalisation.** Why a network that can fit any labels does well on new data when the labels are real. | [`Capacity.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean) shows it can fit anything; [`Perceptron.lean`](../lean/SquigglyLine/Supporting/Training/Perceptron.lean) shows no learner is better on average over all labellings; here bias and variance, and one junk direction of benign overfitting | Nobody knows which property of real data and of training makes the fitted line the right one. The squiggly-line reading is that real labels vary gently and training takes the least travel, but that is a picture and not a theorem. |

At the far end is the question of why predicting the next word gives a model
that can do so much else. There is not yet a statement of it to prove.
