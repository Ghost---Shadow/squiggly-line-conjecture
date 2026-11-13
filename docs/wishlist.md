# Wishlist

**Proofs:** [`Depth.lean`](../lean/SquigglyLine/Networks/Depth.lean), [`Lift.lean`](../lean/SquigglyLine/Networks/Lift.lean), [`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean), [`Capacity.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean), [`Mixtures.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Mixtures.lean), [`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean), [`Perceptron.lean`](../lean/SquigglyLine/Supporting/Training/Perceptron.lean), [`Reparam.lean`](../lean/SquigglyLine/Supporting/Training/Reparam.lean).

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
[`supporting-proofs.md`](supporting-proofs.md#paper-by-paper), paper by paper. Each row here
has a status.

- **next**: looks within reach of the tools already here. Worked through in
  order. 0 are marked as of 14 Nov 2026, from a second pass over the list
  made once the first one was finished. AdamW and RMSNorm go first. The
  list is frozen for this round.
- **out of reach**: needs mathematics or library support that is missing.
  The last two sections say what is in the way.

The papers and years are recalled from memory and have not been checked.

## Slope

| Paper or idea | In squiggly terms | Status |
|---|---|---|

## Nearness

| Paper or idea | In squiggly terms | Status |
|---|---|---|

## Travel

| Paper or idea | In squiggly terms | Status |
|---|---|---|

## The kernel and the lift

| Paper or idea | In squiggly terms | Status |
|---|---|---|

## Folds

| Paper or idea | In squiggly terms | Status |
|---|---|---|

## Averages

| Paper or idea | In squiggly terms | Status |
|---|---|---|
| Where a transformer makes its squiggle | Attention is an average, so it cannot push tokens apart. It can still be steep as a function of its input: a gate adds slope through the spread of what it blends, times how fast the gate changes. Folds come only from the feed-forward block. | Argued from [`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean), [`Mixtures.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Mixtures.lean) and [`Depth.lean`](../lean/SquigglyLine/Networks/Depth.lean) |
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
| How to scale the weights and step sizes with width so that every layer keeps learning features (maximal update parametrisation). | Yang and Hu 2021; here only that rescaling changes flatness and travel and leaves the line alone ([`Reparam.lean`](../lean/SquigglyLine/Supporting/Training/Reparam.lean)) | Limits of wide random layers after a training step. |
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
