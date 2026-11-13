# Insights: what the proofs have in common

**Proofs:** [`Compression.lean`](../lean/SquigglyLine/Theorem/Compression.lean), [`Lift.lean`](../lean/SquigglyLine/Networks/Lift.lean), [`RadialBasis.lean`](../lean/SquigglyLine/Networks/RadialBasis.lean), [`RandomFourier.lean`](../lean/SquigglyLine/Networks/RandomFourier.lean), [`Activations.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Activations.lean), [`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean), [`AttentionRate.lean`](../lean/SquigglyLine/Supporting/NetworkShape/AttentionRate.lean), [`Convolution.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean), [`Gain.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Gain.lean), [`Mixtures.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Mixtures.lean), [`NetworkSlope.lean`](../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean), [`Residual.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Residual.lean), [`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean), [`Mixing.lean`](../lean/SquigglyLine/Supporting/NewInputs/Mixing.lean), [`AdamW.lean`](../lean/SquigglyLine/Supporting/Training/AdamW.lean), [`CrossEntropy.lean`](../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean), [`GanGame.lean`](../lean/SquigglyLine/Supporting/Training/GanGame.lean), [`Optimisers.lean`](../lean/SquigglyLine/Supporting/Training/Optimisers.lean), [`Regularisers.lean`](../lean/SquigglyLine/Supporting/Training/Regularisers.lean), [`SpectralBias.lean`](../lean/SquigglyLine/Supporting/Training/SpectralBias.lean), [`WeightDecay.lean`](../lean/SquigglyLine/Supporting/Training/WeightDecay.lean).

Notes from 14 Nov 2026, written after going through all 81 Lean files and
counting how they use each other. These are readings of the proofs. None is
a new theorem. Each says which files it is read from.

## 1. One factor, applied again and again

The most common statement in the repository has this shape: one step
multiplies something by a factor, so `n` steps multiply it by the factor to
the power `n`. The proof is always an induction, and there are about 40 of
them. The method is ordinary. What is worth noticing is that the same
one-line step turns up in places that are usually taught as separate
subjects.

| Where | The factor | File |
|---|---|---|
| Gradient descent, one direction | `1 − η λ` | [`SpectralBias.lean`](../lean/SquigglyLine/Supporting/Training/SpectralBias.lean) |
| A learning-rate schedule | the product of `1 − η_t λ` | [`Optimisers.lean`](../lean/SquigglyLine/Supporting/Training/Optimisers.lean) |
| Weight decay, AdamW | `1 − η μ` | [`WeightDecay.lean`](../lean/SquigglyLine/Supporting/Training/WeightDecay.lean), [`AdamW.lean`](../lean/SquigglyLine/Supporting/Training/AdamW.lean) |
| Diffusion noising | `1 − β` | [`Mixing.lean`](../lean/SquigglyLine/Supporting/NewInputs/Mixing.lean) |
| Value updates | `γ` | [`Gain.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Gain.lean) |
| LSTM memory | the forget gate | [`Residual.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Residual.lean) |
| Sigmoid layers | `1/4` | [`Activations.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Activations.lean) |
| Attention alone | `1 − exp(−2B)` | [`AttentionRate.lean`](../lean/SquigglyLine/Supporting/NetworkShape/AttentionRate.lean) |
| Graph networks | `1 − n m` | [`Mixing.lean`](../lean/SquigglyLine/Supporting/NewInputs/Mixing.lean) |
| Two players stepping together | `1 + η²` | [`GanGame.lean`](../lean/SquigglyLine/Supporting/Training/GanGame.lean) |

Training, depth, time and noise are the same calculation. What matters each
time is whether the factor is below one (the thing fades), exactly one (it
is carried), or above one (it blows up). Skips, open gates and
normalisation are all ways to hold the factor at one.

## 2. Three ways to combine slope

- **Stacking multiplies it.** Layers, strides and squeezes
  ([`NetworkSlope.lean`](../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean), [`Compression.lean`](../lean/SquigglyLine/Theorem/Compression.lean), [`Convolution.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean)).
- **Averaging never raises it.** Ensembles, pooling, augmentation
  ([`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean), [`Activations.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Activations.lean), [`Mixing.lean`](../lean/SquigglyLine/Supporting/NewInputs/Mixing.lean)).
- **A skip adds one.** Residual layers and the LSTM cell ([`Residual.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Residual.lean)).

Every result about architecture in the repository is one of these three. So
squiggle can only come from stacking pieces that are steep or that fold.

## 3. Frequency, width, stride and temperature are one dial

[`Compression.lean`](../lean/SquigglyLine/Theorem/Compression.lean) is used for the frequency of a sine, for the width of a
bump (as `1 / width`, in [`RadialBasis.lean`](../lean/SquigglyLine/Networks/RadialBasis.lean)) and for stride
([`Convolution.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean)). Temperature divides the slope of the scores in the
same way ([`NetworkSlope.lean`](../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean)). [`RandomFourier.lean`](../lean/SquigglyLine/Networks/RandomFourier.lean) shows that the Fourier
lift and the bump are one kernel on average. The trade of the theorem
(closer, steeper by the same factor, no better in loss) applies to all four.

## 4. A loss either stops asking for slope or never does

A hard label has no best score. A soft label has a finite one
([`CrossEntropy.lean`](../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean)). That one fact is behind label smoothing,
distillation and mixup ([`Regularisers.lean`](../lean/SquigglyLine/Supporting/Training/Regularisers.lean)), and behind the critic of a
GAN, which is finite where real and made data overlap and unbounded where
they do not ([`GanGame.lean`](../lean/SquigglyLine/Supporting/Training/GanGame.lean)).

## 5. For a linear model, the two kinds of regulariser are one

Regularisers sort into charges on slope (noise on the input, adversarial
training, a slope-one critic) and floors on travel (weight decay, early
stopping, dropout, lasso). The proofs say more. Noise on the input adds
`σ² w²` to the loss ([`Regularisers.lean`](../lean/SquigglyLine/Supporting/Training/Regularisers.lean)), which is exactly weight decay.
For a model linear in both its input and its weights, the weight is the
slope, so the two families are the same. They come apart only in a deep
network. **argued**

## 6. Attention cannot spread tokens, and can still be steep

[`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean) proves that attention is an average, so its outputs stay
inside the region its inputs span. [`Mixtures.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Mixtures.lean) proves that a gate adds
slope through the spread of what it blends, times how fast the gate
changes. Attention whose scores depend on the input is such a gate. So
attention cannot push tokens apart, but as a function of its input it can
be steep, and it is steepest where the tokens differ most and the scores
change fastest. An earlier line in the wishlist said attention "adds no
turn". That was too strong and has been corrected.

## 7. Two trees and a thin bridge

Only 130 of the 714 definitions and theorems are used outside the file they
are in. The ones used most are:

- **Geometry:** the nearest distance and the vertical error (12 and 10
  files), and one theorem, the slope sandwich (8 files).
- **Training:** the residual (18 files) and the gradient step (13 files).

Few files use both. [`Lift.lean`](../lean/SquigglyLine/Networks/Lift.lean) is the main bridge between how squiggly the
line is and how far the weights travel. That bridge is the original
conjecture, and it is the thinnest part of the repository. The theorem for
sines is not used by any other file.

## What the proofs do not contain

Nearly every proof is algebra, with little analysis. Everything hard sits
behind the same assumption: a fixed kernel, or a model linear in its
weights. So what is here is the bookkeeping of deep learning with one piece
missing, which is what happens when the features move. The same piece is
behind most of the rows the wishlist marks as out of reach, among them how
to scale the weights and step sizes with width so that the features do
move (**recalled**: Yang and Hu 2021).
