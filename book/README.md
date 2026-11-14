# The Squiggly Line Theorem: A Guided Tour of the Proofs

*By Claude and Souradeep Nanda.*

A book for people who want to understand the proofs in this repository
and do not know where to start. It goes through them in the order of the
ideas, from one picture to the theorem, and then on to what the same
tools say about neural networks.

You need to be able to read Python and to remember school mathematics.
You do not need to know Lean.

- **Read it here:** start with the [preface](00-preface.md).
- **Read it on the web:** [https://ghost---shadow.github.io/squiggly-line-theorem/](https://ghost---shadow.github.io/squiggly-line-theorem/)
- **Read it as a PDF:** a PDF is built for every tagged version and
  attached to the
  [release](https://github.com/Ghost---Shadow/squiggly-line-theorem/releases/latest).
- **Cite it:** see [how to cite this book](how-to-cite.md).

## Contents

[Preface](00-preface.md): who the book is for, and three ways through it.

### Part I. The theorem

| Chapter | What you learn |
|---|---|
| [1. Two distances](01-two-distances.md) | The picture, the conjecture as three claims, and the two meanings of "close". |
| [2. How to read a proof here](02-reading-a-proof.md) | Enough Lean to read every statement in the repository. |
| [3. Slope](03-slope.md) | The slope sandwich: a curve buys nearness with slope and nothing else. |
| [4. Nearness](04-nearness.md) | What "squiggly" means as a number, and the small shift that fits anything. |
| [5. What the loss cannot see](05-the-blind-loss.md) | The loss at the start reads one input at a time, so it is blind to squiggle. |
| [6. The theorem for sines](06-the-sine.md) | The three results put together on one family of curves. |
| [7. The theorem for any function](07-any-function.md) | Nothing was special about the sine: squeeze any function. |

### Part II. Networks

| Chapter | What you learn |
|---|---|
| [8. Folds](08-folds.md) | How depth buys squiggle, and why width cannot keep up. |
| [9. Travel](09-travel.md) | A bigger model does not start lower. It starts nearer to a fit. |
| [10. The kernel](10-the-kernel.md) | Training sees only the kernel; one factor per step; double descent. |
| [11. The lift](11-the-lift.md) | Squiggly below, flat above: Fourier features, bumps and positions. |
| [12. Layers as polarizers](12-polarizers.md) | Why many small turns lose almost nothing, and one big turn loses all. |

### Part III. The same tools elsewhere: a map

Four short chapters. Each is the map of one of the parts that follow.

| Chapter | What you learn |
|---|---|
| [13. One factor, again and again](13-one-factor.md) | Spectral bias, the largest learning rate, weight decay, Adam. |
| [14. Three ways to combine slope](14-combining-slope.md) | Stacking multiplies it, averaging never raises it, a skip adds one. |
| [15. Averages](15-averages.md) | Attention, in-context learning, diffusion, and why counting is hard. |
| [16. New inputs](16-new-inputs.md) | Benign overfitting, pruning, forgetting, adversarial examples. |

### Part IV. Training, proof by proof

How the tools connect to what is known about training. One topic per
chapter, in the order to read them.

| Chapter | What you learn |
|---|---|
| [17. The shortest trip](17-the-shortest-trip.md) | Gradient descent reaches the nearest fit: its implicit bias. |
| [18. Strong directions first](18-strong-directions-first.md) | Spectral bias, and why stopping early keeps out noise. |
| [19. The largest step](19-the-largest-step.md) | The edge of stability, schedules, momentum. |
| [20. Weight decay and early stopping](20-weight-decay-and-early-stopping.md) | Two habits that put the same floor under every direction. |
| [21. Dropout, noise and other regularisers](21-dropout-and-noise.md) | Dropout, lasso, input noise, mixup, distillation. |
| [22. Batches, small steps and budgets](22-batches-steps-and-budgets.md) | The linear scaling rule, warm-up, and how to split a compute budget. |
| [23. Adam, AdamW and clipping](23-adam-and-clipping.md) | What changes when the step ignores the size of the gradient. |
| [24. Symmetry: flat minima and normalisation](24-symmetry.md) | Why sharpness is slippery, and what normalisation does to the weights. |
| [25. Classification](25-classification.md) | Softmax and cross-entropy run on the same machine as squared error. |
| [26. The perceptron, XOR and no free lunch](26-the-perceptron.md) | The oldest results of the field, in the terms of this book. |
| [27. Two players: the GAN game](27-two-players.md) | Why training two networks against each other is unstable. |

### Part V. Architecture, proof by proof

| Chapter | What you learn |
|---|---|
| [28. The slope of a network](28-the-slope-of-a-network.md) | Layers multiply slope; adversarial examples; temperature. |
| [29. The distance field](29-the-distance-field.md) | Signed distance functions and the eikonal equation. |
| [30. Signals through depth](30-signals-through-depth.md) | Vanishing and exploding gradients, and He initialisation. |
| [31. Skips and normalisation](31-skips-and-normalisation.md) | Residual layers, the LSTM cell, and why they hold the factor at one. |
| [32. Depth against width](32-depth-against-width.md) | Depth separation and universal approximation. |
| [33. Convolution](33-convolution.md) | Local layers, stride and what a window cannot see. |
| [34. Capacity and compression](34-capacity-and-compression.md) | How much a model can store, bottlenecks and code length. |
| [35. The landscape](35-the-landscape.md) | Mode connectivity and neural collapse. |

### Part VI. Averages, proof by proof

| Chapter | What you learn |
|---|---|
| [36. Attention](36-attention.md) | Attention as an average, how it merges tokens, in-context learning. |
| [37. Ensembles and the ideal denoiser](37-ensembles-and-the-denoiser.md) | Why ensembles help, and what a diffusion model is aiming at. |
| [38. Mixing](38-mixing.md) | Graph networks, noise schedules, augmentation and guidance. |
| [39. Hard choices and temperature](39-hard-choices-and-temperature.md) | The straight-through trick, cold softmax, Hopfield recall, codebooks. |
| [40. Neighbours](40-neighbours.md) | Nearest neighbours, k-means and contrastive learning. |
| [41. Counting](41-counting.md) | Why a count is the worst thing to ask of an average. |

### Part VII. New inputs, proof by proof

| Chapter | What you learn |
|---|---|
| [42. Same kernel, same predictions](42-same-kernel.md) | When two different models are one learner. |
| [43. Bias and variance](43-bias-and-variance.md) | The oldest trade-off, and where regularisation sits on it. |
| [44. Benign overfitting](44-benign-overfitting.md) | How fitting noise exactly can be harmless. |
| [45. Pruning and forgetting](45-pruning-and-forgetting.md) | Lottery tickets and catastrophic forgetting. |
| [46. The dimpled manifold](46-the-dimpled-manifold.md) | Adversarial examples as a step off the data. |

### Closing

| Chapter | What you learn |
|---|---|
| [47. What is not here](47-what-is-not-here.md) | Where the proofs stop, and how to keep reading. |

### Back matter

- [Glossary](glossary.md): every name the book uses, with the chapter
  that introduces it.
- [How to cite this book](how-to-cite.md)

## Building the PDF yourself

The PDF is made by [`pdf/build.sh`](pdf/build.sh) with pandoc and
XeLaTeX. The workflow in
[`.github/workflows/book.yml`](../.github/workflows/book.yml) runs it on
every change to the book and attaches the result to a release whenever a
tag starting with `v` is pushed.

```bash
bash book/pdf/build.sh
```

## Building the web version

The web version is made by [`html/build.sh`](html/build.sh) with pandoc and
the filter [`html/site.lua`](html/site.lua). It writes a static site to
`book/build/site/`. The `pages` job in
[`.github/workflows/book.yml`](../.github/workflows/book.yml) builds it and
publishes it on GitHub Pages whenever a tag starting with `v` is pushed.

```bash
bash book/html/build.sh
```
