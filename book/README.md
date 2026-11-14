# The Squiggly Line Theorem: A Guided Tour of the Proofs

A book for people who want to understand the proofs in this repository
and do not know where to start. It goes through them in the order of the
ideas, from one picture to the theorem, and then on to what the same
tools say about neural networks.

You need to be able to read Python and to remember school mathematics.
You do not need to know Lean.

- **Read it here:** start with the [preface](00-preface.md).
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

### Part III. The same tools elsewhere

| Chapter | What you learn |
|---|---|
| [13. One factor, again and again](13-one-factor.md) | Spectral bias, the largest learning rate, weight decay, Adam. |
| [14. Three ways to combine slope](14-combining-slope.md) | Stacking multiplies it, averaging never raises it, a skip adds one. |
| [15. Averages](15-averages.md) | Attention, in-context learning, diffusion, and why counting is hard. |
| [16. New inputs](16-new-inputs.md) | Benign overfitting, pruning, forgetting, adversarial examples. |
| [17. What is not here](17-what-is-not-here.md) | Where the proofs stop, and how to keep reading. |

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
