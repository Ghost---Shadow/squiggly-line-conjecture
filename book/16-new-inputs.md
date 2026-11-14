# 16. New inputs

**In the repository:** the files in
[`Supporting/NewInputs/`](../lean/SquigglyLine/Supporting/NewInputs),
with notes in
[`docs/supporting/new-inputs/`](../docs/supporting/new-inputs).
**You need:** chapters 9 and 10.
**The proofs, one by one:** part VII, chapters 42 to 46.

## The idea

So far the book has asked how a model comes to fit its training data.
The question that matters in practice is what the fitted model does at
an input it has never seen.

For a model with a fixed kernel, the tools of Part II answer a good deal
of it. Three ideas do the work.

- Gradient descent reaches the **nearest** fit (chapter 13).
- A fit near the start is **tame** everywhere (chapter 10).
- What happens at a new input goes through the **kernel** between that
  input and the data.

## What follows

| Known puzzle | In the terms of this book | Proof |
|---|---|---|
| Models of different designs end up alike. | Two models with the same kernel give the same answer at a test point after every step, whatever their weights. | [`SameKernel`](../lean/SquigglyLine/Supporting/NewInputs/SameKernel.lean) |
| Regularise more and you underfit, less and you overfit. | The expected squared error at a new input is bias squared plus variance. A floor under every strength raises the first and lowers the second. | [`BiasVariance`](../lean/SquigglyLine/Supporting/NewInputs/BiasVariance.lean) |
| Fitting noisy labels exactly is often harmless in a big model. | Spare features take over the noise. With junk features of strength `junk_strength`, the damage at a new input is capped by `1 / junk_strength`. | [`BenignOverfitting`](../lean/SquigglyLine/Supporting/NewInputs/BenignOverfitting.lean) |
| Most weights can be pruned. | Pruning subtracts a kernel, which makes training slower and the fit farther. It costs nothing along directions where the dropped weights had no strength. | [`Pruning`](../lean/SquigglyLine/Supporting/NewInputs/Pruning.lean) |
| Fine-tune gently, or the model forgets. | A step on a new task changes the old errors only through the kernel between the two tasks, and by at most the new task's travel. | [`Forgetting`](../lean/SquigglyLine/Supporting/NewInputs/Forgetting.lean) |
| A tiny change to an input can fool a model. | A function can keep its loss on the real data and still be one small step from any label, straight off the surface the data lies on. | [`Dimple`](../lean/SquigglyLine/Supporting/NewInputs/Dimple.lean) |
| A model with `m` weights memorises about `m` things. | A model linear in `m` weights fits arbitrary labels on at most `m` points. | [`Capacity`](../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean) |
| No learner is best on every problem. | With no pattern in the labels, any guess at an unseen input is right on half of all labellings. | [`Perceptron`](../lean/SquigglyLine/Supporting/Training/Perceptron.lean) |

## Two of them, a little slower

**Benign overfitting.** A model with far more features than data points
fits its noisy labels exactly, and still predicts well. How? The nearest
fit spreads the noise over many spare features, each of which matters
very little at a new input. The more spare strength there is, the
smaller the damage. This is the right-hand side of the double descent
curve of chapter 10, where the test error comes back down.

**The dimple.** Picture the real data lying on a thin sheet inside a big
space. A model can be correct on the whole sheet and still have a small
dent just off it, where its answer is anything you like. The training
loss never visits the dent, so by chapter 5 the loss cannot see it. An
adversarial example is a step off the sheet into a dent. This is the
two distances of chapter 1 again: near in space, and not counted in the
loss.

## The honest limit

Why do real networks do well on new inputs? The repository's wishlist
lists that under "nobody knows yet". What is proved here is what a fit
does **given** a fixed kernel. Which kernel a real network ends up with,
after its features have moved, is the part that would explain
generalisation, and it is not here.

## Check yourself

1. Two teams train different models that happen to have the same
   kernel, on the same data, with the same learning rate. Team A's
   model has ten times as many weights. Whose test predictions are
   better?
2. You fine-tune on a new task whose inputs have no overlap at all,
   through the kernel, with the old task's inputs. What happens to the
   old task?
3. A model linear in 50 weights is asked to fit random labels on 80
   points. Can it?

**Answers.** (1) Neither. They are the same at every step. (2) Nothing.
The old errors change only through the kernel between the two tasks,
and that is zero. (3) Not in general. It can fit arbitrary labels on at
most 50 points.

Previous: [15. Averages](15-averages.md) · Next: [17. The shortest trip](17-the-shortest-trip.md)
