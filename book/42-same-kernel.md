# 42. Same kernel, same predictions

**In the repository:**
[`SameKernel.lean`](../lean/SquigglyLine/Supporting/NewInputs/SameKernel.lean),
note [`same-kernel.md`](../docs/supporting/new-inputs/same-kernel.md).
**You need:** chapters 9, 10 and 16.

## The idea

People who compare neural networks often compare their **kernels**: for
every pair of inputs, a number saying how alike the network finds them.
Chapter 10 showed that for a model linear in its weights, the kernel on
the training set decides every training error at every step. The weights
drop out.

The question for a new input is the same. Two models can look nothing
alike inside. One is a Fourier series, the other a ReLU network. They can
have different numbers of weights. If their kernels agree, do they make
the same prediction at a test point?

To answer for a test point you need one more row of numbers. The **test
row** says how alike the test point is to each training point. It is the
row the kernel would have if the test point were added to the table.

> If two models have the same kernel on the training set, the same test
> row, the same errors at the start and the same answer at the test
> point at the start, then they give the same answer at the test point
> after every step of gradient descent, and at the fit that training
> heads for.

## An example you can do by hand

There is one training point, with label 10, and both models start with
all weights at zero. The learning rate is 0.02.

- **Model A** has two weights. The training point has features `(3, 4)`.
  The test point has features `(1, 0)`. A model's answer is the features
  multiplied entry by entry with the weights, then added up.
- **Model B** has one weight. The training point has feature 5. The test
  point has feature 0.6.

The kernel on the training set is the features of the training point
against themselves. For A it is `3×3 + 4×4 = 25`. For B it is `5×5 = 25`.
The test row is the test features against the training features. For A it
is `1×3 + 0×4 = 3`. For B it is `0.6×5 = 3`. Same kernel, same test row.

**Step 1.** The error is 10. Model A adds `0.02 × 10 × (3, 4)` to its
weights, which is `(0.6, 0.8)`. Its answer at the training point is
`3×0.6 + 4×0.8 = 5`. Its answer at the test point is `1×0.6 + 0×0.8 =
0.6`. Model B adds `0.02 × 10 × 5 = 1` to its weight. Its answer at the
training point is `5×1 = 5`. At the test point it is `0.6×1 = 0.6`.

**Step 2.** The error is 5. Model A adds `(0.3, 0.4)` and is at
`(0.9, 1.2)`. Its test answer is 0.9. Model B adds `0.02 × 5 × 5 = 0.5`,
is at 1.5, and its test answer is `0.6×1.5 = 0.9`.

The weights are `(0.9, 1.2)` against `1.5`. The test answers are 0.9
against 0.9. The same rule produced both numbers, and the rule is
`0.02 × test_row × error`. Step 1 gives `0.02 × 3 × 10 = 0.6`. Step 2
gives `0.02 × 3 × 5 = 0.3`.

## The statement

First, what one step does to the answer at a test point.

```lean
theorem inner_gradientStep
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (weights : Weights)
    (features : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let stepped_weights :=
      TAKE_GRADIENT_STEP predict labels learning_rate weights
    let answer_after  := inner ℝ features stepped_weights
    let answer_before := inner ℝ features weights
    let test_row      := predict features  -- how alike the test point is to each training point
    let residual      := GET_RESIDUAL linear_predict labels weights
    let correction    := learning_rate * inner ℝ test_row residual
    answer_after = answer_before + correction := by
```

*Read aloud:* one gradient step moves the answer at a test point by the
learning rate times the test row matched against the current errors.

`inner ℝ a b` is the **inner product**: multiply the entries of `a` and
`b` in pairs and add. It is how a linear model turns features and weights
into an answer. `predict features` is the test row: the model applied to
the test point's features. The `residual` is the list of errors on the
training set, as in chapter 10. Neither `weights` nor `stepped_weights`
appears in the `correction`.

Now the main result.

```lean
theorem prediction_iterate_gradientStep_eq
    (same_kernel : ∀ vector,
      predict (adjoint predict vector)
        = other_predict (adjoint other_predict vector))
    (labels : Outputs)
    (learning_rate : ℝ)
    {weights : Weights}
    {other_weights : OtherWeights}
    (same_start_residual :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights
        = GET_RESIDUAL (other_predict : OtherWeights →ₗ[ℝ] Outputs) labels
            other_weights)
    {features : Weights}
    {other_features : OtherWeights}
    (same_test_row : predict features = other_predict other_features)
    (same_start_answer :
      inner ℝ features weights = inner ℝ other_features other_weights)
    (step_count : ℕ) :
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count] weights
    let other_trained_weights :=
      (TAKE_GRADIENT_STEP other_predict labels learning_rate)^[step_count]
        other_weights
    let answer       := inner ℝ features trained_weights
    let other_answer := inner ℝ other_features other_trained_weights
    answer = other_answer := by
```

*Read aloud:* two models with the same kernel, the same test row, the
same starting errors and the same starting answer at the test point
give the same answer there after any number of steps.

The two models have weight spaces `Weights` and `OtherWeights` that need
not be alike. `same_kernel` says that applying the model to its own
transpose (`adjoint`, chapter 10) gives the same result in both. The
notation `^[step_count]` means "apply the step `step_count` times".

A third result, `prediction_kernelFit_eq`, says the same about the fit
that training heads for: start weights plus the transpose applied to the
inverse kernel acting on the errors. Its answer at the test point is the
same in both models.

## Why it is true

The first theorem is three rewrites. A gradient step adds a multiple of
the transpose of the model, applied to the errors, to the weights. The
answer at a test point is an inner product with the weights, so it
changes by an inner product with that addition. Moving the transpose
across the inner product turns it into the model applied to the test
features. That is the test row. The weights have disappeared.

The second theorem is an induction on the number of steps. At zero steps
the claim is the assumption `same_start_answer`. Suppose the two answers
agree after some steps. The next step adds the same correction to both:
the test rows are equal by `same_test_row`, and the errors are equal
because chapter 10 showed that models with the same kernel go through
the same errors (`residual_iterate_gradientStep_eq`). Equal answers plus
equal corrections are equal answers.

The third theorem needs no induction. The fit is the start plus one
fixed correction, and the correction depends only on the test row and the
errors.

## What it explains

The **platonic representation hypothesis** says that different networks,
trained in different ways and even on different kinds of data, drift
towards the same way of representing the world, and that "the same way"
can be measured with kernels (**recalled**: Huh, Cheng, Wang and Isola
2024). The hypothesis is a claim about real networks. It is not proved
here.

What this chapter adds is what the hypothesis would buy. Once two models
have the same kernel, architecture, width and the values of the weights
are all invisible, for training (chapter 10) and now for prediction as
well. "These networks have the same representation" and "these networks
are the same learner" become one statement, not two.

## How this meets the squiggly line

This is the **kernel** idea of chapter 10 applied to a new point. The
nearest fit of chapter 9 is the end of the trip, and the third theorem
says the answer at the test point at the end of that trip is the same for
both models. Chapter 10 already said that their trips are equally long
(`travel_eq_of_kernel_eq`). Together: the same trip, the same arrival
point as seen from the test point.

## What is not shown

The proofs are for models **linear in their weights**, with a **fixed
kernel**.

- **That kernels converge.** This is the hypothesis itself. It is
  **open**.
- **Nearly the same kernel.** Real kernels would agree only roughly.
  That nearly equal kernels give nearly equal predictions is expected and
  is **open** here.
- **Kernels that move.** A deep network's kernel changes while it
  trains. The result is for kernels that stay fixed. **open**.

## Check yourself

1. In the example, what is the answer of both models at the test point
   after step 3, if the learning rate stays 0.02?
2. Model B is changed so that its test feature is 1.2, with everything
   else as before. Does the theorem still say its test answers equal
   those of model A?
3. Model A is given a thousand weights, still with the same kernel and
   the same test row as model B. What can you say about their answers at
   the fit that training heads for?

**Answers.** (1) The error is 10, then 5, then 2.5, so it halves each
step, since `1 − 0.02 × 25 = 0.5`. The correction at step 3 is `0.02 × 3 × 2.5 =
0.15`, so the answer goes from 0.9 to 1.05 in both models. (2) No. The
test row of B would be `1.2×5 = 6`, which is not the 3 of model A, so
`same_test_row` fails, and the first step already differs: `0.02 × 6 ×
10 = 1.2` against 0.6. (3) They are equal, by `prediction_kernelFit_eq`,
because the number of weights does not appear in its assumptions.

Previous: [41. Counting](41-counting.md) · Next: [43. Bias and variance](43-bias-and-variance.md)
