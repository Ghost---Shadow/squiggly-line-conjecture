# Cross-entropy: classification in the same picture

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/Training/CrossEntropy.lean` unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

Every other note here trains on squared error. Almost every network in use
trains on something else: a **softmax** turns its scores into shares that add
up to one, and **cross-entropy** scores those shares against the label. With
two classes the softmax is a **sigmoid**.

So the question is how much of the picture built on squared error survives.
Most of it does, and the reason is one line.

## The one line: prediction minus label

Squared error pushes each output by `output − label`.

Cross-entropy pushes each score by `prediction − label`, where the prediction
is the softmax of the scores (**proved**: `hasDerivAt_crossEntropy` for any
number of classes, `hasDerivAt_logLoss` for two).

The form is the same. The only change is that the output is read through the
softmax before the label is taken away. The softmax itself is a set of
positive shares that add up to one (**proved**: `softmax_pos`, `sum_softmax`).

This is no accident of these two losses. In statistics both are generalized
linear models with their natural link, and every such model has this form
(**recalled**).

## What survives

Take a model that is linear in its weights, and let the loss push the outputs
by any rule at all: `err(outputs)`.

- **The same kernel.** One step moves the outputs by the kernel applied to
  the error (**proved**: `map_errorStep`). Squared error is the case
  `err = output − label` (**proved**: `gradientStep_eq_errorStep`).
  Cross-entropy is the case `err = prediction − label` (**proved**:
  `hasDerivAt_totalLogLoss` and `inner_adjoint_eq_sum`, for two classes).
- **Same kernel, same learner.** Two models with the same kernel that start
  from the same outputs have the same outputs after every step, whatever the
  loss (**proved**: `map_iterate_errorStep_eq`). So the Fourier model and the
  ReLU model of `docs/networks/fourier-and-relu-bridge.md` are the same
  classifier too.
- **Least travel.** Training never leaves the directions of the features. So
  after any number of steps, no weights that give the same outputs are nearer
  to the start (**proved**: `iterate_errorStep_is_nearest`).
- **One valley.** On a straight line between two settings of the weights, the
  cross-entropy loss stays below the straight line between the two end losses
  (**proved**: `totalLogLoss_along_le`). So there is no hill between them
  (**proved**: `totalLogLoss_along_le_max`).
- **A budget of movement.** Going the share `t` of the way to better weights
  removes at least the share `t` of the gap in loss (**proved**:
  `le_totalLogLoss_sub_along`). For squared error the error left was exactly
  `1 − t`. Here it is a bound.

## What changes

For a yes-or-no label there is no best score. The loss is never zero, and a
larger score always has a smaller loss (**proved**: `logLoss_one_pos`,
`strictAnti_logLoss_one`). The same holds with many classes: no share
reaches one, so the loss of a sure label is never zero (**proved**:
`softmax_lt_one`, `crossEntropy_single_pos`).

So a classifier that can separate its training data never finishes. Its loss
keeps falling as its scores grow, and its scores grow only if its weights do.
There is no fit at a finite distance, and "travel to the nearest fit" has no
meaning. What does have meaning is the travel to a given loss.

Three things follow (**argued**).

- **Training longer makes the model more confident, right or wrong.** That is
  the known drift toward overconfidence (**recalled**: Guo et al. 2017).
- **Early stopping and weight decay do real work here.** With squared error
  they cut off weak directions. With cross-entropy they are also what stops
  the weights growing without end.
- **Label smoothing gives the loss a floor.** With a label of 0.9 in place of
  1 the best score is finite, and the weights can stop.

## How this meets the squiggly line

The theorem says a line gets near the data by being steep. Cross-entropy is a
loss that never stops asking. For a model linear in its weights, doubling the
weights doubles every score and doubles the slope of the function. A
classifier trained for long on labels it can separate therefore grows steeper
without limit (**argued**). The cross-entropy loss is the pressure toward a
squigglier line, and the three habits above are what hold it back.

The kernel and the least-travel statements are unchanged, so the rest of the
supporting material applies to classifiers with "error" read as prediction
minus label.

## What is not shown

- **Speed.** Under squared error each direction of the kernel shrinks at its
  own fixed rate (`SpectralBias.lean`, `EdgeOfStability.lean`). Under
  cross-entropy the error is not a linear function of the outputs, so those
  rates change as training goes. **open** here.
- **Where the weights go.** On separable data the direction of the weights
  tends to the widest-margin one (**recalled**: Soudry et al. 2018). Not
  formalised.
- **Many classes on a model.** The model-level statements are for two
  classes. The one-example statement is for any number.
- **The three consequences above** are argued from the proved facts and are
  not themselves in Lean.
- **Deep networks.** The kernel is fixed, as everywhere in these notes.
  **open**
