# 24. Symmetry: flat minima and normalisation

**In the repository:**
[`Reparam.lean`](../lean/SquigglyLine/Supporting/Training/Reparam.lean),
[`Symmetry.lean`](../lean/SquigglyLine/Supporting/Training/Symmetry.lean),
[`RmsNorm.lean`](../lean/SquigglyLine/Supporting/NetworkShape/RmsNorm.lean),
notes [`flat-minima.md`](../docs/supporting/training/flat-minima.md) and
[`symmetry.md`](../docs/supporting/training/symmetry.md).
**You need:** chapters 9, 10 and 13.

## The idea

People who train models like flat minima: a wide valley of the loss is
said to generalise better than a narrow one (**recalled**: Hochreiter and
Schmidhuber 1997; Keskar et al. 2017). There is a known objection. You can
rewrite the same network with rescaled parameters, and make any valley as
wide or narrow as you like, without changing one output (**recalled**:
Dinh, Pascanu, Bengio and Bengio 2017).

Behind both is one fact. The line lives in function space and the weights
live in weight space, and many settings of the weights draw the same
line. A change to the weights that leaves the line alone is a
**symmetry**. The loss has no slope along it, so training does not move
that way.

> Rescaling a model by `scale` keeps every output, makes the loss
> flatter by `scale²` and the nearest fit farther by `|scale|`. For
> a loss that ignores the scale of the weights, the gradient is at
> right angles to the weights, so training only makes them longer.

## An example you can do by hand

**Rescaling.** A model has output `2 × weight`. The label is 4 and the
start is 0. The fit is weight 2, so the travel is 2. Rescale by 10: the
model is now `0.2 × weight`, the fit is weight 20 and the travel is 20,
ten times farther. The kernel was `2 × 2 = 4` and is now
`0.2 × 0.2 = 0.04`, a hundred times weaker. Strength times travel
squared is `4 × 2² = 16` before and `0.04 × 20² = 16` after, and the
error squared is `4² = 16`.

**Right angles.** Weights `(3, 4)` have length 5. The vector `(4, −3)`
has dot product `12 − 12 = 0` with them. Step with `learning_rate = 0.1`
along it: the weights become `(2.6, 4.3)`, with squared length
`6.76 + 18.49 = 25.25`. That is `25 + 0.1² × 25`, the old squared length
plus the squared step.

**Balance.** The model is `first_weight × second_weight`, the label is 0,
`first_weight = 3`, `second_weight = 1` and `learning_rate = 0.1`. The
error is 3. The weights become `3 − 0.1 × 3 × 1 = 2.7` and
`1 − 0.1 × 3 × 3 = 0.1`. The imbalance `first² − second²` goes from
`9 − 1 = 8` to `7.29 − 0.01 = 7.28`, which is 8 times
`1 − 0.1² × 3² = 0.91`.

## The statement

```lean
theorem flatter_is_farther
    {scale : ℝ}
    (scale_ne_zero : scale ≠ 0)
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (start_weights : Weights) :
    let rescaled_predict : LinearPredictor Weights Outputs :=
      RESCALE scale predict
    let linear_predict : LinearPredictor Weights Outputs := predict
    let error_is_kept :=
      GET_RESIDUAL rescaled_predict labels (scale • start_weights)
        = GET_RESIDUAL linear_predict labels start_weights
    let loss_is_flatter := ∀ move : Weights,
      ‖RESCALE scale predict move‖ ^ 2 = ‖predict move‖ ^ 2 / scale ^ 2
    let fit_is_farther :=
      GET_TRAVEL rescaled_predict labels (scale • start_weights)
        = |scale| * GET_TRAVEL linear_predict labels start_weights
    error_is_kept ∧ loss_is_flatter ∧ fit_is_farther := by
```

*Read aloud:* rescaling by `scale` keeps the error, divides the
curvature of the loss by `scale²`, and multiplies the travel by
`|scale|`.

`RESCALE scale predict` is the model with its parameters in other units:
the new parameters are `scale` times the old ones, and are divided by
`scale` before use. `∧` means "and". The three parts are
`residual_rescale`, `norm_rescale_sq` and `travel_rescale`. The same
file shows `kernel_rescale` (the kernel is weaker by `scale²`) and
`gradientStep_rescale`: a step of the rescaled model with step size
`learning_rate` is a step of the old model with step size
`learning_rate / scale²`.

```lean
theorem norm_sq_sub_smul_of_inner_eq_zero
    {weights gradient : Weights}
    (gradient_is_at_right_angles : inner ℝ gradient weights = 0)
    (learning_rate : ℝ) :
    let weights_after_step  := weights - learning_rate • gradient  -- one step of gradient descent
    let step_length_squared := learning_rate ^ 2 * ‖gradient‖ ^ 2
    ‖weights_after_step‖ ^ 2 = ‖weights‖ ^ 2 + step_length_squared := by  -- Pythagoras: the step is at right angles
```

*Read aloud:* a step at right angles to the weights adds exactly the
squared step to their squared length.

`inner ℝ gradient weights` is the dot product, and `‖ ‖` is length. The
theorem `inner_gradient_self_eq_zero` says that a **scale invariant**
loss (`IS_SCALE_INVARIANT`: unchanged when all weights are multiplied by
a positive number) has a gradient at right angles to the weights. Then
`norm_le_norm_sub_smul` says the weights never get shorter.

```lean
theorem balance_after_step
    (first_weight second_weight label learning_rate : ℝ) :
    let error := GET_PRODUCT_ERROR first_weight second_weight label
    let first_weight_after :=
      TAKE_STEP_ON_FIRST_WEIGHT first_weight second_weight label learning_rate
    let second_weight_after :=
      TAKE_STEP_ON_SECOND_WEIGHT first_weight second_weight label learning_rate
    let imbalance_before := first_weight ^ 2 - second_weight ^ 2  -- zero when the two layers have the same size
    let imbalance_after  := first_weight_after ^ 2 - second_weight_after ^ 2
    let shrink_factor    := 1 - learning_rate ^ 2 * error ^ 2  -- no first power of `learning_rate`: a small step barely moves it
    imbalance_after = imbalance_before * shrink_factor := by
```

*Read aloud:* one gradient step multiplies the gap between the two
squared weights by `1 - learning_rate² × error²`.

From this, `balanced_stays_balanced` says equal layers stay equal, and
`abs_eq_abs_of_balanced` says each then carries the same share of the
slope. Two more results: `oneHiddenLayer_relabel` says shuffling the
hidden units of a one-layer network gives the same function, and for
RMSNorm, `normalizeByRms_smul` says it forgets the scale.

## Why it is true

**Rescaling.** The model is divided by `scale` and the weights multiplied
by it, so the outputs cancel. Dividing the outputs by `scale` divides
their squares by `scale²`, which is the curvature. The fits are the
weights that give the labels, and they are all multiplied by `scale`, so
the nearest is `|scale|` times as far. Since `strength × travel²` equals
the error squared (`strength_mul_travel_sq`), flat and far are one
number read two ways.

**Right angles.** Stretch the weights a little along themselves. That is
rescaling, so the loss does not change, so its rate of change is zero.
The rate of change is the dot product of the gradient with the weights.
Then `norm_sub_sq_real` expands the square of the step, and the cross
term is that dot product, which is zero. What is left is Pythagoras.

**Balance.** Write out the two steps and subtract the squares. The terms
in the first power of `learning_rate` cancel, and `ring` collects the
rest.

**RMSNorm.** It divides a vector by its root mean square, so doubling the
vector doubles the divisor, and the output is unchanged.
`isScaleInvariant_comp_normalizeByRms` then feeds this into the right
angles result, giving `inner_gradient_self_eq_zero_of_rmsNorm`.

## What it explains

- **Flatness depends on units.** A valley made ten times flatter costs a
  fit that is `√10` times as far, when rescaling by `√10`. So flatness on
  its own says nothing about the function. Flat means far, sharp means
  near, until you fix how the parameters are measured.
- **Normalised layers grow.** For weights that feed a normalisation
  (**recalled**: Ioffe and Szegedy 2015; Ba, Kiros and Hinton 2016), a
  step never shortens them. The size of those weights then stops meaning
  slope. That weight decay on them sets the step size is **argued**
  (**recalled**: van Laarhoven 2017; Hoffer et al. 2018).
- **Pre-norm against post-norm.** `preNormBlock_smul` and
  `preNormBlock_sub_smul` say a pre-norm branch adds what it always
  added, and the skip path carries the scale through.
  `rootMeanSquare_postNormBlock` says post-norm resets the size at every
  block. That is the usual reason given for why pre-norm trains more
  easily at depth (**recalled**: Xiong et al. 2020).
- **Layers stay in balance.** The law behind deep linear networks
  (**recalled**: Saxe, McClelland and Ganguli 2014; Arora, Cohen and
  Hazan 2018).

## How this meets the squiggly line

The theorem ties nearness to slope in data space (chapters 3 and 6).
Rescaling leaves the function alone, and so leaves that slope alone.
This is the reason to measure steepness of the function and not
flatness of the loss. The **travel** (chapter 9) and the **kernel**
(chapter 10) both do change, which is why this chapter is about the gap
between weights and line.

## What is not shown

- **Deep networks.** The rescaling rule covers the whole model. Scaling
  one layer up and the next down is the balance case, proved only for two
  numbers. That flat valleys generalise once units are fixed is **open**.
- **Normalisation over a batch.** The proofs use only that the loss does
  not change under rescaling. What batch statistics do beyond that is
  **open**.
- **The effective step size.** That the angle turned shrinks as the
  weights grow is argued, not proved.
- **No hill after matching units.** That two trained networks have no hill
  between them once their units are matched is **open**.

## Check yourself

1. A model is rescaled by 2. By what factor does the loss curvature
   change, and by what factor does the travel change?
2. Weights `(6, 8)` take a step of `learning_rate = 0.2` along `(8, −6)`,
   at right angles to them. What is their length afterwards?
3. In the balance example the layers are `3` and `1`, the label is 2 and
   `learning_rate = 0.5`. What is the imbalance after one step?

**Answers.** (1) By `norm_rescale_sq` the curvature is divided by
`2² = 4`, and by `travel_rescale` the travel is multiplied by 2. (2) The
squared length grows by `0.2² × 10²`, which is 4. It was
`6² + 8² = 100`, so it is 104 and the length is about 10.2, by
`norm_sq_sub_smul_of_inner_eq_zero`. (3) The error is `3 × 1 − 2 = 1`,
so the imbalance `8` is multiplied by `1 − 0.5² × 1² = 0.75`, giving 6,
by `balance_after_step`.

Previous: [23. Adam, AdamW and clipping](23-adam-and-clipping.md) · Next: [25. Classification](25-classification.md)
