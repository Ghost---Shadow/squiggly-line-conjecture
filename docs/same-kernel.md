# Same kernel, same predictions

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/SameKernel.lean` unless another file is named),
**recalled**, or **open**.

## The idea

The platonic representation hypothesis says that different networks, trained
in different ways and even on different kinds of data, are drifting towards the
same way of representing the world (**recalled**: Huh, Cheng, Wang and Isola
2024). "The same way" is measured with kernels: for each pair of inputs, how
alike does the network think they are? Two networks agree when their tables of
likeness agree.

That is a claim about what happens to real networks, and it is not proved
here. What can be proved is what it would buy. If two models have the same
kernel, are they the same model in every way that matters?

For models that are linear in their weights the answer is yes, exactly.

## What "same kernel" means here

A model's kernel on the training set is its table of likeness between training
points. For a test point we also need its row: how alike the test point is to
each training point. Call that the test row.

Two models can have the same table and the same test row and still look
nothing alike inside. One can be a Fourier series and the other a ReLU network.
They can have different numbers of weights.

## The result

Take two such models. Suppose

- their kernels on the training set are equal,
- their test rows are equal,
- they start with the same errors on the training set, and
- they start with the same answer at the test point.

Then:

- **Same errors, every step.** Gradient descent takes both through the same
  training errors (**proved** earlier: `residual_iterate_gradientStep_eq` in
  `Kernel.lean`).
- **Same answer at the test point, every step.** Their predictions at the test
  point are equal after any number of steps
  (**proved**: `prediction_iterate_gradientStep_eq`).
- **Same answer in the end.** The fit that training heads for gives the same
  prediction in both models (**proved**: `prediction_kernelFit_eq`).
- **Same distance to go.** Their nearest fits are equally far away (**proved**
  earlier: `travel_eq_of_kernel_eq` in `Kernel.lean`).

The reason is one line. A gradient step changes the answer at a test point by
the step size times the test row matched against the current errors
(**proved**: `inner_gradientStep`). The weights do not appear in that
sentence. Only the kernel does.

## What this says about the hypothesis

The hypothesis is the hard half: that kernels do converge. This note is the
easy half: once they have, nothing else about the network is left to matter.
Architecture, width and the values of the weights are all invisible. So "these
networks have the same representation" and "these networks are the same
learner" are one statement, not two.

It is the same point as the bridge between the Fourier model and the ReLU wind
tunnel. There the two models were shown to be equivalent for training. Here
they are shown to be equivalent for prediction as well.

## What is not shown

- **That kernels converge.** This is the hypothesis itself. **open**
- **Nearly the same kernel.** Real kernels would agree only roughly. That
  nearly equal kernels give nearly equal predictions is expected and is not
  proved here. **open**
- **Kernels that move.** A deep network's kernel changes during training. The
  result is for kernels that stay fixed. **open**
