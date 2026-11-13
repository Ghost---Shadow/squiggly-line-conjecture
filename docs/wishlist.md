# Wishlist and open problems

**Proofs:** [`Coverage.lean`](../lean/SquigglyLine/Theorem/Coverage.lean), [`Oscillation.lean`](../lean/SquigglyLine/Theorem/Oscillation.lean), [`Depth.lean`](../lean/SquigglyLine/Networks/Depth.lean), [`ExchangeRate.lean`](../lean/SquigglyLine/Networks/ExchangeRate.lean), [`Kernel.lean`](../lean/SquigglyLine/Networks/Kernel.lean), [`Lift.lean`](../lean/SquigglyLine/Networks/Lift.lean), [`LinearModel.lean`](../lean/SquigglyLine/Networks/LinearModel.lean), [`Polarizer.lean`](../lean/SquigglyLine/Networks/Polarizer.lean), [`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean), [`Capacity.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean), [`DepthSeparation.lean`](../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean), [`Mixtures.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Mixtures.lean), [`ModeConnectivity.lean`](../lean/SquigglyLine/Supporting/NetworkShape/ModeConnectivity.lean), [`SkipAndNorm.lean`](../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean), [`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean), [`CrossEntropy.lean`](../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean), [`LeastAction.lean`](../lean/SquigglyLine/Supporting/Training/LeastAction.lean), [`Perceptron.lean`](../lean/SquigglyLine/Supporting/Training/Perceptron.lean), [`Reparam.lean`](../lean/SquigglyLine/Supporting/Training/Reparam.lean).

Written 12 Nov 2026, last revised 14 Nov 2026. The aim is to say all of deep
learning in the terms of the squiggly line, with every step machine-checked.
This file lists what is still wanted.

What is proved is not listed here. It is in
[`supporting-proofs.md`](supporting-proofs.md#paper-by-paper), paper by
paper, grouped by the six things a result can connect through: slope,
nearness, travel, the kernel and the lift, folds, and averages. Every item
that was marked "next" in the first two rounds has been proved and moved
there, so five of those six groups have nothing left in this file.

The list keeps to ideas that are well established and in common use. Niche
results and rarely used optimisers are left to others. Nothing goes on it
unless it connects to the squiggly line.

The papers and years are recalled from memory and have not been checked.

## Next

These look within reach of the tools already here. None is proved yet.

| Paper or idea | In squiggly terms | Connects through |
|---|---|---|
| Codebook autoencoders, VQ-VAE (van den Oord et al. 2017) | Snapping a code to its nearest codebook entry moves it by at most the distance to that entry, so the decoder's output moves by at most its slope times that distance. The codebook update is a k-means step, and the gradient passes the snap by the straight-through trick. | Nearness, slope |
| Why image models miscount (fingers, legs, "three cats") | A count is a step. Any smooth read-out that says 2 on one image and 3 on another says 2.5 somewhere between. The ideal denoiser blends a five-finger hand with a six-finger one. Telling `k` from `k + 1` on nearby images costs slope, and a local layer cannot see the whole image. This would show the difficulty, not that it is the cause of real errors. | Slope, averages |
| Temperature trades quality for diversity (Ackley et al. 1985; Holtzman et al. 2020) | As the temperature falls, the average score of a sample rises and the samples concentrate on the top score. Temperature is the slope of the scores. | Slope |

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
| How squiggly a network with random weights is, as a function of width, depth and weight scale. This is the original conjecture for networks. | [open problems](#open-problems), item 1 | No known formula for the oscillation scale. |
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
| What normalising across a batch does. | [open problems](#open-problems), item 21; here one example at a time | Each example's path depends on the others. |
| **Generalisation.** Why a network that can fit any labels does well on new data when the labels are real. | [`Capacity.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean) shows it can fit anything; [`Perceptron.lean`](../lean/SquigglyLine/Supporting/Training/Perceptron.lean) shows no learner is better on average over all labellings; here bias and variance, and one junk direction of benign overfitting | Nobody knows which property of real data and of training makes the fitted line the right one. The squiggly-line reading is that real labels vary gently and training takes the least travel, but that is a picture and not a theorem. |

At the far end is the question of why predicting the next word gives a model
that can do so much else. There is not yet a statement of it to prove.

## Open problems

The tables above are about well-known papers. This part is about the
project's own questions: what is still open about the squiggly line itself,
numbered as the notes refer to them. It was a file of its own until 14 Nov
2026.

What this repository does not settle, stated so that someone else can pick
one up. Written 11 Nov 2026.

Each problem has a status:

- **open**: I do not know the answer, and did not find it in the literature I
  recalled. I have not done a proper search, so check before claiming it.
- **known, not formalised**: the result is in the literature or is a standard
  exercise. What is missing is a machine-checked proof that fits this project.
- **measured**: an experiment here supports it. No proof.

Larger aims that are out of reach for now are in `docs/wishlist.md`.

Definitions and proved results are in `lean/SquigglyLine/`, in one folder
for each group of the README. Plain-language background is in the other
notes under `docs/`, grouped the same way.

### The network case

1. **Oscillation scale of a random ReLU network.** (**open**)
   [`Oscillation.lean`](../lean/SquigglyLine/Theorem/Oscillation.lean) shows that a function which reaches every label within
   distance `ρ` of every input is within `ρ` of the data. For a random ReLU
   network, how does the smallest such `ρ` depend on width, depth and the
   scale of the weights? The conjecture for networks reduces to this.

2. **Does a small distance force a small oscillation scale?** (**open**)
   The covering bound is one direction only. Find the converse, or a
   counterexample.

3. **Initial loss and width, beyond squared error.** (**open**)
   The expected initial MSE of a He-initialised network does not depend on
   width, because only the second moment of the output enters. Other losses
   need the whole distribution of the output, which does change with width at
   small widths. How large is the effect?

4. **When is a trained network a linear model?** (**known, not formalised**)
   [`Kernel.lean`](../lean/SquigglyLine/Networks/Kernel.lean) proves `error ← error − η·K·error` for models linear in their
   weights. For a full network `K` moves during training. The lazy-training
   literature bounds how much, for wide networks. None of it is formalised
   here.

### Resolving power

5. **A target that turns too often cannot be matched.**
   (**proved** for one hidden layer, 12 Nov 2026; otherwise **known, not
   formalised**)
   If the truth crosses a band of height `2ε` more times than the network has
   straight pieces, the network misses it by more than `ε` somewhere. For a
   network with one hidden layer this is now `card_ge_of_zigzag` and
   `depth_separation` in [`DepthSeparation.lean`](../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean): a unit per up-and-down, so
   fewer than `2^L` units cannot stay within one half of `L + 1` tent layers.
   See `docs/supporting/network-shape/depth-separation.md`. For deeper networks it needs the bound on
   pieces in the next item.

6. **The general bound on pieces.** (**known, not formalised**)
   A ReLU network with `L` layers of `n` neurons and one input draws at most
   about `n^L` straight pieces. Only the doubling for `n = 2` is proved.

7. **How many pieces does training use?** (**known, not formalised**; recalled
   from Hanin and Rolnick, not verified here)
   Random and normally trained networks are reported to use about as many
   pieces as they have neurons, far below the maximum. No experiment in this
   repository checks it.

### The Fourier model

8. **Random Fourier features are nearly orthogonal.** (**measured**)
   For `n` scattered points and `m` terms with `m` much larger than `n`, the
   kernel is close to `(m + 1)` times the identity. A concentration bound
   would turn [`ExchangeRate.lean`](../lean/SquigglyLine/Networks/ExchangeRate.lean) into a statement about the experiment, and
   give the `1/√parameters` rate for travel.

9. **The blow-up at the threshold.** (**measured**)
   With barely enough parameters to fit, the travel is enormous: 448 at 21
   parameters for 20 points, against 0.23 at 513. Give the size of the peak as
   a function of how close the parameter count is to the number of points.
   This is the double-descent peak seen in parameter space.

10. **New parameters that start at random.** (**open**)
    `travel_coprod_le` shows that added parameters starting at zero never move
    the nearest fit further away. The experiment starts them at random and the
    result still holds on average. State and prove the version with a random
    start.

11. **Hinges against sines.** (**measured**)
    Random ReLU hinges and Fourier features can draw the same curves on the
    data, but the hinge kernel is far worse conditioned: a ratio of about
    300,000,000 against 1.7 for 513 features and 20 points. How does that
    ratio grow with the number of points?

### The Fourier model under another link

The Fourier model is a generalized linear model with no link and squared
error (see `docs/networks/fourier-parameters.md`). These ask what survives a
change of link or loss. Added 12 Nov 2026.

25. **A budget of movement under any convex loss.** (**proved** for
    cross-entropy with two classes, 12 Nov 2026: `le_totalLogLoss_sub_along`
    and `totalLogLoss_along_le_max` in [`CrossEntropy.lean`](../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean); other losses
    **known, not formalised**)
    `exists_within_budget` says a move of `ε` toward a fit at distance `d`
    removes exactly `ε / d` of the error. For any loss that is convex in the
    weighted sum, which covers the logistic and Poisson losses, the same move
    removes at least `ε / d` of the gap in loss. `no_barrier` extends the same
    way.

26. **Gradient descent reaches the nearest fit, under any link.**
    (**proved**, 12 Nov 2026: `iterate_errorStep_is_nearest` in
    [`CrossEntropy.lean`](../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean))
    `gradientDescent_fit_is_nearest` is proved for squared error. Under any
    link each step is still a weighted sum of the feature vectors, which is
    all the proof uses.

27. **Below the threshold.** (**known, not formalised**)
    With too few parameters no fit exists, and the repository says nothing
    more. Least squares still has an answer: the weights at which the error
    is at right angles to every feature. State it, and show the error splits
    into the part no weights can remove and the part still to go.

28. **Yes-or-no labels.** (**known, not formalised**; recalled from Cover 1965
    and Soudry et al. 2018, not verified here)
    Under the logistic link no finite weights fit, so travel is infinite and
    the threshold changes. Random labels on `n` points can be separated about
    half the time when there are `n / 2` parameters. Gradient descent then
    runs off to infinity along the widest-margin direction. Neither is
    formalised here.

### The geometry of curves

12. **The length bound.** (**known, not formalised**)
    A curve of length `l` inside a region of area `V` has mean distance at
    least about `V / (4·l)` to a random point. It follows from the tube
    identity in [`Coverage.lean`](../lean/SquigglyLine/Theorem/Coverage.lean) and a bound on the area of a tube.

13. **The constant for sines.** (**measured**)
    For a sine spanning the box, distance times frequency tends to
    `(2 − 8/π²)/4 = 0.2974`. Derived by hand in `RESOLUTION.md` and matched by
    experiment. Not proved.

14. **Joint fit.** (**open**)
    Score a random-function prior by the cost `yᵀK⁻¹y` of fitting labels `y`.
    For random labels the mean cost is `tr K⁻¹`, smallest at fixed amplitude
    when `K` is the identity. For smooth targets the order reverses. Find the
    trade-off, and what it says about which prior a network should start from.

### Polarizers and ReLU

15. **Malus's law for ReLU at any angle and in any dimension.** (**open** as a
    statement; the planar case is easy)
    [`Polarizer.lean`](../lean/SquigglyLine/Networks/Polarizer.lean) handles a bird on the edge of the positive quadrant in
    the plane. Give the length a rotate-then-ReLU layer keeps for a bird
    anywhere, in `d` dimensions.

16. **The stepped path converges to the helix.** (**measured**)
    As plates are added, the path of the light's vibration tends to a quarter
    circle and its length to `π/2`.

17. **A stack of polarizers is one linear map; a stack of ReLU layers is
    not.** (**known, not formalised**)
    The contrast is stated in `docs/networks/three-polarizers.md` and proved nowhere.

18. **A network whose activation is a polarizer.** (**open**)
    Store a value as a polarization angle. A polarizer then passes `cos²` of
    it, which is a nonlinear function of the stored value. What can a network
    with this activation compute, and what does it cost to chain layers?

### Chains

19. **Mini-batch training as a chain with chance in it.** (**known, not
    formalised**)

20. **Backprop as the inner chain run backward.** (**known, not formalised**)
    `docs/networks/chain-of-markov-chains.md` describes training as a chain of chains. Only
    the two chains separately are in Lean.

### Using the nearness

23. **Does gradient descent find the warp?** (**open**)
    `exists_warp_of_coversWithin` shows that a warp of the input of size at
    most the oscillation scale fits any target. Whether training reaches such
    a warp, and how fast, is not shown. At high frequency the loss as a
    function of one phase has many local minima.

24. **How smooth can the warp be?** (**open**)
    The warp moves no point far, but it may be rough. Bound its slope in terms
    of the frequency of the curve and the spacing and labels of the data.

### Ideas noted on 11 Nov 2026, not yet thought through

21. **What is batch norm, in the polarizer picture?** (**proved** for one
    example at a time, 12 Nov 2026; across a batch still **open**)
    Rescaling one example after each plate is an amplifier: the light arrives
    at full strength after any turn short of a right angle, and a blocked
    beam stays blocked (`renorm_plate`, `throughNormedPlates_eq`,
    `renorm_plate_of_crossed` in [`SkipAndNorm.lean`](../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean); see `docs/supporting/network-shape/skip-and-norm.md`).
    That is closest to layer normalisation. What follows is the earlier note,
    which is about the batch.
    A first reading: gain control. Batch norm rescales and recentres the flock
    after a layer, which undoes the `cos θ` loss and moves the flock back to
    the middle of the wedge. For one photon the matching step is to
    renormalise the state after each plate, that is, to follow only the
    photons that survive. It acts on the whole flock at once, so with it a
    single bird's path depends on the other birds. It cannot separate birds
    that have merged, and it cannot revive a blocked one.

22. **What is a residual layer, in the polarizer picture?** (**proved** for
    plates, 12 Nov 2026; for ReLU layers still **open**)
    A plate with a bypass never dims the light, does nothing when crossed, and
    turns the light only part of the way (`norm_le_norm_skipPlate`,
    `skipPlate_of_crossed`, `inner_skipPlate` in [`SkipAndNorm.lean`](../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean); see
    `docs/supporting/network-shape/skip-and-norm.md`). What follows is the earlier note.
    A first reading: a bypass. Split the beam, send one part through the plate
    and one part around it, and add them. The result keeps the part the plate
    would have removed, so nothing is ever fully blocked and nothing merges.
    A partial polarizer, which passes one direction fully and the other
    weakly, does the same thing in one piece. This would make every layer a
    small change, which is the "many small turns" regime where almost nothing
    is lost.
