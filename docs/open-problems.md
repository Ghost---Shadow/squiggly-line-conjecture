# Open problems

What this repository does not settle, stated so that someone else can pick
one up. Written 11 Nov 2026.

Each problem has a status:

- **open**: I do not know the answer, and did not find it in the literature I
  recalled. I have not done a proper search, so check before claiming it.
- **known, not formalised**: the result is in the literature or is a standard
  exercise. What is missing is a machine-checked proof that fits this project.
- **measured**: an experiment here supports it. No proof.

Larger aims that are out of reach for now are in the Wishlist section of the
README.

Definitions and proved results are in `lean/SquigglyLine/`, in one folder
for each group of the README. Plain-language background is in the other
notes under `docs/`, grouped the same way.

## The network case

1. **Oscillation scale of a random ReLU network.** (**open**)
   `Oscillation.lean` shows that a function which reaches every label within
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
   `Kernel.lean` proves `error ← error − η·K·error` for models linear in their
   weights. For a full network `K` moves during training. The lazy-training
   literature bounds how much, for wide networks. None of it is formalised
   here.

## Resolving power

5. **A target that turns too often cannot be matched.**
   (**proved** for one hidden layer, 12 Nov 2026; otherwise **known, not
   formalised**)
   If the truth crosses a band of height `2ε` more times than the network has
   straight pieces, the network misses it by more than `ε` somewhere. For a
   network with one hidden layer this is now `card_ge_of_zigzag` and
   `depth_separation` in `DepthSeparation.lean`: a unit per up-and-down, so
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

## The Fourier model

8. **Random Fourier features are nearly orthogonal.** (**measured**)
   For `n` scattered points and `m` terms with `m` much larger than `n`, the
   kernel is close to `(m + 1)` times the identity. A concentration bound
   would turn `ExchangeRate.lean` into a statement about the experiment, and
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

## The Fourier model under another link

The Fourier model is a generalized linear model with no link and squared
error (see `docs/networks/fourier-parameters.md`). These ask what survives a
change of link or loss. Added 12 Nov 2026.

25. **A budget of movement under any convex loss.** (**proved** for
    cross-entropy with two classes, 12 Nov 2026: `le_totalLogLoss_sub_along`
    and `totalLogLoss_along_le_max` in `CrossEntropy.lean`; other losses
    **known, not formalised**)
    `exists_within_budget` says a move of `ε` toward a fit at distance `d`
    removes exactly `ε / d` of the error. For any loss that is convex in the
    weighted sum, which covers the logistic and Poisson losses, the same move
    removes at least `ε / d` of the gap in loss. `no_barrier` extends the same
    way.

26. **Gradient descent reaches the nearest fit, under any link.**
    (**proved**, 12 Nov 2026: `iterate_errorStep_is_nearest` in
    `CrossEntropy.lean`)
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

## The geometry of curves

12. **The length bound.** (**known, not formalised**)
    A curve of length `l` inside a region of area `V` has mean distance at
    least about `V / (4·l)` to a random point. It follows from the tube
    identity in `Coverage.lean` and a bound on the area of a tube.

13. **The constant for sines.** (**measured**)
    For a sine spanning the box, distance times frequency tends to
    `(2 − 8/π²)/4 = 0.2974`. Derived by hand in `RESOLUTION.md` and matched by
    experiment. Not proved.

14. **Joint fit.** (**open**)
    Score a random-function prior by the cost `yᵀK⁻¹y` of fitting labels `y`.
    For random labels the mean cost is `tr K⁻¹`, smallest at fixed amplitude
    when `K` is the identity. For smooth targets the order reverses. Find the
    trade-off, and what it says about which prior a network should start from.

## Polarizers and ReLU

15. **Malus's law for ReLU at any angle and in any dimension.** (**open** as a
    statement; the planar case is easy)
    `Polarizer.lean` handles a bird on the edge of the positive quadrant in
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

## Chains

19. **Mini-batch training as a chain with chance in it.** (**known, not
    formalised**)

20. **Backprop as the inner chain run backward.** (**known, not formalised**)
    `docs/networks/chain-of-markov-chains.md` describes training as a chain of chains. Only
    the two chains separately are in Lean.

## Using the nearness

23. **Does gradient descent find the warp?** (**open**)
    `exists_warp_of_coversWithin` shows that a warp of the input of size at
    most the oscillation scale fits any target. Whether training reaches such
    a warp, and how fast, is not shown. At high frequency the loss as a
    function of one phase has many local minima.

24. **How smooth can the warp be?** (**open**)
    The warp moves no point far, but it may be rough. Bound its slope in terms
    of the frequency of the curve and the spacing and labels of the data.

## Ideas noted on 11 Nov 2026, not yet thought through

21. **What is batch norm, in the polarizer picture?** (**proved** for one
    example at a time, 12 Nov 2026; across a batch still **open**)
    Rescaling one example after each plate is an amplifier: the light arrives
    at full strength after any turn short of a right angle, and a blocked
    beam stays blocked (`renorm_plate`, `throughNormedPlates_eq`,
    `renorm_plate_of_crossed` in `SkipAndNorm.lean`; see `docs/supporting/network-shape/skip-and-norm.md`).
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
    `skipPlate_of_crossed`, `inner_skipPlate` in `SkipAndNorm.lean`; see
    `docs/supporting/network-shape/skip-and-norm.md`). What follows is the earlier note.
    A first reading: a bypass. Split the beam, send one part through the plate
    and one part around it, and add them. The result keeps the part the plate
    would have removed, so nothing is ever fully blocked and nothing merges.
    A partial polarizer, which passes one direction fully and the other
    weakly, does the same thing in one piece. This would make every layer a
    small change, which is the "many small turns" regime where almost nothing
    is lost.
