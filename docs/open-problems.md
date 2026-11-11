# Open problems

What this repository does not settle, stated so that someone else can pick
one up. Written 11 Nov 2026.

Each problem has a status:

- **open**: I do not know the answer, and did not find it in the literature I
  recalled. I have not done a proper search, so check before claiming it.
- **known, not formalised**: the result is in the literature or is a standard
  exercise. What is missing is a machine-checked proof that fits this project.
- **measured**: an experiment here supports it. No proof.

Definitions and proved results are in `lean/SquigglyLine/`. Plain-language
background is in the other files of this folder.

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
   (**known, not formalised**)
   If the truth crosses a band of height `2ε` more times than the network has
   straight pieces, the network misses it by more than `ε` somewhere. This
   would connect `Depth.lean` to difficulty. It is the shortest useful proof
   on this list.

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
    The contrast is stated in `three-polarizers.md` and proved nowhere.

18. **A network whose activation is a polarizer.** (**open**)
    Store a value as a polarization angle. A polarizer then passes `cos²` of
    it, which is a nonlinear function of the stored value. What can a network
    with this activation compute, and what does it cost to chain layers?

## Chains

19. **Mini-batch training as a chain with chance in it.** (**known, not
    formalised**)

20. **Backprop as the inner chain run backward.** (**known, not formalised**)
    `chain-of-markov-chains.md` describes training as a chain of chains. Only
    the two chains separately are in Lean.
