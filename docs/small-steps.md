# Many small steps

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/SmallSteps.lean`), **recalled**, **argued**, or **open**.

## The idea

A lot of methods that work share one move. They replace one big jump with many
small ones.

- A diffusion model does not turn noise into a picture in one go. It removes a
  little noise, many times.
- A curriculum does not start with the hard task. It moves there by easy
  stages.
- Annealing does not drop the temperature at once. It lowers it slowly.
- A stack of polarizers turns light through a right angle that a single plate
  would block.

The last one has an old name in physics, the quantum Zeno effect: a state that
is checked often enough follows wherever the checks lead it
(**recalled**: Misra and Sudarshan 1977).

Why does cutting a jump into pieces help? And when does it not?

## The lemma

Say a step of size `s` keeps at least `1 − c·s²` of what you have. The loss is
proportional to the square of the step. Cover a total distance `D` in `N`
equal steps. Then what is kept is at least

```
1 − c·D² / N
```

(**proved**: `small_steps_keep`.) One step loses up to `c·D²`. A hundred steps
lose at most a hundredth of that. Take enough steps and the loss is as small
as you like.

The reason is plain counting. There are `N` steps, each of size `D / N`, each
losing about `c·(D/N)²`. The total is `N × c·D²/N² = c·D²/N`
(**proved**: `quadratic_cost_total`).

## When it does not help

Now say the loss of a step is proportional to the step itself, not its
square: a step of size `s` costs `c·s`. Then `N` steps cost
`N × c·D/N = c·D`, the same as one (**proved**: `linear_cost_total`).

So the rule is sharp. Small steps help exactly when a step's cost falls faster
than its size. If halving a step halves its cost, nothing is gained. If
halving a step quarters its cost, everything is.

## The polarizers

A plate turned by `s` keeps `cos s` of the length, and `cos s ≥ 1 − s²/2`.
That is a square-law loss with `c = 1/2`. So turning light through any angle
`φ` in `N` plates keeps at least

```
1 − φ² / (2N)
```

(**proved**: `turn_in_steps_keeps`.) This holds for any angle: a quarter turn,
a half turn that flips the sign, or several full turns. It extends
`quarter_turn_arrives`.

And more plates never hurt: replacing every plate by two plates of half the
turn keeps at least as much (**proved**: `cos_pow_le_cos_half_pow`).

## What this says about the other methods

For each of the methods above the claim would be that its step has a
square-law cost.

- **Diffusion.** One denoising step makes an error that shrinks faster than
  the step as the step gets small. **argued**
- **Curriculum.** A model that fits one task is nearly right for a nearby
  task, and the cost of adjusting is second order in how far the task moved.
  **argued**
- **Annealing.** A system moved slowly stays near its resting state, with an
  error that is second order in the speed. **argued**

None of these is proved here. What is proved is the common part: once the
cost of a step is a square law, the rest follows by counting.

## How this meets the squiggly line

A path made of many small turns is a squiggly path. The lemma says such a path
can deliver what a path with a few big turns cannot. Depth buys exactly this:
more layers, smaller turns, less lost. It is the wind tunnel's reason for being
long.

## What is not shown

- **That the methods above have square-law steps.** **open**
- **The price of the steps.** More steps cost more time. The lemma says the
  loss goes down as `1/N`. It says nothing on what `N` steps cost to run.
- **Unequal steps.** The count is for equal steps. That equal steps are best
  is in `least-action.md` for a pair of plates.
