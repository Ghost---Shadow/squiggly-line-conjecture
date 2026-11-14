# Cross-check of Part I experiments (proposal 20261114, section A, steps 1 to 5)

Checker: independent reader. Step 6 (web build and PDF) skipped, pandoc is not installed.
No notebook code, `common.py`, chapter or git state was changed. The notebooks were
re-executed in place (their saved outputs are now from my second run).

## Step 1: run every notebook twice

All six notebooks (`ch01`, `ch03`, `ch04`, `ch05`, `ch06`, `ch07`) finished, both times, with
no error. 46 `[PASS]` lines in each run. I extracted every printed line of each notebook
after run 1 and after run 2 and diffed them: the `[PASS]` lines, the table, the training
printout and the "average loss" lines are byte-identical. The only differences are a Torch
generator memory address (`<torch._C.Generator at 0x...>` in ch05), the process id inside one
UserWarning in ch06, and one blank line. No numeric difference.

Side note: the ch06 notebook prints a `UserWarning` ("Converting a tensor with
requires_grad=True to a scalar", `float(loss)` in the training loop). Harmless; `loss.item()`
would silence it.

## Step 2: numbers in the text against the notebook outputs and figures

Everything below was compared. Matches are not listed. Mismatches:

1. `book/01-two-distances.md` line 104: text says "To run all of Part I:
   `python experiments/part1/run_all.py`". Notebook side: there is no `run_all.py` in
   `experiments/part1/` (and `experiments/part1/README.md` does not mention one; it uses
   `jupyter nbconvert --execute`). **Wrong, must fix.**
2. `book/03-slope.md` "Run it yourself": text says "For 720 random sine models of 1, 3, 10 and
   30 terms ... and random data points". Notebook says 4 sizes x 3 models = 12 models, with 60
   data points each = 720 (model, point) trials. The figure legend ("720 random sine models
   and data points") has the same loose wording. Say "720 trials on 12 random sine models".
3. `book/03-slope.md`: text says the measured gap for straight lines is "below 1e-15". Notebook
   prints 4.4e-16 (true) but the assertion only demands `< 2e-4`. The number is right; the
   check would not catch a 1e-5 error.
4. `book/04-nearness.md` caption of `04-before-and-after-warp.png`: "about 0.4 to 0.6 before the
   warp and about 1e-14 after". Notebook/figure: before 0.36, 0.56, 0.57; after 2e-15, 6e-15,
   2e-14. Rounded, acceptable, but "about 0.4 to 0.6" starts at 0.36 and "about 1e-14" spans
   a factor of ten. Nit.
5. `book/06-the-sine.md` text and figure title "falls thirty times / about 30 times": this
   notebook measures 28 (0.6128 / 0.0220); the book's own table gives 29.6. Fine as "about",
   nit only.
6. `book/06-the-sine.md` "A model that learns": "larger models reached a loss of 0.05 in fewer
   steps". Notebook medians for sizes 1, 2, 4, 8, 16, 32, 64 are 186, 133, 111, 155, 133, 57,
   19: not monotone (4 terms 111, 8 terms 155). The figure title in the notebook ("larger
   models also reach a fixed loss in fewer steps") says the general thing; the chapter's
   figure caption ("falls once the model has 32 terms or more") is the honest wording. Make
   the chapter sentence match the caption.

Everything else checked out: 0.31623 and 1/sqrt(10); 1200 trials; reaches 3.1416, 0.3927,
0.1571; warp fit within 1.8e-14 (text says 1e-13); vertical/budget 0.545 (text "0.55");
width table 0.496 / 0.421 / 0.407 / 0.416 / 0.407 (text 0.50 and 0.41), minus-bias values
0.400 to 0.414 (text "0.40 to 0.41"); 400,000 draws; flat/jagged gaps at most 0.0018 for
squared and 0.0008 for absolute error (text "within 0.003"); spreads 0.297 / 0.068 (text 0.30 /
0.07); claim 1 in 12 settings x 40 points; claim 3 gap 1.1e-16 (text "1e-15"); table gaps
0.0059 and 0.0020 (text 0.006 and 0.002); medians 186, 111, 19; one 2-term run at 4001;
start nearest 0.609 to 0.036; reaches 2.81, 1.41, 0.70, 0.35; slopes 2.13, 4.25, 8.50, 17.00;
loss 0.4062 to 0.4065 (text 0.406 within 0.0003, largest gap 2.5e-4); figure captions for
06-with-and-without-squiggle (0.613, 0.022, 0.665, 0.667, 0.665, 0.666) and 07 (2.81, 1.41,
0.70, 2.1, 4.3, 8.5, 0.13, 8, 1).

Mismatch count: 2 clear (items 1, 2), 4 nits (items 3 to 6).

## Step 3: the figures (each PNG opened)

All 14 files in `book/figures/` exist; `nearest-distance-bounds.svg` is unused, as stated.
Captions agree with the numbers shown in the figures. Defects in layout:

- `01-two-distances-line.png`: the purple model line passes through the text
  "nearest distance = 1 / sqrt(10) ~ 0.32" (it cuts the "1 / sqrt(10)"). A label sits on a
  curve. Move the text.
- `04-before-and-after-warp.png`: the left legend sits over the middle of the bars (it covers
  the grey bars of frequencies 8 and 20). Move it.
- `07-squeeze.png`: the "edge of the label band" text at the top right touches the curve's
  peak (about 0.67 near input 5.7) in the first panel.
- `04-covers-within-reach.png`: in the lower panel the arrow is shorter than its own
  arrowheads and hides under the black dot (it reads as "><"). The explanatory text sits just
  under the curve minima in both panels (tight, not overlapping). The black "input" dot is
  drawn at height 0.67, off the curve, which the caption does not explain.
- `06-frequency-strip.png`: panel titles give vertical error 0.62, 0.57, 0.62 (mean of 250),
  so the orange lines visibly "do not move" only to within noise; the sentence in the
  caption is right but the titles do not look flat. Several points sit on the plot edge
  (inputs near -1 and 1).
- `06-before-and-after-training.png`: the "before training" loss bars are not level
  (0.42 to 0.89; they are means of 5 different data sets), which sits oddly beside the
  chapter's "no lower in loss"; the level result is the 300-draw one in
  `06-trained-sine-model.png`. Consider plotting the 300-draw value instead.
- `03-slope-sandwich.png`: left panel leaves a large blank strip below it. Cosmetic.
- No label sits on a curve in `04-the-warp`, `05-flat-versus-jagged`,
  `05-with-and-without-last-bias`, `06-closer-but-no-better`, `06-with-and-without-squiggle`,
  `06-trained-sine-model`, `07-before-and-after-squeeze`.

## Step 4: does each check test what the chapter says, and could it fail?

Ch 1
- Example (0,1), y = 3x: real; fails if the distance were wrong (tolerance 1e-4).
- Flat line (2,5): real.
- "Nearest never exceeds vertical" (1200 trials): **cannot fail.** `get_nearest_distance`
  returns `min(nearest, vertical_error)`, and the vertical foot is always a sample of the
  polyline, so `nearest <= vertical` by construction. The check tests the code, not the claim.

Ch 3
- Straight lines meet the lower bound: real and tight (tolerance 2e-4).
- Lower bound on 720 sine trials: real (though sine curves sit well above the bound).
- Upper bound: **cannot fail**, same clamp as ch 1.
- The three "check yourself" lines are arithmetic identities (for example
  `abs(1/sqrt(2) - 0.7071) < 1e-4`). They cannot fail.

Ch 4
- Reach `<= pi/frequency` and hit error < 1e-9: real, but one-sided. The text says the reach
  is "exactly" pi over frequency; the PASS line only asserts `<=`. The printed values show
  equality, so the claim is true, but a model that covered within a smaller reach would also
  pass.
- Warp: the shift bound is a real check; the "fit is exact" half is true by construction
  (`get_nearest_hit` inverts the sine in closed form).
- Slope tax `vertical <= sqrt(1+s^2) * reach`: **cannot fail** in this setup. Amplitude 1 and
  labels in [-1, 1] give vertical error <= 2, and the budget `sqrt(1+f^2) * pi/f >= pi`. The
  largest possible ratio is 2/pi = 0.64; measured 0.545. To test the tax, use a model whose
  vertical error can approach the budget (large amplitude and a label far from the model).
- Nearest within reach: real for f = 6 and 15 (reach 0.52, 0.21); trivial for f = 2.
- "Check yourself" lines: arithmetic identities.

Ch 5
- Flat/jagged means vs `y^2 + 1/3` and `(1+y^2)/2`, 400,000 draws, tolerance 4e-3 (about 3
  standard errors; observed gaps at most 0.0018): real. Would fail if a model had a different
  marginal.
- Spread with 100 points, flat std > 3 x jagged: real (observed 4.4 x). Threshold change
  (4 points to 100): honest, the chapter quotes the 100-point numbers, and the ratio is about
  `sqrt(points)` for the jagged model, so 4 points could not separate them. Fine.
- Coin flips: `(coin_flips**2).mean() == 1.0` is a tautology.
- Random-phase sine marginal (tolerance 1e-3, observed 7e-6, deterministic phase grid): real.
- Width check, threshold 0.03 on the spread after subtracting `1/(3 width)`: honest in kind
  (the chapter now says exactly this, and I derived the same numbers: PyTorch default init
  gives `1/3 + 2/27 + 1/(3 width) = 0.4074 + 1/(3 width)`, matching 0.407 at 1024 and 0.496
  at 4). It would fail with the bias left in (raw spread 0.089 > 0.03). Two weaknesses: 0.03
  is about 7% of the mean and about 2.5 standard errors at small width, so it only separates
  the 21% effect from "level", not a 5% effect; and the "without bias" series is arithmetic
  (mean minus `1/(3 width)`), not a network with the last bias zeroed. Zeroing the bias
  (`second.bias.zero_()`) would measure it directly.

Ch 6
- Claim 1 (lower <= nearest <= pi/f): real; slacks 1.3e-6 and 1.2e-2.
- Claim 2 "average nearest <= pi/f": real; "falls as frequency rises (amplitude 1)": real.
- Claim 3 (loss = y^2 + a^2/2, tolerance 1e-6, observed 1e-16): real.
- Claim 4 warp: shift bound real, exactness by construction.
- Table reproduction (threshold changes): the vertical error range now uses 200,000 samples
  (standard error about 0.001, observed gap 0.002): an honest fix, noise was the cause. The
  nearest column still uses 500 points with an absolute tolerance of 0.01 (observed 0.0059).
  Standard error at 500 points is about 0.01 at low frequency, so the tolerance is just
  noise; at high frequency the mean is 0.02, so a 0.01 tolerance accepts an error of 50%.
  The check is nearly vacuous for the 16 and 64 rows. Use a relative tolerance or compare
  to the standard error row by row.
- "Falls about thirty times": asserts 20 < fall < 45 (observed 28): real.
- "Check yourself": arithmetic identities.
- Training section:
  - Sandwich at start, middle and end of every run: real for the lower side (smallest slack
    1.1e-7); the upper side is the clamped quantity, so cannot fail.
  - "Closer but no better: nearest at the start falls": asserts only that 64 terms is below 1
    term. The printed values are monotone, but the check would pass on a non-monotone
    series. Compare every consecutive pair.
  - Loss at the start equals mean(y^2) + 1/2 (300 draws, within 4 s.e.): honest replacement
    for the 5-run version, and the expectation is exact (amplitudes N(0, 1/n)). Weak at small
    size (the 1-term error bar is plus or minus 0.2), strong at 64.
  - Speed result: no assertion (it is labelled measured), good. One confound to state: the
    data is `0.6 sin(x) + 0.3 sin(3x + 1) + noise 0.05`, so a model with fewer than 3 terms
    cannot fit the third-frequency part. Their best possible loss is about 0.045 to 0.048
    (final losses 0.0443 and 0.0470 in the output), sitting right at the 0.05 target. The
    1- and 2-term step counts, and the 2-term run that "did not reach 0.05", measure that
    floor and not the speed of a small model. The effect at 32 and 64 terms is not affected.

Ch 7
- Reach times squeeze factor stays at the original (2% tolerance): real, though it is a
  scaling identity checked through a numerical root finder; it does test the root finder
  (the bug fixed earlier was found this way).
- Steepest slope equals factor x original (tolerance 1e-3, and within factor x slope limit):
  real but a chain-rule identity.
- Average loss equal at every factor (400,000 draws, tolerance 4e-3, observed 2.5e-4):
  real. Tolerance is looser than the observation by more than 10 x; 1e-3 would still pass.
- "Check yourself": arithmetic identities.

Thresholds changed after a failed run (the four the proposal lists):
1. Flat vs jagged spread, 4 points to 100: honest (above).
2. Chapter 5 width check, adjusted for the last-layer bias: honest, and the bias term is
   derived correctly; loose tolerance and subtraction-not-removal noted.
3. Chapter 6 vertical error range, 500 to 200,000 samples: honest (more data, not a looser
   bound). The companion nearest check is the weak one.
4. Starting loss in the training section, 5 runs to 300 draws against the exact expectation:
   honest and statistically sound; weak at 1 to 2 terms.

## Comparison: chapter 5 width experiment vs `scripts/initial_mse.py`

I ran `scripts/initial_mse.py` (about 10 seconds, not "~1 minute" as its docstring says). It
gives He means 1.073, 1.021, 1.069, 1.104, 1.034 against theory 1.034, so "the widths agree"
holds within about 2 standard errors (width 256 is the largest, at 1.9 s.e.). That matches
`graphs/readme_initial_mse.png`.

How the two setups differ:

| | `scripts/initial_mse.py` | chapter 5 notebook |
|---|---|---|
| Inputs | 10-dimensional, uniform on [-1, 1]^10 | 1-dimensional, uniform on [-1, 1] |
| Hidden layers | 2 | 1 |
| Weight init | He, normal with variance 2 / fan_in, all layers including the last | PyTorch default (Kaiming uniform with a = sqrt(5)): uniform in plus or minus 1 / sqrt(fan_in), variance 1 / (3 fan_in) |
| Biases | none | yes in both layers, uniform in plus or minus 1 / sqrt(fan_in) |
| Data | 200 points drawn once, shared by every network | 256 fresh points (x and y) per network |
| Networks per width | 200 | 300 |
| Library, RNG | numpy `default_rng(3)` | PyTorch, seed 5 |
| Expected start loss | `E[y^2] + 2 E|x|^2 / d_in = 1.034`, width-free | `1/3 + 2/27 + 1/(3 width)` = 0.407 + the last-bias term |
| Why widths agree | He keeps the second moment at every width; no biases | weight scale is width-free by the 1/(3 fan_in) rule; the last bias breaks it |

So the chapter's "a re-run in PyTorch" is not a re-run of the same experiment: different
dimension, depth, initialisation scale (variance 1/(3 fan_in) vs 2/fan_in, which is why the
level is 0.41, not 1.03), and the biases (the whole source of the small-width excess) exist
only in the notebook. The script has no last-layer bias, so it cannot show the effect; the
notebook shows it but uses a different network. The chapter text is correct on each point it
makes ("He weights, no biases, 10 inputs, 200 points" for the script); it should not call the
notebook a re-run of the same measurement.

## Step 5: `python book/tools/check_book.py 1 3 4 5 6 7`

Ended with `problems: 0`. Six warnings of the form "lowercase name not in Lean" for
`chNN_*.ipynb` file names, plus `num_terms` in chapter 6. The checker treats them as
made-up local names, which it says is fine. (Another helper was editing chapters at the time;
this is the state of the files when I ran it.)

## Must fix before publishing

1. `book/01-two-distances.md` line 104: remove or correct "`python experiments/part1/run_all.py`"
   (the file does not exist), or add a `run_all.py`.
2. `book/03-slope.md`: "720 random sine models" should be 720 trials on 12 models.
3. Checks that cannot fail, but are described as tests of the claim: ch1 and ch3 "nearest <=
   vertical" (the helper clamps to the vertical error), ch4 "slope tax" (vertical <= 2 < the
   budget always). Either fix the check (do not clamp in the helper for these; use a regime
   where the bound can bind) or say in the text that these are consistency checks of the
   code. At least do not say "the slope tax held with room to spare" in chapter 4 as evidence
   (the room is built in).
4. Chapter 6, "A model that learns": the 1- and 2-term step counts hit the loss floor of the
   target (about 0.045) near the 0.05 threshold, so they are not a speed measurement; state
   it, or add a third frequency check (use a target with only frequency 1 and 2, or target
   loss 0.06 with at least 3 terms). Also change "larger models reached 0.05 in fewer steps"
   to the qualified form used in the caption (non-monotone below 32 terms).
5. Chapter 5: do not call the notebook a re-run of `scripts/initial_mse.py`; the two setups
   differ as in the table above.
6. Figure layout: `01-two-distances-line.png` (line through the label) and
   `04-before-and-after-warp.png` (legend over the bars). `07-squeeze.png` label touches the
   peak.
7. Tolerances worth tightening (not blockers): ch6 table nearest column (relative tolerance),
   ch6 "nearest falls with size" (all consecutive pairs), ch5 width check (zero the bias
   instead of subtracting).

## Fixes applied

All six notebooks were re-run twice after the fixes: 47 `[PASS]` lines, identical. No check
failed. `python book/tools/check_book.py 1 3 4 5 6 7` ends `problems: 0`.

Must fix:
1. Chapter 1 named a missing `run_all.py`. The sentence now gives the `jupyter nbconvert` command.
2. Chapter 3 "720 random sine models" now says 720 trials on 12 models (text, notebook, figure legend).
3. Checks that could not fail. `common.get_nearest_distance` no longer clamps to the vertical error
   and has `include_foot=False`, which leaves the vertical foot out of the samples. Chapter 1 and
   chapter 3 "nearest <= vertical" and the chapter 6 training sandwich use it, tolerance `3e-4`
   (smallest slack in ch1 -2.4e-7 below the bound, ch3 3.2e-5, ch6 training -8.5e-9, all inside it).
   Chapter 4 slope tax: the check is now vertical <= sqrt(1 + slope_limit^2) x the measured nearest
   distance (largest ratio 0.997, so it can bind). The `reach` version is kept, labelled a
   consequence that is built in for a sine, and the chapter says so. The "room to spare" wording is gone.
   The "check yourself" arithmetic checks in chapters 3, 4, 6 and 7 now measure a line, a sine
   reach or a squeezed line with the helpers instead of recomputing the formula.
4. Chapter 6 learning: the text now says medians are not monotone below 32 terms and that the 1 and
   2 term runs hit the target's loss floor (about 0.045), so they are not a speed measurement. The
   notebook text and the figure title say the same.
5. Chapter 5 no longer calls the notebook a re-run of `scripts/initial_mse.py`.
6. Figures redrawn: `01-two-distances-line` (text moved off the line), `04-before-and-after-warp`
   (legend below the bars), `07-squeeze` (label moved off the peak and the dashed line).

Step 2 and nits: chapter 3 gap now "at most 4e-16" and asserted `< 1e-9` (was `2e-4`); chapter 4
caption "0.36 to 0.57 before, 2e-15 to 2e-14 after" and "within 2e-14"; chapter 4 reach is asserted
equal to pi over frequency (both sides, `1e-6`), not only `<=`; chapter 6 adds the measured fall of
28 times beside the book's 30.

Step 3 figures: `04-covers-within-reach` redrawn (one-headed arrow along the label line from the black
input, which now sits on the line; separate x range for the fast sine; text moved off the curve minima);
`06-frequency-strip` (vertical error now the mean of 200,000, so the three titles read 0.59, and no points
on the plot edge; titles on three lines); `06-before-and-after-training` (loss before training is now the
300-draw mean, about 0.7 at every size); `03-slope-sandwich` (legend inside the right panel, no blank strip).

Step 4 tolerances: chapter 6 table nearest column is compared row by row within 5 standard errors of
the row's own 500 points (largest gap 0.9 standard errors); "nearest falls with size" compares every
consecutive pair; chapter 5 width check now zeroes the last bias in the same networks (output minus
the bias) and adds a check against the exact width-free mean 1/3 + 2/27 within 4 standard errors
(differences -0.0057, -0.0076, -0.0024, +0.0071, -0.0008; passes); chapter 7 loss tolerance tightened
from 4e-3 to 1e-3 (observed 2.5e-4). `float(loss)` replaced by `loss.item()`.

Not changed: the coin-flip tautology in chapter 5 is kept (it is the chapter's own arithmetic answer,
labelled as such). The chapter 6 and chapter 7 root-finder and warp "exact by construction" parts are
unchanged; they test the code, as the chapters say.
