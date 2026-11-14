# Writing a chapter of the book: the brief for helpers

This is the standing brief for anyone, human or AI, who writes a chapter
of the book in this folder. Your prompt names the chapters that are
yours. Everything else you need is here.

## The book and its reader

The book is a guided tour of the machine-checked proofs in this
repository. Parts I to III (chapters 1 to 16) are written. They give the
theorem, the tools, and a short map of what the tools say about deep
learning. Parts IV to VII, which you are writing, go through the
supporting proofs **one topic per chapter**, gently, and connect each to
the research or the practice it is about.

The reader can read Python and remembers school mathematics. They do not
know Lean, and they may not know the deep-learning result the chapter is
about. They have read chapters 1 to 16.

## Your job

Write the chapter files named in your prompt, in `book/`, with the Write
tool. Then run the checker on them and fix what it reports.

- Write **only** your chapter files. Do not edit any other file.
- Do **not** run git, and do not build Lean.
- Do not search the web. Everything is in the repository.
- Write files with the Write tool, never a shell heredoc.

## What to read, once each

1. Three finished chapters, to see the form and the voice:
   `book/03-slope.md`, `book/04-nearness.md`, `book/10-the-kernel.md`.
2. The map chapter of your part (the table below says which): it already
   states your results in one line each. Your chapter must agree with it.
3. For each of your chapters, the **notes** listed in the table. A note
   is the plain-English account of the proofs, marks each statement
   **proved**, **argued**, **recalled** or **open**, and ends with "How
   this meets the squiggly line" and "What is not shown".
4. For each of your chapters, the **Lean files** listed. Read the header
   comment, then the statements. For a file over 300 lines, read the
   header, list the statements with
   `grep -n -E "^(theorem|def|noncomputable def|abbrev)" <file>`, and
   read only the ones you will use. Skim a proof only for the names
   after `have`: they are the outline of the argument.

## The shape of a chapter

Follow this template. Keep the section titles, except where a different
title says the same thing better.

```
# N. Title

**In the repository:**
[`File.lean`](../lean/SquigglyLine/.../File.lean),
note [`name.md`](../docs/supporting/.../name.md).
**You need:** chapters ... (the earlier chapters this one leans on)

## The idea
## An example you can do by hand
## The statement
## Why it is true
## What it explains
## How this meets the squiggly line
## What is not shown
## Check yourself

Previous: [..](..) · Next: [..](..)
```

- **The idea.** Start from something the reader has met: a habit of
  people who train models, or a well-known puzzle. Say in plain words
  what is going on. Then give the result as one sentence in a quote
  block (`> ...`). No Lean yet.
- **An example you can do by hand.** Small round numbers. The reader
  should be able to check it with a calculator.
- **The statement.** One to three statements copied from the Lean file,
  the most important first. After each, a line starting *Read aloud:*
  that says it in one plain sentence, and a short explanation of any
  name or symbol chapters 1 to 16 did not introduce. Other results of
  the file can be named in a sentence with their theorem name in
  backticks, without being quoted.
- **Why it is true.** The argument in words, in a few short paragraphs,
  following the steps of the Lean proof.
- **What it explains.** The research or practice this connects to. Say
  what the proof adds to what people already believed.
- **How this meets the squiggly line.** Which of the six ideas it uses
  (slope, nearness, travel, the kernel and the lift, folds, averages),
  and which earlier chapter introduced them.
- **What is not shown.** Take this from the note. It is not optional.
  Say which simplified model the proof is for.
- **Check yourself.** Three questions, then a paragraph starting
  `**Answers.**`. Each answer must follow from a statement the chapter
  quoted or named.
- The last line is the navigation line, exactly in the form used by the
  finished chapters, with the titles and file names from the table
  below.

Length: 110 to 170 lines of your own prose, wrapped at about 72 columns
like the finished chapters. Quoted Lean does not count, but keep the
whole file under about 220 lines: quote fewer statements and name the
rest. Table rows and quoted Lean lines are not wrapped.

## Voice

- Plain English. Short sentences. One idea per sentence.
- Address the reader as "you". Do not write "we".
- British spelling, as in the repository: normalisation, initialisation.
- No single letters and no Greek for quantities, not even for a
  temporary one in an argument (write `move`, not `d`). Use the names the Lean
  file uses: `learning_rate`, `strength`, `slope_limit`, `decay`. In a
  formula write `×` for times and spell the names out.
- A formula that is not Lean goes in a plain fenced block or in
  backticks.
- Bold a key term the first time it appears, and say what it means.
- No dashes used as punctuation. Use a full stop, a comma or a colon.
- No sales talk: not "powerful", "elegant", "remarkably", "crucial".
- Be gentle. If a step needs an idea the reader may lack, give it one
  sentence. Do not say "clearly", "simply" or "obviously".

## Truth

These rules matter more than anything above.

- **Claim nothing the Lean statement does not say.** If the note marks
  something argued, recalled, measured or open, the chapter says so in
  the same word.
- **Quote Lean by copying.** Inside a ```` ```lean ```` block every line
  must be a whole line of the Lean file, unchanged, comments included.
  Quote a statement from its `/-- ... -/` comment or its `theorem` line
  down to the line ending in `:= by`. You may leave out the comment. For
  a long statement you may quote a run of whole lines and say what you
  left out. Never retype, shorten or tidy a line.
- **Every theorem or definition name in backticks must exist** in the
  Lean files.
- **Say which model.** Nearly every proof is for a simplified model: a
  fixed kernel, a model linear in its weights, one direction, two
  weights multiplied. Say which, in "What is not shown". Never write
  that a proof explains what real networks do.
- **Do the arithmetic twice.** Every number in an example or an answer
  must be right.
- **Papers.** Name a paper or its authors only where the note or
  `docs/supporting-proofs.md` names it, and mark it the way the notes
  do: `(**recalled**: Author year)`. Add no citation of your own.
- If the note and the Lean file disagree, follow the Lean file and say
  so in your report.

## The checker

```bash
python book/tools/check_book.py 17 18 19
```

Give it your chapter numbers. It checks that every quoted Lean line is
in the repository word for word, that names in backticks exist, and that
links resolve. It must end with `problems: 0`. Look at each warning: a
warning about a name is fine only if the name is a made-up local name
in a formula, not a theorem.

## Your report

Under 80 words: the files you wrote, the checker's last line, and any
place where a note and a Lean file disagreed or where you were unsure a
claim was proved. Do not summarise the chapters.

## Contents of the book

Lean paths are under `lean/SquigglyLine/`. Note paths are under `docs/`.
`T/` is `Supporting/Training/`, `S/` is `Supporting/NetworkShape/`,
`N/` is `Supporting/NewInputs/`. For notes, `t/` is
`supporting/training/`, `s/` is `supporting/network-shape/`, `n/` is
`supporting/new-inputs/`.

### Written: parts I to III

| # | File | Title |
|---|---|---|
| 1 | `01-two-distances.md` | Two distances |
| 2 | `02-reading-a-proof.md` | How to read a proof here |
| 3 | `03-slope.md` | Slope |
| 4 | `04-nearness.md` | Nearness |
| 5 | `05-the-blind-loss.md` | What the loss cannot see |
| 6 | `06-the-sine.md` | The theorem for sines |
| 7 | `07-any-function.md` | The theorem for any function |
| 8 | `08-folds.md` | Folds |
| 9 | `09-travel.md` | Travel |
| 10 | `10-the-kernel.md` | The kernel |
| 11 | `11-the-lift.md` | The lift |
| 12 | `12-polarizers.md` | Layers as polarizers |
| 13 | `13-one-factor.md` | One factor, again and again (map of part IV) |
| 14 | `14-combining-slope.md` | Three ways to combine slope (map of part V) |
| 15 | `15-averages.md` | Averages (map of part VI) |
| 16 | `16-new-inputs.md` | New inputs (map of part VII) |

### Part IV. Training, proof by proof (map: chapter 13)

| # | File | Title | Lean files | Notes |
|---|---|---|---|---|
| 17 | `17-the-shortest-trip.md` | The shortest trip | `T/LeastAction.lean` | `t/least-action.md` |
| 18 | `18-strong-directions-first.md` | Strong directions first | `T/SpectralBias.lean` | `t/spectral-bias.md` |
| 19 | `19-the-largest-step.md` | The largest step | `T/EdgeOfStability.lean`, `T/Optimisers.lean` | `t/edge-of-stability.md`, `t/spectral-bias.md` |
| 20 | `20-weight-decay-and-early-stopping.md` | Weight decay and early stopping | `T/WeightDecay.lean` | `t/weight-decay.md` |
| 21 | `21-dropout-and-noise.md` | Dropout, noise and other regularisers | `T/Dropout.lean`, `T/Regularisers.lean` | `t/dropout.md`, `t/weight-decay.md` |
| 22 | `22-batches-steps-and-budgets.md` | Batches, small steps and budgets | `T/BatchSize.lean`, `T/SmallSteps.lean`, `T/ComputeBudget.lean` | `t/batch-size.md`, `t/small-steps.md`, `t/compute-budget.md` |
| 23 | `23-adam-and-clipping.md` | Adam, AdamW and clipping | `T/StepRules.lean`, `T/AdamW.lean` | `t/step-rules.md` |
| 24 | `24-symmetry.md` | Symmetry: flat minima and normalisation | `T/Reparam.lean`, `T/Symmetry.lean`, `S/RmsNorm.lean` | `t/flat-minima.md`, `t/symmetry.md` |
| 25 | `25-classification.md` | Classification | `T/CrossEntropy.lean`, `T/PolicyGradient.lean` | `t/cross-entropy.md` |
| 26 | `26-the-perceptron.md` | The perceptron, XOR and no free lunch | `T/Perceptron.lean` | `t/perceptron.md` |
| 27 | `27-two-players.md` | Two players: the GAN game | `T/GanGame.lean` | `t/gan-game.md` |

### Part V. Architecture, proof by proof (map: chapter 14)

| # | File | Title | Lean files | Notes |
|---|---|---|---|---|
| 28 | `28-the-slope-of-a-network.md` | The slope of a network | `S/NetworkSlope.lean` | `s/network-slope.md` |
| 29 | `29-the-distance-field.md` | The distance field | `S/SignedDistance.lean`, `S/Eikonal.lean` | `s/signed-distance.md` |
| 30 | `30-signals-through-depth.md` | Signals through depth | `S/VanishingGradients.lean`, `S/Gain.lean`, `S/Activations.lean` | `s/vanishing-gradients.md`, `s/gain.md` |
| 31 | `31-skips-and-normalisation.md` | Skips and normalisation | `S/SkipAndNorm.lean`, `S/Residual.lean` | `s/skip-and-norm.md` |
| 32 | `32-depth-against-width.md` | Depth against width | `S/DepthSeparation.lean`, `S/UniversalApproximation.lean`, `S/KolmogorovArnold.lean` | `s/depth-separation.md`, `s/universal-approximation.md` |
| 33 | `33-convolution.md` | Convolution | `S/Convolution.lean` | `s/convolution.md` |
| 34 | `34-capacity-and-compression.md` | Capacity and compression | `S/Capacity.lean`, `S/Bottleneck.lean`, `S/CodeLength.lean`, `S/Mixtures.lean` | `s/capacity.md`, `s/information-bottleneck.md`, `s/code-length.md` |
| 35 | `35-the-landscape.md` | The landscape: connected fits and collapsed classes | `S/ModeConnectivity.lean`, `S/NeuralCollapse.lean` | `s/mode-connectivity.md`, `s/neural-collapse.md` |

### Part VI. Averages, proof by proof (map: chapter 15)

| # | File | Title | Lean files | Notes |
|---|---|---|---|---|
| 36 | `36-attention.md` | Attention | `S/Attention.lean`, `S/AttentionRate.lean` | `s/attention.md` |
| 37 | `37-ensembles-and-the-denoiser.md` | Ensembles and the ideal denoiser | `N/Averaging.lean` | `n/averaging.md` |
| 38 | `38-mixing.md` | Mixing: graphs, noise schedules and guidance | `N/Mixing.lean`, `N/OnAverage.lean` | `n/mixing.md` |
| 39 | `39-hard-choices-and-temperature.md` | Hard choices and temperature | `S/HardChoices.lean`, `S/Temperature.lean` | `s/attention.md`, `s/network-slope.md` |
| 40 | `40-neighbours.md` | Neighbours | `N/Neighbours.lean` | `n/neighbours.md` |
| 41 | `41-counting.md` | Counting | `N/Counting.lean` | `n/counting.md` |

### Part VII. New inputs, proof by proof (map: chapter 16)

| # | File | Title | Lean files | Notes |
|---|---|---|---|---|
| 42 | `42-same-kernel.md` | Same kernel, same predictions | `N/SameKernel.lean` | `n/same-kernel.md` |
| 43 | `43-bias-and-variance.md` | Bias and variance | `N/BiasVariance.lean` | `n/bias-variance.md` |
| 44 | `44-benign-overfitting.md` | Benign overfitting | `N/BenignOverfitting.lean` | `n/benign-overfitting.md` |
| 45 | `45-pruning-and-forgetting.md` | Pruning and forgetting | `N/Pruning.lean`, `N/Forgetting.lean` | `n/lottery-ticket.md`, `n/forgetting.md` |
| 46 | `46-the-dimpled-manifold.md` | The dimpled manifold | `N/Dimple.lean` | `n/dimpled-manifold.md` |

### Closing

| # | File | Title |
|---|---|---|
| 47 | `47-what-is-not-here.md` | What is not here |

The navigation line of a chapter links the chapter before it and the
chapter after it in this list, for example for chapter 18:

```
Previous: [17. The shortest trip](17-the-shortest-trip.md) · Next: [19. The largest step](19-the-largest-step.md)
```
