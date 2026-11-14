# Writing a chapter's notebook: the brief for helpers

Each chapter of the book gets **one Jupyter notebook** that checks the
chapter's claims with numbers. A notebook may hold several experiments.
Your prompt names your chapter. Everything else is here.

## Read first, once each

1. `experiments/part1/README.md`, `experiments/part1/common.py` and one
   finished notebook, `experiments/part1/ch04_nearness.ipynb`. Copy their
   form: what a cell explains, how a check is asserted, how a figure is
   drawn and saved.
2. Your chapter in `book/`, and its "Run it yourself" counterpart in
   `book/04-nearness.md`, to see how a chapter reports measured numbers.
3. The Lean file your chapter names, statements only, so that each
   experiment checks what the theorem says and nothing wider.

## What to make

- `experiments/partN/chNN_short_name.ipynb`, where `partN` is the part of
  the book your chapter is in (`part2` for chapters 8 to 12).
- Its figures, saved as PNG into `book/figures/NN-what-it-shows.png`.
- In your chapter file, the figures where they help and a section
  `## Run it yourself` just before `## What is not shown` (or before
  `## Check yourself` if the chapter has no such section): what the
  notebook checks, the measured numbers, and the command to run it.

## Rules for the notebook

- **One experiment per claim the chapter makes.** State the claim in a
  markdown cell, run the experiment, then `assert` the result and print a
  line starting `[PASS]`. A failed check must stop the notebook.
- **A check must be able to fail.** Ask of each one: would it fail if the
  claim were false? Do not loosen a threshold to make a check pass
  without saying so in the cell and in your report.
- **Seed everything.** Two runs must print identical `[PASS]` lines.
- **The right stand-in model.** Use the model the theorem is about. Where
  a proof assumes a model that is *linear in its weights*, train the sine
  and cosine coefficients of fixed frequencies, which is linear. Training
  an amplitude and a phase per term is not linear: use it only to show
  what changes when the features move, and say so. For folds use the tent
  layer and ReLU networks. Say in the first cell which model is used.
- **Cheap.** The whole notebook runs in under two minutes on a laptop CPU.
- **Names.** Locals are `snake_case`, constants are `SCREAMING_SNAKE_CASE`,
  functions are verbs (`measure_travel`, `draw_curve`). No single-letter
  names, in code or in prose.
- **Figures.** Use the figure style in `common.py` (import it from
  `experiments/part1`; do not edit it). Every axis is labelled, the title
  says what the figure shows, and no label sits on a curve.
- **Self-contained.** Helpers your chapter needs go in your notebook.
  Create no shared file.

## Rules for the chapter text

- Numbers in the chapter are copied from the notebook's output.
- Call them **measured**. An experiment is evidence, not a proof: say so
  once in the section.
- Change nothing else in the chapter, and do not touch quoted Lean.

## Before you report

```bash
jupyter nbconvert --to notebook --execute --inplace experiments/partN/chNN_*.ipynb
python book/tools/check_book.py NN
```

Run the notebook twice and compare the `[PASS]` lines. The checker must
end with `problems: 0`.

Write only your notebook, your figures and your chapter. Do not run git.

## Your report

Under 100 words: files written, the `[PASS]` count, any threshold you
changed after a failure and why, and any claim of the chapter that the
experiment did **not** bear out. That last item is the most useful thing
you can report.
