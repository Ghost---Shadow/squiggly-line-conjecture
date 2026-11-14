# Part I experiments

One Jupyter notebook per chapter of [the book](../../book/README.md), in PyTorch.
Each notebook says which claim of its chapter it checks, runs the experiment,
asserts the result, and draws the chapter's figures with seaborn into
[`book/figures/`](../../book/figures/). They are measurements. The Lean files
are the proofs.

| Notebook | Chapter | What it checks |
|---|---|---|
| `ch01_two_distances.ipynb` | 1 | the worked example, the answers, nearest distance at most vertical error |
| `ch03_slope_sandwich.ipynb` | 3 | `vertical_error / √(1 + slope_limit²) ≤ nearest_distance ≤ vertical_error` |
| `ch04_nearness.ipynb` | 4 | the reach of a sine, the warp, the slope tax |
| `ch05_the_blind_loss.ipynb` | 5 | flat and jagged models, one-point marginals, untrained widths |
| `ch06_sine_theorem.ipynb` | 6 | the four claims, the chapter's table, and the sine model trained by SGD |
| `ch07_squeeze.ipynb` | 7 | reach, slope and loss under squeezing |

Chapter 2 is about reading Lean and has nothing to measure. `common.py` holds the
shared helpers: the sine model, the nearest-distance measure, the figure style.

The sine model is `sum over term of amplitudes[term] * sin(term * input + phases[term])`.
The number of terms is the model size (its width). Each term has a fixed integer
frequency and two learnable parameters, so there are `2 × num_terms` of them.

```bash
pip install torch numpy matplotlib seaborn pandas jupyter nbconvert ipykernel
jupyter lab experiments/part1                       # open a notebook and run the cells
jupyter nbconvert --to notebook --execute --inplace experiments/part1/ch*.ipynb    # run them all
```

Every notebook is seeded, so two runs give the same numbers. A failed check
raises an error and stops the notebook, so a notebook that runs to the end has
passed. The nearest distance is measured on a fine polyline, so the bound
checks allow a slack of `3e-4`. `get_nearest_distance` always samples the point straight above or below the
data point unless it is called with `include_foot=False`; every check of "nearest <= vertical error" uses
`include_foot=False`, because otherwise that bound would hold by construction.
