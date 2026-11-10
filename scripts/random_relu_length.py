"""Random ReLU networks in 1-D: curve length, turns and distance to a scatter, no training.

Added 10 Nov 2026 (see handoff.md). Weights He-uniform (+-sqrt(6/fan_in)), hidden biases
uniform +-0.5, output shifted and scaled so that its range over [-1,1] is exactly [-1,1].
300 networks for each size. Width sweep: 2 hidden layers. Depth sweep: width 64.

Caveats:
- 1-D input only, and the output is rescaled, so amplitude is controlled but the
  marginal distribution of f(x) is NOT held fixed (frequency_isolation.py does that).
- Only the Euclidean nearest-point distance is measured. The vertical residual, which
  RESOLUTION.md shows is the quantity that matters for training, is not measured here.
- Distances use a fixed 4001-point grid. For the reference sine with 16 periods this
  overestimates the distance by about 7% (0.0209 against 0.0196 with exact segment
  projection). Use curves.py for anything steeper.
Writes results2.json to the current directory.
"""
import json
import numpy as np

rng = np.random.default_rng(1)
GRID = np.linspace(-1.0, 1.0, 4001)
N_NETS = 300
POINTS = np.random.default_rng(0).uniform(-1, 1, size=(200, 2))


def random_mlp(width, depth):
    h = GRID[:, None]
    fan_in = 1
    for _ in range(depth):
        b = np.sqrt(6.0 / fan_in)
        W = rng.uniform(-b, b, size=(fan_in, width))
        bias = rng.uniform(-0.5, 0.5, size=width)
        h = np.maximum(h @ W + bias, 0.0)
        fan_in = width
    W = rng.uniform(-1, 1, size=(fan_in, 1))
    y = (h @ W)[:, 0]
    lo, hi = y.min(), y.max()
    if hi - lo < 1e-12:
        return np.zeros_like(y)
    return 2 * (y - lo) / (hi - lo) - 1


def arc_length(y):
    return float(np.sum(np.sqrt(np.diff(GRID) ** 2 + np.diff(y) ** 2)))


def turns(y):
    s = np.sign(np.diff(y))
    s = s[s != 0]
    return int(np.sum(s[1:] != s[:-1]))


def mean_distance(y):
    d2 = (POINTS[:, 0:1] - GRID[None, :]) ** 2 + (POINTS[:, 1:2] - y[None, :]) ** 2
    return float(np.sqrt(d2.min(axis=1)).mean())


def sweep(configs):
    out = []
    for width, depth in configs:
        L, D, T = [], [], []
        for _ in range(N_NETS):
            y = random_mlp(width, depth)
            L.append(arc_length(y)); D.append(mean_distance(y)); T.append(turns(y))
        L, D, T = np.array(L), np.array(D), np.array(T)
        params = (width + width) + (depth - 1) * (width * width + width) + width
        se = lambda a: a.std() / np.sqrt(N_NETS)
        out.append(dict(width=width, depth=depth, params=int(params), len_mean=L.mean(), len_sem=se(L),
                        dist_mean=D.mean(), dist_sem=se(D), turns_mean=T.mean()))
        print(f"w={width:5d} d={depth:2d} params={params:8d} len={L.mean():6.3f}+-{se(L):.3f} "
              f"turns={T.mean():6.2f} dist={D.mean():.4f}+-{se(D):.4f}")
    return out


res = {}
print("width sweep (2 hidden layers)")
res["width"] = sweep([(w, 2) for w in (2, 4, 8, 16, 32, 64, 128, 256, 512)])
print("depth sweep (width 64)")
res["depth"] = sweep([(64, d) for d in (1, 2, 3, 4, 6, 8, 12, 16)])
# all nets pooled: does length predict distance?
L, D = [], []
for w, d in [(w, d) for w in (4, 16, 64, 256) for d in (1, 2, 4, 8)]:
    for _ in range(100):
        y = random_mlp(w, d); L.append(arc_length(y)); D.append(mean_distance(y))
L, D = np.array(L), np.array(D)
res["pooled_corr_len_dist"] = float(np.corrcoef(L, D)[0, 1])
res["pooled"] = dict(len=L.tolist(), dist=D.tolist())
print("pooled correlation(length, distance):", res["pooled_corr_len_dist"])
# reference curves spanning the box
res["diag_dist"] = mean_distance(GRID.copy())
for k in (1, 2, 4, 8, 16):
    y = np.sin(k * np.pi * GRID)
    print(f"sine with {k} periods: len={arc_length(y):.2f} dist={mean_distance(y):.4f}")
    res[f"sine_{k}"] = dict(len=arc_length(y), dist=mean_distance(y))
print("diagonal y=x: len=%.3f dist=%.4f" % (arc_length(GRID), res["diag_dist"]))
json.dump(res, open("results2.json", "w"))
