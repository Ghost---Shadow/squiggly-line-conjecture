"""
common.py

Shared pieces for the Part I experiments (chapters 1 to 7 of the book).

Everything is plain PyTorch in float64. The model is the sine model:

    model(input) = sum over term = 1 .. num_terms of
                   amplitudes[term] * sin(term * input + phases[term])

Term `term` has the fixed integer frequency `term`. The amplitudes and the
phases are the learnable parameters, so the model has 2 * num_terms of them and
trains with ordinary SGD. With num_terms = 1 it is the single sine of chapter 6.

Names follow the book: `slope_limit`, `vertical_error`, `nearest_distance`.
"""

import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import seaborn as sns
import torch

torch.set_default_dtype(torch.float64)

HERE = Path(__file__).resolve().parent
FIGURES = HERE.parent.parent / "book" / "figures"

# Seaborn's default theme and its "deep" palette. Colour follows the quantity in every figure:
# blue is the nearest distance, orange is the vertical error, purple is the model, green is a
# bound, grey is "before" or "without".
_DEEP = sns.color_palette("deep")
NEAREST, VERTICAL, BOUND, MODEL, BEFORE = _DEEP[0], _DEEP[1], _DEEP[2], _DEEP[4], _DEEP[7]
DATA, MUTED, GRID = "black", _DEEP[7], "#d9d9d9"


def use_style():
    """The book's figures use seaborn's default theme."""
    sns.set_theme()


def save_figure(figure, name):
    """Write a figure to book/figures/<name>.png, where the chapters link it."""
    FIGURES.mkdir(parents=True, exist_ok=True)
    figure.savefig(FIGURES / f"{name}.png", dpi=160, bbox_inches="tight")
    print(f"wrote book/figures/{name}.png")

TWO_PI = 2.0 * math.pi


class SineModel(torch.nn.Module):
    """A sum of sines with fixed integer frequencies and learnable amplitudes and phases."""

    def __init__(self, num_terms, amplitude_scale=1.0, generator=None):
        super().__init__()
        self.num_terms = num_terms
        self.register_buffer("frequencies", torch.arange(1, num_terms + 1, dtype=torch.float64))
        amplitudes = torch.randn(num_terms, generator=generator) * amplitude_scale / math.sqrt(num_terms)
        phases = torch.rand(num_terms, generator=generator) * TWO_PI
        self.amplitudes = torch.nn.Parameter(amplitudes)
        self.phases = torch.nn.Parameter(phases)

    def forward(self, inputs):
        angles = inputs.unsqueeze(-1) * self.frequencies + self.phases
        return (self.amplitudes * torch.sin(angles)).sum(dim=-1)

    def get_slope_limit(self):
        """The steepest slope the model can have: sum of frequency * |amplitude|."""
        return float((self.frequencies * self.amplitudes.detach().abs()).sum())


def evaluate_sine(amplitude, frequency, phase, inputs):
    """The single sine of chapter 6: amplitude * sin(frequency * input + phase)."""
    return amplitude * torch.sin(frequency * inputs + phase)


def get_vertical_error(model_value, label):
    return abs(float(label) - float(torch.as_tensor(model_value).detach()))


def get_distance_to_polyline(xs, ys, point_x, point_y):
    """Exact distance from a point to the polyline through (xs, ys)."""
    start_x, start_y = xs[:-1], ys[:-1]
    step_x, step_y = xs[1:] - start_x, ys[1:] - start_y
    length_squared = (step_x ** 2 + step_y ** 2).clamp_min(1e-300)
    along = ((point_x - start_x) * step_x + (point_y - start_y) * step_y) / length_squared
    along = along.clamp(0.0, 1.0)
    nearest_x = start_x + along * step_x
    nearest_y = start_y + along * step_y
    return torch.sqrt((nearest_x - point_x) ** 2 + (nearest_y - point_y) ** 2).min()


def get_nearest_distance(curve, point_x, point_y, slope_limit, resolution=1e-3,
                         max_points=3_000_000, domain=None, include_foot=True):
    """
    Distance from the data point to the graph of `curve`.

    The nearest point is no further than the vertical error, so only inputs
    within the vertical error of `point_x` can hold it. The window is sampled
    finely enough that the curve moves at most `resolution` between samples,
    and the distance is exact to the polyline through the samples.

    `domain` is an optional (low, high) pair: the curve is only drawn there.

    With `include_foot=True` the point straight above or below the data point is always one of the
    samples, so the answer can never exceed the vertical error: that is a fact about the code. A check
    of the claim "nearest <= vertical" must pass `include_foot=False`. The sample count is then even,
    the window is centred on the data point, the vertical foot is not a sample, and the answer is not
    clamped to anything.
    """
    point_x = float(point_x)
    point_y = float(point_y)
    with torch.no_grad():
        model_value = float(curve(torch.tensor([point_x])))
        vertical_error = abs(point_y - model_value)
        if vertical_error == 0.0:
            return 0.0
        window_low, window_high = point_x - vertical_error, point_x + vertical_error
        if domain is not None:
            window_low, window_high = max(window_low, domain[0]), min(window_high, domain[1])
        point_count = int((window_high - window_low) * math.sqrt(1 + slope_limit ** 2) / resolution) + 3
        point_count = min(max(point_count, 101), max_points)
        if include_foot:
            point_count += 1 - point_count % 2          # odd count
        else:
            point_count += point_count % 2             # even count: the centre of the window is not a sample
        xs = torch.linspace(window_low, window_high, point_count)
        if include_foot:
            xs = torch.cat([xs, torch.tensor([point_x])]).sort().values      # the vertical foot is a sample
        ys = curve(xs)
        nearest = float(get_distance_to_polyline(xs, ys, point_x, point_y))
    return nearest


def report(label, passed, detail=""):
    """Print one check. A failed check stops the notebook, so a broken claim cannot hide."""
    mark = "PASS" if passed else "FAIL"
    print(f"[{mark}] {label}" + (f"  ({detail})" if detail else ""))
    assert passed, f"check failed: {label}"
    return True


def get_nearest_hit(amplitude, frequency, phase, inputs, labels):
    """
    For each (input, label) pair, the nearest input that the sine sends exactly to the label.

    The inputs that hit a label are known in closed form:
        (asin(label / amplitude) - phase + 2 pi k) / frequency
        (pi - asin(label / amplitude) - phase + 2 pi k) / frequency
    so the answer is exact, not estimated. This is the warp of chapter 4.
    """
    angle = torch.asin((labels / amplitude).clamp(-1.0, 1.0))
    candidates = []
    for base in (angle, math.pi - angle):
        first_hit = (base - phase) / frequency
        spacing = TWO_PI / frequency
        steps = torch.round((inputs - first_hit) / spacing)
        for shift in (-1.0, 0.0, 1.0):
            candidates.append(first_hit + (steps + shift) * spacing)
    candidates = torch.stack(candidates)
    best = (candidates - inputs).abs().argmin(dim=0)
    return candidates.gather(0, best.unsqueeze(0)).squeeze(0)
