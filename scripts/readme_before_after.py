"""Draw graphs/readme_before_and_after.png: the headline theorem in both styles.

The left panel is the statement as it was first written, read from git
history. The right panel is an excerpt of the statement as it is now, read
from the Lean file. Run from the repository root:

    python scripts/readme_before_after.py
"""
import pathlib
import re
import subprocess

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_FILE = "lean/SquigglyLine/Theorem/SquigglyLineTheorem.lean"
FIRST_VERSION = "d1e1686"          # the last commit before the restyle

PAGE, INK, MUTED = "#ece8e1", "#1b1b22", "#55555e"
DARK, DARK_INK, ORANGE = "#1d1d23", "#d6d6dc", "#f2a64a"
LIGHT, COMMENT, TEAL, ACCENT = "#ffffff", "#77777f", "#0f6b5f", "#9a4a1a"
MONO = ["DejaVu Sans Mono", "Segoe UI Symbol"]
SANS = ["Segoe UI", "DejaVu Sans"]

CRYPTIC = {
    "A": "amplitude", "ℓ": "loss_fn", "μ": "data_distribution", "φ": "phase",
    "w": "frequency", "w'": "other_frequency", "p": "data_point", "x": "input",
    "hℓ": "loss_is_measurable", "hμ": "labels_in_band", "hw": "frequency_pos",
    "hp": "label_is_in_band", "ht": "target_stays_in_band",
}
TOKEN = re.compile(r"[^\W\d][\w']*|\s+|.", re.UNICODE)


def read_before():
    text = subprocess.run(["git", "show", f"{FIRST_VERSION}:{LEAN_FILE}"], cwd=ROOT,
                          capture_output=True, text=True, encoding="utf-8").stdout
    lines = text.split("\n")
    start = next(i for i, line in enumerate(lines) if line.startswith("theorem squiggly_line_theorem"))
    end = next(i for i, line in enumerate(lines) if line.startswith("end SquigglyLine"))
    return [line for line in lines[start:end] if line.strip()]


def read_after():
    lines = (ROOT / LEAN_FILE).read_text(encoding="utf-8").split("\n")
    start = next(i for i, line in enumerate(lines) if line.startswith("theorem squiggly_line_theorem"))
    end = next(i for i, line in enumerate(lines) if "claim_4_warp_fits_any_target := by" in line)
    excerpt = lines[start:end + 1]
    cut_from = next(i for i, line in enumerate(excerpt) if line.strip().startswith("-- Claim 2:"))
    cut_to = next(i for i, line in enumerate(excerpt) if line.strip().startswith("-- Claim 4:"))
    return excerpt[:cut_from] + ["    ⋯ claims 2 and 3 are left out of this picture ⋯", ""] + excerpt[cut_to:]


def colour_before(line):
    return [(tok, ORANGE if tok in CRYPTIC else DARK_INK) for tok in TOKEN.findall(line)]


def colour_after(line):
    code, sep, comment = line.partition("--")
    runs = [(tok, TEAL if tok.startswith("claim_") else INK) for tok in TOKEN.findall(code)]
    if sep:
        runs.append((sep + comment, COMMENT))
    return runs


def draw_code(ax, lines, colour, left, top, size, leading):
    # measure the width of one character as it is drawn, in inches
    probe = ax.text(0, 0, "M" * 100, family=MONO, fontsize=size)
    ax.figure.canvas.draw()
    advance = probe.get_window_extent().width / 100 / ax.figure.dpi
    probe.remove()
    for row, line in enumerate(lines):
        column = 0
        for text, color in merge(colour(line)):
            if text.strip():
                ax.text(left + column * advance, top - row * leading, text, color=color,
                        family=MONO, fontsize=size, va="top", ha="left",
                        style="italic" if color == COMMENT else "normal")
            column += len(text)


def merge(runs):
    merged = []
    for text, color in runs:
        if merged and (merged[-1][1] == color or not text.strip()):
            merged[-1] = (merged[-1][0] + text, merged[-1][1])
        else:
            merged.append((text, color))
    return merged


def panel(ax, x, y, width, height, face, edge):
    ax.add_patch(FancyBboxPatch((x, y), width, height, boxstyle="round,pad=0,rounding_size=0.14",
                                facecolor=face, edgecolor=edge, linewidth=1))


def main():
    before, after = read_before(), read_after()
    W, H, size = 19.0, 13.3, 7.6
    leading = size * 1.42 / 72
    fig = plt.figure(figsize=(W, H), dpi=200, facecolor=PAGE)
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, W)
    ax.set_ylim(0, H)
    ax.axis("off")

    ax.text(0.6, H - 0.55, "SAME THEOREM  ·  SAME MATHEMATICS", color=ACCENT, family=SANS,
            fontsize=12, fontweight="bold", va="top")
    ax.text(0.6, H - 0.95, "A Lean statement, before and after", color=INK, family=SANS,
            fontsize=34, fontweight="bold", va="top")
    ax.text(0.6, H - 1.85, "The squiggly line theorem, rewritten so that a reader who knows Python can "
            "follow it. Only the names, the types and the layout changed.", color=MUTED,
            family=SANS, fontsize=14, va="top")

    top, bottom = H - 2.55, 1.35
    left_w = 7.25
    panel(ax, 0.6, bottom, left_w, top - bottom, DARK, DARK)
    panel(ax, 0.6 + left_w + 0.35, bottom, W - 1.2 - left_w - 0.35, top - bottom, LIGHT, "#d9d5cd")

    ax.text(0.9, top - 0.3, " BEFORE ", color=DARK, family=SANS, fontsize=10, fontweight="bold",
            va="top", bbox=dict(boxstyle="round,pad=0.35", facecolor=ORANGE, edgecolor="none"))
    ax.text(2.05, top - 0.3, "As first written. Orange marks every short name.", color=DARK_INK,
            family=SANS, fontsize=12, va="top")
    draw_code(ax, before, colour_before, 0.9, top - 0.85, size, leading)

    legend_top = bottom + 2.25
    ax.plot([0.9, 0.3 + left_w], [legend_top + 0.25, legend_top + 0.25], color="#3a3a44", linewidth=1)
    ax.text(0.9, legend_top, f"The {len(CRYPTIC)} short names, decoded", color=DARK_INK,
            family=SANS, fontsize=12, fontweight="bold", va="top")
    for index, (short, long) in enumerate(CRYPTIC.items()):
        column, row = divmod(index, 7)
        x = 0.9 + column * 3.4
        y = legend_top - 0.42 - row * 0.24
        ax.text(x, y, short, color=ORANGE, family=MONO, fontsize=9, va="top")
        ax.text(x + 0.35, y, "→ " + long, color=DARK_INK, family=MONO, fontsize=9, va="top")

    right = 0.6 + left_w + 0.35 + 0.3
    ax.text(right, top - 0.3, " AFTER ", color="white", family=SANS, fontsize=10, fontweight="bold",
            va="top", bbox=dict(boxstyle="round,pad=0.35", facecolor=TEAL, edgecolor="none"))
    ax.text(right + 1.05, top - 0.3, "An excerpt of the file as it is now. Comments at the end of a "
            "line say why.", color=MUTED, family=SANS, fontsize=12, va="top")
    draw_code(ax, after, colour_after, right, top - 0.85, size, leading)

    for x, big, small in [(0.6, f"{len(CRYPTIC)} → 0", "short names"),
                          (3.6, "4 claims", "each with its own name"),
                          (6.9, "Same mathematics", "Lean proves the original statement from the new one")]:
        ax.text(x, 1.05, big, color=INK, family=SANS, fontsize=22, fontweight="bold", va="top")
        ax.text(x, 0.52, small, color=MUTED, family=SANS, fontsize=11, va="top")
    ax.text(W - 0.6, 0.75, f"Before: commit {FIRST_VERSION}. After: {LEAN_FILE}.\n"
            "Both are copied from the repository without edits.", color=MUTED, family=SANS,
            fontsize=10, va="top", ha="right")

    fig.savefig(ROOT / "graphs" / "readme_before_and_after.png", facecolor=PAGE)
    print("lines before:", len(before), "after:", len(after))


if __name__ == "__main__":
    main()
