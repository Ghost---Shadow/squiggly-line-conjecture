# Paper

> **Draft of 11 Nov 2026, not reviewed.** Drafted by an AI assistant and stopped
> before a final pass. The references have not been independently checked. The
> draft predates several results now in the repository. The README at the top
> of the repository is the current state.

"The Squiggly Line Conjecture: A Geometric Picture of Overparameterization That
Training Cannot Use". A preprint in NeurIPS format. It has not been submitted to
or accepted by NeurIPS; the style is loaded with the `preprint` option, so the
footer reads "Preprint."

## Build

From this folder (MiKTeX or TeX Live):

```bash
latexmk -pdf main.tex
```

or, by hand:

```bash
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

The output is `main.pdf`. `latexmk -c` removes the intermediate files.

## Layout

| Path | Contents |
|---|---|
| `main.tex` | preamble, title, abstract |
| `sections/01_introduction.tex` ... `06_discussion.tex` | main text |
| `sections/A_appendix.tex` | proofs, the record of earlier errors, experimental details |
| `references.bib` | bibliography (natbib, `plainnat`) |
| `neurips_2026.sty` | official style file, unmodified |

The four figures are read from `../graphs/readme_*.png`, which
`../scripts/readme_figures.py` draws. Every number in the paper comes from the
scripts in `../scripts/` or from `../docs/RESOLUTION.md`.

## Style file

`neurips_2026.sty` is from
<https://media.neurips.cc/Conferences/NeurIPS2026/Formatting_Instructions_For_NeurIPS_2026.zip>,
linked from the NeurIPS 2026 Call for Papers.
