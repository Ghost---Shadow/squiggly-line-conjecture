#!/usr/bin/env bash
# Build the book as one PDF: book/build/the-squiggly-line-theorem-book.pdf
#
#   bash book/pdf/build.sh [version]
#
# Needs pandoc, XeLaTeX and the DejaVu fonts. The version is printed on the
# title page; it defaults to "draft".
set -euo pipefail

cd "$(dirname "$0")/.."          # the book folder: image paths start here
version="${1:-draft}"
today="$(date -u +'%-d %B %Y')"

mkdir -p build
pandoc \
  --from gfm+smart \
  --metadata-file pdf/metadata.yaml \
  --metadata date="Version ${version}, ${today}" \
  --lua-filter pdf/book.lua \
  --pdf-engine xelatex \
  --top-level-division chapter \
  --number-sections \
  --toc --toc-depth 1 \
  --output build/the-squiggly-line-theorem-book.pdf \
  00-preface.md \
  01-two-distances.md \
  02-reading-a-proof.md \
  03-slope.md \
  04-nearness.md \
  05-the-blind-loss.md \
  06-the-sine.md \
  07-any-function.md \
  08-folds.md \
  09-travel.md \
  10-the-kernel.md \
  11-the-lift.md \
  12-polarizers.md \
  13-one-factor.md \
  14-combining-slope.md \
  15-averages.md \
  16-new-inputs.md \
  17-what-is-not-here.md \
  glossary.md \
  how-to-cite.md

echo "built book/build/the-squiggly-line-theorem-book.pdf (version ${version})"
