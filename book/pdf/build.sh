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
  [0-9][0-9]-*.md glossary.md how-to-cite.md

echo "built book/build/the-squiggly-line-theorem-book.pdf (version ${version})"
