#!/usr/bin/env bash
# Build the book as a static site: book/build/site/index.html and one page per
# chapter.
#
#   bash book/html/build.sh [version]
#
# Needs pandoc. The version is shown in the footer of every page; it defaults
# to "draft".
set -euo pipefail

cd "$(dirname "$0")/.."          # the book folder
version="${1:-draft}"
today="$(date -u +'%-d %B %Y')"
book_title="The Squiggly Line Theorem: A Guided Tour of the Proofs"
site="build/site"

rm -rf "$site"
mkdir -p "$site/graphs" build/html-parts

cp html/style.css "$site/style.css"

printf '<div class="topbar"><a href="index.html">%s</a></div>\n' "$book_title" \
  > build/html-parts/before.html
printf '<div class="footer">Version %s, %s</div>\n' "$version" "$today" \
  > build/html-parts/after.html

build_page() {
  local source="$1" output="$2" page_title
  page_title="$(grep -m1 '^# ' "$source" | sed 's/^# //')"
  if [ "$source" = "README.md" ]; then
    page_title="$book_title"
  else
    page_title="$page_title | $book_title"
  fi
  pandoc \
    --from gfm \
    --to html5 \
    --standalone \
    --lua-filter html/site.lua \
    --css style.css \
    --metadata lang=en \
    --metadata pagetitle="$page_title" \
    --include-before-body build/html-parts/before.html \
    --include-after-body build/html-parts/after.html \
    --output "$site/$output" \
    "$source"
}

build_page README.md index.html

for source in [0-9][0-9]-*.md glossary.md how-to-cite.md; do
  build_page "$source" "${source%.md}.html"
done

# Copy only the images the book uses.
grep -oh '(\.\./graphs/[^)]*)' [0-9][0-9]-*.md glossary.md how-to-cite.md README.md \
  | sed 's/^(\.\.\///; s/)$//' | sort -u \
  | while read -r image; do
      cp "../$image" "$site/$image"
    done

# Figures drawn for the book live in book/figures and are linked as figures/x.png.
mkdir -p "$site/figures"
grep -oh '(figures/[^)]*)' [0-9][0-9]-*.md glossary.md how-to-cite.md README.md \
  | sed 's/^(//; s/)$//' | sort -u \
  | while read -r image; do
      cp "$image" "$site/$image"
    done

echo "built book/$site (version ${version})"
