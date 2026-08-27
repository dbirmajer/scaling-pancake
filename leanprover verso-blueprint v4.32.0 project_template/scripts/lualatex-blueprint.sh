#!/usr/bin/env bash

set -euo pipefail

tex_file=""
for arg in "$@"; do
  case "$arg" in
    *.tex) tex_file="$arg" ;;
  esac
done

if [[ -n "$tex_file" ]] && ! grep -q "Blueprint Unicode fallbacks" "$tex_file"; then
  perl -0pi -e 's/(?=\\title\{)/% Blueprint Unicode fallbacks\n\\newunicodechar{ℝ}{\\ensuremath{\\mathbb{R}}}\n\\newunicodechar{ℕ}{\\ensuremath{\\mathbb{N}}}\n\\newunicodechar{ℐ}{\\ensuremath{\\mathcal{I}}}\n\\newunicodechar{∈}{\\ensuremath{\\in}}\n\\newunicodechar{⊆}{\\ensuremath{\\subseteq}}\n\\newunicodechar{↔}{\\ensuremath{\\leftrightarrow}}\n\\newunicodechar{∨}{\\ensuremath{\\lor}}\n\\newunicodechar{⋅}{\\ensuremath{\\cdot}}\n\\newunicodechar{⋂}{\\ensuremath{\\bigcap}}\n\\newunicodechar{⋄}{\\ensuremath{\\diamond}}\n\\newunicodechar{◇}{\\ensuremath{\\diamond}}\n\\newunicodechar{□}{\\ensuremath{\\square}}\n\\newunicodechar{⅟}{\\ensuremath{1\/}}\n\\newunicodechar{⋯}{\\ensuremath{\\cdots}}\n/' "$tex_file"
fi

exec lualatex "$@"
