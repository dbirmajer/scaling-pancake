#!/usr/bin/env bash

set -euo pipefail

export PATH="$PWD/scripts:$PATH"

lake build ProjectTemplate.Blueprint
lake lean ProjectTemplateMain.lean -- --run ProjectTemplateMain.lean \
  --output _out/site \
  --pdf \
  --pdf-engine lualatex-blueprint.sh

cp _out/site/pdf/main.pdf _out/site/html-multi/calculus-in-lean.pdf

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/calculus-in-lean.pdf
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
