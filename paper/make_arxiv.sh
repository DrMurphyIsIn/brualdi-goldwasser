#!/bin/bash
# Build the arXiv source package paper/arxiv.tar.gz and test-compile it in a clean directory.
set -euo pipefail
cd "$(dirname "$0")"
python3 gen_table.py >/dev/null
python3 figdata.py >/dev/null
rm -rf arxiv && mkdir -p arxiv/figdata
cp paper.tex table_maximizers.tex arxiv/
cp figdata/*.dat arxiv/figdata/
# arXiv's TeX Live builds pdflatex sources; \pdfoutput=1 makes that explicit.
grep -q '^\\pdfoutput=1' arxiv/paper.tex || sed -i.bak '1s/^/\\pdfoutput=1\n/' arxiv/paper.tex && rm -f arxiv/paper.tex.bak
(cd arxiv && pdflatex -interaction=nonstopmode paper.tex >/dev/null && pdflatex -interaction=nonstopmode paper.tex > build.log)
grep -E "^!|Output written" arxiv/build.log
# arXiv wants the .bbl-free, .aux-free sources only (the bibliography is inline).
(cd arxiv && rm -f *.aux *.log *.out *.toc paper.pdf)
tar -czf arxiv.tar.gz -C arxiv .
rm -rf arxiv
echo "wrote paper/arxiv.tar.gz"; tar -tzf arxiv.tar.gz | head -20
