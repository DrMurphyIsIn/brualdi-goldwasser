# The paper

`paper.tex` is the paper; `paper.pdf` is the compiled version, kept in the repository so it can be read
without building anything.

## Build it

Needs a TeX distribution with `pdflatex` (TeX Live 2023 or later, or MacTeX) including the packages
`amsmath`, `mathtools`, `geometry`, `booktabs`, `longtable`, `microtype`, `enumitem`, `caption`,
`subcaption`, `xcolor`, `tikz`, `pgfplots` (with the `groupplots` library), `hyperref` and `cleveref`.
A full TeX Live install has all of them.

```bash
cd paper
python3 gen_table.py      # the appendix table, read from formalization/R3Cert/BGSpiderTableData.lean
python3 figdata.py        # the data behind the plots (figdata/*.dat)
pdflatex paper.tex && pdflatex paper.tex
```

Both Python scripts use only the standard library. `./make_arxiv.sh` builds the arXiv source package
`arxiv.tar.gz` and test-compiles it in a clean directory.
