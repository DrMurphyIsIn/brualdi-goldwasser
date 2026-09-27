# The project page

Published at <https://drmurphyisin.github.io/brualdi-goldwasser/> by the `pages` workflow.

`template.html`, `labs.html` and `labs.js` are the sources. `build.py` fills in the table of maximizers
from `formalization/R3Cert/BGSpiderTableData.lean`, inlines the labs, and copies `paper/paper.pdf`,
producing the single self-contained file `index.html` (no external scripts or network requests).

```bash
python3 site/build.py          # standard library only
open site/index.html           # or any browser; #treelab, #spiderlab, #races open the labs directly
```

`telperion-explorer/index.html` is the Telperion Registry Explorer: a page generated in the Telperion
development repository from its missions registry, then patched by `scripts/explorer_feature_bg.py` to put
a Brualdi-Goldwasser tab in front (the script's docstring explains how). It is also self-contained. The
`pages` workflow publishes it at <https://drmurphyisin.github.io/brualdi-goldwasser/telperion-explorer/>.
