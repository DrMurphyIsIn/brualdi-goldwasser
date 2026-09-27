# The project page

Published at <https://drmurphyisin.github.io/brualdi-goldwasser/> by the `pages` workflow.

`template.html`, `labs.html` and `labs.js` are the sources. `build.py` fills in the table of maximizers
from `formalization/R3Cert/BGSpiderTableData.lean`, inlines the labs, and copies `paper/paper.pdf`,
producing the single self-contained file `index.html` (no external scripts or network requests).

```bash
python3 site/build.py          # standard library only
open site/index.html           # or any browser; #treelab, #spiderlab, #races open the labs directly
```
