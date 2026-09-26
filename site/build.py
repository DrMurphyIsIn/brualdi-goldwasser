"""Build site/index.html from template.html, injecting the n <= 491 maximizer table from the Lean data.

    python3 site/build.py
"""
import json, re
from pathlib import Path

HERE = Path(__file__).resolve().parent
src = (HERE.parent / "formalization/R3Cert/BGSpiderTableData.lean").read_text()
body = src.split("def tabData")[1].split(":=", 1)[1].split("\n\n")[0]
rows = [list(map(int, t)) for t in re.findall(r"\((\d+), (\d+), (\d+), (\d+)\)", body)]
assert len(rows) == 488
html = (HERE / "template.html").read_text().replace("/*ROWS*/[]", json.dumps(rows, separators=(",", ":")))
html = html.replace("<!--LABS_HTML-->", (HERE / "labs.html").read_text())
html = html.replace("/*LABS_JS*/", (HERE / "labs.js").read_text())
(HERE / "index.html").write_text(html)
print("wrote", HERE / "index.html", len(html), "bytes")

pdf = HERE.parent / "paper/paper.pdf"
if pdf.exists():
    (HERE / "paper.pdf").write_bytes(pdf.read_bytes())
    print("copied paper.pdf")
