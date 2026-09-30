"""Patch the Telperion Registry Explorer so that it features Brualdi-Goldwasser.

The explorer page is generated in the Telperion development repository (private) by
`telperion/explorer/build.py`, with the Riemann campaigns in front and no links into that repository.
This script takes such a build and produces `site/telperion-explorer/index.html`: a Brualdi-Goldwasser tab
first (text, live plots from `paper/figdata/`), the registry defaulting to the `bg` campaign, and the
Riemann tabs grouped after it.

    python3 scripts/explorer_feature_bg.py <built explorer.html> site/telperion-explorer/index.html paper/figdata

Every replacement must match exactly once, so a changed upstream page fails loudly instead of being
patched silently. Always patch a fresh build; the script is not idempotent.
"""
import json
import sys
from pathlib import Path

src, dst, figdata = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
s = src.read_text()


def sub(old, new, count=1):
    global s
    n = s.count(old)
    if n != count:
        raise SystemExit(f"expected {count} occurrence(s), found {n}: {old[:80]!r}")
    s = s.replace(old, new)


def dat(name):
    rows = (figdata / name).read_text().split("\n")[1:]
    return [[float(x) for x in r.split()] for r in rows if r.strip()]


ratio = [[int(n), r] for n, r in dat("ratio_table.dat") + dat("ratio_rule.dat")]
rates = [[int(j), r] for j, r in dat("rates.dat")]
BGDATA = json.dumps({"ratio": ratio, "rates": rates}, separators=(",", ":"))

# ------------------------------------------------------------------ head
sub('<meta name="description" content="A static explorer for the Telperion missions registry: the reverse-Dyson quasicrystal program, the falsification zoo, the wall map, the Li face, and every registered node with its status read from the registry. conjecture1_proved = False.">',
    '<meta name="description" content="A static explorer for the Telperion missions registry, with the Brualdi-Goldwasser theorem in front: which tree maximizes the Laplacian ratio, proved for every n and checked by the Lean kernel. The Riemann-hypothesis campaigns follow; the Riemann Hypothesis is not proved.">')
sub("</style>", """.banner.solved { background: var(--pass); color: var(--pass-ink); border-color: var(--proved); }
.banners { display: flex; flex-wrap: wrap; gap: 8px; }
.banners .banner { margin: 6px 0 12px; }
nav.tabs .group { align-self: center; color: var(--muted); font-size: 0.85rem; margin: 0 2px 0 10px; }
.bgfacts { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 10px; margin: 12px 0; }
.bgfacts div { background: var(--surface); border: 1px solid var(--line); border-radius: 8px; padding: 10px 12px; }
.bgfacts b { display: block; font-family: var(--mono); font-size: 1.05rem; color: var(--ink); }
.bgfacts span { color: var(--muted); font-size: 0.88rem; }
.tablewrap table.plain { min-width: 520px; }
</style>""")

# ------------------------------------------------------------------ header
sub('<div class="banner">conjecture1_proved = False</div>',
    '<div class="banners"><div class="banner solved">Brualdi-Goldwasser: solved for every n, kernel-checked</div>'
    '<div class="banner">Riemann Hypothesis: not proved</div></div>')
sub('<p class="sub">One registry of formal statements about the Riemann zeta function and its zeros, kept in TOML files and checked by a Lean 4 kernel, with the reverse-Dyson quasicrystal program in front. Every status on this page is read from the registry; nothing is inferred, and nothing here is a proof of the Riemann Hypothesis.</p>',
    '<p class="sub">Telperion keeps its research programs as a registry of formal statements: each one written down in Lean, tracked in TOML files, and marked proved only when the Lean kernel has checked a proof of exactly that statement. This page puts the first program to reach its goal in front: the <strong>Brualdi-Goldwasser problem</strong>, which asks which tree maximizes the Laplacian ratio, now answered for every size. Behind it are the three Riemann-hypothesis campaigns, which are open research: they hold many proved steps, and nothing here is a proof of the Riemann Hypothesis.</p>')
sub('<p class="note">The plots are computed live in your browser from bundled data.',
    '<p class="note">New here? Start with the first tab, then the registry. For the Brualdi-Goldwasser theorem on its own, with interactive labs, see the <a href="../">project page</a>. The plots are computed live in your browser from bundled data.')

# ------------------------------------------------------------------ nav
sub('<button class="tab" role="tab" id="tab-qc" aria-selected="true" data-panel="qc">The quasicrystal</button>',
    '<button class="tab" role="tab" id="tab-bg" aria-selected="true" data-panel="bg">Brualdi-Goldwasser</button>\n'
    '  <button class="tab" role="tab" id="tab-reg" aria-selected="false" data-panel="reg">The registry</button>\n'
    '  <span class="group">Riemann campaigns:</span>\n'
    '  <button class="tab" role="tab" id="tab-qc" aria-selected="false" data-panel="qc">The quasicrystal</button>')
sub('  <button class="tab" role="tab" id="tab-reg" aria-selected="false" data-panel="reg">The registry</button>\n  <button class="tab" role="tab" id="tab-known"',
    '  <span class="group"></span>\n  <button class="tab" role="tab" id="tab-known"')
sub('<section class="panel active" id="panel-qc"', '<section class="panel" id="panel-qc"')

# ------------------------------------------------------------------ the BG panel
REPO = "https://github.com/DrMurphyIsIn/brualdi-goldwasser"
SITE = "https://drmurphyisin.github.io/brualdi-goldwasser/"
BG_PANEL = f"""<!-- ================================================================ -->
<section class="panel active" id="panel-bg" role="tabpanel" aria-labelledby="tab-bg">
  <h2>Brualdi-Goldwasser: which tree maximizes the Laplacian ratio?</h2>
  <p>This is the program that shows what Telperion is for. The conceptual argument fits in a paper, but it rests on far more exact inequalities than anyone could check by hand: the sweep of spider shapes alone covers almost five million configurations. Telperion generated certificates for all of them, and the Lean kernel checked every one. The result is a complete answer to a question that had been open since 1984.</p>

  <div class="bgfacts">
    <div><b>every n &ge; 4</b><span>the maximizer is known exactly, for every size</span></div>
    <div><b>621/64 = &rho;<sup>11</sup></b><span>the five-cherry arm: the block that sets the growth rate</span></div>
    <div><b>3 axioms</b><span>propext, Classical.choice, Quot.sound: no sorry, no native_decide</span></div>
    <div><b>316 modules</b><span>every one used by the final theorem</span></div>
  </div>

  <div class="step"><div class="letter">a</div><div class="body">
    <h3>The question</h3>
    <p>Take a tree <code>T</code> on <code>n</code> vertices. Its Laplacian <code>L(T)</code> is the degree matrix minus the adjacency matrix. In 1984 Richard Brualdi and John Goldwasser studied the permanent of this matrix and the <em>Laplacian ratio</em></p>
    <pre>pi(T) = per L(T) / prod over v of deg(v)</pre>
    <p>and asked which tree makes it as large as possible. The ratio has a friendlier description: it is a weighted count of matchings, <code>pi(T) = sum over matchings M of prod over edges uv in M of 1/(deg u deg v)</code>. So the question asks which tree has the heaviest matchings once every edge is discounted by the degrees of its two ends. Stars lose badly: every matching of a star has at most one edge, so its ratio is stuck at 2. Paths lose too, more narrowly: their ratio grows like <code>((1 + sqrt 2)/2)^n &asymp; 1.207^n</code>, while the true maximum grows like <code>1.2295^n</code>. The answer sits in between.</p>
    <p>A conjectured answer by Wu, Dong and Lai was refuted earlier in 2026 by Pant, whose counterexamples were caterpillars of hubs. After that the question was open again.</p>
  </div></div>

  <div class="step"><div class="letter">b</div><div class="body">
    <h3>The answer: spiders of cherry arms</h3>
    <p>A <em>cherry</em> is a pendant path of length two. An <em>arm</em> is a vertex carrying some number of cherries. For every <code>n &ge; 4</code> the maximizer is a <strong>spider of cherry arms</strong>: one centre, with only arms hanging from it, and almost every arm carrying exactly <strong>five</strong> cherries.</p>
    <ul>
      <li>For <code>n &ge; 492</code>, let <code>s = 6(n - 1) mod 11</code>. Every arm carries 5 cherries, except: for <code>s = 1, 2, 3, 4</code>, <code>s</code> arms carry 6 (but for <code>s = 3</code> with <code>n &le; 722</code>, and <code>s = 4</code> with <code>n &le; 2319</code>, it is instead <code>11 - s</code> arms that carry 4); for <code>s = 5, ..., 10</code>, <code>11 - s</code> arms carry 4.</li>
      <li>For <code>4 &le; n &le; 491</code> the maximizer is an explicit table. For small <code>n</code> it may also carry a few cherries or a leaf directly at the centre, and at <code>n = 21</code> two different trees tie.</li>
    </ul>
    <p><strong>Why five?</strong> An arm with <code>j</code> cherries has <code>2j + 1</code> vertices, and each arm contributes a fixed factor to the ratio. The fair way to compare arms of different sizes is the growth rate per vertex. The five-cherry arm is an 11-vertex block contributing exactly <code>621/64 = rho^11</code>, where <code>rho = (621/64)^(1/11) &asymp; 1.2295</code>, and no other arm matches that rate. The chart below draws it (the vertical axis is zoomed in, because the rates are close): move the slider to compare any two arms.</p>
    <div class="plotwrap">
      <div class="controls">
        <label>compare with an arm of j cherries <input type="range" id="bg-j" min="1" max="15" step="1" value="4"> <span class="mono" id="bg-j-val"></span></label>
      </div>
      <canvas id="bg-rate-canvas" width="1000" height="300"></canvas>
      <div class="legend"><span><span class="sw" style="background:var(--proved)"></span>j = 5, the rate log rho = log(621/64)/11</span><span><span class="sw" style="background:var(--cool)"></span>other arm sizes</span><span><span class="sw" style="background:var(--accent)"></span>your comparison</span></div>
      <div class="readout" id="bg-rate-readout"></div>
    </div>
    <p class="note">Try the arms yourself on the project site: the <a href="{SITE}#spiderlab">Spider lab</a> builds any spider and computes its ratio exactly, and the <a href="{SITE}#treelab">Tree lab</a> lets you edit an arbitrary tree.</p>
  </div></div>

  <div class="step"><div class="letter">&#9679;</div><div class="body">
    <h3>Why five: the &lambda;-ladder</h3>
    <p>Give every matched edge an extra weight &lambda;, so that &pi;<sub>&lambda;</sub>(T) = &Sigma;<sub>M</sub> &lambda;<sup>|M|</sup> &prod;<sub>uv&isin;M</sub> 1/(deg u deg v); Brualdi and Goldwasser's ratio is &lambda; = 1. As &lambda; increases, the best building block climbs A<sub>3</sub>, A<sub>4</sub>, A<sub>5</sub>, A<sub>6</sub>, &hellip;, with breakpoints 0.4305, 0.8725, 1.1924, 1.4356, &hellip; increasing to 1 + &radic;5. There the arms run off to infinity and plain cherries take over. The value &lambda; = 1 sits on the A<sub>5</sub> rung.</p>
    <p>One balance condition decides the whole ladder: a long arm's hub vertex must buy more, H(&lambda;) = 2(1+&lambda;)/(2+&lambda;), than the same vertex would earn in a cherry, &zeta;(&lambda;) = &radic;((2+&lambda;)/2). The balance point is a single cubic,</p>
    <pre>8(1+&lambda;)^2 = (2+&lambda;)^3   &lt;=&gt;   (x-2)(x^2-6x+4) = 0,  x = 2+&lambda;,</pre>
    <p>with roots &lambda; = 0, the bottom of the ladder, where the problem becomes the Randi&#263; index, and &lambda; = 1 + &radic;5, the top, where hub factor and cherry rate both equal the golden ratio &phi;. Explore it interactively on the project page: <a href="{SITE}#ladder">Why five: the ladder</a>.</p>
    <p class="note">The ladder among leaves, cherries and arms, and the cubic, are proved. That the best block also sets the growth rate of &pi;<sub>&lambda;</sub> is proved at &lambda; = 1 (the sharp ceiling) and conjectured in general, with supporting computation.</p>
  </div></div>

  <div class="step"><div class="letter">c</div><div class="body">
    <h3>How big the maximum is</h3>
    <p>Because five-cherry arms dominate, the maximum grows like <code>rho^n</code>. The proof pins this down on both sides, <code>(64/621) rho^n &le; max pi &le; 2 rho^(n-1)</code>. The chart shows the exact maximum divided by <code>rho^(n-1)</code>. For large <code>n</code> it settles into eleven separate strands, one for each value of <code>6(n - 1) mod 11</code>, because that is all the rule above depends on. The top strand is exact: for <code>n = 1 (mod 11)</code> and <code>n &ge; 254</code> the maximum is exactly <code>(26/23) rho^(n-1)</code>, and <code>26/23</code> is the limsup of the whole sequence.</p>
    <div class="plotwrap">
      <div class="controls">
        <label>largest n shown <input type="range" id="bg-n" min="40" max="1500" step="10" value="600"> <span class="mono" id="bg-n-val"></span></label>
      </div>
      <canvas id="bg-ratio-canvas" width="1000" height="340"></canvas>
      <div class="legend"><span><span class="sw" style="background:var(--cool)"></span>n &le; 491: from the table</span><span><span class="sw" style="background:var(--proved)"></span>n &ge; 492: from the rule</span><span><span class="sw" style="background:var(--accent)"></span>26/23, the limsup</span></div>
      <div class="readout" id="bg-ratio-readout">Hover the plot to read a value.</div>
    </div>
    <p class="note">Computed in floating point from the proved maximizers (the paper's figure data).</p>
  </div></div>

  <div class="step"><div class="letter">d</div><div class="body">
    <h3>The theorem, as Lean states it</h3>
    <p>The statement uses only Mathlib's definitions on the graph side: <code>SimpleGraph.IsTree</code>, <code>SimpleGraph.lapMatrix</code>, <code>Matrix.permanent</code>, <code>SimpleGraph.degree</code>. The only project definitions it relies on are the short closed form <code>F</code> for a spider's ratio and the list <code>bgChildren n</code> of the maximizer's arms (<a href="{REPO}/blob/main/formalization/Statement.lean">formalization/Statement.lean</a>).</p>
    <pre>theorem brualdi_goldwasser_upper (n : N) (h4 : 4 &le; n) {{V : Type}} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (hV : Fintype.card V = n) :
    (G.lapMatrix R).permanent / (prod v, (G.degree v : R)) &le; (F (bgChildren n) : R)

theorem brualdi_goldwasser_attained (n : N) (h4 : 4 &le; n) :
    exists G : SimpleGraph (Fin n), exists _ : DecidableRel G.Adj, G.IsTree and
      (G.lapMatrix R).permanent / (prod v, (G.degree v : R)) = (F (bgChildren n) : R)</pre>
    <p class="note">Symbols written out in ASCII here (N, R, prod, exists); the file uses the usual Lean notation.</p>
  </div></div>

  <div class="step"><div class="letter">e</div><div class="body">
    <h3>How the proof is split, and where Telperion comes in</h3>
    <p>The proof reduces every tree to a spider, then finds the best spider. The reduction is where most of the computation lives, and it changes character with the size:</p>
    <div class="tablewrap"><table class="plain">
      <tr><th>n</th><th>argument</th></tr>
      <tr><td>4 to 6</td><td>exact rational evaluation of every tree</td></tr>
      <tr><td>7 to 149</td><td>an <em>envelope certificate</em>: a sharded, kernel-checked Bellman bound showing that every tree which is not a spider is strictly beaten</td></tr>
      <tr><td>150 to 491</td><td>refined per-vertex <em>rate cells</em> show the maximizer is a spider; an exhaustive kernel sweep of the spider family finds the best one</td></tr>
      <tr><td>492 and up</td><td>the same reduction to spiders, then exchange arguments and 223 polynomial certificates identify the rule</td></tr>
    </table></div>
    <p>Each certificate family is written by an untrusted Python generator and replayed by the kernel. Telperion's provenance layer freezes every family, so anyone can regenerate it and check that the Lean files come out byte for byte the same.</p>
    <div class="tablewrap"><table class="plain">
      <tr><th>family</th><th>what it certifies</th></tr>
      <tr><td><code>spider_table</code></td><td>the best spider for each 4 &le; n &le; 491 (exhaustive exact search, a 4,977,356-configuration sweep)</td></tr>
      <tr><td><code>envcert_g149</code></td><td>the envelope certificate: every non-spider rooting with root degree &le; 23 loses, 7 &le; n &le; 149</td></tr>
      <tr><td><code>mid_cells</code></td><td>credited rate cells and root knapsack checks, 150 &le; n &le; 491</td></tr>
      <tr><td><code>cand_certs</code></td><td>223 polynomial certificates: the rule spider beats every candidate, n &ge; 492</td></tr>
    </table></div>
    <p>The kernel is the only trusted component. A wrong certificate does not produce a wrong theorem; it produces a failed build.</p>
  </div></div>

  <div class="step"><div class="letter">f</div><div class="body">
    <h3>How it has been checked</h3>
    <div class="claim">
      <p><strong>Checked.</strong> The full formalization builds from scratch on Lean 4 v4.32.0 with Mathlib, and continuous integration rebuilds it on every push to the main branch. An axiom guard confirms that every headline theorem depends only on <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. A separate job regenerates every certificate family and compares it byte for byte with the committed Lean. And a <a href="{REPO}/tree/main/formalization/comparator">Comparator check</a> passed on 27 September 2026: a second, independent kernel (nanoda) and Lean's own kernel both accepted the proof against a statement that imports nothing but the definitions of <code>F</code> and <code>bgChildren</code> (run on macOS, without Comparator's Linux sandbox).</p>
      <p><strong>Still to come.</strong> The paper has not been refereed, and expert review of the statement is welcome.</p>
    </div>
    <p class="note">About the registry tab: Telperion's registry records the Brualdi-Goldwasser campaign as it stood on 2026-09-24, before the final theorem was assembled on 2026-09-26. Its nodes show the path taken, including a refuted capstone and superseded formulations, and its goal node is still a draft there. The theorem above lives in the public repository and is checked there; it has not yet been registered as a node.</p>
    <p>Everything you need is public: the <a href="{REPO}">repository</a>, the <a href="{REPO}/blob/main/formalization/READING_GUIDE.md">reading guide</a> for reviewers, the <a href="{REPO}/blob/main/paper/paper.pdf">paper</a>, and the <a href="{SITE}">project page</a> with interactive labs. Archived as <a href="https://doi.org/10.5281/zenodo.22983412">doi:10.5281/zenodo.22983412</a>.</p>
  </div></div>
</section>

"""
sub('<!-- ================================================================ -->\n<section class="panel" id="panel-qc"',
    BG_PANEL + '<!-- ================================================================ -->\n<section class="panel" id="panel-qc"')

# ------------------------------------------------------------------ registry / known / compute text
sub('<p>Four campaigns, one schema.', '<p>Four campaigns, one schema: <code>bg</code> (Brualdi-Goldwasser, shown first) and the three Riemann campaigns <code>mirrormere</code>, <code>rh</code> and <code>anduril</code>.')
sub('<li><strong>The Brualdi-Goldwasser campaign.</strong> Nine proved lemmas and one refuted capstone; the conjecture itself is a draft goal.</li>', '')
sub('<h2>What is known</h2>\n  <ul>',
    '<h2>What is known</h2>\n  <ul>\n    <li><strong>The Brualdi-Goldwasser problem, solved.</strong> For every <code>n &ge; 4</code> the tree maximizing <code>per L(T) / prod deg(v)</code> is the explicit spider of cherry arms described in the first tab, and the maximum grows like <code>rho^n</code> with <code>rho^11 = 621/64</code>. Kernel-checked in the public repository, three standard axioms only. The registry\'s <code>bg</code> campaign predates this theorem (see the note in the first tab).</li>\n    <li><strong>The Riemann campaigns</strong>, in the items below.</li>')
sub('<li>The Riemann Hypothesis. <code>conjecture1_proved = False</code> in every campaign manifest and in this page.</li>',
    '<li>The Riemann Hypothesis. <code>conjecture1_proved = False</code> in every Riemann campaign manifest and in this page.</li>')
sub('<li>The goal node of every campaign: <code>MM_zeta_comb_membership</code>, <code>RH_conjecture</code>, <code>AND_ladder_1e13</code>, <code>BG_conjecture1</code>. All four are drafts.</li>',
    '<li>The goal node of every Riemann campaign: <code>MM_zeta_comb_membership</code>, <code>RH_conjecture</code>, <code>AND_ladder_1e13</code>. All three are drafts. (The <code>bg</code> campaign\'s registered goal, <code>BG_backbone_conjecture</code>, is also still a draft in this registry snapshot; the Brualdi-Goldwasser answer itself is proved in the public repository.)</li>')
sub('<p>Everything on this page can be regenerated from the repository, and the claims behind it can be re-checked at three levels: the registry gate, the Lean kernel, and an independent second kernel.</p>',
    f'''<p>Everything on this page can be regenerated, and the claims behind it can be re-checked at three levels: the registry gate, the Lean kernel, and an independent second kernel.</p>

  <h3>The Brualdi-Goldwasser theorem</h3>
  <p>This part is fully public. The build needs a machine with about 96 GB of memory for its largest certificate files; <a href="{REPO}#getting-started">Getting started</a> has the details.</p>
  <pre>git clone {REPO}.git
cd brualdi-goldwasser/formalization
./build.sh                         # builds every module, heavy files one at a time
lake env lean Statement.lean       # the Mathlib-vocabulary statement; prints its axioms
cd .. &amp;&amp; certificates/verify.sh    # regenerate every certificate family, byte for byte</pre>

  <h3>The Riemann campaigns</h3>
  <p class="note">The commands below run in the Telperion development repository, which is private; they are listed so that the page's claims can be traced.</p>''')

# ------------------------------------------------------------------ JS: default tab, default campaign, BG drawers
sub('if (!panels[name]) name = "qc";', 'if (!panels[name]) name = "bg";')
sub('selectTab(location.hash.replace("#", "") || "qc", false);', 'selectTab(location.hash.replace("#", "") || "bg", false);')
sub('gsel.value = "mirrormere";', 'gsel.value = "bg";')
sub('csel.value = "mirrormere";', 'csel.value = "bg";')

BG_JS = """
  // ================================================================== BRUALDI-GOLDWASSER
  (function bgTab() {
    var D = BGDATA, LOGRHO = Math.log(621 / 64) / 11;
    var jIn = document.getElementById("bg-j"), jVal = document.getElementById("bg-j-val");
    var nIn = document.getElementById("bg-n"), nVal = document.getElementById("bg-n-val");
    function drawRates() {
      var cv = setupCanvas("bg-rate-canvas"), jc = +jIn.value;
      jVal.textContent = jc + " (" + (2 * jc + 1) + " vertices)";
      var lo = 0.2035, hi = 0.2072;
      var A = axes(cv, 0.4, D.rates.length + 0.6, lo, hi, { xticks: D.rates.map(function (r) { return r[0]; }), yfmt: function (v) { return v.toFixed(4); }, xlabel: "cherries per arm, j", ylabel: "rate per vertex" });
      var ctx = cv.ctx, bw = (A.X(2) - A.X(1)) * 0.6;
      D.rates.forEach(function (r) {
        ctx.fillStyle = r[0] === 5 ? cssVar("--proved") : r[0] === jc ? cssVar("--accent") : cssVar("--cool");
        var top = Math.max(r[1], lo);
        ctx.fillRect(A.X(r[0]) - bw / 2, A.Y(top), bw, A.Y(lo) - A.Y(top));
        if (r[1] < lo) { ctx.fillStyle = cssVar("--muted"); ctx.textAlign = "center"; ctx.textBaseline = "bottom"; ctx.fillText(r[1].toFixed(3) + " (below)", A.X(r[0]), A.Y(lo) - 3); }
      });
      ctx.setLineDash([4, 4]); polyline(ctx, [[A.X(0.4), A.Y(LOGRHO)], [A.X(D.rates.length + 0.6), A.Y(LOGRHO)]], cssVar("--proved"), 1); ctx.setLineDash([]);
      var r5 = D.rates[4][1], rj = D.rates[jc - 1][1];
      document.getElementById("bg-rate-readout").textContent = jc === 5
        ? "j = 5 is the best arm: rate " + r5.toFixed(6) + " per vertex = log(621/64)/11."
        : "j = " + jc + ": rate " + rj.toFixed(6) + " per vertex, versus " + r5.toFixed(6) + " for five cherries. Over 11 vertices that is a factor " + Math.exp(11 * (r5 - rj)).toFixed(4) + " in favour of the five-cherry arm.";
    }
    function drawRatio() {
      var cv = setupCanvas("bg-ratio-canvas"), nmax = +nIn.value;
      nVal.textContent = nmax;
      var pts = D.ratio.filter(function (r) { return r[0] <= nmax; });
      var ymin = 1.1, ymax = 1.36;
      if (nmax > 200) { ymin = 1.115; ymax = 1.16; }
      var A = axes(cv, 4, nmax, ymin, ymax, { xlabel: "n", ylabel: "max pi / rho^(n-1)", yfmt: function (v) { return v.toFixed(3); } });
      var ctx = cv.ctx;
      ctx.setLineDash([4, 4]); polyline(ctx, [[A.X(4), A.Y(26 / 23)], [A.X(nmax), A.Y(26 / 23)]], cssVar("--accent"), 1); ctx.setLineDash([]);
      ctx.save(); ctx.beginPath(); ctx.rect(A.ml, A.mt, cv.W - A.ml - A.mr, cv.H - A.mt - A.mb); ctx.clip();
      var rad = nmax > 800 ? 1.2 : 1.8;
      pts.forEach(function (r) {
        ctx.fillStyle = r[0] >= 492 ? cssVar("--proved") : cssVar("--cool");
        ctx.beginPath(); ctx.arc(A.X(r[0]), A.Y(r[1]), rad, 0, 2 * Math.PI); ctx.fill();
      });
      ctx.restore();
      var c = document.getElementById("bg-ratio-canvas");
      c.onmousemove = function (ev) {
        var rect = c.getBoundingClientRect(), x = ev.clientX - rect.left;
        var n = Math.round(4 + (x - A.ml) / (cv.W - A.ml - A.mr) * (nmax - 4));
        var row = D.ratio.filter(function (r) { return r[0] === n; })[0];
        if (row) document.getElementById("bg-ratio-readout").textContent = "n = " + n + ": max pi / rho^(n-1) = " + row[1].toFixed(6) + (n >= 492 ? "   (rule, s = 6(n-1) mod 11 = " + ((6 * (n - 1)) % 11) + ")" : "   (table)");
      };
    }
    jIn.addEventListener("input", drawRates); nIn.addEventListener("input", drawRatio);
    drawers.bg = function () { drawRates(); drawRatio(); };
  })();
"""
sub("  // ================================================================== REGISTRY", BG_JS + "\n  // ================================================================== REGISTRY")
sub('  var ZEROS = PLOTS.zeros.ordinates;', '  var BGDATA = JSON.parse(document.getElementById("bg-data").textContent);\n  var ZEROS = PLOTS.zeros.ordinates;')
sub('<script id="plot-data" type="application/json">', f'<script id="bg-data" type="application/json">{BGDATA}</script>\n<script id="plot-data" type="application/json">')

# ------------------------------------------------------------------ footer
sub('<p><strong>Telperion Registry Explorer.</strong>',
    '<p><strong>Telperion Registry Explorer.</strong> Companion to the <a href="../">Brualdi-Goldwasser project page</a>. The Brualdi-Goldwasser tab is drawn from the public repository (its statement, certificate manifest and paper figure data).')

dst.write_text(s)
print("wrote", dst, len(s), "bytes")
