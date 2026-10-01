// Interactive labs: Tree lab (matchings, cavity recursion, profit/subaction), Spider lab, Races.
// Everything that is claimed exactly is computed with BigInt fractions.
(function () {
  "use strict";
  var BG = window.BG;
  var NS = "http://www.w3.org/2000/svg";
  var FS = Math.log(621 / 64) / 11;

  // ---------------------------------------------------------------- exact rationals
  function gcd(a, b) { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) { var t = a % b; a = b; b = t; } return a; }
  function Q(n, d) {
    n = BigInt(n); d = d === undefined ? 1n : BigInt(d);
    if (d < 0n) { n = -n; d = -d; }
    var g = gcd(n, d) || 1n;
    return { n: n / g, d: d / g };
  }
  function add(a, b) { return Q(a.n * b.d + b.n * a.d, a.d * b.d); }
  function mul(a, b) { return Q(a.n * b.n, a.d * b.d); }
  function div(a, b) { return Q(a.n * b.d, a.d * b.n); }
  function cmp(a, b) { var x = a.n * b.d - b.n * a.d; return x > 0n ? 1 : x < 0n ? -1 : 0; }
  function qpow(a, k) { var r = Q(1); for (var i = 0; i < k; i++) r = mul(r, a); return r; }
  function num(a) {   // float value, safe for huge numerators/denominators
    var ln = a.n.toString().replace("-", "").length, ld = a.d.toString().length;
    var sn = ln > 17 ? ln - 17 : 0, sd = ld > 17 ? ld - 17 : 0;
    var v = Number(a.n / 10n ** BigInt(sn)) / Number(a.d / 10n ** BigInt(sd));
    return v * Math.pow(10, sn - sd);
  }
  function logq(a) {
    var ln = a.n.toString().length, ld = a.d.toString().length;
    var sn = ln > 17 ? ln - 17 : 0, sd = ld > 17 ? ld - 17 : 0;
    return Math.log(Number(a.n / 10n ** BigInt(sn))) - Math.log(Number(a.d / 10n ** BigInt(sd))) + (sn - sd) * Math.LN10;
  }
  function qs(a) { return a.d === 1n ? a.n.toString() : a.n.toString() + "/" + a.d.toString(); }
  function qshort(a) { var s = qs(a); return s.length <= 11 ? s : num(a).toPrecision(6); }

  function el(name, attrs, parent, text) {
    var e = document.createElementNS(NS, name);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (text !== undefined) e.textContent = text;
    if (parent) parent.appendChild(e);
    return e;
  }
  function clear(svg) { while (svg.firstChild) svg.removeChild(svg.firstChild); }

  // ================================================================= TREE LAB
  // The tree is an undirected adjacency list; the root is a chosen vertex.
  var T = { adj: [], root: 0, sel: 0, mode: "match", mIdx: 0, timer: null };

  function fromParents(par) {
    var adj = par.map(function () { return []; });
    par.forEach(function (p, i) { if (p >= 0) { adj[i].push(p); adj[p].push(i); } });
    return adj;
  }
  // builders ---------------------------------------------------------------
  function B() { this.par = [-1]; }
  B.prototype.add = function (p) { this.par.push(p); return this.par.length - 1; };
  B.prototype.cherry = function (p) { var m = this.add(p); this.add(m); };
  B.prototype.arm = function (p, j) { var a = this.add(p); for (var i = 0; i < j; i++) this.cherry(a); return a; };

  function spiderFromComp(cp) {
    var b = new B();
    for (var i = 0; i < cp.c; i++) b.cherry(0);
    Object.keys(cp.arms).forEach(function (j) { for (var i = 0; i < cp.arms[j]; i++) b.arm(0, +j); });
    return b.par;
  }
  function preset(name) {
    var b = new B();
    if (name === "fig3") { b.cherry(0); b.cherry(0); b.add(0); }
    else if (name === "a5") { b.arm(0, 5); }
    else if (name === "path") { var p = 0; for (var i = 0; i < 6; i++) p = b.add(p); }
    else if (name === "star") { for (var i2 = 0; i2 < 6; i2++) b.add(0); }
    else if (name === "pant") { var x1 = 0, x2 = b.add(x1), x3 = b.add(x2); [x1, x2, x3].forEach(function (x) { b.cherry(x); b.cherry(x); }); }
    else if (name === "max21") { return spiderFromComp(BG.comp(21)); }
    else if (name === "max34") { return spiderFromComp(BG.comp(34)); }
    else { for (var k = 1; k < 10; k++) b.add(Math.floor(Math.random() * k)); }
    return b.par;
  }
  function load(name) {
    T.adj = fromParents(preset(name)); T.root = 0; T.sel = 0; T.mIdx = 0; stopPlay(); renderTree();
  }

  // rooted structure ---------------------------------------------------------
  function rooted() {
    var n = T.adj.length, par = new Array(n).fill(-1), ch = T.adj.map(function () { return []; }), order = [], seen = new Array(n).fill(false);
    var stack = [T.root]; seen[T.root] = true;
    while (stack.length) {
      var v = stack.pop(); order.push(v);
      T.adj[v].forEach(function (w) { if (!seen[w]) { seen[w] = true; par[w] = v; ch[v].push(w); stack.push(w); } });
    }
    return { par: par, ch: ch, order: order };
  }
  function layout(rt) {
    var pos = {}, next = 0, maxd = 0;
    (function place(v, d) {
      maxd = Math.max(maxd, d);
      if (!rt.ch[v].length) { pos[v] = { x: next++, y: d }; return; }
      rt.ch[v].forEach(function (c) { place(c, d + 1); });
      var xs = rt.ch[v].map(function (c) { return pos[c].x; });
      pos[v] = { x: (Math.min.apply(null, xs) + Math.max.apply(null, xs)) / 2, y: d };
    })(T.root, 0);
    return { pos: pos, w: Math.max(1, next - 1), h: maxd };
  }

  // cavity recursion, exact ---------------------------------------------------
  function cavity(rt) {
    var n = T.adj.length, Tq = new Array(n), yq = new Array(n), Rq = new Array(n), dd = new Array(n);
    for (var i = rt.order.length - 1; i >= 0; i--) {
      var v = rt.order[i], C = rt.ch[v];
      var R = Q(0), P = Q(1);
      C.forEach(function (c) { R = add(R, yq[c]); P = mul(P, Tq[c]); });
      Rq[v] = R;
      if (v === T.root) {
        dd[v] = C.length;
        Tq[v] = C.length ? mul(P, add(Q(1), div(R, Q(C.length)))) : Q(1);   // pi
      } else {
        var d = C.length + 1; dd[v] = d;
        Tq[v] = mul(P, div(add(Q(d), R), Q(d)));
        yq[v] = div(Q(1), add(Q(d), R));
      }
    }
    return { T: Tq, y: yq, R: Rq, d: dd, pi: Tq[T.root] };
  }

  // matchings ------------------------------------------------------------------
  function edges() { var E = []; T.adj.forEach(function (nb, v) { nb.forEach(function (w) { if (v < w) E.push([v, w]); }); }); return E; }
  function matchings(limit) {
    var E = edges(), out = [], used = new Array(T.adj.length).fill(false), cur = [];
    (function rec(i) {
      if (out.length >= limit) return;
      if (i === E.length) { out.push(cur.slice()); return; }
      rec(i + 1);
      var e = E[i];
      if (!used[e[0]] && !used[e[1]]) { used[e[0]] = used[e[1]] = true; cur.push(e); rec(i + 1); cur.pop(); used[e[0]] = used[e[1]] = false; }
    })(0);
    return out;
  }
  function mweight(M) {
    var w = Q(1);
    M.forEach(function (e) { w = mul(w, Q(1, T.adj[e[0]].length * T.adj[e[1]].length)); });
    return w;
  }
  function permanentLaplacian() {   // Ryser, exact
    var n = T.adj.length, Lm = [];
    for (var i = 0; i < n; i++) { Lm.push(new Array(n).fill(0n)); Lm[i][i] = BigInt(T.adj[i].length); T.adj[i].forEach(function (j) { Lm[i][j] = -1n; }); }
    var total = 0n;
    for (var S = 1; S < (1 << n); S++) {
      var prod = 1n, bits = 0;
      for (var r = 0; r < n; r++) {
        var s = 0n;
        for (var c = 0; c < n; c++) if (S & (1 << c)) s += Lm[r][c];
        prod *= s; if (prod === 0n) break;
      }
      for (var b = S; b; b &= b - 1) bits++;
      total += ((n - bits) % 2 ? -1n : 1n) * prod;
    }
    return total;
  }

  // drawing ---------------------------------------------------------------
  function renderTree() {
    var svg = document.getElementById("tlSvg"); clear(svg);
    var rt = rooted(), L = layout(rt), n = T.adj.length;
    var W = 600, sx = Math.min(70, (W - 60) / L.w), sy = 70;
    var X = function (v) { return 30 + L.pos[v].x * sx; }, Y = function (v) { return 30 + L.pos[v].y * sy; };
    var cav = cavity(rt), hl = {}, M = null, list = null;
    if (T.mode === "match") {
      list = matchings(5000);
      T.mIdx = Math.min(T.mIdx, list.length - 1);
      M = list[T.mIdx];
      M.forEach(function (e) { hl[e[0] + "-" + e[1]] = true; });
    }
    var prof = T.mode === "profit" ? profit(rt, cav) : null;
    var g = el("g", {}, svg);
    edges().forEach(function (e) {
      var on = hl[e[0] + "-" + e[1]];
      el("line", { x1: X(e[0]), y1: Y(e[0]), x2: X(e[1]), y2: Y(e[1]), stroke: on ? "var(--accent)" : "var(--faint)", "stroke-width": on ? 5 : 1.4, "stroke-linecap": "round", opacity: on ? 0.8 : 1 }, g);
    });
    for (var v = 0; v < n; v++) (function (v) {
      var fill = "var(--ink)";
      if (prof && v !== T.root) fill = prof.slack[v] < 1e-9 ? "var(--accent)" : "var(--cool)";
      var c = el("circle", { cx: X(v), cy: Y(v), r: v === T.root ? 8 : 6, fill: v === T.root ? "var(--surface)" : fill, stroke: v === T.sel ? "var(--a6)" : "var(--ink)", "stroke-width": v === T.sel ? 3 : 1.4, style: "cursor:pointer" }, g);
      c.addEventListener("click", function () { T.sel = v; renderTree(); });
      var lab = "";
      if (T.mode === "match") lab = "deg " + T.adj[v].length;
      else if (T.mode === "cavity") lab = v === T.root ? "" : "T=" + qshort(cav.T[v]) + "  y=" + qshort(cav.y[v]);
      else if (v !== T.root) lab = "slack " + prof.slack[v].toFixed(4);
      if (lab) el("text", { x: X(v) + 10, y: Y(v) + 4, "font-size": 11, fill: "var(--muted)" }, g, lab);
    })(v);
    var bb = g.getBBox();
    svg.setAttribute("viewBox", (bb.x - 12) + " " + (bb.y - 12) + " " + (bb.width + 24) + " " + (bb.height + 24));
    svg.style.maxHeight = Math.min(420, 80 + L.h * 70) + "px";
    document.getElementById("tlMatchCtl").style.display = T.mode === "match" ? "" : "none";
    readout(rt, cav, M, list, prof);
  }

  function profit(rt, cav) {
    var n = T.adj.length, e = new Array(n), r = new Array(n), slack = new Array(n), ell = new Array(n).fill(0), size = new Array(n).fill(1);
    for (var i = rt.order.length - 1; i >= 0; i--) {
      var v = rt.order[i]; if (v === T.root) continue;
      var C = rt.ch[v], y = num(cav.y[v]), d = cav.d[v], R = num(cav.R[v]);
      e[v] = Math.log(1 + R / d) - FS;
      var k = C.length;
      r[v] = k === 0 ? FS : k === 1 ? 2 * FS - Math.log(1.5) + (y - 1 / 3) / 4 : k === 2 ? y / 32 : k === 3 ? y / 384 : 0;
      slack[v] = C.reduce(function (s, c) { return s + r[c]; }, 0) - e[v] - r[v];
      ell[v] = e[v] + C.reduce(function (s, c) { return s + ell[c]; }, 0);
      size[v] = 1 + C.reduce(function (s, c) { return s + size[c]; }, 0);
    }
    return { e: e, r: r, slack: slack, ell: ell, size: size };
  }

  function readout(rt, cav, M, list, prof) {
    var out = document.getElementById("tlReadout"), ex = document.getElementById("tlExplain"), n = T.adj.length;
    var degs = T.adj.map(function (a) { return a.length; });
    if (T.mode === "match") {
      var run = Q(0); for (var i = 0; i <= T.mIdx; i++) run = add(run, mweight(list[i]));
      var capped = list.length >= 5000;
      document.getElementById("tlMatchPos").textContent = "matching " + (T.mIdx + 1) + " of " + (capped ? "5000+" : list.length);
      var s = "n = " + n + " &nbsp; this matching has " + M.length + " edge" + (M.length === 1 ? "" : "s") +
        ", weight " + qs(mweight(M)) + " &nbsp; running total " + qs(run) + "<br>&pi; = sum over all matchings = <b>" + qs(cav.pi) + "</b> = " + num(cav.pi).toFixed(6);
      if (n <= 12) {
        var per = permanentLaplacian(), pd = degs.reduce(function (a, b) { return a * BigInt(b); }, 1n);
        var ok = cmp(Q(per, pd), cav.pi) === 0;
        s += "<br>per L = " + per + ", &prod; deg = " + pd + ", per L / &prod; deg = " + qs(Q(per, pd)) + (ok ? " &nbsp;&#10003; the same number" : " &nbsp;MISMATCH");
      } else s += "<br>(the permanent itself is computed for trees with at most 12 vertices)";
      out.innerHTML = s;
      ex.innerHTML = "Each matched edge uv contributes 1/(deg u &middot; deg v); the empty matching contributes 1. " +
        "The sum of all these weights is exactly the permanent of the Laplacian divided by the product of degrees: " +
        "for a tree, every nonzero term of the permanent is a matching (Theorem 4 of the paper).";
    } else if (T.mode === "cavity") {
      var k = rt.ch[T.root].length, R = cav.R[T.root];
      out.innerHTML = "root has k = " + k + " children, R = &Sigma; y = " + qs(R) + "<br>&pi; = &prod; T<sub>c</sub> &middot; (1 + R/k) = <b>" + qs(cav.pi) + "</b> = " + num(cav.pi).toFixed(6) +
        "<br>Try <i>make root</i> on any vertex: every label changes, &pi; does not.";
      ex.innerHTML = "Each vertex summarizes the subtree below it by a weight T and a message y = 1/(d + R), where d is its degree and R the sum of its children's messages; " +
        "then T = &prod; T<sub>c</sub> &middot; (d + R)/d. One pass from the leaves up computes &pi; exactly, in linear time. " +
        "A cherry has T = 3/2, y = 1/3; an arm with five cherries has T = 621/64.";
    } else {
      var C = rt.ch[T.root], k2 = C.length, S = 0, parts = [];
      C.forEach(function (c) { S += num(cav.y[c]); parts.push((Math.abs(prof.ell[c]) < 5e-6 ? 0 : prof.ell[c]).toFixed(5)); });
      var lhs = Math.log(num(cav.pi)) - (n - 1) * FS, bonus = k2 ? Math.log(1 + S / k2) : 0;
      var tight = 0, total = 0; for (var v = 0; v < n; v++) if (v !== T.root) { total++; if (prof.slack[v] < 1e-9) tight++; }
      out.innerHTML = "log &pi; &minus; (n&minus;1) log &rho; = " + lhs.toFixed(5) + " &nbsp;=&nbsp; &Sigma; &#8467;(branch) [" + parts.join(", ") + "] + root bonus " + bonus.toFixed(5) +
        "<br>tight vertices (slack 0): " + tight + " of " + total + (tight === total && total ? " &nbsp; every inequality is tight" : "") +
        "<br>smallest slack: " + Math.min.apply(null, prof.slack.filter(function (x) { return x !== undefined; })).toFixed(6) + " (never negative)";
      ex.innerHTML = "Each vertex v below the root has a local profit e<sub>v</sub> = log(1 + R/d) &minus; log &rho; and a credit &rho;(v) that depends only on its number of children and its message. " +
        "The subaction inequality e<sub>v</sub> + &rho;(v) &le; &Sigma; &rho;(children) holds at every vertex; its slack is shown. Summed over a branch, the credits cancel and the branch's profit &#8467; is at most 0. " +
        "<span style='color:var(--accent)'>Red</span> vertices are tight. Load <i>a five-cherry arm</i>: every vertex is tight, and the branch has profit exactly 0, which is why A<sub>5</sub> sets the growth rate.";
    }
  }

  function stopPlay() { if (T.timer) { clearInterval(T.timer); T.timer = null; document.getElementById("tlPlay").textContent = "play"; } }

  function initTreeLab() {
    document.getElementById("tlPreset").addEventListener("change", function (e) { load(e.target.value); });
    document.getElementById("tlAdd").addEventListener("click", function () {
      if (T.adj.length >= 40) return;
      var w = T.adj.length; T.adj.push([T.sel]); T.adj[T.sel].push(w); T.mIdx = 0; renderTree();
    });
    document.getElementById("tlDel").addEventListener("click", function () {
      if (T.sel === T.root) return;
      var rt = rooted(), kill = {};
      (function mark(v) { kill[v] = true; rt.ch[v].forEach(mark); })(T.sel);
      var map = {}, keep = [];
      T.adj.forEach(function (_, v) { if (!kill[v]) { map[v] = keep.length; keep.push(v); } });
      T.adj = keep.map(function (v) { return T.adj[v].filter(function (w) { return !kill[w]; }).map(function (w) { return map[w]; }); });
      T.root = map[T.root]; T.sel = T.root; T.mIdx = 0; renderTree();
    });
    document.getElementById("tlRoot").addEventListener("click", function () { T.root = T.sel; renderTree(); });
    document.getElementById("tlPrev").addEventListener("click", function () { stopPlay(); T.mIdx = Math.max(0, T.mIdx - 1); renderTree(); });
    document.getElementById("tlNext").addEventListener("click", function () { stopPlay(); T.mIdx++; renderTree(); });
    document.getElementById("tlPlay").addEventListener("click", function (e) {
      if (T.timer) { stopPlay(); return; }
      e.target.textContent = "pause";
      T.timer = setInterval(function () { var L = matchings(5000).length; T.mIdx = (T.mIdx + 1) % L; renderTree(); }, 700);
    });
    document.querySelectorAll(".subtab").forEach(function (b) {
      b.addEventListener("click", function () {
        stopPlay(); T.mode = b.dataset.m;
        document.querySelectorAll(".subtab").forEach(function (x) { x.setAttribute("aria-selected", x === b ? "true" : "false"); });
        renderTree();
      });
    });
    load("fig3");
  }

  // ================================================================= SPIDER LAB
  var S = { c: 0, arms: {}, hist: [] };
  var MAXJ = 10;
  function gArm(j) { return mul(qpow(Q(3, 2), j), Q(4 * j + 3, 3 * (j + 1))); }
  function yArm(j) { return Q(3, 4 * j + 3); }
  function nOf(st) { var n = 1 + 2 * st.c; for (var j in st.arms) n += st.arms[j] * (2 * j + 1); return n; }
  function Dof(st) { var d = st.c; for (var j in st.arms) d += st.arms[j]; return d; }
  function Fexact(st) {
    var G = qpow(Q(3, 2), st.c), R = mul(Q(st.c), Q(1, 3)), D = Dof(st);
    if (!D) return Q(1);
    for (var j in st.arms) { var m = st.arms[j]; if (!m) continue; G = mul(G, qpow(gArm(+j), m)); R = add(R, mul(Q(m), yArm(+j))); }
    return mul(G, add(Q(1), div(R, Q(D))));
  }
  function optComp(n) { var cp = BG.comp(n); var arms = {}; for (var j in cp.arms) arms[j] = cp.arms[j]; return { c: cp.c, arms: arms }; }
  function armList(st) { var L = []; Object.keys(st.arms).forEach(function (j) { for (var i = 0; i < st.arms[j]; i++) L.push(+j); }); return L.sort(function (a, b) { return b - a; }); }
  function setArms(st, L) { st.arms = {}; L.forEach(function (j) { st.arms[j] = (st.arms[j] || 0) + 1; }); }

  function slRender(note) {
    var n = nOf(S), D = Dof(S), box = document.getElementById("slCounts"), html = [];
    html.push(row("cherries at the centre", "c", S.c));
    for (var j = 0; j <= MAXJ; j++) html.push(row(j === 0 ? "leaves (A<sub>0</sub>)" : "arms A<sub>" + j + "</sub> (" + (2 * j + 1) + " vertices)", j, S.arms[j] || 0));
    box.innerHTML = html.join("");
    box.querySelectorAll("button[data-k]").forEach(function (b) {
      b.addEventListener("click", function () {
        var k = b.dataset.k, d = +b.dataset.d;
        if (k === "c") S.c = Math.max(0, S.c + d); else S.arms[k] = Math.max(0, (S.arms[k] || 0) + d);
        if (nOf(S) > 1500) { if (k === "c") S.c -= d; else S.arms[k] -= d; }
        S.hist = []; slRender();
      });
    });
    // readout
    var F = Fexact(S), out = document.getElementById("slReadout");
    var s = "n = " + n + " vertices, centre degree D = " + D + "<br>F = " + (qs(F).length < 60 ? qs(F) : num(F).toPrecision(10)) + " &nbsp; F / &rho;<sup>n&minus;1</sup> = " + Math.exp(logq(F) - (n - 1) * FS).toFixed(6);
    if (n >= 4) {
      var opt = optComp(n), Fo = Fexact(opt), c = cmp(F, Fo), rel = Math.expm1(logq(F) - logq(Fo));
      s += "<br>the maximizer for n = " + n + " has F / &rho;<sup>n&minus;1</sup> = " + Math.exp(logq(Fo) - (n - 1) * FS).toFixed(6) +
        (c === 0 ? " &nbsp; <b>this spider is optimal</b>" : " &nbsp; this spider is " + (-rel).toExponential(2) + " below it (relative)");
      S.hist.push(rel);
      if (S.hist.length > 60) S.hist.shift();
    }
    if (note) s += "<br>" + note;
    out.innerHTML = s;
    drawSpider(); drawHist();
    function row(label, k, v) {
      return "<div class='cnt'><span>" + label + "</span><span><button class='btn sm' data-k='" + k + "' data-d='-1'>&minus;</button> <b class='mono'>" + v +
        "</b> <button class='btn sm' data-k='" + k + "' data-d='1'>+</button></span></div>";
    }
  }
  function drawSpider() {
    var svg = document.getElementById("slSvg"); clear(svg);
    var kids = armList(S); for (var i = 0; i < S.c; i++) kids.push(-1);
    var D = kids.length; if (!D) return;
    var g = el("g", {}, svg), R1 = 120, dot = Math.max(1.4, Math.min(4, 40 / Math.sqrt(nOf(S))));
    kids.forEach(function (j, idx) {
      var th = 2 * Math.PI * idx / D - Math.PI / 2, ax = R1 * Math.cos(th), ay = R1 * Math.sin(th);
      var col = j < 0 ? "var(--other)" : j === 5 ? "var(--a5)" : j === 4 ? "var(--a4)" : j === 6 ? "var(--a6)" : "var(--other)";
      el("line", { x1: 0, y1: 0, x2: ax, y2: ay, stroke: "var(--faint)", "stroke-width": 0.8 }, g);
      if (j < 0) {   // a cherry at the centre: middle vertex (drawn below as the "arm" dot) and its leaf
        el("line", { x1: ax, y1: ay, x2: 1.5 * ax, y2: 1.5 * ay, stroke: "var(--faint)" }, g);
        el("circle", { cx: 1.5 * ax, cy: 1.5 * ay, r: dot, fill: col }, g);
      }
      else {
        var sp = Math.min(2 * Math.PI / D, 1.0), L1 = Math.min(45, 700 / D + 10);
        for (var k = 0; k < j; k++) {
          var t = th + (j === 1 ? 0 : sp * (k / (j - 1) - 0.5) * 0.9);
          el("line", { x1: ax, y1: ay, x2: ax + 1.9 * L1 * Math.cos(t), y2: ay + 1.9 * L1 * Math.sin(t), stroke: "var(--faint)", "stroke-width": 0.6 }, g);
          el("circle", { cx: ax + L1 * Math.cos(t), cy: ay + L1 * Math.sin(t), r: dot * 0.8, fill: col }, g);
          el("circle", { cx: ax + 1.9 * L1 * Math.cos(t), cy: ay + 1.9 * L1 * Math.sin(t), r: dot * 0.8, fill: col }, g);
        }
      }
      el("circle", { cx: ax, cy: ay, r: dot * 1.2, fill: col }, g);
    });
    el("circle", { cx: 0, cy: 0, r: 6, fill: "var(--surface)", stroke: "var(--ink)", "stroke-width": 1.5 }, g);
    var bb = g.getBBox();
    svg.setAttribute("viewBox", (bb.x - 10) + " " + (bb.y - 10) + " " + (bb.width + 20) + " " + (bb.height + 20));
  }
  function drawHist() {
    var svg = document.getElementById("slHist"); clear(svg);
    var H = S.hist; if (!H.length) return;
    var lo = Math.min.apply(null, H.concat([0])), W = 600, h = 120;
    var X = function (i) { return 30 + i * (W - 50) / Math.max(1, 59); };
    var Y = function (v) { return 10 + (lo === 0 ? 0 : (v / lo)) * (h - 20); };
    el("line", { x1: 30, x2: W - 10, y1: Y(0), y2: Y(0), stroke: "var(--line)" }, svg);
    el("text", { x: 26, y: Y(0) + 4, "text-anchor": "end", "font-size": 10, fill: "var(--muted)" }, svg, "opt");
    var d = H.map(function (v, i) { return (i ? "L" : "M") + X(i) + " " + Y(v); }).join(" ");
    el("path", { d: d, fill: "none", stroke: "var(--cool)", "stroke-width": 1.5 }, svg);
    H.forEach(function (v, i) { el("circle", { cx: X(i), cy: Y(v), r: 2.5, fill: v === 0 ? "var(--accent)" : "var(--cool)" }, svg); });
  }
  function balanceMove() {
    var L = armList(S), D = Dof(S);
    if (D < 3) return "the centre needs at least three children for the balance lemma";
    if (!L.length || L[0] - L[L.length - 1] < 2) return "already balanced: all arm sizes differ by at most one";
    var hi = L[0], lo = L[L.length - 1];
    L[0] = hi - 1; L[L.length - 1] = lo + 1; setArms(S, L);
    return "moved one cherry from an A<sub>" + hi + "</sub> to an A<sub>" + lo + "</sub>";
  }
  function initSpiderLab() {
    var o = optComp(60); S.c = o.c; S.arms = o.arms;
    document.getElementById("slOpt").addEventListener("click", function () { var n = nOf(S); if (n < 4) return; var o2 = optComp(n); S.c = o2.c; S.arms = o2.arms; slRender("loaded bgMax(" + n + ")"); });
    document.getElementById("slScr").addEventListener("click", function () {
      var L = armList(S); if (L.length < 2) { slRender("add at least two arms first"); return; }
      for (var t = 0; t < 6; t++) {   // move cherries between random arms; n stays the same
        var a = Math.floor(Math.random() * L.length), b = Math.floor(Math.random() * L.length);
        if (a !== b && L[a] > 0) { L[a]--; L[b]++; }
      }
      setArms(S, L); slRender("scrambled: cherries moved between arms (n unchanged)");
    });
    document.getElementById("slBal").addEventListener("click", function () { slRender(balanceMove()); });
    document.getElementById("slBalAll").addEventListener("click", function () {
      var steps = 0, msg;
      while (steps < 200) { msg = balanceMove(); if (msg.indexOf("moved") !== 0) break; steps++; slRender(); }
      slRender(steps + " balance move" + (steps === 1 ? "" : "s") + "; " + msg);
    });
    slRender();
  }

  // ================================================================= RACES
  function raceStates(n, s) {
    var k4 = 11 - s, k6 = s;
    var a = (n - 1 - 9 * k4) / 11, b = (n - 1 - 13 * k6) / 11;
    return { four: { c: 0, arms: { 4: k4, 5: a } }, six: { c: 0, arms: { 5: b, 6: k6 } } };
  }
  function classNs(s) { var L = []; for (var n = 150; n <= 3200; n++) if ((6 * (n - 1)) % 11 === s) L.push(n); return L; }
  function lf(st) {   // float log F
    var lg = 0, R = 0, D = 0;
    for (var j in st.arms) { var m = st.arms[j]; lg += m * (j * Math.log(1.5) + Math.log((4 * j + 3) / (3 * (+j + 1)))); R += m * 3 / (4 * j + 3); D += m; }
    return lg + Math.log(1 + R / D);
  }
  function raceRender() {
    var s = +document.getElementById("raS").value, Ns = classNs(s), idx = +document.getElementById("raN").value;
    document.getElementById("raN").max = Ns.length - 1;
    idx = Math.min(idx, Ns.length - 1);
    var n = Ns[idx], svg = document.getElementById("raSvg"); clear(svg);
    var vals = Ns.map(function (m) { var r = raceStates(m, s); return 1e6 * Math.expm1(lf(r.four) - lf(r.six)); });
    var lo = -300, hi = 1200, W = 900, H = 320, L = 60, Bm = 34, Tm = 12;
    var X = function (m) { return L + (m - 150) / (3200 - 150) * (W - L - 12); };
    var Y = function (v) { return Tm + (hi - Math.max(lo, Math.min(hi, v))) / (hi - lo) * (H - Tm - Bm); };
    [-250, 0, 250, 500, 750, 1000].forEach(function (v) {
      el("line", { x1: L, x2: W - 12, y1: Y(v), y2: Y(v), stroke: v === 0 ? "var(--ink)" : "var(--line)", "stroke-width": v === 0 ? 1.2 : 1 }, svg);
      el("text", { x: L - 6, y: Y(v) + 4, "text-anchor": "end", "font-size": 11, fill: "var(--muted)" }, svg, String(v));
    });
    [150, 492, 722, 1000, 1500, 2000, 2319, 3000].forEach(function (m) { el("text", { x: X(m), y: H - 12, "text-anchor": "middle", "font-size": 11, fill: "var(--muted)" }, svg, String(m)); });
    el("line", { x1: X(492), x2: X(492), y1: Tm, y2: H - Bm, stroke: "var(--faint)", "stroke-dasharray": "3 3" }, svg);
    el("text", { x: X(492) + 4, y: Tm + 12, "font-size": 11, fill: "var(--muted)" }, svg, "rule proved from 492");
    Ns.forEach(function (m, i) { if (vals[i] > hi || vals[i] < lo) return; el("circle", { cx: X(m), cy: Y(vals[i]), r: 1.8, fill: vals[i] > 0 ? "var(--a4)" : "var(--a6)" }, svg); });
    el("text", { x: L + 4, y: Tm + 12, "font-size": 11, fill: "var(--muted)" }, svg, "smaller n: fours ahead, off the scale");
    if (vals[idx] <= hi && vals[idx] >= lo) el("circle", { cx: X(n), cy: Y(vals[idx]), r: 6, fill: "none", stroke: "var(--accent)", "stroke-width": 2 }, svg);
    el("text", { x: W - 16, y: Tm + 14, "text-anchor": "end", "font-size": 12, fill: "var(--a4)" }, svg, "fours win above 0");
    el("text", { x: W - 16, y: H - Bm - 6, "text-anchor": "end", "font-size": 12, fill: "var(--a6)" }, svg, "sixes win below 0");
    // exact comparison at n
    var r = raceStates(n, s), F4 = Fexact(r.four), F6 = Fexact(r.six), c = cmp(F4, F6);
    document.getElementById("raNval").textContent = "n = " + n;
    var lab = function (st) { return Object.keys(st.arms).sort().reverse().map(function (j) { return "A" + j + "^" + st.arms[j]; }).join(" "); };
    document.getElementById("raReadout").innerHTML = "n = " + n + ", s = " + s + "<br>fours: " + lab(r.four) + " &nbsp; sixes: " + lab(r.six) +
      "<br>exact comparison: " + (c > 0 ? "<b>the fours win</b>" : c < 0 ? "<b>the sixes win</b>" : "tie") +
      ", by " + Math.abs(vals[idx]).toFixed(3) + " parts per million";
  }
  function initRaces() {
    var sel = document.getElementById("raS"), rng = document.getElementById("raN");
    sel.addEventListener("change", function () { var Ns = classNs(+sel.value); rng.value = Math.floor(Ns.length / 3); raceRender(); });
    rng.addEventListener("input", raceRender);
    var Ns = classNs(3); rng.max = Ns.length - 1; rng.value = Ns.indexOf(722);
    raceRender();
  }

  // ================================================================= LADDER
  function atomRate(j, l) {                 // log T / |b| per vertex, activity l; j = -1 cherry, 0 leaf, j >= 1 arm
    if (j === -1) return 0.5 * Math.log((2 + l) / 2);
    if (j === 0) return 0;
    var Tc = (2 + l) / 2, yc = 1 / (2 + l);
    return (j * Math.log(Tc) + Math.log((j + 1 + l * j * yc) / (j + 1))) / (2 * j + 1);
  }
  function bestAtom(l) {
    var best = -1, bv = atomRate(-1, l);
    for (var j = 1; j <= 400; j++) { var v = atomRate(j, l); if (v > bv + 1e-15) { bv = v; best = j; } }
    return { j: best, v: bv };
  }
  var LBREAK = null;
  function breakpoints() {
    if (LBREAK) return LBREAK;
    LBREAK = [];
    for (var j = 3; j <= 8; j++) {
      var a = 0.05, b = 1 + Math.sqrt(5) - 1e-9, g = function (l) { return atomRate(j, l) - atomRate(j + 1, l); };
      for (var it = 0; it < 80; it++) { var m = (a + b) / 2; if (g(a) * g(m) <= 0) b = m; else a = m; }
      LBREAK.push([j, a]);
    }
    return LBREAK;
  }
  var LMAX = 4.2;
  function sliderL() { return Math.max(0.01, (+document.getElementById("ldL").value / 1000) * LMAX); }
  function ladderRender() {
    var l = sliderL(), svg = document.getElementById("ldSvg"); clear(svg);
    var W = 900, H = 360, L = 66, R = 14, T = 14, B = 36, lo = -0.012, hi = 0.0065;
    var X = function (x) { return L + x / LMAX * (W - L - R); };
    var Y = function (v) { return T + (hi - Math.max(lo, Math.min(hi, v))) / (hi - lo) * (H - T - B); };
    [-0.01, -0.005, 0, 0.005].forEach(function (v) {
      el("line", { x1: L, x2: W - R, y1: Y(v), y2: Y(v), stroke: v === 0 ? "var(--ink)" : "var(--line)", "stroke-width": v === 0 ? 1.2 : 1 }, svg);
      el("text", { x: L - 6, y: Y(v) + 4, "text-anchor": "end", "font-size": 11, fill: "var(--muted)" }, svg, v.toFixed(3));
    });
    [0, 0.5, 1, 1.5, 2, 2.5, 3, 3.5, 4].forEach(function (x) { el("text", { x: X(x), y: H - 14, "text-anchor": "middle", "font-size": 11, fill: "var(--muted)" }, svg, String(x)); });
    el("text", { x: W - R, y: H - 2, "text-anchor": "end", "font-size": 11, fill: "var(--muted)" }, svg, "λ");
    var g = 1 + Math.sqrt(5);
    el("line", { x1: X(g), x2: X(g), y1: T, y2: H - B, stroke: "var(--faint)", "stroke-dasharray": "3 3" }, svg);
    el("text", { x: X(g) + 4, y: T + 12, "font-size": 11, fill: "var(--muted)" }, svg, "1+√5");
    el("line", { x1: X(1), x2: X(1), y1: T, y2: H - B, stroke: "var(--faint)", "stroke-dasharray": "3 3" }, svg);
    el("text", { x: X(1) + 4, y: T + 12, "font-size": 11, fill: "var(--muted)" }, svg, "λ = 1");
    var best = bestAtom(l).j;
    for (var j = 1; j <= 12; j++) {
      var col = j === 5 ? "var(--a5)" : j === 4 ? "var(--a4)" : j === 6 ? "var(--a6)" : "var(--other)";
      var seg = [], flush = function () { if (seg.length > 1) el("polyline", { points: seg.join(" "), fill: "none", stroke: col, "stroke-width": j === best ? 3 : 1.1, opacity: j === best ? 1 : 0.7 }, svg); seg = []; };
      for (var i = 0; i <= 480; i++) {
        var x = 0.01 + i / 480 * (LMAX - 0.01), v = atomRate(j, x) - atomRate(-1, x);
        if (v < lo || v > hi) { flush(); continue; }
        seg.push(X(x).toFixed(1) + "," + Y(v).toFixed(1));
      }
      flush();
      var xl = Math.min(LMAX - 0.05, 0.25 + 0.3 * (j - 1)), yl = Y(atomRate(j, xl) - atomRate(-1, xl));
      if (j <= 8) el("text", { x: X(xl) + 3, y: yl - 4, "font-size": 11, fill: col }, svg, "A" + j);
    }
    el("line", { x1: X(l), x2: X(l), y1: T, y2: H - B, stroke: "var(--accent)", "stroke-width": 1.5 }, svg);
    var b = bestAtom(l), bp = breakpoints();
    document.getElementById("ldLval").textContent = "λ = " + l.toFixed(3);
    var name = b.j === -1 ? "the cherry" : "the arm A" + b.j + " (" + (2 * b.j + 1) + " vertices)";
    document.getElementById("ldReadout").innerHTML = "at λ = " + l.toFixed(3) + ", the best of the leaf, cherry and arms is <b>" + name + "</b>, weight per vertex " +
      Math.exp(b.v).toFixed(6) + "<br>breakpoints: " + bp.map(function (p) { return "A" + p[0] + "→A" + (p[0] + 1) + " at " + p[1].toFixed(4); }).join(", ") +
      ", … → 1+√5 = " + g.toFixed(4) + "<br>" + ceilingStatus(l);
  }
  function ceilingStatus(l) {              // the growth-rate ceiling at this λ: which proof regime (proved for every λ > 0)
    var g = 1 + Math.sqrt(5), how;
    if (!(l > 0)) return "ceiling: λ must be positive";   // unreachable from the slider (sliderL floors at 0.01); kept as a guard
    if (l >= g) return "ceiling at this λ: proved (cherry regime, λ ≥ 1+√5: growth rate ½ log(1+λ/2)); hand proof from an interval-arithmetic anchor at 1+√5, not formalized in Lean";
    if (l <= 0.1) how = "typed induction, 0 < λ ≤ 0.1";
    else if (l <= 0.47) how = "power shoulder, 0.1 ≤ λ ≤ 0.47";
    else if (l <= 1.6) how = "quadratic shoulder, 0.47 ≤ λ ≤ 1.6";
    else if (l <= 3.22) how = "three-piece linear, 1.6 ≤ λ ≤ 3.22";
    else how = "hand argument for the thin window 3.22 ≤ λ < 1+√5";
    return "ceiling at this λ: proved (" + how + "); computer-assisted (interval arithmetic), not formalized in Lean" +
      (Math.abs(l - 1) < 0.0025 ? "; at λ = 1 exactly it is also the sharp ceiling of the Lean proof" : "");
  }
  function goldenRender() {
    var svg = document.getElementById("ldGoldSvg"); clear(svg);
    var W = 900, H = 300, L = 56, R = 14, T = 14, B = 34, xmax = 6, lo = 1, hi = 2;
    var X = function (x) { return L + x / xmax * (W - L - R); };
    var Y = function (v) { return T + (hi - v) / (hi - lo) * (H - T - B); };
    [1, 1.25, 1.5, 1.75, 2].forEach(function (v) {
      el("line", { x1: L, x2: W - R, y1: Y(v), y2: Y(v), stroke: "var(--line)" }, svg);
      el("text", { x: L - 6, y: Y(v) + 4, "text-anchor": "end", "font-size": 11, fill: "var(--muted)" }, svg, v.toFixed(2));
    });
    [0, 1, 2, 3, 4, 5, 6].forEach(function (x) { el("text", { x: X(x), y: H - 12, "text-anchor": "middle", "font-size": 11, fill: "var(--muted)" }, svg, String(x)); });
    var Hf = function (l) { return 2 * (1 + l) / (2 + l); }, Z = function (l) { return Math.sqrt((2 + l) / 2); };
    [[Hf, "var(--a5)", "hub factor H(λ)"], [Z, "var(--a4)", "cherry rate ζ(λ)"]].forEach(function (c, k) {
      var pts = []; for (var i = 0; i <= 300; i++) { var x = i / 300 * xmax; pts.push(X(x).toFixed(1) + "," + Y(c[0](x)).toFixed(1)); }
      el("polyline", { points: pts.join(" "), fill: "none", stroke: c[1], "stroke-width": 2 }, svg);
      el("text", { x: X(5.2), y: Y(c[0](5.2)) + (k ? 16 : -8), "font-size": 12, fill: c[1] }, svg, c[2]);
    });
    var g = 1 + Math.sqrt(5), phi = (1 + Math.sqrt(5)) / 2;
    el("circle", { cx: X(g), cy: Y(phi), r: 5, fill: "none", stroke: "var(--accent)", "stroke-width": 2 }, svg);
    el("text", { x: X(g) + 8, y: Y(phi) + 18, "font-size": 12, fill: "var(--ink)" }, svg, "(1+√5, φ = " + phi.toFixed(4) + ")");
    el("text", { x: X(1.3), y: Y(1.93), "font-size": 12, fill: "var(--muted)" }, svg, "long arms win");
    el("text", { x: X(4.2), y: Y(1.08), "font-size": 12, fill: "var(--muted)" }, svg, "cherries win");
  }
  function initLadder() {
    var r = document.getElementById("ldL");
    r.value = Math.round(1 / LMAX * 1000);
    r.addEventListener("input", ladderRender);
    document.getElementById("ldOne").addEventListener("click", function () { r.value = Math.round(1 / LMAX * 1000); ladderRender(); });
    document.getElementById("ldGold").addEventListener("click", function () { r.value = Math.round((1 + Math.sqrt(5)) / LMAX * 1000); ladderRender(); });
    ladderRender(); goldenRender();
  }

  var inited = {};
  function start(p) {
    if (inited[p]) return;
    if (p === "treelab") initTreeLab(); else if (p === "spiderlab") initSpiderLab(); else if (p === "races") initRaces(); else if (p === "ladder") initLadder(); else return;
    inited[p] = true;
  }
  document.addEventListener("bg-show", function (e) { start(e.detail); });
  var act = document.querySelector(".panel.active");   // a deep link may have opened a lab before this ran
  if (act) start(act.id.slice(2));
})();
