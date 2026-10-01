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
    if (l >= g) return "ceiling at this λ: proved (cherry regime, λ ≥ 1+√5: growth rate ½ log(1+λ/2)); hand proof (calculus at 1+√5 with the golden-ratio identities, then a monotonicity argument), also kernel-checked in Lean";
    if (l <= 0.1) how = "typed induction, 0 < λ ≤ 0.1";
    else if (l <= 0.47) how = "power shoulder, 0.1 ≤ λ ≤ 0.47";
    else if (l <= 1.6) how = "quadratic shoulder, 0.47 ≤ λ ≤ 1.6";
    else if (l < 2) how = "three-piece linear, 1.6 ≤ λ ≤ 3.22";
    else if (l < 3.22) return "ceiling at this λ: proved (three-piece linear, 1.6 ≤ λ ≤ 3.22; computer-assisted, interval arithmetic); also proved in Lean, not by hand: the window witness is verified by 45 exact-rational box checks (2,078 inequalities) checked by the kernel (the inequality; its equality clause is not formalized)";
    else return "ceiling at this λ: proved (hand argument for the thin window 3.22 ≤ λ < 1+√5); also proved in Lean, by hand (the inequality; its equality clause is not formalized)";
    return "ceiling at this λ: proved (" + how + "); computer-assisted (interval arithmetic); Lean reduces it to these numerical inputs but does not prove them" +
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

  // ================================================================= THE λ-FAMILY: CHERRY REGIME, NEVER ATTAINED, ONE BLOCK
  // LAMBDA-CORE:BEGIN   (pure functions, no DOM; scripts/check_lambda_labs.py runs this block in node)
  // A planted branch is the array of its children (each a branch); the leaf is [].
  // LTREES:BEGIN
  // every unlabeled tree on n vertices, n = 1..12, as base-36 parent arrays (scripts/gen_lambda_lab_data.py)
  var LTREES = [
    "",
    "0",
    "00",
    "000,001",
    "0000,0001,0012",
    "00000,00001,00011,00012,00112,00123",
    "000000,000001,000011,000012,000112,000123,000124,001112,001122,001223,001234",
    "0000000,0000001,0000011,0000012,0000111,0000112,0000123,0000125,0001112,0001122,0001123,0001124,0001224,0001234,0001245,0011112,0011122,0011223,0011235,0012223,0012233,0012334,0012345",
    "00000000,00000001,00000011,00000012,00000111,00000112,00000123,00000126,00001112,00001122,00001123,00001125,00001225,00001234,00001235,00001255,00001256,00011112,00011122,00011123,00011223,00011224,00011234,00011246,00012224,00012234,00012244,00012344,00012345,00012445,00012456,00111112,00111122,00111222,00111236,00112223,00112235,00112335,00112345,00122223,00122233,00122334,00122346,00123334,00123344,00123445,00123456",
    "000000000,000000001,000000011,000000012,000000111,000000112,000000123,000000127,000001111,000001112,000001122,000001123,000001126,000001226,000001234,000001236,000001266,000001267,000011112,000011122,000011123,000011125,000011223,000011225,000011234,000011235,000011257,000012225,000012235,000012255,000012345,000012355,000012356,000012556,000012567,000111112,000111122,000111123,000111222,000111223,000111224,000111234,000111247,000112224,000112233,000112234,000112244,000112245,000112246,000112345,000112346,000112446,000112456,000112467,000122224,000122234,000122244,000122334,000122344,000122445,000122457,000123345,000123445,000123456,000123457,000124445,000124455,000124556,000124567,001111112,001111122,001111222,001111237,001112223,001112236,001112336,001112346,001122223,001122233,001122234,001122335,001122345,001122357,001123335,001123345,001123355,001123556,001123567,001222223,001222233,001222333,001222334,001222347,001223334,001223345,001223346,001223446,001223456,001233334,001233344,001233445,001233457,001234445,001234455,001234556,001234567",
    "0000000000,0000000001,0000000011,0000000012,0000000111,0000000112,0000000123,0000000128,0000001111,0000001112,0000001122,0000001123,0000001127,0000001227,0000001234,0000001237,0000001277,0000001278,0000011112,0000011122,0000011123,0000011126,0000011223,0000011226,0000011234,0000011236,0000011266,0000011267,0000011268,0000012226,0000012236,0000012266,0000012345,0000012346,0000012366,0000012367,0000012666,0000012667,0000012678,0000111112,0000111122,0000111123,0000111222,0000111223,0000111225,0000111234,0000111235,0000111258,0000112225,0000112233,0000112234,0000112235,0000112255,0000112256,0000112257,0000112345,0000112355,0000112356,0000112357,0000112557,0000112567,0000112578,0000122225,0000122235,0000122255,0000122335,0000122345,0000122355,0000122555,0000122556,0000122568,0000123356,0000123455,0000123456,0000123555,0000123556,0000123567,0000123568,0000125556,0000125566,0000125567,0000125667,0000125677,0000125678,0001111112,0001111122,0001111123,0001111222,0001111223,0001111248,0001112223,0001112224,0001112233,0001112234,0001112247,0001112347,0001112447,0001112457,0001122224,0001122234,0001122244,0001122245,0001122334,0001122344,0001122345,0001122346,0001122446,0001122456,0001122468,0001123346,0001123446,0001123456,0001123467,0001123468,0001124446,0001124456,0001124466,0001124667,0001124678,0001222224,0001222234,0001222244,0001222334,0001222344,0001222444,0001222445,0001222458,0001223344,0001223444,0001223445,0001223458,0001224445,0001224456,0001224457,0001224557,0001224567,0001224577,0001233345,0001233445,0001233458,0001234445,0001234455,0001234456,0001234457,0001234557,0001234567,0001234577,0001234578,0001244445,0001244455,0001244556,0001244568,0001245556,0001245566,0001245667,0001245678,0011111112,0011111122,0011111222,0011111238,0011112222,0011112237,0011112337,0011112347,0011122223,0011122236,0011122336,0011122346,0011123336,0011123346,0011123366,0011123456,0011123678,0011222223,0011222233,0011222234,0011222335,0011222345,0011222358,0011223335,0011223345,0011223355,0011223356,0011223456,0011223557,0011223567,0011223578,0011233335,0011233345,0011233355,0011233445,0011233455,0011233568,0011234568,0011235556,0011235667,0012222223,0012222233,0012222333,0012222334,0012222348,0012223334,0012223345,0012223347,0012223447,0012223457,0012223477,0012233334,0012233344,0012233345,0012233446,0012233456,0012233468,0012234446,0012234456,0012234466,0012234566,0012234667,0012234678,0012333334,0012333344,0012333444,0012333458,0012334445,0012334457,0012334557,0012334567,0012344445,0012344455,0012344556,0012344568,0012345556,0012345566,0012345667,0012345678",
    "00000000000,00000000001,00000000011,00000000012,00000000111,00000000112,00000000123,00000000129,00000001111,00000001112,00000001122,00000001123,00000001128,00000001228,00000001234,00000001238,00000001288,00000001289,00000011111,00000011112,00000011122,00000011123,00000011127,00000011223,00000011227,00000011234,00000011237,00000011277,00000011278,00000011279,00000012227,00000012237,00000012277,00000012345,00000012347,00000012377,00000012378,00000012777,00000012778,00000012789,00000111112,00000111122,00000111123,00000111126,00000111222,00000111223,00000111226,00000111234,00000111236,00000111269,00000112226,00000112233,00000112234,00000112236,00000112266,00000112267,00000112268,00000112345,00000112346,00000112366,00000112367,00000112368,00000112668,00000112678,00000112689,00000122226,00000122236,00000122266,00000122336,00000122346,00000122366,00000122666,00000122667,00000122679,00000123367,00000123456,00000123466,00000123467,00000123666,00000123667,00000123678,00000123679,00000126667,00000126677,00000126678,00000126778,00000126788,00000126789,00001111112,00001111122,00001111123,00001111222,00001111223,00001111225,00001111234,00001111235,00001111259,00001112223,00001112225,00001112233,00001112234,00001112235,00001112255,00001112256,00001112258,00001112345,00001112356,00001112358,00001112558,00001112568,00001112589,00001122225,00001122235,00001122255,00001122256,00001122334,00001122335,00001122345,00001122355,00001122356,00001122357,00001122557,00001122567,00001122579,00001123357,00001123455,00001123456,00001123457,00001123557,00001123567,00001123578,00001123579,00001125557,00001125567,00001125577,00001125778,00001125789,00001222225,00001222235,00001222255,00001222335,00001222345,00001222355,00001222555,00001222556,00001222569,00001223345,00001223355,00001223455,00001223555,00001223556,00001223569,00001225556,00001225567,00001225568,00001225668,00001225678,00001225688,00001233356,00001233456,00001233556,00001233569,00001234555,00001234556,00001234567,00001234569,00001235556,00001235566,00001235567,00001235568,00001235668,00001235678,00001235688,00001235689,00001255556,00001255566,00001255667,00001255679,00001256667,00001256677,00001256778,00001256789,00011111112,00011111122,00011111123,00011111222,00011111223,00011111249,00011112222,00011112223,00011112224,00011112233,00011112234,00011112248,00011112348,00011112448,00011112458,00011122224,00011122233,00011122234,00011122244,00011122245,00011122247,00011122334,00011122344,00011122345,00011122347,00011122447,00011122457,00011122479,00011123347,00011123447,00011123457,00011123478,00011123479,00011124447,00011124457,00011124477,00011124567,00011124778,00011124789,00011222224,00011222234,00011222244,00011222245,00011222334,00011222344,00011222345,00011222444,00011222445,00011222446,00011222456,00011222469,00011223344,00011223345,00011223346,00011223445,00011223446,00011223456,00011223468,00011223469,00011224446,00011224456,00011224466,00011224467,00011224468,00011224567,00011224568,00011224668,00011224678,00011224689,00011233346,00011233446,00011233456,00011233469,00011234446,00011234456,00011234466,00011234467,00011234567,00011234568,00011234668,00011234678,00011234689,00011244446,00011244456,00011244466,00011244556,00011244566,00011244667,00011244679,00011245667,00011245679,00011246667,00011246677,00011246778,00011246789,00012222224,00012222234,00012222244,00012222334,00012222344,00012222444,00012222445,00012222459,00012223334,00012223344,00012223444,00012223445,00012223459,00012224445,00012224456,00012224458,00012224558,00012224568,00012224588,00012233444,00012233445,00012233459,00012234445,00012234456,00012234457,00012234458,00012234558,00012234568,00012234578,00012234588,00012244445,00012244455,00012244456,00012244557,00012244567,00012244579,00012245557,00012245567,00012245577,00012245677,00012245778,00012245789,00012333345,00012333445,00012333459,00012334445,00012334455,00012334458,00012334558,00012334588,00012334589,00012344445,00012344455,00012344456,00012344556,00012344557,00012344567,00012344579,00012345557,00012345567,00012345577,00012345677,00012345678,00012345778,00012345789,00012444445,00012444455,00012444555,00012444556,00012444569,00012445556,00012445567,00012445568,00012445668,00012445678,00012455556,00012455566,00012455667,00012455679,00012456667,00012456677,00012456778,00012456789,00111111112,00111111122,00111111222,00111111239,00111112222,00111112238,00111112338,00111112348,00111122223,00111122237,00111122337,00111122347,00111123337,00111123347,00111123377,00111123457,00111123789,00111222223,00111222233,00111222234,00111222336,00111222346,00111222369,00111223336,00111223346,00111223366,00111223367,00111223456,00111223467,00111223668,00111223678,00111223689,00111233336,00111233346,00111233366,00111233446,00111233456,00111233466,00111233679,00111234679,00111236667,00111236778,00112222223,00112222233,00112222234,00112222333,00112222334,00112222335,00112222345,00112222359,00112223335,00112223345,00112223356,00112223358,00112223458,00112223558,00112223568,00112233335,00112233345,00112233355,00112233356,00112233445,00112233455,00112233456,00112233557,00112233567,00112233579,00112234557,00112234567,00112234579,00112235557,00112235567,00112235577,00112235778,00112235789,00112333335,00112333345,00112333355,00112333445,00112333455,00112333555,00112333569,00112334455,00112334569,00112335556,00112335568,00112335668,00112335678,00112344569,00112345556,00112345668,00112345678,00112355556,00112355566,00112355667,00112355679,00112356667,00112356677,00112356778,00112356789,00122222223,00122222233,00122222333,00122222334,00122222349,00122223333,00122223334,00122223345,00122223348,00122223448,00122223458,00122223488,00122233334,00122233344,00122233345,00122233347,00122233447,00122233456,00122233457,00122233479,00122234447,00122234457,00122234477,00122234567,00122234577,00122234778,00122234789,00122333334,00122333344,00122333345,00122333445,00122333446,00122333456,00122333469,00122334446,00122334456,00122334466,00122334467,00122334567,00122334568,00122334668,00122334678,00122334689,00122344446,00122344456,00122344466,00122344556,00122344566,00122344667,00122344679,00122345667,00122345679,00122346667,00122346778,00123333334,00123333344,00123333444,00123333459,00123334445,00123334458,00123334558,00123334568,00123344445,00123344455,00123344456,00123344557,00123344567,00123344579,00123345557,00123345567,00123345577,00123345778,00123345789,00123444445,00123444455,00123444555,00123444556,00123444569,00123445556,00123445567,00123445568,00123445668,00123445678,00123455556,00123455566,00123455667,00123455679,00123456667,00123456677,00123456778,00123456789"
  ];
  // LTREES:END
  var LCH = 1 + Math.sqrt(5), PHI = (1 + Math.sqrt(5)) / 2;
  function brTY(b, l) {                    // cavity recursion: [T_b, y_b], d = #children + 1
    var P = 1, R = 0;
    for (var i = 0; i < b.length; i++) { var c = brTY(b[i], l); P *= c[0]; R += c[1]; }
    var d = b.length + 1;
    return [P * (d + l * R) / d, 1 / (d + l * R)];
  }
  function brT(b, l) { return brTY(b, l)[0]; }
  function brSize(b) { var s = 1; for (var i = 0; i < b.length; i++) s += brSize(b[i]); return s; }
  function wholePi(b, l) {                 // pi_lambda of the whole tree rooted at b (root degree k = #children)
    if (!b.length) return 1;
    var P = 1, R = 0;
    for (var i = 0; i < b.length; i++) { var c = brTY(b[i], l); P *= c[0]; R += c[1]; }
    return P * (b.length + l * R) / b.length;
  }
  function parToBr(par) {                  // parent array (par[0] = -1) -> branch rooted at vertex 0
    var ch = par.map(function () { return []; });
    for (var i = par.length - 1; i >= 1; i--) ch[par[i]].unshift(ch[i]);
    return ch[0];
  }
  function decodeTree(s) { var p = [-1]; for (var i = 0; i < s.length; i++) p.push(parseInt(s[i], 36)); return p; }
  function treesOf(n) { return n >= 1 && n <= LTREES.length ? LTREES[n - 1].split(",").map(decodeTree) : null; }
  function maxPi(n, l) {                   // M_n(lambda) for n <= 12, and a maximizer
    var ts = treesOf(n); if (!ts) return null;
    var best = -1, arg = null;
    ts.forEach(function (p) { var v = wholePi(parToBr(p), l); if (v > best) { best = v; arg = p; } });
    return { v: best, par: arg };
  }
  var BR_CHERRY = [[]];
  function brArm(j) { var a = []; for (var i = 0; i < j; i++) a.push([[]]); return a; }
  function brPath(m) { var b = []; for (var i = 1; i < m; i++) b = [b]; return b; }
  function atomLogRate(l) {                // f*(lambda): best log-rate over leaf, cherry and arms A_j, j <= 400
    var c = 1 + l / 2, t = l / (2 + l), best = 0.5 * Math.log(c), arg = -1;
    for (var j = 1; j <= 400; j++) {
      var v = (j * Math.log(c) + Math.log(1 + t * j / (j + 1))) / (2 * j + 1);
      if (v > best + 1e-15) { best = v; arg = j; }
    }
    return { v: Math.max(best, 0), j: arg };
  }
  function blockWitness(b, n) {            // center + k copies of b + r leaves, n vertices
    var s = brSize(b), k = Math.floor((n - 1) / s), r = n - 1 - k * s, w = [];
    for (var i = 0; i < k; i++) w.push(b);
    for (var q = 0; q < r; q++) w.push([]);
    return { tree: w, k: k, r: r };
  }
  // LAMBDA-CORE:END

  function lplot(svg, o) {                  // axes on a 900-wide viewBox; returns coordinate maps
    var W = 900, H = +svg.getAttribute("viewBox").split(" ")[3], L = o.left || 70, R = 16, T = 14, B = 40;
    var X = function (x) { return L + (x - o.x0) / (o.x1 - o.x0) * (W - L - R); };
    var Y = function (v) { return T + (o.y1 - Math.max(o.y0, Math.min(o.y1, v))) / (o.y1 - o.y0) * (H - T - B); };
    o.yt.forEach(function (v) {
      el("line", { x1: L, x2: W - R, y1: Y(v), y2: Y(v), stroke: v === o.zero ? "var(--ink)" : "var(--line)", "stroke-width": v === o.zero ? 1.2 : 1 }, svg);
      el("text", { x: L - 6, y: Y(v) + 5, "text-anchor": "end", "font-size": 14, fill: "var(--muted)" }, svg, o.yf ? o.yf(v) : String(v));
    });
    o.xt.forEach(function (x) { el("text", { x: X(x), y: H - 16, "text-anchor": "middle", "font-size": 14, fill: "var(--muted)" }, svg, o.xf ? o.xf(x) : String(x)); });
    if (o.xl) el("text", { x: W - R, y: H - 1, "text-anchor": "end", "font-size": 14, fill: "var(--muted)" }, svg, o.xl);
    return { X: X, Y: Y, W: W, H: H, L: L, R: R, T: T, B: B };
  }
  function curve(svg, A, f, x0, x1, col, w, dash, lo, hi) {
    var seg = [], N = 360, flush = function () {
      if (seg.length > 1) { var a = { points: seg.join(" "), fill: "none", stroke: col, "stroke-width": w }; if (dash) a["stroke-dasharray"] = dash; el("polyline", a, svg); }
      seg = [];
    };
    for (var i = 0; i <= N; i++) {
      var x = x0 + i / N * (x1 - x0), v = f(x);
      if (!isFinite(v) || v < lo || v > hi) { flush(); continue; }
      seg.push(A.X(x).toFixed(1) + "," + A.Y(v).toFixed(1));
    }
    flush();
  }
  function vmark(svg, A, x, label, col) {
    el("line", { x1: A.X(x), x2: A.X(x), y1: A.T, y2: A.H - A.B, stroke: col || "var(--faint)", "stroke-dasharray": col ? null : "3 3", "stroke-width": col ? 1.5 : 1 }, svg);
    if (label) el("text", { x: A.X(x) + 5, y: A.T + 14, "font-size": 14, fill: "var(--muted)" }, svg, label);
  }
  function drawBrTree(svg, b, opts) {        // tidy top-down drawing of a rooted tree (b = children of the root)
    clear(svg);
    var W = 900, H = +svg.getAttribute("viewBox").split(" ")[3], nodes = [], edges = [], leafX = 0, maxD = 0;
    (function place(t, d, col) {
      var me = { d: d, col: col }; nodes.push(me); maxD = Math.max(maxD, d);
      if (!t.length) { me.x = leafX++; return me; }
      var xs = t.map(function (c, i) { var ch = place(c, d + 1, d === 0 && opts.colorOf ? opts.colorOf(i) : col); edges.push([me, ch]); return ch.x; });
      me.x = (xs[0] + xs[xs.length - 1]) / 2; return me;
    })(b, 0, "var(--ink)");
    var sx = (W - 40) / Math.max(1, leafX - 1), sy = (H - 40) / Math.max(1, maxD);
    var X = function (v) { return leafX === 1 ? W / 2 : 20 + v.x * sx; }, Y = function (v) { return 20 + v.d * Math.min(sy, 70); };
    edges.forEach(function (e) { el("line", { x1: X(e[0]), y1: Y(e[0]), x2: X(e[1]), y2: Y(e[1]), stroke: e[1].col, "stroke-width": 1.6 }, svg); });
    var r = Math.max(2.5, Math.min(7, sx / 3));
    nodes.forEach(function (v) { el("circle", { cx: X(v), cy: Y(v), r: v.d === 0 ? r + 2 : r, fill: v.d === 0 ? "var(--accent)" : "var(--surface)", stroke: v.col, "stroke-width": 1.5 }, svg); });
    if (opts.caption) el("text", { x: W - 10, y: H - 6, "text-anchor": "end", "font-size": 14, fill: "var(--muted)" }, svg, opts.caption);
  }
  function fmtNum(v) { return Math.abs(v) >= 1e6 || (Math.abs(v) < 1e-3 && v !== 0) ? v.toExponential(5) : v.toPrecision(8); }

  // ---------------------------------------------------------------- cherry regime
  var CRMAX = 20, CRSEED = 7, CRRAND = null;
  function seeded(seed) { var s = seed >>> 0; return function () { s = (s * 1664525 + 1013904223) >>> 0; return s / 4294967296; }; }
  function randomBranch(seed) {
    var rnd = seeded(seed), m = 7 + Math.floor(rnd() * 3), par = [-1];
    for (var i = 1; i < m; i++) par.push(Math.floor(rnd() * i));
    return parToBr(par);
  }
  function crBranches() {
    if (!CRRAND) CRRAND = randomBranch(CRSEED);
    return [
      { name: "cherry", b: BR_CHERRY, col: "var(--ink)", w: 3 },
      { name: "path P3 (planted at an end)", b: brPath(3), col: "var(--a4)", w: 1.8 },
      { name: "star K1,3 (planted at the center)", b: [[], [], []], col: "var(--a6)", w: 1.8 },
      { name: "A2", b: brArm(2), col: "var(--other)", w: 1.8 },
      { name: "A5", b: brArm(5), col: "var(--a5)", w: 2.2 },
      { name: "random, " + brSize(CRRAND) + " vertices", b: CRRAND, col: "var(--cool)", w: 1.6, dash: "6 4" }
    ];
  }
  function crL() { return LCH + (+document.getElementById("crL").value / 1000) * (CRMAX - LCH); }
  function normRate(b, l) { return Math.log(brT(b, l)) / brSize(b) - 0.5 * Math.log(1 + l / 2); }
  function crRender() {
    var l = crL(), x0 = 2, x1 = CRMAX;
    document.getElementById("crLval").textContent = "λ = " + l.toFixed(3);
    // arms against the cherry
    var svg = document.getElementById("crAtomSvg"); clear(svg);
    var lo = -0.03, hi = 0.004;
    var A = lplot(svg, { x0: x0, x1: x1, y0: lo, y1: hi, yt: [-0.03, -0.02, -0.01, 0], zero: 0, yf: function (v) { return v.toFixed(2); }, xt: [2, 4, 6, 8, 10, 12, 14, 16, 18, 20], xl: "λ" });
    vmark(svg, A, LCH, "1+√5");
    var cr = function (x) { return 0.5 * Math.log(1 + x / 2); };
    for (var j = 1; j <= 12; j++) (function (j) {
      var col = j === 5 ? "var(--a5)" : j === 4 ? "var(--a4)" : j === 6 ? "var(--a6)" : "var(--other)";
      curve(svg, A, function (x) { var c = 1 + x / 2, t = x / (2 + x); return (j * Math.log(c) + Math.log(1 + t * j / (j + 1))) / (2 * j + 1) - cr(x); }, x0, x1, col, j === 5 ? 2 : 1.1, null, lo, hi);
      var fj = function (x) { var c = 1 + x / 2, t = x / (2 + x); return (j * Math.log(c) + Math.log(1 + t * j / (j + 1))) / (2 * j + 1) - cr(x); };
      if (j === 3 || j === 4 || j === 5 || j === 8 || j === 12) {        // label where the curve leaves the plot, or at the right edge
        var xe = x1;
        if (fj(x1) < lo) { var a = LCH, b = x1; for (var it = 0; it < 50; it++) { var m = (a + b) / 2; if (fj(m) < lo) b = m; else a = m; } xe = a; }
        el("text", { x: A.X(xe) + (xe < x1 ? 4 : -4), y: A.Y(fj(xe)) - 5, "text-anchor": xe < x1 ? "start" : "end", "font-size": 13, fill: col }, svg, "A" + j);
      }
    })(j);
    el("text", { x: A.X(x1) - 4, y: A.Y(0) - 6, "text-anchor": "end", "font-size": 13, fill: "var(--ink)" }, svg, "cherry");
    vmark(svg, A, l, null, "var(--accent)");
    // normalized branch weights
    svg = document.getElementById("crSvg"); clear(svg);
    lo = -0.25; hi = 0.012;
    A = lplot(svg, { x0: x0, x1: x1, y0: lo, y1: hi, yt: [-0.25, -0.2, -0.15, -0.1, -0.05, 0], zero: 0, yf: function (v) { return v.toFixed(2); }, xt: [2, 4, 6, 8, 10, 12, 14, 16, 18, 20], xl: "λ" });
    el("rect", { x: A.X(2), y: A.T, width: A.X(LCH) - A.X(2), height: A.H - A.T - A.B, fill: "var(--sunk)", opacity: 0.6 }, svg);
    vmark(svg, A, LCH, null);
    el("text", { x: A.X(LCH) + 6, y: A.Y(-0.22), "font-size": 14, fill: "var(--muted)" }, svg, "anchor 1+√5: T_b ≤ φ^|b|");
    var BRS = crBranches(), leg = document.getElementById("crLegend"); leg.innerHTML = "";
    BRS.forEach(function (o) {
      curve(svg, A, function (x) { return normRate(o.b, x); }, x0, x1, o.col, o.w, o.dash, lo, hi);
      var sp = document.createElement("span"); sp.style.color = o.col; sp.textContent = o.name; leg.appendChild(sp);
    });
    vmark(svg, A, l, null, "var(--accent)");
    // readout
    var best = -1, bv = -1e9;
    for (var k = 1; k <= 400; k++) { var c = 1 + l / 2, t = l / (2 + l), v = (k * Math.log(c) + Math.log(1 + t * k / (k + 1))) / (2 * k + 1); if (v > bv) { bv = v; best = k; } }
    var atAnchor = Math.abs(l - LCH) < 1e-9;
    var lines = ["at λ = " + l.toFixed(4) + ": cherry rate ½ log(1+λ/2) = " + cr(l).toFixed(6) + "; closest arm (j ≤ 400) A" + best + " rate " + bv.toFixed(6) + " (below by " + (cr(l) - bv).toExponential(2) + ")"];
    BRS.forEach(function (o) {
      var s = brSize(o.b), T = brT(o.b, l), U = atAnchor ? Math.pow(PHI, s) : Math.pow(1 + l / 2, s / 2);
      lines.push(o.name + ": |b| = " + s + ", T_b = " + fmtNum(T) + (atAnchor ? " ≤ φ^|b| = " : " ≤ (1+λ/2)^(|b|/2) = ") + fmtNum(U) + ", ratio " + (T / U).toFixed(6));
    });
    document.getElementById("crReadout").innerHTML = lines.join("<br>");
  }

  // ---------------------------------------------------------------- never attained
  var NAMAX = 20;
  function naL() { return LCH + (+document.getElementById("naL").value / 1000) * (NAMAX - LCH); }
  function naRender() {
    var l = naL(), n0 = +document.getElementById("naN").value, c = 1 + l / 2;
    document.getElementById("naLval").textContent = "λ = " + l.toFixed(3);
    document.getElementById("naNval").textContent = "n = " + n0;
    var up = function (n) { return (1 + l) * Math.pow(c, (n - 1) / 2); }, low = function (n) { return Math.pow(c, Math.floor((n - 1) / 2)); };
    var M = []; for (var n = 1; n <= 12; n++) M[n] = maxPi(n, l);
    // normalized log plot
    var svg = document.getElementById("naSvg"); clear(svg);
    var norm = function (v, n) { return Math.log(v / Math.pow(c, (n - 1) / 2)); };
    var y1 = Math.log(1 + l) + 0.25, y0 = -0.5 * Math.log(c) - 0.25;
    var yt = [], ytv = [0.25, 0.5, 1, 2, 4, 8, 16, 32];
    ytv.forEach(function (v) { if (Math.log(v) >= y0 && Math.log(v) <= y1) yt.push(Math.log(v)); });
    var A = lplot(svg, { x0: 0.5, x1: 20.5, y0: y0, y1: y1, yt: yt, yf: function (v) { return String(+Math.exp(v).toPrecision(3)); }, xt: [1, 4, 8, 12, 16, 20], xl: "n" });
    el("line", { x1: A.X(0.5), x2: A.X(20.5), y1: A.Y(Math.log(1 + l)), y2: A.Y(Math.log(1 + l)), stroke: "var(--a5)", "stroke-width": 2 }, svg);
    el("text", { x: A.X(20.5) - 4, y: A.Y(Math.log(1 + l)) - 6, "text-anchor": "end", "font-size": 13, fill: "var(--a5)" }, svg, "upper bound: 1 + λ");
    vmark(svg, A, n0, null, "var(--accent)");
    for (n = 1; n <= 20; n++) {
      el("circle", { cx: A.X(n), cy: A.Y(norm(low(n), n)), r: 4, fill: "none", stroke: "var(--a4)", "stroke-width": 1.6 }, svg);
      if (n <= 12) el("circle", { cx: A.X(n), cy: A.Y(norm(M[n].v, n)), r: 5, fill: "var(--ink)" }, svg);
    }
    // n-th roots
    svg = document.getElementById("naRateSvg"); clear(svg);
    var rho = Math.sqrt(c), NN = 120;
    y0 = rho * 0.8; y1 = rho * 1.3;
    var B = lplot(svg, { x0: 1, x1: NN, y0: y0, y1: y1, yt: [rho * 0.8, rho * 0.9, rho, rho * 1.1, rho * 1.2, rho * 1.3], yf: function (v) { return v.toFixed(3); }, xt: [1, 20, 40, 60, 80, 100, 120], xl: "n" });
    [[up, "var(--a5)"], [low, "var(--a4)"]].forEach(function (f) {   // integer n only
      var pts = []; for (var k = 1; k <= NN; k++) { var v = Math.pow(f[0](k), 1 / k); if (v >= y0 && v <= y1) pts.push(B.X(k).toFixed(1) + "," + B.Y(v).toFixed(1)); }
      el("polyline", { points: pts.join(" "), fill: "none", stroke: f[1], "stroke-width": 1.8 }, svg);
    });
    el("line", { x1: B.X(1), x2: B.X(NN), y1: B.Y(rho), y2: B.Y(rho), stroke: "var(--ink)", "stroke-dasharray": "6 4" }, svg);
    el("text", { x: B.X(NN) - 4, y: B.Y(rho) - 6, "text-anchor": "end", "font-size": 13, fill: "var(--ink)" }, svg, "√(1+λ/2) = " + rho.toFixed(4));
    for (n = 1; n <= 12; n++) el("circle", { cx: B.X(n), cy: B.Y(Math.pow(M[n].v, 1 / n)), r: 3.5, fill: "var(--ink)" }, svg);
    // readout + a maximizer
    var lines = ["n = " + n0 + ", λ = " + l.toFixed(4) + ": lower (1+λ/2)^⌊(n−1)/2⌋ = " + fmtNum(low(n0)) + ", upper (1+λ)(1+λ/2)^((n−1)/2) = " + fmtNum(up(n0))];
    var tsvg = document.getElementById("naTreeSvg");
    if (n0 <= 12) {
      var m = M[n0];
      lines.push("M_n = " + fmtNum(m.v) + " over " + treesOf(n0).length + " trees; M_n / upper = " + (m.v / up(n0)).toFixed(6) + " < 1; M_n / lower = " + (m.v / low(n0)).toFixed(6) + " ≥ 1");
      drawBrTree(tsvg, parToBr(m.par), { caption: "a maximizer on " + n0 + " vertices at this λ (drawn from vertex 0)" });
    } else {
      lines.push("n > 12: the bounds only (M_n is drawn for n ≤ 12)");
      drawBrTree(tsvg, blockWitness(BR_CHERRY, n0).tree, { caption: "the lower-bound tree: a center with ⌊(n−1)/2⌋ cherries" + (n0 % 2 === 0 ? " and a leaf" : "") });
    }
    document.getElementById("naReadout").innerHTML = lines.join("<br>");
  }

  // ---------------------------------------------------------------- one block
  var OBMAX = 6;
  function obL() { return +document.getElementById("obL").value / 600 * OBMAX; }
  function obBranch() {
    var v = document.getElementById("obB").value;
    if (v === "leaf") return { b: [], name: "the leaf" };
    if (v === "cherry") return { b: BR_CHERRY, name: "the cherry" };
    if (v === "path") return { b: brPath(5), name: "the path on 5 vertices" };
    return { b: brArm(+v), name: "the arm A" + v };
  }
  function obRender() {
    var l = obL(), n = +document.getElementById("obN").value, B = obBranch(), s = brSize(B.b);
    document.getElementById("obLval").textContent = "λ = " + l.toFixed(3);
    document.getElementById("obNval").textContent = "n = " + n;
    var wit = blockWitness(B.b, n);
    drawBrTree(document.getElementById("obTreeSvg"), wit.tree, {
      colorOf: function (i) { return i < wit.k ? "var(--a5)" : "var(--other)"; },
      caption: "center + " + wit.k + " × " + B.name.replace(/^the /, "") + " + " + wit.r + " leaves = " + n + " vertices"
    });
    // per-vertex rate plot
    var svg = document.getElementById("obRateSvg"); clear(svg);
    var y0 = 0.96, y1 = 1.003, rhoF = function (x) { return x >= LCH ? Math.sqrt(1 + x / 2) : Math.exp(atomLogRate(x).v); };
    var A = lplot(svg, { x0: 0, x1: OBMAX, y0: y0, y1: y1, yt: [0.96, 0.97, 0.98, 0.99, 1], zero: 1, yf: function (v) { return v.toFixed(2); }, xt: [0, 1, 2, 3, 4, 5, 6], xl: "λ", left: 64 });
    vmark(svg, A, LCH, "1+√5");
    curve(svg, A, function (x) { return Math.sqrt(1 + x / 2) / rhoF(x); }, 0.01, OBMAX, "var(--faint)", 1.4, "5 4", y0, y1);
    curve(svg, A, function (x) { return Math.pow(brT(B.b, x), 1 / s) / rhoF(x); }, 0.01, OBMAX, "var(--a5)", 2.2, null, y0, y1);
    el("circle", { cx: A.X(1), cy: A.Y(1), r: 5, fill: "none", stroke: "var(--accent)", "stroke-width": 2 }, svg);
    el("text", { x: A.X(1) + 8, y: A.Y(1) + 34, "font-size": 13, fill: "var(--ink)" }, svg, "λ = 1: A5 attains ρ(1) = (621/64)^(1/11)");
    vmark(svg, A, l, null, "var(--accent)");
    // readout
    var T = brT(B.b, l), rate = Math.pow(T, 1 / s), at = atomLogRate(l), rho = Math.exp(at.v);
    var exact = l >= LCH;
    if (exact) rho = Math.sqrt(1 + l / 2);
    var low = Math.pow(T, wit.k), wv = wholePi(wit.tree, l), up = (1 + l) * Math.pow(rho, n - 1);
    var lines = [B.name + ": |b| = " + s + ", T_b(λ) = " + fmtNum(T) + ", per vertex T_b^(1/|b|) = " + rate.toFixed(6),
      "ρ(λ) = " + rho.toFixed(6) + (exact ? " = √(1+λ/2), the cherry (kernel-checked for λ ≥ 1+√5)" :
        " = e^f*, best block " + (at.j < 0 ? "the cherry" : "A" + at.j) + (l >= 3.22 ? " (proved in Lean by hand on the window 3.22 ≤ λ < 1+√5; arms j ≤ 400)" : l >= 2 ? " (proved in Lean on 2 ≤ λ < 3.22 by kernel-checked exact-rational box checks; arms j ≤ 400)" : " (computer-assisted; in Lean only reduced to its numerical inputs; arms j ≤ 400)")) +
        (rate > rho - 1e-12 ? "  — this branch attains ρ" : "  — this branch is below ρ"),
      "k = ⌊(n−1)/|b|⌋ = " + wit.k + ", lower bound T_b^k = " + fmtNum(low) + " ≤ π_λ(drawn tree) = " + fmtNum(wv)];
    if (n <= 12) lines.push("M_n(λ) = " + fmtNum(maxPi(n, l).v) + " (exact, all " + treesOf(n).length + " trees)");
    lines.push("upper bound (1+λ) ρ^(n−1) = " + fmtNum(up) + "; ρ ≤ 1 + λ = " + (1 + l).toFixed(4));
    if (Math.abs(l - 1) < 1e-9 && document.getElementById("obB").value === "5") lines.push("at λ = 1, T(A5) = 621/64 = " + T.toFixed(9) + ", so A5 attains ρ(1) = (621/64)^(1/11) = " + rate.toFixed(9));
    document.getElementById("obReadout").innerHTML = lines.join("<br>");
  }
  function initLambdaLabs() {
    var cr = document.getElementById("crL");
    cr.addEventListener("input", crRender);
    document.getElementById("crGold").addEventListener("click", function () { cr.value = 0; crRender(); });
    document.getElementById("crRand").addEventListener("click", function () { CRSEED = Math.floor(Math.random() * 1e9); CRRAND = null; crRender(); });
    crRender();
    document.getElementById("naL").addEventListener("input", naRender);
    document.getElementById("naN").addEventListener("input", naRender);
    naRender();
    var ol = document.getElementById("obL");
    ["obL", "obN"].forEach(function (id) { document.getElementById(id).addEventListener("input", obRender); });
    document.getElementById("obB").addEventListener("change", obRender);
    document.getElementById("obOne").addEventListener("click", function () { ol.value = 100; obRender(); });
    obRender();
  }

  var inited = {};
  function start(p) {
    if (inited[p]) return;
    if (p === "treelab") initTreeLab(); else if (p === "spiderlab") initSpiderLab(); else if (p === "races") initRaces(); else if (p === "ladder") { initLadder(); initLambdaLabs(); } else return;
    inited[p] = true;
  }
  document.addEventListener("bg-show", function (e) { start(e.detail); });
  var act = document.querySelector(".panel.active");   // a deep link may have opened a lab before this ran
  if (act) start(act.id.slice(2));
})();
