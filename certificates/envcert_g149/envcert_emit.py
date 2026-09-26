"""Emit the sharded Lean certificate for 7 <= n <= NMAX (R3Cert/BGEnvCert/G<NMAX>/*.lean) and re-check it.

Usage:  python3 envcert_emit.py NMAX CAPS [OUTROOT]
  e.g.  python3 envcert_emit.py 40 1,2,3,4,5,6,7,8,12,16,22,38

Every emitted number is re-checked here exactly as the Lean kernel will check it (envcert.py mirrors
the definitions of R3Cert/BGEnvCert/Check.lean and Spider.lean); the script refuses to emit a
certificate that fails any check.
"""
import os, sys, time
from fractions import Fraction as Fr
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import envcert as E

HERE = os.path.dirname(os.path.abspath(__file__))
FORMAL = os.path.normpath(os.path.join(HERE, '..', '..', 'formalization'))
CHUNK = 1000   # lanes per hex literal


def pack(tab):
    """row-major lanes (row N, column h) -> one integer, lane i = H*N + h."""
    flat = [int(x) for x in tab.reshape(-1)]
    chunks = []
    for j in range(0, len(flat), CHUNK):
        v = 0
        for i, x in enumerate(flat[j:j + CHUNK]):
            assert 0 <= x < (1 << E.W)
            v |= x << (E.W * i)
        chunks.append(v)
    return chunks, len(flat)


def enc_wit(rows):
    """one level: per g the list of h (byte h+1), terminated by 255."""
    bs = []
    for hs in rows:
        bs += [h + 1 for h in hs] + [255]
    v = 0
    for i, b in enumerate(bs):
        assert 1 <= b <= 255
        v |= b << (8 * i)
    return v


def f64(z, signed):
    if signed:
        z = z + (1 << 63)
    assert 0 <= z < (1 << 64)
    return z


def enc_entries(es, signs):
    """entries of 5 fields x 64 bits; first field stored +1."""
    v = 0
    for j, e in enumerate(es):
        w = 0
        for i, (x, sg) in enumerate(zip(e, signs)):
            if i == 0:
                x = x + 1
            w |= f64(x, sg) << (64 * i)
        v |= w << (320 * j)
    return v


def lean_int(z):
    return str(z) if z >= 0 else f"({z})"


def emit_nat(name, chunks):
    out = []
    for j, c in enumerate(chunks):
        out.append(f"def {name}_{j} : ℕ := 0x{c:x}\n")
    terms = [f"{name}_{j} * 2 ^ {E.W * CHUNK * j}" if j else f"{name}_0" for j in range(len(chunks))]
    out.append(f"def {name} : ℕ :=\n  " + " +\n  ".join(terms) + "\n")
    return "".join(out)


def recheck_shared(tan_used, ld_max, phis, spcodes, spm, nmin, nmax):
    """tanOK1, ldOK, spiderOK exactly."""
    for (g, h) in tan_used:
        u, m, A, N = E.tangent(g, h)
        mu, muh = E.MU[g], E.MU[h]
        nu = (u - mu) / u ** 2
        assert h < E.H and u > 0 and 2 * mu <= u and nu <= muh
        assert E.SCALE * nu <= N and E.logOK(u, m)
        assert E.SCALE * (E.logUB(u, m) + 2 * mu / u - 1 - E.FQ) <= A
    for d in range(2, ld_max + 1):
        m, Ld = E.logd_lo(d)
        assert E.logOK(Fr(d), m) and Ld <= E.SCALE * E.logLB(Fr(d), m)
    for n in range(nmin, nmax + 1):
        cs = spcodes[n]
        assert cs and sum(spsz(c) for c in cs) + 1 == n
        Q = spQ(cs)
        assert E.logOK(Q, spm[n])
        assert phis[n][0] <= E.SCALE * (E.logLB(Q, spm[n]) - (n - 1) * E.FQ)


def code_of(nm):
    if nm == "C":
        return 0
    if nm == "L":
        return 1
    return int(nm[1:]) + 1


def spT(c):
    if c == 0:
        return Fr(3, 2)
    j = c - 1
    return Fr(3, 2) ** j * Fr(4 * j + 3, 3 * j + 3)


def spY(c):
    return Fr(1, 3) if c == 0 else Fr(3, 4 * (c - 1) + 3)


def spsz(c):
    return 2 if c == 0 else 2 * (c - 1) + 1


def spQ(cs):
    Pp = Fr(1)
    for c in cs:
        Pp *= spT(c)
    return Pp * (1 + sum(spY(c) for c in cs) / len(cs))


def main():
    nmax = int(sys.argv[1])
    caps = [int(x) for x in sys.argv[2].split(",")]
    nmin = 7
    outroot = sys.argv[3] if len(sys.argv) > 3 else FORMAL
    tag = f"G{nmax}"
    odir = os.path.join(outroot, "R3Cert", "BGEnvCert", tag)
    os.makedirs(odir, exist_ok=True)
    ns = f"R3Cert.EnvCert.{tag}"
    t0 = time.time()
    sp = E.best_spiders(nmax)
    spcodes = {n: [code_of(x) for x in sp[n][1][0]] for n in range(nmin, nmax + 1)}
    phis = {}
    spm = {}
    for n in range(nmin, nmax + 1):
        Q = spQ(spcodes[n])
        assert Q == E.spider_Q(sp[n][1][0])
        m = E.redm(Q)
        spm[n] = m
        phis[n] = (E.floor_fr(E.SCALE * (E.logLB(Q, m) - (n - 1) * E.FQ)), m)
    Smax = nmax - 1
    R = Smax + 1
    groups = {}
    KMAXCOV = int(os.environ.get('ENVCERT_KMAX', nmax - 1))   # cover root degrees k <= KMAXCOV only
    for k in range(2, min(nmax, KMAXCOV + 1)):
        groups.setdefault(E.cap_of(k, caps), []).append(k)
    tan_used = set()
    capmods = []
    stats = []
    for C in sorted(groups):
        ks = groups[C]
        kmax = max(ks)
        assert kmax <= C + 1 and C + 1 <= 120
        ct = E.CapTables(C, Smax, kmax)
        K, Kx, Rt = E.kernel_tables(ct.Wa, ct.Wn, C, kmax)
        # lane bounds as in Lean
        for c in K:
            assert K[c].max() < 2 * c * E.OFF and Kx[c].max() < 2 * c * E.OFF
        for c in Rt:
            assert Rt[c].max() < 2 * c * E.OFF
        bad = E.bellman_check(ct.Wa, ct.Wn, K, Kx, C, ct.wit_a, ct.wit_n)
        assert bad == 0, f"cap {C}: {bad} Bellman lanes fail"
        # witness lists (sorted) + witOK1 bounds
        witA = [[sorted(ct.wit_a.get((c, g), {0})) for g in range(E.H)] for c in range(1, C + 1)]
        witN = [[sorted(ct.wit_n.get((c, g), {0})) for g in range(E.H)] for c in range(1, C + 1)]
        for c in range(1, C + 1):
            for g in range(E.H):
                for h in witA[c - 1][g] + witN[c - 1][g]:
                    Kc = E.cst_exact(c, g, h)
                    assert Kc <= c * E.OFF and c * E.OFF - Kc + 2 * E.OFF <= 256 * E.OFF
                    tan_used.add((g, h))
        # leaf, data bounds
        for g in range(E.H):
            assert E.SCALE * (E.MU[g] - E.FQ) <= int(ct.Wa[1, g]) - E.OFF
        assert ct.Wa.max() < 2 * E.OFF and ct.Wn.max() < 2 * E.OFF and ct.Wa.min() >= 0 and ct.Wn.min() >= 0
        # roots
        mg = E.root_margins(Rt, ks, nmin, nmax, {n: phis[n] for n in phis})
        roots = []
        for k in ks:
            for n in range(max(nmin, k + 1), nmax + 1):
                margin, g = mg[(n, k)]
                m, Tr = E.troot(k, g)
                t = 1 / (k * E.MU[g])
                assert E.logOK(t, m) and E.SCALE * (E.logUB(t, m) + k * E.MU[g] - 1) <= Tr
                lanev = int(Rt[k][n - 1, g])
                assert lanev + Tr < phis[n][0] + k * E.OFF, (n, k)
                roots.append((n, k, g, Tr, m, margin))
        stats.append((C, ks, len(roots), sum(len(x) for l in witA for x in l) + sum(len(x) for l in witN for x in l),
                      min(r[5] for r in roots) / E.SCALE if roots else None))
        # emit the cap data module
        name = f"cap{C}"
        waC, nl = pack(ct.Wa)
        wnC, _ = pack(ct.Wn)
        assert nl == E.H * R
        with open(os.path.join(odir, f"Cap{C}.lean"), "w") as f:
            f.write(f"/- Generated by proof/verification/finite_cert/envcert_emit.py: cap C = {C}, "
                    f"k = {ks[0]}..{ks[-1]}, rows 0..{Smax}. -/\n")
            f.write("import R3Cert.BGEnvCert.Check\nimport R3Cert.BGEnvCert.Decode\n\n")
            f.write(f"namespace {ns}\nopen R3Cert.EnvCert\n\n")
            f.write(emit_nat(f"{name}Wa", waC))
            f.write(emit_nat(f"{name}Wn", wnC))
            f.write(f"def {name}witA : List (List (List ℕ)) := [\n")
            f.write(",\n".join(f"  decW 0x{enc_wit(row):x}" for row in witA))
            f.write("]\n")
            f.write(f"def {name}witN : List (List (List ℕ)) := [\n")
            f.write(",\n".join(f"  decW 0x{enc_wit(row):x}" for row in witN))
            f.write("]\n")
            f.write(f"def {name}roots : List (ℕ × ℕ × ℕ × ℤ × ℤ) :=\n")
            parts = []
            for k in ks:
                es = [(n, kk, g, Tr, m) for (n, kk, g, Tr, m, _) in roots if kk == k]
                if es:
                    parts.append(f"decRoots 100000 0x{enc_entries(es, (False, False, False, True, True)):x}")
            f.write("  " + " ++\n  ".join(parts) + "\n\n")
            f.write(f"def {name} : CapData where\n  C := {C}\n  R := {R}\n  kmax := {kmax}\n"
                    f"  Wa := {name}Wa\n  Wn := {name}Wn\n  witA := {name}witA\n  witN := {name}witN\n"
                    f"  roots := {name}roots\n\n")
            f.write(f"end {ns}\n")
        capmods.append((C, name))
        print(f"cap {C}: k={ks[0]}..{ks[-1]} roots={len(roots)} witnesses={stats[-1][3]} "
              f"worst margin={stats[-1][4]:.3e}  {time.time() - t0:.1f}s", flush=True)
    Dmax = max(caps) + 1
    recheck_shared(tan_used, Dmax, phis, spcodes, spm, nmin, nmax)
    # shared tables
    with open(os.path.join(odir, "Common.lean"), "w") as f:
        f.write(f"/- Generated by proof/verification/finite_cert/envcert_emit.py (n <= {nmax}). -/\n")
        f.write("import R3Cert.BGEnvCert.Check\nimport R3Cert.BGEnvCert.Decode\n\n")
        f.write(f"namespace {ns}\nopen R3Cert.EnvCert\n\n")
        f.write("def tanTab : TanTab := [\n")
        rows = []
        for g in range(E.H):
            es = []
            for h in sorted(h for (gg, h) in tan_used if gg == g):
                u, m, A, N = E.tangent(g, h)
                assert u.denominator <= E.UDEN and E.UDEN % u.denominator == 0
                es.append((h, u.numerator * (E.UDEN // u.denominator), m, A, N))
            rows.append(f"  decTan 1000 0x{enc_entries(es, (False, False, True, True, True)):x}" if es
                        else "  []")
        f.write(",\n".join(rows) + "]\n\n")
        lds = ["(0, 0)", "(0, 0)"] + [f"({lean_int(E.logd_lo(d)[0])}, {lean_int(E.logd_lo(d)[1])})"
                                      for d in range(2, Dmax + 1)]
        f.write("def ldTab : LdTab := [" + ", ".join(lds) + "]\n\n")
        f.write("def phiTab : PhiTab := [" + ", ".join(lean_int(phis[n][0]) if n in phis else "0"
                                                   for n in range(nmax + 1)) + "]\n\n")
        f.write("def spTab : List (List ℕ) := [" + ", ".join(
            "[" + ", ".join(map(str, spcodes[n])) + "]" if n in spcodes else "[]" for n in range(nmax + 1)) + "]\n\n")
        f.write("def spM : List ℤ := [" + ", ".join(lean_int(spm[n]) if n in spm else "0"
                                                  for n in range(nmax + 1)) + "]\n\n")
        f.write(f"def DMAX : ℕ := {Dmax}\n\n")
        f.write(f"end {ns}\n")
    # fragments
    for C, name in capmods:
        with open(os.path.join(odir, f"Frag{C}.lean"), "w") as f:
            f.write(f"/- Generated: kernel check of cap C = {C}. -/\n")
            f.write(f"import R3Cert.BGEnvCert.{tag}.Common\nimport R3Cert.BGEnvCert.{tag}.Cap{C}\n\n")
            f.write(f"namespace {ns}\nopen R3Cert.EnvCert\n\n")
            f.write(f"set_option maxRecDepth 100000 in\n")
            f.write(f"theorem {name}_ok : capCheck tanTab ldTab phiTab {name} = true := by decide +kernel\n\n")
            f.write(f"end {ns}\n")
    with open(os.path.join(odir, "FragShared.lean"), "w") as f:
        f.write("/- Generated: kernel checks of the shared tables. -/\n")
        f.write(f"import R3Cert.BGEnvCert.{tag}.Common\nimport R3Cert.BGEnvCert.Spider\n"
                f"import R3Cert.BGEnvCert.Assemble\n\n")
        f.write(f"namespace {ns}\nopen R3Cert.EnvCert\n\n")
        f.write("set_option maxRecDepth 100000 in\n")
        f.write("theorem tan_ok : tanOK tanTab 0 HG = true := by decide +kernel\n\n")
        f.write("theorem ld_ok : ldOK ldTab DMAX = true := by decide +kernel\n\n")
        f.write(f"set_option maxRecDepth 100000 in\n")
        f.write(f"theorem spiders_ok : spidersOK phiTab spTab spM {nmin} {nmax} = true := by decide +kernel\n\n")
        f.write(f"end {ns}\n")
    with open(os.path.join(odir, "Main.lean"), "w") as f:
        f.write(f"/-\n  R3Cert.BGEnvCert.{tag}.Main -- the envelope certificate for {nmin} <= n <= {nmax} (generated).\n\n"
                f"  Every tree on n vertices, {nmin} <= n <= {nmax}, either reroots to a spider or has Aobj strictly\n"
                f"  below the certified best spider `spiderT spTab n`.  Kernel-checked (`decide +kernel`, no\n"
                f"  native_decide), no sorry, standard axioms only.\n-/\n")
        f.write(f"import R3Cert.BGEnvCert.{tag}.FragShared\n")
        for C, _ in capmods:
            f.write(f"import R3Cert.BGEnvCert.{tag}.Frag{C}\n")
        f.write(f"\nnamespace {ns}\nopen R3Cert.EnvCert R3Cert.BGSCL R3Cert.RTree R3Cert.Step3 BGMax\n\n")
        f.write("def caps : List CapData := [" + ", ".join(n for _, n in capmods) + "]\n\n")
        f.write("theorem caps_ok : ∀ d ∈ caps, capCheck tanTab ldTab phiTab d = true ∧ d.C + 1 ≤ DMAX := by\n"
                "  intro d hd\n  simp only [caps, List.mem_cons, List.not_mem_nil, or_false] at hd\n"
                "  rcases hd with " + " | ".join("rfl" for _ in capmods) + "\n")
        for C, name in capmods:
            f.write(f"  · exact ⟨{name}_ok, by decide⟩\n")
        f.write(f"\nset_option maxRecDepth 100000 in\n")
        f.write(f"theorem cover_ok : coverOK caps {nmin} {nmax} = true := by decide +kernel\n\n")
        f.write(f"/-- **Finite range {nmin} ≤ n ≤ {nmax}.**  Every tree either reroots to a spider or is strictly\n"
                f"    beaten by the certified spider of the same size. -/\n")
        f.write(f"theorem envcert (t : UTree) (h1 : {nmin} ≤ usize t) (h2 : usize t ≤ {nmax}) :\n"
                f"    usize (spiderT spTab (usize t)) = usize t ∧\n"
                f"      ((∃ cs : List UTree, (∀ c ∈ cs, c = cherryU ∨ ∃ j, c = armU j) ∧ RerootRel t (UTree.node cs)) ∨\n"
                f"        Aobj t < Aobj (spiderT spTab (usize t))) :=\n"
                f"  envcert_utree tanTab ldTab phiTab spTab spM DMAX caps {nmin} {nmax} (by norm_num) tan_ok ld_ok\n"
                f"    caps_ok cover_ok spiders_ok t h1 h2\n\n")
        f.write(f"end {ns}\n")
    print("emitted", odir, f"{time.time() - t0:.1f}s")
    print("tangent pairs used:", len(tan_used))
    for s in stats:
        print("  cap", s[0], "k", s[1][0], "..", s[1][-1], "roots", s[2], "witnesses", s[3], "min margin", s[4])


if __name__ == "__main__":
    main()
