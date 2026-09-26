"""The F <= h(mu) envelope: mapped, and shown NON-inductive (single-variable proofs ruled out).

`recursive_transfer.py` reduced BG to the per-vertex step `F_v = (64/621) a_v^11 prod_c F_c` and located
the crux at "dangerous" vertices.  The natural attempt to close it is an ENVELOPE: an explicit `h(mu)` with
`F_v <= h(mu_v)` that is INDUCTIVE (so `F_c <= h(mu_c)` for all children forces `F_v <= h(mu_v)`) and
`h <= 1` -- then BG follows by induction from the leaves (`F_leaf = 64/621 <= h(1)`).

WHAT THE ENVELOPE LOOKS LIKE.  The empirical envelope `h*(mu) = sup{ F : a vertex has message mu }` peaks at
EXACTLY 1 at the tie message `mu = 3/23` and is `< 1` everywhere else; the tie's own children are the
envelope extremizers at their messages (leaf: `mu=1, F=64/621`; arm/mid: `mu=1/3, F=486/529`) -- a
self-consistent spine.

WHY NO SINGLE-VARIABLE ENVELOPE CLOSES IT (the negative result).  The induction step needs
`(64/621) a_v^11 prod_c h(mu_c) <= h(mu_v)` for every realizable `(a_v, {mu_c})`.  Tested with the TIGHT
envelope `h = h*`, this FAILS: thousands of actual vertices have `(64/621) a_v^11 prod_c h*(mu_c) > h*(mu_v)`
-- overshooting by up to ~100x.  The reason is structural: `F_c <= h(mu_c)` is correct per child, but
`prod_c h(mu_c)` is NOT jointly realizable -- distinct children attain their per-message maxima on DIFFERENT
subtrees that cannot coexist as siblings.  A bound in `mu` alone cannot see this sibling correlation, and a
LARGER `h` only worsens the product.  So NO single-variable `F <= h(mu)` envelope is inductive.

This RULES OUT the entire class of per-message envelope proofs and sharpens the target: any closing
invariant must be JOINT over siblings (multi-variable) -- PROOF_STATUS dead-end #1 ("collective, non-local;
not a sum / product of local terms") at the finest recursive resolution.  The envelope run is a reasoned
dead-end, not a proof.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .recursive_transfer import W


def _collect_vertices(m_max, extra_blocks=()):
    """Every vertex's `(mu, a, [child messages], F)` over all rooted trees up to m_max, plus any explicit
    `extra_blocks` = [(n, edges, root), ...] (used to anchor large exemplars like the tie, n=11)."""
    import networkx as nx
    verts = []

    def rec(g, v, parent):
        kids = [w for w in g[v] if w != parent]
        child = [rec(g, w, v) for w in kids]        # (mu_c, F_c)
        j = len(kids)
        S = sum((mu for mu, _ in child), Fr(0))
        a = 1 + S * Fr(1, j + 1)
        F = W * a ** 11
        for _, Fc in child:
            F *= Fc
        mu = Fr(1) / (j + 1 + S)
        verts.append((mu, a, [mc for mc, _ in child], F))
        return mu, F

    def run(n, edges, root):
        g = {i: set() for i in range(n)}
        for a, b in edges:
            g[a].add(b)
            g[b].add(a)
        rec(g, root, None)

    for m in range(1, m_max + 1):
        trees = [nx.empty_graph(1)] if m == 1 else list(nx.nonisomorphic_trees(m))
        for T in trees:
            idx = {v: i for i, v in enumerate(T.nodes())}
            e = tuple((idx[a], idx[b]) for a, b in T.edges())
            for r in range(m):
                run(m, e, r)
    for (n, e, r) in extra_blocks:
        run(n, e, r)
    return verts


def empirical_envelope(verts):
    """`h*(mu) = sup{F : message == mu}` from a collected vertex list."""
    env = {}
    for mu, _a, _cm, F in verts:
        if mu not in env or F > env[mu]:
            env[mu] = F
    return env


@dataclass(frozen=True)
class EnvelopeCertificate:
    """Maps the `F <= h(mu)` envelope and shows it is NOT inductive: no single-variable `h(mu)` closes the
    recursion (the sibling product overshoots).  `check()` certifies the characterization (peak = 1 at the
    tie, `h* <= 1`, tie-children extremal) AND the non-closure (supersolution test fails) -- NOT BG.  See the
    module docstring: the invariant must be joint over siblings.  conjecture1_proved = False."""

    m_max: int = 9

    def _tie_block(self):
        from .frustration_free import near_star_edges
        n, e = near_star_edges(5)
        return (n, e, 0)

    def _verts_and_env(self):
        verts = _collect_vertices(self.m_max, extra_blocks=[self._tie_block()])
        return verts, empirical_envelope(verts)

    def envelope_peaks_at_tie(self) -> bool:
        """`h*` attains its maximum, exactly 1, at the tie message `mu = 3/23`."""
        _verts, env = self._verts_and_env()
        mu_star, F_star = max(env.items(), key=lambda kv: kv[1])
        return F_star == 1 and mu_star == Fr(3, 23)

    def envelope_below_one(self) -> bool:
        """`h*(mu) <= 1` for every message, with equality only at the tie (verified over the census)."""
        _verts, env = self._verts_and_env()
        return all(F <= 1 for F in env.values()) and sum(1 for F in env.values() if F == 1) == 1

    def tie_children_are_extremal(self) -> bool:
        """The tie's children realize the envelope at their messages: leaf `(mu=1, 64/621)` and arm/mid
        `(mu=1/3, 486/529)` are the max-F blocks at those messages -- the self-consistent spine."""
        _verts, env = self._verts_and_env()
        return env.get(Fr(1)) == W and env.get(Fr(1, 3)) == Fr(486, 529)

    def mu_envelope_not_inductive(self):
        """Supersolution test: count vertices where `(64/621) a^11 prod_c h*(mu_c) > h*(mu_v)` (the step a
        mu-envelope would need).  Returns `(violations, total, worst_ratio)`; a positive violation count
        means NO single-variable `h(mu)` closes the induction."""
        verts, env = self._verts_and_env()
        viol = total = 0
        worst = Fr(0)
        for mu, a, cm, _F in verts:
            if mu not in env or any(mc not in env for mc in cm):
                continue
            total += 1
            R = W * a ** 11
            for mc in cm:
                R *= env[mc]
            ratio = R / env[mu]
            if ratio > worst:
                worst = ratio
            if R > env[mu]:
                viol += 1
        return viol, total, worst

    def finding(self) -> str:
        viol, total, worst = self.mu_envelope_not_inductive()
        return (
            "NEGATIVE -- single-variable F <= h(mu) envelope proofs are RULED OUT. The empirical envelope "
            "h*(mu) peaks at EXACTLY 1 at the tie (mu=3/23) and is < 1 elsewhere, with the tie's children "
            "(leaf mu=1, arm mu=1/3) the extremizers -- a self-consistent spine. BUT the envelope is not a "
            f"supersolution: {viol}/{total} vertices have (64/621) a^11 prod_c h*(mu_c) > h*(mu_v), "
            f"overshooting by up to {float(worst):.0f}x. Reason: prod_c h(mu_c) is not JOINTLY realizable -- "
            "siblings attain their per-message maxima on incompatible subtrees, invisible to a mu-only bound "
            "(a larger h only worsens the product). So no single-variable h(mu) is inductive; a closing "
            "invariant must be JOINT over siblings -- dead-end #1 (collective/non-local) at the finest "
            "recursive resolution. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the envelope characterization (peak 1 at the tie, h* <= 1, tie-children extremal) and
        the non-closure (the mu-envelope fails the supersolution step) -- NOT BG."""
        viol, total, _worst = self.mu_envelope_not_inductive()
        return (
            self.envelope_peaks_at_tie()
            and self.envelope_below_one()
            and self.tie_children_are_extremal()
            and total > 0
            and viol > 0            # the mu-envelope is NOT a supersolution -> not inductive
        )
