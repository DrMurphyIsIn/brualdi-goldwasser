"""Formal numbers  c + sum_p a_p log p  (c, a_p rational, p prime) with exact cancellation, and rigorous
interval enclosures (mpmath.iv, outward rounding) for their values."""
from fractions import Fraction as Fr
from sympy import factorint
from mpmath import iv
iv.dps = 60

_logp = {}


def logp_iv(p):
    if p not in _logp:
        _logp[p] = iv.log(iv.mpf(p))
    return _logp[p]


class FL:
    __slots__ = ("c", "a")

    def __init__(self, c=0, a=None):
        self.c = Fr(c)
        self.a = {k: v for k, v in (a or {}).items() if v != 0}

    @staticmethod
    def log(q):
        q = Fr(q)
        assert q > 0
        a = {}
        for p, e in factorint(q.numerator).items():
            a[int(p)] = a.get(int(p), 0) + Fr(int(e))
        for p, e in factorint(q.denominator).items():
            a[int(p)] = a.get(int(p), 0) - Fr(int(e))
        return FL(0, a)

    def __add__(self, o):
        if not isinstance(o, FL):
            return FL(self.c + Fr(o), self.a)
        a = dict(self.a)
        for k, v in o.a.items():
            a[k] = a.get(k, 0) + v
        return FL(self.c + o.c, a)
    __radd__ = __add__

    def __neg__(self):
        return FL(-self.c, {k: -v for k, v in self.a.items()})

    def __sub__(self, o):
        return self + (-o if isinstance(o, FL) else -Fr(o))

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, r):
        assert not isinstance(r, FL)
        r = Fr(r)
        return FL(self.c * r, {k: v * r for k, v in self.a.items()})
    __rmul__ = __mul__

    def __truediv__(self, r):
        return self * (1 / Fr(r))

    def is_zero(self):
        return self.c == 0 and not self.a

    def iv(self):
        x = iv.mpf(self.c.numerator) / self.c.denominator
        for p, v in self.a.items():
            x += (iv.mpf(v.numerator) / v.denominator) * logp_iv(p)
        return x

    def hi(self):
        return self.iv().b

    def lo(self):
        return self.iv().a

    def __repr__(self):
        return "FL(%s + %s)" % (self.c, " + ".join("%s*log%d" % (v, k) for k, v in sorted(self.a.items())))


def ivq(q):
    q = Fr(q)
    return iv.mpf(q.numerator) / q.denominator
