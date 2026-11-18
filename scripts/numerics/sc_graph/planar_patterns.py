#!/usr/bin/env python3
"""The planar contraction patterns of the Lean proof for S+, S- (QED/TwoLoop/UnitSCGraph*.lean),
evaluated on the second-order jets of the planar data, against the 4x4 trace computation of
symbolic_c2.py. NOT a proof.

Planar elements (s, a, b, c) = s + a g0 + b g1 + c g0 g1 with the product, grade involution `bar`,
contractions `gam`, `gamT` and constants g0, g1, g0L of QED/TwoLoop/UnitLGraphTracePlanar.lean.
Jets (x0, x1, x2) as in QED/TwoLoop/UnitLGraphTraceJet.lean (`PJ`). The base pattern is
pw(P; W, Z) = sum_mu tr(P_mu W gamma^mu Z) with planar value
4 (Q0 w g0 z).s + 4 (Q1 w g1 z).s - 8 (R bar(w) z).s for P planar of data (Q0, Q1, R).
Run: nice -n 10 python3 planar_patterns.py
"""
import sympy as sp


class Pl:
    def __init__(self, s, a=0, b=0, c=0):
        self.v = [sp.sympify(s), sp.sympify(a), sp.sympify(b), sp.sympify(c)]

    s = property(lambda self: self.v[0])

    def __add__(self, o):
        return Pl(*[x + y for x, y in zip(self.v, o.v)])

    def __sub__(self, o):
        return Pl(*[x - y for x, y in zip(self.v, o.v)])

    def __neg__(self):
        return Pl(*[-x for x in self.v])

    def sc(self, k):
        return Pl(*[k * x for x in self.v])

    def __mul__(self, o):
        xs, xa, xb, xc = self.v
        ys, ya, yb, yc = o.v
        return Pl(xs * ys + xa * ya - xb * yb + xc * yc,
                  xs * ya + xa * ys + xb * yc - xc * yb,
                  xs * yb + xb * ys + xa * yc - xc * ya,
                  xs * yc + xc * ys + xa * yb - xb * ya)

    def bar(self):
        return Pl(self.v[0], -self.v[1], -self.v[2], self.v[3])

    def gam(self):
        return Pl(-4 * self.v[0], 2 * self.v[1], 2 * self.v[2], 0)

    def gamT(self):
        return Pl(2 * self.v[0], 0, 0, -2 * self.v[3])


ONE, ZERO = Pl(1), Pl(0)
G0, G1, G0L = Pl(0, 1), Pl(0, 0, 1), Pl(0, -1)


class PJ:
    """second-order jet of a planar function of u."""

    def __init__(self, j0, j1=None, j2=None):
        self.j = [j0, j1 or ZERO, j2 or ZERO]

    def __mul__(self, o):
        a, b = self.j, o.j
        return PJ(a[0] * b[0], a[0] * b[1] + a[1] * b[0], a[0] * b[2] + a[1] * b[1] + a[2] * b[0])

    def __add__(self, o):
        return PJ(*[x + y for x, y in zip(self.j, o.j)])

    def sc(self, k):
        return PJ(*[x.sc(k) for x in self.j])

    def bar(self):
        return PJ(*[x.bar() for x in self.j])

    def gam(self):
        return PJ(*[x.gam() for x in self.j])

    def gamT(self):
        return PJ(*[x.gamT() for x in self.j])


def c(x):
    return PJ(x)


# jets of the Lean data at m = 1 (QED/TwoLoop/UnitLGraphTraceJet.lean: qJ0, qJ1, rJ, eJ, wJ)
qJ0 = PJ(ZERO, ZERO, Pl(-16, -16))
qJ1 = PJ(ZERO, ZERO, ZERO)
rJ = PJ(ZERO, Pl(0, 0, 8, 8), Pl(-8, -8))


def eJ(al, be):
    return PJ(Pl(1, al), Pl(0, 0, -2 * be), Pl(0, 2 * be))


class Fam:
    """planar Pauli family data (Q0, Q1, R) as jets."""

    def __init__(self, q0, q1, r):
        self.q0, self.q1, self.r = q0, q1, r

    def contract(self):
        return Fam(self.q0.gam(), self.q1.gam(), self.r.gamT())

    def mulRight(self, y):
        return Fam(self.q0 * y, self.q1 * y, self.r * y.bar())

    def mulLeft(self, y):
        return Fam(y * self.q0, y * self.q1, y * self.r)


P0 = Fam(qJ0, qJ1, rJ)


def pw(F, w, z, k=2):
    t = (F.q0 * w * c(G0) * z).j[k].s * 4 + (F.q1 * w * c(G1) * z).j[k].s * 4 \
        - (F.r * w.bar() * z).j[k].s * 8
    return sp.expand(t)


al = sp.symbols('al0:4'); be = sp.symbols('be0:4')
E = [eJ(al[k], be[k]) for k in range(4)]
I1 = c(ONE)


def Sp_pieces(k=2):
    P1 = P0.contract()
    P2 = P1.contract()
    t1 = 6 * pw(P1, E[0] * E[1].gam() * E[2], E[3], k)
    two = {
        (0, 1): -8 * pw(P1, E[2], E[3], k),
        (0, 2): pw(P1, E[1].gam().gam(), E[3], k),
        (0, 3): pw(P2, E[1].gam() * E[2], I1, k),
        (1, 2): -8 * pw(P1, E[0], E[3], k),
        (1, 3): 2 * pw(P1.mulRight(E[0]).contract(), E[2], I1, k),
        (2, 3): 2 * pw(P1, E[0] * E[1].gam(), I1, k),
    }
    four = {(0, 1, 2, 3): -16 * pw(P1, I1, I1, k), (0, 2, 1, 3): 8 * pw(P1, I1, I1, k),
            (0, 3, 1, 2): -16 * pw(P1, I1, I1, k)}
    return t1, two, four


def Sm_pieces(k=2):
    P1 = P0.contract()
    P2 = P1.contract()
    t1 = 6 * pw(P1, E[0], E[1] * E[2].gam() * E[3], k)
    two = {
        (0, 1): 2 * pw(P1, I1, E[2].gam() * E[3], k),
        (0, 2): 2 * pw(P1.mulLeft(E[3]).contract(), I1, E[1], k),
        (0, 3): pw(P2, I1, E[1] * E[2].gam(), k),
        (1, 2): -8 * pw(P1, E[0], E[3], k),
        (1, 3): pw(P1, E[0], E[2].gam().gam(), k),
        (2, 3): -8 * pw(P1, E[0], E[1], k),
    }
    four = {(0, 1, 2, 3): -16 * pw(P1, I1, I1, k), (0, 2, 1, 3): 8 * pw(P1, I1, I1, k),
            (0, 3, 1, 2): -16 * pw(P1, I1, I1, k)}
    return t1, two, four


def main():
    import symbolic_c2 as S
    for name, pieces in (('Sp', Sp_pieces), ('Sm', Sm_pieces)):
        a2, b2, Cs, t1, t2, t3 = S.coefficients(name)
        p1, p2, p4 = pieces()
        rep = {a2[k]: al[k] for k in range(4)}; rep.update({b2[k]: be[k] for k in range(4)})
        T2 = sum(sp.Symbol(f'C{k}{l}') * v for (k, l), v in p2.items())
        T3 = sum(sp.Symbol(f'C{a}{b}') * sp.Symbol(f'C{cc}{d}') * v / 4
                 for (a, b, cc, d), v in p4.items())
        print(name, 'T1 match:', sp.expand(t1.subs(rep) - p1) == 0,
              ' T2 match:', sp.expand(t2.subs(rep) - T2) == 0,
              ' T3 match:', sp.expand(t3.subs(rep) - T3) == 0)
        for kk in (0, 1):
            q1, q2, q4 = pieces(kk)
            print(name, f'order {kk} vanish:', q1 == 0, all(v == 0 for v in q2.values()),
                  all(v == 0 for v in q4.values()))
        print(name, 'pieces of T1:', sp.factor(p1))
        for kl, v in p2.items():
            print(name, 'piece', kl, ':', sp.factor(v))
        print(name, 'pw(P1;1,1) c2 =', p4[(0, 1, 2, 3)])


if __name__ == '__main__':
    main()
