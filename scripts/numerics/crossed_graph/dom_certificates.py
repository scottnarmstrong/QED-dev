#!/usr/bin/env python3
"""Certificates for the domination of the crossed-ladder integrand (NOT a proof by itself).

Generates the data of QED/TwoLoop/UnitXCloseBoundData.lean. The merged integrand of
QED/TwoLoop/UnitXGraphReduce.lean is T(mu_a, mu_b) = M [Psi1/(2 U^6 V^2) - Psi2/(2 U^5 V)] with
V >= E = Et/U, so |T| <= |M Psi1|/(2 U^4 Et^2) + |M Psi2|/(2 U^4 Et). On the open simplex
sum z = 1, so each quotient is sum_i z_i * (quotient). For every monomial z^n of M Psi1(M/2)
(d = 2) and M Psi2(M/2) (d = 1) and every index i this script finds natural weights Theta
(on the 8 monomials of U) and Phi (on the 13 monomials of Et), each summing to N, with

    4 sum_j Theta_j U_j[k] + d sum_j Phi_j Et_j[k] <= N (n_k + [k = i]) + S   for all k,

by exact linear programming (two-phase simplex over Fractions, minimizing s = S/N), rounded to
denominator N. The Lean side re-checks every inequality by `decide` and turns it into
z_i z^n / (U^4 Et^d) <= prod_k z_k^(-S/N) by the weighted AM-GM inequality.

Run: nice -n 10 python3 dom_certificates.py [N S] > ../../../QED/TwoLoop/UnitXCloseBoundData.lean   (seconds; default
N = 1000000, S = 990000). The output is the whole module UnitXCloseBoundData.lean: certificates,
term lists, and the Lean proofs of the expansions and of the checks.
"""
import os, sys
from fractions import Fraction as F
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, 'target_check.py')).read()
exec(_src[_src.index('def lean_data'):_src.index("print('1.")])   # lean_data, psi1, psi2, Psi

A, M, c, a, b = sp.symbols('A M c a b', positive=True)
V = (A, M, c, a, b)
U0, P1, P2 = Psi(A, M/2, M, c, a, b)
Et = A**2*(M+b+c) + A*M**2 + 2*A*M*(b+c) + A*c**2 + M**2*(a+b+c) + 2*M*a*c + M*c**2 + a*c**2


def exps(P):
    Pl = sp.Poly(sp.expand(P), *V)
    return list(zip(Pl.monoms(), Pl.coeffs()))


Uex = [m for m, _ in exps(U0)]
Eex = [m for m, _ in exps(Et)]
nU, nE = len(Uex), len(Eex)
# the orders used by UExp, EExp in QED/TwoLoop/UnitXCloseNewton.lean
assert Uex == [(1, 1, 0, 0, 0), (1, 0, 1, 0, 0), (1, 0, 0, 0, 1), (0, 1, 1, 0, 0), (0, 1, 0, 1, 0),
               (0, 1, 0, 0, 1), (0, 0, 1, 1, 0), (0, 0, 0, 1, 1)]
assert Eex == [(2, 1, 0, 0, 0), (2, 0, 1, 0, 0), (2, 0, 0, 0, 1), (1, 2, 0, 0, 0), (1, 1, 1, 0, 0),
               (1, 1, 0, 0, 1), (1, 0, 2, 0, 0), (0, 2, 1, 0, 0), (0, 2, 0, 1, 0), (0, 2, 0, 0, 1),
               (0, 1, 2, 0, 0), (0, 1, 1, 1, 0), (0, 0, 2, 1, 0)]
shiftM = lambda m: tuple(x + (1 if k == 1 else 0) for k, x in enumerate(m))
fam = {'f1': [(shiftM(m), co) for m, co in exps(P1)], 'f2': [(shiftM(m), co) for m, co in exps(P2)]}
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
S = int(sys.argv[2]) if len(sys.argv) > 2 else 990000


def simplex_min(c, A_ub, b_ub, A_eq, b_eq):
    """minimize c.x s.t. A_ub x <= b_ub, A_eq x = b_eq, x >= 0 (two-phase, Bland's rule)."""
    n = len(c); m_ub = len(A_ub)
    rows, rhs = [], []
    for r, (row, bb) in enumerate(zip(A_ub, b_ub)):
        rows.append([F(x) for x in row] + [F(int(k == r)) for k in range(m_ub)]); rhs.append(F(bb))
    for row, bb in zip(A_eq, b_eq):
        rows.append([F(x) for x in row] + [F(0)]*m_ub); rhs.append(F(bb))
    m = len(rows); Nv = n + m_ub
    for r in range(m):
        if rhs[r] < 0:
            rows[r] = [-x for x in rows[r]]; rhs[r] = -rhs[r]
    T = [rows[r] + [F(int(k == r)) for k in range(m)] + [rhs[r]] for r in range(m)]
    basis = [Nv + r for r in range(m)]; tot = Nv + m

    def pivot(pr, pc):
        pv = T[pr][pc]; T[pr] = [x/pv for x in T[pr]]
        for r in range(m):
            if r != pr and T[r][pc] != 0:
                f = T[r][pc]; T[r] = [x - f*y for x, y in zip(T[r], T[pr])]
        basis[pr] = pc

    def run(cost, allowed):
        while True:
            cb = [cost[bb] for bb in basis]; ent = None
            for j in range(tot):
                if allowed(j) and j not in basis and cost[j] - sum(cb[r]*T[r][j] for r in range(m)) < 0:
                    ent = j; break
            if ent is None:
                return True
            pr = None
            for r in range(m):
                if T[r][ent] > 0:
                    q = T[r][-1]/T[r][ent]
                    if pr is None or q < T[pr][-1]/T[pr][ent] or (q == T[pr][-1]/T[pr][ent] and basis[r] < basis[pr]):
                        pr = r
            if pr is None:
                return False
            pivot(pr, ent)
    run([F(0)]*Nv + [F(1)]*m, lambda j: True)
    if any(basis[r] >= Nv and T[r][-1] != 0 for r in range(m)):
        return None
    for r in range(m):
        if basis[r] >= Nv:
            for j in range(Nv):
                if T[r][j] != 0:
                    pivot(r, j); break
    if not run([F(x) for x in c] + [F(0)]*m_ub + [F(0)]*m, lambda j: j < Nv):
        return None
    x = [F(0)]*Nv
    for r in range(m):
        if basis[r] < Nv:
            x[basis[r]] = T[r][-1]
    return sum(F(ci)*xi for ci, xi in zip(c, x[:n])), x[:n]


def lp(n, i, d):
    Aub = [[4*Uex[j][k] for j in range(nU)] + [d*Eex[j][k] for j in range(nE)] + [-1] for k in range(5)]
    bub = [n[k] + int(k == i) - 5 for k in range(5)]            # variable s' = s + 5 >= 0
    Aeq = [[1]*nU + [0]*nE + [0], [0]*nU + [1]*nE + [0]]
    val, x = simplex_min([0]*(nU+nE) + [1], Aub, bub, Aeq, [1, 1])
    return val - 5, x[:nU], x[nU:nU+nE]


def check(Th, Ph, n, i, d):
    return sum(Th) == N and sum(Ph) == N and all(
        4*sum(Th[j]*Uex[j][k] for j in range(nU)) + d*sum(Ph[j]*Eex[j][k] for j in range(nE))
        <= N*(n[k] + int(k == i)) + S for k in range(5))


def round_w(w):
    raw = [F(x)*N for x in w]; fl = [int(x) for x in raw]
    for j in sorted(range(len(w)), key=lambda j: -(raw[j] - fl[j]))[:N - sum(fl)]:
        fl[j] += 1
    return fl


certs, out, worst = [], {}, F(0)
for name, d in (('f1', 2), ('f2', 1)):
    terms = []
    for n, co in fam[name]:
        ks = []
        for i in range(5):
            hit = next((ci for ci, (Th, Ph) in enumerate(certs) if check(Th, Ph, n, i, d)), None)
            if hit is None:
                v, th, ph = lp(n, i, d); worst = max(worst, v)
                Th, Ph = round_w(th), round_w(ph)
                assert check(Th, Ph, n, i, d), (name, n, i, v)
                certs.append((Th, Ph)); hit = len(certs) - 1
            ks.append(hit)
        terms.append((co, n, ks))
    out[name] = terms
print(f'-- {len(certs)} certificates; largest LP optimum s* = {worst}; s = {S}/{N}', file=sys.stderr)
# sanity: the term lists reproduce M Psi1(M/2), M Psi2(M/2)
for name, P in (('f1', P1), ('f2', P2)):
    rec = sum(co*sp.prod([v**k for v, k in zip(V, n)]) for co, n, ks in out[name])
    assert sp.expand(rec - M*P) == 0


def vec(v): return '![' + ', '.join(str(x) for x in v) + ']'


def q(co):
    co = sp.Rational(co)
    return f'({co.p} : ℚ)' if co.q == 1 else f'({co.p}/{co.q} : ℚ)'


def mono(n):
    f = [f'{v} ^ {k}' if k > 1 else v for v, k in zip(['A', 'M', 'c', 'a', 'b'], n) if k > 0]
    return ' * '.join(f) if f else '1'


def coef(co):
    co = sp.Rational(co)
    return f'({co.p})' if co.q == 1 else f'({co.p} / {co.q})'


def wrap(items, first, indent, sep=', '):
    """join items after `first`, breaking lines at 100 characters"""
    out, line = [], first
    for k, it in enumerate(items):
        piece = it + (sep.rstrip() if k < len(items) - 1 else '')
        if len(line) + len(piece) + 1 > 100 and line.strip():
            out.append(line.rstrip()); line = indent
        line += piece + ' '
    out.append(line.rstrip())
    return '\n'.join(out)


HDR = f"""/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseCert
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Data for the domination of the crossed-ladder integrand

Generated by `scripts/numerics/crossed_graph/dom_certificates.py` (exact linear programming over
the rationals): the expansions of `M Ψ₁(M/2)` and `M Ψ₂(M/2)` into monomials of the group sums
`(z_A, z_M, z_c, z_a, z_b)` (`domTerms₁`, `domTerms₂`, in chunks of {30} terms), and for each
monomial and each index `i` a certificate `(Θ, Φ)` of the Newton-polytope bound
(`domCerts`, {len(certs)} certificates), with `N = {N}`, `S = {S}` (`s = S/N`; the largest
linear-programming optimum is `{worst}`).

* `domTerms₁_ok`, `domTerms₂_ok`: every certificate passes the check `termOK` (by kernel `decide`);
* `mul_gPsi1_eq`, `mul_gPsi2_eq`: the expansions (by `ring`, chunk by chunk).
-/

@[expose] public section

namespace QED.TwoLoop.UnitXClose

open QED.TwoLoop.UnitXGraph

/-- The denominator `N` of the certificate weights. -/
def domN : ℕ := {N}

/-- The numerator `S` of the exponent `s = S/N < 1`. -/
def domS : ℕ := {S}
"""
lines = [HDR, f'/-- The certificates `(Θ, Φ)` (weights with sum `{N}`). -/', 'def domCerts : List Cert := [',
         ',\n'.join(f'  ({vec(Th)},\n    {vec(Ph)})' for Th, Ph in certs), ']\n']
CH = 30
lemmas = []
nch = {}
for name, lname, doc, tag in (('f1', 'domTerms₁', '`M Ψ₁(M/2)`', '₁'), ('f2', 'domTerms₂', '`M Ψ₂(M/2)`', '₂')):
    ts = out[name]; names = []
    for ci, k in enumerate(range(0, len(ts), CH)):
        ch = ts[k:k+CH]; cn = f'domChunk{tag}_{ci}'; names.append(cn)
        lines += [f'/-- Terms {k}–{k+len(ch)-1} of {doc} with their certificates. -/', f'def {cn} : List Term := [',
                  ',\n'.join(f'  ({q(co)}, {vec(n)}, {vec(ks)})' for co, n, ks in ch), ']\n']
        poly = ' +\n      '.join(f'{coef(co)} * ({mono(n)})' for co, n, ks in ch)
        lemmas.append(f"""theorem evalTerms_{cn} (A M c a b : ℝ) :
    evalTerms {cn} (gz A M c a b) =
      {poly} := by
  simp only [evalTerms, {cn}, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Fin.prod_univ_five, gz, Matrix.cons_val]
  push_cast
  ring
""")
    nch[tag] = len(names)
    lines += [f'/-- The terms of {doc} with their certificates. -/',
              wrap([nm for nm in names], f'def {lname} : List Term := ', '    ', sep=' ++ ') + '\n']
lines += lemmas


def expansion(tag, P, psi, sym):
    simps = ['List.append_assoc'] + ['evalTerms_append']*(nch[tag]-1) + [f'evalTerms_domChunk{tag}_{k}' for k in range(nch[tag])]
    return f"""/-- **The expansion of `M {sym}(M/2)`.** -/
theorem mul_g{P}_eq (A M c a b : ℝ) :
    M * g{P} A (M / 2) M c a b = evalTerms domTerms{tag} (gz A M c a b) := by
{wrap(simps, f'  simp only [domTerms{tag}, ', '    ')}]
  simp only [g{P}, {psi}, gXan, gXbn, gXU, Matrix.cons_val]
  ring
"""


lines += [f"""/-- Every term of `M Ψ₁(M/2)` passes the certificate check (`d = 2`). -/
theorem domTerms₁_ok : domTerms₁.all (termOK domN domS 2 domCerts) = true := by decide +kernel

/-- Every term of `M Ψ₂(M/2)` passes the certificate check (`d = 1`). -/
theorem domTerms₂_ok : domTerms₂.all (termOK domN domS 1 domCerts) = true := by decide +kernel
""", expansion('₁', 'Psi1', 'psiT1h', 'Ψ₁'), expansion('₂', 'Psi2', 'psiT2h', 'Ψ₂'),
          'end QED.TwoLoop.UnitXClose\n\nend']
print('\n'.join(lines))
