#!/usr/bin/env python3
"""Low-dimensional integral representations of the q-type two-loop units. NOT a proof.

Companion of docs/TWO-LOOP-UNITS.md. Starting point: the covariant Feynman-parametric
integrand of scripts/numerics/two_loop_units.py (section 11 of docs/TWO-LOOP-DERIVATION.md),
whose numerator patterns are imported from that script. The integrand is rebuilt here in
exact rational arithmetic (sympy), written in the hierarchical Cheng-Wu variables of
docs/TWO-LOOP-UNITS.md, section 2, and integrated analytically over the outer electron
parameter b. The remaining integrals are evaluated with mpmath and compared with
Barbieri-Mignaco-Remiddi I, p. 852, and with the finite-regulator values of
docs/TWO-LOOP-DERIVATION.md, section 11.

Modes (each runs in ONE process; run niced):
  nice -n 10 python3 scripts/numerics/two_loop_unit_integrals.py ladder      # ~2 min
  nice -n 10 python3 scripts/numerics/two_loop_unit_integrals.py selfenergy  # ~6 min
  nice -n 10 python3 scripts/numerics/two_loop_unit_integrals.py corner      # ~20 min (--level 8)
  nice -n 10 python3 scripts/numerics/two_loop_unit_integrals.py crossed     # ~5 min (levels 8, 16)
  nice -n 10 python3 scripts/numerics/two_loop_unit_integrals.py crossedexact  # ~2 min (section 4.5)
  nice -n 10 python3 scripts/numerics/two_loop_unit_integrals.py cornerexact   # ~20 s (section 6.6)
  nice -n 10 python3 scripts/numerics/two_loop_unit_integrals.py exact       # seconds
  nice -n 10 python3 scripts/numerics/two_loop_unit_integrals.py all
Options: --dps N (base working precision of the 2D/3D integrals; extra digits are added
         automatically near edges and removable singularities), --level K (inverse step of
         the outer tanh-sinh rules; doubling K roughly squares the error, and costs 4x),
         --skip-finite (skip the finite-photon-mass cross-checks).
Memory stays below 0.5 GB. Requires numpy, sympy, mpmath (run with numpy 2.5.3,
sympy 1.14.0, mpmath 1.3.0).

Units (coefficient of r^2 = (alpha/pi)^2 in F_2 at q -> 0; photon mass lambda on every
photon line, Pauli-Villars photon Lambda -> infinity, m = 1):
  L   = ladder + delta_1 F2^(2)                     -> 11/48 + zeta(2)/3
  X   = crossed ladder                              -> 1/6 - 5 zeta(2) ln 2 + 13/6 zeta(2) + 5/4 zeta(3)
  S   = S+ + S- + (delta_2, delta_m) insertions     =  ln(lambda) + b_S + o(1)
  C   = C+ + C- + 2 delta_1 F2^(2)                  = -ln(lambda) + b_C + o(1)
  S+C -> -7/3 + 2 zeta(2) ln 2 - zeta(3)/2
"""
import argparse, math, os, sys, time
import mpmath as mp
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

def targets():
    with mp.workdps(60):
        return _targets()


def _targets():
    z2, z3, l2 = mp.zeta(2), mp.zeta(3), mp.log(2)
    return dict(L=mp.mpf(11)/48 + z2/3,
                X=mp.mpf(1)/6 - 5*z2*l2 + mp.mpf(13)/6*z2 + mp.mpf(5)/4*z3,
                S=mp.mpf(11)/24 - z2/3,
                C=-mp.mpf(67)/24 + 2*z2*l2 + z2/3 - z3/2,
                SC=-mp.mpf(7)/3 + 2*z2*l2 - z3/2)


# ====================================================================== exact parametric engine
_PATS = {}


def patterns(name):
    """numerator patterns (exact rationals) of two_loop_units.py for graph `name`."""
    if name not in _PATS:
        import two_loop_units as T
        from fractions import Fraction
        g = T.graph(name)
        _PATS[name] = dict(lines=g.lines, slots=g.slots, groups=g.groups, pref=g.pref.real,
                           pats=[(p, c, Fraction(v).limit_denominator(10000)) for p, c, v in g.pats])
        for (p, c, v), (p2, c2, v2) in zip(_PATS[name]['pats'], g.pats):
            assert abs(float(v) - v2) < 1e-10
    return _PATS[name]


def integrand_parts(name, Z, L=2):
    """Exact version of two_loop_units.Graph.integrand: returns (A, U, D0) with
    integrand = sum_e A[e] * D^(-e), D = D0 + sum_i z_i m_i^2 (D0: massless part, m = 1)."""
    g = patterns(name)
    lines, slots, groups, pats = g['lines'], g['slots'], g['groups'], g['pats']
    N = len(lines)
    z = [None]*N; w = sp.Integer(1)
    for gi, grp in enumerate(groups):
        for l in grp:
            z[l] = Z[gi]/len(grp)
        w *= Z[gi]**(len(grp)-1)/sp.factorial(len(grp)-1)
    xi = [l['xi'] for l in lines]
    al = [sp.nsimplify(l['a']) for l in lines]; be = [sp.nsimplify(l['b']) for l in lines]
    U = sp.Matrix(L, L, lambda s, t: sum(z[i]*xi[i][s]*xi[i][t] for i in range(N)))
    det = sp.expand(U.det()); Ui = U.adjugate()/det
    jp = sp.Matrix([sum(z[i]*xi[i][s]*al[i] for i in range(N)) for s in range(L)])
    jq = sp.Matrix([sum(z[i]*xi[i][s]*be[i] for i in range(N)) for s in range(L)])
    Uijp, Uijq = Ui*jp, Ui*jq
    a = [al[i] - sum(xi[i][s]*Uijp[s] for s in range(L)) for i in range(N)]
    bq = [be[i] - sum(xi[i][s]*Uijq[s] for s in range(L)) for i in range(N)]
    C = [[sum(xi[i][s]*Ui[s, t]*xi[j][t] for s in range(L) for t in range(L)) for j in range(N)]
         for i in range(N)]
    D0 = ((jp.T*Uijp)[0] - sum(z[i]*al[i]**2 for i in range(N))
          + sum(z[i] for i in range(N) if lines[i]['k'] == 'e'))
    line = {k: s[1] for k, s in enumerate(slots) if s[0] == 'm'}
    cst = {k: sp.nsimplify(s[2]) for k, s in enumerate(slots) if s[0] == 'm'}
    Pk = {}
    for pairs, choice, val in pats:
        term = sp.Rational(val.numerator, val.denominator)
        for k, c in choice.items():
            term *= (a[line[k]] if c == 'P' else bq[line[k]] if c == 'Q' else cst[k])
        for (i, j) in pairs:
            term *= -C[line[i]][line[j]]
        Pk[len(pairs)] = Pk.get(len(pairs), 0) + term
    pref = sp.nsimplify(g['pref'])
    A = {}
    for kk, val in Pk.items():
        e = N - 2*L - kk
        assert e > 0
        A[e] = A.get(e, 0) + pref*sp.gamma(e)/2**kk*val*w/det**2
    return A, det, D0


# ====================================================================== b-integration masters
bS, MS, hS, betaS, AS = sp.symbols('b M h beta A', positive=True)
_MAST = {}


def master(j, n):
    """regularized int_beta^oo b^j (M + b h)^(-n) db, the ln(A) divergence (present only
    for j - n = -1, coefficient h^-n) removed. Returns (value, ln-coefficient)."""
    if (j, n) in _MAST:
        return _MAST[(j, n)]
    F = sp.integrate(sp.apart(bS**j/(MS + bS*hS)**n, bS), bS)
    c = hS**(-n) if j - n == -1 else sp.Integer(0)

    def fixlog(arg):
        arg = sp.factor(arg)
        if arg.has(AS):
            d = sp.degree(sp.numer(arg), AS) - sp.degree(sp.denom(arg), AS)
            return d*sp.log(AS) + sp.log(sp.simplify(arg/AS**d))
        return sp.log(arg)
    FA = sp.expand(sp.expand_log(F.subs(bS, AS), force=True).replace(sp.log, fixlog))
    val = sp.limit(FA - c*sp.log(AS), AS, sp.oo) - F.subs(bS, betaS)
    _MAST[(j, n)] = (sp.expand_log(sp.simplify(val), force=True), c)
    return _MAST[(j, n)]


def laurent(expr, var):
    num, den = sp.fraction(sp.together(expr))
    den = sp.factor(den); k = sp.degree(den, var); cst = sp.simplify(den/var**k)
    assert sp.diff(cst, var) == 0, den
    P = sp.Poly(sp.expand(num), var)
    return {m[0]-k: c/cst for m, c in zip(P.monoms(), P.coeffs())}


def b_integral(A2, A1, var):
    """E = int_beta^oo [A2/(M+b h)^2 + A1/(M+b h)] db (ln A removed), ln-coefficient, and the
    large-M constant e0 with E(M) = -logc ln M + e0 + o(1)."""
    E, logc = 0, 0
    lt2, lt1 = laurent(A2, var), laurent(A1, var)
    for n, lt in ((2, lt2), (1, lt1)):
        for j, c in lt.items():
            v, lc = master(j, n); E += c*v; logc += c*lc
    c12 = lt2.get(1, 0)
    e0 = logc*sp.log(hS) - c12/hS**2
    return E, sp.simplify(logc), e0


# ====================================================================== ladder (section 3)
def ladder_f(Y, a, za, ma, mb):
    """hierarchical ladder integrand (Cheng-Wu: z_B = Y, z_b = 1-Y; a = z_A + Y(1-Y))."""
    c = Y*(1-Y); U = a + za
    D = Y**2 + (1-Y)*mb + a**2/U + ma*za
    Q0 = (3*Y-2)*a**2 + (4*Y-Y**2-2)*a*za - 2*c*za**2
    return Y*za*(a-c)/(2*U**4)*((9*c+a)/D + Q0/(U*D**2))


def ladder_K(Y):
    L1, LY = mp.log1p(-Y), mp.log(Y)
    return ((Y**3+3*Y**2-2*Y-2)*L1/(12*Y**2) + (-7*Y**3+11*Y**2+Y-6)*LY/(12*(1-Y)**2)
            - (23*Y**3-41*Y**2+16*Y+4)/(24*Y*(1-Y)))


def ladder_finite(lam):
    """L unit at photon mass lam (Lambda = infinity): eq. (3.4) of the document."""
    l2 = mp.mpf(lam)**2
    f2 = mp.quad(lambda x: x**2*(1-x)/(x**2+(1-x)*l2), [0, lam, 1])

    def inner(Y):
        c = Y*(1-Y); M0 = Y**2 + (1-Y)*l2

        def gx(x):
            h = (x**2 + (1-x)*l2)/x; z = (1-x)/x
            q0 = (3*Y-2) + (4*Y-Y**2-2)*z - 2*c*z**2
            Q = c*(8*M0 + 9*c*h - x*q0)
            return Y*x*(1-x)/2*(x*q0/(M0*h) - 9*c/M0 - mp.log(M0+c*h)/h
                                + Q/M0**2*mp.log(1+M0/(c*h)))
        return (mp.quad(gx, [0, lam, mp.sqrt(lam), 1])
                - f2*(Y*(Y**2+2*Y-2)/(2*M0) - Y/2*mp.log(M0)))
    return mp.quad(inner, [0, lam, mp.sqrt(lam), 1])


def run_ladder(args):
    T = targets()
    print('== ladder unit L')
    # (a) the hand-written hierarchical integrand equals the engine integrand
    Y, a, za, ma, mb = sp.symbols('Y a z_a m_a m_b', positive=True)
    A, U, D0 = integrand_parts('L', [a - Y*(1-Y), Y, za, 1-Y])
    D = D0 + ma*za + mb*(1-Y)
    eng = sum(Ae*D**(-e) for e, Ae in A.items())
    pt = {Y: sp.Rational(3, 10), a: sp.Rational(7, 5), za: sp.Rational(2, 3),
          ma: sp.Rational(1, 7), mb: sp.Rational(2, 9)}
    print('  engine vs eq. (3.1) at a rational point:',
          sp.N(eng.subs(pt), 20), sp.N(ladder_f(*[pt[s] for s in (Y, a, za, ma, mb)]), 20))
    # (b) finite photon mass, Lambda = infinity, against section 11.4 (Lambda = 1000)
    if not args.skip_finite:
        mp.mp.dps = 20
        for lam, ref in ((1e-2, '0.671404 (Lambda=1000)'), (1e-4, '0.774975 (Lambda=1000)')):
            print(f'  L(lambda={lam:g}) = {mp.nstr(ladder_finite(lam), 12)}   section 11.4: {ref}')
    # (c) the limit, 1D representation
    mp.mp.dps = 40
    v = mp.mpf(1)/6 + mp.quad(ladder_K, [0, mp.mpf(1)/2, 1])
    print('  L = 1/6 + int_0^1 K_L =', mp.nstr(v, 35))
    print('  BMR 11/48 + zeta(2)/3  =', mp.nstr(T['L'], 35), '  difference', mp.nstr(v - T['L'], 3))


# ====================================================================== self-energy (section 5)
def selfenergy_parts():
    Y, a, x = sp.symbols('Y a x', positive=True)
    c = Y*(1-Y)
    A, U, D0 = integrand_parts('S+', [a - c, Y, a*(1-x)/x, 1-Y])
    assert sp.simplify(D0 - (Y**2 + a**2/U)) == 0
    A2 = sp.factor(sp.together(A[2]*a/x**2)).subs(a, bS)
    A1 = sp.factor(sp.together(A[1]*a/x**2)).subs(a, bS)
    A2h = x**2*(x-1)*(Y**2-Y+bS)**2*(Y*x-Y-x+3)/(4*bS)
    A1h = -x*(x-1)*(Y**2-Y+bS)**2*(2*Y*x+Y-2*x+2)/(2*bS**2)
    assert sp.simplify(A2 - A2h) == 0 and sp.simplify(A1 - A1h) == 0
    E, logc, e0 = b_integral(A2h, A1h, bS)
    return Y, x, E, logc, e0


def ct_k(mu):
    return mp.quad(lambda t: t**2*(t-1)*(-4*mu*t**2+2*mu*t+2*mu+3*t**3+3*t**2)
                   / (2*(t**2+(1-t)*mu)**2), [0, mp.sqrt(mu), 1])


def ct_m(mu):
    return mp.quad(lambda t: -t**2*(t-1)*(-3*mu*t+3*mu+2*t**2)/(2*(t**2+(1-t)*mu)**2),
                   [0, mp.sqrt(mu), 1])


def selfenergy_KS(Y):
    return ((1-Y)*(3*Y**2+2*Y+1)*mp.log1p(-Y)/(12*Y**2) + (3*Y**2-3*Y+2)/(24*Y)
            + Y*(9*Y-8)*mp.log(Y)/(12*(1-Y)))


def run_selfenergy(args):
    T = targets()
    print('== self-energy unit S')
    Y, x, E, logc, e0 = selfenergy_parts()
    print('  engine integrand = eq. (5.1): checked')
    if not args.skip_finite:
        mp.mp.dps = 25
        fE = sp.lambdify((Y, x, MS, hS), (E - e0).subs(betaS, Y*(1-Y)), 'mpmath')
        lam = mp.mpf('0.01'); l2 = lam**2
        Vk, Vm = ct_k(l2), ct_m(l2)

        def SY(y):
            D = y**2 + (1-y)*l2
            two = mp.quad(lambda xx: fE(y, xx, D, (xx**2+(1-xx)*l2)/xx), [0, lam, 0.5, 1])
            d2 = (1-y)*mp.log(D)/2 + (1+y)*y*(1-y)/D
            sig = -(1-(1-y)/2)*mp.log(D)
            return two + d2*Vk + (d2-sig)*Vm
        v = 2*mp.quad(SY, [0, lam, 0.5, 1])
        print(f'  S(lambda=0.01) = {mp.nstr(v, 10)}   section 11.3: -4.579348 (Lambda=1000)')
        print(f'  S - ln(lambda) = {mp.nstr(v - mp.log(lam), 10)}   (limit b_S = {mp.nstr(T["S"], 10)};'
              ' the difference is O(lambda ln lambda))')
    # lambda-free two-loop part: check the closed-form x-integral at a point
    G0 = sp.expand_log((E - e0).subs({MS: Y**2, betaS: Y*(1-Y)}).subs(hS, x), force=True)
    g0 = sp.lambdify((Y, x), G0, 'mpmath')
    mp.mp.dps = 30
    y = mp.mpf('0.37')
    print('  int_0^1 G_S(0.37,x) dx =', mp.nstr(mp.quad(lambda xx: g0(y, xx), [0, 1]), 20),
          '  K_S(0.37) =', mp.nstr(selfenergy_KS(y), 20))
    mp.mp.dps = 40
    v = 2*mp.quad(selfenergy_KS, [0, mp.mpf(1)/2, 1])
    print('  b_S = 2 int_0^1 K_S =', mp.nstr(v, 35))
    print('  BMR 11/24 - zeta(2)/3 =', mp.nstr(T['S'], 35), '  difference', mp.nstr(v - T['S'], 3))
    return v


# ====================================================================== corner (section 6)
def corner_parts():
    y3, y4, b, x = sp.symbols('y3 y4 b x', positive=True)
    yb = 1 - y3 - y4
    A, U, D0 = integrand_parts('C+', [b - y3*yb, y3, y4, b*(1-x)/x - y3*y4, yb])
    assert sp.simplify(D0 - ((y3+y4)**2 + b**2/U)) == 0
    A2 = sp.factor(sp.together(A[2]*b/x**2)); A1 = sp.factor(sp.together(A[1]*b/x**2))
    g = y3*yb
    p1 = (2*x**3*y3**2 - 2*x**3*y3 - 6*x**2*y3**2 - 4*x**2*y3*y4 + 6*x**2*y3 + 2*x**2*y4 - x**2
          + 6*x*y3**2 + 8*x*y3*y4 - 6*x*y3 + 2*x*y4**2 - 6*x*y4 - 2*y3**2 - 4*y3*y4 + 4*y3
          - 2*y4**2 + 4*y4)
    p2 = (8*x**2*y3**2 - 8*x**2*y3 - 10*x*y3**2 - 4*x*y3*y4 + 2*x*y3 - 2*x*y4 + 5*x + 2*y3**2
          + 4*y3 - 2*y4**2 + 4*y4 - 4)
    A2h = x*(b-g)*(p1*b + x*(2-x)*(1-2*y3)*g)/(4*b**2)
    A1h = -x*(b-g)*(2*(x-1)*b**2 + p2*b - 3*x*(1-2*y3)*g)/(4*b**3)
    assert sp.simplify(A2 - A2h) == 0 and sp.simplify(A1 - A1h) == 0
    E, logc, e0 = b_integral(A2h.subs(b, bS), A1h.subs(b, bS), bS)
    return y3, y4, x, E, logc, e0


def de_nodes(h, T=3.4):
    """tanh-sinh nodes on (0,1): (u, 1-u, weight), both u and 1-u accurate."""
    out, k = [], -int(T/h)
    while k*h <= T:
        t = k*h; s = mp.pi/2*mp.sinh(t)
        out.append((1/(1+mp.exp(-2*s)), 1/(1+mp.exp(2*s)),
                    h*mp.pi/2*mp.cosh(t)/(2*mp.cosh(s)**2))); k += 1
    return out


def bumped(m, extra_per_decade=6):
    """extra working digits for an evaluation at distance m from an edge of the simplex or
    from a removable singularity (the integrands lose about 4-5 digits per decade there)."""
    m = max(m, mp.mpf(10)**-80)
    return int(extra_per_decade*max(0, -mp.log10(m))) + 10


def run_corner(args):
    T = targets()
    print('== corner unit C')
    y3, y4, x, E, logc, e0 = corner_parts()
    print('  engine integrand = eq. (6.2): checked')
    Y = y3 + y4
    if not args.skip_finite:
        # finite photon mass, Lambda = infinity, eq. (6.3): a quick double-precision
        # Gauss-Legendre product rule (accurate to about 1e-5 here)
        import numpy as np
        l2s = sp.Symbol('l2', positive=True)
        Mp = Y**2 + (1-Y)*l2s - l2s*y3*y4
        hx = (x**2 + (1-x)*l2s)/x
        f = sp.lambdify((y3, y4, x, betaS, l2s), sp.expand_log((E - e0).subs(MS, Mp).subs(hS, hx),
                        force=True), 'numpy')

        def rule(n, k=3):
            t, w = np.polynomial.legendre.leggauss(n); uu = (t+1)/2; w = w/2
            p_, q_ = uu**k, (1-uu)**k
            return p_/(p_+q_), w*k*(uu**(k-1)*q_ + p_*(1-uu)**(k-1))/(p_+q_)**2
        lam = 0.01; l2 = lam**2
        t, wt = rule(48); tx, wx = rule(64)
        F2 = float(np.sum(wx*tx**2*(1-tx)/(tx**2+(1-tx)*l2)))
        tot = 0.0
        with np.errstate(all='ignore'):
            for Yv, wa in zip(t, wt):
                for s_, ws in zip(t, wt):
                    a3, a4 = Yv*s_, Yv*(1-s_); gv, ev = a3*(1-Yv), a3*a4; xs = gv/(gv+ev); val = 0.0
                    for lo, hi, mode in ((0, xs, 0), (xs, 1, 1)):
                        X = lo + (hi-lo)*tx; W = (hi-lo)*wx
                        B = gv*np.ones_like(X) if mode == 0 else ev*X/((1-xs)*(1-tx))
                        vv = W*f(a3, a4, X, B, l2); val += np.sum(vv[np.isfinite(vv)])
                    Mi = Yv**2 + (1-Yv)*l2
                    tot += wa*ws*Yv*(val - F2*((Yv**2+2*Yv-2)/(2*Mi) - 0.5*math.log(Mi)))
        print(f'  C(lambda=0.01) = {2*tot:.6f}   section 11.3: 3.926720 (Lambda=1000)')
    mp.mp.dps = args.dps
    G1 = sp.expand_log((E - e0).subs(MS, Y**2).subs(hS, x).subs(betaS, y3*(1-Y)), force=True)
    G2 = sp.expand_log((E - e0).subs(MS, Y**2).subs(hS, x).subs(betaS, y3*y4*x/(1-x)), force=True)
    f1 = sp.lambdify((y3, y4, x), G1, 'mpmath'); f2 = sp.lambdify((y3, y4, x), G2, 'mpmath')
    xn = de_nodes(mp.mpf(1)/16)

    def xint(a3, a4, Yv, Ym):
        # fixed tanh-sinh rule in x on [0, x*] and [x*, 1]; an exact zero division can occur
        # only at a node rounded onto an edge, whose weight is negligible
        gv, ev = a3*Ym, a3*a4; xs = gv/(gv+ev); tot = 0
        for u, um, w in xn:
            with mp.workdps(mp.mp.dps + bumped(min(a3, a4, Ym, xs*u, (1-xs)*um, abs(a3-a4)))):
                try:
                    tot += w*xs*f1(a3, a4, xs*u)
                except ZeroDivisionError:
                    pass
                try:
                    tot += w*(1-xs)*f2(a3, a4, 1-(1-xs)*um)
                except ZeroDivisionError:
                    pass
        return tot
    t0 = time.time()
    N = de_nodes(mp.mpf(1)/args.level)
    two = 0
    for Yv, Ym, wy in N:           # y3 = Y s; s in (0,1/2) and (1/2,1) (split at y3 = y4)
        sub = 0
        for u, um, wu in N:
            v = Yv*u/2
            sub += wu*(xint(v, Yv - v, Yv, Ym) + xint(Yv - v, v, Yv, Ym))/2
        two += wy*Yv*sub
    bC = 2*two - mp.mpf(3)/2
    print(f'  b_C = 2 int G_C - 3/2 = {mp.nstr(bC, 25)}   ({time.time()-t0:.0f} s)')
    print('  BMR row c) finite part =', mp.nstr(T['C'], 25), '  difference', mp.nstr(bC - T['C'], 3))
    return bC


# ====================================================================== crossed (section 4)
def crossed_Phi():
    """2D integrand Phi(z2, z3) of eq. (4.4), built from the engine (w- then b-integration)."""
    z2, z3, b, w, t, u, v = sp.symbols('z2 z3 b w t u v', positive=True)
    zb = 1 - z2 - z3; Y = z2 + z3; e = z2*z3; g = z2*zb
    A, U, D0 = integrand_parts('X', [b - z2*zb, z2, z3, w - z2*z3, zb])
    assert sp.simplify(D0 - (Y**2 + b**2/U)) == 0
    f = sp.together(A[2]*U**2/(Y**2*U + b**2)**2 + A[1]*U/(Y**2*U + b**2))
    num, den = sp.fraction(f)
    assert sp.expand(den - 4*U**4*(Y**2*U + b**2)**2) == 0
    J = sp.log(u/v)/(u - v)

    def K(p, q):
        if p <= 0:
            return sum(sp.binomial(-p, k)*(u-v)**(-p-k)/((q-k-1)*v**(q-k-1)) for k in range(-p+1))
        return (-1)**(p+q-2)/(sp.factorial(p-1)*sp.factorial(q-1))*sp.diff(J, u, p-1, v, q-1)
    numt = sp.Poly(sp.expand(num.subs(w, t + e)), t)
    res = 0
    for (j,), cf in zip(numt.monoms(), numt.coeffs()):
        res += cf*sum(sp.binomial(j, i)*(-u)**(j-i)*K(4-i, 2) for i in range(j+1))
    res = (res/(4*Y**4)).subs({u: b + e, v: b + e + b**2/Y**2})
    Ls = sp.Symbol('Ls')
    r2 = sp.expand(res.xreplace({l: Ls for l in res.atoms(sp.log)}))
    R1, R0 = sp.factor(sp.together(r2.coeff(Ls, 1))), sp.factor(sp.together(r2.coeff(Ls, 0)))

    def pfrac(numr, factors):
        out = {}
        for d, m in factors:
            rest = sp.Integer(1)
            for d2, m2 in factors:
                if d2 is not d:
                    rest *= (b + d2)**m2
            s = sp.Symbol('s')
            ser = sp.series((numr/rest).subs(b, s - d), s, 0, m).removeO()
            for k in range(1, m+1):
                out[(d, k)] = sp.factor(sp.together(ser.coeff(s, m - k)))
        return out
    n1, d1 = sp.fraction(R1); n0, d0 = sp.fraction(R0)
    pf1 = pfrac(sp.expand(n1/4), [(sp.Integer(0), 5)])
    pf0 = pfrac(sp.expand(n0/(4*Y)), [(sp.Integer(0), 3), (e, 3), (Y*z2, 1), (Y*z3, 1)])

    def int_rat(pf):
        r = 0
        for (d, k), c in pf.items():
            r += -c*sp.log(g + d) if k == 1 else c*(g + d)**(1-k)/(k-1)
        return r

    def int_log(pf, cs):
        r = 0
        for (d, k), c in pf.items():
            Dd = g + d
            for si, Ci in cs:
                Cc = g + Ci
                if k == 1:
                    r += c*si*(-sp.log(Dd)**2/2 - sp.polylog(2, 1 - Cc/Dd))
                else:
                    m = k - 1
                    if sp.simplify(Cc - Dd) == 0:
                        Kv = 1/(m*Dd**m)
                    else:
                        uu, vv = sp.symbols('u_ v_', positive=True)
                        Jj = sp.log(uu/vv)/(uu - vv)
                        Kv = ((-1)**(m-1)/sp.factorial(m-1)*sp.diff(Jj, vv, m-1)).subs({uu: Cc, vv: Dd})
                    r += c*si*(sp.log(Cc)*Dd**(1-k)/(k-1) + Kv/(k-1))
        return r
    Phi = (int_rat(pf0) + 2*sp.log(Y)*int_rat(pf1)
           + int_log(pf1, [(1, e), (-1, Y*z2), (-1, Y*z3)]))
    return z2, z3, Phi


def run_crossed(args):
    T = targets()
    print('== crossed-ladder unit X')
    t0 = time.time()
    z2, z3, Phi = crossed_Phi()
    zbs = sp.Symbol('zb', positive=True)
    fA = sp.lambdify((z2, z3), Phi, 'mpmath')
    fB = sp.lambdify((z2, zbs), Phi.subs(z3, 1 - z2 - zbs), 'mpmath')
    print(f'  Phi built ({time.time()-t0:.0f} s); Phi(0.2,0.3) =',
          mp.nstr(fA(mp.mpf('0.2'), mp.mpf('0.3')), 15))
    mp.mp.dps = args.dps
    # variables Y = z2 + z3, xi = z2/Y; the removable singular line z2 = z3 is xi = 1/2
    for lev in (args.level, 2*args.level):
        t0 = time.time(); N = de_nodes(mp.mpf(1)/lev); v = 0
        for Y, Ym, wy in N:
            sub = 0
            for u, um, wu in N:
                for xi, xim in ((u/2, 1 - u/2), (1 - u/2, u/2)):
                    a2, a3 = Y*xi, Y*xim
                    with mp.workdps(mp.mp.dps + bumped(min(a2, a3, Ym, um/2))):
                        sub += wu/2*(fA(a2, a3) if Y < 0.5 else fB(a2, Ym))
            v += wy*Y*sub
        print(f'  X = int Phi = {mp.nstr(v, 22)}   (tanh-sinh step 1/{lev}, {time.time()-t0:.0f} s)')
    print('  BMR row e)  =', mp.nstr(T['X'], 22), '  difference', mp.nstr(v - T['X'], 3))


# ====================================================================== crossed: exact evaluation (section 4.5)
# Weight functions of the 1D kernel, as symbols (derivative rules in _CX_DERIV):
#   L = Li2(Y), D = Li2(1-2Y) - Li2(2Y-1), a = ln Y, b = ln(1-Y), z2 = zeta(2) = pi^2/6.
_CX_Y = sp.Symbol('Y', positive=True)
_CX_L, _CX_D, _CX_a, _CX_b, _CX_z2 = sp.symbols('L D a b z2')


def _cx_kernel_doc():
    """K_X(Y) of eq. (4.7), as written in docs/TWO-LOOP-UNITS.md (partial fractions)."""
    Y, L, D, a, b, z2 = _CX_Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2
    R = sp.Rational
    rho = R(5, 6)/(Y-1) - R(3, 4)/(Y-1)**2 - R(8, 3)/(Y-1)**3 - 1/(Y-1)**4
    kL = -R(5, 2)*Y - R(5, 4) + 2*rho + R(5, 6)/Y - R(7, 12)/Y**2
    kD = -R(7, 6)*Y - R(11, 12) + rho + R(5, 6)/Y - R(1, 12)/Y**2
    kaa = Y/12 - R(7, 24) + rho/2
    kab = -R(4, 3)*Y - R(1, 3) + R(5, 6)/Y - R(7, 12)/Y**2
    ka = (-R(11, 12)*Y - R(5, 4) - R(1, 8)/(2*Y-1) + R(11, 12)/(Y-1) - R(2, 3)/(Y-1)**2
          - 1/(Y-1)**3 - R(5, 12)/Y)
    kb = (R(11, 12)*Y - R(13, 12) + R(1, 8)/(2*Y-1) - R(2, 3)/(Y-1) - 1/(Y-1)**2 + R(7, 6)/Y
          - R(1, 24)/Y**2)
    kz = R(23, 12)*Y + R(19, 24) - rho/2 - R(5, 4)/Y + R(1, 8)/Y**2
    k1 = -R(17, 12)*Y + R(1, 24) + R(2, 3)/(Y-1) + 1/(Y-1)**2 + R(3, 8)/Y
    return kL*L + kD*D + kaa*a**2 + kab*a*b + ka*a + kb*b + kz*z2 + k1


def _cx_boundary_doc():
    """the boundary function G(Y) of eq. (4.8)."""
    Y, L, D, a, b, z2 = _CX_Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2
    R = sp.Rational
    gL = -R(5, 4)*Y**2 - R(5, 4)*Y + R(3, 2)/(Y-1) + R(8, 3)/(Y-1)**2 + R(2, 3)/(Y-1)**3 + R(7, 12)/Y
    gD = -R(7, 12)*Y**2 - R(11, 12)*Y + R(3, 4)/(Y-1) + R(4, 3)/(Y-1)**2 + R(1, 3)/(Y-1)**3 + R(1, 12)/Y
    gaa = Y**2/24 - R(7, 24)*Y + R(3, 8)/(Y-1) + R(2, 3)/(Y-1)**2 + R(1, 6)/(Y-1)**3 - R(1, 8)
    gab = -R(2, 3)*Y**2 - R(1, 3)*Y + R(7, 12)/Y
    ga = -R(11, 24)*Y**2 - R(7, 8)*Y + R(1, 3)/(Y-1) + R(1, 3)/(Y-1)**2 + R(5, 12)
    gb = R(11, 24)*Y**2 - R(19, 24)*Y + R(1, 3)/(Y-1) + R(1, 24)/Y + R(23, 24)
    g1 = -z2*(R(2, 3)/(Y-1)**2 + R(1, 6)/(Y-1)**3 + R(3, 8)/(Y-1) + R(1, 8)/Y) - R(1, 3)/(Y-1)
    # (the constant shifts -1/8 a^2, +5/12 a, +23/24 b absorb the divergent simple-pole pieces)
    return gL*L + gD*D + gaa*a**2 + gab*a*b + ga*a + gb*b + g1


def _cx_masters_doc():
    """K_m(Y) of eq. (4.9): polynomial + convergent simple-pole terms."""
    Y, L, D, a, b, z2 = _CX_Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2
    R = sp.Rational
    return (R(5, 6)*((L + a*b)/Y + (D - R(3, 2)*z2)/Y + 2*(L - z2)/(Y-1) + (D + R(3, 2)*z2)/(Y-1))
            + R(5, 12)*a**2/(Y-1) + R(5, 12)*a/(Y-1) + R(11, 6)*b/Y + R(4, 3)*(a - b)/(2*Y-1))


_CX_DERIV = {_CX_L: -_CX_b/_CX_Y, _CX_D: 2*(_CX_a - _CX_b)/(1 - 2*_CX_Y),
             _CX_a: 1/_CX_Y, _CX_b: -1/(1 - _CX_Y), _CX_z2: 0}


def _cx_ddY(expr):
    """total Y-derivative of an expression in Y and the weight symbols."""
    out = sp.diff(expr, _CX_Y)
    for s, ds in _CX_DERIV.items():
        out += sp.diff(expr, s)*ds
    return out


def _cx_coeffs(expr):
    """coefficients of expr (polynomial in L, D, a, b, z2) as cancelled rational functions of Y."""
    P = sp.Poly(sp.expand(expr), _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2)
    return {m: sp.cancel(c) for m, c in zip(P.monoms(), P.coeffs())}


def _cx_is_zero(expr):
    return all(c == 0 for c in _cx_coeffs(expr).values())


def crossed_letters():
    """Phi_X in the variables Y = z2 + z3, xi = z2/Y, as R_1 + sum_l R_l ln(letter_l).
    Returns ({'1'|letter: coefficient}, Phi in z-variables)."""
    z2, z3, Phi = crossed_Phi()
    assert not Phi.atoms(sp.polylog), 'Phi_X contains a dilogarithm'
    Y, xi = _CX_Y, sp.Symbol('xi', positive=True)
    letters = {'Y': Y, 'xi': xi, '1-Y*xi': 1 - Y*xi, 'xi+Y-2*Y*xi': xi + Y - 2*Y*xi, '1-Y': 1 - Y}
    Ls = {k: sp.Symbol('ln_' + k) for k in letters}
    pt = {Y: sp.Rational(3, 10), xi: sp.Rational(1, 5)}

    def logmap(arg):
        num, den = sp.fraction(sp.factor(sp.together(arg)))
        res, const = 0, sp.Integer(1)
        for part, sgn in ((num, 1), (den, -1)):
            c0, fl = sp.factor_list(part)
            const *= c0**sgn
            for f, mult in fl:
                sg = sp.sign(f.subs(pt)); f = sp.expand(sg*f); const *= sg**(mult*sgn)
                key = [k for k, v in letters.items() if sp.expand(f - v) == 0]
                assert len(key) == 1, f
                res += sgn*mult*Ls[key[0]]
        assert const > 0
        return res + sp.log(const)
    P = Phi.subs({z2: Y*xi, z3: Y*(1 - xi)})
    P = P.xreplace({l: logmap(l.args[0]) for l in P.atoms(sp.log)})
    out = {}
    for k, s in Ls.items():
        out[k] = sp.cancel(sp.together(sp.diff(P, s)))
    out['1'] = sp.cancel(sp.together(P.xreplace({s: 0 for s in Ls.values()})))
    return xi, out, (z2, z3, Phi)


def crossed_xi_integral(xi, co):
    """K(Y) = int_0^1 Y Phi(Y, xi) dxi in closed form (finite parts at xi = 0, 1; the 1/(2 xi - 1)
    pole of the ln xi and ln(xi+Y-2Y xi) coefficients is integrated as one regular term).
    Returns K in the weight symbols and the dictionary of divergent parts (all must vanish)."""
    Y = _CX_Y
    Li2 = lambda z: sp.polylog(2, z)
    # letter data ln(al + be t): t = xi near xi = 0, t = 1 - xi near xi = 1
    ab0 = {'1-Y*xi': (sp.Integer(1), -Y), 'xi+Y-2*Y*xi': (Y, 1 - 2*Y)}
    ab1 = {'1-Y*xi': (1 - Y, Y), 'xi+Y-2*Y*xi': (1 - Y, -(1 - 2*Y)), 'xi': (sp.Integer(1), sp.Integer(-1))}
    zeta2 = sp.pi**2/6

    def tc(al, be, m):
        return sp.log(al) if m == 0 else -(-be/al)**m/m

    def conv(al, be, k):   # int_0^1 t^-k [ln(al + be t) - Taylor_{k-1}] dt
        if sp.simplify(al + be) == 0:
            return -zeta2 if k == 1 else -sp.harmonic(k-1)/(k-1)
        if k == 1:
            return -Li2(-be/al)
        R1 = sp.log(al + be) - sum(tc(al, be, m) for m in range(k))
        return R1/(1 - k) + (-be/al)**(k-1)*sp.log(1 + be/al)/(k - 1)

    def fp_log(al, be, k):
        fp = conv(al, be, k) + sum(tc(al, be, m)/(m - k + 1) for m in range(k - 1))
        div = {('log',): -tc(al, be, k - 1)}
        for m in range(k - 1):
            div[('pow', m - k + 1)] = -tc(al, be, m)/(m - k + 1)
        return fp, div

    def fp_rat(k):
        return (0, {('log',): -1}) if k == 1 else (sp.Rational(1, 1 - k), {('pow', 1 - k): -sp.Rational(1, 1 - k)})

    def fp_lnt(k):
        n = -k
        if n == -1:
            return 0, {('log2',): -sp.Rational(1, 2)}
        return -sp.Rational(1, (n+1)**2), {('powlog', n+1): -sp.Rational(1, n+1), ('pow', n+1): sp.Rational(1, (n+1)**2)}

    def poly_log(al, be, n):   # int_0^1 t^n ln(al + be t) dt
        I = (sum((-al)**j/(be**(j+1)*(n - j + 1)) for j in range(n + 1))
             + (-al/be)**(n+1)/be*sp.log((al + be)/al))
        return sp.log(al + be)/(n + 1) - be/(n + 1)*I
    assert co['1-Y'] == 0
    rx = sp.cancel(sp.limit(co['xi']*(2*xi - 1), xi, sp.Rational(1, 2)))
    rB = sp.cancel(sp.limit(co['xi+Y-2*Y*xi']*(2*xi - 1), xi, sp.Rational(1, 2)))
    assert sp.cancel(rx + rB) == 0
    pieces = {'Y': co['Y'], 'xi': sp.cancel(co['xi'] - rx/(2*xi - 1)), '1-Y*xi': co['1-Y*xi'],
              'xi+Y-2*Y*xi': sp.cancel(co['xi+Y-2*Y*xi'] - rB/(2*xi - 1)), '1': co['1']}
    # int_0^1 (ln xi - ln(xi+Y-2Y xi))/(2 xi - 1) dxi = (pi^2/4 - Li2(1-2Y) + Li2(2Y-1))/2
    K = Y*rx*(sp.pi**2/4 - Li2(1 - 2*Y) + Li2(2*Y - 1))/2
    div = {}
    for L, coef in pieces.items():
        fac = sp.log(Y) if L == 'Y' else 1
        for term in sp.Add.make_args(sp.apart(sp.cancel(Y*coef), xi)):
            A, rest = term.as_independent(xi, as_Add=False)
            A2, rest = sp.factor(rest).as_independent(xi, as_Add=False)
            A = A*A2*fac
            if rest == 1:
                n, kind = 0, 'xi'
            elif rest == xi or (rest.is_Pow and rest.base == xi):
                n, kind = (1 if rest == xi else int(rest.exp)), 'xi'
            elif sp.expand(rest - (xi - 1)) == 0:
                n, kind = 1, 'one'
            elif rest.is_Pow and sp.expand(rest.base - (xi - 1)) == 0:
                n, kind = int(rest.exp), 'one'
            else:
                raise ValueError(term)
            if kind == 'one':
                A = A*sp.Integer(-1)**n      # (xi - 1)^n = (-1)^n t^n, t = 1 - xi
            free = L in ('1', 'Y')
            if n >= 0:
                if free:
                    K += A/(n + 1)
                elif kind == 'xi':
                    K += -A/sp.Integer((n + 1)**2) if L == 'xi' else A*poly_log(*ab0[L], n)
                else:
                    K += -A*sp.harmonic(n + 1)/(n + 1) if L == 'xi' else A*poly_log(*ab1[L], n)
                continue
            k = -n
            if free:
                fp, d = fp_rat(k)
            elif kind == 'xi':
                fp, d = fp_lnt(k) if L == 'xi' else fp_log(*ab0[L], k)
            else:
                fp, d = fp_log(*ab1[L], k)
            K += A*fp
            for kk, v in d.items():
                div[(kind,) + kk] = div.get((kind,) + kk, 0) + A*v
    return K, {k: sp.simplify(v) for k, v in div.items()}


def crossed_canonical(K):
    """rewrite K in the weight symbols, using (4.6): Li2 arguments -> Li2(Y), D; logs -> ln Y, ln(1-Y)."""
    Y, L, D, a, b, z2 = _CX_Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2
    Pp, Mm = sp.symbols('Pp Mm')     # Li2(1-2Y), Li2(2Y-1); D = Pp - Mm
    rep = {}
    for p in K.atoms(sp.polylog):
        arg = p.args[1]
        table = [(Y, L), (1 - 2*Y, Pp), (2*Y - 1, Mm),
                 ((1 - 2*Y)/(1 - Y), Pp - Mm + L - b**2/2 + a*b - z2/2),
                 ((2*Y - 1)/Y, -Pp + Mm - L - a**2/2 + z2/2),
                 (-Y/(1 - Y), -L - b**2/2)]
        hit = [v for u, v in table if sp.simplify(arg - u) == 0]
        assert len(hit) == 1, p
        rep[p] = hit[0]
    lrep = {}
    for l in K.atoms(sp.log):
        arg = l.args[0]
        table = [(Y, a), (1 - Y, b), (1/(1 - Y), -b), ((1 - Y)/Y, b - a), (Y/(1 - Y), a - b)]
        hit = [v for u, v in table if sp.simplify(arg - u) == 0]
        assert len(hit) == 1, l
        lrep[l] = hit[0]
    K2 = sp.expand(K.xreplace(rep).xreplace(lrep).subs(sp.pi, sp.sqrt(6*z2)))
    Pc = sp.Poly(K2, L, Pp, Mm, a, b, z2)
    cf = {m: sp.cancel(c) for m, c in zip(Pc.monoms(), Pc.coeffs())}
    # D enters only as Pp - Mm
    cP = cf.pop((0, 1, 0, 0, 0, 0), 0); cM = cf.pop((0, 0, 1, 0, 0, 0), 0)
    assert sp.cancel(cP + cM) == 0
    out = cP*D
    for (eL, eP, eM, ea, eb, ez), c in cf.items():
        assert eP == 0 and eM == 0
        out += c*L**eL*a**ea*b**eb*z2**ez
    return out


def _cx_numeric(expr):
    """mpmath function of Y from an expression in the weight symbols."""
    Y = _CX_Y
    f = sp.lambdify((Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2), expr, 'mpmath')

    def g(y):
        return f(y, mp.polylog(2, y), mp.polylog(2, 1 - 2*y) - mp.polylog(2, 2*y - 1),
                 mp.log(y), mp.log1p(-y), mp.zeta(2))
    return g


def _cx_series_limit(expr, end, order=7):
    """exact limit of expr (in the weight symbols) at Y -> 0+ (end=0) or 1- (end=1); returns
    (limit, divergent remainder), using the expansions of L, D, a, b at the endpoint."""
    e, l = sp.symbols('eps ell')        # ell = ln(eps)
    z2 = _CX_z2
    t = sp.Symbol('t')
    log1m = lambda x: -sum(x**k/sp.Integer(k) for k in range(1, order + 1))
    Li2s = lambda x: sum(x**k/sp.Integer(k)**2 for k in range(1, order + 1))
    geo = sum((2*t)**m for m in range(order + 1))
    pl, pr = sp.expand(2*geo), sp.expand(-2*geo*log1m(t))

    def D0(x, lx):   # D(x) = 3 z2/2 + int_0^x 2 (ln u - ln(1-u))/(1-2u) du
        r = sp.Rational(3, 2)*z2
        for k in range(order + 1):
            r += pl.coeff(t, k)*x**(k+1)*(lx/(k+1) - sp.Rational(1, (k+1)**2)) + pr.coeff(t, k)*x**(k+1)/(k+1)
        return r
    if end == 0:
        sub = {_CX_a: l, _CX_b: log1m(e), _CX_L: Li2s(e), _CX_D: D0(e, l)}
        Yv = e
    else:
        sub = {_CX_a: log1m(e), _CX_b: l, _CX_L: z2 - l*log1m(e) - Li2s(e), _CX_D: -D0(e, l)}
        Yv = 1 - e
    tot = 0
    for mono, c in _cx_coeffs(expr).items():
        cs = sp.series(c.subs(_CX_Y, Yv), e, 0, order - 1).removeO()
        term = cs*sp.Mul(*[s**k for s, k in zip((_CX_L, _CX_D, _CX_a, _CX_b, _CX_z2), mono)])
        tot += sp.expand(term.xreplace(sub))
    tot = sp.expand(tot)
    lim = tot.coeff(e, 0).subs(l, 0)
    div = sp.expand(sum(tot.coeff(e, -k) for k in range(1, order + 2)) + (tot.coeff(e, 0) - lim))
    return sp.expand(lim), div


def run_crossedexact(args):
    T = targets()
    Y, L, D, a, b, z2 = _CX_Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2
    print('== crossed-ladder unit X: exact evaluation (section 4.5)')
    t0 = time.time()
    # step 1: Phi_X has no dilogarithm; letters
    xi, co, (z2s, z3s, Phi) = crossed_letters()
    print(f'  step 1: Phi_X = R_1 + sum R_l ln(l), letters Y, xi, 1-Y xi, xi+Y-2Y xi; no Li2 ({time.time()-t0:.0f} s)')
    for k, v in co.items():
        print(f'    denominator of the {k:12s} coefficient: {sp.factor(sp.fraction(v)[1])}')
    # step 2: xi-integration
    K, div = crossed_xi_integral(xi, co)
    assert all(v == 0 for v in div.values()), div
    print(f'  step 2: xi-integral in closed form; all {len(div)} endpoint divergences cancel')
    Kc = crossed_canonical(K)
    print('  step 3: canonical form (identities (4.6)) equals eq. (4.7):', _cx_is_zero(Kc - _cx_kernel_doc()))
    # numerical checks of (4.6)
    mp.mp.dps = 40
    worst = 0
    for y in (mp.mpf(1)/7, mp.mpf(1)/2 + mp.mpf(1)/11, mp.mpf(9)/10):
        Dv = mp.polylog(2, 1-2*y) - mp.polylog(2, 2*y-1); Lv = mp.polylog(2, y); A, B = mp.log(y), mp.log1p(-y)
        worst = max(worst,
                    abs(mp.polylog(2, (1-2*y)/(1-y)) - (Dv + Lv - B**2/2 + A*B - mp.zeta(2)/2)),
                    abs(mp.polylog(2, (2*y-1)/y) - (-Dv - Lv - A**2/2 + mp.zeta(2)/2)),
                    abs(mp.polylog(2, -y/(1-y)) - (-Lv - B**2/2)))
    print('    identities (4.6) at three points: max deviation', mp.nstr(worst, 3))
    # step 2 check: K(Y) against direct xi-quadrature of Y Phi
    fP = sp.lambdify((z2s, z3s), Phi, 'mpmath'); fK = _cx_numeric(_cx_kernel_doc())
    mp.mp.dps = args.dps
    xn = de_nodes(mp.mpf(1)/args.level)
    for y in (mp.mpf('0.3'), mp.mpf('0.7')):
        v = 0
        for u, um, w in xn:      # xi in (0,1/2) and (1/2,1), xi = u/2 and 1 - u/2
            for x_, xm in ((u/2, 1 - u/2), (1 - u/2, u/2)):
                with mp.workdps(mp.mp.dps + bumped(min(x_, xm, um/2))):
                    v += w/2*y*fP(y*x_, y*xm)
        with mp.workdps(mp.mp.dps + 20):
            kv = fK(y)
        print(f'    K({mp.nstr(y, 2)}): xi-quadrature {mp.nstr(v, 22)}  eq. (4.7) {mp.nstr(kv, 22)}  diff {mp.nstr(v - kv, 3)}')
    # step 3 check: int_0^1 K = X
    mp.mp.dps = 35

    def Kh(y):
        if y <= 0 or y >= 1:
            return mp.mpf(0)
        with mp.workdps(int(5*max(0, -mp.log10(min(y, 1 - y)))) + 80):
            return fK(y)
    v = mp.quad(Kh, [0, 0.1, 0.2, 0.45, 0.52, 0.8, 0.95, 1])
    print('    int_0^1 K_X =', mp.nstr(v, 32), '  BMR', mp.nstr(T['X'], 32), '  diff', mp.nstr(v - T['X'], 3))
    # step 4: K = G' + K_m exactly
    G, Km = _cx_boundary_doc(), _cx_masters_doc()
    Ppoly = sp.cancel(sp.expand(_cx_kernel_doc() - _cx_ddY(G) - Km))
    cf = _cx_coeffs(Ppoly)
    assert set(cf) <= {(0, 0, 0, 0, 0), (0, 0, 0, 0, 1)}, cf
    print('  step 4: K_X - G\' - K_m =', sp.factor(Ppoly), '(a polynomial: it is p(Y) of eq. (4.9))')
    pint = sp.integrate(Ppoly, (Y, 0, 1))
    g0, d0 = _cx_series_limit(G, 0); g1, d1 = _cx_series_limit(G, 1)
    print(f'    G(0+) = {g0},  G(1-) = {g1}  (divergent parts: {d0}, {d1})')
    with mp.workdps(60):
        fG = _cx_numeric(G)
        e_ = mp.mpf(10)**-12
        print('    numerically G(1e-12) =', mp.nstr(fG(e_), 12), ' G(1-1e-12) =', mp.nstr(fG(1 - e_), 12))
    # step 5: masters
    mp.mp.dps = 40
    Z2, Z3, LN2 = mp.zeta(2), mp.zeta(3), mp.log(2)
    Dn = lambda y: mp.polylog(2, 1-2*y) - mp.polylog(2, 2*y-1)
    q = lambda f, pts=(0, 0.5, 1): mp.quad(f, list(pts))
    masters = [
        ('M1  int Li2(Y)/Y', q(lambda y: mp.polylog(2, y)/y), Z3, 'Lean: integral_Li₂_div'),
        ('M2  int ln Y ln(1-Y)/Y', q(lambda y: mp.log(y)*mp.log1p(-y)/y), Z3, 'Lean: integral_log_mul_log_one_sub_div'),
        ('M3  int (D - 3z2/2)/Y', q(lambda y: (Dn(y) - 3*Z2/2)/y, (0, 0.25, 0.5, 1)), -3*Z2*LN2 - 7*Z3/4, 'Lean: UnitX; route (4.11)'),
        ('M3\' int (D + 3z2/2)/(Y-1)', q(lambda y: (Dn(y) + 3*Z2/2)/(y-1), (0, 0.5, 0.75, 1)), -3*Z2*LN2 - 7*Z3/4, 'Lean: UnitX; = M3 (Y -> 1-Y)'),
        ('M4  int (Li2(Y) - z2)/(Y-1)', q(lambda y: (mp.polylog(2, y) - Z2)/(y-1)), 2*Z3, 'Lean: UnitX; = -A1'),
        ('M5  int ln^2 Y/(Y-1)', q(lambda y: mp.log(y)**2/(y-1)), -2*Z3, 'Lean: UnitX; = -J1'),
        ('M6  int ln Y/(Y-1)', q(lambda y: mp.log(y)/(y-1)), Z2, 'Lean: UnitX'),
        ('M7  int ln(1-Y)/Y', q(lambda y: mp.log1p(-y)/y), -Z2, 'Lean: ExtraIntegrals, UnitLS'),
        ('M8  int (ln Y - ln(1-Y))/(2Y-1)', q(lambda y: (mp.log(y) - mp.log1p(-y))/(2*y-1), (0, 0.3, 0.7, 1)), 3*Z2/2, 'Lean: UnitX'),
    ]
    print('  step 5: master integrals over (0,1) (40 digits)')
    for nm, val, ref, src in masters:
        print(f'    {nm:30s} {mp.nstr(val, 30):>34s}  diff {mp.nstr(val - ref, 3):>9s}   [{src}]')
    # the derivation of M3 from classical integrals (section 4.5.4)
    xq = lambda f: mp.quad(f, [0, 1])
    chain = [
        ('J1  int ln^2(1-x)/x = 2 z3', xq(lambda x: mp.log1p(-x)**2/x), 2*Z3),
        ('J2  int ln(1-x) ln(1+x)/x = -5/8 z3', xq(lambda x: mp.log1p(-x)*mp.log1p(x)/x), -5*Z3/8),
        ('J3  int ln^2(1+x)/x = z3/4', xq(lambda x: mp.log1p(x)**2/x), Z3/4),
        ('A1  int (Li2(x) - z2)/(1-x) = -2 z3', xq(lambda x: (mp.polylog(2, x) - Z2)/(1-x)), -2*Z3),
        ('A2  int (Li2(-x) + z2/2)/(1-x) = 5/8 z3', xq(lambda x: (mp.polylog(2, -x) + Z2/2)/(1-x)), 5*Z3/8),
        ('A3  int Li2(x)/(1+x) = z2 ln2 - 5/8 z3', xq(lambda x: mp.polylog(2, x)/(1+x)), Z2*LN2 - 5*Z3/8),
        ('A4  int Li2(-x)/(1+x) = z3/4 - z2 ln2/2', xq(lambda x: mp.polylog(2, -x)/(1+x)), Z3/4 - Z2*LN2/2),
    ]
    for nm, val, ref in chain:
        print(f'    {nm:42s} {mp.nstr(val, 30):>34s}  diff {mp.nstr(val - ref, 3)}')
    A = {nm[:2]: val for nm, val, ref in chain}
    m3n = masters[2][1]
    print('    (4.11): (A1 - A2) - A3 + A4 - 3/2 z2 ln2 - M3 =',
          mp.nstr(A['A1'] - A['A2'] - A['A3'] + A['A4'] - 3*Z2*LN2/2 - m3n, 3))
    # step 6: assembly
    z3, M3 = sp.symbols('z3 M3')
    sp_int = (sp.Rational(5, 6)*(z3 + z3 + M3 + 2*2*z3 + M3) + sp.Rational(5, 12)*(-2*z3)
              + sp.Rational(5, 12)*z2 + sp.Rational(11, 6)*(-z2) + sp.Rational(4, 3)*sp.Rational(3, 2)*z2)
    total = sp.expand(g1 - g0 + pint + sp_int)
    print('  step 6: X = G(1-) - G(0+) + int p + int (simple-pole part) =', total)
    final = sp.expand(total.subs(M3, -3*z2*sp.log(2) - sp.Rational(7, 4)*z3))
    print('          with M3 = -3 z2 ln2 - 7/4 z3:  X =', final)
    with mp.workdps(40):
        fv = sp.N(final.subs({z2: sp.pi**2/6, z3: sp.zeta(3)}), 40)
        print('          =', mp.nstr(mp.mpf(str(fv)), 30), '  BMR', mp.nstr(T['X'], 30), '  diff',
              mp.nstr(mp.mpf(str(fv)) - T['X'], 3))


# ====================================================================== corner: exact evaluation (section 6.6)
# Letters of Phi_C in the variables Y = y3 + y4, xi = y3/Y, and the x-linear letters of G_C.
def _cc_kernel_doc():
    """K_C(Y) of eq. (6.10), as written in docs/TWO-LOOP-UNITS.md (partial fractions)."""
    Y, L, D, a, b, z2 = _CX_Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2
    R = sp.Rational
    kL = Y - R(1, 2) - R(1, 3)/(Y-1) - R(1, 6)/Y + R(1, 2)/Y**2
    kD = R(2, 3)*Y - R(1, 3) - R(1, 6)/(Y-1) - R(1, 6)/Y
    kaa = Y/6 - R(1, 12) - R(1, 12)/(Y-1)
    kab = Y/3 - R(1, 6) - R(1, 6)/Y + R(1, 2)/Y**2
    ka = Y/6 - R(1, 4) - R(5, 12)/(Y-1) + R(1, 2)/Y
    kb = -R(2, 3)*Y + R(4, 3) - R(5, 6)/Y + R(1, 6)/Y**2
    kz = -R(2, 3)*Y + R(1, 3) + R(1, 12)/(Y-1) + R(1, 4)/Y
    k1 = R(31, 24)*Y - R(7, 6) - R(1, 3)/Y
    return kL*L + kD*D + kaa*a**2 + kab*a*b + ka*a + kb*b + kz*z2 + k1


def _cc_boundary_doc():
    """the boundary function G_C(Y) of eq. (6.11)."""
    Y, L, D, a, b, z2 = _CX_Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2
    R = sp.Rational
    return ((Y**2/2 - Y/2 - 1/(2*Y))*L + (Y**2 - Y)/3*D + (Y**2 - Y)/12*a**2
            + (Y**2/6 - Y/6 - 1/(2*Y))*a*b + (Y**2/12 - Y/4 - R(1, 2))*a
            + (-Y**2/3 + R(7, 6)*Y - R(2, 3) - 1/(6*Y))*b - z2*(Y**2 - Y)/3 + R(37, 48)*Y**2 - R(7, 4)*Y)


def _cc_masters_doc():
    """K_m^C(Y) of eq. (6.11): the convergent simple-pole terms (masters of section 4.5.4)."""
    Y, L, D, a, b, z2 = _CX_Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2
    R = sp.Rational
    return (-R(1, 6)*(L/Y + a*b/Y + (D - R(3, 2)*z2)/Y + 2*(L - z2)/(Y-1) + (D + R(3, 2)*z2)/(Y-1))
            - R(1, 12)*(a**2/(Y-1) - a/(Y-1)) - R(5, 6)*b/Y - R(1, 6)*(a - b)/(2*Y-1))


def _cc_letter_decomp(expr, letters, pt):
    """expr (rational functions and logarithms) as {letter or '1': coefficient}; every logarithm
    argument must factor into the given letters times a positive constant."""
    Ls = {k: sp.Symbol('ln_' + k) for k in letters}

    def logmap(arg):
        num, den = sp.fraction(sp.factor(sp.together(arg)))
        res, const = 0, sp.Integer(1)
        for part, sgn in ((num, 1), (den, -1)):
            c0, fl = sp.factor_list(part)
            const *= c0**sgn
            for f, mult in fl:
                sg = sp.sign(f.subs(pt)); f = sp.expand(sg*f); const *= sg**(mult*sgn)
                key = [k for k, v in letters.items() if sp.expand(f - v) == 0]
                assert len(key) == 1, f
                res += sgn*mult*Ls[key[0]]
        assert const > 0
        return res + sp.log(const)
    P = expr.xreplace({l: logmap(l.args[0]) for l in expr.atoms(sp.log)})
    out = {k: sp.cancel(sp.together(sp.diff(P, sy))) for k, sy in Ls.items()}
    out['1'] = sp.cancel(sp.together(P.xreplace({sy: 0 for sy in Ls.values()})))
    return {k: v for k, v in out.items() if v != 0}


def corner_x_integral():
    """Phi_C(Y, xi) = int_0^1 G_C dx in closed form (section 6.6.1). Returns the two branch
    decompositions of G_C, the coefficients of Phi_C over the letters, and the engine data."""
    y3, y4, x, E, logc, e0 = corner_parts()
    Y, xi = _CX_Y, sp.Symbol('xi', positive=True)
    Yc = y3 + y4
    G = (E - e0).subs(MS, Yc**2).subs(hS, x)
    sub = {y3: Y*xi, y4: Y*(1 - xi)}
    G1 = G.subs(betaS, y3*(1 - Yc)).subs(sub)              # x < x* = (1-Y)/(1-Y xi)
    G2 = G.subs(betaS, y3*y4*x/(1 - x)).subs(sub)          # x > x*
    pt = {Y: sp.Rational(3, 10), xi: sp.Rational(1, 5), x: sp.Rational(2, 7)}
    lin1 = {'x': (0, 1), 'Y+xi(1-Y)x': (Y, xi*(1 - Y))}
    lin2 = {'x': (0, 1), '1-x': (1, -1), '1-xi x': (1, -xi), '1-(1-xi)x': (1, -(1 - xi))}
    cst = {'Y': Y, 'xi': xi, '1-Y': 1 - Y, '1-xi': 1 - xi}
    d1 = _cc_letter_decomp(G1, {**cst, **{k: a + b*x for k, (a, b) in lin1.items()}}, pt)
    d2 = _cc_letter_decomp(G2, {**cst, **{k: a + b*x for k, (a, b) in lin2.items()}}, pt)
    # structure: every logarithm coefficient is a polynomial in x; the rational part is a
    # polynomial in x on the first branch and has simple poles at x = 1/xi, 1/(1-xi) on the second
    for d in (d1, d2):
        for k, c in d.items():
            if k != '1':
                assert not sp.fraction(c)[1].has(x), (k, c)
    assert not sp.fraction(d1['1'])[1].has(x)
    DOM = sp.QQ.frac_field(Y, xi)
    xs = (1 - Y)/(1 - Y*xi)
    pv = {'xs': xs, 1: sp.Integer(1), 0: sp.Integer(0)}
    # logarithm of each x-linear letter at the endpoints, over the letters of Phi_C
    lv = {('x', 'xs'): {'1-Y': 1, '1-Y*xi': -1}, ('x', 1): {},
          ('1-x', 'xs'): {'Y': 1, '1-xi': 1, '1-Y*xi': -1},
          ('Y+xi(1-Y)x', 'xs'): {'xi+Y-2*Y*xi': 1, '1-Y*xi': -1}, ('Y+xi(1-Y)x', 0): {'Y': 1},
          ('1-xi x', 'xs'): {'1-xi': 1, '1-Y*xi': -1}, ('1-xi x', 1): {'1-xi': 1},
          ('1-(1-xi)x', 'xs'): {'xi+Y-2*Y*xi': 1, '1-Y*xi': -1}, ('1-(1-xi)x', 1): {'xi': 1}}
    acc = {}

    def add(k, v):
        acc[k] = acc.get(k, 0) + v

    def branch(d, lin, lo, hi):
        for k, c in d.items():
            if k == '1':
                continue
            C = sp.Poly(c, x, domain=DOM).integrate()
            if k in cst:
                add(k, C.as_expr().subs(x, pv[hi]) - C.as_expr().subs(x, pv[lo]))
                continue
            # int c ln(a + b x) = Ct ln(a + b x) - int b Ct/(a + b x), Ct(-a/b) = 0: no new log
            a, b = lin[k]
            Ct = C - sp.Poly(C.as_expr().subs(x, -sp.Integer(1)*a/b), x, domain=DOM)
            q, r = sp.div(Ct*sp.Poly(b, x, domain=DOM), sp.Poly(a + b*x, x, domain=DOM))
            assert r.is_zero
            Q = q.integrate()
            add('1', -(Q.as_expr().subs(x, pv[hi]) - Q.as_expr().subs(x, pv[lo])))
            for p, sg in ((hi, 1), (lo, -1)):
                if (k, p) in (('x', 0), ('1-x', 1)):
                    continue          # Ct vanishes there
                cv = Ct.as_expr().subs(x, pv[p])
                for l, m in lv[(k, p)].items():
                    add(l, sg*m*cv)
        r = d['1']
        poly = r
        if sp.fraction(r)[1].has(x):
            for k, (a, b) in (('1-xi x', lin2['1-xi x']), ('1-(1-xi)x', lin2['1-(1-xi)x'])):
                res = sp.cancel(sp.cancel(r*(a + b*x)).subs(x, -sp.Integer(1)*a/b))
                poly = poly - res/(a + b*x)
                for p, sg in ((hi, 1), (lo, -1)):
                    for l, m in lv[(k, p)].items():
                        add(l, sg*m*res/b)
            poly = sp.cancel(poly)
            assert not sp.fraction(poly)[1].has(x)
        P = sp.Poly(poly, x, domain=DOM).integrate()
        add('1', P.as_expr().subs(x, pv[hi]) - P.as_expr().subs(x, pv[lo]))
    branch(d1, lin1, 0, 'xs')
    branch(d2, lin2, 'xs', 1)
    co = {k: sp.cancel(sp.together(v)) for k, v in acc.items()}
    co = {k: v for k, v in co.items() if v != 0}
    return xi, co, (d1, d2), (y3, y4, x, G)


def _cc_phi_expr(xi, co):
    Y = _CX_Y
    lt = {'Y': Y, 'xi': xi, '1-Y': 1 - Y, '1-xi': 1 - xi, '1-Y*xi': 1 - Y*xi, 'xi+Y-2*Y*xi': xi + Y - 2*Y*xi}
    return co.get('1', 0) + sum(c*sp.log(lt[k]) for k, c in co.items() if k != '1')


def run_cornerexact(args):
    T = targets()
    Y, L, D, a, b, z2 = _CX_Y, _CX_L, _CX_D, _CX_a, _CX_b, _CX_z2
    print('== corner unit C: exact evaluation (section 6.6)')
    t0 = time.time()
    # step 1: x-integration
    xi, co, (d1, d2), (y3, y4, x, G) = corner_x_integral()
    print(f'  step 1: G_C letters: branch x<x*: {sorted(d1)}; branch x>x*: {sorted(d2)}')
    print('    all logarithm coefficients are polynomials in x; rational parts: polynomial (x<x*),'
          ' simple poles at x = 1/xi, 1/(1-xi) (x>x*) -> no dilogarithm')
    print(f'    Phi_C = int_0^1 G_C dx: letters {sorted(k for k in co if k != "1")} ({time.time()-t0:.0f} s)')
    for k in ('1', 'Y', 'xi', '1-Y*xi', 'xi+Y-2*Y*xi'):
        print(f'    denominator of the {k:12s} coefficient: {sp.factor(sp.fraction(co[k])[1])}')
    Phi = _cc_phi_expr(xi, co)
    fP = sp.lambdify((Y, xi), Phi, 'mpmath')
    f1 = sp.lambdify((y3, y4, x), G.subs(betaS, y3*(1 - y3 - y4)), 'mpmath')
    f2 = sp.lambdify((y3, y4, x), G.subs(betaS, y3*y4*x/(1 - x)), 'mpmath')
    mp.mp.dps = 40
    worst = 0
    for yv, sv in (('0.3', '0.2'), ('0.8', '0.65'), ('0.55', '0.9')):
        yv, sv = mp.mpf(yv), mp.mpf(sv)
        a3, a4 = yv*sv, yv*(1 - sv); xsv = (1 - yv)/(1 - yv*sv)
        q = mp.quad(lambda t: f1(a3, a4, t), [0, xsv]) + mp.quad(lambda t: f2(a3, a4, t), [xsv, 1])
        worst = max(worst, abs(q - fP(yv, sv)))
    print('    Phi_C against x-quadrature of G_C at three points (40 digits): max deviation', mp.nstr(worst, 3))
    # step 2: xi-integration (same finite-part machinery as for X)
    cox = dict(co); cox.setdefault('1-Y', 0)
    assert set(cox) <= {'1', 'Y', 'xi', '1-Y*xi', 'xi+Y-2*Y*xi', '1-Y'} and cox['1-Y'] == 0
    K, div = crossed_xi_integral(xi, cox)
    assert all(v == 0 for v in div.values()), div
    print(f'  step 2: xi-integral in closed form; all {len(div)} endpoint divergences cancel')
    Kc = crossed_canonical(K)
    print('    canonical form (identities (4.6)) equals eq. (6.10):', _cx_is_zero(Kc - _cc_kernel_doc()))
    fK = _cx_numeric(_cc_kernel_doc())
    mp.mp.dps = args.dps
    xn = de_nodes(mp.mpf(1)/args.level, T=4.0)
    for yv in (mp.mpf('0.3'), mp.mpf('0.7')):
        v = 0
        for u, um, w in xn:
            for x_, xm in ((u/2, 1 - u/2), (1 - u/2, u/2)):
                with mp.workdps(mp.mp.dps + bumped(min(x_, xm, um/2))):
                    try:
                        v += w/2*yv*fP(yv, x_)
                    except ZeroDivisionError:    # a node rounded onto xi = 1/2; negligible weight
                        pass
        with mp.workdps(mp.mp.dps + 20):
            kv = fK(yv)
        print(f'    K_C({mp.nstr(yv, 2)}): xi-quadrature {mp.nstr(v, 25)}  eq. (6.10) {mp.nstr(kv, 25)}  diff {mp.nstr(v - kv, 3)}')
    mp.mp.dps = 40

    def Kh(y):
        if y <= 0 or y >= 1:
            return mp.mpf(0)
        with mp.workdps(int(5*max(0, -mp.log10(min(y, 1 - y)))) + 60):
            return fK(y)
    v = mp.quad(Kh, [0, 0.1, 0.3, 0.5, 0.7, 0.9, 1])
    bC = 2*v - mp.mpf(3)/2
    print('    int_0^1 K_C =', mp.nstr(v, 35))
    print('    b_C = 2 int K_C - 3/2 =', mp.nstr(bC, 35), '  BMR', mp.nstr(T['C'], 35), '  diff', mp.nstr(bC - T['C'], 3))
    # step 3: K_C = G' + K_m exactly, boundary values
    Gb, Km = _cc_boundary_doc(), _cc_masters_doc()
    print("  step 3: K_C - G_C' - K_m^C = 0 identically:", _cx_is_zero(_cc_kernel_doc() - _cx_ddY(Gb) - Km))
    g0, dd0 = _cx_series_limit(Gb, 0); g1, dd1 = _cx_series_limit(Gb, 1)
    print(f'    G_C(0+) = {g0},  G_C(1-) = {g1}  (divergent parts: {dd0}, {dd1})')
    with mp.workdps(60):
        fG = _cx_numeric(Gb); e_ = mp.mpf(10)**-12
        print('    numerically G_C(1e-12) =', mp.nstr(fG(e_), 12), ' G_C(1-1e-12) =', mp.nstr(fG(1 - e_), 12))
    # step 4: the masters (all from section 4.5.4)
    Z2, Z3, LN2 = mp.zeta(2), mp.zeta(3), mp.log(2)
    Dn = lambda y: mp.polylog(2, 1-2*y) - mp.polylog(2, 2*y-1)
    q = lambda f, pts=(0, 0.5, 1): mp.quad(f, list(pts))
    mv = {'M1': (q(lambda y: mp.polylog(2, y)/y), Z3), 'M2': (q(lambda y: mp.log(y)*mp.log1p(-y)/y), Z3),
          'M3': (q(lambda y: (Dn(y) - 3*Z2/2)/y, (0, 0.25, 0.5, 1)), -3*Z2*LN2 - 7*Z3/4),
          "M3'": (q(lambda y: (Dn(y) + 3*Z2/2)/(y-1), (0, 0.5, 0.75, 1)), -3*Z2*LN2 - 7*Z3/4),
          'M4': (q(lambda y: (mp.polylog(2, y) - Z2)/(y-1)), 2*Z3), 'M5': (q(lambda y: mp.log(y)**2/(y-1)), -2*Z3),
          'M6': (q(lambda y: mp.log(y)/(y-1)), Z2), 'M7': (q(lambda y: mp.log1p(-y)/y), -Z2),
          'M8': (q(lambda y: (mp.log(y) - mp.log1p(-y))/(2*y-1), (0, 0.3, 0.7, 1)), 3*Z2/2)}
    print('  step 4: the masters M1..M8 of section 4.5.4 (40 digits): max deviation',
          mp.nstr(max(abs(u - w) for u, w in mv.values()), 3))
    # step 5: assembly
    z3, M3 = sp.symbols('z3 M3')
    mex = {'M1': z3, 'M2': z3, 'M3': M3, "M3'": M3, 'M4': 2*z3, 'M5': -2*z3, 'M6': z2, 'M7': -z2,
           'M8': sp.Rational(3, 2)*z2}
    R = sp.Rational
    comb = (-R(1, 6)*(mex['M1'] + mex['M2'] + mex['M3'] + 2*mex['M4'] + mex["M3'"])
            - R(1, 12)*(mex['M5'] - mex['M6']) - R(5, 6)*mex['M7'] - R(1, 6)*mex['M8'])
    intK = sp.expand(g1 - g0 + comb)
    print('  step 5: int K_C = G_C(1-) - G_C(0+) + (masters) =', intK)
    intK = sp.expand(intK.subs(M3, -3*z2*sp.log(2) - R(7, 4)*z3))
    bCs = sp.expand(2*intK - R(3, 2))
    SCs = sp.expand(bCs + R(11, 24) - z2/3)
    print('          with M3 = -3 z2 ln2 - 7/4 z3:  b_C =', bCs)
    print('          S + C = b_S + b_C =', SCs, '  (b_S = 11/24 - z2/3, section 5.5)')
    with mp.workdps(40):
        for nm, ex, ref in (('b_C', bCs, T['C']), ('S+C', SCs, T['SC'])):
            fv = mp.mpf(str(sp.N(ex.subs({z2: sp.pi**2/6, z3: sp.zeta(3)}), 45)))
            print(f'          {nm} = {mp.nstr(fv, 30)}   BMR {mp.nstr(ref, 30)}   diff {mp.nstr(fv - ref, 3)}')


# ====================================================================== exact pieces
def run_exact(args):
    """the elementary decompositions of int K_L and int K_S used in sections 3.5 and 5.5."""
    mp.mp.dps = 40
    q = lambda f: mp.quad(f, [0, mp.mpf(1)/2, 1])
    z2 = mp.zeta(2)
    checks = [
        ('int_0^1 ln(1-y)/y = -zeta(2)', q(lambda y: mp.log1p(-y)/y), -z2),
        ('int_0^1 ln(y)/(1-y) = -zeta(2)', q(lambda y: mp.log(y)/(1-y)), -z2),
        ('int_0^1 [ln(1-y)+y]/y^2 = -1', q(lambda y: (mp.log1p(-y)+y)/y**2), -1),
        ('int K_L = 1/16 + zeta(2)/3', q(ladder_K), mp.mpf(1)/16 + z2/3),
        ('int K_S = 11/48 - zeta(2)/6', q(selfenergy_KS), mp.mpf(11)/48 - z2/6),
    ]
    for name, val, ref in checks:
        print(f'  {name:36s} {mp.nstr(val, 30)}  diff {mp.nstr(val - ref, 3)}')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('mode', choices=['ladder', 'selfenergy', 'corner', 'crossed', 'crossedexact', 'cornerexact',
                                         'exact', 'all'])
    ap.add_argument('--dps', type=int, default=None)
    ap.add_argument('--skip-finite', action='store_true')
    ap.add_argument('--level', type=int, default=None,
                    help='inverse tanh-sinh step of the outer rules (corner default 8, crossed 8 and 16)')
    args = ap.parse_args()
    modes = (['exact', 'ladder', 'selfenergy', 'corner', 'crossed', 'crossedexact', 'cornerexact'] if args.mode == 'all'
             else [args.mode])
    bS_, bC_ = None, None
    for m in modes:
        t0 = time.time()
        if m == 'ladder':
            run_ladder(args)
        elif m == 'selfenergy':
            bS_ = run_selfenergy(args)
        elif m == 'corner':
            args.dps = args.dps or 24; lv = args.level; args.level = lv or 8
            bC_ = run_corner(args); args.level = lv
        elif m == 'crossed':
            args.dps = args.dps or 30; lv = args.level; args.level = lv or 8
            run_crossed(args); args.level = lv
        elif m == 'crossedexact':
            dps, lv = args.dps, args.level
            args.dps = dps or 30; args.level = lv or 16
            run_crossedexact(args); args.dps, args.level = dps, lv
        elif m == 'cornerexact':
            dps, lv = args.dps, args.level
            args.dps = dps or 50; args.level = lv or 64
            run_cornerexact(args); args.dps, args.level = dps, lv
        elif m == 'exact':
            run_exact(args)
        print(f'  [{m}: {time.time()-t0:.0f} s]', flush=True)
    if bS_ is not None and bC_ is not None:
        T = targets()
        print('== S + C = b_S + b_C =', mp.nstr(bS_ + bC_, 22), '  BMR', mp.nstr(T['SC'], 22),
              '  difference', mp.nstr(bS_ + bC_ - T['SC'], 3))


if __name__ == '__main__':
    main()
