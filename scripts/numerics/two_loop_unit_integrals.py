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
    ap.add_argument('mode', choices=['ladder', 'selfenergy', 'corner', 'crossed', 'exact', 'all'])
    ap.add_argument('--dps', type=int, default=None)
    ap.add_argument('--skip-finite', action='store_true')
    ap.add_argument('--level', type=int, default=None,
                    help='inverse tanh-sinh step of the outer rules (corner default 8, crossed 8 and 16)')
    args = ap.parse_args()
    modes = ['exact', 'ladder', 'selfenergy', 'corner', 'crossed'] if args.mode == 'all' else [args.mode]
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
        elif m == 'exact':
            run_exact(args)
        print(f'  [{m}: {time.time()-t0:.0f} s]', flush=True)
    if bS_ is not None and bC_ is not None:
        T = targets()
        print('== S + C = b_S + b_C =', mp.nstr(bS_ + bC_, 22), '  BMR', mp.nstr(T['SC'], 22),
              '  difference', mp.nstr(bS_ + bC_ - T['SC'], 3))


if __name__ == '__main__':
    main()
