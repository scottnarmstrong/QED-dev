#!/usr/bin/env python3
"""Numerical validation of the Phase 5 vacuum-polarization chains (task T1). NOT a proof.

Companion of docs/HIGHER-LOOP-PLAN.md (sections 7, 8.3 T1 and 9). It folds in the planning
scripts (chain_checks.py, tau_check.py, ratio_check.py, three_pslq.py) and adds the
model-level checks of T1 item 2. Every statement it supports remains a proof obligation;
floating-point agreement is evidence only.

Conventions (those of the two-loop VP unit, docs/TWO-LOOP-DERIVATION.md 5.3 and 11, and of
QED/TwoLoop/UnitVPLink.lean): open-line mass m = 1, Euclidean photon variable s = k^2,
r = alpha/pi = e^2/(4 pi^2).
  * Pauli-Villars photon function   D(s) = 1/(s + m_gamma^2) - 1/(s + Lambda^2).
  * Model loop function (QED.WickModel.vacuumPolarizationLoop), divided by r:
        Pi_loop(s)/r = 2 sum_f c_f int_0^1 t(1-t) log(M_f^2 + t(1-t) s) dt,
    flavours f = 0, 1, 2 with masses (m_loop, M_1, M_2), c_0 = 1 and c_1, c_2 fixed by the two
    Pauli-Villars conditions 1 + c_1 + c_2 = 0, m_loop^2 + c_1 M_1^2 + c_2 M_2^2 = 0.
  * delta_3 = Pi_loop(0), the photon condition (Z8).
  * Subtracted one-flavour function PiHat_M(s) = 2 int t(1-t) log(1 + t(1-t) s/M^2) dt
    (Srednicki (62.25)/r), with the spectral form int_0^1 rho(v) s/(s + 4M^2/(1-v^2)) dv,
    rho(v) = v^2(1 - v^2/3)/(1 - v^2) (O2-18).
  * Outer one-loop functional at q -> 0 (UnitVPLink.outerF2 times 4 pi^2):
        O[R] = int_0^1 x^2 R(x^2/(1-x)) dx .
    For R = 1/(s + c) it is the one-loop F2/r with a photon of squared mass c (f2 of
    two_loop_units.py). It is evaluated in the variable t = log s:
        O[R] = int dt  x^4/(2x + s) R(s),   x = 2s/(s + sqrt(s^2 + 4s)),
    with tanh-sinh quadrature split at the logarithms of every mass scale.
  * Chain of n bubbles: photon function D (Pi k^2 D)^n, so the coefficient of r^(n+1) is
    O[(Pi/r)^n s^n D^(n+1)]. At m_gamma = 0, Lambda = inf, M_f = inf it is the planning
    formula int_0^1 (1-x) prod_i PiHat(x^2/(1-x)) dx. A multiset of flavours carries the
    multinomial number of orderings.

Sections of the output:
  A. Every row of HIGHER-LOOP-PLAN section 9 against its pinned reference, plus the I(a)
     mass-dependent entries of AHKN Tables 1-2 and the A_3^(6) values of AHKN (2.11) and
     AKN Table 1 (also pinned).
  B. O3-M3: Passera (10) (direct, and rewritten for y = m_e/m_l < 1 with Li2 at y, -y, y^2)
     against the spectral double integral and the Feynman-parameter form, at the Passera,
     AHKN and AKN mass ratios.
  C. Stage 1a model-level check (O3-10, O3-11, O3-12 in the Q1 order): the set (b) value at
     finite (m_gamma, Lambda, M_1, M_2), from the nested form O[(Pi_loop - delta_3)^2 s^2 D^3],
     not from the limited formula; its four contraction types; a spectral cross-check of the
     O3-10 representation; convergence tables.
  D. O3-12: the cross terms 2 Pi_{R,e} Delta_M and Delta_M^2 as min(M_1, M_2) -> inf at
     several ratios M_2/M_1.
  E. Stage 0 analogue: the heavy-lepton VP unit O[(Pi_loop,l - delta_3,l) s D^2], with the
     lepton's own Pauli-Villars pair, at finite regulators, converging to A_2^(4)(m_e/m_l).

What these numerics do NOT test: the energy-first prescription and epsilon -> 0+, the
q^2 -> 0+ limit (the outer functional is already the q -> 0 value), nested-equals-joint (O3-6),
covariance and the projector (O3-8), and the family enumeration (O3-3, O3-4). They start from
the outer functional, as TWO-LOOP-DERIVATION 11 did for the VP unit.

Run (one core, about 4 minutes on a loaded machine; memory below 0.1 GB):
  OMP_NUM_THREADS=1 nice -n 19 python3 scripts/numerics/phase5_chains.py > scripts/numerics/phase5_chains.out
  python3 scripts/numerics/phase5_chains.py --quick    # sections A-B at lower precision only
Requires mpmath (run with mpmath 1.3.0, sympy 1.14.0, numpy 2.5.3).
"""
import platform
import sys
import time

import mpmath
from mpmath import mp, mpf, inf, log, sqrt, pi, zeta, polylog, pslq, re, quad

T0 = time.time()


def say(*a):
    print(*a, flush=True)


# ======================================================================= one-loop bubble
def pihat(s, M=1):
    """Subtracted one-flavour bubble PiHat_M(s) = Pi_{R,M}(s)/r (Srednicki (62.25)/r)."""
    s = mpf(s) / mpf(M) ** 2
    if s == 0:
        return mpf(0)
    if s < mpf(1) / 10:
        # 2 sum_k (-1)^(k+1) s^k/k B(k+2,k+2); B(k+3,k+3)/B(k+2,k+2) = (k+2)/(2(2k+5))
        b = mpf(1) / 30          # B(3,3)
        tot, k, sk = mpf(0), 1, s
        eps = mpf(2) ** (-mp.prec - 10)
        while True:
            term = sk / k * b
            tot += term if k % 2 else -term
            if abs(term) < eps * abs(tot):
                break
            b *= mpf(k + 2) / (2 * (2 * k + 5))
            sk *= s
            k += 1
        return 2 * tot
    a = 4 / s
    be = sqrt(1 + a)
    return (-mpf(5) / 3 + a + (1 - a / 2) * be * log((be + 1) ** 2 / a)) / 3


def pihat_int(s, M=1):
    """The defining integral of PiHat (quadrature)."""
    M2 = mpf(M) ** 2
    return 2 * quad(lambda t: t * (1 - t) * log(1 + t * (1 - t) * s / M2), [0, 1])


def pihat_spec(s, M=1):
    """Spectral form int rho(v) s/(s + 4M^2/(1-v^2)) dv (O2-18), by quadrature."""
    M2 = mpf(M) ** 2
    return quad(lambda v: v ** 2 * (1 - v ** 2 / 3) * s / ((1 - v ** 2) * s + 4 * M2),
                [0, mpf(1) / 2, mpf(9) / 10, 1])


def pv_coeffs(m, M1, M2):
    """Pauli-Villars coefficients for loop mass m: 1+c1+c2 = 0, m^2 + c1 M1^2 + c2 M2^2 = 0."""
    m, M1, M2 = mpf(m), mpf(M1), mpf(M2)
    return (M2 ** 2 - m ** 2) / (M1 ** 2 - M2 ** 2), (M1 ** 2 - m ** 2) / (M2 ** 2 - M1 ** 2)


class Flavours:
    """Loop mass m with its Pauli-Villars pair (M1, M2); M1 = None means no regulator flavours
    (the limit M_f -> inf of the subtracted function, used only for limited comparisons)."""

    def __init__(self, m=1, M1=None, M2=None):
        self.m = mpf(m)
        if M1 is None:
            self.masses, self.coeffs = [self.m], [mpf(1)]
        else:
            c1, c2 = pv_coeffs(m, M1, M2)
            self.masses, self.coeffs = [self.m, mpf(M1), mpf(M2)], [mpf(1), c1, c2]

    def loop(self, s):
        """Pi_loop(s)/r, closed form of the model's integral (Lean vacuumPolarizationLoop / r):
        2 int t(1-t) log(M^2 + t(1-t)s) dt = (1/3) log M^2 + PiHat_M(s) for each flavour."""
        return sum(c * (log(M ** 2) / 3 + pihat(s, M)) for c, M in zip(self.coeffs, self.masses))

    def loop_int(self, s):
        """Pi_loop(s)/r by quadrature of the defining integral, for checking loop()."""
        return 2 * quad(lambda t: t * (1 - t) * sum(
            c * log(M ** 2 + t * (1 - t) * s) for c, M in zip(self.coeffs, self.masses)), [0, 1])

    def delta3(self):
        return self.loop(0)

    def renorm(self, s):
        return sum(c * pihat(s, M) for c, M in zip(self.coeffs, self.masses))

    def spectral(self, s):
        return sum(c * pihat_spec(s, M) for c, M in zip(self.coeffs, self.masses))

    def scales(self):
        return [M ** 2 for M in self.masses] + [4 * M ** 2 for M in self.masses]


# ======================================================================= outer functional
def xofs(s):
    return 2 * s / (s + sqrt(s * s + 4 * s))


def outer(R, scales=(), err=False):
    """O[R] = int_0^1 x^2 R(x^2/(1-x)) dx, in t = log s, split at log(scale)."""
    pts = {mpf(0)}
    for c in scales:
        if c is not None and c != inf and c > 0:
            lc = log(mpf(c))
            pts.update((lc - 2, lc, lc + 2))
    pts = sorted(pts)

    def g(t):
        s = mp.exp(t)
        x = xofs(s)
        return x ** 4 / (2 * x + s) * R(s)

    val, e = quad(g, [-inf] + pts + [inf], error=True)
    return (val, e) if err else val


def photonD(mg, Lam):
    mg2 = mpf(mg) ** 2
    if Lam == inf:
        return lambda s: 1 / (s + mg2)
    L2 = mpf(Lam) ** 2
    return lambda s: 1 / (s + mg2) - 1 / (s + L2)


def f2(c):
    """one-loop F2/r with a photon of squared mass c."""
    c = mpf(c)
    return outer(lambda s: 1 / (s + c), [c])


def chain(Ms, mult=1):
    """Limited chain int (1-x) prod PiHat_{M_i}(x^2/(1-x)) dx = O[prod PiHat / s]."""
    sc = [1, 4] + [mpf(M) ** 2 for M in Ms] + [4 * mpf(M) ** 2 for M in Ms]
    return mult * outer(lambda s: mp.fprod([pihat(s, M) for M in Ms]) / s, sc)


# ======================================================================= Passera (10)
def passera10(x):
    """Passera (2007) eq. (10), A_2^(4)(1/x), x = m_j/m_l; real parts for x > 1."""
    x = mpf(x)
    L = log(x)
    t1 = -mpf(25) / 36 - L / 3 + x ** 2 * (4 + 3 * L)
    br = pi ** 2 / 2 - L * log(abs((1 - x) / (1 + x))) - re(polylog(2, x)) + polylog(2, -x)
    t2 = x / 2 * (1 - 5 * x ** 2) * br
    t3 = x ** 4 * (pi ** 2 / 3 - 2 * L * log(abs(1 / x - x)) - re(polylog(2, x ** 2)))
    return t1 + t2 + t3


def passera10_inv(y):
    """Passera (10) at x = 1/y > 1 rewritten with Li2 at y, -y, y^2 (inversion formula
    Re Li2(z) + Li2(1/z) = pi^2/3 - log^2(z)/2 for z > 1, Li2(-z) + Li2(-1/z) = -pi^2/6 - log^2(z)/2);
    every function is real on 0 < y < 1."""
    y = mpf(y)
    L = log(y)                       # log x = -L
    t1 = -mpf(25) / 36 + L / 3 + (4 - 3 * L) / y ** 2
    # pi^2/2 - log x log((x-1)/(x+1)) - Re Li2(x) + Li2(-x)
    br = (pi ** 2 / 2 + L * log((1 - y) / (1 + y))
          - (pi ** 2 / 3 - L ** 2 / 2 - polylog(2, y))
          + (-pi ** 2 / 6 - L ** 2 / 2 - polylog(2, -y)))
    t2 = (1 - 5 / y ** 2) / (2 * y) * br
    # x^4 [pi^2/3 - 2 log x log(x - 1/x) - Re Li2(x^2)] = y^-4 [2 L log(1-y^2) + Li2(y^2)]
    t3 = (2 * L * log(1 - y ** 2) + polylog(2, y ** 2)) / y ** 4
    return t1 + t2 + t3


def vplim_spectral(M):
    """The spectral double integral int_0^1 rho(v) f2(4M^2/(1-v^2)) dv (O2-18 / O3-M3)."""
    M2 = mpf(M) ** 2
    rho = lambda v: v ** 2 * (1 - v ** 2 / 3) / (1 - v ** 2)
    return quad(lambda v: rho(v) * f2(4 * M2 / (1 - v ** 2)), [0, mpf(1) / 2, mpf(9) / 10, 1])


# ======================================================================= reporting helpers
def nsig(val, ref, unc):
    return abs(val - ref) / unc


def status(val, ref, unc):
    n = nsig(val, ref, unc)
    if n <= 1:
        return f"agrees ({mp.nstr(n, 2)} sigma)"
    if n <= 2:
        return f"agrees within 2 sigma ({mp.nstr(n, 2)} sigma)"
    return f"DISAGREES ({mp.nstr(n, 3)} sigma)"


def trunc_status(val, digits_str):
    """reference quoted as truncated digits, e.g. '0.000876865' followed by '...'."""
    ok = mp.nstr(val, 30, strip_zeros=False).startswith(digits_str)
    return "agrees (digits match)" if ok else "DISAGREES (digits differ)"


def e(v, n=12):
    return mp.nstr(v, n)


# Mass ratios m_e/m_l of the pinned sources
RATIOS = {
    "Pas": ("4.83633167e-3", "2.87564e-4", "Passera (3)-(4)"),
    "AHKN": ("4.83633166e-3", "2.87592e-4", "AHKN p. 4 (sec. 2)"),
    "AKN": ("4.83633170e-3", "2.87585e-4", "AKN Table 1 caption"),
}
# A_2^(4) references: (value, uncertainty, label)
A24_REF = {
    ("Pas", "mu"): ("5.19738670e-7", "0.00000028e-7", "Pas (11)"),
    ("AHKN", "mu"): ("5.19738667e-7", "0.00000026e-7", "AHKN (2.6)"),
    ("AKN", "mu"): ("0.519738676e-6", "0.000000024e-6", "AKN Table 1"),
    ("Pas", "tau"): ("1.83762e-9", "0.00060e-9", "Pas (12)"),
    ("AHKN", "tau"): ("1.83798e-9", "0.00034e-9", "AHKN (2.7)"),
    ("AKN", "tau"): ("0.183790e-8", "0.000025e-8", "AKN Table 1"),
}
AB_CLOSED = lambda: 8 * zeta(3) / 3 - 4 * pi ** 2 / 135 - mpf(943) / 324
IA8_CLOSED = lambda: mpf(151849) / 40824 + 32 * zeta(3) / 63 - 2 * pi ** 4 / 45


# ======================================================================= section A
def section_A(quick=False):
    say("=" * 100)
    say("A. HIGHER-LOOP-PLAN section 9, row by row, against the pinned references")
    say("=" * 100)
    mp.dps = 35
    say("A.0 machinery")
    for s, M in ((mpf("0.3"), 1), (mpf(7), 1), (mpf(5), 3), (mpf("0.05"), 1), (mpf(1000), 1)):
        say(f"  PiHat closed form - defining integral, s={e(s, 4)}, M={M}: "
            f"{e(pihat(s, M) - pihat_int(s, M), 3)};  - spectral form: {e(pihat(s, M) - pihat_spec(s, M), 3)}")
    for c in (mpf("1e-6"), mpf("0.3"), mpf(4), mpf("1e8")):
        bp = sorted({p for p in (sqrt(c) / 4, sqrt(c), 4 * sqrt(c), mpf(1) / 2, 1 - 1 / c,
                                 1 - 10 / c, 1 - mpf(1) / (10 * c)) if 0 < p < 1})
        ref = quad(lambda x: x ** 2 * (1 - x) / (x ** 2 + (1 - x) * c), [0] + bp + [1])
        say(f"  outer functional f2(c) in t = log s minus direct x-quadrature, c={e(c, 3)}: {e(f2(c) - ref, 3)}")
    say(f"  f2(0) = O[1/s] = {e(outer(lambda s: 1 / s, [1]), 20)} (exact 1/2)")

    rows = []   # (quantity, computed, sec-9 recorded, reference, status)
    mp.dps = 40
    one = chain([1])
    rows.append(("one electron bubble int(1-x)PiHat", e(one, 25), "0.015687421859102682610725",
                 "119/36 - pi^2/3 (BMR-II (1.10); integral_vpUnit)",
                 f"diff {e(one - (mpf(119) / 36 - pi ** 2 / 3), 3)}"))

    a24 = {}
    for src in ("Pas", "AHKN", "AKN"):
        for k, lep in ((0, "mu"), (1, "tau")):
            mp.dps = 60
            y = mpf(RATIOS[src][k])
            vchain = chain([1 / y])
            v10 = passera10(1 / y)
            a24[(src, lep)] = vchain
            val, unc, lab = A24_REF[(src, lep)]
            rows.append((f"A2(4)(me/m{lep}), {src} ratio {RATIOS[src][k]}",
                         f"{e(vchain, 13)} (Pas(10) - chain: {e(v10 - vchain, 2)})",
                         {("Pas", "mu"): "5.19738669696e-7", ("AHKN", "mu"): "5.197386675e-7",
                          ("AKN", "mu"): "5.197386761e-7", ("Pas", "tau"): "1.8376226e-9",
                          ("AHKN", "tau"): "1.8379805e-9", ("AKN", "tau"): "1.8378910e-9"}[(src, lep)],
                         f"{lab} {val}({unc})", status(vchain, mpf(val), mpf(unc))))

    mp.dps = 40
    a36 = {}
    for src, ref, unc, lab in (("Pas", "1.90945e-13", "0.00062e-13", "Pas (21)"),
                               ("AHKN", "1.909e-13", "0.001e-13", "AHKN (2.11)"),
                               ("AKN", "0.1909e-12", "0.0001e-12", "AKN Table 1")):
        ymu, ytau = mpf(RATIOS[src][0]), mpf(RATIOS[src][1])
        v = chain([1 / ymu, 1 / ytau], 2)
        a36[src] = v
        rows.append((f"A3(6) = 2 int(1-x)PiHat_mu PiHat_tau, {src} ratios", e(v, 10),
                     "1.909446e-13" if src == "Pas" else "(not in sec. 9)",
                     f"{lab} {ref}({unc})", status(v, mpf(ref), mpf(unc))))

    mp.dps = 30 if quick else 62
    two = chain([1, 1])
    res_b = two - AB_CLOSED()
    rows.append(("set (b) int(1-x)PiHat^2", e(two, 30), "0.002558524936517345199267462799635",
                 "- (closed form by PSLQ, source to pin)",
                 f"(8/3)z3-(4/135)pi^2-943/324 residual {e(res_b, 3)}"))
    mp.dps = 30 if quick else 72
    three = chain([1, 1, 1])
    res_3 = three - IA8_CLOSED()
    rows.append(("eighth-order I(a) int(1-x)PiHat^3", e(three, 22), "0.0008768658588899906979",
                 "AHKN Table 1 0.000 876 865...",
                 trunc_status(three, "0.000876865") + f"; 151849/40824+(32/63)z3-(2/45)pi^4 residual {e(res_3, 3)}"))
    mp.dps = 35
    four = chain([1, 1, 1, 1])
    rows.append(("tenth-order I(a) int(1-x)PiHat^4", e(four, 12), "0.000470905716",
                 "AHKN Table 2 0.000 470 94(6)", status(four, mpf("0.00047094"), mpf("0.00000006"))))
    ymu = mpf(RATIOS["Pas"][0])
    emu = chain([1, 1 / ymu], 2)
    rows.append(("e-mu chain 2 int(1-x)PiHat_e PiHat_mu (Pas ratio)", e(emu, 10), "2.634672e-7",
                 "part of Pas (15); no pinned comparison", "-"))

    # Extra pinned entries (not in section 9): AHKN Table 1 (eighth order) and Table 2 (tenth)
    # mass-dependent I(a) columns. AHKN states its ratios on p. 4; the values are also shown at
    # the Passera (CODATA 2002) and AKN ratios, since the table entries may predate them.
    e1 = mpf(1)

    def ia_mass(src):
        mu, tau = 1 / mpf(RATIOS[src][0]), 1 / mpf(RATIOS[src][1])
        return (chain([e1, e1, mu], 3) + chain([e1, mu, mu], 3) + chain([mu, mu, mu]),
                chain([e1, e1, tau], 3) + chain([e1, tau, tau], 3) + chain([tau, tau, tau]),
                chain([e1, mu, tau], 6) + chain([mu, mu, tau], 3) + chain([mu, tau, tau], 3),
                chain([e1, e1, e1, mu], 4) + chain([e1, e1, mu, mu], 6) + chain([e1, mu, mu, mu], 4)
                + chain([mu, mu, mu, mu]))
    ia = {src: ia_mass(src) for src in ("AHKN", "Pas", "AKN")}
    for k, (lab, ref, unc, src) in enumerate((
            ("eighth I(a) A2(8)(me/mmu): eemu x3 + emumu x3 + mumumu", "0.000226456e-3", "0.000000014e-3", "AHKN Table 1"),
            ("eighth I(a) A2(8)(me/mtau): eetau x3 + etautau x3 + tau^3", "0.000080233e-5", "0.000000005e-5", "AHKN Table 1"),
            ("eighth I(a) A3(8): emutau x6 + mumutau x3 + mutautau x3", "0.000011994e-7", "0.000000001e-7", "AHKN Table 1"),
            ("tenth I(a) A2(10)(me/mmu): e^3mu x4 + e^2mu^2 x6 + emu^3 x4 + mu^4", "0.00000028", "0.00000001", "AHKN Table 2"))):
        v = ia["AHKN"][k]
        other = "; ".join(f"at {o} ratios {e(ia[o][k], 9)}: {status(ia[o][k], mpf(ref), mpf(unc))}"
                          for o in ("Pas", "AKN"))
        rows.append((lab, f"{e(v, 9)} (AHKN ratios)", "(not in sec. 9)", f"{src} {ref}({unc})",
                     f"at AHKN ratios: {status(v, mpf(ref), mpf(unc))}; {other}"))

    say("\nA.1 table (computed | section-9 recorded value | pinned reference | status)")
    for r in rows:
        say(f"  * {r[0]}\n      computed  : {r[1]}\n      sec. 9    : {r[2]}\n"
            f"      reference : {r[3]}\n      status    : {r[4]}")

    if not quick:
        say("\nA.2 integer-relation detection")
        mp.dps = 45
        two45 = +two
        rel = pslq([two45, mpf(1), pi ** 2, zeta(3), pi ** 2 * log(2), pi ** 4], maxcoeff=10 ** 6, maxsteps=10 ** 6)
        say(f"  set (b), 45 digits, basis [A, 1, pi^2, zeta3, pi^2 ln2, pi^4]: {rel}"
            "  (1620 A + 4715 + 48 pi^2 - 4320 zeta3 = 0 <=> A = (8/3)zeta3 - (4/135)pi^2 - 943/324)")
        mp.dps = 60
        three60 = +three
        rel3 = pslq([three60, mpf(1), pi ** 2, zeta(3), pi ** 4], maxcoeff=10 ** 8, maxsteps=10 ** 7)
        say(f"  eighth-order I(a), 60 digits, basis [A, 1, pi^2, zeta3, pi^4]: {rel3}"
            "  (<=> A = 151849/40824 + (32/63)zeta3 - (2/45)pi^4)")
        qline = "  quadrature check: set (b) at 62 digits minus at 45 digits recomputed: "
        mp.dps = 45
        say(qline + e(chain([1, 1]) - two45, 3))
    say(f"[section A done, {time.time() - T0:.0f} s]")
    return a24


# ======================================================================= section B
def section_B():
    say("\n" + "=" * 100)
    say("B. O3-M3: Passera (10) against the spectral integral, A_2^(4)(y), y = m_e/m_l")
    say("=" * 100)
    say("  columns: spectral double integral int rho(v) f2(4/(y^2(1-v^2))) dv (dps 30) | Feynman-parameter"
        " form int(1-x)PiHat_{1/y} (dps 30) | Pas (10) direct (dps 60) | Pas (10) inverted form, Li2 at y,-y,y^2 (dps 60)")
    for src in ("Pas", "AHKN", "AKN"):
        for k, lep in ((0, "mu"), (1, "tau")):
            ystr = RATIOS[src][k]
            mp.dps = 60
            y = mpf(ystr)
            d10 = passera10(1 / y)
            i10 = passera10_inv(y)
            mp.dps = 30
            t = time.time()
            sp = vplim_spectral(1 / mpf(ystr))
            fp = chain([1 / mpf(ystr)])
            mp.dps = 60
            val, unc, lab = A24_REF[(src, lep)]
            say(f"  {src:4s} m_e/m_{lep:3s} = {ystr}: spectral {e(sp, 16)} | x-form {e(fp, 16)} | "
                f"Pas(10) {e(d10, 16)} | inverted {e(i10, 16)}")
            say(f"        relative differences: spectral/Pas(10)-1 = {e(sp / d10 - 1, 2)}, x-form/Pas(10)-1 = "
                f"{e(fp / d10 - 1, 2)}, inverted - direct = {e(i10 - d10, 2)};  vs {lab} {val}({unc}): "
                f"{status(d10, mpf(val), mpf(unc))}  [{time.time() - t:.0f} s]")
    mp.dps = 60
    say("  checks of the inverted form away from the physical ratios (direct - inverted):")
    for y in ("0.5", "0.9", "0.01", "1e-6"):
        say(f"    y = {y}: {e(passera10(1 / mpf(y)) - passera10_inv(mpf(y)), 3)}")
    say(f"  y = 1: Pas (10) - (119/36 - pi^2/3) = {e(passera10(mpf(1) + mpf(10) ** -40) - (mpf(119) / 36 - pi ** 2 / 3), 3)}"
        " (at x = 1 + 1e-40)")
    say("  small-y behaviour (recalled leading term y^2/45; informational): A2(4)(y)/y^2 * 45 at"
        f" y = 1e-3, 1e-5: {e(passera10_inv(mpf('1e-3')) / mpf('1e-6') * 45, 8)}, "
        f"{e(passera10_inv(mpf('1e-5')) / mpf('1e-10') * 45, 8)}")
    say("  Precision note: Pas (10) direct at the tau ratio, dps 15/25/40/60: " + ", ".join(
        e(_at_dps(dp, lambda: passera10(1 / mpf(RATIOS['Pas'][1]))), 10) for dp in (15, 25, 40, 60)))
    say(f"[section B done, {time.time() - T0:.0f} s]")


def _at_dps(dp, f):
    with mp.workdps(dp):
        return +f()


# ======================================================================= section C
def chain_reg(fl, mg, Lam, err=False):
    """Set (b) at finite regulators from the nested form O[(Pi_loop - delta_3)^2 s^2 D^3]."""
    D = photonD(mg, Lam)
    d3 = fl.delta3()
    sc = fl.scales() + [mpf(mg) ** 2 if mg else None, None if Lam == inf else mpf(Lam) ** 2, 1, 4]
    return outer(lambda s: (fl.loop(s) - d3) ** 2 * s ** 2 * D(s) ** 3, sc, err)


def chain_pieces(fl, mg, Lam):
    """The four contraction types: bubble-bubble, bubble-delta3 (twice), delta3-delta3."""
    D = photonD(mg, Lam)
    d3 = fl.delta3()
    sc = fl.scales() + [mpf(mg) ** 2, None if Lam == inf else mpf(Lam) ** 2, 1, 4]
    bb = outer(lambda s: fl.loop(s) ** 2 * s ** 2 * D(s) ** 3, sc)
    bd = -d3 * outer(lambda s: fl.loop(s) * s ** 2 * D(s) ** 3, sc)
    dd = d3 ** 2 * outer(lambda s: s ** 2 * D(s) ** 3, sc)
    return bb, bd, dd, d3


def chain_spectral(fl, mg, Lam):
    """O3-10 representation: spectral form of each bubble (inner v-integrals), outer x."""
    D = photonD(mg, Lam)
    sc = fl.scales() + [mpf(mg) ** 2, None if Lam == inf else mpf(Lam) ** 2, 1, 4]
    return outer(lambda s: fl.spectral(s) ** 2 * s ** 2 * D(s) ** 3, sc)


def section_C():
    say("\n" + "=" * 100)
    say("C. Stage 1a model-level check: set (b) at finite (m_gamma, Lambda, M1, M2), nested form")
    say("   value = O[(Pi_loop - delta_3)^2 s^2 D^3], Pi_loop the model's flavour-summed loop, delta_3 = Pi_loop(0) (Z8)")
    say("=" * 100)
    mp.dps = 30
    Ab = AB_CLOSED()
    say(f"  target A_(b) = (8/3)zeta3 - (4/135)pi^2 - 943/324 = {e(Ab, 25)}")

    say("\nC.0 Pi_loop closed form against the defining integral (Lean vacuumPolarizationLoop / r)")
    for M1, M2 in ((3, 5), (100, 300), (1000, 1001)):
        fl = Flavours(1, M1, M2)
        say(f"  (M1,M2)=({M1},{M2}): c1={e(fl.coeffs[1], 8)}, c2={e(fl.coeffs[2], 8)}; "
            f"PV conditions: {e(sum(fl.coeffs), 2)}, {e(sum(c * M ** 2 for c, M in zip(fl.coeffs, fl.masses)), 2)}; "
            + "; ".join(f"s={s}: {e(fl.loop(mpf(s)) - fl.loop_int(mpf(s)), 2)}" for s in ("0", "0.5", "40", "1e6"))
            + f"; delta3 = Pi_loop(0)/r = {e(fl.delta3(), 8)}")

    say("\nC.1 the four contraction types at finite regulators (each grows like log^2 M; the sum is finite)")
    say("    columns: bubble-bubble | 2 x bubble-delta3 | delta3-delta3 | sum = nested value | sum - A_(b)")
    for (M1, M2), mg, Lam in (((10, 20), mpf("1e-2"), 100), ((100, 300), mpf("1e-3"), 1000),
                              ((1000, 3000), mpf("1e-3"), 10 ** 4), ((10 ** 4, 3 * 10 ** 4), mpf("1e-3"), 10 ** 5)):
        fl = Flavours(1, M1, M2)
        bb, bd, dd, d3 = chain_pieces(fl, mg, Lam)
        nest = chain_reg(fl, mg, Lam)
        say(f"  M=({M1},{M2}) m_g={e(mg, 2)} Lam={Lam}: delta3/r={e(d3, 7)} | {e(bb, 12)} | {e(2 * bd, 12)} | "
            f"{e(dd, 12)} | {e(bb + 2 * bd + dd, 12)} (nested {e(nest, 12)}) | {e(nest - Ab, 3)}")

    say("\nC.2 the O3-10 representation (spectral form of each bubble, Fubini) against the nested form")
    for (M1, M2), mg, Lam in (((3, 5), mpf("0.1"), 10), ((10, 20), mpf("1e-2"), 100), ((30, 60), 0, inf)):
        fl = Flavours(1, M1, M2)
        mp.dps = 20
        t = time.time()
        sp = chain_spectral(fl, mg, Lam)
        mp.dps = 30
        nest = chain_reg(fl, mg, Lam)
        say(f"  M=({M1},{M2}) m_g={mg} Lam={Lam}: nested {e(nest, 15)}  spectral {e(sp, 15)}  "
            f"diff {e(nest - sp, 2)}  [{time.time() - t:.0f} s]")

    say("\nC.3 regulator table in the Q1 order: value - A_(b); rows (M1,M2), columns (m_gamma, Lambda).")
    say("    The (0, inf) column is the (m_gamma, Lambda) limit at fixed M (O3-11); the M -> inf row")
    say("    (no regulator flavours, i.e. Delta_M = 0) is the opposite order, shown for comparison only.")
    cols = [(mpf("1e-1"), 10), (mpf("1e-2"), 100), (mpf("1e-3"), 1000), (mpf("1e-4"), 10 ** 4),
            (mpf("1e-5"), 10 ** 5), (0, inf)]
    say("    " + f"{'(M1,M2)':>16s}" + "".join(f"{'(' + e(mg, 1) + ',' + e(mpf(L), 1) + ')':>16s}" for mg, L in cols))
    lim_at_M = {}
    maxerr = mpf(0)
    for M in ((3, 5), (10, 20), (30, 60), (100, 300), (1000, 1001), (1000, 3000), (10 ** 4, 3 * 10 ** 4), None):
        fl = Flavours(1, *M) if M else Flavours(1)
        vals = []
        for mg, L in cols:
            v, er = chain_reg(fl, mg, L, err=True)
            maxerr = max(maxerr, er)
            vals.append(v)
        lim_at_M[M] = vals[-1]
        say("    " + f"{str(M) if M else 'inf':>16s}" + "".join(f"{e(v - Ab, 3):>16s}" for v in vals))
    say(f"    (largest quadrature error estimate in the table: {e(maxerr, 2)})")

    say("\nC.4 the (m_gamma, Lambda) limit at fixed M, separately in each regulator, M = (10, 20):")
    fl = Flavours(1, 10, 20)
    L0 = lim_at_M[(10, 20)]
    say("    Lambda = inf, m_gamma -> 0:   " + ", ".join(
        f"m_g={mg}: {e(chain_reg(fl, mpf(mg), inf) - L0, 3)}" for mg in ("1e-1", "1e-2", "1e-3", "1e-4", "1e-6")))
    say("    m_gamma = 0, Lambda -> inf:   " + ", ".join(
        f"Lam={L}: {e(chain_reg(fl, 0, L) - L0, 3)}" for L in (10, 30, 100, 300, 1000, 10 ** 4)))
    say("    off-diagonal (joint limit):  " + ", ".join(
        f"({mg},{L}): {e(chain_reg(fl, mpf(mg), L) - L0, 3)}"
        for mg, L in (("1e-6", 10), ("1e-6", 100), ("0.1", 10 ** 6), ("1e-2", 10 ** 6), ("1e-8", 10 ** 8))))

    kappa = -2 * outer(lambda s: pihat(s), [1, 4]) / 15
    say("\nC.5 regulator fermions last (D-37.4 / Q1): limited value at fixed M minus A_(b), and diff/(M1^-2 + M2^-2)")
    say(f"    leading term predicted from Delta_M ~ -(s/15)(M1^-2 + M2^-2) for s << M^2: kappa (M1^-2 + M2^-2),"
        f" kappa = -(2/15) int x^2 PiHat_e dx = {e(kappa, 8)}")
    for M in ((3, 5), (10, 20), (30, 60), (100, 300), (1000, 1001), (1000, 3000), (10 ** 4, 3 * 10 ** 4)):
        d = lim_at_M[M] - Ab
        say(f"    (M1,M2)={str(M):>16s}: {e(d, 4):>12s}   diff/(M1^-2 + M2^-2) = "
            f"{e(d / (mpf(M[0]) ** -2 + mpf(M[1]) ** -2), 6)}")
    say(f"    no regulator flavours, m_gamma=0, Lambda=inf: {e(lim_at_M[None] - Ab, 3)} (the limited formula)")
    say(f"[section C done, {time.time() - T0:.0f} s]")


# ======================================================================= section D
def section_D():
    say("\n" + "=" * 100)
    say("D. O3-12: cross terms in the Q1 order (m_gamma = 0, Lambda = inf), Pi_R = Pi_{R,e} + Delta_M,")
    say("   Delta_M = c1 PiHat_{M1} + c2 PiHat_{M2}.  X1 = O[2 Pi_{R,e} Delta_M / s], X2 = O[Delta_M^2 / s]")
    say("=" * 100)
    mp.dps = 40
    Ab = AB_CLOSED()
    kappa = -2 * outer(lambda s: pihat(s), [1, 4]) / 15
    say(f"  kappa = -(2/15) int x^2 PiHat_e dx = {e(kappa, 8)} (predicted X1 ~ kappa (M1^-2 + M2^-2))")
    say("  columns: M1 | M2/M1 | c1 | X1 | X2 | X1 + X2 + A_(b) - (limited nested value) | X1/(M1^-2+M2^-2) | M1^4 X2")
    for ratio in ("1.000001", "1.001", "1.1", "2", "10", "100", "1000"):
        for M1 in (10, 100, 1000, 10 ** 4):
            M1 = mpf(M1)
            M2 = M1 * mpf(ratio)
            fl = Flavours(1, M1, M2)
            c1, c2 = fl.coeffs[1], fl.coeffs[2]
            dM = lambda s: c1 * pihat(s, M1) + c2 * pihat(s, M2)
            sc = fl.scales() + [1, 4]
            X1 = outer(lambda s: 2 * pihat(s) * dM(s) / s, sc)
            X2 = outer(lambda s: dM(s) ** 2 / s, sc)
            nest = chain_reg(fl, 0, inf)
            say(f"  {e(M1, 6):>7s} | {ratio:>9s} | {e(c1, 6):>12s} | {e(X1, 6):>12s} | {e(X2, 6):>12s} | "
                f"{e(X1 + X2 + Ab - nest, 2):>9s} | {e(X1 / (M1 ** -2 + M2 ** -2), 6):>10s} | {e(M1 ** 4 * X2, 6):>10s}")
    say("  ratios below 1 (M2 < M1) are the same pairs with the labels swapped (the value is symmetric):")
    for M1, M2 in ((100, 50), (1000, 10)):
        a = chain_reg(Flavours(1, M1, M2), 0, inf)
        b = chain_reg(Flavours(1, M2, M1), 0, inf)
        say(f"    ({M1},{M2}) - ({M2},{M1}) = {e(a - b, 3)}")
    say(f"[section D done, {time.time() - T0:.0f} s]")


# ======================================================================= section E
def vp_heavy_reg(fl, mg, Lam, err=False):
    """Heavy-lepton VP unit O[(Pi_loop,l - delta_3,l) s D^2]: one flavour block, its own PV pair."""
    D = photonD(mg, Lam)
    d3 = fl.delta3()
    sc = fl.scales() + [mpf(mg) ** 2 if mg else None, None if Lam == inf else mpf(Lam) ** 2, 1, 4]
    return outer(lambda s: (fl.loop(s) - d3) * s * D(s) ** 2, sc, err)


def section_E():
    say("\n" + "=" * 100)
    say("E. Stage 0 analogue: heavy-lepton VP insertion at finite regulators, nested form")
    say("   value = O[(Pi_loop,l - delta_3,l) s D^2], loop mass m_l = 1/y with its own PV pair (M1, M2)")
    say("   (PV conditions with m_l: 1 + c1 + c2 = 0, m_l^2 + c1 M1^2 + c2 M2^2 = 0; HIGHER-LOOP-PLAN Q5 (i))")
    say("=" * 100)
    mp.dps = 40
    for lep, k in (("mu", 0), ("tau", 1)):
        y = mpf(RATIOS["Pas"][k])
        ml = 1 / y
        A = passera10_inv(y)
        say(f"\n  m_e/m_{lep} = {RATIOS['Pas'][k]} (Pas), target A2(4) = Pas (10) = {e(A, 15)}")
        say("  E.1 relative deviation (value/A2(4) - 1); rows (M1,M2)/m_l, columns (m_gamma, Lambda)")
        cols = [(mpf("1e-1"), 10), (mpf("1e-2"), 10 ** 2), (mpf("1e-2"), 10 ** 3), (mpf("1e-3"), 10 ** 4),
                (mpf("1e-4"), 10 ** 5), (mpf("1e-5"), 10 ** 6), (0, inf)]
        say("    " + f"{'(M1,M2)/m_l':>16s}" + "".join(f"{'(' + e(mg, 1) + ',' + e(mpf(L), 1) + ')':>16s}" for mg, L in cols))
        lims = {}
        for kM in ((2, 3), (10, 20), (100, 300), (1000, 1001), (10 ** 4, 3 * 10 ** 4), None):
            fl = Flavours(ml, kM[0] * ml, kM[1] * ml) if kM else Flavours(ml)
            vals = [vp_heavy_reg(fl, mg, L) for mg, L in cols]
            lims[kM] = vals[-1]
            say("    " + f"{str(kM) if kM else 'inf':>16s}" + "".join(f"{e(v / A - 1, 3):>16s}" for v in vals))
        say("  E.2 regulator fermions last: limited value at fixed M minus A2(4), and its scaling")
        for kM in ((2, 3), (10, 20), (100, 300), (1000, 1001), (10 ** 4, 3 * 10 ** 4)):
            d = lims[kM] - A
            say(f"    (M1,M2)/m_l={str(kM):>16s}: {e(d, 4):>12s}  (M1)^2 x diff = {e(d * (kM[0] * ml) ** 2, 5)}"
                f"  [(M1^-2 + M2^-2)/45 = {e((1 / (kM[0] * ml) ** 2 + 1 / (kM[1] * ml) ** 2) / 45, 3)}: the form of"
                f" abs_vpLimSum_sub_le, proved only for loop mass 1]")
        say(f"    no regulator flavours (0, inf): {e(lims[None] - A, 3)}")
    say(f"[section E done, {time.time() - T0:.0f} s]")


# ======================================================================= main
def main():
    quick = "--quick" in sys.argv
    say("phase5_chains.py -- numerical validation of the Phase 5 VP chains (task T1). Evidence, not proof.")
    say(f"python {platform.python_version()}, mpmath {mpmath.__version__}; started "
        f"{time.strftime('%Y-%m-%d %H:%M:%S %Z')}; mode {'quick' if quick else 'full'}")
    section_A(quick)
    section_B()
    if not quick:
        section_C()
        section_D()
        section_E()
    say(f"\ntotal run time {time.time() - T0:.0f} s")


if __name__ == "__main__":
    main()
