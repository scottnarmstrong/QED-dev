#!/usr/bin/env python3
"""Generate the box partitions certifying the one-loop Pauli enclosures (packet Q, D-34/D-35).

This script proposes data; it proves nothing. Lean's kernel checks the data with
`QED.Numerics.Quadrature.check` and the interval extension `QED.Numerics.Pauli.remExt`
(QED/Numerics/PauliExtension.lean); the soundness theorem
`QED.Numerics.Pauli.integral_pauliIntegrand_mem_of_check` turns an accepted check into an
enclosure of the integral. A wrong or tampered partition can only make the check fail.

Semantics. For a = 10^-k, b = 10^k (k = 1, 2, 3) and c = 10^-4 the certified integrand is the
remainder

    g(x, y) = 2(1 - y)(1 - T_A + T_B),   T_K = y^2 / ((1 - y) K + y^2 (1 + x(1 - x) c)),

with A = a^2, B = b^2, on the unit square, so that
int pauliIntegrand m (m a, m b, m^2 c) = 1 - int g. The claimed bounds [lo, hi] for int g are
[1 - t_hi, 1 - t_lo], where [t_lo, t_hi] is the interval of the frozen statement.

Data. One strip x in (0, 1]; the cut heights y_1 < ... < y_n = 2^64 (scale S = 2^64) are found by
greedy bisection, starting from geometric cuts 2^40, ..., 2^63, S and always splitting the
segment whose split most reduces the enclosure width, until the width is below a target. The
script evaluates the extension with an exact integer mirror of `QED.Numerics.Interval` (same
operations, same outward rounding), so the enclosure it prints is the one the kernel computes.
Only the standard library is used, and all arithmetic is on integers, so the output is
deterministic.

Usage (from the repository root):
    python3 scripts/numerics/gen_pauli_certificates.py            # write the data modules
    python3 scripts/numerics/gen_pauli_certificates.py --check    # regenerate and compare
"""
import argparse
import heapq
import sys
from fractions import Fraction
from pathlib import Path

S = 2 ** 64
OUT_DIR = Path("QED/Numerics/Certificates")

# (module name, k, claimed bounds for int g as (num, den) pairs, target enclosure width)
POINTS = [
    ("Ten", 1, (2327, 10000), (2332, 10000), Fraction(25, 100000)),
    ("Hundred", 2, (295, 10000), (300, 10000), Fraction(25, 100000)),
    ("Thousand", 3, (29, 10000), (34, 10000), Fraction(25, 100000)),
]

# --- exact mirror of QED.Numerics.Interval at scale S ------------------------------------


def cdiv(m, d):
    return -((-m) // d)


def of_int(n):
    return (n * S, n * S, True)


def of_rat(q):
    q = Fraction(q)
    n = q.numerator * S
    return (n // q.denominator, cdiv(n, q.denominator), True)


def add(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] and b[2])


def sub(a, b):
    return (a[0] - b[1], a[1] - b[0], a[2] and b[2])


def mul(a, b):
    ok = a[2] and b[2]
    if a[0] >= 0 and b[0] >= 0:
        return ((a[0] * b[0]) // S, cdiv(max(a[1], 0) * max(b[1], 0), S), ok)
    c = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(c) // S, cdiv(max(c), S), ok)


def sq(a):
    if a[0] >= 0:
        p, q = a[0], max(a[1], 0)
    elif a[1] < 0:
        p, q = -a[1], -a[0]
    else:
        p, q = 0, max(-a[0], a[1])
    return ((p * p) // S, cdiv(q * q, S), a[2])


def inv(a):
    ss = S * S
    if a[0] >= 1:
        h = max(a[1], 0)
        return (ss // h if h > 0 else 0, cdiv(ss, a[0]), a[2])
    if a[1] < 0:
        return (-cdiv(ss, -a[1]), -(ss // abs(a[0])), a[2])
    return (0, 0, False)


ONE, TWO = of_int(1), of_int(2)
QUARTER, HALF = of_rat(Fraction(1, 4)), of_rat(Fraction(1, 2))

# --- mirror of QED.Numerics.Pauli.{qExt, tExt, remExt} -----------------------------------


def q_ext(C, X):
    return add(ONE, mul(C, sub(QUARTER, sq(sub(X, HALF)))))


def t_ext(K, C, X, Y, y0):
    if y0 == 0:
        return mul(sq(Y), inv(add(mul(sub(ONE, Y), K), mul(sq(Y), q_ext(C, X)))))
    return inv(add(mul(mul(sub(ONE, Y), inv(sq(Y))), K), q_ext(C, X)))


def make_rem_ext(k):
    KA = of_rat(Fraction(1, 10 ** (2 * k)))
    KB = of_rat(10 ** (2 * k))
    C = of_rat(Fraction(1, 10 ** 4))

    def rem_ext(x0, x1, y0, y1):
        X, Y = (x0, x1, True), (y0, y1, True)
        V = add(sub(ONE, t_ext(KA, C, X, Y, y0)), t_ext(KB, C, X, Y, y0))
        return mul(mul(TWO, sub(ONE, Y)), V)

    return rem_ext


# --- partition ---------------------------------------------------------------------------


def seg_sums(F, y0, y1):
    """Scaled contributions (area * lo, area * hi) of the box (0, 1] x (y0/S, y1/S]."""
    lo, hi, ok = F(0, S, y0, y1)
    if not ok:
        raise ValueError(f"no enclosure on the box y in ({y0}, {y1}]")
    w = S * (y1 - y0)
    return w * lo, w * hi


def greedy_cuts(F, target):
    segs, heap = {}, []

    def push(y0, y1):
        L, H = seg_sums(F, y0, y1)
        segs[(y0, y1)] = (L, H)
        # The box touching y = 0 is never split below 2^40 (y^2 must stay visible at scale S).
        if y1 - y0 >= 2 and not (y0 == 0 and y1 <= 2 ** 40):
            mid = (y0 + y1) // 2
            L1, H1 = seg_sums(F, y0, mid)
            L2, H2 = seg_sums(F, mid, y1)
            heapq.heappush(heap, (-((H - L) - (H1 - L1) - (H2 - L2)), y0, y1))

    init = [0] + [2 ** j for j in range(40, 64)] + [S]
    for y0, y1 in zip(init, init[1:]):
        push(y0, y1)
    width = sum(H - L for L, H in segs.values())
    while Fraction(width, S ** 3) > target:
        _, y0, y1 = heapq.heappop(heap)
        L, H = segs.pop((y0, y1))
        width -= H - L
        mid = (y0 + y1) // 2
        push(y0, mid)
        push(mid, y1)
        width += sum(segs[s][1] - segs[s][0] for s in ((y0, mid), (mid, y1)))
    return sorted(y1 for (_, y1) in segs)


def enclosure(F, cuts):
    """The checker's sums for the single strip (0, 1] cut at `cuts`, as exact rationals."""
    L = H = 0
    y0 = 0
    for y1 in cuts:
        a, b = seg_sums(F, y0, y1)
        L, H, y0 = L + a, H + b, y1
    return Fraction(L, S ** 3), Fraction(H, S ** 3)


# --- output ------------------------------------------------------------------------------

HEADER = """/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Numerics.BoxQuadrature
"""


def dec(q, digits=9, up=False):
    """The exact rational `q` as a decimal with `digits` places, rounded down (or up)."""
    n = q.numerator * 10 ** digits
    n = cdiv(n, q.denominator) if up else n // q.denominator
    sign, n = ("-", -n) if n < 0 else ("", n)
    return f"{sign}{n // 10 ** digits}.{n % 10 ** digits:0{digits}d}"


def render(name, k, lo, hi, cuts, L, H):
    a = f"1/{10 ** k}"
    lines = [HEADER]
    lines.append(f"""/-!
# Box partition for the Pauli remainder at `m_γ = m/{10 ** k}` (generated data)

Generated by `scripts/numerics/gen_pauli_certificates.py`; do not edit. Replay: run
`python3 scripts/numerics/gen_pauli_certificates.py --check` from the repository root, which
regenerates this file and compares it byte for byte (see `certificates/README.md`).

Semantics: one strip `x ∈ (0, 1]` cut at the heights `y = n / 2⁶⁴` for `n` in
`pauli{name}Cuts` ({len(cuts)} boxes). `QED.Numerics.PauliEnclosures` checks it with
`QED.Numerics.Quadrature.check` for the extension `QED.Numerics.Pauli.remExt` of the remainder
`2(1 - y)(1 - T_A + T_B)` at `A = a²`, `B = 1/a²`, `c = 1/10⁴`, `a = {a}`, with the claimed
bounds `[{lo[0]}/{lo[1]}, {hi[0]}/{hi[1]}]`. The checker's enclosure, computed exactly by the
generator, is `[{dec(L)}, {dec(H, up=True)}]` (rounded outward to 9 places).
-/

@[expose] public section

namespace QED.Numerics.Certificates

/-- The cut heights of the single strip, scaled by `2⁶⁴` (generated). -/
noncomputable def pauli{name}Cuts : List ℕ := [""")
    body, line = [], "   "
    for i, c in enumerate(cuts):
        item = f" {c}" + ("," if i + 1 < len(cuts) else "]")
        if len(line) + len(item) > 100:
            body.append(line)
            line = "   "
        line += item
    body.append(line)
    lines.append("\n".join(body))
    lines.append(f"""
/-- The box partition: one strip `x ∈ (0, 1]` cut at `pauli{name}Cuts` (generated). -/
noncomputable def pauli{name}Partition : List Strip :=
  [⟨{S}, pauli{name}Cuts⟩]

end QED.Numerics.Certificates

end
""")
    return "\n".join(lines)


def generate():
    out = {}
    for name, k, lo, hi, target in POINTS:
        F = make_rem_ext(k)
        cuts = greedy_cuts(F, target)
        L, H = enclosure(F, cuts)
        flo, fhi = Fraction(*lo), Fraction(*hi)
        accepted = flo <= L and H <= fhi
        print(f"Pauli{name}: k={k} boxes={len(cuts)} "
              f"enclosure=[{dec(L, 12)}, {dec(H, 12, up=True)}] "
              f"claim=[{dec(flo, 4)}, {dec(fhi, 4)}] margins=({dec(L - flo, 6)}, "
              f"{dec(fhi - H, 6)}) accepted={accepted}")
        if not accepted:
            raise SystemExit(f"Pauli{name}: the partition does not certify the claim")
        out[OUT_DIR / f"Pauli{name}.lean"] = render(name, k, lo, hi, cuts, L, H)
    return out


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="regenerate and compare with the files on disk instead of writing")
    args = parser.parse_args(argv)
    files = generate()
    if args.check:
        bad = [p for p, text in files.items()
               if not p.exists() or p.read_text(encoding="utf-8") != text]
        for p in bad:
            print(f"MISMATCH: {p}", file=sys.stderr)
        print("certificates match" if not bad else "certificates differ")
        return 1 if bad else 0
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    for p, text in files.items():
        p.write_text(text, encoding="utf-8")
        print(f"wrote {p}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
