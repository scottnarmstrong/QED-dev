#!/usr/bin/env python3
"""Enumerate the order-5 Wick contractions of the frozen two-loop model (obligation O2-2).

This is an independent, faithful re-implementation of the frozen definitions of packet 6a
(`QED/Frozen/WickModel/`) and packet T1 (`QED/Frozen/TwoLoop/`), restricted to the vertex
function `nf = nA = 1`:

* `Wick.VertexKind` with `order` (g 1, gCt 3, fCt 2, pCt 2) and `photonSlots` (1, 1, 0, 2);
* `FermionVertex κ` = vertices that are not `photonCt`; `PhotonSlot κ` = pairs `(t, k)`,
  `k < photonSlots (κ t)`, with key `2 t + k`;
* `Contraction 1 1 κ` = (σ, τ) with σ a permutation of `{ext} ∪ FermionVertex κ` (σ a = b: the Ψ
  at a is contracted with the Ψ̄ at b) and τ a fixed-point-free involution of
  `{ext} ∪ PhotonSlot κ`;
* fermion line indexed by t with σ(t) = s a vertex: ends (tail, head) = (s, t), label t;
  photon line indexed by the smaller-key slot a of an internal pair (a, b): ends (a.t, b.t),
  label N + key a;
* `IsOnePI` = externals attached ∧ vertices connected ∧ no bridge (a self-loop is never a bridge);
* `fermionSign` = (-1)^|FermionVertex κ| · sign σ;
* `IsChord f`: the ends of f are joined by lines of label > label f; `loopCount` = #chords.

For every kind sequence of total order exactly 5 it counts the contractions, the 1PI ones, and
classifies the 1PI ones by graph shape (section 3.1-3.2 of docs/TWO-LOOP-DERIVATION.md), checking
that the fermion sign and the loop count are constant on each class and that every class has
exactly N!/(multiplicity of the kind sequence) members per sequence (no automorphisms).

Usage: python3 scripts/numerics/two_loop_enumeration.py [--json]
"""

from __future__ import annotations

import itertools
import json
import math
import sys
from collections import Counter, defaultdict

G, GCT, FCT, PCT = "g", "gCt", "fCt", "pCt"
ORDER = {G: 1, GCT: 3, FCT: 2, PCT: 2}
SLOTS = {G: 1, GCT: 1, FCT: 0, PCT: 2}
EXT = "ext"


def perm_sign(perm: dict) -> int:
    seen, sign = set(), 1
    for x in perm:
        if x in seen:
            continue
        n, y = 0, x
        while y not in seen:
            seen.add(y)
            y = perm[y]
            n += 1
        if n % 2 == 0:
            sign = -sign
    return sign


def involutions(elems: list):
    """Fixed-point-free involutions of `elems`, as dicts."""
    if not elems:
        yield {}
        return
    a, rest = elems[0], elems[1:]
    for i, b in enumerate(rest):
        for inv in involutions(rest[:i] + rest[i + 1:]):
            d = dict(inv)
            d[a], d[b] = b, a
            yield d


def contractions(kappa: tuple):
    fv = [t for t, k in enumerate(kappa) if k != PCT]
    ps = [(t, s) for t, k in enumerate(kappa) for s in range(SLOTS[k])]
    fdom = [EXT] + fv
    for img in itertools.permutations(fdom):
        sigma = dict(zip(fdom, img))
        for tau in involutions([EXT] + ps):
            yield sigma, tau


def key(a):
    return 2 * a[0] + a[1]


def lines(kappa, sigma, tau):
    """Internal lines as (label, tail, head, kind, index)."""
    n = len(kappa)
    out = []
    for t, s in sigma.items():
        if t != EXT and s != EXT:
            out.append((t, s, t, "f", t))
    for a, b in tau.items():
        if a != EXT and b != EXT and key(a) < key(b):
            out.append((n + key(a), a[0], b[0], "p", a))
    return out


def connected(n, edges, u, w):
    adj = defaultdict(set)
    for (_, x, y, _, _) in edges:
        adj[x].add(y)
        adj[y].add(x)
    seen, stack = {u}, [u]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return w in seen


def is_one_pi(kappa, sigma, tau):
    n = len(kappa)
    if sigma[EXT] == EXT or tau[EXT] == EXT:
        return False
    ls = lines(kappa, sigma, tau)
    if not all(connected(n, ls, 0, w) for w in range(n)):
        return False
    for f in ls:
        rest = [g for g in ls if g is not f]
        if not connected(n, rest, f[1], f[2]):
            return False
    return True


def fermion_sign(kappa, sigma):
    nfv = sum(1 for k in kappa if k != PCT)
    return (-1) ** nfv * perm_sign(sigma)


def loop_count(kappa, sigma, tau):
    ls = lines(kappa, sigma, tau)
    return sum(
        1 for f in ls if connected(len(kappa), [g for g in ls if g[0] > f[0]], f[1], f[2])
    )


def fermion_cycles(sigma):
    """Open line (vertex order in the direction of fermion flow, from the incoming electron
    y to the outgoing x) and the closed loops (each in flow order)."""
    inv = {b: a for a, b in sigma.items()}
    # flow s -> t when sigma(t) = s; the first vertex is t with sigma(t) = ext
    openl, x = [], inv[EXT]
    while x != EXT:
        openl.append(x)
        x = inv[x]
    rest = set(sigma) - set(openl) - {EXT}
    loops = []
    while rest:
        start = min(rest)
        cyc, x = [], start
        while True:
            cyc.append(x)
            rest.discard(x)
            x = inv[x]
            if x == start:
                break
        loops.append(cyc)
    return openl, loops


def classify(kappa, sigma, tau):
    """Class name of a 1PI contraction of total order 5."""
    openl, loops = fermion_cycles(sigma)
    ext_vertex = tau[EXT][0]
    # photon lines between vertices, as unordered vertex pairs, keeping slot data for pCt
    plines = [(a, b) for a, b in tau.items() if a != EXT and b != EXT and key(a) < key(b)]
    pos = {v: i + 1 for i, v in enumerate(openl)}
    cts = [t for t, k in enumerate(kappa) if k != G]
    if not cts:
        if not loops:
            j = pos[ext_vertex]
            pairing = sorted(tuple(sorted((pos[a[0]], pos[b[0]]))) for a, b in plines)
            table = {
                (3, ((1, 5), (2, 4))): "L",
                (3, ((1, 4), (2, 5))): "X",
                (2, ((1, 4), (3, 5))): "C+",
                (4, ((1, 3), (2, 5))): "C-",
                (2, ((1, 5), (3, 4))): "S+",
                (4, ((1, 5), (2, 3))): "S-",
            }
            return table.get((j, tuple(pairing)), f"open?{j}{pairing}")
        if len(loops) == 1 and len(loops[0]) == 2 and len(openl) == 3:
            assert pos.get(ext_vertex) == 2
            return "VP"
        if len(loops) == 1 and len(loops[0]) == 3 and len(openl) == 2:
            loop = loops[0]
            assert ext_vertex in loop
            # loop vertex photon-joined to v1 (incoming open-line vertex)
            partner = {}
            for a, b in plines:
                partner[a[0]] = b[0]
                partner[b[0]] = a[0]
            a1 = partner[openl[0]]
            i = loop.index(ext_vertex)
            # flow order in `loop`: loop[i] -> loop[i+1]
            return "F+" if loop[(i + 1) % 3] == a1 else "F-"
        return f"other:{openl}:{loops}"
    # one counterterm vertex in a one-loop vertex graph
    assert len(cts) == 1 and not loops, (kappa, openl, loops)
    c = cts[0]
    k = kappa[c]
    if k == GCT:
        # open line of three vertices, photon at position 2
        return f"d1@v{pos[c]}"
    if k == FCT:
        # open line of four vertices; the fCt splits an internal line of the triangle
        # (v1 -> photon vertex: incoming line; photon vertex -> v3: outgoing line)
        return "d2m@in" if pos[c] < pos[ext_vertex] else "d2m@out"
    if k == PCT:
        # the pCt sits on the internal photon line; record which of its slots meets v1
        for a, b in plines:
            if c in (a[0], b[0]):
                other, slot = (b[0], a[1]) if a[0] == c else (a[0], b[1])
                if other == openl[0]:
                    return f"d3:slot{slot}@v1"
        return "d3?"
    return "ct?"


def kind_sequences(total=5):
    kinds = [G, GCT, FCT, PCT]
    for n in range(0, total + 1):
        for kappa in itertools.product(kinds, repeat=n):
            if sum(ORDER[k] for k in kappa) == total:
                yield kappa


def main():
    as_json = "--json" in sys.argv
    rows = []
    grand = Counter()
    for kappa in kind_sequences(5):
        n = len(kappa)
        total = attached_conn = onepi = 0
        classes = Counter()
        signs = defaultdict(set)
        loopc = defaultdict(set)
        for sigma, tau in contractions(kappa):
            total += 1
            if not is_one_pi(kappa, sigma, tau):
                continue
            onepi += 1
            c = classify(kappa, sigma, tau)
            classes[c] += 1
            signs[c].add(fermion_sign(kappa, sigma))
            loopc[c].add(loop_count(kappa, sigma, tau))
        for c in classes:
            grand[c] += classes[c]
        rows.append({
            "kappa": "".join({G: "g", GCT: "C", FCT: "f", PCT: "p"}[k] for k in kappa),
            "N": n,
            "contractions": total,
            "onePI": onepi,
            "classes": {c: {"count": classes[c], "sign": sorted(signs[c]),
                            "loops": sorted(loopc[c])} for c in sorted(classes)},
        })
    # with N! weighting, each class should total N! over all kind sequences
    if as_json:
        print(json.dumps({"rows": rows, "totals": dict(grand)}, indent=1))
        return
    print(f"{'kappa':8} {'N':>2} {'#contr':>7} {'#1PI':>5}  classes (count, sign, loops)")
    for r in rows:
        cl = ", ".join(f"{c}:{v['count']}({'+' if v['sign'] == [1] else '-' if v['sign'] == [-1] else v['sign']},L{v['loops']})"
                       for c, v in r["classes"].items())
        print(f"{r['kappa']:8} {r['N']:>2} {r['contractions']:>7} {r['onePI']:>5}  {cl}")
    print()
    print("Totals over kind sequences (each should be N! for its N):")
    for c, v in sorted(grand.items()):
        print(f"  {c:12} {v}")
    print("Number of kind sequences of order 5:", len(rows))
    print("Order-parity check: sequences of even order <= 4 with a contraction:",
          sum(1 for t in (2, 4) for kp in kind_sequences(t)
              for _ in itertools.islice(contractions(kp), 1)))


if __name__ == "__main__":
    main()
