#!/usr/bin/env python3
"""Find the counterterm class representatives and relabelling permutations of the order-e^5
vertex (provenance of QED/TwoLoop/RelabelCountertermClasses.lean). NOT a proof: the Lean
file states each list identity and the kernel checks it (`decide +kernel`); this script only
proposed the representatives and permutations. It reuses the independent enumeration in
two_loop_enumeration.py.

Run: nice -n 10 python3 scripts/numerics/two_loop_counterterm_classes.py   (seconds)
"""
import sys, itertools
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import two_loop_enumeration as T
import two_loop_enumeration_lean as TL

S = {'g': T.G, 'C': T.GCT, 'f': T.FCT, 'p': T.PCT}
def kap(n): return tuple(S[c] for c in n)
def onepi(n):
    k = kap(n)
    return [(s, t) for s, t in T.contractions(k) if T.is_one_pi(k, s, t)]
def relabel(p, c):
    s, t = c
    fm = lambda x: x if x == T.EXT else p[x]
    sm = lambda a: a if a == T.EXT else (p[a[0]], a[1])
    return ({fm(a): fm(b) for a, b in s.items()}, {sm(a): sm(b) for a, b in t.items()})

CLS = {'d2m@in': 'd2In', 'd2m@out': 'd2Out', 'd3:slot0@v1': 'd3Slot0', 'd3:slot1@v1': 'd3Slot1',
       'd1@v1': 'd1At1', 'd1@v2': 'd1At2', 'd1@v3': 'd1At3'}
WANT = {'d2In': ([0, 3, 1, 2], 1), 'd2Out': ([0, 1, 3, 2], 1), 'd3Slot0': ([0, 1, 2], 1),
        'd3Slot1': ([0, 1, 2], 1), 'd1At1': ([2, 0, 1], 0), 'd1At2': ([0, 2, 1], 2),
        'd1At3': ([0, 1, 2], 1)}
DOC = {
 'd2In': "`δ₂`, `δ_m` on the incoming internal electron line: fermion flow `0 → 3 → 1 → 2` with the\n`fermionCt` vertex `3` between `v₁ = 0` and the external-photon vertex `1`; photon line `0 — 2`.",
 'd2Out': "`δ₂`, `δ_m` on the outgoing internal electron line: fermion flow `0 → 1 → 3 → 2` with the\n`fermionCt` vertex `3` between the external-photon vertex `1` and `v₃ = 2`; photon line `0 — 2`.",
 'd3Slot0': "`δ₃` on the internal photon, slot `0` of the `photonCt` vertex `3` towards `v₁`: fermion flow\n`0 → 1 → 2`, external photon at `1`, photon lines `0 — 3₀` and `2 — 3₁`.",
 'd3Slot1': "`δ₃` on the internal photon, slot `1` of the `photonCt` vertex `3` towards `v₁`: fermion flow\n`0 → 1 → 2`, external photon at `1`, photon lines `0 — 3₁` and `2 — 3₀`.",
 'd1At1': "`δ₁` at `v₁`: fermion flow `2 → 0 → 1` with the `gaugeCt` vertex `2` first, external photon at\n`0`, photon line `2 — 1`.",
 'd1At2': "`δ₁` at `v₂`, the external-photon vertex: fermion flow `0 → 2 → 1`, external photon at the\n`gaugeCt` vertex `2`, photon line `0 — 1`.",
 'd1At3': "`δ₁` at `v₃`: fermion flow `0 → 1 → 2` with the `gaugeCt` vertex `2` last, external photon at\n`1`, photon line `0 — 2`.",
}
groups = [(['gggf', 'ggfg', 'gfgg', 'fggg'], ['d2In', 'd2Out']),
          (['gggp', 'ggpg', 'gpgg', 'pggg'], ['d3Slot0', 'd3Slot1']),
          (['ggC', 'gCg', 'Cgg'], ['d1At1', 'd1At2', 'd1At3'])]
def R(name): return 'rep' + name[0].upper() + name[1:]

reps = {}; repseq = {}
for seqs, names in groups:
    rs = seqs[0]; rk = kap(rs)
    for c in onepi(rs):
        name = CLS[T.classify(rk, *c)]
        openl, _ = T.fermion_cycles(c[0])
        if (openl, c[1][T.EXT][0]) == WANT[name]:
            assert name not in reps
            reps[name] = c; repseq[name] = rs
assert len(reps) == 7

repdefs = []
for seqs, names in groups:
    for name in names:
        rs = repseq[name]; c = reps[name]
        term = (f"⟨({TL.sigma_term(kap(rs), c[0])},\n    {TL.tau_term(kap(rs), c[1])}), by decide +kernel⟩").replace('@@', f'k_{rs}')
        import textwrap
        doc = textwrap.fill("The representative of the class " + DOC[name].replace("\n", " ") + " -/", 96, initial_indent="/-- ", subsequent_indent="")
        repdefs.append(f"{doc}\ndef {R(name)} : Contraction 1 1 k_{rs} :=\n  {term}\n")
        repdefs.append(f"theorem {R(name)}_mem : {R(name)} ∈ onePI_{rs} := by decide +kernel\n")
        repdefs.append(f"theorem {R(name)}_isOnePI : IsOnePI {R(name)} := (isOnePI_iff_{rs} _).mpr {R(name)}_mem\n")

eqs = []; vals = []
for seqs, names in groups:
    for ts in seqs:
        tk = kap(ts); N = len(tk); terms = []; counts = {n: 0 for n in names}
        for c2 in onepi(ts):
            found = []
            for name in names:
                c = reps[name]; rk = kap(repseq[name])
                for p in itertools.permutations(range(N)):
                    if all(tk[p[t]] == rk[t] for t in range(N)) and relabel(p, c) == c2:
                        found.append((name, p))
            assert len(found) == 1, (ts, found)
            name, p = found[0]
            assert CLS[T.classify(tk, *c2)] == name
            counts[name] += 1
            inv = [p.index(i) for i in range(N)]
            terms.append(f"relabelK (permK ![{', '.join(map(str, p))}] ![{', '.join(map(str, inv))}]) (by decide +kernel) {R(name)}")
        eqs.append(f"/-- The 1PI contractions of `{ts}` are relabellings of the representatives. -/\n"
                   f"theorem onePI_{ts}_eq_relabelK : onePI_{ts} =\n    [" + ",\n      ".join(terms) + "] := by\n  decide +kernel\n")
        rhs = " +\n      ".join(f"{counts[n]} * contractionValue₂ P {R(n)} pOut pIn kIn αOut βIn μ" for n in names)
        hs = ",\n    ".join(f"value_relabelK P hmom {R(n)}_isOnePI" for n in names)
        vals.append(f"theorem listValue_{ts} (P : Params) {{pOut pIn kIn : Fin 1 → Fin 4 → ℝ}}\n"
                    f"    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :\n"
                    f"    listValue P onePI_{ts} pOut pIn kIn αOut βIn μ =\n      {rhs} := by\n"
                    f"  rw [listValue, onePI_{ts}_eq_relabelK]\n"
                    f"  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,\n    {hs}]\n"
                    f"  ring\n")
        print(ts, counts, file=sys.stderr)
open('reps.lean', 'w').write("\n".join(repdefs))
open('eqs.lean', 'w').write("\n".join(eqs))
open('vals.lean', 'w').write("\n".join(vals))
