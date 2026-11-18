# Two-loop enumeration: the order-$e^5$ vertex contractions

[Campaign HQ](../README.md) · [Two-loop derivation](TWO-LOOP-DERIVATION.md) ·
[Decisions](campaign/DECISIONS.md)

**Status (2026-11-18):** obligation O2-2 (section 3 of
[TWO-LOOP-DERIVATION.md](TWO-LOOP-DERIVATION.md)), combinatorial part, proved in Lean at
fixed parameters. The relabelling invariance of the contraction value is also proved, so
each of the nine classes of five gauge vertices enters with coefficient one, under momentum
conservation (section 3, item 1). The counterterm contractions are not yet grouped into
classes (section 3, item 2). Not reviewed; nothing here is frozen.

The object is the order-exactly-5 part of the frozen two-loop 1PI function (T₁₁, D-38) for
the vertex, $n_f=n_A=1$:
`onePIFunction₂ P 1 1 5 … − onePIFunction₂ P 1 1 4 …`, the (HV₁) vertex of packet T3 (frozen
provisionally, D-41). It sums, over $N$, the kind sequences
$\kappa:\mathrm{Fin}\,N\to$ `VertexKind` of total order exactly 5 and their 1PI
contractions, each with $1/N!$ and its fermionic sign.

## 1. Inventory

Computed by `scripts/numerics/two_loop_enumeration.py`, an independent re-implementation of
the frozen `Contraction`, `Line`, `Line.label`, `Line.ends`, `IsBridge`, `IsOnePI`,
`fermionSign`, `IsChord` and `loopCount` (packet 6a, packet T1), enumerating every
contraction of every sequence. Kinds: `g` gauge (order 1), `C` gaugeCt (3), `f` fermionCt (2),
`p` photonCt (2). The 1PI sets, their sizes and signs, and the absence of any other 1PI
contraction are confirmed by the Lean kernel (section 2); the total numbers of contractions
and the loop counts are from the script only, except that the kernel also checks
`loopCount = 2` for the nine representatives of `ggggg`.

**Parity.** A contraction pairs the external photon with the vertex photon fields by a
fixed-point-free involution, so the number of vertex photon fields
$n_g+n_C+2n_p$ must be odd. It has the parity of the order $n_g+3n_C+2n_f+2n_p$, so with one
external photon every contributing term has odd order; sequences of order 2 or 4 have no
contraction at all. This is checked by the Python script only, not by the kernel; the Lean
proof does not need it, since it sums only the sequences of order exactly 5.

There are 28 sequences of order exactly 5:

| $\kappa$ | $N$ | contractions | 1PI | classes (count each, sign, loops) |
| --- | --- | --- | --- | --- |
| `ggggg` | 5 | 10800 | 1080 | L, X, C₊, C₋, S₊, S₋, VP, F₊, F₋: 120 each; sign $+1$ for L…S₋, $-1$ for VP, F₊, F₋; 2 loops |
| `gggf`, `ggfg`, `gfgg`, `fggg` | 4 | 360 each | 12 each | $\delta_2,\delta_m$ on the incoming internal electron line: 6; on the outgoing: 6; sign $+1$; 1 loop |
| `gggp`, `ggpg`, `gpgg`, `pggg` | 4 | 360 each | 12 each | $\delta_3$ on the internal photon, the slot `0` of `photonCt` towards $v_1$: 6; slot `1` towards $v_1$: 6; sign $+1$; 1 loop |
| `ggC`, `gCg`, `Cgg` | 3 | 72 each | 6 each | $\delta_1$ at $v_1$, $v_2$ (the external-photon vertex), $v_3$: 2 each; sign $+1$; 1 loop |
| `gff`, `fgf`, `ffg` | 3 | 24 each | 0 | trees |
| `gfp`, `gpf`, `fgp`, `fpg`, `pgf`, `pfg` | 3 | 18 each | 0 | trees |
| `gpp`, `pgp`, `ppg` | 3 | 30 each | 0 | trees |
| `Cf`, `fC`, `Cp`, `pC` | 2 | 6 each | 0 | trees |

Summed over the sequences with the same $N$, every class has exactly $N!$ members: 120 for
each of the nine classes of `ggggg`; 24 for each of $\delta_{2,m}$-in, $\delta_{2,m}$-out,
$\delta_3$-slot-0, $\delta_3$-slot-1; 6 for each of $\delta_1$ at $v_1,v_2,v_3$. So, as
section 3.3 predicts, no class has an automorphism. With the two $\delta_3$ slot pairings
counted as one class (D-24, V₁₉), these are the $9+6$ classes of sections 3.1–3.2. Nothing
else occurs: no tadpole, no contraction with two closed loops, no 1PI tree. All 1PI
contractions without a closed fermion loop have sign $+1$; those with one have sign $-1$.

The class names follow section 3.1, with vertices numbered along the fermion flow from the
incoming electron, $v_1,\dots,v_k$, and $v_j$ carrying the external photon. The
representatives used in Lean (`QED.TwoLoop.Enumeration.Class5.rep`) are tabulated in the
docstring of `QED/TwoLoop/EnumerationGauge5.lean`. F₊ is the Furry triangle whose fermion
flow runs from the external-photon vertex to the loop vertex joined to $v_1$; F₋ is the
other orientation.

## 2. What is proved in Lean

All checks run in the kernel (`decide +kernel`; no `native_decide`, no option overrides).
`IsOnePI` is decided through a proved Boolean characterization (`isOnePI_iff_onePIE`): the
line data (label, ends) of a contraction is computed once, and reachability is a fixed
number of closure steps, proved equal to `Relation.ReflTransGen`
(`reflTransGen_iff_mem_reachSet`). The naive instance (reachability through Mathlib's
`SimpleGraph.Reachable`) costs about 0.5 s per $N=5$ contraction; the characterization about
0.1 s.

**Files** (namespace `QED.TwoLoop.Enumeration`):

- `QED/TwoLoop/EnumerationDecide.lean` — the decision procedure for `IsOnePI` and `IsChord`.
- `QED/TwoLoop/EnumerationRelabel.lean` — relabelling the vertices of a contraction of gauge
  vertices: an action of $S_N$ that preserves `IsOnePI` and `fermionSign`.
- `QED/TwoLoop/EnumerationGauge5.lean` — the nine classes of five gauge vertices.
- `QED/TwoLoop/EnumerationCounterterm.lean` — the 27 other sequences (generated by
  `scripts/numerics/two_loop_enumeration_lean.py`; the script only proposes the lists, the
  kernel checks them).
- `QED/TwoLoop/EnumerationOrderFive.lean` — the assembly on `onePIFunction₂`.

**Five gauge vertices.** A direct `decide` over the 10800 contractions is out of reach (the
Mathlib `Fintype` of the subtype enumerates $6!\cdot6! = 518400$ pairs). The proof instead
uses the $S_5$ symmetry:

1. every fermion pairing becomes one of 32 normal forms after the relabelling read off from
   its cycles (`exists_std`, six kernel checks over the 720 pairings);
2. the 15 photon pairings are listed (`inv_mem`);
3. each of the $32\times15$ normal-form contractions that is 1PI is a relabelling of a
   representative (`classify_std`, four checks; 14 are 1PI);
4. a relabelling of a representative is a representative only trivially (`relabel_rep_eq`,
   $9\cdot9\cdot120$ cases);
5. relabelling preserves `IsOnePI` and `fermionSign` (hand proofs), so the checks transport.

**Theorems.**

```lean
theorem exists_rep_of_isOnePI {C : Contraction 1 1 (gauges 5)} (hC : IsOnePI C) :
    ∃ c : Class5, ∃ π : Equiv.Perm (Fin 5), C = relabel π c.rep

theorem relabel_rep_inj {c c' : Class5} {π π' : Equiv.Perm (Fin 5)}
    (h : relabel π c.rep = relabel π' c'.rep) : c = c' ∧ π = π'

theorem sum_isOnePI_gauges5 {instF : Fintype (Contraction 1 1 (gauges 5))}
    {instD : DecidablePred (IsOnePI (nf := 1) (nA := 1) (κ := gauges 5))}
    (G : Contraction 1 1 (gauges 5) → ℂ) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 (gauges 5))).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * G C =
      ∑ c : Class5, (c.sign : ℂ) * ∑ π : Equiv.Perm (Fin 5), G (relabel π c.rep)

theorem card_isOnePI_gauges5 … :
    ((Finset.univ : Finset (Contraction 1 1 (gauges 5))).filter IsOnePI).card = 1080

theorem sum_isOnePI_gauges5_of_invariant … (G : Contraction 1 1 (gauges 5) → ℂ)
    (hG : ∀ π C, G (relabel π C) = G C) :
    ∑ C ∈ … .filter IsOnePI, ((fermionSign C : ℤ) : ℂ) * G C =
      (Nat.factorial 5 : ℂ) * ∑ c : Class5, (c.sign : ℂ) * G c.rep
```

**Counterterm sequences.** For each of the 27 sequences `κ`: `isOnePI_iff_κ` (a contraction
is 1PI iff it is in the explicit list `onePI_κ`), `sign_κ` (all signs $+1$) and
`sum_isOnePI_κ` (the signed sum of any `G` over the 1PI contractions is the sum over the
list). Each sequence is checked over (all fermion pairings) × (the listed photon pairings),
with the photon list proved complete.

**Assembly.**

```lean
theorem onePIFunction₂_five_sub_four (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    onePIFunction₂ P 1 1 5 pOut pIn kIn αOut βIn μ - onePIFunction₂ P 1 1 4 pOut pIn kIn αOut βIn μ =
      (Nat.factorial 5 : ℂ)⁻¹ * ∑ c : Class5, (c.sign : ℂ) *
          ∑ π : Equiv.Perm (Fin 5), contractionValue₂ P (relabel π c.rep) pOut pIn kIn αOut βIn μ +
        (Nat.factorial 4 : ℂ)⁻¹ * (listValue P onePI_gggf … + ⋯ + listValue P onePI_pggg …) +
        (Nat.factorial 3 : ℂ)⁻¹ * (listValue P onePI_ggC … + listValue P onePI_gCg … +
          listValue P onePI_Cgg …)
```

and `onePIFunction₂_five_sub_four_of_invariant`, which, under the hypothesis that
`contractionValue₂ P (relabel π C) … = contractionValue₂ P C …` for contractions of five gauge
vertices, replaces the first term by `∑ c, sign c * contractionValue₂ P c.rep …`.

**O2-4.** For the 1PI function, tadpoles do not occur: they are absent from the complete
lists above (every 1PI contraction of order 5 is in one of the listed classes). The
statement for the connected and LSZ functions (tadpoles vanish) is analytic and not
addressed.

## 3. What remains

1. **Relabelling invariance of the value: proved.** For contractions of `N` gauge vertices
   with connected vertices and conserved external momenta,
   `contractionValue₂ P (relabel π C) … = contractionValue₂ P C …`
   (`QED/TwoLoop/RelabelInvariance.lean`, `contractionValue₂_relabel`, and
   `contractionValue₂_relabel_of_isOnePI` for 1PI contractions with
   `∑ pOut = ∑ pIn + ∑ kIn`). The routings of the two contractions differ by a unimodular
   integer change of the loop momenta plus a shift (`QED/TwoLoop/RoutingChange.lean`,
   `LineCorr.exists_routing_change`, O2-5 (ii)); the amplitudes agree under the line
   correspondence, including the flavour weights of closed loops; and the joint prescription
   is invariant under such maps for every integrand. Momentum conservation is needed, by the
   following argument (not a Lean theorem): without it the routing is not conserved and
   depends on the orientation of photon lines, which relabelling changes. Consequently, with
   momentum conservation, the order-5 vertex is
   `∑ c, sign c * contractionValue₂ P c.rep …` plus the counterterm terms, with coefficient one
   per class (`QED/TwoLoop/RelabelInvarianceOrderFive.lean`,
   `onePIFunction₂_five_sub_four_eq`).
2. **Counterterm classes by relabelling: proved.** A relabelling across kind sequences
   (`relabelK`, $\kappa\mapsto\kappa\circ\pi^{-1}$) preserves the contraction value for
   connected contractions with conserved external momenta, including the momentum-dependent
   `fermionCt` and two-slot `photonCt` vertex factors
   (`QED/TwoLoop/RelabelCountertermValue.lean`, `contractionValue₂_relabelK`). The eleven
   counterterm lists are, by kernel checks, relabellings of seven representatives (δ₂/δm on the
   incoming or outgoing internal electron line, δ₃ with either slot pairing, δ₁ at each of the
   three vertices), each class having exactly $N!$ members. Under momentum conservation the
   order-5 vertex is therefore the sum of the seven five-gauge classes L, X, C±, S±, VP with
   their signs and the seven counterterm classes, all with coefficient one
   (`QED/TwoLoop/RelabelCountertermClasses.lean`, `onePIFunction₂_five_sub_four_eq_classes`).
   The representatives and permutations were found by
   `scripts/numerics/two_loop_counterterm_classes.py`; the Lean proof does not rely on it.
3. **O2-3 (Furry pair): proved.** With momentum conservation, the two orientations of the
   closed three-vertex loop cancel at fixed parameters, flavour by flavour
   (`QED/TwoLoop/FurryPair.lean`, `furry_pair`), by charge conjugation with `C = γ⁰γ²`
   (`QED/Algebra/ChargeConjugation.lean`), which acts on the frozen index sums as a signed
   reindexing, and the reflection invariance of the joint prescription. The order-5 vertex is
   then the sum over the seven classes L, X, C±, S±, VP with coefficient one plus the
   counterterm contractions (`onePIFunction₂_five_sub_four_eq_furry`).

## 4. Replay and costs

```
python3 scripts/numerics/two_loop_enumeration.py          # inventory table, < 1 s
python3 scripts/numerics/two_loop_enumeration_lean.py > QED/TwoLoop/EnumerationCounterterm.lean
lake build QED.TwoLoop.EnumerationOrderFive
python3 scripts/numerics/two_loop_crosschecks.py furry   # charge conjugation, numerically, < 1 s
```

Measured on lemma.farm (niced, shared machine, 2026-11-17), with a watchdog at 8 GB:

| target | wall time | peak RSS |
| --- | --- | --- |
| `EnumerationDecide`, `EnumerationRelabel` | a few seconds each | < 2 GB |
| `EnumerationGauge5` (all kernel checks) | about 50–80 s | 3.5 GB |
| `EnumerationCounterterm` (27 sequences) | about 160 s | 3.4 GB |
| `EnumerationOrderFive` | about 10 s | 1.5 GB |
| the whole chain from a clean state of these five files | 224 s | 3.5 GB |

Abandoned designs, for the record: the frozen predicates decided through Mathlib's
`SimpleGraph.Reachable` cost 74 s and 11.7 GB for the 360 contractions of `gggf`; a single
kernel check of "every fermion pairing is conjugate to a normal form" by searching over
$S_5$ exceeded 8 GB and was stopped; the same check with the relabelling computed from the
cycles took 7.1 GB in one declaration and is split into six (`exists_std_*`).
