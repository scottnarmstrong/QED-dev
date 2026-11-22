/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Contraction

@[expose] public section

open QED.WickModel (Contraction)

namespace QED.ThreeLoop

/-- (Sd₁) **The one-loop vertex skeleton with a light-by-light scattering loop: sixth-order set
(d) at order `7`** (decisions D-49.4, D-54.1, D-54.3 P3; AKN Fig. 3 (d), p. 9). The contraction
`C` of the vertex function `⟨Ψ(x) Ψ̄(y) A(z)⟩` has only `gauge` vertices (no counterterm vertex),
and there are fermion vertices `a, b, c, u` and photon fields `sa, sb, sc, su, xa, xb, xc` such
that:
* **the open line** is `Ψ̄(y) → c → b → a → Ψ(x)` (X₃), exactly as in (A₁) and (C₁);
* **the loop**: `u` lies on a cycle of the fermion pairing that contains no external field (a
  closed fermion loop), and every vertex other than `a`, `b`, `c` lies on that cycle;
* **the external photon** `A(z)` is contracted with the photon field `su` of `u`, on the loop;
* **the three internal photons** join the photon fields `sa`, `sb`, `sc` of `a`, `b`, `c` to
  photon fields `xa`, `xb`, `xc` of vertices on the loop.

The predicate does not read the grading: with only `gauge` vertices there is no counterterm
vertex to grade. Since `C.1.2` is an involution, `su`, `xa`, `xb`, `xc` are four distinct photon
fields on the loop, and a `gauge` vertex has one photon field, so the loop has at least four
vertices. In the family vertex (Gf₁) at total graded order `K = 7` it has exactly four: the open
line has order `3` and the loop order `4`, and every photon field of the loop is `su`, `xa`, `xb`
or `xc`. So the loop is a four-photon fermion loop (light-by-light scattering) whose photons are
the external photon and the three photons of the open line, and the family at `K = 7` is the
sixth-order set (d) of AKN Fig. 3, p. 9: six diagrams, one for each order in which the loop's
fermion line, starting from `u`, meets the photons from `a`, `b`, `c` (the two orientations of a
loop are distinct contractions and distinct diagrams; a four-photon loop is not removed by
Furry's theorem). The set has no counterterm graph: it is ultraviolet finite as a sum over the
six orderings (the four-photon subgraph is finite by gauge invariance) and infrared finite. Every
flavour of the loop is summed inside the value (G₄), with the Pauli–Villars weights of its block.
Excluded: an external photon on the open line (sets (a), (b), (c), (e)); a loop with three
photons (Furry graphs, which cancel in pairs); counterterm vertices anywhere. The predicate is
invariant under relabelling the vertices. The relabelling orbits at `K = 7` are to be enumerated
(obligation of the Stage 3d proof): six orbits, each without automorphisms. At `K = 9` the same
predicate gives the light-by-light graphs with one internal photon inside the loop. -/
def IsSetD {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) : Prop :=
  (∀ t : Fin N, κ t = .gauge) ∧
  ∃ (a b c u : Wick.FermionVertex κ) (sa sb sc su xa xb xc : Wick.PhotonSlot κ),
    C.1.1 (.inl 0) = .inr a ∧ C.1.1 (.inr a) = .inr b ∧ C.1.1 (.inr b) = .inr c ∧
    C.1.1 (.inr c) = .inl 0 ∧
    (∀ i : Fin 1, ¬ (C.1.1).SameCycle (.inl i) (.inr u)) ∧
    (∀ t : Fin N, t = a.1 ∨ t = b.1 ∨ t = c.1 ∨
      ∃ v : Wick.FermionVertex κ, v.1 = t ∧ (C.1.1).SameCycle (.inr u) (.inr v)) ∧
    su.1 = u.1 ∧ C.1.2 (.inl 0) = .inr su ∧
    sa.1 = a.1 ∧ sb.1 = b.1 ∧ sc.1 = c.1 ∧
    C.1.2 (.inr sa) = .inr xa ∧ C.1.2 (.inr sb) = .inr xb ∧ C.1.2 (.inr sc) = .inr xc ∧
    ∃ va vb vc : Wick.FermionVertex κ, va.1 = xa.1 ∧ vb.1 = xb.1 ∧ vc.1 = xc.1 ∧
      (C.1.1).SameCycle (.inr u) (.inr va) ∧ (C.1.1).SameCycle (.inr u) (.inr vb) ∧
      (C.1.1).SameCycle (.inr u) (.inr vc)

end QED.ThreeLoop

end
