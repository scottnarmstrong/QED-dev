/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Contraction
public import QED.Frozen.Graded.Grading

@[expose] public section

open QED.WickModel (Contraction)

namespace QED.ThreeLoop

/-- (Sc₃) **Sixth-order set (c) at order `7`: one vacuum-polarization element in the fourth-order
vertex, with its counterterm graphs** (decisions D-49.4, D-54.3 P3; plan sections 3 and 4 (c);
`SETC-KERNEL-PLAN.md` section 3, its row for `IsSetC`). Every `photonCt` vertex of `C` has level
`0`, and one of the following holds, where a vertex is *on the open line* if it is a fermion vertex
on the cycle of the fermion pairing through the external field `Ψ(x)`:
* **a `δ₃` element**: there is one `photonCt` vertex, and every other vertex is on the open line;
* **a bubble**: there are two `gauge` vertices `u ≠ w` whose fermion fields form a closed loop
  `u → w → u`, and every other vertex is on the open line;
* **a VP-share counterterm**: every vertex is on the open line, there is exactly one counterterm
  vertex, and it has level `1`.

In the family vertex (Gf₁) at total graded order `K = 7`, with the 1PI filter, this is exactly the
set (c) family (count by vertex orders and photon fields; the 1PI filter removes the graphs whose
bubble or `photonCt` sits on the external photon or whose internal lines include a bridge):
* with a bubble or `δ₃` element, the open line has order `5`: five `gauge` vertices joined by two
  internal photon lines, one carrying the element, which with 1PI are the six two-loop vertex
  skeletons other than the vacuum-polarization one (ladder, crossed, two corner, two self-energy
  graphs) with the element on either photon line: the 12 diagrams of set (c) (AKN Fig. 3 (c),
  p. 9) and their 12 level-`0` `δ₃` partners; or three `gauge` vertices and one level-`0`
  `fermionCt`, or two `gauge` vertices and one level-`0` `gaugeCt`: the one-loop vertex with a
  dressed photon and one level-`0` counterterm on the open line (the counterterm graphs of the
  inner subgraph when the element is on the outer photon line), 5 placements, each with a bubble
  or a `δ₃`;
* with a VP-share counterterm, the open line is the one-loop vertex with one level-`1` `gaugeCt`
  (at either end or in the middle) or one level-`1` `fermionCt` (on either internal line): the
  counterterm graphs of the two-loop subgraph when the element is on the inner photon line, 5
  placements. The level-`1` data are substituted by the VP share (Sc₂) in the headline (HS₆).

Excluded: a level-`1` `photonCt` (set (a)); two elements (set (b)); a closed loop with more than
two vertices, which belongs to set (d) (light-by-light) or is a Furry graph, or, as the two-loop
vacuum polarization in the one-loop vertex, to set (a); the graphs with no element and level-`0`
counterterms only, and the graphs with seven `gauge` vertices on the open line (set (e)). So set
(c) has 39 graphs and 56 relabelling orbits (each of the 17 graphs with a `photonCt` vertex gives
two orbits, one per field pairing), each orbit without automorphisms (to be proved). -/
def IsSetC {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (g : Graded.Grading κ) : Prop :=
  (∀ t : Graded.CtVertex κ, κ t.1 = .photonCt → g t = 0) ∧
  ((∃ t₀ : Fin N, κ t₀ = .photonCt ∧ ∀ t : Fin N, t = t₀ ∨
      ∃ v : Wick.FermionVertex κ, v.1 = t ∧ (C.1.1).SameCycle (.inl 0) (.inr v)) ∨
    (∃ u w : Wick.FermionVertex κ, κ u.1 = .gauge ∧ κ w.1 = .gauge ∧ u ≠ w ∧
      C.1.1 (.inr u) = .inr w ∧ C.1.1 (.inr w) = .inr u ∧ ∀ t : Fin N, t = u.1 ∨ t = w.1 ∨
        ∃ v : Wick.FermionVertex κ, v.1 = t ∧ (C.1.1).SameCycle (.inl 0) (.inr v)) ∨
    ((∀ t : Fin N, ∃ v : Wick.FermionVertex κ, v.1 = t ∧ (C.1.1).SameCycle (.inl 0) (.inr v)) ∧
      ∃ t₀ : Graded.CtVertex κ, g t₀ = 1 ∧ ∀ t : Graded.CtVertex κ, t = t₀))

end QED.ThreeLoop

end
