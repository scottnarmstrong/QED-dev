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

/-- (A₁) **The one-loop vertex with one single-loop insertion on its photon: sixth-order set (a)
at order `7`** (decisions D-49.4, D-54.3 P3; plan section 3 (a); successor of (C₁) at one
insertion). The contraction `C` of the vertex function `⟨Ψ(x) Ψ̄(y) A(z)⟩` is the one-loop vertex
whose internal photon carries one two-photon insertion that is either a single closed fermion loop
or a single `photonCt` vertex. Explicitly, there are fermion vertices `a, b, c` and photon fields
`sa, sb, sc, x, y` such that:
* **the open line** is `Ψ̄(y) → c → b → a → Ψ(x)` (X₃), with three `gauge` vertices, exactly as
  in (C₁);
* **the external photon** `A(z)` is contracted with the photon field `sb` of `b`;
* **the photon of the one-loop vertex** leaves `a` through its field `sa`, contracted with `x`,
  and reaches `c` through its field `sc`, contracted with `y`;
* **the insertion** between `x` and `y` is either
  - a `photonCt` vertex, `x` and `y` being its two distinct fields, and there is no vertex
    other than `a`, `b`, `c` and it; or
  - a closed fermion loop: `x` and `y` are the photon fields of two vertices `u`, `w` on one cycle
    of the fermion pairing that contains no external field, and every vertex other than `a`, `b`,
    `c` is a fermion vertex on that cycle.

The predicate does not read the grading. In the family vertex (Gf₁) at total graded order
`K = 7` the open line has order `3`, so the insertion has order exactly `4`, and the order fixes
both its shape and its levels. Since `gauge` and `gaugeCt` vertices have one photon field each and
the loop carries `x` and `y`, the possible loops are: four `gauge` vertices, the two not carrying
`x`, `y` joined by an internal photon (the three two-loop vacuum-polarization graphs of order
`e⁴`: the self-energy insertion on either line of the bubble, and the vertex-type graph); two
`gauge` vertices and one level-`0` `fermionCt` vertex on either line (the `δ₂`, `δ_m`
counterterm graphs of the two-loop bubble); one `gauge` and one level-`0` `gaugeCt` vertex, the
latter carrying `x` or `y` (the `δ₁` counterterm graphs). A `photonCt` insertion has order `4` only
at level `1`: it is the order-`e⁴` photon counterterm `δ₃⁽⁴⁾`. So at `K = 7` the family is the
sixth-order set (a) of AKN Fig. 3, p. 9 (three diagrams: the fourth-order vacuum polarization
inserted in the second-order vertex), together with its counterterm graphs: the level-`0`
counterterms inside the loop and the level-`1` photon counterterm. Every flavour of a loop is
summed inside the value (G₄), with the counterterms of its block. Counterterms on the open line
and second insertions (set (b), set (c)) are excluded: every vertex is `a`, `b`, `c` or in the
insertion. The predicate is invariant under relabelling the vertices and under exchanging the two
fields of a `photonCt` vertex; both field pairings of the `photonCt` insertion occur as distinct
contractions, and the `photonCt` factor (V₁₉) is half the counterterm rule, as in (C₁). At
`K = 5` the same predicate gives the vacuum-polarization class of the order-`e⁵` vertex with its
level-`0` `δ₃` class (that is, `IsVPChain 1`). The relabelling orbits at `K = 7` are to be
enumerated as for (C₁) (obligation of the Stage 3a proof): three two-loop-bubble orbits, two
`fermionCt` orbits, two `gaugeCt` orbits and the `photonCt` insertion with its two field pairings,
each orbit without automorphisms. -/
def IsSetA {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) : Prop :=
  ∃ (a b c : Wick.FermionVertex κ) (sa sb sc x y : Wick.PhotonSlot κ),
    κ a.1 = .gauge ∧ κ b.1 = .gauge ∧ κ c.1 = .gauge ∧
    C.1.1 (.inl 0) = .inr a ∧ C.1.1 (.inr a) = .inr b ∧ C.1.1 (.inr b) = .inr c ∧
    C.1.1 (.inr c) = .inl 0 ∧
    sb.1 = b.1 ∧ C.1.2 (.inl 0) = .inr sb ∧
    sa.1 = a.1 ∧ sc.1 = c.1 ∧ C.1.2 (.inr sa) = .inr x ∧ C.1.2 (.inr sc) = .inr y ∧
    ((κ x.1 = .photonCt ∧ y.1 = x.1 ∧ y ≠ x ∧
        ∀ t : Fin N, t = a.1 ∨ t = b.1 ∨ t = c.1 ∨ t = x.1) ∨
      ∃ u w : Wick.FermionVertex κ, u.1 = x.1 ∧ w.1 = y.1 ∧
        (∀ i : Fin 1, ¬ (C.1.1).SameCycle (.inl i) (.inr u)) ∧
        (C.1.1).SameCycle (.inr u) (.inr w) ∧
        ∀ t : Fin N, t = a.1 ∨ t = b.1 ∨ t = c.1 ∨
          ∃ v : Wick.FermionVertex κ, v.1 = t ∧ (C.1.1).SameCycle (.inr u) (.inr v))

end QED.ThreeLoop

end
