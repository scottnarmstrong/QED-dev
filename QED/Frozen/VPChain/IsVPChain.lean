/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Contraction

@[expose] public section

open QED.WickModel (Contraction)

namespace QED.VPChain

/-- (C₁) **The vacuum-polarization chains with `n` insertions** (decision D-49.4; plan section 3(b),
Q3 option (i), O3-3): the contraction `C` of the vertex function `⟨Ψ(x) Ψ̄(y) A(z)⟩` is the
one-loop vertex whose internal photon is dressed by a chain of `n` insertions, each a closed
fermion loop with two vertices (a second-order vacuum-polarization bubble) or a `photonCt` vertex
(its `δ₃` counterterm partner). For `n = 2` this is the sixth-order set (b) of AKN Fig. 3, p. 9
(one diagram), together with its counterterm graphs (bubble–`δ₃`, `δ₃`–bubble, `δ₃`–`δ₃`); for
`n = 3` it is the eighth-order I(a) of AKN Fig. 4 with its partners; `n = 1` is the
vacuum-polarization class of the order-`e⁵` vertex with its `δ₃` class, and `n = 0` the one-loop
vertex. Explicitly, there are fermion vertices `a, b, c`, a photon field `sb` and photon fields
`src i`, `dst i` (`i ≤ n`) such that:
* **the open line** is `Ψ̄(y) → c → b → a → Ψ(x)` (X₃): the external `Ψ(x)` is contracted with
  the `Ψ̄` of `a`, the `Ψ` of `a` with the `Ψ̄` of `b`, the `Ψ` of `b` with the `Ψ̄` of `c`, and the
  `Ψ` of `c` with the external `Ψ̄(y)`; the three are `gauge` vertices;
* **the external photon** `A(z)` is contracted with the photon field `sb` of the middle vertex `b`;
* **the chain**: for each `i ≤ n` the photon fields `src i` and `dst i` are contracted (the
  internal photon line `i`); `src 0` is the photon field of `a` and `dst n` that of `c`;
* **the insertions**: for each `i < n`, the fields `dst i` (where photon line `i` ends) and
  `src (i + 1)` (where photon line `i + 1` starts) belong either to two distinct `gauge` vertices
  `u, w` whose fermion fields form a closed loop `u → w → u` (the `Ψ` of each contracted with the
  `Ψ̄` of the other), or to one `photonCt` vertex, as its two distinct fields;
* **no other vertex**: every vertex is `a`, `b`, `c` or a vertex of an insertion.

The predicate fixes every field contraction of `C`, so a contraction satisfying it is determined
by its kind sequence and the data above. Conversely the data are determined by `C`: the open line
by the fermion pairing from `Ψ(x)`, and the chain by the alternating walk from the photon field of
`a`, which takes the photon partner (the involution `C.1.2`) and then the other field of the
insertion (the insertion partner, also an involution); a walk alternating two involutions from an
end point is a simple path, so it ends at the photon field of `c` and visits each insertion once
(to be proved, O3-4). It is invariant under
relabelling the vertices and under exchanging the two fields of a `photonCt` vertex. Both
orientations of each insertion occur (which vertex of a bubble, which field of a `photonCt`, faces
`a`), as distinct contractions; the `photonCt` factor (V₁₉) is half the counterterm rule, so its two
field pairings together give the rule once. It implies one-particle irreducibility (X₁₈), total
order `2n + 3` in `e` (V₁), `1 + #bubbles` loops (T₂), and fermionic sign `(-1)^{#bubbles}` (X₅)
(to be proved, O3-4; checked on representatives).
Only gauge vertices and `photonCt` vertices occur, so the counterterms `δ₁, δ₂, δ_m` do not enter.
The source counts one sixth-order diagram (AKN Fig. 3 (b)) and the counterterm graphs of the
on-shell scheme; obligation O3-4 shows the predicate to be the relabelling orbit of explicit
representatives, each orbit with `N!` elements (no automorphism). -/
def IsVPChain (n : ℕ) {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) : Prop :=
  ∃ (a b c : Wick.FermionVertex κ) (sb : Wick.PhotonSlot κ)
    (src dst : Fin (n + 1) → Wick.PhotonSlot κ),
    κ a.1 = .gauge ∧ κ b.1 = .gauge ∧ κ c.1 = .gauge ∧
    C.1.1 (.inl 0) = .inr a ∧ C.1.1 (.inr a) = .inr b ∧ C.1.1 (.inr b) = .inr c ∧
    C.1.1 (.inr c) = .inl 0 ∧
    sb.1 = b.1 ∧ C.1.2 (.inl 0) = .inr sb ∧
    (src 0).1 = a.1 ∧ (dst (Fin.last n)).1 = c.1 ∧
    (∀ i, C.1.2 (.inr (src i)) = .inr (dst i)) ∧
    (∀ i : Fin n,
      (κ (dst i.castSucc).1 = .gauge ∧ κ (src i.succ).1 = .gauge ∧
        (dst i.castSucc).1 ≠ (src i.succ).1 ∧
        ∃ u w : Wick.FermionVertex κ, u.1 = (dst i.castSucc).1 ∧ w.1 = (src i.succ).1 ∧
          C.1.1 (.inr u) = .inr w ∧ C.1.1 (.inr w) = .inr u) ∨
      (κ (dst i.castSucc).1 = .photonCt ∧ (src i.succ).1 = (dst i.castSucc).1 ∧
        src i.succ ≠ dst i.castSucc)) ∧
    ∀ t : Fin N, t = a.1 ∨ t = b.1 ∨ t = c.1 ∨
      ∃ i : Fin n, t = (dst i.castSucc).1 ∨ t = (src i.succ).1

end QED.VPChain

end
