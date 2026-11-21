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

/-- (Sc₁) **The one-loop self-energy with one insertion on its photon** (the self-energy analogue
of (C₁) of Stage 1a at `n = 1`): the contraction `C` of `⟨Ψ(x) Ψ̄(y)⟩` is the one-loop self-energy
whose internal photon carries one second-order vacuum-polarization bubble or one `photonCt`
vertex. Explicitly, there are `gauge` vertices `a`, `c` and photon fields `sa, sc, x, y` such
that the open line is `Ψ̄(y) → c → a → Ψ(x)`; the photon leaves `a` through `sa`, contracted with
`x`, and reaches `c` through `sc`, contracted with `y`; and between `x` and `y` there is either a
`photonCt` vertex (`x`, `y` its two distinct fields) or a closed loop `u → w → u` of two `gauge`
vertices carrying `x` and `y`; there is no other vertex. At total graded order `4` a `photonCt`
insertion has level `0`, so this is the order-`e⁴` self-energy graph with the electron bubble
(every flavour summed inside the value) and its level-`0` `δ₃` partner: the vacuum-polarization
family of the order-`e⁴` self-energy. -/
def IsVPSelfEnergy {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 0 κ) : Prop :=
  ∃ (a c : Wick.FermionVertex κ) (sa sc x y : Wick.PhotonSlot κ),
    κ a.1 = .gauge ∧ κ c.1 = .gauge ∧
    C.1.1 (.inl 0) = .inr a ∧ C.1.1 (.inr a) = .inr c ∧ C.1.1 (.inr c) = .inl 0 ∧
    sa.1 = a.1 ∧ sc.1 = c.1 ∧ C.1.2 (.inr sa) = .inr x ∧ C.1.2 (.inr sc) = .inr y ∧
    ((κ x.1 = .photonCt ∧ y.1 = x.1 ∧ y ≠ x ∧ ∀ t : Fin N, t = a.1 ∨ t = c.1 ∨ t = x.1) ∨
      (κ x.1 = .gauge ∧ κ y.1 = .gauge ∧ x.1 ≠ y.1 ∧
        (∃ u w : Wick.FermionVertex κ, u.1 = x.1 ∧ w.1 = y.1 ∧ C.1.1 (.inr u) = .inr w ∧
          C.1.1 (.inr w) = .inr u) ∧
        ∀ t : Fin N, t = a.1 ∨ t = c.1 ∨ t = x.1 ∨ t = y.1))

end QED.ThreeLoop

end
