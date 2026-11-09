/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.VertexKindPhotonSlots

@[expose] public section

namespace QED.Wick

/-- (V₄) The photon fields of the vertices of `κ`: the field `⟨t, k⟩` is the `k`-th photon field of
vertex `t`. -/
abbrev PhotonSlot {N : ℕ} (κ : Fin N → VertexKind) : Type :=
  Σ t : Fin N, Fin (κ t).photonSlots

end QED.Wick

end
