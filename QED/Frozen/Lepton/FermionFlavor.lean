/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.Flavoring

@[expose] public section

namespace QED.Lepton

/-- (F₂) The flavour of a fermion field under the flavouring `φ`, the successor of (X₂): an
external field (`inl i`) has the open-line flavour, and the field of vertex `t` has flavour
`φ t`. -/
def fermionFlavor {F : Type} (Φ : Flavors F) {nf N : ℕ} {κ : Fin N → Wick.VertexKind}
    (φ : Flavoring Φ κ) : Fin nf ⊕ Wick.FermionVertex κ → F
  | .inl _ => Φ.openLine
  | .inr t => φ.1 t

end QED.Lepton

end
