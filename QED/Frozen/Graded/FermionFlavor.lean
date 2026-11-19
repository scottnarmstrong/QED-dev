/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.Flavoring
public import QED.Frozen.Lepton.Flavors

@[expose] public section

namespace QED.Graded

/-- (G₁′) The flavour of a fermion field under the flavouring `φ`, successor of (F₂): an external
field (`inl i`) has the open-line flavour `Φ.openLine`, and the field of vertex `t` has flavour
`φ t`. -/
def fermionFlavor {F : Type} (Φ : Lepton.Flavors F) {nf N : ℕ} {κ : Fin N → Wick.VertexKind}
    (φ : Flavoring F κ) : Fin nf ⊕ Wick.FermionVertex κ → F
  | .inl _ => Φ.openLine
  | .inr t => φ t

end QED.Graded

end
