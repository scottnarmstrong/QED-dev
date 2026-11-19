/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.FermionFlavor
public import QED.Frozen.WickModel.Contraction

@[expose] public section

open QED.WickModel (Contraction)

namespace QED.Graded

/-- (G₁″) The contraction `C` preserves the flavouring `φ`, successor of (F₃): the free
propagator `⟨Ψ_f Ψ̄_g⟩` vanishes unless `f = g`. -/
def Preserves {F : Type} (Φ : Lepton.Flavors F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (φ : Flavoring F κ) : Prop :=
  ∀ a, fermionFlavor Φ φ (C.1.1 a) = fermionFlavor Φ φ a

end QED.Graded

end
