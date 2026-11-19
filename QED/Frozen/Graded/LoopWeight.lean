/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.FermionFlavor
public import QED.Frozen.WickModel.ClosedLoop

@[expose] public section

open QED.WickModel (Contraction ClosedLoop)

namespace QED.Graded

open scoped Classical in
/-- (G₁‴) The regulator weight of the flavoured contraction `(C, φ)`, successor of (F₄): the
product over the closed fermion loops (X₆) of the coefficient of the loop's flavour, read off its
representative field. Only flavourings that `C` preserves (G₁″) enter (G₄), and for them the
flavour is constant on each loop. -/
noncomputable def loopWeight {F : Type} (Φ : Lepton.Flavors F) {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring F κ) : ℝ :=
  ∏ q : ClosedLoop C, Φ.coeff (fermionFlavor Φ φ q.1.out)

end QED.Graded

end
