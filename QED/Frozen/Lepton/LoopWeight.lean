/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ClosedLoop
public import QED.Frozen.Lepton.FermionFlavor

@[expose] public section

open QED.WickModel (Contraction ClosedLoop)

namespace QED.Lepton

open scoped Classical in
/-- (F₄) The regulator weight of the flavoured contraction `(C, φ)`, the successor of (X₇): the
product over the closed fermion loops (X₆) of the coefficient of the loop's flavour, read off its
representative field. -/
noncomputable def loopWeight {F : Type} (Φ : Flavors F) {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring Φ κ) : ℝ :=
  ∏ q : ClosedLoop C, Φ.coeff (fermionFlavor Φ φ q.1.out)

end QED.Lepton

end
