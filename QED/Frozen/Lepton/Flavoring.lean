/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.Flavors
public import QED.Frozen.Wick.FermionVertex

@[expose] public section

namespace QED.Lepton

/-- (F₁) A flavouring of a vertex sequence `κ` for the flavour data `Φ`: the successor of (X₁).
The flavour of the fermion fields `Ψ̄ Ψ` of each vertex that has them; the interaction has a
gauge vertex `e Ψ̄_f A̸ Ψ_f` for every flavour `f`, and the counterterm vertices act on the
open-line flavour. -/
abbrev Flavoring {F : Type} (Φ : Flavors F) {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  {φ : Wick.FermionVertex κ → F // ∀ t, κ t.1 ≠ .gauge → φ t = Φ.openLine}

end QED.Lepton

end
