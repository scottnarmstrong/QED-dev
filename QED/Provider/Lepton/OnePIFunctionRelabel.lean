/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction
import QED.LeptonProof.EmbedRelabel

/-!
# Provider for `QED.Lepton.onePIFunction₂_relabel`

Proves the frozen theorem goal `QED.Lepton.onePIFunction₂_relabel` (Phase 5 Stage 0 packet, decision
D-50) as `QED.Provider.Lepton.onePIFunction₂_relabel`, with the binder convention of decision D-13,
from the helper in `QED.LeptonProof.EmbedRelabel`. This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem onePIFunction₂_relabel {P : QED.WickModel.Params} {F G : Type} [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G] {e : F ≃ G} {Φ : QED.Lepton.Flavors F} {Ψ : QED.Lepton.Flavors G}
    (hmass : ∀ f, Ψ.mass (e f) = Φ.mass f := by assumption)
    (hcoeff : ∀ f, Ψ.coeff (e f) = Φ.coeff f := by assumption)
    (hopen : e Φ.openLine = Ψ.openLine := by assumption) :
    QED.Lepton.onePIFunction₂ P Φ = QED.Lepton.onePIFunction₂ P Ψ :=
  QED.Lepton.Proof.onePIFunction₂_relabel' P e Φ Ψ hmass hcoeff hopen

end QED.Provider.Lepton

end
