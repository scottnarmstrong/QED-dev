/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.IsPhotonOnShell
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.WickModel.IsPhotonOnShell
import QED.LeptonProof.EmbedRelabel

/-!
# Provider for `QED.Lepton.isPhotonOnShell_leptonFlavors_zero_iff`

Proves the frozen theorem goal `QED.Lepton.isPhotonOnShell_leptonFlavors_zero_iff` (Phase 5 Stage 0
packet, decision D-50) as `QED.Provider.Lepton.isPhotonOnShell_leptonFlavors_zero_iff`, with the
binder convention of decision D-13, from the helper in `QED.LeptonProof.EmbedRelabel`. This module
must never import the frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem isPhotonOnShell_leptonFlavors_zero_iff {P : QED.WickModel.Params}
    {H : Fin 0 → QED.Lepton.HeavyLepton}
    (hm : 0 < P.m := by assumption) (hM₁ : P.m < P.M₁ := by assumption)
    (hM₂ : P.m < P.M₂ := by assumption) (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption) :
    QED.Lepton.IsPhotonOnShell P (QED.Lepton.leptonFlavors P H) ↔
      QED.WickModel.IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂ :=
  QED.Lepton.Proof.isPhotonOnShell_leptonFlavors_zero_iff' P H hm hM₁ hM₂ hPV₁ hPV₂

end QED.Provider.Lepton

end
