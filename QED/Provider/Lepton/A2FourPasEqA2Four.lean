/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.A2Four
public import QED.Frozen.Lepton.A2FourPas
import QED.LeptonProof.CoeffPas

/-!
# Provider for `QED.Lepton.a2FourPas_eq_a2Four`

Proves the frozen theorem goal `QED.Lepton.a2FourPas_eq_a2Four` (Phase 5 Stage 0 packet, decision
D-50) as `QED.Provider.Lepton.a2FourPas_eq_a2Four`, with the binder convention of decision D-13,
from the helper in `QED.LeptonProof.CoeffPas`. This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem a2FourPas_eq_a2Four {y : ℝ} (hy0 : 0 < y := by assumption) (hy1 : y < 1 := by assumption) :
    QED.Lepton.a2FourPas y = QED.Lepton.a2Four y :=
  QED.Lepton.Proof.a2FourPas_eq_a2Four' hy0 hy1

end QED.Provider.Lepton

end
