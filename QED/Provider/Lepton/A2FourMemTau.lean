/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.A2Four
import QED.LeptonProof.CoeffA2Four

/-!
# Provider for `QED.Lepton.a2Four_mem_tau`

Proves the frozen theorem goal `QED.Lepton.a2Four_mem_tau` (Phase 5 Stage 0 packet, decision D-50)
as `QED.Provider.Lepton.a2Four_mem_tau`, with the binder convention of decision D-13, from the
helper in `QED.LeptonProof.CoeffA2Four`. This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem a2Four_mem_tau {y : ℝ}
    (hy : y ∈ Set.Icc (0.000287566 : ℝ) 0.000287604 := by assumption) :
    QED.Lepton.a2Four y ∈ Set.Icc (1.8376e-9 : ℝ) 1.8382e-9 :=
  QED.Lepton.Proof.a2Four_mem_tau' y hy

end QED.Provider.Lepton

end
