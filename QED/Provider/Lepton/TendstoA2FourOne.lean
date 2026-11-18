/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.A2Four
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import QED.LeptonProof.CoeffA2Four

/-!
# Provider for `QED.Lepton.tendsto_a2Four_one`

Proves the frozen theorem goal `QED.Lepton.tendsto_a2Four_one` (Phase 5 Stage 0 packet, decision
D-50) as `QED.Provider.Lepton.tendsto_a2Four_one`, with the binder convention of decision D-13, from
the helper in `QED.LeptonProof.CoeffA2Four`. This module must never import the frozen anchor.
-/

public section

open Filter Topology

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem tendsto_a2Four_one :
    Tendsto QED.Lepton.a2Four (𝓝[<] 1) (𝓝 (119 / 36 - Real.pi ^ 2 / 3)) :=
  QED.Lepton.Proof.tendsto_a2Four_one'

end QED.Provider.Lepton

end
