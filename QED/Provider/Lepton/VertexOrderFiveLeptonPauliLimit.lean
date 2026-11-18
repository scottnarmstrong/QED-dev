/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.IsVertexOrderFiveLimit
public import QED.Frozen.Lepton.IsPhotonOnShell
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.Lepton.A2Four
public import QED.Frozen.TwoLoop.A1Four
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.IsFormFactorPair

/-!
# Provider for `QED.Lepton.isFormFactorPair_vertexOrderFive_lepton_pauli_limit`

Under development. This module will prove the frozen theorem goal
`QED.Lepton.isFormFactorPair_vertexOrderFive_lepton_pauli_limit` (Phase 5 Stage 0 packet, decision
D-50) as `QED.Provider.Lepton.isFormFactorPair_vertexOrderFive_lepton_pauli_limit`, with the binder
convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
