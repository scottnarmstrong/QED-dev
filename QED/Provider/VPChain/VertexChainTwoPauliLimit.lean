/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVertexChainLimit
public import QED.Frozen.VPChain.A1SixSetB
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.WickModel.IsPhotonOnShell
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.IsFormFactorPair

/-!
# Provider for `QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`

Under development. This module will prove the frozen theorem goal
`QED.VPChain.isFormFactorPair_vertexChain_two_pauli_limit` (Phase 5 Stage 1a packet, decision D-53)
as `QED.Provider.VPChain.isFormFactorPair_vertexChain_two_pauli_limit`, with the binder convention
of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
