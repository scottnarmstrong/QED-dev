/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Frozen.TwoLoop.RegulatedAmplitude
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount

/-!
# Provider for `QED.VPChain.jointEnergyFirstIntegrable_vertexChain_two`

Under development. This module will prove the frozen theorem goal
`QED.VPChain.jointEnergyFirstIntegrable_vertexChain_two` (Phase 5 Stage 1a packet, decision D-53) as
`QED.Provider.VPChain.jointEnergyFirstIntegrable_vertexChain_two`, with the binder convention of
decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
