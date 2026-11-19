/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.GradedOrder
public import QED.Frozen.Graded.RegulatedAmplitude
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.ExternalsAttached
public import QED.Frozen.WickModel.VerticesConnected
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable

/-!
# Provider for `QED.Graded.jointEnergyFirstIntegrable_connectedPart_five`

Under development. This module will prove the frozen theorem goal
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (Phase 5 Stage 2 packet, decision D-57)
as `QED.Provider.Graded.jointEnergyFirstIntegrable_connectedPart_five`, with the binder convention
of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
