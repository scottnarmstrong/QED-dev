/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.VPChain.IsVPChain

/-!
# Provider for `QED.ThreeLoop.not_isSetA_and_isVPChain_two`

Under development. This module will prove the frozen theorem goal
`QED.ThreeLoop.not_isSetA_and_isVPChain_two` (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.not_isSetA_and_isVPChain_two`, with the binder convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
