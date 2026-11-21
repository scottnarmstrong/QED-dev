/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetC
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount

/-!
# Provider for `QED.ThreeLoop.exists_isSetC`

Under development. This module will prove the frozen theorem goal
`QED.ThreeLoop.exists_isSetC` (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.exists_isSetC`, with the binder convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
