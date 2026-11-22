/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetD
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount

/-!
# Provider for `QED.ThreeLoop.exists_isSetD`

Under development. This module will prove the frozen theorem goal
`QED.ThreeLoop.exists_isSetD` (Phase 5 Stage 3d packet, decision D-59) as
`QED.Provider.ThreeLoop.exists_isSetD`, with the binder convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
