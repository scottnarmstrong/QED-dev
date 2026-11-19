/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.CountertermsWithLevel
public import QED.Frozen.Graded.IsRenormalizedThrough

/-!
# Provider for `QED.Graded.existsUnique_withLevel_zero`

Under development. This module will prove the frozen theorem goal
`QED.Graded.existsUnique_withLevel_zero` (Phase 5 Stage 2 packet, decision D-57) as
`QED.Provider.Graded.existsUnique_withLevel_zero`, with the binder convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
