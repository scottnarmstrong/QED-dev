/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.WickVertex
public import QED.Frozen.OneLoop.VertexFunction

/-!
# Provider for `QED.Wick.tendsto_wickVertex`

Under development. This module will prove the frozen theorem goal
`QED.Wick.tendsto_wickVertex`
(packet 5, decision D-20) as
`QED.Provider.Wick.tendsto_wickVertex`,
with the exact frozen statement. Until the frozen anchor is sealed, this module is quarantined:
only the frozen anchor file may import it (`scripts/check_frozen_anchors.py`). It must never
import the frozen anchor.
-/
