/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.SourceMagneticMoment
public import QED.Frozen.OneLoop.IsResponseMagneticMoment

/-!
# Provider for `QED.OneLoop.integrable_and_tendsto_sourceMagneticMoment`

Under development. This module will prove the frozen theorem goal
`QED.OneLoop.integrable_and_tendsto_sourceMagneticMoment`
(packet 4b, decision D-18) as
`QED.Provider.OneLoop.integrable_and_tendsto_sourceMagneticMoment`,
with the exact frozen statement. Until the frozen anchor is sealed, this module is quarantined:
only the frozen anchor file may import it (`scripts/check_frozen_anchors.py`). It must never
import the frozen anchor.
-/
