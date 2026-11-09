/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.WickModel.RegulatedAmplitude

/-!
# Provider for `QED.WickModel.vacuumPolarization_existsUnique`

Under development. This module will prove the frozen theorem goal
`QED.WickModel.vacuumPolarization_existsUnique`
(packet 6b-1, decision D-26) as
`QED.Provider.WickModel.vacuumPolarization_existsUnique`,
with the exact frozen statement. Until the frozen anchor is sealed, this module is quarantined:
only the frozen anchor file may import it (`scripts/check_frozen_anchors.py`). It must never
import the frozen anchor.
-/
