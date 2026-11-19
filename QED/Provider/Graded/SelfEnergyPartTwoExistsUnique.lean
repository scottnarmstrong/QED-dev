/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelfEnergyPart
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Provider for `QED.Graded.selfEnergyPart_two_existsUnique`

Under development. This module will prove the frozen theorem goal
`QED.Graded.selfEnergyPart_two_existsUnique` (Phase 5 Stage 2 packet, decision D-57) as
`QED.Provider.Graded.selfEnergyPart_two_existsUnique`, with the binder convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
