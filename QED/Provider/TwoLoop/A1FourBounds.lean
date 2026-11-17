/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.A1Four
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Provider for `QED.TwoLoop.a1Four_bounds`

Under development. This module will prove the frozen theorem goal
`QED.TwoLoop.a1Four_bounds` (packet T2, decision D-39) as
`QED.Provider.TwoLoop.a1Four_bounds`, with the binder convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
