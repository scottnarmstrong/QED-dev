/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.OnePIFunction
public import QED.Frozen.WickModel.OnePIFunction
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Provider for `QED.WickModel.onePIFunction₂_eq_onePIFunction`

Under development. This module will prove the frozen theorem goal
`QED.WickModel.onePIFunction₂_eq_onePIFunction` (packet T1, decision D-38) as
`QED.Provider.TwoLoop.onePIFunction₂_eq_onePIFunction`, with the binder convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
