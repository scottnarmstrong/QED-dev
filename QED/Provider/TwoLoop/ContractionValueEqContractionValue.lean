/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.ContractionValue
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.ContractionValue
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
# Provider for `QED.WickModel.contractionValue₂_eq_contractionValue`

Under development. This module will prove the frozen theorem goal
`QED.WickModel.contractionValue₂_eq_contractionValue` (packet T1, decision D-38) as
`QED.Provider.TwoLoop.contractionValue₂_eq_contractionValue`, with the binder convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
