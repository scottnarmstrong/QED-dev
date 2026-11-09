/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ConnectedFunction
public import QED.Frozen.WickModel.RegulatedAmplitude
public import QED.Frozen.WickModel.ExternalsAttached
public import QED.Frozen.WickModel.VerticesConnected
public import QED.Frozen.WickModel.IsLoopLine
public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.Wick.VertexKindOrder
public import QED.Frozen.Algebra.Bar
public import QED.Frozen.Algebra.Spinor
public import QED.Frozen.Algebra.Dot
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Provider for `QED.WickModel.lszAmplitude_existsUnique`

Under development. This module will prove the frozen theorem goal
`QED.WickModel.lszAmplitude_existsUnique` (packet 6c-1, decision D-30) as
`QED.Provider.WickModel.lszAmplitude_existsUnique`, with the binder convention of decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
