/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Frozen.OneLoop.VertexOneLoop
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Provider for `QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_enclosure_ten`

Under development. This module will prove the frozen theorem goal
`QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_enclosure_ten` (packet Q, decision D-35) as
`QED.Provider.OneLoop.isFormFactorPair_vertexOneLoop_pauli_enclosure_ten`, with the binder
convention of decision D-13. Until the frozen anchor is sealed, this module is quarantined: only the
frozen anchor file may import it (`scripts/check_frozen_anchors.py`). It must never import the
frozen anchor.
-/
