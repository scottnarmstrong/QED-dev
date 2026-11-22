/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetD
public import QED.Frozen.ThreeLoop.A1SixSetD
public import QED.Frozen.Graded.IsFamilyVertexLimit
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.OneLoop.IsFormFactorPair

/-!
# Provider for `QED.ThreeLoop.isFormFactorPair_vertexSetD_pauli_limit`

Under development. This module will prove the frozen theorem goal
`QED.ThreeLoop.isFormFactorPair_vertexSetD_pauli_limit` (Phase 5 Stage 3d packet, decision D-59) as
`QED.Provider.ThreeLoop.isFormFactorPair_vertexSetD_pauli_limit`, with the binder convention of
decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
