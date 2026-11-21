/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.ThreeLoop.A1SixSetA
public import QED.Frozen.Graded.IsFamilyVertexLimit
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.OneLoop.IsFormFactorPair

/-!
# Provider for `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`

Under development. This module will prove the frozen theorem goal
`QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit` (Phase 5 Stage 3a/3b packet, decision D-58)
as `QED.Provider.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`, with the binder convention of
decision D-13.
Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor file may
import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
