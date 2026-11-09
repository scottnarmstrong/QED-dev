/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsLSZChargeNormalized
public import QED.Frozen.WickModel.LszAmplitudeExistsUnique
public import QED.Frozen.WickModel.VacuumPolarization
public import QED.Frozen.OneLoop.VertexFunction
public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.PacketNormSq
public import QED.OneLoop.OneParticle
public import QED.Algebra.OnShell
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support

/-!
# Provider for `QED.WickModel.isLSZChargeNormalized_iff_isChargeNormalized`

Under development. This module will prove the frozen theorem goal
`QED.WickModel.isLSZChargeNormalized_iff_isChargeNormalized` (packet 6c-2, decision D-31) as
`QED.Provider.WickModel.isLSZChargeNormalized_iff_isChargeNormalized`, with the binder convention of
decision D-13. Until the frozen anchor is sealed, this module is quarantined: only the frozen anchor
file may import it (`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/
