/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexIntegrand
public import QED.Frozen.OneLoop.EnergyFirstIntegral

/-!
# Provider for `QED.OneLoop.vertexLimit_existsUnique` (under development)

This module will prove the frozen theorem goal `QED.OneLoop.vertexLimit_existsUnique`
(packet 1, decision D-11) as `QED.Provider.OneLoop.vertexLimit_existsUnique`, with the exact
frozen statement. Until the frozen anchor is sealed, this module is quarantined: only the
frozen anchor file may import it (`scripts/check_frozen_anchors.py`). It must never import
the frozen anchor.
-/
