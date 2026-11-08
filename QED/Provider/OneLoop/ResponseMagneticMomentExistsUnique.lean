/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsResponseMagneticMoment
import QED.OneLoop.MagneticResponse

/-!
# Provider for `QED.OneLoop.existsUnique_isResponseMagneticMoment`

Proves packet 4a's theorem goal (R) (decision D-16) as
`QED.Provider.OneLoop.existsUnique_isResponseMagneticMoment`, with the binder convention of
decision D-13. The frozen anchor is sealed with this theorem (2026-11-08).
This module must never import the frozen anchor.
-/

@[expose] public section

open Matrix Complex
open QED.OneLoop QED.OneLoop.VertexLimit

namespace QED.Provider.OneLoop

/-- Packet 4a's (R), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem existsUnique_isResponseMagneticMoment {e Z₁ m mγ Λ : ℝ} (hm : 0 < m := by assumption)
    (hmγ : 0 < mγ := by assumption) (hΛ : 0 < Λ := by assumption) :
    ∃! μ : ℝ, IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ :=
  ⟨_, magneticMu_spec hm hmγ hΛ, fun _ hμ => eq_of_magnetic_spec hm hmγ hΛ hμ
    (magneticMu_spec hm hmγ hΛ)⟩

end QED.Provider.OneLoop

end
