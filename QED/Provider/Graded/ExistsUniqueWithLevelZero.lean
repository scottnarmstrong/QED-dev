/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.CountertermsWithLevel
public import QED.Frozen.Graded.IsRenormalizedThrough
import QED.GradedProof.LevelZero

/-!
# Provider for `QED.Graded.existsUnique_withLevel_zero`

Proves the frozen theorem goal `QED.Graded.existsUnique_withLevel_zero` (Phase 5 Stage 2 packet,
decision D-57) as `QED.Provider.Graded.existsUnique_withLevel_zero`, with the binder convention of
decision D-13, from the helper in `QED.GradedProof.LevelZero`. Until the frozen anchor is sealed,
this module is quarantined: only the frozen anchor file may import it
(`scripts/check_frozen_anchors.py`). It must never import the frozen anchor.
-/

public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem existsUnique_withLevel_zero {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {rep : F → F} (he : P.e ≠ 0 := by assumption)
    (hmass : ∀ f, 0 < Φ.mass f := by assumption) (hmγ : 0 < P.mγ := by assumption)
    (hΛ : 0 < P.Λ := by assumption) (hrep : ∀ f, rep (rep f) = rep f := by assumption)
    (hPV₁ : ∑ f, Φ.coeff f = 0 := by assumption)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0 := by assumption) :
    ∃! x : (F → ℝ × ℝ × ℝ) × ℝ, IsRenormalizedThrough P Φ (D.withLevel 0 x.1 x.2) rep 1 :=
  QED.GradedProof.existsUnique_withLevel_zero' P Φ D rep he hmass hmγ hΛ hrep hPV₁ hPV₂

end QED.Provider.Graded

end
