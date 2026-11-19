/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.Frozen.OneLoop.IsChargeNormalized
import QED.GradedProof.LevelOneCharge

/-!
# Provider for `QED.Graded.isChargeNormalizedAt_one_iff`

Proves the frozen theorem goal `QED.Graded.isChargeNormalizedAt_one_iff` (Phase 5 Stage 2 packet,
decision D-57) as `QED.Provider.Graded.isChargeNormalizedAt_one_iff`, with the binder convention of
decision D-13, from the helper in `QED.GradedProof.LevelOneCharge`. The anchor is sealed (D-57 seal
note).
-/

public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem isChargeNormalizedAt_one_iff {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {f : F} (hf : 0 < Φ.mass f := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption) :
    IsChargeNormalizedAt P Φ D f 1 ↔
      QED.OneLoop.IsChargeNormalized P.e (1 + P.e ^ 2 * D.d₁ f 0) (Φ.mass f) P.mγ P.Λ hf hmγ
        hΛ :=
  QED.GradedProof.isChargeNormalizedAt_one_iff' P Φ D f hf hmγ hΛ

end QED.Provider.Graded

end
