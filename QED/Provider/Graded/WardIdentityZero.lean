/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.Graded.IsChargeNormalizedAt
import QED.GradedProof.LevelZeroWard

/-!
# Provider for `QED.Graded.d₁_eq_d₂_zero`

Proves the frozen theorem goal `QED.Graded.d₁_eq_d₂_zero` (Phase 5 Stage 2 packet, decision
D-57) as `QED.Provider.Graded.d₁_eq_d₂_zero`, with the binder convention of decision D-13, from
the helper in `QED.GradedProof.LevelZeroWard`. Until the frozen anchor is sealed, this module is
quarantined: only the frozen anchor file may import it (`scripts/check_frozen_anchors.py`). It
must never import the frozen anchor.
-/

public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem d₁_eq_d₂_zero {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {f : F} (he : P.e ≠ 0 := by assumption)
    (hf : 0 < Φ.mass f := by assumption) (hmγ : 0 < P.mγ := by assumption)
    (hΛ : 0 < P.Λ := by assumption) (hon : IsOnShellAt P Φ D f 1 := by assumption)
    (hK : IsChargeNormalizedAt P Φ D f 1 := by assumption) :
    D.d₁ f 0 = D.d₂ f 0 :=
  QED.GradedProof.d₁_eq_d₂_zero' P Φ D f he hf hmγ hΛ hon hK

end QED.Provider.Graded

end
