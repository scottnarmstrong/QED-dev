-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellSelAt
public import QED.Frozen.Graded.IsOnShellAt
public import QED.Provider.Graded.IsOnShellSelAtIsOnePIIff

@[expose] public section

open QED.WickModel (Params IsOnePI)

namespace QED.Graded

/-- (MS₁) **With the 1PI selection, (Gs₂) is (G₉)** (meaning theorem). Expected by `Iff.rfl`. -/
theorem isOnShellSelAt_isOnePI_iff (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (n : ℕ) :
    IsOnShellSelAt P Φ D (fun C _ => IsOnePI C) f n ↔ IsOnShellAt P Φ D f n :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
