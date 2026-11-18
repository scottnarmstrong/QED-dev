-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
public import QED.Provider.Lepton.ExistsHeavyLeptonRegulators

@[expose] public section

namespace QED.Lepton

/-- **Admissible heavy-lepton regulators exist above every threshold** (non-vacuity of the
regulator hypotheses of (HM₂); the family form of the two-loop challenge's
`exists_pauliVillars_regulators`): for any lepton masses and any `R_M` there are regulator pairs,
one per lepton, heavier than their lepton and than `R_M`, satisfying both Pauli–Villars
conditions with their lepton's mass. -/
theorem exists_heavyLepton_regulators {n : ℕ} (mH : Fin n → ℝ) (RM : ℝ) :
    ∃ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) ∧ (∀ ℓ, mH ℓ < MH₂ ℓ) ∧
      (∀ ℓ, RM < MH₁ ℓ) ∧ (∀ ℓ, RM < MH₂ ℓ) ∧ (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) ∧
      ∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Lepton.exists_heavyLepton_regulators
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
