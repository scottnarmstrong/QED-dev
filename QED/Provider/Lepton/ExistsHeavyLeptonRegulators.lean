/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
import QED.LeptonProof.CoeffRegulators

/-!
# Provider for `QED.Lepton.exists_heavyLepton_regulators`

Proves the frozen theorem goal `QED.Lepton.exists_heavyLepton_regulators` (Phase 5 Stage 0 packet,
decision D-50) as `QED.Provider.Lepton.exists_heavyLepton_regulators`, with the binder convention of
decision D-13, from the helper in `QED.LeptonProof.CoeffRegulators`. This module must never import
the frozen anchor.
-/

public section

namespace QED.Provider.Lepton

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem exists_heavyLepton_regulators {n : ℕ} {mH : Fin n → ℝ} {RM : ℝ} :
    ∃ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) ∧ (∀ ℓ, mH ℓ < MH₂ ℓ) ∧
      (∀ ℓ, RM < MH₁ ℓ) ∧ (∀ ℓ, RM < MH₂ ℓ) ∧ (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) ∧
      ∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0 :=
  QED.Lepton.Proof.exists_heavyLepton_regulators' mH RM

end QED.Provider.Lepton

end
