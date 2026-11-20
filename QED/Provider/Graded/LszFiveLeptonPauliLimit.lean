/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.IsLSZAmplitudePart
public import QED.Frozen.Graded.IsSpinFormFactorPair
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.TwoLoop.A1Four
public import QED.Frozen.Lepton.A2Four
public import QED.GradedProof.X2Seal

/-!
# Provider for `QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit`

Proves the frozen theorem goal `QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit`
(Phase 5 Stage 2 packet, decision D-57) as
`QED.Provider.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit`, with the binder convention
of decision D-13, from `QED.GradedProof.X2.isSpinFormFactorPair_lszFive_lepton_pauli_limit'`.
This module must never import the frozen anchor.
-/

@[expose] public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- (X₂), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem isSpinFormFactorPair_lszFive_lepton_pauli_limit {n : ℕ} {P₀ : Params}
    {mH : Fin n → ℝ} (he : P₀.e ≠ 0 := by assumption) (hm : 0 < P₀.m := by assumption)
    (hmH : ∀ ℓ, P₀.m < mH ℓ := by assumption) {η : ℝ} (hη : 0 < η := by assumption) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
        (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
        (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
          IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2) ∧
        ∀ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
          IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2 →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ M, IsLSZAmplitudePart
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 5 p' p M) ∧
            ∀ M, IsLSZAmplitudePart
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 5 p' p M →
              (∃ F : ℂ × ℂ, IsSpinFormFactorPair P₀.e P₀.m p' p M F) ∧
              ∀ F : ℂ × ℂ, IsSpinFormFactorPair P₀.e P₀.m p' p M F →
                ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 -
                  ((QED.TwoLoop.a1Four + ∑ ℓ, Lepton.a2Four (P₀.m / mH ℓ) : ℝ) : ℂ)‖ < η :=
  QED.GradedProof.X2.isSpinFormFactorPair_lszFive_lepton_pauli_limit' P₀ mH he hm hmH η hη

end QED.Provider.Graded

end
