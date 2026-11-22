/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Lepton.LeptonFlavors
import QED.GradedProof.RPi4Wire2Asm
import QED.GradedProof.RPi4FaceRateIncAClass
import QED.GradedProof.RPi4FaceRateIncW11

/-!
# Provider for `QED.Graded.vacuumPolarizationPart_two_lepton_limit`

Proves the frozen theorem goal (R-Π₄) (Phase 5 Stage 2 packet, decision D-57) as
`QED.Provider.Graded.vacuumPolarizationPart_two_lepton_limit`, with the binder convention of
decision D-13. The assembly `vacuumPolarizationPart_two_lepton_limit_of_incPieces` gives the
frozen conclusion from the per-piece increment bounds of the three vertex-type classes; these are
`faceRateIncAQ_piecesAB_incPieces` (A increment) and `faceRateIncBPiecesAB_incPieces`
(B increment). This module must never import the frozen anchor.
-/

@[expose] public section

open Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- (R-Π₄), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem vacuumPolarizationPart_two_lepton_limit {n : ℕ} {P₀ : Params} {mH : Fin n → ℝ}
    (he : P₀.e ≠ 0 := by assumption) (hm : 0 < P₀.m := by assumption)
    (hmH : ∀ ℓ, P₀.m < mH ℓ := by assumption) :
    ∃ (Pinf : ℝ → ℂ) (C : ℝ), ∀ S₀ S η : ℝ, -(4 * P₀.m ^ 2) < S₀ → 0 < η →
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
            (∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) ∧
            ∀ Pol : ℝ → ℂ, (∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) →
              (∀ s : ℝ, S₀ ≤ s → s ≤ S → ‖Pol s / (P₀.e : ℂ) ^ 4 - Pinf s‖ < η) ∧
              ∀ s : ℝ, 0 ≤ s →
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 :=
  QED.GradedProof.RPi4.vacuumPolarizationPart_two_lepton_limit_of_incPieces P₀ mH he hm hmH
    (QED.GradedProof.RPi4.faceRateIncAQ_piecesAB_incPieces P₀.e)
    (QED.GradedProof.RPi4.faceRateIncBPiecesAB_incPieces P₀.e)

end QED.Provider.Graded

end
