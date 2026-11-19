/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0NsCheck
public import QED.GradedProof.X0Assemble
public import QED.GradedProof.X0ClosedEnum

/-!
# (X₀): every term of the order-`e⁵` connected part satisfies (T₉′)

The Phase 5 Stage 2 goal (X₀) `QED.Graded.jointEnergyFirstIntegrable_connectedPart_five`
(decision D-57), as `jointEnergyFirstIntegrable_connectedPart_five'`: from
`jointEnergyFirstIntegrable_five_of_goals` with the one-loop goal (`oneLoopGoal`) and the
two-loop goal with a closed fermion loop (`twoLoopClosedGoal_of_std` and `twoLoopStdGoal`).
No mass bound is used, only `ε > 0` and the block conditions.
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount lineMomentum₂)

/-- **(X₀).** -/
theorem jointEnergyFirstIntegrable_connectedPart_five' (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Grading κ) (hg : gradedOrder κ g = 5)
    (C : Contraction 1 1 κ) (hC : ExternalsAttached C ∧ VerticesConnected C)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  jointEnergyFirstIntegrable_five_of_goals P Φ D hε (oneLoopGoal P Φ D rep hε hrep hPV₁ hPV₂ hD)
    (twoLoopClosedGoal_of_std P Φ D (twoLoopStdGoal P Φ D rep hε hrep hPV₁ hPV₂)) g hg C hC pOut
    pIn kIn hmom αOut βIn μ

end QED.GradedProof.X0

end
