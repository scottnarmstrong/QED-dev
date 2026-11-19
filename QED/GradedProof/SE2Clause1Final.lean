/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Clause1V
public import QED.GradedProof.SE2ClassV

/-!
# Clause 1 of G-Σ₂

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57). `selfEnergyPart_two_clause1` is exactly the first conjunct (T₉′) of the frozen
statement: every 1PI one-fermion contraction of graded order `4` has a jointly integrable,
energy-first regulated amplitude. It combines the reduction to the three two-loop classes
(`jointEnergyFirstIntegrable_of_classV`, with `classInt_repR`, `classInt_repX`) with the class
obligation of the vacuum-polarization graph (`classInt_repV`).
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.Graded

/-- **Clause 1 (T₉′) of G-Σ₂**, with exactly the hypotheses and first conclusion of
`QED.Graded.selfEnergyPart_two_existsUnique`. -/
theorem selfEnergyPart_two_clause1 (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    ∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } { Φ with openLine := f } D C g ![p] ![]
              (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] :=
  jointEnergyFirstIntegrable_of_classV classInt_repV P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂

end QED.GradedProof.SE2

end
