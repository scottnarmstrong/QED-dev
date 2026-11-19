/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Clause1
public import QED.GradedProof.SE2ClassRX

/-!
# Clause 1 of G-Σ₂ from the vacuum-polarization class

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57). With the rainbow and crossed classes proved (`classInt_repR`, `classInt_repX`
in `SE2ClassRX`), the first clause (T₉′) of G-Σ₂ needs only the class obligation of the
vacuum-polarization graph `V`: `jointEnergyFirstIntegrable_of_classV`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.Graded

/-- **Clause 1 of G-Σ₂ from the vacuum-polarization class.** -/
theorem jointEnergyFirstIntegrable_of_classV (hV : ClassInt repV) (P : Params) {F : Type}
    [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    ∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } { Φ with openLine := f } D C g ![p] ![]
              (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] :=
  jointEnergyFirstIntegrable_of_twoLoopClasses classInt_repR classInt_repX hV P Φ D f m₀ hm₀
    hmass hmγ hΛ hPV₁ hPV₂

end QED.GradedProof.SE2

end
