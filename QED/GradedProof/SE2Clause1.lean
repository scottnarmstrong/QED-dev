/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ClassF

/-!
# Clause 1 of G-Σ₂ from the three two-loop classes

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57). `QED.GradedProof.SE2.jointEnergyFirstIntegrable_of_classes` reduces the first
clause (T₉′) of G-Σ₂ to the eight class obligations `ClassInt`. The five one-loop obligations
(`C1`, `C2`, `F`, `P0`, `P1`) are proved in `SE2ClassC`, `SE2ClassF`, `SE2ClassP`; what remains are
the three two-loop classes: rainbow `R`, crossed `X` and vacuum polarization `V`.

## Main statements

* `jointEnergyFirstIntegrable_of_twoLoopClasses`: the first clause of G-Σ₂ from `ClassInt repR`,
  `ClassInt repX` and `ClassInt repV`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.Graded

/-- **Clause 1 of G-Σ₂ from the two-loop classes.** -/
theorem jointEnergyFirstIntegrable_of_twoLoopClasses (hR : ClassInt repR) (hX : ClassInt repX)
    (hV : ClassInt repV) (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    ∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } { Φ with openLine := f } D C g ![p] ![]
              (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] :=
  jointEnergyFirstIntegrable_of_classes hR hX hV classInt_repF classInt_repP0 classInt_repP1
    classInt_repC1 classInt_repC2 P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂

end QED.GradedProof.SE2

end
