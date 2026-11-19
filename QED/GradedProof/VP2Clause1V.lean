/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Clause1F
public import QED.GradedProof.VP2ClassVB
public import QED.GradedProof.VP2ClassVC

/-!
# Clause 1 of G-Π₂

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57): the first clause (T₉′),
with exactly the hypotheses and first conclusion of the goal, from the class obligations of all
seven classes (`classInt2_repVA`, `classInt2_repVB`, `classInt2_repVC`, `classInt2_repG0`,
`classInt2_repG1`, `classInt2_repF0`, `classInt2_repF1`).
-/

@[expose] public section

open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)

namespace QED.GradedProof.VP2

open QED.Graded

/-- **Clause 1 of G-Π₂**: (T₉′) for every 1PI two-photon contraction of graded order `4`. -/
theorem vacuumPolarizationPart_two_clause1 (P : Params)
    {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F)
    (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) :
    ∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 0 2 κ, IsOnePI C → ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } Φ D C g ![] ![k, -k]
              (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν] :=
  jointEnergyFirstIntegrable_of_classesV classInt2_repVA classInt2_repVB classInt2_repVC P Φ D rep
    m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD

end QED.GradedProof.VP2

end
