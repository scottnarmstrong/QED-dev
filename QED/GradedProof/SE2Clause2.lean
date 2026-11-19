/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormF
public import QED.GradedProof.SE2FormV

/-!
# Clause 2 of (G-Σ₂)

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57). `selfEnergyPart_two_clause2` is exactly the second conjunct of the frozen
statement, with its hypotheses: the eight class obligations (`classForm_repR`, `…_repX`,
`…_repV`, `…_repF`, `…_repP0`, `…_repP1`, `…_repC1`, `…_repC2`) fed to
`selfEnergyPart_two_clause2_of_classes`.
-/

@[expose] public section

open Filter Topology

namespace QED.GradedProof.SE2

open QED.WickModel QED.Graded

/-- **Clause 2 of G-Σ₂**: the unique covariant form of the order-`e⁴` self-energy below the
thresholds, with exactly the hypotheses and second conclusion of
`QED.Graded.selfEnergyPart_two_existsUnique`. -/
theorem selfEnergyPart_two_clause2 (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    ∃! AB : {s : ℝ // -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < s} → ℂ × ℂ,
      ∀ (p : Fin 4 → ℝ)
        (hp : -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < Minkowski.dot p p)
        (α β : Fin 4),
        Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 2 p α β) (𝓝[>] 0)
          (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
            + ((AB ⟨_, hp⟩).2 * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) :=
  selfEnergyPart_two_clause2_of_classes classForm_repR classForm_repX classForm_repV
    classForm_repF classForm_repP0 classForm_repP1 classForm_repC1 classForm_repC2 P Φ D f m₀ hm₀
    hmass hmγ hΛ hPV₁ hPV₂

end QED.GradedProof.SE2

end
