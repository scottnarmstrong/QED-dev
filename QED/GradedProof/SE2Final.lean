/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Clause1Final
public import QED.GradedProof.SE2Clause2
public import QED.GradedProof.SE2Clause3

/-!
# G-Σ₂: the order-`e⁴` self-energy

Proof level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57). `selfEnergyPart_two_existsUnique'` has exactly the frozen statement; it is the
conjunction of `selfEnergyPart_two_clause1` (T₉′), `selfEnergyPart_two_clause2` (the unique
covariant form) and `selfEnergyPart_two_clause3` (differentiability at `z = -M_f`).
-/

@[expose] public section

open Filter Topology
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)

namespace QED.GradedProof.SE2

open QED.Graded

/-- **(G-Σ₂)**, with exactly the statement of `QED.Graded.selfEnergyPart_two_existsUnique`. -/
theorem selfEnergyPart_two_existsUnique' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } { Φ with openLine := f } D C g ![p] ![]
              (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![]) ∧
    (∃! AB : {s : ℝ // -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < s} → ℂ × ℂ,
      ∀ (p : Fin 4 → ℝ)
        (hp : -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < Minkowski.dot p p)
        (α β : Fin 4),
        Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 2 p α β) (𝓝[>] 0)
          (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
            + ((AB ⟨_, hp⟩).2 * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) ∧
    ∀ A B : ℝ → ℂ,
      (∀ p : Fin 4 → ℝ,
        -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
        Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 2 p α β) (𝓝[>] 0)
          (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
            + (B (Minkowski.dot p p) * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) →
      DifferentiableAt ℝ (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * Φ.mass f)
        (-Φ.mass f) :=
  ⟨selfEnergyPart_two_clause1 P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂,
    selfEnergyPart_two_clause2 P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂,
    selfEnergyPart_two_clause3 P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂⟩

end QED.GradedProof.SE2

end
