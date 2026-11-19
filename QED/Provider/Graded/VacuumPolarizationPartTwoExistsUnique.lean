/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.VacuumPolarizationPart
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.GradedProof.VP2Final

/-!
# Provider for `QED.Graded.vacuumPolarizationPart_two_existsUnique`

Proves the frozen theorem goal `QED.Graded.vacuumPolarizationPart_two_existsUnique` (Phase 5
Stage 2 packet, decision D-57) as `QED.Provider.Graded.vacuumPolarizationPart_two_existsUnique`,
with the binder convention of decision D-13, from
`QED.GradedProof.VP2.vacuumPolarizationPart_two_existsUnique'`. This module must never import the
frozen anchor.
-/

@[expose] public section

open Filter Topology
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)
open QED.Graded

namespace QED.Provider.Graded

/-- (G-Π₂), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem vacuumPolarizationPart_two_existsUnique {P : Params} {F : Type} [Fintype F]
    [DecidableEq F] {Φ : Lepton.Flavors F} {D : Counterterms F} {rep : F → F} {m₀ : ℝ}
    (hm₀ : 0 < m₀ := by assumption) (hmass : ∀ g, m₀ ≤ Φ.mass g := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption)
    (hrep : ∀ f, rep (rep f) = rep f := by assumption)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0 := by
      assumption)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0 := by
      assumption)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0 := by assumption) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 0 2 κ, IsOnePI C → ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } Φ D C g ![] ![k, -k]
              (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν]) ∧
    ∃! Pol : {s : ℝ // -(4 * m₀ ^ 2) < s} → ℂ,
      ∀ (k : Fin 4 → ℝ) (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
        Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
          (𝓝 (Pol ⟨_, hk⟩ *
            ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) :=
  QED.GradedProof.VP2.vacuumPolarizationPart_two_existsUnique' P Φ D rep m₀ hm₀ hmass hmγ hΛ
    hrep hPV₁ hPV₂ hD

end QED.Provider.Graded

end
