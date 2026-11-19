/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelfEnergyPart
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import QED.GradedProof.SE2Final

/-!
# Provider for `QED.Graded.selfEnergyPart_two_existsUnique`

Proves the frozen theorem goal `QED.Graded.selfEnergyPart_two_existsUnique` (Phase 5 Stage 2
packet, decision D-57) as `QED.Provider.Graded.selfEnergyPart_two_existsUnique`, with the binder
convention of decision D-13, from `QED.GradedProof.SE2.selfEnergyPart_two_existsUnique'`. This
module must never import the frozen anchor.
-/

@[expose] public section

open Filter Topology
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)
open QED.Graded

namespace QED.Provider.Graded

/-- (G-Σ₂), with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem selfEnergyPart_two_existsUnique {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {f : F} {m₀ : ℝ}
    (hm₀ : 0 < m₀ := by assumption) (hmass : ∀ g, m₀ ≤ Φ.mass g := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption)
    (hPV₁ : ∑ g, Φ.coeff g = 0 := by assumption)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0 := by assumption) :
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
  QED.GradedProof.SE2.selfEnergyPart_two_existsUnique' P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂

end QED.Provider.Graded

end
