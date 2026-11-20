/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.LevelOneElectron
public import QED.WickModel.ElectronOnShell

/-!
# (X₁): continuity of the order-`e²` self-energy form factor at the mass shell

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece B″. The leg lemmas `QED.GradedProof.X1.tendsto_leg_in`,
`QED.GradedProof.X1.tendsto_leg_out` need the form factor `A` of the self-energy to be continuous
at `-M_f²`. For the order-`e⁴` self-energy this is
`QED.GradedProof.X1.continuousAt_A_selfEnergyPart_two`. At order `e²` the self-energy (G₈ₛ) is
the one-loop self-energy (X₂₈) at mass `M_f` (`QED.GradedProof.selfEnergyPart_one_apply`), whose
limit has the explicit form factor `A_loop - δ₂`, differentiable below both thresholds
(`QED.WickModel.differentiableAt_selfEnergyLoopA`). Any `A` with the limit property agrees with it
near `-M_f²` (`QED.GradedProof.eventuallyEq_of_tendsto`), so it is continuous there.

## Main statements

* `QED.GradedProof.X1C.continuousAt_A_selfEnergyPart_one`.
-/

@[expose] public section

open Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X1C

/-- **Continuity of the order-`e²` form factor at the shell (piece B″).** If `A`, `B` are form
factors of the limit `ε → 0⁺` of the order-`e²` self-energy (G₈ₛ) of flavour `f` on a region
`p² > -R²` with `R > M_f`, then `A` is continuous at `-M_f²`. -/
theorem continuousAt_A_selfEnergyPart_one (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (hf : 0 < Φ.mass f)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {R : ℝ} (hR : Φ.mass f < R) (A B : ℝ → ℂ)
    (hAB : ∀ p : Fin 4 → ℝ, -R ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 1 p α β) (𝓝[>] 0)
        (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
          + (B (Minkowski.dot p p) * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) :
    ContinuousAt A (-Φ.mass f ^ 2) := by
  set P' : Params :=
    { P with m := Φ.mass f, δ₂ := P.e ^ 2 * D.d₂ f 0, δm := P.e ^ 2 * D.dm f 0 } with hP'
  set M := Φ.mass f with hM
  set A₀ : ℝ → ℂ := fun s => QED.WickModel.selfEnergyLoopA P' s - P'.δ₂ with hA₀
  set B₀ : ℝ → ℂ := fun s => QED.WickModel.selfEnergyLoopB P' s - P'.δm with hB₀
  have hμ : 0 < min P.mγ P.Λ := lt_min hmγ hΛ
  have hlim₀ : ∀ p : Fin 4 → ℝ, -(M + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 1 p α β) (𝓝[>] 0)
        (𝓝 ((A₀ (Minkowski.dot p p) • Dirac.slash p
          + (B₀ (Minkowski.dot p p) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) := by
    intro p hp α β
    simp only [selfEnergyPart_one_apply]
    exact QED.WickModel.tendsto_onePIFunction_selfEnergyLoop P' hf hmγ hΛ p hp α β
  have hAB' : ∀ p : Fin 4 → ℝ, -(M + (R - M)) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 1 p α β) (𝓝[>] 0)
        (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
          + (B (Minkowski.dot p p) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) := by
    intro p hp
    rw [add_sub_cancel] at hp
    exact hAB p hp
  have heq := eventuallyEq_of_tendsto hf (sub_pos.2 hR) hμ hAB' hlim₀
  have hA₀ : ContinuousAt A₀ (-M ^ 2) := by
    have hs : -M ^ 2 ∈ Ioi (-(P'.m + P'.mγ) ^ 2) ∩ Ioi (-(P'.m + P'.Λ) ^ 2) := by
      refine ⟨?_, ?_⟩ <;> simp only [mem_Ioi, hP'] <;> nlinarith
    exact (QED.WickModel.differentiableAt_selfEnergyLoopA (P := P') hf hmγ hΛ
      hs).continuousAt.sub continuousAt_const
  exact hA₀.congr (heq.mono fun s hs => hs.1.symm)

end QED.GradedProof.X1C

end
