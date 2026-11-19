/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0NsAmp
public import QED.GradedProof.X0SepEnum

/-!
# (X₀): the test for the non-separated contractions with a closed loop

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), part B of
`TwoLoopClosedGoal`. A contraction passing `NsCrit` satisfies (X₀)
(`jointEnergyFirstIntegrable_of_nsCrit`). `NsCheckσ σ` says that every attached connected
contraction with fermion pairing `σ` whose two loops share a line passes `NsCrit`; it is
checked by kernel evaluation in `X0NsCheck`.
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel
open QED.TwoLoop.Enumeration (gauges withSigma lineData reachE)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

theorem card_zSet_zLine (C : Contraction 1 nA κ) :
    (zSet C).card = Fintype.card (ZLine C (zOf C)) := by
  classical
  rw [← Finset.card_univ]
  refine (Finset.card_bij (fun f _ => (Sum.inl f.1 : Line C)) (fun f _ => ?_)
    (fun f _ f' _ h => Subtype.ext (Sum.inl_injective h)) (fun l hl => ?_)).symm
  · simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and, isZL_inl, decide_eq_true_eq]
    exact f.2
  · simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rcases l with fl | g
    · exact ⟨⟨fl, by simpa using hl⟩, Finset.mem_univ _, rfl⟩
    · simp at hl

/-- **(X₀) for a contraction passing the non-separated test.** -/
theorem jointEnergyFirstIntegrable_of_nsCrit (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (C : Contraction 1 1 κ) (hL : loopCount C = 2)
    (hcrit : NsCrit C) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  obtain ⟨⟨s1, s2, s3⟩, hr, hpat⟩ := hcrit
  exact jointEnergyFirstIntegrable_nsClosed P Φ D rep hrep hPV₁ hPV₂ hε hκ C hL
    ⟨s1, fun t ht => s2 t ht not_false, s3⟩ ((card_zSet_zLine C).trans_le hr) hpat pOut pIn kIn
    αOut βIn μ

/-- The non-separated test for one fermion pairing. -/
def NsCheckσ (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) : Prop :=
  ∀ C ∈ withSigma σ, C.1.2 (.inl 0) ≠ .inl 0 →
    (∀ (h : 0 < 5) (w : Fin 5), w ∈ reachE (lineData C) (fun _ => true) ⟨0, h⟩ 5) →
      ¬ SepLines C → NsCrit C

instance (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5))) : Decidable (NsCheckσ σ) := by
  unfold NsCheckσ; infer_instance

end QED.GradedProof.X0

end
