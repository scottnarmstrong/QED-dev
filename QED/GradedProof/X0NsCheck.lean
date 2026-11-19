/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0NsEnum
public import QED.GradedProof.X0SepCheck

/-!
# (X₀): the kernel check for the non-separated contractions with a closed loop

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), part B of
`TwoLoopClosedGoal`. For each of the fifteen normal-form fermion pairings with a closed loop and
an attached external fermion, every attached connected contraction whose two loops share a line
passes `NsCrit` (one kernel evaluation per pairing, `decide +kernel`; such contractions occur
only for `stdList0[3]`, `stdList0[7]` and `stdList1[7]`). With part A
(`jointEnergyFirstIntegrable_std_sep`) this proves `TwoLoopStdGoal` (`twoLoopStdGoal`).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount)
open QED.TwoLoop.Enumeration (gauges stdList stdList0 stdList1 stdList2 stdList3
  verticesConnected_iff mem_withSigma)

variable {F : Type} [Fintype F] [DecidableEq F]

theorem nsCheck_0_1 : NsCheckσ stdList0[1] := by decide +kernel

theorem nsCheck_0_2 : NsCheckσ stdList0[2] := by decide +kernel

theorem nsCheck_0_3 : NsCheckσ stdList0[3] := by decide +kernel

theorem nsCheck_0_4 : NsCheckσ stdList0[4] := by decide +kernel

theorem nsCheck_0_5 : NsCheckσ stdList0[5] := by decide +kernel

theorem nsCheck_0_6 : NsCheckσ stdList0[6] := by decide +kernel

theorem nsCheck_0_7 : NsCheckσ stdList0[7] := by decide +kernel

theorem nsCheck_1_0 : NsCheckσ stdList1[0] := by decide +kernel

theorem nsCheck_1_1 : NsCheckσ stdList1[1] := by decide +kernel

theorem nsCheck_1_2 : NsCheckσ stdList1[2] := by decide +kernel

theorem nsCheck_1_3 : NsCheckσ stdList1[3] := by decide +kernel

theorem nsCheck_1_4 : NsCheckσ stdList1[4] := by decide +kernel

theorem nsCheck_1_5 : NsCheckσ stdList1[5] := by decide +kernel

theorem nsCheck_1_6 : NsCheckσ stdList1[6] := by decide +kernel

theorem nsCheck_1_7 : NsCheckσ stdList1[7] := by decide +kernel

/-- The non-separated test for a list of fermion pairings. -/
def NsCheck (L : List (Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 5)))) : Prop :=
  ∀ σ ∈ L, σ (.inl 0) ≠ .inl 0 → ¬ (∀ x, Equiv.Perm.SameCycle σ x (.inl 0)) → NsCheckσ σ

theorem nsCheck₀ : NsCheck stdList0 := by
  intro σ hσ h0 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hσ
  have hl : stdList0.length = 8 := rfl
  rw [hl] at hi
  interval_cases i
  · exact absurd stdList0_zero_cycle hc
  · exact nsCheck_0_1
  · exact nsCheck_0_2
  · exact nsCheck_0_3
  · exact nsCheck_0_4
  · exact nsCheck_0_5
  · exact nsCheck_0_6
  · exact nsCheck_0_7

theorem nsCheck₁ : NsCheck stdList1 := by
  intro σ hσ h0 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hσ
  have hl : stdList1.length = 8 := rfl
  rw [hl] at hi
  interval_cases i
  · exact nsCheck_1_0
  · exact nsCheck_1_1
  · exact nsCheck_1_2
  · exact nsCheck_1_3
  · exact nsCheck_1_4
  · exact nsCheck_1_5
  · exact nsCheck_1_6
  · exact nsCheck_1_7

theorem nsCheck_std : NsCheck stdList := by
  intro σ hσ h0
  simp only [stdList, List.mem_append] at hσ
  rcases hσ with ((hσ | hσ) | hσ) | hσ
  · exact nsCheck₀ σ hσ h0
  · exact nsCheck₁ σ hσ h0
  · exact absurd (stdList_inl σ (List.mem_append_left _ hσ)) h0
  · exact absurd (stdList_inl σ (List.mem_append_right _ hσ)) h0

/-- **`TwoLoopStdGoal`**: (X₀) for the normal-form two-loop contractions with a closed loop. -/
theorem twoLoopStdGoal (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F)
    (hε : 0 < P.ε) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) :
    TwoLoopStdGoal P Φ D := by
  intro C hstd hA hV hcyc pOut pIn kIn _ αOut βIn μ
  by_cases hF : SepLines C
  · exact jointEnergyFirstIntegrable_std_sep P Φ D rep hε hrep hPV₁ hPV₂ C hstd hA hV hcyc hF
      pOut pIn kIn αOut βIn μ
  · exact jointEnergyFirstIntegrable_of_nsCrit P Φ D rep hrep hPV₁ hPV₂ hε gauges5 C
      (loopCount_gauges_five hA hV)
      (nsCheck_std C.1.1 hstd (hA.1 0 0) hcyc C (mem_withSigma C) (hA.2 0 0)
        ((verticesConnected_iff C).mp hV) hF) pOut pIn kIn αOut βIn μ

end QED.GradedProof.X0

end
