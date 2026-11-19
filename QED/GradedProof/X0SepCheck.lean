/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0SepEnum

/-!
# (X₀): the kernel check for the separated contractions with closed loops

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), part A of
`TwoLoopClosedGoal`. For each of the fifteen normal-form fermion pairings with a closed loop and
an attached external fermion (`stdList0` without the open line, and `stdList1`), every attached
connected contraction whose two loops share no line passes `SepClosedCrit` (one kernel
evaluation per pairing, `decide +kernel`; peak memory about 5.4 GB including the imports). So
these contractions satisfy (T₉′) (`jointEnergyFirstIntegrable_std_sep`).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount)
open QED.TwoLoop.Enumeration (gauges stdList stdList0 stdList1 stdList2 stdList3
  verticesConnected_iff mem_withSigma)

variable {F : Type} [Fintype F] [DecidableEq F]

theorem sepCheck_0_1 : SepCheckσ stdList0[1] := by decide +kernel

theorem sepCheck_0_2 : SepCheckσ stdList0[2] := by decide +kernel

theorem sepCheck_0_3 : SepCheckσ stdList0[3] := by decide +kernel

theorem sepCheck_0_4 : SepCheckσ stdList0[4] := by decide +kernel

theorem sepCheck_0_5 : SepCheckσ stdList0[5] := by decide +kernel

theorem sepCheck_0_6 : SepCheckσ stdList0[6] := by decide +kernel

theorem sepCheck_0_7 : SepCheckσ stdList0[7] := by decide +kernel

theorem sepCheck_1_0 : SepCheckσ stdList1[0] := by decide +kernel

theorem sepCheck_1_1 : SepCheckσ stdList1[1] := by decide +kernel

theorem sepCheck_1_2 : SepCheckσ stdList1[2] := by decide +kernel

theorem sepCheck_1_3 : SepCheckσ stdList1[3] := by decide +kernel

theorem sepCheck_1_4 : SepCheckσ stdList1[4] := by decide +kernel

theorem sepCheck_1_5 : SepCheckσ stdList1[5] := by decide +kernel

theorem sepCheck_1_6 : SepCheckσ stdList1[6] := by decide +kernel

theorem sepCheck_1_7 : SepCheckσ stdList1[7] := by decide +kernel

theorem stdList0_zero_cycle : ∀ x, Equiv.Perm.SameCycle stdList0[0] x (.inl 0) := by
  decide +kernel

theorem sepCheck₀ : SepCheck stdList0 := by
  intro σ hσ h0 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hσ
  have hl : stdList0.length = 8 := rfl
  rw [hl] at hi
  interval_cases i
  · exact absurd stdList0_zero_cycle hc
  · exact sepCheck_0_1
  · exact sepCheck_0_2
  · exact sepCheck_0_3
  · exact sepCheck_0_4
  · exact sepCheck_0_5
  · exact sepCheck_0_6
  · exact sepCheck_0_7

theorem sepCheck₁ : SepCheck stdList1 := by
  intro σ hσ h0 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hσ
  have hl : stdList1.length = 8 := rfl
  rw [hl] at hi
  interval_cases i
  · exact sepCheck_1_0
  · exact sepCheck_1_1
  · exact sepCheck_1_2
  · exact sepCheck_1_3
  · exact sepCheck_1_4
  · exact sepCheck_1_5
  · exact sepCheck_1_6
  · exact sepCheck_1_7

theorem stdList_inl : ∀ σ ∈ stdList2 ++ stdList3, σ (.inl 0) = .inl 0 := by decide +kernel

theorem sepCheck_std : SepCheck stdList := by
  intro σ hσ h0
  simp only [stdList, List.mem_append] at hσ
  rcases hσ with ((hσ | hσ) | hσ) | hσ
  · exact sepCheck₀ σ hσ h0
  · exact sepCheck₁ σ hσ h0
  · exact absurd (stdList_inl σ (List.mem_append_left _ hσ)) h0
  · exact absurd (stdList_inl σ (List.mem_append_right _ hσ)) h0

/-- **(X₀) for the normal-form separated contractions with a closed loop.** -/
theorem jointEnergyFirstIntegrable_std_sep (P : Params) (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (hε : 0 < P.ε) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (C : Contraction 1 1 (gauges 5)) (hstd : C.1.1 ∈ stdList) (hA : ExternalsAttached C)
    (hV : VerticesConnected C) (hcyc : ¬ ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0))
    (hF : SepLines C) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) :=
  jointEnergyFirstIntegrable_of_sepClosedCrit P Φ D rep hrep hPV₁ hPV₂ hε gauges5 C
    (loopCount_gauges_five hA hV) hF
    (sepCheck_std C.1.1 hstd (hA.1 0 0) hcyc C (mem_withSigma C) (hA.2 0 0)
      ((verticesConnected_iff C).mp hV) hF) pOut pIn kIn αOut βIn μ

end QED.GradedProof.X0

end
