/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2LimRX
public import QED.TwoLoop.ClassLimitVP

/-!
# The class `V`: the `ε → 0⁺` limit

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2, step L1. The value of the vacuum-polarization graph `repV` converges
below the threshold `-(m + ν)²`, `0 < ν ≤ min(m_γ, Λ)`, `ν ≤ 2 m₀` with `m₀` a lower bound of
`m, M₁, M₂` (`exists_tendsto_contractionValue₂_repV`).

## Proof

The integrand at every `ε ≠ 0` is the sum `vSum` of five pieces `Fₖ ∏ᵢ D_{k,i}⁻¹` over the
shapes `sh1, …, sh5` of `QED/GradedProof/SE2ClassV.lean` (`v_key`, the identity of
`classInt_repV` stated for every parameter set); the numerators `vF1`, `vF2` do not depend on
`ε`. Each piece converges by `QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined`
(eight or nine lines), with `V ≥ c > 0` from `symanzikV_vShape_ge`, and the joint integral is
additive on integrable pieces.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel QED.TwoLoop.Bridge
open QED.Integration.TwoLoop (lineDenom castLoopMatrix RefinedBound IntNoSubdivergenceRefined
  symanzikU symanzikV noSubdivergenceRefined_castLoopMatrix_iff)
open Complex Filter Topology

/-- The constant `(2π)⁻⁸`. -/
noncomputable def vκ : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹

/-- The coupling constant of the amplitude. -/
noncomputable def vC (Q : Params) : ℂ := (I * Q.e) ^ 4 * (1 / I) ^ 5

/-- The Pauli–Villars factor `(M₁² - m²)(M₂² - m²)`. -/
noncomputable def vK (Q : Params) : ℂ := ((((Q.M₁ ^ 2 - Q.m ^ 2) * (Q.M₂ ^ 2 - Q.m ^ 2)) : ℝ) : ℂ)

/-- The numerator of the first three pieces. -/
noncomputable def vF1 (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  vκ * vC Q * vK Q *
    (seE0 Q α β (bm p ℓ 0) (bm p ℓ 1) (bm p ℓ 2) + ((Q.m ^ 2 : ℝ) : ℂ) * seE2 Q α β (bm p ℓ 0))

/-- The numerator of the last two pieces. -/
noncomputable def vF2 (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  -(vκ * vC Q * vK Q * seE2 Q α β (bm p ℓ 0))

/-- The five pieces at the prescription `ε`. -/
noncomputable def vSum (Q : Params) (ε : ℝ) (p : Fin 4 → ℝ) (α β : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  vF1 Q p α β ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh1 i))
      (fun i => basePP p (sh1 i)) (ms1 Q) ε i ℓ)⁻¹ +
    vF1 Q p α β ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh2 i))
      (fun i => basePP p (sh2 i)) (ms2 Q) ε i ℓ)⁻¹ +
    vF1 Q p α β ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh3 i))
      (fun i => basePP p (sh3 i)) (ms3 Q) ε i ℓ)⁻¹ +
    vF2 Q p α β ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh4 i))
      (fun i => basePP p (sh4 i)) (ms4 Q) ε i ℓ)⁻¹ +
    vF2 Q p α β ℓ * ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh5 i))
      (fun i => basePP p (sh5 i)) (ms5 Q) ε i ℓ)⁻¹

/-- **The integrand of `V` as five pieces**, at every parameter set with `ε ≠ 0` and the two
Pauli–Villars conditions. -/
theorem v_key (Q : Params) (hpv1 : 1 + Q.c₁ + Q.c₂ = 0)
    (hpv2 : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0) (hε' : Q.ε ≠ 0)
    (p : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vκ * regulatedAmplitude₂ Q repV ![p] ![] (lineMomentum₂ repV ![p] ![p] ![] ℓ) ![α] ![β] ![] =
      vSum Q Q.ε p α β ℓ := by
  unfold vSum
  obtain ⟨i1, i2, i3, i4, i5⟩ := idxV_apply
  have hv : ∀ f, vMom p ℓ f = bm p ℓ (idxV f) := fun _ => rfl
  have hc0 : Q.loopCoeff 0 = 1 := rfl
  have hc1 : Q.loopCoeff 1 = Q.c₁ := rfl
  have hc2 : Q.loopCoeff 2 = Q.c₂ := rfl
  have hm0 : Q.mass 0 = Q.m := rfl
  have hm1 : Q.mass 1 = Q.M₁ := rfl
  have hm2 : Q.mass 2 = Q.M₂ := rfl
  rw [lineMomentum₂_repV, regulatedAmplitude₂_repV, Fin.sum_univ_three, v_amplitude_eq _ hε',
    v_amplitude_eq _ hε', v_amplitude_eq _ hε', prod1, prod2, prod3, prod4, prod5]
  simp only [hv, i1, i2, i3, i4, i5, hc0, hc1, hc2, hm0, hm1, hm2, Complex.ofReal_one]
  have hfl := flavourSum_propDenom hε' (bm p ℓ 1) (bm p ℓ 2) hpv1 hpv2
    (seE0 Q α β (bm p ℓ 0) (bm p ℓ 1) (bm p ℓ 2)) (seE2 Q α β (bm p ℓ 0))
  have hu : propDenom Q.M₂ Q.ε (bm p ℓ 1) * (propDenom Q.M₂ Q.ε (bm p ℓ 1))⁻¹ = 1 :=
    mul_inv_cancel₀ (propDenom_ne_zero hε' _)
  have hw : propDenom Q.M₁ Q.ε (bm p ℓ 2) * (propDenom Q.M₁ Q.ε (bm p ℓ 2))⁻¹ = 1 :=
    mul_inv_cancel₀ (propDenom_ne_zero hε' _)
  rw [show ((((Q.M₁ ^ 2 - Q.m ^ 2) * (Q.M₂ ^ 2 - Q.m ^ 2)) : ℝ) : ℂ) = vK Q from rfl] at hfl
  simp only [vF1, vF2, denR]
  rw [show (I * (Q.e : ℂ)) ^ 4 * (1 / I) ^ 5 = vC Q from rfl]
  linear_combination (vκ * vC Q * denR Q p ℓ) * hfl -
    (vκ * vC Q * vK Q * seE2 Q α β (bm p ℓ 0) * denR Q p ℓ * (propDenom Q.M₁ Q.ε (bm p ℓ 1))⁻¹ *
      (propDenom Q.M₁ Q.ε (bm p ℓ 2))⁻¹ * (propDenom Q.M₂ Q.ε (bm p ℓ 2))⁻¹) * hu -
    (vκ * vC Q * vK Q * seE2 Q α β (bm p ℓ 0) * denR Q p ℓ * (propDenom Q.M₁ Q.ε (bm p ℓ 1))⁻¹ *
      (propDenom Q.M₂ Q.ε (bm p ℓ 1))⁻¹ * (propDenom Q.M₂ Q.ε (bm p ℓ 2))⁻¹) * hw

theorem isLoopPoly_vF1 (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) :
    IsLoopPoly 2 4 (vF1 Q p α β) := by
  have ha : ∀ j : Fin 5, IsLoopAffine fun ℓ => bm p ℓ j := fun j =>
    isLoopAffine_lineMomentum _ _ _
  have h2 := ((isLoopPoly_seE2 Q α β (ha 0)).mono (n' := 3) (by norm_num)).const_mul
    ((Q.m ^ 2 : ℝ) : ℂ)
  exact (((isLoopPoly_seE0 Q α β (ha 0) (ha 1) (ha 2)).add h2).const_mul
    (vκ * vC Q * vK Q)).mono (by norm_num)

theorem isLoopPoly_vF2 (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) :
    IsLoopPoly 2 4 (vF2 Q p α β) := by
  have ha : IsLoopAffine fun ℓ => bm p ℓ 0 := isLoopAffine_lineMomentum _ _ _
  have h := ((isLoopPoly_seE2 Q α β ha).const_mul (-(vκ * vC Q * vK Q))).mono (n' := 4)
    (by norm_num)
  refine (congrArg (IsLoopPoly 2 4) (funext fun ℓ => ?_)).mp h
  simp only [vF2]
  ring

theorem refinedBound_vF1 (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (sh : Fin (8 + 1) → Fin 5)
    (s0 : sh 0 = 0) (s1 : sh 1 = 1) (s2 : sh 2 = 2) :
    RefinedBound (castLoopMatrix fun i => baseA (sh i)) {0, 1, 2} 4 (vF1 Q p α β) := by
  have e : ∀ (j : Fin (8 + 1)) (k : Fin 5), sh j = k → ∀ ℓ, QED.Integration.TwoLoop.lineMomentum
      (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) j ℓ = bm p ℓ k := by
    intro j k hjk ℓ
    exact congrArg (bm p ℓ) hjk
  have h0 := refinedBound_seE0 (castLoopMatrix fun i => baseA (sh i))
    (fun i => basePP p (sh i)) Q α β (e0 := 0) (e1 := 1) (e2 := 2) (by decide) (by decide)
    (by decide)
  have h2 := (refinedBound_seE2 (castLoopMatrix fun i => baseA (sh i))
    (fun i => basePP p (sh i)) Q α β 0).mono (E' := {0, 1, 2}) (by decide) (by norm_num :
      1 ≤ 3)
  simp only [e 0 0 s0, e 1 1 s1, e 2 2 s2] at h0 h2
  exact ((h0.add (h2.const_mul ((Q.m ^ 2 : ℝ) : ℂ))).const_mul (vκ * vC Q * vK Q)).mono
    subset_rfl (by norm_num)

theorem refinedBound_vF2 (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (sh : Fin (7 + 1) → Fin 5)
    (s0 : sh 0 = 0) :
    RefinedBound (castLoopMatrix fun i => baseA (sh i)) {0} 4 (vF2 Q p α β) := by
  have e : ∀ ℓ, QED.Integration.TwoLoop.lineMomentum
      (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) 0 ℓ = bm p ℓ 0 := by
    intro ℓ
    exact congrArg (bm p ℓ) s0
  have h2 := refinedBound_seE2 (castLoopMatrix fun i => baseA (sh i))
    (fun i => basePP p (sh i)) Q α β 0
  simp only [e] at h2
  exact ((h2.const_mul (vκ * vC Q * vK Q)).neg).mono subset_rfl (by norm_num)

/-- **The limit of one piece** below threshold. -/
theorem exists_tendsto_vPiece {n : ℕ} (hn : 7 ≤ n) (sh : Fin (n + 1) → Fin 5)
    (Ms : Fin (n + 1) → ℝ) (p : Fin 4 → ℝ) {E : Finset (Fin (n + 1))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun i => baseA (sh i))
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound (castLoopMatrix fun i => baseA (sh i)) E 4 F) {m m₀ ν : ℝ}
    (hm0 : 0 < m₀) (hmm : m₀ ≤ m) (hν0 : 0 < ν) (hν2 : ν ≤ 2 * m₀)
    (h0 : ∀ i, sh i = 0 → m ≤ Ms i) (h12 : ∀ i, sh i = 1 ∨ sh i = 2 → m₀ ≤ Ms i)
    (h34 : ∀ i, sh i = 3 ∨ sh i = 4 → ν ≤ Ms i) (hs : -(m + ν) ^ 2 < Minkowski.dot p p) :
    ∃ L : ℂ, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => F ℓ *
      ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) Ms ε i
        ℓ)⁻¹)) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨P, rfl⟩ := hpoly.exists_loopQuartic
  have hm : 0 < m := hm0.trans_le hmm
  have hc : 0 < min (m₀ ^ 2) (ν ^ 2) := lt_min (by positivity) (by positivity)
  have hMc : ∀ i, min (m₀ ^ 2) (ν ^ 2) ≤ Ms i ^ 2 := by
    intro i
    rcases (by decide : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) (sh i) with
      h | h | h | h | h
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (hmm.trans (h0 i h)) 2)
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (h12 i (Or.inl h)) 2)
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (h12 i (Or.inr h)) 2)
    · exact (min_le_right _ _).trans (pow_le_pow_left₀ hν0.le (h34 i (Or.inl h)) 2)
    · exact (min_le_right _ _).trans (pow_le_pow_left₀ hν0.le (h34 i (Or.inr h)) 2)
  exact ⟨_, QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined P _ _ Ms hn
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB
    (min_one_mul_pos (by positivity) hc hs)
    (fun z hz hz1 hU => symanzikV_vShape_ge sh Ms hm hν0 hν2 h0 h12 h34 hc hMc hs hz hz1 hU)⟩

theorem cond_sh1 (Q : Params) {m₀ ν : ℝ} (hM1 : m₀ ≤ Q.M₁) (hM2 : m₀ ≤ Q.M₂) (hmm : m₀ ≤ Q.m)
    (hγ : ν ≤ Q.mγ) (hΛ : ν ≤ Q.Λ) :
    (∀ i, sh1 i = 0 → Q.m ≤ ms1 Q i) ∧ (∀ i, sh1 i = 1 ∨ sh1 i = 2 → m₀ ≤ ms1 Q i) ∧
      (∀ i, sh1 i = 3 ∨ sh1 i = 4 → ν ≤ ms1 Q i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;>
    fin_cases i <;> simp [sh1, ms1] at hi ⊢ <;> assumption

theorem cond_sh2 (Q : Params) {m₀ ν : ℝ} (hM1 : m₀ ≤ Q.M₁) (hM2 : m₀ ≤ Q.M₂) (hmm : m₀ ≤ Q.m)
    (hγ : ν ≤ Q.mγ) (hΛ : ν ≤ Q.Λ) :
    (∀ i, sh2 i = 0 → Q.m ≤ ms2 Q i) ∧ (∀ i, sh2 i = 1 ∨ sh2 i = 2 → m₀ ≤ ms2 Q i) ∧
      (∀ i, sh2 i = 3 ∨ sh2 i = 4 → ν ≤ ms2 Q i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;>
    fin_cases i <;> simp [sh2, ms2] at hi ⊢ <;> assumption

theorem cond_sh3 (Q : Params) {m₀ ν : ℝ} (hM1 : m₀ ≤ Q.M₁) (hM2 : m₀ ≤ Q.M₂) (hmm : m₀ ≤ Q.m)
    (hγ : ν ≤ Q.mγ) (hΛ : ν ≤ Q.Λ) :
    (∀ i, sh3 i = 0 → Q.m ≤ ms3 Q i) ∧ (∀ i, sh3 i = 1 ∨ sh3 i = 2 → m₀ ≤ ms3 Q i) ∧
      (∀ i, sh3 i = 3 ∨ sh3 i = 4 → ν ≤ ms3 Q i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;>
    fin_cases i <;> simp [sh3, ms3] at hi ⊢ <;> assumption

theorem cond_sh4 (Q : Params) {m₀ ν : ℝ} (hM1 : m₀ ≤ Q.M₁) (hM2 : m₀ ≤ Q.M₂) (_hmm : m₀ ≤ Q.m)
    (hγ : ν ≤ Q.mγ) (hΛ : ν ≤ Q.Λ) :
    (∀ i, sh4 i = 0 → Q.m ≤ ms4 Q i) ∧ (∀ i, sh4 i = 1 ∨ sh4 i = 2 → m₀ ≤ ms4 Q i) ∧
      (∀ i, sh4 i = 3 ∨ sh4 i = 4 → ν ≤ ms4 Q i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;>
    fin_cases i <;> simp [sh4, ms4] at hi ⊢ <;> assumption

theorem cond_sh5 (Q : Params) {m₀ ν : ℝ} (hM1 : m₀ ≤ Q.M₁) (hM2 : m₀ ≤ Q.M₂) (_hmm : m₀ ≤ Q.m)
    (hγ : ν ≤ Q.mγ) (hΛ : ν ≤ Q.Λ) :
    (∀ i, sh5 i = 0 → Q.m ≤ ms5 Q i) ∧ (∀ i, sh5 i = 1 ∨ sh5 i = 2 → m₀ ≤ ms5 Q i) ∧
      (∀ i, sh5 i = 3 ∨ sh5 i = 4 → ν ≤ ms5 Q i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;>
    fin_cases i <;> simp [sh5, ms5] at hi ⊢ <;> assumption
/-- The value of `V` at `ε > 0` as the sum of the joint integrals of the five pieces. -/
theorem contractionValue₂_repV_eq {Q : Params} (hpv1 : 1 + Q.c₁ + Q.c₂ = 0)
    (hpv2 : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    (p : Fin 4 → ℝ) (α β : Fin 4) :
    contractionValue₂ { Q with ε := ε } repV ![p] ![p] ![] ![α] ![β] ![] =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => vF1 Q p α β ℓ *
          ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh1 i))
            (fun i => basePP p (sh1 i)) (ms1 Q) ε i ℓ)⁻¹) +
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => vF1 Q p α β ℓ *
          ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh2 i))
            (fun i => basePP p (sh2 i)) (ms2 Q) ε i ℓ)⁻¹) +
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => vF1 Q p α β ℓ *
          ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh3 i))
            (fun i => basePP p (sh3 i)) (ms3 Q) ε i ℓ)⁻¹) +
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => vF2 Q p α β ℓ *
          ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh4 i))
            (fun i => basePP p (sh4 i)) (ms4 Q) ε i ℓ)⁻¹) +
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => vF2 Q p α β ℓ *
          ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh5 i))
            (fun i => basePP p (sh5 i)) (ms5 Q) ε i ℓ)⁻¹) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := crit_sh
  have hp1 := isLoopPoly_vF1 Q p α β
  have hp2 := isLoopPoly_vF2 Q p α β
  have i1 := jointEnergyFirstIntegrable_vPiece (by norm_num) sh1 (ms1 Q) hε p c1 hp1
    (refinedBound_vF1 Q p α β sh1 rfl rfl rfl)
  have i2 := jointEnergyFirstIntegrable_vPiece (by norm_num) sh2 (ms2 Q) hε p c2 hp1
    (refinedBound_vF1 Q p α β sh2 rfl rfl rfl)
  have i3 := jointEnergyFirstIntegrable_vPiece (by norm_num) sh3 (ms3 Q) hε p c3 hp1
    (refinedBound_vF1 Q p α β sh3 rfl rfl rfl)
  have i4 := jointEnergyFirstIntegrable_vPiece (by norm_num) sh4 (ms4 Q) hε p c4 hp2
    (refinedBound_vF2 Q p α β sh4 rfl)
  have i5 := jointEnergyFirstIntegrable_vPiece (by norm_num) sh5 (ms5 Q) hε p c5 hp2
    (refinedBound_vF2 Q p α β sh5 rfl)
  have j12 := QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add i1 i2
  have j123 := QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add j12 i3
  have j1234 := QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add j123 i4
  have e1 : contractionValue₂ { Q with ε := ε } repV ![p] ![p] ![] ![α] ![β] ![] =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => vSum Q ε p α β ℓ) := by
    unfold contractionValue₂
    rw [loopCount_repV]
    exact congrArg _ (funext fun ℓ => v_key { Q with ε := ε } hpv1 hpv2 hε.ne' p α β ℓ)
  refine e1.trans ?_
  refine (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add j1234 i5).trans ?_
  refine congrArg (· + _) ((QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add j123 i4).trans ?_)
  refine congrArg (· + _) ((QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add j12 i3).trans ?_)
  exact congrArg (· + _) (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add i1 i2)

/-- **The limit of the vacuum-polarization class `V`** exists below threshold. -/
theorem exists_tendsto_contractionValue₂_repV {Q : Params} (hpv1 : 1 + Q.c₁ + Q.c₂ = 0)
    (hpv2 : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0) {m₀ ν : ℝ} (hm0 : 0 < m₀)
    (hmm : m₀ ≤ Q.m) (hM1 : m₀ ≤ Q.M₁) (hM2 : m₀ ≤ Q.M₂) (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (hν2 : ν ≤ 2 * m₀) {p : Fin 4 → ℝ}
    (hs : -(Q.m + ν) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      contractionValue₂ { Q with ε := ε } repV ![p] ![p] ![] ![α] ![β] ![]) (𝓝[>] 0) (𝓝 L) := by
  have hγ : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have hΛ : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  obtain ⟨c1, c2, c3, c4, c5⟩ := crit_sh
  have hp1 := isLoopPoly_vF1 Q p α β
  have hp2 := isLoopPoly_vF2 Q p α β
  obtain ⟨a1, b1, d1⟩ := cond_sh1 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a2, b2, d2⟩ := cond_sh2 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a3, b3, d3⟩ := cond_sh3 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a4, b4, d4⟩ := cond_sh4 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a5, b5, d5⟩ := cond_sh5 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨L1, t1⟩ := exists_tendsto_vPiece (by norm_num) sh1 (ms1 Q) p c1 hp1
    (refinedBound_vF1 Q p α β sh1 rfl rfl rfl) hm0 hmm hν0 hν2 a1 b1 d1 hs
  obtain ⟨L2, t2⟩ := exists_tendsto_vPiece (by norm_num) sh2 (ms2 Q) p c2 hp1
    (refinedBound_vF1 Q p α β sh2 rfl rfl rfl) hm0 hmm hν0 hν2 a2 b2 d2 hs
  obtain ⟨L3, t3⟩ := exists_tendsto_vPiece (by norm_num) sh3 (ms3 Q) p c3 hp1
    (refinedBound_vF1 Q p α β sh3 rfl rfl rfl) hm0 hmm hν0 hν2 a3 b3 d3 hs
  obtain ⟨L4, t4⟩ := exists_tendsto_vPiece (by norm_num) sh4 (ms4 Q) p c4 hp2
    (refinedBound_vF2 Q p α β sh4 rfl) hm0 hmm hν0 hν2 a4 b4 d4 hs
  obtain ⟨L5, t5⟩ := exists_tendsto_vPiece (by norm_num) sh5 (ms5 Q) p c5 hp2
    (refinedBound_vF2 Q p α β sh5 rfl) hm0 hmm hν0 hν2 a5 b5 d5 hs
  refine ⟨L1 + L2 + L3 + L4 + L5, ((((t1.add t2).add t3).add t4).add t5).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (contractionValue₂_repV_eq hpv1 hpv2 hε p α β).symm

end QED.GradedProof.SE2

end
