/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMAssemblyAux
public import QED.Frozen.Lepton.IsVertexOrderFiveLimit
public import QED.Frozen.Lepton.A2Four
public import QED.Frozen.TwoLoop.A1Four
import QED.Algebra.FormFactorProjector

/-!
# (HM₂) at fixed regulators and counterterms

Helper level, Phase 5 Stage 0 (decision D-50). At fixed regulators, photon regulators and
counterterms, the `q² → 0⁺` clause of (HM₂) follows from

* the same clause of T1's (HV₃) at the shifted counterterm `δ₃ - ∑_ℓ π_ℓ` (tolerance `η/2`),
* T1's form-factor clause and uniform `q² → 0⁺` limit at `P` and at the auxiliary sets,
* the heavy bracket (`QED/LeptonProof/HMBracket.lean`) within `η/4` of `∑_ℓ A₂⁽⁴⁾(m/m_ℓ)`,

through the flavour split of the vertex (`QED/LeptonProof/HMVertex.lean`): the multi-lepton
vertex limit is `V_P + ∑ w V_Q`, its form-factor pair is `F_P + ∑ w F_Q`, and
`F₂ = F₂(P') + [F₂(P) - F₂(P') + ∑ w F₂(Q)]` (`fixed_clause`).
-/

@[expose] public section

open Complex Finset Matrix Filter Topology
open scoped Real
open QED.WickModel (Params)
open QED.TwoLoop.PauliZeroLimit QED.Chain.HeavyVP

namespace QED.Lepton.Proof.HM

variable {n : ℕ} {H : Fin n → HeavyLepton} {X : Fin n → ℝ}

/-- **The `q² → 0⁺` clause of (HM₂) at fixed regulators and counterterms.** -/
theorem fixed_clause (P : Params) (hP : T1Adm P) (he : P.e ≠ 0) (hok : AuxOK H X P.m)
    (hgt : AuxGt H X P.m) (hH₂ : ∀ ℓ, (H ℓ).m < (H ℓ).M₂) {η : ℝ} (hη : 0 < η)
    (hT1 : ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, QED.Minkowski.dot p' p' = -P.m ^ 2 →
      QED.Minkowski.dot p p = -P.m ^ 2 → 0 < p' 0 → 0 < p 0 →
      0 < QED.Minkowski.dot (p' - p) (p' - p) → QED.Minkowski.dot (p' - p) (p' - p) < q₀ →
      (∃ V, QED.TwoLoop.IsVertexOrderFiveLimit (shiftP P H X) p' p V) ∧
      ∀ V, QED.TwoLoop.IsVertexOrderFiveLimit (shiftP P H X) p' p V →
        (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P.e P.m p' p V F) ∧
        ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P.e P.m p' p V F →
          ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P.e : ℂ) ^ 4 - (QED.TwoLoop.a1Four : ℂ)‖ < η / 2)
    (hheavy : |∑ ℓ, heavyUnitReg ((H ℓ).m / P.m) (P.mγ / P.m) (P.Λ / P.m) ((H ℓ).M₁ / P.m)
        ((H ℓ).M₂ / P.m) - ∑ ℓ, a2Four (P.m / (H ℓ).m)| < η / 4) :
    ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, QED.Minkowski.dot p' p' = -P.m ^ 2 →
      QED.Minkowski.dot p p = -P.m ^ 2 → 0 < p' 0 → 0 < p 0 →
      0 < QED.Minkowski.dot (p' - p) (p' - p) → QED.Minkowski.dot (p' - p) (p' - p) < q₀ →
      (∃ V, IsVertexOrderFiveLimit P (leptonFlavors P H) p' p V) ∧
      ∀ V, IsVertexOrderFiveLimit P (leptonFlavors P H) p' p V →
        (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P.e P.m p' p V F) ∧
        ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P.e P.m p' p V F →
          ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P.e : ℂ) ^ 4 -
            ((QED.TwoLoop.a1Four + ∑ ℓ, a2Four (P.m / (H ℓ).m) : ℝ) : ℂ)‖ < η := by
  obtain ⟨q₀₀, hq₀₀, hT⟩ := hT1
  set w : Fin n → Fin 3 → ℝ := fun ℓ j => auxWeight P (H ℓ) (X ℓ) j with hw
  set Q : Fin n → Fin 3 → Params := fun ℓ j => auxParams P (H ℓ) (X ℓ) j with hQdef
  set c : ℂ := 16 * (π : ℂ) ^ 4 / (P.e : ℂ) ^ 4 with hc
  set W : ℝ := 2 + ∑ ℓ, ∑ j, |w ℓ j| with hW
  have hW0 : 0 ≤ W := by positivity
  set τ : ℝ := η / 4 / (‖c‖ * W + 1) with hτdef
  have hden : 0 < ‖c‖ * W + 1 := by positivity
  have hτ : 0 < τ := by positivity
  obtain ⟨qP, hqP, hUP⟩ := uniform_pauli_t1 hP he hτ
  obtain ⟨qS, hqS, hUS⟩ := uniform_pauli_t1 (hP.shiftP H X) he hτ
  have hQU := fun ℓ j => uniform_pauli_t1 (hP.aux hok hgt ℓ j) he hτ
  choose qQ hqQ hUQ using hQU
  obtain ⟨qQ', hqQ', hqQle⟩ := exists_pos_le_forall (fun x : Fin n × Fin 3 => qQ x.1 x.2)
    fun x => hqQ x.1 x.2
  refine ⟨min (min q₀₀ qP) (min qS qQ'), lt_min (lt_min hq₀₀ hqP) (lt_min hqS hqQ'),
    fun p' p hp' hp hp0' hp0 hq hqq => ?_⟩
  have hq1 : QED.Minkowski.dot (p' - p) (p' - p) < q₀₀ :=
    hqq.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hq2 : QED.Minkowski.dot (p' - p) (p' - p) < qP :=
    hqq.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hq3 : QED.Minkowski.dot (p' - p) (p' - p) < qS :=
    hqq.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hq4 : ∀ ℓ j, QED.Minkowski.dot (p' - p) (p' - p) < qQ ℓ j := fun ℓ j =>
    hqq.trans_le (((min_le_right _ _).trans (min_le_right _ _)).trans (hqQle (ℓ, j)))
  -- T1's limits and pairs
  obtain ⟨⟨VP, hVP⟩, hFPx⟩ := exists_isVertexOrderFiveLimit_t1 hP he hp' hp hp0' hp0 hq
  obtain ⟨FP, hFP⟩ := hFPx VP hVP
  have hQx : ∀ ℓ j, ∃ V, QED.TwoLoop.IsVertexOrderFiveLimit (Q ℓ j) p' p V ∧
      ∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P.e P.m p' p V F := fun ℓ j => by
    obtain ⟨⟨V, hV⟩, hF⟩ := exists_isVertexOrderFiveLimit_t1 (hP.aux hok hgt ℓ j) he hp' hp hp0'
      hp0 hq
    exact ⟨V, hV, hF V hV⟩
  choose VQ hVQ FQ hFQ using hQx
  obtain ⟨⟨VS, hVS⟩, hSx⟩ := hT p' p hp' hp hp0' hp0 hq hq1
  obtain ⟨⟨FS, hFS⟩, hFSb⟩ := hSx VS hVS
  -- the multi-lepton limit
  set Vtot : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := VP + ∑ ℓ, ∑ j, (w ℓ j : ℂ) • VQ ℓ j with hVtot
  have hlim : IsVertexOrderFiveLimit P (leptonFlavors P H) p' p Vtot := by
    intro μ a b
    have hT2 : Tendsto (fun ε => QED.TwoLoop.vertexOrderFive { P with ε := ε } p' p μ a b +
        ∑ ℓ, ∑ j, (w ℓ j : ℂ) *
          QED.TwoLoop.vertexOrderFive { Q ℓ j with ε := ε } p' p μ a b) (𝓝[>] 0)
        (𝓝 (Vtot μ a b)) := by
      have := (hVP μ a b).add (tendsto_finsetSum univ fun ℓ _ => tendsto_finsetSum univ
        fun j _ => (hVQ ℓ j μ a b).const_mul (w ℓ j : ℂ))
      convert this using 2
      simp [hVtot, Matrix.sum_apply, Finset.sum_apply]
    refine hT2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h := vertexOrderFive_leptonFlavors_eq { P with ε := ε } hε hP.pv₁ hP.pv₂ hok p' p μ
    have hl : leptonFlavors { P with ε := ε } H = leptonFlavors P H := rfl
    rw [hl] at h
    rw [h]
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  refine ⟨⟨Vtot, hlim⟩, fun V hV => ?_⟩
  have hVeq : V = Vtot := by
    funext μ
    ext a b
    exact tendsto_nhds_unique (hV μ a b) (hlim μ a b)
  subst hVeq
  have hFtot : QED.OneLoop.IsFormFactorPair P.e P.m p' p Vtot
      (FP + ∑ ℓ, ∑ j, (w ℓ j : ℂ) • FQ ℓ j) :=
    isFormFactorPair_add hFP (isFormFactorPair_sum _ fun ℓ _ => isFormFactorPair_sum _
      fun j _ => isFormFactorPair_smul _ (hFQ ℓ j))
  refine ⟨⟨_, hFtot⟩, fun F hF => ?_⟩
  have hm0 : P.m ≠ 0 := hP.hm.ne'
  have hFeq : F = FP + ∑ ℓ, ∑ j, (w ℓ j : ℂ) • FQ ℓ j := by
    rw [QED.OneLoop.eq_formFactorProj_of_isFormFactorPair he hm0 hp' hp hq hF,
      QED.OneLoop.eq_formFactorProj_of_isFormFactorPair he hm0 hp' hp hq hFtot]
  have hF2 : F.2 = FP.2 + ∑ ℓ, ∑ j, (w ℓ j : ℂ) * (FQ ℓ j).2 := by
    rw [hFeq]
    simp [Prod.snd_sum]
  -- the three bounds
  have b1 := hFSb FS hFS
  have bP := hUP p' p hp hp' hp0 hp0' hq hq2 VP hVP FP hFP
  have bS := hUS p' p hp hp' hp0 hp0' hq hq3 VS hVS FS hFS
  have bQ := fun ℓ j => hUQ ℓ j p' p hp hp' hp0 hp0' hq (hq4 ℓ j) (VQ ℓ j) (hVQ ℓ j) (FQ ℓ j)
    (hFQ ℓ j)
  have hbr := heavyBracket_eq P hP he hok hgt hH₂
  set pP := pauliZeroLimit P P.e
  set pS := pauliZeroLimit (shiftP P H X) P.e
  set pQ : Fin n → Fin 3 → ℂ := fun ℓ j => pauliZeroLimit (Q ℓ j) P.e
  have he4 : (P.e : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 (ofReal_ne_zero.mpr he)
  have key : 16 * (π : ℂ) ^ 4 * F.2 / (P.e : ℂ) ^ 4 -
      ((QED.TwoLoop.a1Four + ∑ ℓ, a2Four (P.m / (H ℓ).m) : ℝ) : ℂ) =
      (16 * (π : ℂ) ^ 4 * FS.2 / (P.e : ℂ) ^ 4 - (QED.TwoLoop.a1Four : ℂ)) +
        c * ((FP.2 - pP) - (FS.2 - pS) + ∑ ℓ, ∑ j, (w ℓ j : ℂ) * ((FQ ℓ j).2 - pQ ℓ j)) +
        (((∑ ℓ, heavyUnitReg ((H ℓ).m / P.m) (P.mγ / P.m) (P.Λ / P.m) ((H ℓ).M₁ / P.m)
          ((H ℓ).M₂ / P.m) - ∑ ℓ, a2Four (P.m / (H ℓ).m) : ℝ)) : ℂ) := by
    rw [hF2, Complex.ofReal_sub, ← hbr]
    push_cast
    simp only [hc, mul_sub, sum_sub_distrib]
    field_simp
    ring
  rw [key]
  have bmid : ‖(FP.2 - pP) - (FS.2 - pS) + ∑ ℓ, ∑ j, (w ℓ j : ℂ) * ((FQ ℓ j).2 - pQ ℓ j)‖ ≤
      τ * W := by
    have hs : ‖∑ ℓ, ∑ j, (w ℓ j : ℂ) * ((FQ ℓ j).2 - pQ ℓ j)‖ ≤ ∑ ℓ, ∑ j, |w ℓ j| * τ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun ℓ _ => (norm_sum_le _ _).trans
        (sum_le_sum fun j _ => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (bQ ℓ j).le (abs_nonneg _)
    calc _ ≤ ‖FP.2 - pP‖ + ‖FS.2 - pS‖ + ‖∑ ℓ, ∑ j, (w ℓ j : ℂ) * ((FQ ℓ j).2 - pQ ℓ j)‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ τ + τ + ∑ ℓ, ∑ j, |w ℓ j| * τ := add_le_add (add_le_add bP.le bS.le) hs
      _ = τ * W := by
        rw [hW]
        simp only [← sum_mul]
        ring
  have b2 : ‖c * ((FP.2 - pP) - (FS.2 - pS) +
      ∑ ℓ, ∑ j, (w ℓ j : ℂ) * ((FQ ℓ j).2 - pQ ℓ j))‖ < η / 4 := by
    rw [norm_mul]
    have h1 : ‖c‖ * (τ * W) < η / 4 := by
      rw [hτdef]
      rw [show ‖c‖ * (η / 4 / (‖c‖ * W + 1) * W) = η / 4 * (‖c‖ * W / (‖c‖ * W + 1)) by
        field_simp]
      have : ‖c‖ * W / (‖c‖ * W + 1) < 1 := by
        rw [div_lt_one hden]
        linarith
      nlinarith
    exact (mul_le_mul_of_nonneg_left bmid (norm_nonneg c)).trans_lt h1
  have b3 : ‖(((∑ ℓ, heavyUnitReg ((H ℓ).m / P.m) (P.mγ / P.m) (P.Λ / P.m) ((H ℓ).M₁ / P.m)
      ((H ℓ).M₂ / P.m) - ∑ ℓ, a2Four (P.m / (H ℓ).m) : ℝ)) : ℂ)‖ < η / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hheavy
  calc _ ≤ ‖16 * (π : ℂ) ^ 4 * FS.2 / (P.e : ℂ) ^ 4 - (QED.TwoLoop.a1Four : ℂ)‖ +
        ‖c * ((FP.2 - pP) - (FS.2 - pS) + ∑ ℓ, ∑ j, (w ℓ j : ℂ) * ((FQ ℓ j).2 - pQ ℓ j))‖ +
        ‖(((∑ ℓ, heavyUnitReg ((H ℓ).m / P.m) (P.mγ / P.m) (P.Λ / P.m) ((H ℓ).M₁ / P.m)
          ((H ℓ).M₂ / P.m) - ∑ ℓ, a2Four (P.m / (H ℓ).m) : ℝ)) : ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _) |>.trans_eq (by ring)
    _ < η / 2 + η / 4 + η / 4 := by linarith
    _ = η := by ring

end QED.Lepton.Proof.HM

end
