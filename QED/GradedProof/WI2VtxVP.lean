/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2VtxVPDen
public import QED.GradedProof.V5ZeroLimVP
public import QED.GradedProof.SE2Decomp
public import QED.TwoLoop.LimitCovarianceClasses

/-!
# A7 for the class `VP`: insertions on the open line of `V`

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A7 for the vacuum-polarization vertex class `VP`.

At zero photon momentum (`p' = p`, on shell), the class `VP` contracted with `r`
(`∑_μ r_μ V^μ`) is `e` times the sum over the five pieces of the self-energy class `V` of the
parametric values of their one-slot numerators with the insertion `(m - k̸) r̸ (m - k̸)` on the
open line, over the data with the open line doubled (`sum_lower_classLimitV_VP`): this is
`e · vInsV`, minus `e` times the Ward–Takahashi derivative of `V` (`hasDerivAt_vPV_wt`).

The identity holds for the joint integrands at every `ε > 0` after the change of loop momenta
`mVP` (`integrand_VP_ins`): the contracted numerators are `num_VP_lt`, `num_VP_three`, the
denominators `prod_vpDenom_zero`, …, and term `3` of `VP` splits into the pieces `vD4`, `vD5`
by cancelling one denominator (`vpDenom_three_split`). Both sides converge as `ε → 0⁺`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.ClassLimit QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance

/-- A piece of the insertion on the open line of `V`, at the prescription `ε`. -/
noncomputable abbrev insTerm (D : SEData) (Q : Params)
    (c : Fin 4 × Fin 4 × Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ) (p r : Fin 4 → ℝ)
    (α β : Fin 4) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  D.slotV 0 Q.m aSlotV bSlotV c p r ℓ α β *
    ∏ j, (lineDenom (D.dup 0).α (dbl 0 (D.mom p)) (D.dup 0).M ε j ℓ)⁻¹

/-- The five pieces of the insertion on the open line of `V`, at the prescription `ε`. -/
noncomputable def insSum (Q : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) (ε : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  insTerm (vD1 Q) Q (cSlotV1 Q) p r α β ε ℓ + insTerm (vD2 Q) Q (cSlotV1 Q) p r α β ε ℓ +
    insTerm (vD3 Q) Q (cSlotV1 Q) p r α β ε ℓ + insTerm (vD4 Q) Q (cSlotV2 Q) p r α β ε ℓ +
    insTerm (vD5 Q) Q (cSlotV2 Q) p r α β ε ℓ

theorem sum_lower_mul_mul (a f : Fin 4 → ℂ) (c X : ℂ) :
    ∑ μ, a μ * (c * (f μ * X)) = (∑ μ, a μ * (c * f μ)) * X := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun μ _ => by ring

theorem vpTermNumer_lt (Q : Params) (ε : ℝ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) {t : Fin 4} (ht : t ≠ 3) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpTermNumer { Q with ε := ε } pOut pIn kIn αOut βIn μ t ℓ =
      vpTermNumer Q pOut pIn kIn αOut βIn μ t ℓ := by
  simp only [vpTermNumer, ht, ↓reduceIte]
  rfl

theorem vpTermNumer_three (Q : Params) (ε : ℝ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpTermNumer { Q with ε := ε } pOut pIn kIn αOut βIn μ 3 ℓ =
      -(vpBubbleCoeff Q * vpE2 Q pIn kIn αOut βIn μ ℓ) *
        (vpDenom { Q with ε := ε } 3 (pIn 0) (pOut 0) 8 ℓ +
          vpDenom { Q with ε := ε } 3 (pIn 0) (pOut 0) 3 ℓ) := by
  simp only [vpTermNumer, ↓reduceIte, neg_mul]
  rfl

/-- **The contracted integrand of `VP` at `p' = p` as the insertions on the open line of `V`**,
at every `ε > 0`, after the change of loop momenta `mVP`. -/
theorem integrand_VP_ins (Q : Params) {ε : ℝ} (hε : 0 < ε) (p r : Fin 4 → ℝ) (α β : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * ((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      ∑ t : Fin 4, vpTermNumer { Q with ε := ε } (fun _ => p) (fun _ => p) (fun _ => p - p)
        (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ∏ i : Fin 10, (vpDenom { Q with ε := ε } t p p i ℓ)⁻¹) =
      Q.e * insSum Q p r α β ε (loopAff mVP 0 ℓ) := by
  have h3 := vpDenom_three_split Q p ε ℓ hε
  have e : ∀ μ : Fin 4, (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      ∑ t : Fin 4, vpTermNumer { Q with ε := ε } (fun _ => p) (fun _ => p) (fun _ => p - p)
        (fun _ => α) (fun _ => β) (fun _ => μ) t ℓ *
        ∏ i : Fin 10, (vpDenom { Q with ε := ε } t p p i ℓ)⁻¹ =
      twoLoopNorm * (vpTermNumer Q (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α)
          (fun _ => β) (fun _ => μ) 0 ℓ * ∏ i, (vpDenom { Q with ε := ε } 0 p p i ℓ)⁻¹) +
        twoLoopNorm * (vpTermNumer Q (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α)
          (fun _ => β) (fun _ => μ) 1 ℓ * ∏ i, (vpDenom { Q with ε := ε } 1 p p i ℓ)⁻¹) +
        twoLoopNorm * (vpTermNumer Q (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α)
          (fun _ => β) (fun _ => μ) 2 ℓ * ∏ i, (vpDenom { Q with ε := ε } 2 p p i ℓ)⁻¹) +
        twoLoopNorm * (-(vpBubbleCoeff Q * vpE2 Q (fun _ => p) (fun _ => p - p) (fun _ => α)
          (fun _ => β) (fun _ => μ) ℓ) *
          ((vpDenom { Q with ε := ε } 3 p p 8 ℓ + vpDenom { Q with ε := ε } 3 p p 3 ℓ) *
            ∏ i, (vpDenom { Q with ε := ε } 3 p p i ℓ)⁻¹)) := by
    intro μ
    rw [Fin.sum_univ_four, vpTermNumer_lt Q ε _ _ _ _ _ _ (by decide : (0 : Fin 4) ≠ 3),
      vpTermNumer_lt Q ε _ _ _ _ _ _ (by decide : (1 : Fin 4) ≠ 3),
      vpTermNumer_lt Q ε _ _ _ _ _ _ (by decide : (2 : Fin 4) ≠ 3), vpTermNumer_three]
    ring
  simp only [e, mul_add, Finset.sum_add_distrib]
  rw [sum_lower_mul_mul, sum_lower_mul_mul, sum_lower_mul_mul, sum_lower_mul_mul, h3,
    num_VP_lt Q p r α β ℓ (by decide : (0 : Fin 4) ≠ 3),
    num_VP_lt Q p r α β ℓ (by decide : (1 : Fin 4) ≠ 3),
    num_VP_lt Q p r α β ℓ (by decide : (2 : Fin 4) ≠ 3), num_VP_three,
    Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib,
    prod_vpDenom_zero, prod_vpDenom_one, prod_vpDenom_two]
  have s1 : ∀ c, (vD1 Q).slotV 0 Q.m aSlotV bSlotV c p r (loopAff mVP 0 ℓ) α β = _ :=
    fun c => slotV_vData_apply _ sh1 _ _ _ Q rfl c p r _ α β
  have s2 : ∀ c, (vD2 Q).slotV 0 Q.m aSlotV bSlotV c p r (loopAff mVP 0 ℓ) α β = _ :=
    fun c => slotV_vData_apply _ sh2 _ _ _ Q rfl c p r _ α β
  have s3 : ∀ c, (vD3 Q).slotV 0 Q.m aSlotV bSlotV c p r (loopAff mVP 0 ℓ) α β = _ :=
    fun c => slotV_vData_apply _ sh3 _ _ _ Q rfl c p r _ α β
  have s4 : ∀ c, (vD4 Q).slotV 0 Q.m aSlotV bSlotV c p r (loopAff mVP 0 ℓ) α β = _ :=
    fun c => slotV_vData_apply _ sh4 _ _ _ Q rfl c p r _ α β
  have s5 : ∀ c, (vD5 Q).slotV 0 Q.m aSlotV bSlotV c p r (loopAff mVP 0 ℓ) α β = _ :=
    fun c => slotV_vData_apply _ sh5 _ _ _ Q rfl c p r _ α β
  simp only [insSum, insTerm, s1, s2, s3, s4, s5, dupDen, Finset.prod_inv_distrib]
  ring

/-- **A piece of the insertion**: integrable at every `ε > 0`, and its joint integral tends to
the parametric value `vIns`. -/
theorem insTerm_piece {D : SEData} (Q : Params)
    {c : Fin 4 × Fin 4 × Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ}
    {S : Finset (Fin (D.m + 1))} (hS : (0 : Fin (D.m + 1)) ∉ S) (hSE : insert 0 S ⊆ D.E)
    (hcp : ∀ l, IsLoopPoly 2 2 (c l)) (hcb : ∀ l, RefinedBound D.α S 2 (c l))
    (p r : Fin 4 → ℝ) (α β : Fin 4) :
    (∀ ε, 0 < ε →
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (insTerm D Q c p r α β ε)) ∧
    (D.VPos (D.mom p) → Tendsto (fun ε =>
      QED.TwoLoop.jointEnergyFirstIntegral 2 (insTerm D Q c p r α β ε)) (𝓝[>] 0)
        (𝓝 (vIns D Q c p r α β))) := by
  obtain ⟨QV, hQV⟩ :=
    (D.isLoopPoly_slotV 0 Q.m (A := aSlotV) (B := bSlotV) hcp p r α β).exists_loopQuartic
  have h7 : 7 ≤ (D.dup 0).m := by
    have := D.hm
    change 7 ≤ D.m + 1
    omega
  have hg : (D.dup 0).Good QV := ⟨Or.inl h7, by
    rw [hQV]
    exact D.refinedBound_slotV 0 Q.m (A := aSlotV) (B := bSlotV) hS hSE hcb p r α β⟩
  refine ⟨fun ε hε => ?_, fun hV => ?_⟩
  · have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined QV
      (D.dup 0).α (dbl 0 (D.mom p)) (D.dup 0).M h7 hε (D.dup 0).hcrit hg.2
    simp only [hQV] at h
    exact h
  · have h := SEData.tendsto_pv hg (hV.dup 0)
    rw [vIns, SEData.pvF_eq hg hQV (hV.dup 0)]
    simp only [hQV] at h
    exact h

/-- **The contracted value of `VP` at `p' = p` and `ε > 0`** as the joint integral of the
insertions on the open line of `V`. -/
theorem sum_lower_contractionValue₂_VP {Q : Params} (hpv1 : 1 + Q.c₁ + Q.c₂ = 0)
    (hpv2 : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    (p r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * contractionValue₂ { Q with ε := ε } Class5.VP.rep
      (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) =
      Q.e * QED.TwoLoop.jointEnergyFirstIntegral 2 (insSum Q p r α β ε) := by
  have hmom : (fun _ : Fin 1 => p) 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p - p) 0 := by
    simp
  have hpf := fun μ : Fin 4 => (parametricForm_VP { Q with ε := ε } hε.ne' hpv1 hpv2
    (pOut := fun _ => p) (pIn := fun _ => p) (kIn := fun _ => p - p) hmom (fun _ => α)
    (fun _ => β) (fun _ => μ)).1
  simp only [hpf]
  rw [← jointEnergyFirstIntegral_sum Finset.univ _ _ fun μ _ =>
    QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_VP_classRouting { Q with ε := ε } hε
      _ _ _ _ _ _]
  rw [← jointEnergyFirstIntegral_loopAff (insSum Q p r α β ε) mVP isUnit_det_mVP 0,
    ← jointEnergyFirstIntegral_const_mul]
  exact congrArg _ (funext fun ℓ => integrand_VP_ins Q hε p r α β ℓ)

/-- **A7 for `VP`**: the contracted limit of `VP` at `p' = p` is `e` times the sum over the five
pieces of `V` of the insertions `(m - k̸) r̸ (m - k̸)` on the open line. -/
theorem sum_lower_classLimitV_VP {Q : Params} (hpv1 : 1 + Q.c₁ + Q.c₂ = 0)
    (hpv2 : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0) {m₀ ν : ℝ} (hm0 : 0 < m₀)
    (hmm : m₀ ≤ Q.m) (hM1 : m₀ ≤ Q.M₁) (hM2 : m₀ ≤ Q.M₂) (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (hν2 : ν ≤ 2 * m₀) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -Q.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV .VP Q p p μ α β =
      Q.e * vInsV Q p r α β := by
  have hm : 0 < Q.m := hm0.trans_le hmm
  have hγ : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have hΛ : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  have hs : -(Q.m + ν) ^ 2 < Minkowski.dot p p := by rw [hp]; nlinarith
  obtain ⟨a1, b1, d1⟩ := cond_sh1 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a2, b2, d2⟩ := cond_sh2 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a3, b3, d3⟩ := cond_sh3 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a4, b4, d4⟩ := cond_sh4 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a5, b5, d5⟩ := cond_sh5 Q hM1 hM2 hmm hγ hΛ
  have p1 := insTerm_piece (D := vD1 Q) Q s12_notMem s12_subset (isLoopPoly_cSlotV1 Q)
    (refinedBound_cSlotV1 _ sh1 _ _ _ Q rfl rfl one_ne_two_nine) p r α β
  have p2 := insTerm_piece (D := vD2 Q) Q s12_notMem s12_subset (isLoopPoly_cSlotV1 Q)
    (refinedBound_cSlotV1 _ sh2 _ _ _ Q rfl rfl one_ne_two_nine) p r α β
  have p3 := insTerm_piece (D := vD3 Q) Q s12_notMem s12_subset (isLoopPoly_cSlotV1 Q)
    (refinedBound_cSlotV1 _ sh3 _ _ _ Q rfl rfl one_ne_two_nine) p r α β
  have p4 := insTerm_piece (D := vD4 Q) Q s0_notMem s0_subset (isLoopPoly_cSlotV2 Q)
    (refinedBound_cSlotV2 _ sh4 _ _ _ Q) p r α β
  have p5 := insTerm_piece (D := vD5 Q) Q s0_notMem s0_subset (isLoopPoly_cSlotV2 Q)
    (refinedBound_cSlotV2 _ sh5 _ _ _ Q) p r α β
  have hR : Tendsto (fun ε => Q.e * QED.TwoLoop.jointEnergyFirstIntegral 2
      (insSum Q p r α β ε)) (𝓝[>] 0) (𝓝 (Q.e * vInsV Q p r α β)) := by
    refine Tendsto.const_mul _ ?_
    have h := ((((p1.2 (vpos_vData _ sh1 _ _ _ hm hm0 hmm hν0 hν2 a1 b1 d1 hs)).add
      (p2.2 (vpos_vData _ sh2 _ _ _ hm hm0 hmm hν0 hν2 a2 b2 d2 hs))).add
      (p3.2 (vpos_vData _ sh3 _ _ _ hm hm0 hmm hν0 hν2 a3 b3 d3 hs))).add
      (p4.2 (vpos_vData _ sh4 _ _ _ hm hm0 hmm hν0 hν2 a4 b4 d4 hs))).add
      (p5.2 (vpos_vData _ sh5 _ _ _ hm hm0 hmm hν0 hν2 a5 b5 d5 hs))
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have i1 := p1.1 ε hε
    have i2 := p2.1 ε hε
    have i3 := p3.1 ε hε
    have i4 := p4.1 ε hε
    have i12 := QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add i1 i2
    have i123 := QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add i12 i3
    have i1234 := QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add i123 i4
    unfold insSum
    rw [jointEnergyFirstIntegral_add i1234 (p5.1 ε hε), jointEnergyFirstIntegral_add i123 i4,
      jointEnergyFirstIntegral_add i12 i3, jointEnergyFirstIntegral_add i1 i2]
  have hL : Tendsto (fun ε : ℝ => ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) *
      contractionValue₂ { Q with ε := ε } Class5.VP.rep (fun _ => p) (fun _ => p)
        (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ)) (𝓝[>] 0)
      (𝓝 (∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV .VP Q p p μ α β)) := by
    refine tendsto_finsetSum _ fun μ _ => Tendsto.const_mul _ ?_
    obtain ⟨_, -, -, h⟩ := QED.GradedProof.V5Zero.Lim.tendsto_contractionValue₂_VP Q hm0 hmm
      (hν0.trans_le hγ) (hν0.trans_le hΛ) hM1 hM2 hpv1 hpv2 (pOut := fun _ => p)
      (pIn := fun _ => p) (kIn := fun _ => p - p) (by simp) hp hp (by simp [Minkowski.dot])
      (fun _ => α) (fun _ => β) (fun _ => μ)
    simp only [classLimitV, Matrix.of_apply]
    rw [h.limUnder_eq]
    exact h
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (sum_lower_contractionValue₂_VP hpv1 hpv2 hε p r α β).symm

end QED.GradedProof.WI2

end
