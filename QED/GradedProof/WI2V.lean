/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2VSlot
public import QED.GradedProof.WI2P

/-!
# The class `V`: limit and Ward–Takahashi derivative

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the vacuum-polarization class `V`.

* `jef_vPiece`: at every `ε`, the joint integral of a frozen piece of `V` (shape `sh`) is that of
  the one-slot numerator over the Ward–Takahashi data `vData` (`ℓ ↦ loopAff mV ![p, 0] ℓ`).
* `vD1`, …, `vD5`: the Ward–Takahashi data of the five pieces; `vPV`: the sum of the parametric
  values of their one-slot numerators.
* `tendsto_repV_wt`: below threshold the class value of `V` tends to `vPV`.
* `vInsV`: the sum over the pieces of the insertion values on the open line.
* `hasDerivAt_vPiece_wt`, `hasDerivAt_vPV_wt`: the derivative along a ray `t ↦ t r` is minus the
  sum of the parametric values of the one-slot numerators with the zero-momentum insertion on the
  open line, over the data with line `0` doubled.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Bridge

section Piece

variable {n : ℕ} (hn : 6 ≤ n) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
  (E : Finset (Fin (n + 1))) (hw : IntNoSubdivergenceRefined 2 E fun i => awV (sh i))

/-- **A piece of `V` in the Ward–Takahashi routing**, at every `ε`. -/
theorem jef_vPiece (Q : Params) (s0 : sh 0 = 0) (F : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (c : Fin 4 × Fin 4 × Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ) (p : Fin 4 → ℝ)
    (α β : Fin 4) (hF : ∀ ℓ, F (loopAff mV ![p, 0] ℓ) = ∑ l, c l ℓ *
      (aSlotV l * electronNumerator Q.m (p - ℓ 0) * bSlotV l) α β) (ε : ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => F ℓ *
        ∏ i, (lineDenom (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) Ms ε
          i ℓ)⁻¹) =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
        (vData hn sh Ms E hw).slotN 0 Q.m aSlotV bSlotV c p ℓ α β *
          ∏ i, (lineDenom (vData hn sh Ms E hw).α ((vData hn sh Ms E hw).mom p)
            (vData hn sh Ms E hw).M ε i ℓ)⁻¹) := by
  refine (jointEnergyFirstIntegral_loopAff _ mV det_mV ![p, 0]).symm.trans ?_
  congr 1
  funext ℓ
  rw [hF, slotN_vData_apply hn sh Ms E hw Q s0]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [lineDenom_vData]

theorem cs_vData (hsh : ∀ i, i ≠ 0 → sh i ≠ 0) (i : Fin (n + 1)) (hi : i ≠ 0) :
    (vData hn sh Ms E hw).cs i = 0 := by
  change csV (sh i) = 0
  have h := hsh i hi
  generalize sh i = j at h
  fin_cases j <;> simp_all [csV]

end Piece

/-- The Ward–Takahashi data of the first piece of `V`. -/
noncomputable def vD1 (Q : Params) : SEData := vData (by norm_num) sh1 (ms1 Q) _ crit_shw.1

/-- The Ward–Takahashi data of the second piece of `V`. -/
noncomputable def vD2 (Q : Params) : SEData := vData (by norm_num) sh2 (ms2 Q) _ crit_shw.2.1

/-- The Ward–Takahashi data of the third piece of `V`. -/
noncomputable def vD3 (Q : Params) : SEData := vData (by norm_num) sh3 (ms3 Q) _ crit_shw.2.2.1

/-- The Ward–Takahashi data of the fourth piece of `V`. -/
noncomputable def vD4 (Q : Params) : SEData :=
  vData (by norm_num) sh4 (ms4 Q) _ crit_shw.2.2.2.1

/-- The Ward–Takahashi data of the fifth piece of `V`. -/
noncomputable def vD5 (Q : Params) : SEData :=
  vData (by norm_num) sh5 (ms5 Q) _ crit_shw.2.2.2.2

/-- The parametric value of a one-slot numerator of `V` over data `D`. -/
noncomputable abbrev vPiece (D : SEData) (Q : Params)
    (c : Fin 4 × Fin 4 × Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ) (p : Fin 4 → ℝ)
    (α β : Fin 4) : ℂ :=
  D.pvF (fun ℓ => D.slotN 0 Q.m aSlotV bSlotV c p ℓ α β) (D.mom p)

/-- **The limit of `V` in the Ward–Takahashi routing**: the sum over the five pieces. -/
noncomputable def vPV (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  vPiece (vD1 Q) Q (cSlotV1 Q) p α β + vPiece (vD2 Q) Q (cSlotV1 Q) p α β +
    vPiece (vD3 Q) Q (cSlotV1 Q) p α β + vPiece (vD4 Q) Q (cSlotV2 Q) p α β +
    vPiece (vD5 Q) Q (cSlotV2 Q) p α β

theorem s12_notMem : (0 : Fin 9) ∉ ({1, 2} : Finset (Fin 9)) := by decide

theorem s12_subset : insert (0 : Fin 9) ({1, 2} : Finset (Fin 9)) ⊆ {0, 1, 2} := by decide

theorem one_ne_two_nine : (1 : Fin 9) ≠ 2 := by decide

theorem s0_notMem : (0 : Fin 8) ∉ (∅ : Finset (Fin 8)) := by decide

theorem s0_subset : insert (0 : Fin 8) (∅ : Finset (Fin 8)) ⊆ {0} := by decide

/-- The limit of one piece, from an admissible quartic and positivity. -/
theorem tendsto_vPiece {D : SEData} {Q : Params}
    {c : Fin 4 × Fin 4 × Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ} {p : Fin 4 → ℝ}
    {α β : Fin 4} {S : Finset (Fin (D.m + 1))} (hS : (0 : Fin (D.m + 1)) ∉ S)
    (hSE : insert 0 S ⊆ D.E) (hcp : ∀ l, IsLoopPoly 2 2 (c l))
    (hcb : ∀ l, RefinedBound D.α S 2 (c l)) (hV : D.VPos (D.mom p)) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
        D.slotN 0 Q.m aSlotV bSlotV c p ℓ α β * ∏ i, (lineDenom D.α (D.mom p) D.M ε i ℓ)⁻¹))
      (𝓝[>] 0) (𝓝 (vPiece D Q c p α β)) := by
  obtain ⟨Q₀, hg, -, he⟩ := D.good_slotN 0 Q.m hS hSE hcp hcb p α β
  rw [vPiece, SEData.pvF_eq hg he hV]
  have h := SEData.tendsto_pv hg hV
  rwa [he] at h

/-- **The class value of `V` tends to `vPV`** below threshold. -/
theorem tendsto_repV_wt {Q : Params} (hpv1 : 1 + Q.c₁ + Q.c₂ = 0)
    (hpv2 : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0) {m₀ ν : ℝ} (hm0 : 0 < m₀)
    (hmm : m₀ ≤ Q.m) (hM1 : m₀ ≤ Q.M₁) (hM2 : m₀ ≤ Q.M₂) (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (hν2 : ν ≤ 2 * m₀) {p : Fin 4 → ℝ}
    (hs : -(Q.m + ν) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    Tendsto (fun ε : ℝ =>
      contractionValue₂ { Q with ε := ε } repV ![p] ![p] ![] ![α] ![β] ![]) (𝓝[>] 0)
        (𝓝 (vPV Q p α β)) := by
  have hm : 0 < Q.m := hm0.trans_le hmm
  have hγ : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have hΛ : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  obtain ⟨a1, b1, d1⟩ := cond_sh1 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a2, b2, d2⟩ := cond_sh2 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a3, b3, d3⟩ := cond_sh3 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a4, b4, d4⟩ := cond_sh4 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a5, b5, d5⟩ := cond_sh5 Q hM1 hM2 hmm hγ hΛ
  have t1 := tendsto_vPiece (D := vD1 Q) (Q := Q) (α := α) (β := β) s12_notMem s12_subset
    (isLoopPoly_cSlotV1 Q) (refinedBound_cSlotV1 _ sh1 _ _ _ Q rfl rfl one_ne_two_nine)
    (vpos_vData _ sh1 _ _ _ hm hm0 hmm hν0 hν2 a1 b1 d1 hs)
  have t2 := tendsto_vPiece (D := vD2 Q) (Q := Q) (α := α) (β := β) s12_notMem s12_subset
    (isLoopPoly_cSlotV1 Q) (refinedBound_cSlotV1 _ sh2 _ _ _ Q rfl rfl one_ne_two_nine)
    (vpos_vData _ sh2 _ _ _ hm hm0 hmm hν0 hν2 a2 b2 d2 hs)
  have t3 := tendsto_vPiece (D := vD3 Q) (Q := Q) (α := α) (β := β) s12_notMem s12_subset
    (isLoopPoly_cSlotV1 Q) (refinedBound_cSlotV1 _ sh3 _ _ _ Q rfl rfl one_ne_two_nine)
    (vpos_vData _ sh3 _ _ _ hm hm0 hmm hν0 hν2 a3 b3 d3 hs)
  have t4 := tendsto_vPiece (D := vD4 Q) (Q := Q) (α := α) (β := β) s0_notMem s0_subset
    (isLoopPoly_cSlotV2 Q) (refinedBound_cSlotV2 _ sh4 _ _ _ Q)
    (vpos_vData _ sh4 _ _ _ hm hm0 hmm hν0 hν2 a4 b4 d4 hs)
  have t5 := tendsto_vPiece (D := vD5 Q) (Q := Q) (α := α) (β := β) s0_notMem s0_subset
    (isLoopPoly_cSlotV2 Q) (refinedBound_cSlotV2 _ sh5 _ _ _ Q)
    (vpos_vData _ sh5 _ _ _ hm hm0 hmm hν0 hν2 a5 b5 d5 hs)
  refine ((((t1.add t2).add t3).add t4).add t5).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [contractionValue₂_repV_eq hpv1 hpv2 hε p α β]
  have h1 := fun F (hF : ∀ ℓ, F (loopAff mV ![p, 0] ℓ) = _) =>
    jef_vPiece (by norm_num) sh1 (ms1 Q) _ crit_shw.1 Q rfl F (cSlotV1 Q) p α β hF ε
  have h2 := fun F (hF : ∀ ℓ, F (loopAff mV ![p, 0] ℓ) = _) =>
    jef_vPiece (by norm_num) sh2 (ms2 Q) _ crit_shw.2.1 Q rfl F (cSlotV1 Q) p α β hF ε
  have h3 := fun F (hF : ∀ ℓ, F (loopAff mV ![p, 0] ℓ) = _) =>
    jef_vPiece (by norm_num) sh3 (ms3 Q) _ crit_shw.2.2.1 Q rfl F (cSlotV1 Q) p α β hF ε
  have h4 := fun F (hF : ∀ ℓ, F (loopAff mV ![p, 0] ℓ) = _) =>
    jef_vPiece (by norm_num) sh4 (ms4 Q) _ crit_shw.2.2.2.1 Q rfl F (cSlotV2 Q) p α β hF ε
  have h5 := fun F (hF : ∀ ℓ, F (loopAff mV ![p, 0] ℓ) = _) =>
    jef_vPiece (by norm_num) sh5 (ms5 Q) _ crit_shw.2.2.2.2 Q rfl F (cSlotV2 Q) p α β hF ε
  rw [h1 _ (vF1_loopAff Q p α β), h2 _ (vF1_loopAff Q p α β), h3 _ (vF1_loopAff Q p α β),
    h4 _ (vF2_loopAff Q p α β), h5 _ (vF2_loopAff Q p α β)]
  rfl

/-- **The Ward–Takahashi derivative of a piece of `V` along a ray.** -/
theorem hasDerivAt_vPiece_wt {D : SEData} {Q : Params}
    {c : Fin 4 × Fin 4 × Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ}
    {S : Finset (Fin (D.m + 1))} (hS : (0 : Fin (D.m + 1)) ∉ S) (hSE : insert 0 S ⊆ D.E)
    (hcp : ∀ l, IsLoopPoly 2 2 (c l)) (hcb : ∀ l, RefinedBound D.α S 2 (c l))
    (hM : D.M 0 = Q.m) (h0 : ∀ i, i ≠ 0 → D.cs i = 0) (r : Fin 4 → ℝ) {t₀ : ℝ}
    (hV : ∀ᶠ t in 𝓝 t₀, D.VPos (D.mom (t • r))) (α β : Fin 4) :
    HasDerivAt (fun t => vPiece D Q c (t • r) α β)
      (-(D.dup 0).pvF (fun ℓ => D.slotV 0 Q.m aSlotV bSlotV c (t₀ • r) r ℓ α β)
        (dbl 0 (D.mom (t₀ • r)))) t₀ :=
  D.hasDerivAt_pvF_slotN 0 Q.m hS hSE hcp hcb hM h0 r hV α β

/-- The parametric value of the insertion on the open line of a piece of `V`. -/
noncomputable abbrev vIns (D : SEData) (Q : Params)
    (c : Fin 4 × Fin 4 × Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ) (p r : Fin 4 → ℝ)
    (α β : Fin 4) : ℂ :=
  (D.dup 0).pvF (fun ℓ => D.slotV 0 Q.m aSlotV bSlotV c p r ℓ α β) (dbl 0 (D.mom p))

/-- The sum over the five pieces of the insertions on the open line. -/
noncomputable def vInsV (Q : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  vIns (vD1 Q) Q (cSlotV1 Q) p r α β + vIns (vD2 Q) Q (cSlotV1 Q) p r α β +
    vIns (vD3 Q) Q (cSlotV1 Q) p r α β + vIns (vD4 Q) Q (cSlotV2 Q) p r α β +
    vIns (vD5 Q) Q (cSlotV2 Q) p r α β

theorem sh1_ne : ∀ i : Fin 9, i ≠ 0 → sh1 i ≠ 0 := by decide

theorem sh2_ne : ∀ i : Fin 9, i ≠ 0 → sh2 i ≠ 0 := by decide

theorem sh3_ne : ∀ i : Fin 9, i ≠ 0 → sh3 i ≠ 0 := by decide

theorem sh4_ne : ∀ i : Fin 8, i ≠ 0 → sh4 i ≠ 0 := by decide

theorem sh5_ne : ∀ i : Fin 8, i ≠ 0 → sh5 i ≠ 0 := by decide

/-- **The Ward–Takahashi derivative of the limit of `V` along a ray.** -/
theorem hasDerivAt_vPV_wt {Q : Params} {m₀ ν : ℝ} (hm0 : 0 < m₀) (hmm : m₀ ≤ Q.m)
    (hM1 : m₀ ≤ Q.M₁) (hM2 : m₀ ≤ Q.M₂) (hν0 : 0 < ν) (hν : ν ≤ min Q.mγ Q.Λ)
    (hν2 : ν ≤ 2 * m₀) (r : Fin 4 → ℝ) {t₀ : ℝ}
    (hr : -(Q.m + ν) ^ 2 < Minkowski.dot (t₀ • r) (t₀ • r)) (α β : Fin 4) :
    HasDerivAt (fun t => vPV Q (t • r) α β) (-vInsV Q (t₀ • r) r α β) t₀ := by
  have hm : 0 < Q.m := hm0.trans_le hmm
  have hγ : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have hΛ : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  obtain ⟨a1, b1, d1⟩ := cond_sh1 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a2, b2, d2⟩ := cond_sh2 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a3, b3, d3⟩ := cond_sh3 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a4, b4, d4⟩ := cond_sh4 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a5, b5, d5⟩ := cond_sh5 Q hM1 hM2 hmm hγ hΛ
  have hreg := eventually_region r hr
  have t1 := hasDerivAt_vPiece_wt (D := vD1 Q) (Q := Q) s12_notMem s12_subset
    (isLoopPoly_cSlotV1 Q) (refinedBound_cSlotV1 _ sh1 _ _ _ Q rfl rfl one_ne_two_nine) rfl
    (cs_vData _ sh1 _ _ _ sh1_ne) r
    (hreg.mono fun _ ht => vpos_vData _ sh1 _ _ _ hm hm0 hmm hν0 hν2 a1 b1 d1 ht) α β
  have t2 := hasDerivAt_vPiece_wt (D := vD2 Q) (Q := Q) s12_notMem s12_subset
    (isLoopPoly_cSlotV1 Q) (refinedBound_cSlotV1 _ sh2 _ _ _ Q rfl rfl one_ne_two_nine) rfl
    (cs_vData _ sh2 _ _ _ sh2_ne) r
    (hreg.mono fun _ ht => vpos_vData _ sh2 _ _ _ hm hm0 hmm hν0 hν2 a2 b2 d2 ht) α β
  have t3 := hasDerivAt_vPiece_wt (D := vD3 Q) (Q := Q) s12_notMem s12_subset
    (isLoopPoly_cSlotV1 Q) (refinedBound_cSlotV1 _ sh3 _ _ _ Q rfl rfl one_ne_two_nine) rfl
    (cs_vData _ sh3 _ _ _ sh3_ne) r
    (hreg.mono fun _ ht => vpos_vData _ sh3 _ _ _ hm hm0 hmm hν0 hν2 a3 b3 d3 ht) α β
  have t4 := hasDerivAt_vPiece_wt (D := vD4 Q) (Q := Q) s0_notMem s0_subset
    (isLoopPoly_cSlotV2 Q) (refinedBound_cSlotV2 _ sh4 _ _ _ Q) rfl
    (cs_vData _ sh4 _ _ _ sh4_ne) r
    (hreg.mono fun _ ht => vpos_vData _ sh4 _ _ _ hm hm0 hmm hν0 hν2 a4 b4 d4 ht) α β
  have t5 := hasDerivAt_vPiece_wt (D := vD5 Q) (Q := Q) s0_notMem s0_subset
    (isLoopPoly_cSlotV2 Q) (refinedBound_cSlotV2 _ sh5 _ _ _ Q) rfl
    (cs_vData _ sh5 _ _ _ sh5_ne) r
    (hreg.mono fun _ ht => vpos_vData _ sh5 _ _ _ hm hm0 hmm hν0 hν2 a5 b5 d5 ht) α β
  have h := (((t1.add t2).add t3).add t4).add t5
  convert h using 1
  · funext t
    simp only [vPV, Pi.add_apply]
  · simp only [vInsV, vIns]
    ring

end QED.GradedProof.WI2

end
