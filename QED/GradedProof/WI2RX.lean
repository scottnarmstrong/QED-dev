/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2RXData

/-!
# The classes `R` and `X`: limits and Ward–Takahashi derivatives

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the classes `R` and `X`.

* `contractionValue₂_repR_eq`, `contractionValue₂_repX_eq`: at `ε > 0` the class value is
  `cRX Q` times the joint integral of the open chain over the denominators in the
  Ward–Takahashi routing (`wtData`), by the change of loop momenta `ℓ ↦ -ℓ + (p, p)`
  (`jointEnergyFirstIntegral_loopAff`).
* `tendsto_repR_wt`, `tendsto_repX_wt`: below threshold the class value tends to `cRX Q` times
  the parametric value of the chain in that routing.
* `hasDerivAt_repR_wt`, `hasDerivAt_repX_wt`: the derivative of that parametric value along a
  ray `t ↦ t r` is minus the sum over the three electron lines of the parametric values of the
  chain with the zero-momentum insertion `(m - k̸) r̸ (m - k̸)` on that line, over the data with
  the line doubled (`SEData.hasDerivAt_pvF_chN`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Routing
open QED.TwoLoop.Enumeration QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance

/-- The constant of the open chains of `R` and `X`: `(2π)⁻⁸ (ie)⁴ (1/i)³`. -/
noncomputable def cRX (Q : Params) : ℂ :=
  (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * ((I * Q.e) ^ 4 * (1 / I) ^ 3)

/-- The Ward–Takahashi data of `R`. -/
abbrev dR (Q : Params) : SEData := wtData aRw intCrit_Rw Q

/-- The Ward–Takahashi data of `X`. -/
abbrev dX (Q : Params) : SEData := wtData aXw intCrit_Xw Q

theorem mem_E_eRX {aw : Fin 7 → Fin 2 → ℤ} (hw : IntNoSubdivergenceRefined 2 {0, 1, 2} aw)
    (Q : Params) (j : Fin 3) : eRX j ∈ (wtData aw hw Q).E := by
  change eRX j ∈ ({0, 1, 2} : Finset (Fin 7))
  fin_cases j <;> decide

theorem M_eRX {aw : Fin 7 → Fin 2 → ℤ} (hw : IntNoSubdivergenceRefined 2 {0, 1, 2} aw)
    (Q : Params) (j : Fin 3) : (wtData aw hw Q).M (eRX j) = Q.m := by
  fin_cases j <;> rfl

theorem cs_eRX {aw : Fin 7 → Fin 2 → ℤ} (hw : IntNoSubdivergenceRefined 2 {0, 1, 2} aw)
    (Q : Params) (i : Fin 7) (h : ∀ j, eRX j ≠ i) : (wtData aw hw Q).cs i = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  fin_cases i <;> simp_all [eRX, wtData, cswRX]

theorem eventually_region {T : ℝ} (r : Fin 4 → ℝ) {t₀ : ℝ}
    (hr : -T ^ 2 < Minkowski.dot (t₀ • r) (t₀ • r)) :
    ∀ᶠ t in 𝓝 t₀, -T ^ 2 < Minkowski.dot (t • r) (t • r) := by
  have hc : Continuous fun t : ℝ => Minkowski.dot (t • r) (t • r) := by
    simp only [Minkowski.dot_eq, Pi.smul_apply, smul_eq_mul]
    fun_prop
  exact (hc.tendsto t₀).eventually (lt_mem_nhds hr)

/-! ### The rainbow `R` -/

theorem vpos_dR (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν) (hν : ν ≤ min Q.mγ Q.Λ)
    {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p) : (dR Q).VPos ((dR Q).mom p) :=
  vpos_wtData intCrit_Rw Q rr_aR (rr_ppR p)
    (min_one_mul_pos (by positivity) (lt_min (by positivity) (by positivity)) hp)
    fun _ hz hz1 hU => symanzikV_R_ge Q hm hν0 hν hp hz hz1 hU

theorem numG_repR_loopAff (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    numG Q repR p (loopAff (-1) ![p, p] ℓ) =
      ((I * Q.e) ^ 4 * (1 / I) ^ 3) • (dR Q).chN eRX (wR Q) Q.m p ℓ := by
  obtain ⟨i1, i2, i3, -, -⟩ := idxR_apply
  rw [numG_repR]
  simp only [SEData.chN, chainAt, SEData.chE,
    lineMomentum_wtData intCrit_Rw Q rr_aR (rr_ppR p), rMom, i1, i2, i3, eRX]
  rfl

/-- **The class value of `R` at `ε > 0` in the Ward–Takahashi routing.** -/
theorem contractionValue₂_repR_eq (Q : Params) {ε : ℝ} (hε : 0 < ε) (p : Fin 4 → ℝ)
    (α β : Fin 4) :
    contractionValue₂ { Q with ε := ε } repR ![p] ![p] ![] ![α] ![β] ![] =
      cRX Q * QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
        (dR Q).chN eRX (wR Q) Q.m p ℓ α β *
          ∏ i, (lineDenom (dR Q).α ((dR Q).mom p) (dR Q).M ε i ℓ)⁻¹) := by
  unfold contractionValue₂
  rw [loopCount_repR, ← jointEnergyFirstIntegral_loopAff _ (-1) det_neg_one ![p, p],
    ← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  congr 1
  funext ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring _ (sameCycle_of_pow (n := 5) (by decide +kernel)),
    contractionAmplitude₂_eq { Q with ε := ε } hε.ne', r_denominator]
  have hN := congrArg (fun A => A α β) (numG_repR_loopAff Q p ℓ)
  simp only [numG, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at hN
  change _ * (amplitudeNumerator Q repR (zeroFlavoring k_gggg) ![p] ![] _ ![α] ![β] ![] * _) = _
  have hD : ∏ i, (lineDenom (castLoopMatrix aR) (ppR p) (massesSE Q) ε i
      (loopAff (-1) ![p, p] ℓ))⁻¹ = ∏ i, (lineDenom (dR Q).α ((dR Q).mom p) (dR Q).M ε i ℓ)⁻¹ :=
    Finset.prod_congr rfl fun i _ => by rw [lineDenom_wtData intCrit_Rw Q rr_aR (rr_ppR p)]
  rw [hN, cRX]
  change _ * (_ * ∏ i, (lineDenom (castLoopMatrix aR) (ppR p) (massesSE Q) ε i
      (loopAff (-1) ![p, p] ℓ))⁻¹) = _
  rw [hD]
  ring

/-- **The class value of `R` tends to the parametric value in the Ward–Takahashi routing.** -/
theorem tendsto_repR_wt (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε => contractionValue₂ { Q with ε := ε } repR ![p] ![p] ![] ![α] ![β] ![])
      (𝓝[>] 0) (𝓝 (cRX Q * (dR Q).pvF (fun ℓ => (dR Q).chN eRX (wR Q) Q.m p ℓ α β)
        ((dR Q).mom p))) := by
  obtain ⟨Q₀, hg, -, he⟩ :=
    (dR Q).good_chN (wR Q) Q.m eRX_injective (mem_E_eRX intCrit_Rw Q) p α β
  have hV := vpos_dR Q hm hν0 hν hp
  rw [SEData.pvF_eq hg he hV]
  have h := (SEData.tendsto_pv hg hV).const_mul (cRX Q)
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (contractionValue₂_repR_eq Q hε p α β).symm

/-- **The Ward–Takahashi derivative of the class `R` along a ray.** -/
theorem hasDerivAt_repR_wt (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (r : Fin 4 → ℝ) {t₀ : ℝ}
    (hr : -(Q.m + ν) ^ 2 < Minkowski.dot (t₀ • r) (t₀ • r)) (α β : Fin 4) :
    HasDerivAt (fun t => (dR Q).pvF (fun ℓ => (dR Q).chN eRX (wR Q) Q.m (t • r) ℓ α β)
        ((dR Q).mom (t • r)))
      (-∑ j, ((dR Q).dup (eRX j)).pvF
        (fun ℓ => (dR Q).chV eRX (wR Q) Q.m (t₀ • r) r ℓ j α β)
        (dbl (eRX j) ((dR Q).mom (t₀ • r)))) t₀ :=
  (dR Q).hasDerivAt_pvF_chN (wR Q) Q.m eRX_injective (mem_E_eRX intCrit_Rw Q)
    (M_eRX intCrit_Rw Q) (cs_eRX intCrit_Rw Q) r
    ((eventually_region r hr).mono fun _ ht => vpos_dR Q hm hν0 hν ht) α β

/-! ### The crossed `X` -/

theorem vpos_dX (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν) (hν : ν ≤ min Q.mγ Q.Λ)
    (hν2 : ν ≤ 2 * Q.m) {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p) :
    (dX Q).VPos ((dX Q).mom p) :=
  vpos_wtData intCrit_Xw Q rr_aX (rr_ppX p)
    (min_one_mul_pos (by positivity) (lt_min (by positivity) (by positivity)) hp)
    fun _ hz hz1 hU => symanzikV_X_ge Q hm hν0 hν hν2 hp hz hz1 hU

theorem numG_repX_loopAff (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    numG Q repX p (loopAff (-1) ![p, p] ℓ) =
      ((I * Q.e) ^ 4 * (1 / I) ^ 3) • (dX Q).chN eRX (wX Q) Q.m p ℓ := by
  obtain ⟨i1, i2, i3, -, -⟩ := idxX_apply
  rw [numG_repX]
  simp only [SEData.chN, chainAt, SEData.chE,
    lineMomentum_wtData intCrit_Xw Q rr_aX (rr_ppX p), xMom, i1, i2, i3, eRX]
  rfl

/-- **The class value of `X` at `ε > 0` in the Ward–Takahashi routing.** -/
theorem contractionValue₂_repX_eq (Q : Params) {ε : ℝ} (hε : 0 < ε) (p : Fin 4 → ℝ)
    (α β : Fin 4) :
    contractionValue₂ { Q with ε := ε } repX ![p] ![p] ![] ![α] ![β] ![] =
      cRX Q * QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
        (dX Q).chN eRX (wX Q) Q.m p ℓ α β *
          ∏ i, (lineDenom (dX Q).α ((dX Q).mom p) (dX Q).M ε i ℓ)⁻¹) := by
  unfold contractionValue₂
  rw [loopCount_repX, ← jointEnergyFirstIntegral_loopAff _ (-1) det_neg_one ![p, p],
    ← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  congr 1
  funext ℓ
  rw [regulatedAmplitude₂_eq_zeroFlavoring _ (sameCycle_of_pow (n := 5) (by decide +kernel)),
    contractionAmplitude₂_eq { Q with ε := ε } hε.ne', x_denominator]
  have hN := congrArg (fun A => A α β) (numG_repX_loopAff Q p ℓ)
  simp only [numG, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at hN
  change _ * (amplitudeNumerator Q repX (zeroFlavoring k_gggg) ![p] ![] _ ![α] ![β] ![] * _) = _
  have hD : ∏ i, (lineDenom (castLoopMatrix aX) (ppX p) (massesSE Q) ε i
      (loopAff (-1) ![p, p] ℓ))⁻¹ = ∏ i, (lineDenom (dX Q).α ((dX Q).mom p) (dX Q).M ε i ℓ)⁻¹ :=
    Finset.prod_congr rfl fun i _ => by rw [lineDenom_wtData intCrit_Xw Q rr_aX (rr_ppX p)]
  rw [hN, cRX]
  change _ * (_ * ∏ i, (lineDenom (castLoopMatrix aX) (ppX p) (massesSE Q) ε i
      (loopAff (-1) ![p, p] ℓ))⁻¹) = _
  rw [hD]
  ring

/-- **The class value of `X` tends to the parametric value in the Ward–Takahashi routing.** -/
theorem tendsto_repX_wt (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (hν2 : ν ≤ 2 * Q.m) {p : Fin 4 → ℝ}
    (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    Tendsto (fun ε => contractionValue₂ { Q with ε := ε } repX ![p] ![p] ![] ![α] ![β] ![])
      (𝓝[>] 0) (𝓝 (cRX Q * (dX Q).pvF (fun ℓ => (dX Q).chN eRX (wX Q) Q.m p ℓ α β)
        ((dX Q).mom p))) := by
  obtain ⟨Q₀, hg, -, he⟩ :=
    (dX Q).good_chN (wX Q) Q.m eRX_injective (mem_E_eRX intCrit_Xw Q) p α β
  have hV := vpos_dX Q hm hν0 hν hν2 hp
  rw [SEData.pvF_eq hg he hV]
  have h := (SEData.tendsto_pv hg hV).const_mul (cRX Q)
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (contractionValue₂_repX_eq Q hε p α β).symm

/-- **The Ward–Takahashi derivative of the class `X` along a ray.** -/
theorem hasDerivAt_repX_wt (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (hν2 : ν ≤ 2 * Q.m) (r : Fin 4 → ℝ) {t₀ : ℝ}
    (hr : -(Q.m + ν) ^ 2 < Minkowski.dot (t₀ • r) (t₀ • r)) (α β : Fin 4) :
    HasDerivAt (fun t => (dX Q).pvF (fun ℓ => (dX Q).chN eRX (wX Q) Q.m (t • r) ℓ α β)
        ((dX Q).mom (t • r)))
      (-∑ j, ((dX Q).dup (eRX j)).pvF
        (fun ℓ => (dX Q).chV eRX (wX Q) Q.m (t₀ • r) r ℓ j α β)
        (dbl (eRX j) ((dX Q).mom (t₀ • r)))) t₀ :=
  (dX Q).hasDerivAt_pvF_chN (wX Q) Q.m eRX_injective (mem_E_eRX intCrit_Xw Q)
    (M_eRX intCrit_Xw Q) (cs_eRX intCrit_Xw Q) r
    ((eventually_region r hr).mono fun _ ht => vpos_dX Q hm hν0 hν hν2 ht) α β

end QED.GradedProof.WI2

end
