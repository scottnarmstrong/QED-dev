/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2FData
public import QED.GradedProof.SE2ClassF

/-!
# The class `F` in the Ward–Takahashi routing

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the class `F`.

* `tendsto_repF_wt`: the class value of `F` tends to the parametric value of the two-slot
  numerator over the data `dF`, divided by the auxiliary loop.
* `hasDerivAt_dF_wt`: the Ward–Takahashi derivative of that parametric value along a ray: the
  parametric value with the middle matrix replaced by `δ₂ r̸` (the derivative of the counterterm
  vertex), minus the two parametric values with the zero-momentum insertion on an electron line.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ClassIntegrable

/-- The integrand of the data of `F` at `ε ≠ 0` is the one-loop integrand times the auxiliary
loop. -/
theorem integrand_dF (Q : Params) {ε : ℝ} (hε : ε ≠ 0) (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (α β : Fin 4) :
    kappaSE Q.e * ((dF Q).twN eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) p ℓ α β *
        ∏ i, (lineDenom (dF Q).α ((dF Q).mom p) (dF Q).M ε i ℓ)⁻¹) =
      kappaSE Q.e * seChain (electronInsertion Q.m ε Q.δ₂ Q.δm (p + ℓ 0))
        (QED.OneLoop.photonPropagator Q.mγ Q.Λ ε (ℓ 0)) α β *
          ((propDenom Q.m ε (ℓ 1))⁻¹) ^ 3 := by
  rw [twN_dF, prod_lineDenom_dF, electronInsertion_eq_smul, photonPropagator_eq_scalar _ _ hε,
    seChain_smul_in, seChain_smul_photon, smul_smul, Matrix.smul_apply, smul_eq_mul]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsF, massesF, LineKind.lineMom,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

theorem eF_ne : eF 0 ≠ eF 1 := by decide

theorem two_ne_eF_zero : (2 : Fin 7) ≠ eF 0 := by decide

theorem two_ne_eF_one : (2 : Fin 7) ≠ eF 1 := by decide

theorem eF_mem : ∀ j, eF j ∈ ({0, 1, 2} : Finset (Fin 7)) := by decide

theorem two_mem_EF : (2 : Fin 7) ∈ ({0, 1, 2} : Finset (Fin 7)) := by decide

theorem good_twN_dF (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) :
    ∃ Q₀ : LoopQuartic, (dF Q).Good Q₀ ∧ Q₀.quart = 0 ∧
      Q₀.eval = fun ℓ => (dF Q).twN eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) p ℓ α β := by
  obtain ⟨Q₀, hq, hQ⟩ := IsLoopPoly.exists_loopQuartic_cubic
    ((dF Q).isLoopPoly_twN eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) (isLoopPolyMat_gF Q) p α β)
  refine ⟨Q₀, ⟨Or.inr hq, ?_⟩, hq, hQ⟩
  rw [hQ]
  exact ((dF Q).refinedBound_twN eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) (e₂ := (2 : Fin 7))
    eF_ne two_ne_eF_zero two_ne_eF_one eF_mem two_mem_EF (refinedBoundMat_gF Q) p α
      β).mono subset_rfl (by norm_num)

/-- **The one-loop counterterm-inserted self-energy integral tends to the parametric value of
the data of `F`** (divided by the auxiliary loop). -/
theorem tendsto_seF_dF (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q =>
        kappaSE Q.e * seChain (electronInsertion Q.m ε Q.δ₂ Q.δm (p + q))
          (QED.OneLoop.photonPropagator Q.mγ Q.Λ ε q) α β)
      (𝓝[>] 0) (𝓝 ((auxLimit Q.m)⁻¹ * (kappaSE Q.e *
        (dF Q).pvF (fun ℓ => (dF Q).twN eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) p ℓ α β)
          ((dF Q).mom p)))) := by
  obtain ⟨Q₀, hg, -, he⟩ := good_twN_dF Q p α β
  have hV := vpos_dF Q hm hν0 hν hp
  rw [SEData.pvF_eq hg he hV]
  have hH := tendsto_energyFirstIntegral_aux hm
  have hH0 := auxLimit_ne_zero hm
  have h := (hH.inv₀ hH0).mul ((SEData.tendsto_pv hg hV).const_mul (kappaSE Q.e))
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hH.eventually_ne hH0] with ε (hε : 0 < ε) hne
  rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  have e := funext fun ℓ => integrand_dF Q hε.ne' p ℓ α β
  rw [e, jointEnergyFirstIntegral_two_mul (fun q => kappaSE Q.e * seChain
    (electronInsertion Q.m ε Q.δ₂ Q.δm (p + q)) (QED.OneLoop.photonPropagator Q.mγ Q.Λ ε q) α β)
    (fun k => ((propDenom Q.m ε k)⁻¹) ^ 3), mul_comm]
  exact mul_inv_cancel_right₀ hne _

/-- **The class value of `F` tends to the parametric value of its data.** -/
theorem tendsto_repF_wt (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε => contractionValue₂ { Q with ε := ε } repF ![p] ![p] ![] ![α] ![β] ![])
      (𝓝[>] 0) (𝓝 ((auxLimit Q.m)⁻¹ * (kappaSE Q.e *
        (dF Q).pvF (fun ℓ => (dF Q).twN eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) p ℓ α β)
          ((dF Q).mom p)))) := by
  refine (tendsto_seF_dF Q hm hν0 hν hp α β).congr fun ε => ?_
  exact (contractionValue₂_of_one_chord _ f_isChord_iff (fMom p) (f_isConserved p)
    (fun ℓ => (fMom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => f_integrand { Q with ε := ε } p ℓ α β)).symm

theorem cs_dF (Q : Params) (i : Fin 7) (h : ∀ j, eF j ≠ i) : (dF Q).cs i = 0 := by
  have h0 := h 0
  have h1 := h 1
  fin_cases i
  · exact absurd rfl h0
  · exact absurd rfl h1
  all_goals simp [dF, kindsF]

/-- **The Ward–Takahashi derivative of the data of `F` along a ray.** -/
theorem hasDerivAt_dF_wt (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (r : Fin 4 → ℝ) {t₀ : ℝ}
    (hr : -(Q.m + ν) ^ 2 < Minkowski.dot (t₀ • r) (t₀ • r)) (α β : Fin 4) :
    HasDerivAt (fun t => (dF Q).pvF
        (fun ℓ => (dF Q).twN eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) (t • r) ℓ α β)
        ((dF Q).mom (t • r)))
      ((dF Q).pvF (fun ℓ => (dF Q).twR eF Q.m aSlotF bSlotF (cSlotF Q) (t₀ • r)
          ((Q.δ₂ : ℂ) • Dirac.slash r) ℓ α β) ((dF Q).mom (t₀ • r)) -
        ∑ j, ((dF Q).dup (eF j)).pvF
          (fun ℓ => (dF Q).twV eF Q.m aSlotF bSlotF (cSlotF Q) (gF Q) (t₀ • r) r ℓ j α β)
          (dbl (eF j) ((dF Q).mom (t₀ • r)))) t₀ :=
  (dF Q).hasDerivAt_pvF_twN Q.m (e₂ := (2 : Fin 7)) eF_ne two_ne_eF_zero two_ne_eF_one
    eF_mem two_mem_EF (refinedBoundMat_gF Q) (isLoopPolyMat_gF Q) (isLoopPolyMat_gF_mom Q)
    (fun j => by fin_cases j <;> rfl) (cs_dF Q) r _ (gF_smul Q r)
    ((eventually_region r hr).mono fun _ ht => vpos_dF Q hm hν0 hν ht) α β

end QED.GradedProof.WI2

end
