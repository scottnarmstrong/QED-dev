/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2SlotWard
public import QED.GradedProof.SE2FormP
public import QED.GradedProof.WI2RX

/-!
# The classes `P0`, `P1`: limits and Ward–Takahashi derivatives

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the classes with the `δ₃` insertion on the internal photon line.

* `SEData.good_slotN`: an admissible cubic quartic for a one-slot numerator.
* `dP`: the product data of `kindsSEP` (no rerouting: the external momentum already flows only
  through the electron line `0`); `slotN_dP`: the one-slot numerator with
  `Aₗ = γ^ρ`, `Bₗ = γ^ν`, `cₗ = photonNum(ℓ₀)_{νρ}` is the numerator `numSEP`.
* `tendsto_repP0_wt`, `tendsto_repP1_wt`: below threshold the class value tends to
  `κ auxLimit⁻¹` times the parametric value of the one-slot numerator.
* `hasDerivAt_dP_wt`: the derivative of that parametric value along a ray `t ↦ t r` is minus the
  parametric value of the one-slot numerator with the zero-momentum insertion, over the data with
  line `0` doubled (`SEData.hasDerivAt_pvF_slotN`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassIntegrable QED.TwoLoop.Bridge QED.GradedProof.WI2

variable (D : SEData) (e₀ : Fin (D.m + 1)) (mass : ℝ) {ι : Type*} [Fintype ι]
  {A B : ι → Matrix (Fin 4) (Fin 4) ℂ} {c : ι → (Fin 2 → Fin 4 → ℝ) → ℂ}

/-- An admissible cubic quartic for an entry of a one-slot numerator. -/
theorem good_slotN {S : Finset (Fin (D.m + 1))} (hS : e₀ ∉ S) (hSE : insert e₀ S ⊆ D.E)
    (hcp : ∀ l, IsLoopPoly 2 2 (c l)) (hcb : ∀ l, RefinedBound D.α S 2 (c l))
    (p : Fin 4 → ℝ) (a b : Fin 4) : ∃ Q : LoopQuartic, D.Good Q ∧ Q.quart = 0 ∧
      Q.eval = fun ℓ => D.slotN e₀ mass A B c p ℓ a b := by
  obtain ⟨Q, hq, hQ⟩ :=
    IsLoopPoly.exists_loopQuartic_cubic (D.isLoopPoly_slotN e₀ mass (A := A) (B := B) hcp p a b)
  refine ⟨Q, ⟨Or.inr hq, ?_⟩, hq, hQ⟩
  rw [hQ]
  exact (D.refinedBound_slotN e₀ mass (A := A) (B := B) hS hSE hcb p a b).mono subset_rfl
    (by norm_num)

end QED.GradedProof.SE2.SEData

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Routing
open QED.TwoLoop.Enumeration QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.TwoLoop.CountertermLimit

/-- The data of `P0`, `P1`: the product data of `kindsSEP`. -/
noncomputable abbrev dP (Q : Params) : SEData :=
  kindsData (by norm_num) kindsSEP (massesSEP Q) (by decide)

/-- The left factors `γ^ρ` of the one-slot numerator of `P0`, `P1`. -/
noncomputable def aSlotP : Fin 4 × Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun l => Dirac.gamma l.2

/-- The right factors `γ^ν` of the one-slot numerator of `P0`, `P1`. -/
noncomputable def bSlotP : Fin 4 × Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun l => Dirac.gamma l.1

/-- The scalar coefficients `photonNum(ℓ₀)_{νρ}` of the one-slot numerator of `P0`, `P1`. -/
noncomputable def cSlotP (Q : Params) : Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ :=
  fun l ℓ => photonNum Q.δ₃ Q.mγ Q.Λ (ℓ 0) l.1 l.2

theorem alpha_dP (Q : Params) {i : Fin 8} (hi : kindsSEP i ≠ .aux) : (dP Q).α i = ![1, 0] := by
  change castLoopMatrix (fun i => (kindsSEP i).dir) i = _
  funext s
  rcases h : kindsSEP i with _ | _ | _ | _
  · fin_cases s <;> simp [castLoopMatrix, h, LineKind.dir]
  · fin_cases s <;> simp [castLoopMatrix, h, LineKind.dir]
  · fin_cases s <;> simp [castLoopMatrix, h, LineKind.dir]
  · exact absurd h hi

theorem lineMomentum_dP_zero (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Integration.TwoLoop.lineMomentum (dP Q).α ((dP Q).mom p) 0 ℓ = p + ℓ 0 := by
  funext μ
  simp [Integration.TwoLoop.lineMomentum, SEData.mom, dP, kindsData, castLoopMatrix, kindsSEP,
    LineKind.dir, Fin.sum_univ_two, add_comm]

theorem slotN_dP (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dP Q).slotN 0 Q.m aSlotP bSlotP (cSlotP Q) p ℓ = numSEP Q p (ℓ 0) := by
  rw [SEData.slotN, numSEP, seChain, Fintype.sum_prod_type]
  simp only [SEData.slotE, lineMomentum_dP_zero, aSlotP, bSlotP, cSlotP]

theorem refinedBound_coord_dP (Q : Params) {i : Fin 8} (hi : kindsSEP i = .pho) (ν : Fin 4) :
    RefinedBound (dP Q).α ({i} : Finset (Fin 8)) 1 fun ℓ => ((ℓ 0 ν : ℝ) : ℂ) := by
  have h := refinedBound_lineMomentum (dP Q).α (fun _ => 0) i ν
  have e : (fun ℓ => ((Integration.TwoLoop.lineMomentum (dP Q).α (fun _ => 0) i ℓ ν : ℝ) : ℂ)) =
      fun ℓ => ((ℓ 0 ν : ℝ) : ℂ) := by
    funext ℓ
    simp [Integration.TwoLoop.lineMomentum, alpha_dP Q (i := i) (by rw [hi]; decide),
      Fin.sum_univ_two]
  rw [e] at h
  exact h

theorem refinedBound_quad_dP (Q : Params) (a b : Fin 4) :
    RefinedBound (dP Q).α ({1, 2} : Finset (Fin 8)) 2
      fun ℓ => ((ℓ 0 a : ℝ) : ℂ) * ((ℓ 0 b : ℝ) : ℂ) := by
  have h := (refinedBound_coord_dP Q (i := 1) rfl a).mul (refinedBound_coord_dP Q (i := 2) rfl b)
    (by change Disjoint ({1} : Finset (Fin 8)) {2}; decide)
  exact h.mono (by change ({1} ∪ {2} : Finset (Fin 8)) ⊆ {1, 2}; decide) le_rfl

theorem propDenom_zero_eq (k : Fin 4 → ℝ) :
    propDenom 0 0 k = -(((k 0 : ℝ) : ℂ) * ((k 0 : ℝ) : ℂ)) + ((k 1 : ℝ) : ℂ) * ((k 1 : ℝ) : ℂ) +
      ((k 2 : ℝ) : ℂ) * ((k 2 : ℝ) : ℂ) + ((k 3 : ℝ) : ℂ) * ((k 3 : ℝ) : ℂ) := by
  simp only [propDenom, Minkowski.dot_eq]
  push_cast
  ring

theorem refinedBound_cP (Q : Params) (l : Fin 4 × Fin 4) :
    RefinedBound (dP Q).α ({1, 2} : Finset (Fin 8)) 2 (cSlotP Q l) := by
  unfold cSlotP photonNum
  refine RefinedBound.const_mul _ (RefinedBound.sum _ fun a _ => RefinedBound.sum _ fun b _ => ?_)
  simp only [photonCtFactor_eq, propDenom_zero_eq]
  have hq := refinedBound_quad_dP Q
  have h := ((((((hq 0 0).neg.add (hq 1 1)).add (hq 2 2)).add (hq 3 3)).const_mul
    (-(I / 2) * Q.δ₃ * Minkowski.metric a b)).add ((hq a b).const_mul (I / 2 * Q.δ₃))).const_mul
    (pvPhotonNum Q.mγ Q.Λ l.1 a * pvPhotonNum Q.mγ Q.Λ l.2 b)
  convert h using 2 with ℓ
  ring

theorem isLoopPoly_cP (Q : Params) (l : Fin 4 × Fin 4) : IsLoopPoly 2 2 (cSlotP Q l) :=
  isLoopPoly_photonNum _ _ _ _ _

theorem cs_dP (Q : Params) (i : Fin ((dP Q).m + 1)) (h : i ≠ 0) : (dP Q).cs i = 0 := by
  change (if kindsSEP i = .inn then (1 : ℝ) else 0) = 0
  revert i
  change ∀ i : Fin 8, i ≠ 0 → (if kindsSEP i = .inn then (1 : ℝ) else 0) = 0
  intro i h
  fin_cases i <;> simp_all [kindsSEP]

theorem vpos_dP (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν) (hν : ν ≤ min Q.mγ Q.Λ)
    {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p) : (dP Q).VPos ((dP Q).mom p) := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  obtain ⟨hMe, hMp⟩ := massesSEP_bounds Q hmγ hΛ
  refine ⟨min 1 (1 + Minkowski.dot p p / (Q.m + ν) ^ 2) * min (Q.m ^ 2) (ν ^ 2),
    min_one_mul_pos (by positivity) (lt_min (by positivity) (by positivity)) hp,
    fun z hz hz1 hU => ?_⟩
  rw [kindsData_mom _ _ (by decide)]
  exact symanzikV_kinds_se_ge kindsSEP (by decide) (massesSEP Q) hm hν0 hp hMe
    (fun i hi => (pow_le_pow_left₀ hν0.le hν 2).trans (hMp i hi)) hz hz1 hU

theorem zero_notMem_S_dP : (0 : Fin 8) ∉ ({1, 2} : Finset (Fin 8)) := by decide

theorem insert_subset_E_dP : insert (0 : Fin 8) ({1, 2} : Finset (Fin 8)) ⊆ {0, 1, 2, 3} := by
  decide

theorem prod_lineDenom_dP (Q : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, (lineDenom (dP Q).α ((dP Q).mom p) (dP Q).M ε i ℓ)⁻¹ =
      ∏ i : Fin 8, (propDenom (massesSEP Q i) ε ((kindsSEP i).lineMom p p ℓ))⁻¹ := by
  rw [kindsData_mom _ _ (by decide)]
  exact prod_lineDenom_kinds _ _ _ _ _ _

/-- The integrand of the data of `P0`, `P1` at `ε ≠ 0` is the one-loop integrand times the
auxiliary loop. -/
theorem integrand_dP (Q : Params) {ε : ℝ} (hε : ε ≠ 0) (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (α β : Fin 4) :
    kappaSE Q.e * ((dP Q).slotN 0 Q.m aSlotP bSlotP (cSlotP Q) p ℓ α β *
        ∏ i, (lineDenom (dP Q).α ((dP Q).mom p) (dP Q).M ε i ℓ)⁻¹) =
      kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m ε (p + ℓ 0))
        (photonInsertion Q.δ₃ Q.mγ Q.Λ ε (ℓ 0)) α β * ((propDenom Q.m ε (ℓ 1))⁻¹) ^ 3 := by
  rw [slotN_dP, prod_lineDenom_dP, integrand_seP_eq Q hε, Matrix.smul_apply, smul_eq_mul]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsSEP, massesSEP,
    LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

/-- **The one-loop `δ₃` self-energy integral tends to the parametric value of the data of `P0`,
`P1`** (divided by the auxiliary loop). -/
theorem tendsto_seP_dP (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun q =>
        kappaSE Q.e * seChain (QED.OneLoop.electronPropagator Q.m ε (p + q))
          (photonInsertion Q.δ₃ Q.mγ Q.Λ ε q) α β)
      (𝓝[>] 0) (𝓝 ((auxLimit Q.m)⁻¹ * (kappaSE Q.e *
        (dP Q).pvF (fun ℓ => (dP Q).slotN 0 Q.m aSlotP bSlotP (cSlotP Q) p ℓ α β)
          ((dP Q).mom p)))) := by
  obtain ⟨Q₀, hg, -, he⟩ := (dP Q).good_slotN 0 Q.m zero_notMem_S_dP insert_subset_E_dP
    (isLoopPoly_cP Q) (refinedBound_cP Q) p α β
  have hV := vpos_dP Q hm hν0 hν hp
  rw [SEData.pvF_eq hg he hV]
  have hH := tendsto_energyFirstIntegral_aux hm
  have hH0 := auxLimit_ne_zero hm
  have h := (hH.inv₀ hH0).mul ((SEData.tendsto_pv hg hV).const_mul (kappaSE Q.e))
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hH.eventually_ne hH0] with ε (hε : 0 < ε) hne
  rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  have e := funext fun ℓ => integrand_dP Q hε.ne' p ℓ α β
  rw [e, jointEnergyFirstIntegral_two_mul (fun q => kappaSE Q.e * seChain
    (QED.OneLoop.electronPropagator Q.m ε (p + q)) (photonInsertion Q.δ₃ Q.mγ Q.Λ ε q) α β)
    (fun k => ((propDenom Q.m ε k)⁻¹) ^ 3), mul_comm]
  exact mul_inv_cancel_right₀ hne _

/-- **The class value of `P0` tends to the parametric value of its data.** -/
theorem tendsto_repP0_wt (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε => contractionValue₂ { Q with ε := ε } repP0 ![p] ![p] ![] ![α] ![β] ![])
      (𝓝[>] 0) (𝓝 ((auxLimit Q.m)⁻¹ * (kappaSE Q.e *
        (dP Q).pvF (fun ℓ => (dP Q).slotN 0 Q.m aSlotP bSlotP (cSlotP Q) p ℓ α β)
          ((dP Q).mom p)))) := by
  refine (tendsto_seP_dP Q hm hν0 hν hp α β).congr fun ε => ?_
  exact (contractionValue₂_of_one_chord _ p0_isChord_iff (p0Mom p) (p0_isConserved p)
    (fun ℓ => (p0Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => p0_integrand { Q with ε := ε } p ℓ α β)).symm

/-- **The class value of `P1` tends to the parametric value of its data.** -/
theorem tendsto_repP1_wt (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε => contractionValue₂ { Q with ε := ε } repP1 ![p] ![p] ![] ![α] ![β] ![])
      (𝓝[>] 0) (𝓝 ((auxLimit Q.m)⁻¹ * (kappaSE Q.e *
        (dP Q).pvF (fun ℓ => (dP Q).slotN 0 Q.m aSlotP bSlotP (cSlotP Q) p ℓ α β)
          ((dP Q).mom p)))) := by
  refine (tendsto_seP_dP Q hm hν0 hν hp α β).congr fun ε => ?_
  exact (contractionValue₂_of_one_chord _ p1_isChord_iff (p1Mom p) (p1_isConserved p)
    (fun ℓ => (p1Mom_apply p ℓ).1) ![α] ![β] ![] _ p
    (fun ℓ => p1_integrand { Q with ε := ε } p ℓ α β)).symm

/-- **The Ward–Takahashi derivative of the data of `P0`, `P1` along a ray.** -/
theorem hasDerivAt_dP_wt (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (r : Fin 4 → ℝ) {t₀ : ℝ}
    (hr : -(Q.m + ν) ^ 2 < Minkowski.dot (t₀ • r) (t₀ • r)) (α β : Fin 4) :
    HasDerivAt (fun t => (dP Q).pvF
        (fun ℓ => (dP Q).slotN 0 Q.m aSlotP bSlotP (cSlotP Q) (t • r) ℓ α β)
        ((dP Q).mom (t • r)))
      (-((dP Q).dup 0).pvF (fun ℓ => (dP Q).slotV 0 Q.m aSlotP bSlotP (cSlotP Q) (t₀ • r) r ℓ α β)
        (dbl 0 ((dP Q).mom (t₀ • r)))) t₀ :=
  (dP Q).hasDerivAt_pvF_slotN 0 Q.m zero_notMem_S_dP insert_subset_E_dP (isLoopPoly_cP Q)
    (refinedBound_cP Q) rfl (cs_dP Q) r
    ((eventually_region r hr).mono fun _ ht => vpos_dP Q hm hν0 hν ht) α β

end QED.GradedProof.WI2

end
