/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2VData
public import QED.GradedProof.WI2SlotWard

/-!
# The class `V` in the Ward–Takahashi routing: one-slot numerators

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the vacuum-polarization class `V`. In the Ward–Takahashi routing the numerators
`vF1`, `vF2` of the five pieces are one-slot numerators `∑ₗ cₗ γ^{l₁} (m - k̸₀) γ^{l₀}` over
`l = (l₀, l₁, l₂, l₃)`, with the open-line momentum `k₀ = p - ℓ₀` and scalar coefficients:

* `cSlotV1`: the metric factors times the bubble trace `Tr[γ^{l₂} (-u̸) γ^{l₃} (-v̸)]` at
  `u = ℓ₁`, `v = ℓ₀ + ℓ₁`, plus `m²` times `Tr[γ^{l₂} γ^{l₃}]` (`vF1_loopAff`);
* `cSlotV2`: minus the metric factors times `Tr[γ^{l₂} γ^{l₃}]` (`vF2_loopAff`).

`refinedBound_cSlotV1`, `isLoopPoly_cSlotV1`: the bubble coefficients are bounded by the two
bubble lines with exponent two and have degree two.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)

/-- The left factors `γ^{l₁}` of the one-slot numerators of `V`. -/
noncomputable def aSlotV : Fin 4 × Fin 4 × Fin 4 × Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun l => Dirac.gamma l.2.1

/-- The right factors `γ^{l₀}` of the one-slot numerators of `V`. -/
noncomputable def bSlotV : Fin 4 × Fin 4 × Fin 4 × Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun l => Dirac.gamma l.1

/-- The metric factors of the photon numerators of `V`. -/
noncomputable def gSlotV (Q : Params) (l : Fin 4 × Fin 4 × Fin 4 × Fin 4) : ℂ :=
  ((Minkowski.metric l.1 l.2.2.1 * (Q.Λ ^ 2 - Q.mγ ^ 2) : ℝ) : ℂ) *
    ((Minkowski.metric l.2.1 l.2.2.2 * (Q.Λ ^ 2 - Q.mγ ^ 2) : ℝ) : ℂ)

/-- The scalar coefficients of the first three pieces of `V`. -/
noncomputable def cSlotV1 (Q : Params) (l : Fin 4 × Fin 4 × Fin 4 × Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  vκ * vC Q * vK Q * gSlotV Q l * (trSE 0 (ℓ 1) (ℓ 0 + ℓ 1) l.2.2.1 l.2.2.2 +
    ((Q.m ^ 2 : ℝ) : ℂ) * (Dirac.gamma l.2.2.1 * Dirac.gamma l.2.2.2).trace)

/-- The scalar coefficients of the last two pieces of `V`. -/
noncomputable def cSlotV2 (Q : Params) (l : Fin 4 × Fin 4 × Fin 4 × Fin 4)
    (_ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  -(vκ * vC Q * vK Q) * gSlotV Q l * (Dirac.gamma l.2.2.1 * Dirac.gamma l.2.2.2).trace

theorem vF1_loopAff (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vF1 Q p α β (loopAff mV ![p, 0] ℓ) = ∑ l, cSlotV1 Q l ℓ *
      (aSlotV l * electronNumerator Q.m (p - ℓ 0) * bSlotV l) α β := by
  obtain ⟨h0, h1, h2⟩ := bm_loopAff_mV p ℓ
  simp only [vF1, seE0, seE2, outerSE, h0, h1, h2, Fintype.sum_prod_type, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l1 _ =>
    Finset.sum_congr rfl fun l2 _ => Finset.sum_congr rfl fun l3 _ => ?_
  simp only [cSlotV1, gSlotV, aSlotV, bSlotV]
  ring

theorem vF2_loopAff (Q : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vF2 Q p α β (loopAff mV ![p, 0] ℓ) = ∑ l, cSlotV2 Q l ℓ *
      (aSlotV l * electronNumerator Q.m (p - ℓ 0) * bSlotV l) α β := by
  obtain ⟨h0, -, -⟩ := bm_loopAff_mV p ℓ
  simp only [vF2, seE2, outerSE, h0, Fintype.sum_prod_type, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l1 _ =>
    Finset.sum_congr rfl fun l2 _ => Finset.sum_congr rfl fun l3 _ => ?_
  simp only [cSlotV2, gSlotV, aSlotV, bSlotV]
  ring

variable {n : ℕ} (hn : 6 ≤ n) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
  (E : Finset (Fin (n + 1))) (hw : IntNoSubdivergenceRefined 2 E fun i => awV (sh i))

theorem slotN_vData_apply (Q : Params) (s0 : sh 0 = 0)
    (c : Fin 4 × Fin 4 × Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ) (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (α β : Fin 4) :
    (vData hn sh Ms E hw).slotN 0 Q.m aSlotV bSlotV c p ℓ α β = ∑ l, c l ℓ *
      (aSlotV l * electronNumerator Q.m (p - ℓ 0) * bSlotV l) α β := by
  have hk : lineMomentum (vData hn sh Ms E hw).α ((vData hn sh Ms E hw).mom p) 0 ℓ = p - ℓ 0 := by
    have h := lineMomentum_vData hn sh Ms E hw p 0 ℓ
    rw [s0, (bm_loopAff_mV p ℓ).1] at h
    exact h
  simp only [SEData.slotN, SEData.slotE, hk, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem lineMomentum_vData_bubble (s1 : sh 1 = 1) (s2 : sh 2 = 2) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (vData hn sh Ms E hw).α ((vData hn sh Ms E hw).mom 0) 1 ℓ = ℓ 1 ∧
      lineMomentum (vData hn sh Ms E hw).α ((vData hn sh Ms E hw).mom 0) 2 ℓ = ℓ 0 + ℓ 1 := by
  obtain ⟨-, h1, h2⟩ := bm_loopAff_mV 0 ℓ
  have e1 := lineMomentum_vData hn sh Ms E hw 0 1 ℓ
  have e2 := lineMomentum_vData hn sh Ms E hw 0 2 ℓ
  rw [s1, h1] at e1
  rw [s2, h2] at e2
  exact ⟨e1, e2⟩

theorem refinedBound_cSlotV1 (Q : Params) (s1 : sh 1 = 1) (s2 : sh 2 = 2)
    (h12 : (1 : Fin (n + 1)) ≠ 2) (l : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    RefinedBound (vData hn sh Ms E hw).α {1, 2} 2 (cSlotV1 Q l) := by
  set D := vData hn sh Ms E hw
  have e : cSlotV1 Q l = fun ℓ => vκ * vC Q * vK Q * gSlotV Q l *
      ((Dirac.gamma l.2.2.1 * electronNumerator 0 (lineMomentum D.α (D.mom 0) 1 ℓ) *
        Dirac.gamma l.2.2.2 * electronNumerator 0 (lineMomentum D.α (D.mom 0) 2 ℓ)).trace +
        ((Q.m ^ 2 : ℝ) : ℂ) * (Dirac.gamma l.2.2.1 * Dirac.gamma l.2.2.2).trace) := by
    funext ℓ
    obtain ⟨h1, h2⟩ := lineMomentum_vData_bubble hn sh Ms E hw s1 s2 ℓ
    rw [h1, h2]
    rfl
  refine (congrArg (RefinedBound D.α {1, 2} 2) e).mpr ?_
  have hT := ((((RefinedBoundMat.const (al := D.α) (Dirac.gamma l.2.2.1)).mul
    (refinedBoundMat_elec D.α (D.mom 0) 1 0) (Finset.disjoint_empty_left _)).mul
      (RefinedBoundMat.const (Dirac.gamma l.2.2.2)) (Finset.disjoint_empty_right _)).mul
        (refinedBoundMat_elec D.α (D.mom 0) 2 0) (Finset.disjoint_singleton.mpr h12)).trace
  simp only [Finset.empty_union, Finset.union_empty, zero_add, add_zero] at hT
  have hc := (RefinedBound.const (α := D.α)
    (((Q.m ^ 2 : ℝ) : ℂ) * (Dirac.gamma l.2.2.1 * Dirac.gamma l.2.2.2).trace)).mono
      (E' := {1} ∪ {2}) (Finset.empty_subset _) (by norm_num : 0 ≤ 1 + 1)
  exact ((hT.add hc).const_mul _).mono (by intro x hx; simpa using hx) le_rfl

theorem isLoopPoly_cSlotV1 (Q : Params) (l : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    IsLoopPoly 2 2 (cSlotV1 Q l) := by
  have hu : IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => ℓ 1 := ⟨![0, 1], 0, fun ℓ => by simp⟩
  have hv : IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => ℓ 0 + ℓ 1 :=
    ⟨![1, 1], 0, fun ℓ => by simp⟩
  have hT := ((((IsLoopPolyMat.const (L := 2) (Dirac.gamma l.2.2.1)).mul
    (hu.isLoopPolyMat_electronNumerator 0)).mul (IsLoopPolyMat.const (Dirac.gamma l.2.2.2))).mul
      (hv.isLoopPolyMat_electronNumerator 0)).trace
  have h := (hT.add ((IsLoopPoly.const (n := 0) (((Q.m ^ 2 : ℝ) : ℂ) *
    (Dirac.gamma l.2.2.1 * Dirac.gamma l.2.2.2).trace)).mono (by norm_num))).const_mul
      (vκ * vC Q * vK Q * gSlotV Q l)
  exact h

theorem refinedBound_cSlotV2 (Q : Params) (l : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    RefinedBound (vData hn sh Ms E hw).α ∅ 2 (cSlotV2 Q l) :=
  (RefinedBound.const _).mono subset_rfl (by norm_num)

theorem isLoopPoly_cSlotV2 (Q : Params) (l : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    IsLoopPoly 2 2 (cSlotV2 Q l) :=
  (IsLoopPoly.const (n := 0) _).mono (by norm_num)

end QED.GradedProof.WI2

end
