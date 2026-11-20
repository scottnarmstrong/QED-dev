/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2ChainWard

/-!
# One-slot numerators and their Ward–Takahashi derivative

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the classes whose external momentum flows through a single electron line in the
Ward–Takahashi routing (the vacuum-polarization class `V`, and the one-loop classes with an
insertion on the photon line or at a vertex). The numerator is
`slotN = ∑ₗ cₗ(ℓ) Aₗ (m - k̸₀) Bₗ` with `k₀` the momentum of line `e₀` and the scalar
coefficients `cₗ` of degree two, bounded by lines `S ∌ e₀`.

* `SEData.slotN`, `slotQ` (`q̸ = (c_{e₀} r)̸` in the slot), `slotV` (the insertion
  `(m - k̸₀) q̸ (m - k̸₀)` in the slot): bounds and degrees, `slotV_eq` (the insertion identity).
* `SEData.hasDerivAt_pvF_slotN`: if `cᵢ = 0` off `e₀`, the derivative of the parametric value of
  an entry of `slotN` along `t ↦ t r` is minus the parametric value of `slotV` over the data with
  `e₀` doubled.
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassIntegrable QED.TwoLoop.Bridge QED.GradedProof.WI2
open QED.TwoLoop.LimitCovariance (qsum eval_qsum)

variable (D : SEData) (e₀ : Fin (D.m + 1)) (mass : ℝ) {ι : Type*} [Fintype ι]
  (A B : ι → Matrix (Fin 4) (Fin 4) ℂ) (c : ι → (Fin 2 → Fin 4 → ℝ) → ℂ)

/-- The electron numerator of line `e₀`. -/
noncomputable def slotE (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  electronNumerator mass (lineMomentum D.α (D.mom p) e₀ ℓ)

/-- The one-slot numerator `∑ₗ cₗ Aₗ (m - k̸₀) Bₗ`. -/
noncomputable def slotN (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ l, c l ℓ • (A l * D.slotE e₀ mass p ℓ * B l)

/-- The one-slot numerator with `q̸ = (c_{e₀} r)̸` in the slot. -/
noncomputable def slotQ (r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ l, c l ℓ • (A l * Dirac.slash (D.mom r e₀) * B l)

/-- The one-slot numerator with the insertion `(m - k̸₀) q̸ (m - k̸₀)` in the slot. -/
noncomputable def slotV (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ l, c l ℓ • (A l * (D.slotE e₀ mass p ℓ * Dirac.slash (D.mom r e₀) *
    D.slotE e₀ mass p ℓ) * B l)

/-- **The insertion identity** for the one-slot numerator. -/
theorem slotV_eq (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    D.slotV e₀ mass A B c p r ℓ =
      ((Minkowski.dot (lineMomentum D.α (D.mom p) e₀ ℓ) (lineMomentum D.α (D.mom p) e₀ ℓ) +
        mass ^ 2 : ℝ) : ℂ) • D.slotQ e₀ A B c r ℓ +
      ((2 * Minkowski.dot (D.mom r e₀) (lineMomentum D.α (D.mom p) e₀ ℓ) : ℝ) : ℂ) •
        D.slotN e₀ mass A B c p ℓ := by
  simp only [slotV, slotQ, slotN, slotE, electronNumerator, numerator_slash_numerator,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
    Finset.sum_add_distrib, Finset.smul_sum, smul_smul, mul_comm]

variable {A B c}

section Bounds

variable {S : Finset (Fin (D.m + 1))} (hS : e₀ ∉ S) (hSE : insert e₀ S ⊆ D.E)
  (hcp : ∀ l, IsLoopPoly 2 2 (c l)) (hcb : ∀ l, RefinedBound D.α S 2 (c l))
include hS hSE hcb

theorem refinedBound_slotN (p : Fin 4 → ℝ) (a b : Fin 4) :
    RefinedBound D.α D.E 3 fun ℓ => D.slotN e₀ mass A B c p ℓ a b := by
  simp only [slotN, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine RefinedBound.sum _ fun l _ => ?_
  have hE : RefinedBoundMat D.α {e₀} 1 fun ℓ => D.slotE e₀ mass p ℓ := fun a b =>
    refinedBound_electronNumerator D.α (D.mom p) e₀ mass a b
  have h := ((RefinedBoundMat.const (A l)).mul hE (Finset.disjoint_empty_left _)).mul
    (RefinedBoundMat.const (B l)) (Finset.disjoint_empty_right _)
  simp only [Finset.empty_union, Finset.union_empty, zero_add, add_zero] at h
  have h' := (hcb l).mul (h a b) (Finset.disjoint_singleton_right.mpr hS)
  refine h'.mono ?_ le_rfl
  rw [Finset.union_comm, ← Finset.insert_eq]
  exact hSE

omit hS in
theorem refinedBound_slotQ (r : Fin 4 → ℝ) (a b : Fin 4) :
    RefinedBound D.α D.E 4 fun ℓ => D.slotQ e₀ A B c r ℓ a b := by
  simp only [slotQ, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine RefinedBound.sum _ fun l _ => ?_
  have h := (hcb l).mul (RefinedBound.const ((A l * Dirac.slash (D.mom r e₀) * B l) a b))
    (Finset.disjoint_empty_right _)
  refine h.mono ?_ (by norm_num)
  rw [Finset.union_empty]
  exact (Finset.subset_insert _ _).trans hSE

theorem refinedBound_slotV (p r : Fin 4 → ℝ) (a b : Fin 4) :
    RefinedBound (dbl e₀ D.α) (dblLines D.E) 4 fun ℓ => D.slotV e₀ mass A B c p r ℓ a b := by
  simp only [slotV, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine RefinedBound.sum _ fun l _ => ?_
  have h1 : RefinedBoundMat (dbl e₀ D.α) {e₀.castSucc} 1 fun ℓ => D.slotE e₀ mass p ℓ :=
    fun a b => by
      have e : ∀ ℓ, D.slotE e₀ mass p ℓ = electronNumerator mass
          (lineMomentum (dbl e₀ D.α) (dbl e₀ (D.mom p)) e₀.castSucc ℓ) := fun ℓ => by
        rw [lineMomentum_dbl, dblIdx_castSucc]
        rfl
      simp only [e]
      exact refinedBound_electronNumerator _ _ _ mass a b
  have h2 : RefinedBoundMat (dbl e₀ D.α) {Fin.last (D.m + 1)} 1
      fun ℓ => D.slotE e₀ mass p ℓ := fun a b => by
    simp only [slotE, ← lineMomentum_dbl_last D.α (D.mom p) e₀]
    exact refinedBound_electronNumerator _ _ _ mass a b
  have hin := ((h1.mul (RefinedBoundMat.const (Dirac.slash (D.mom r e₀)))
    (Finset.disjoint_empty_right _)).mul h2 (by simp))
  have h := ((RefinedBoundMat.const (A l)).mul hin (Finset.disjoint_empty_left _)).mul
    (RefinedBoundMat.const (B l)) (Finset.disjoint_empty_right _)
  simp only [Finset.empty_union, Finset.union_empty, zero_add, add_zero] at h
  have hc := refinedBound_dbl_map (hcb l) e₀
  have hd : Disjoint (S.map Fin.castSuccEmb) ({e₀.castSucc} ∪ {Fin.last (D.m + 1)}) := by
    rw [Finset.disjoint_union_right]
    refine ⟨?_, Finset.disjoint_singleton_right.mpr (last_notMem_map S)⟩
    refine Finset.disjoint_singleton_right.mpr fun hm => hS ?_
    obtain ⟨x, hx, hxe⟩ := Finset.mem_map.mp hm
    rw [Fin.castSuccEmb_apply] at hxe
    rwa [← Fin.castSucc_injective _ hxe]
  have h' := hc.mul (h a b) hd
  have hsub : S.map Fin.castSuccEmb ∪ ({e₀.castSucc} ∪ {Fin.last (D.m + 1)}) ⊆
      dblLines D.E := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_map,
      Fin.castSuccEmb_apply] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl | rfl
    · exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _
        (hSE (Finset.mem_insert_of_mem hy)))
    · exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _
        (hSE (Finset.mem_insert_self _ _)))
    · exact Finset.mem_insert_self _ _
  exact h'.mono hsub (by norm_num)

omit hS hSE hcb in
include hcp in
theorem isLoopPoly_slotN (p : Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 2 3 fun ℓ => D.slotN e₀ mass A B c p ℓ a b := by
  simp only [slotN, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.sum _ fun l _ => ?_
  have hE : IsLoopPolyMat 2 1 fun ℓ => D.slotE e₀ mass p ℓ :=
    (isLoopAffine_lineMomentum D.α (D.mom p) e₀).isLoopPolyMat_electronNumerator mass
  have h := ((IsLoopPolyMat.const (L := 2) (A l)).mul hE).mul (IsLoopPolyMat.const (B l))
  simpa using (hcp l).mul (h a b)

omit hS hSE hcb in
include hcp in
theorem isLoopPoly_slotQ (r : Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 2 3 fun ℓ => D.slotQ e₀ A B c r ℓ a b := by
  simp only [slotQ, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact IsLoopPoly.sum _ fun l _ => (((hcp l).mul (IsLoopPoly.const (n := 0) _))).mono
    (by norm_num)

omit hS hSE hcb in
include hcp in
theorem isLoopPoly_slotV (p r : Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 2 4 fun ℓ => D.slotV e₀ mass A B c p r ℓ a b := by
  simp only [slotV, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.sum _ fun l _ => ?_
  have hE : IsLoopPolyMat 2 1 fun ℓ => D.slotE e₀ mass p ℓ :=
    (isLoopAffine_lineMomentum D.α (D.mom p) e₀).isLoopPolyMat_electronNumerator mass
  have h := ((IsLoopPolyMat.const (L := 2) (A l)).mul
    ((hE.mul (IsLoopPolyMat.const (Dirac.slash (D.mom r e₀)))).mul hE)).mul
    (IsLoopPolyMat.const (B l))
  simpa using (hcp l).mul (h a b)

omit hS hSE hcb in
theorem isLoopPoly_slotN_mom (ℓ : Fin 2 → Fin 4 → ℝ) (a b : Fin 4) :
    IsLoopPoly 1 3 fun y => D.slotN e₀ mass A B c (y 0) ℓ a b := by
  simp only [slotN, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.sum _ fun l _ => ?_
  have hE : IsLoopPolyMat 1 1 fun y => D.slotE e₀ mass (y 0) ℓ :=
    IsLoopAffine.isLoopPolyMat_electronNumerator ⟨![D.cs e₀], lineMomentum D.α 0 e₀ ℓ,
      fun y => by
        funext μ
        simp [lineMomentum, mom]
        ring⟩ mass
  have h := ((IsLoopPolyMat.const (L := 1) (A l)).mul hE).mul (IsLoopPolyMat.const (B l))
  simpa using ((IsLoopPoly.const (n := 0) (c l ℓ)).mul (h a b)).mono (by norm_num)

end Bounds

end QED.GradedProof.SE2.SEData

end
