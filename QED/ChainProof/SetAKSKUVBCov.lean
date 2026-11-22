/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDYB
public import QED.ChainProof.SetCKCoordJac

/-!
# Set (a), stage D: the inner vertex simplex in the coordinates `(ρ, β)`

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). The inner
vertex point of the `VB` class is `x = (ρ(1 - β), ρβ, 1 - ρ)`: `ρ = 1 - x₂` and
`β = x₁/(1 - x₂)`. The map `(ρ, β) ↦ (ρ(1 - β), ρβ)` is a bijection of the open unit square
onto the open triangle, with Jacobian `ρ`.

Main results:

* **`ksU_integrableOn_simplex_iff`**, **`ksU_integral_simplex_eq`**: an integral over `Δ₂` of
  a function of the barycentric point is the integral over `(0, 1)²` of `ρ g(ksUPtB ρ β)`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.ChainProof.SetAKS

open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.ChengWu (openSimplex mem_openSimplex)
open QED.ChainProof.SetCK (coordMat det_coordMat coord_hasFDerivAt_mat)

/-- The inner vertex point at `ρ = 1 - x₂`, `β = x₁/(1 - x₂)`. -/
noncomputable def ksUPtB (ρ β : ℝ) : Fin 3 → ℝ := ![ρ * (1 - β), ρ * β, 1 - ρ]

/-- The polar map of the triangle. -/
def ksUPolar (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * (1 - p.2), p.1 * p.2)

/-- The open triangle. -/
def ksUTri : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

theorem ksU_measurableSet_square : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem ksU_image_polar : ksUPolar '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = ksUTri := by
  ext q
  constructor
  · rintro ⟨p, ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, rfl⟩
    refine ⟨mul_pos h0 (by linarith), mul_pos h0 h2, ?_⟩
    simp only [ksUPolar]
    nlinarith
  · rintro ⟨h0, h1, h2⟩
    have hs : 0 < q.1 + q.2 := by linarith
    refine ⟨(q.1 + q.2, q.2 / (q.1 + q.2)), ⟨⟨hs, h2⟩, ⟨div_pos h1 hs, ?_⟩⟩, ?_⟩
    · rw [div_lt_one hs]; linarith
    · simp only [ksUPolar]
      ext
      · field_simp; ring
      · field_simp

theorem ksU_injOn_polar : InjOn ksUPolar (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rintro ⟨a, b⟩ ⟨⟨ha, -⟩, -⟩ ⟨c, d⟩ ⟨⟨hc, -⟩, -⟩ h
  simp only [ksUPolar, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hac : a = c := by linarith
  subst hac
  refine Prod.ext rfl ?_
  exact mul_left_cancel₀ ha.ne' h2

theorem ksU_hasFDerivAt_polar (p : ℝ × ℝ) :
    HasFDerivAt ksUPolar (coordMat (1 - p.2) (-p.1) p.2 p.1) p := by
  refine coord_hasFDerivAt_mat (f := fun q : ℝ × ℝ => q.1 * (1 - q.2))
    (g := fun q : ℝ × ℝ => q.1 * q.2) (by fun_prop) ?_ ?_ (by fun_prop) ?_ ?_
  · simpa using (hasDerivAt_id p.1).mul_const (1 - p.2)
  · simpa using ((hasDerivAt_id p.2).const_sub 1).const_mul p.1
  · simpa using (hasDerivAt_id p.1).mul_const p.2
  · simpa using (hasDerivAt_id p.2).const_mul p.1

theorem ksU_abs_det_polar {p : ℝ × ℝ} (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    |(coordMat (1 - p.2) (-p.1) p.2 p.1).det| = p.1 := by
  rw [det_coordMat, show (1 - p.2) * p.1 - -p.1 * p.2 = p.1 by ring, abs_of_pos hp.1.1]

theorem ksU_openSimplex_eq :
    openSimplex 2 = (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹' ksUTri := by
  ext q
  simp only [mem_openSimplex, Fin.forall_fin_two, Fin.sum_univ_two, mem_preimage, ksUTri,
    MeasurableEquiv.finTwoArrow_apply, mem_ofPred_eq]
  tauto

theorem ksU_simplexPoint_polar (p : ℝ × ℝ) :
    simplexPoint ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm (ksUPolar p)) =
      ksUPtB p.1 p.2 := by
  have h : (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm (ksUPolar p) =
      ![p.1 * (1 - p.2), p.1 * p.2] := by
    ext i; fin_cases i <;> rfl
  rw [h, ksD_simplexPoint_two, ksUPtB, show 1 - (p.1 * (1 - p.2) + p.1 * p.2) = 1 - p.1 by ring]

theorem ksU_simplex_to_tri (g : (Fin 3 → ℝ) → ℝ) :
    (IntegrableOn (fun q => g (simplexPoint q)) (simplexSet 2) ↔
      IntegrableOn (fun z => g (simplexPoint
        ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm z))) ksUTri) ∧
    ∫ q in simplexSet 2, g (simplexPoint q) = ∫ z in ksUTri, g (simplexPoint
        ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm z)) := by
  set e := (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)
  have hae := QED.Integration.ChengWu.simplexSet_ae_eq_openSimplex (⟨0, two_pos⟩ : Fin 2)
  have hmp : MeasurePreserving e.symm volume volume := (volume_preserving_finTwoArrow ℝ).symm
  have hpre : e.symm ⁻¹' openSimplex 2 = ksUTri := by
    ext z
    simp [mem_openSimplex, Fin.forall_fin_two, Fin.sum_univ_two, ksUTri, e,
      MeasurableEquiv.finTwoArrow_symm_apply, and_assoc]
  refine ⟨?_, ?_⟩
  · rw [integrableOn_congr_set_ae hae, ← hpre,
      ← hmp.integrableOn_comp_preimage e.symm.measurableEmbedding]
    rfl
  · rw [setIntegral_congr_set hae, ← hpre]
    exact (hmp.setIntegral_preimage_emb e.symm.measurableEmbedding _ _).symm

/-- **Integrability on `Δ₂` in the coordinates `(ρ, β)`.** -/
theorem ksU_integrableOn_simplex_iff (g : (Fin 3 → ℝ) → ℝ) :
    IntegrableOn (fun q => g (simplexPoint q)) (simplexSet 2) ↔
      IntegrableOn (fun p : ℝ × ℝ => p.1 * g (ksUPtB p.1 p.2))
        (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rw [(ksU_simplex_to_tri g).1, ← ksU_image_polar,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume ksU_measurableSet_square
      (fun p _ => (ksU_hasFDerivAt_polar p).hasFDerivWithinAt) ksU_injOn_polar]
  refine integrableOn_congr_fun (fun p hp => ?_) ksU_measurableSet_square
  simp only [smul_eq_mul, ksU_abs_det_polar hp, ksU_simplexPoint_polar]

/-- **The integral over `Δ₂` in the coordinates `(ρ, β)`** (Jacobian `ρ`). -/
theorem ksU_integral_simplex_eq (g : (Fin 3 → ℝ) → ℝ) :
    ∫ q in simplexSet 2, g (simplexPoint q) =
      ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, p.1 * g (ksUPtB p.1 p.2) := by
  rw [(ksU_simplex_to_tri g).2, ← ksU_image_polar,
    integral_image_eq_integral_abs_det_fderiv_smul volume ksU_measurableSet_square
      (fun p _ => (ksU_hasFDerivAt_polar p).hasFDerivWithinAt) ksU_injOn_polar]
  refine setIntegral_congr_fun ksU_measurableSet_square fun p hp => ?_
  simp only [smul_eq_mul, ksU_abs_det_polar hp, ksU_simplexPoint_polar]

theorem ksU_ksUPtB_sum (ρ β : ℝ) : ksUPtB ρ β 0 + ksUPtB ρ β 1 + ksUPtB ρ β 2 = 1 := by
  simp [ksUPtB]; ring

theorem ksU_ksUPtB_beta {ρ β : ℝ} (hρ : ρ ≠ 0) : ksUPtB ρ β 1 / (1 - ksUPtB ρ β 2) = β := by
  simp [ksUPtB]; field_simp

end QED.ChainProof.SetAKS

end
