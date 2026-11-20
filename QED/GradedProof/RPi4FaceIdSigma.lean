/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdLim

/-!
# (R-Π₄) step L6d3: the `σ`-integral of a face at `ρ = 0`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The face limit
of `face_sector_rate` is `∫₀^∞ gJ(0, σ) dσ`. Here the `σ`-integral is done exactly: for
`θ > 0`, `v > 0`, `k ≥ 2`, `∫₀^∞ θ (v + θσ)^{-k} dσ = v^{1-k}/(k - 1)`, and by Fubini (with the
majorant `θ (c₁ + θσ)^{-2}` of `SigData`, whose `σ`-integral is `1/c₁`)

`∫₀^∞ gJ(0, σ) dσ = ∫_{Δ_p × Δ_q} ∑ⱼ coefJⱼ(0) · vHat(0)^{1-kⱼ}/(kⱼ - 1)`.

* `faceId_integral_Ioi_inv_pow`: the one-dimensional integral;
* `SigData.faceId_integral_sigG_zero`: the abstract Fubini step (`θ > 0` almost everywhere);
* `FaceShape.faceIdInt` (the face integral at `ρ = 0`), **`FaceShape.faceId_integral_gJ_zero`**
  (`∫₀^∞ gJ(0, σ) dσ = faceIdInt` for a family satisfying `FamHyp`);
* the data at `ρ = 0` on the simplex (`Û = â = ĉ = 1`, `V̂ = m_R - P₀·P₀`) and
  **`FaceShape.faceId_faceIdInt_eq`** (the explicit face integral when the face block has as many
  fermion lines as the order `d` of the bracket), `FaceShape.faceId_faceIdInt_eq_zero` (more
  fermion lines than `d`: `0`).
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

/-! ### The one-dimensional integral -/

section OneDim

variable {θ v : ℝ} {k : ℕ}

theorem faceId_hasDerivAt_inv_pow (hθ : 0 < θ) (hv : 0 < v) (hk : 2 ≤ k) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    HasDerivAt (fun σ : ℝ => -(((v + θ * σ) ^ (k - 1))⁻¹ / (k - 1 : ℝ)))
      (θ * ((v + θ * σ) ^ k)⁻¹) σ := by
  have hw : 0 < v + θ * σ := by positivity
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h1 : HasDerivAt (fun σ : ℝ => v + θ * σ) θ σ := by
    simpa using ((hasDerivAt_id σ).const_mul θ).const_add v
  have h2 := (h1.pow (j + 1)).inv (pow_ne_zero _ hw.ne')
  have h3 := (h2.div_const ((j : ℝ) + 1)).neg
  simp only [show j + 2 - 1 = j + 1 by omega]
  convert h3 using 1
  · funext x
    simp only [Pi.neg_apply, Pi.inv_apply, Pi.pow_apply]
    push_cast
    ring
  · simp only [Pi.pow_apply, Nat.add_sub_cancel]
    have hj : (j : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem faceId_tendsto_inv_pow (hθ : 0 < θ) (hk : 2 ≤ k) :
    Tendsto (fun σ : ℝ => -(((v + θ * σ) ^ (k - 1))⁻¹ / (k - 1 : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun σ : ℝ => v + θ * σ) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hθ)
  have h2 : Tendsto (fun σ : ℝ => (v + θ * σ) ^ (k - 1)) atTop atTop :=
    (tendsto_pow_atTop (by omega)).comp h1
  simpa using ((tendsto_inv_atTop_zero.comp h2).div_const ((k : ℝ) - 1)).neg

/-- **`∫₀^∞ θ (v + θσ)^{-k} dσ = v^{1-k}/(k - 1)`** (`θ, v > 0`, `k ≥ 2`), with integrability. -/
theorem faceId_integral_Ioi_inv_pow (hθ : 0 < θ) (hv : 0 < v) (hk : 2 ≤ k) :
    IntegrableOn (fun σ : ℝ => θ * ((v + θ * σ) ^ k)⁻¹) (Ioi 0) ∧
    ∫ σ in Ioi (0 : ℝ), θ * ((v + θ * σ) ^ k)⁻¹ = (v ^ (k - 1))⁻¹ / (k - 1 : ℝ) := by
  have hc : ContinuousWithinAt (fun σ : ℝ => -(((v + θ * σ) ^ (k - 1))⁻¹ / (k - 1 : ℝ)))
      (Ici 0) 0 :=
    (faceId_hasDerivAt_inv_pow hθ hv hk le_rfl).continuousAt.continuousWithinAt
  have hd : ∀ σ ∈ Ioi (0 : ℝ), HasDerivAt
      (fun σ : ℝ => -(((v + θ * σ) ^ (k - 1))⁻¹ / (k - 1 : ℝ))) (θ * ((v + θ * σ) ^ k)⁻¹) σ :=
    fun σ hσ => faceId_hasDerivAt_inv_pow hθ hv hk (le_of_lt hσ)
  have hpos : ∀ σ ∈ Ioi (0 : ℝ), 0 ≤ θ * ((v + θ * σ) ^ k)⁻¹ := fun σ hσ => by
    have : 0 < v + θ * σ := by have : (0 : ℝ) < σ := hσ; positivity
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg hc hd hpos (faceId_tendsto_inv_pow hθ hk)
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hint (faceId_tendsto_inv_pow hθ hk)]
  simp

end OneDim

/-! ### The abstract Fubini step -/

section Abstract

variable {X : Type*} [MeasurableSpace X] {r : ℕ} {μ : Measure X} {ρ₀ c₁ BD LD LV : ℝ}
  {θ : X → ℝ} {D : Fin r → ℝ → X → ℂ} {vh : ℝ → X → ℝ} {k : Fin r → ℕ}

namespace SigData

variable (h : SigData μ ρ₀ c₁ BD LD LV θ D vh k)
include h

/-- The majorant `θ (c₁ + θσ)^{-2}` has `σ`-integral `1/c₁` for `θ > 0`, and `0` for `θ = 0`. -/
theorem faceId_integral_sigM_le {x : X} (hx : 0 ≤ θ x) :
    IntegrableOn (fun σ => sigM θ c₁ σ x) (Ioi 0) ∧
      ∫ σ in Ioi (0 : ℝ), sigM θ c₁ σ x ≤ c₁⁻¹ := by
  rcases hx.lt_or_eq with hx | hx
  · obtain ⟨hi, he⟩ := faceId_integral_Ioi_inv_pow hx h.c₁_pos le_rfl (k := 2)
    refine ⟨hi, ?_⟩
    simp only [sigM]
    rw [he]
    norm_num
  · simp only [sigM, ← hx, zero_mul, integral_zero]
    exact ⟨integrableOn_zero, inv_nonneg.mpr h.c₁_pos.le⟩

theorem faceId_integrable_sigM_prod [IsFiniteMeasure μ] :
    Integrable (fun y : ℝ × X => sigM θ c₁ y.1 y.2) ((volume.restrict (Ioi 0)).prod μ) := by
  have hm : Measurable fun y : ℝ × X => sigM θ c₁ y.1 y.2 := by
    have := h.hθm
    unfold sigM
    fun_prop
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  constructor
  · filter_upwards [h.hθ] with x hx
    exact (h.faceId_integral_sigM_le hx.1).1
  · refine Integrable.of_bound ?_ c₁⁻¹ ?_
    · exact (hm.norm.stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Ioi 0))).aestronglyMeasurable
    · filter_upwards [h.hθ] with x hx
      have hnn : ∀ σ ∈ Ioi (0 : ℝ), ‖sigM θ c₁ σ x‖ = sigM θ c₁ σ x := fun σ hσ => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg hx.1 (inv_nonneg.mpr (sq_nonneg _))
      rw [setIntegral_congr_fun measurableSet_Ioi hnn]
      have h0 : 0 ≤ ∫ σ in Ioi (0 : ℝ), sigM θ c₁ σ x :=
        setIntegral_nonneg measurableSet_Ioi fun σ _ =>
          mul_nonneg hx.1 (inv_nonneg.mpr (sq_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact (h.faceId_integral_sigM_le hx.1).2

/-- **The `σ`-integral of the face function at `ρ = 0`** (`θ > 0` almost everywhere):
`∫₀^∞ g(0, σ) dσ = ∫ ∑ⱼ Dⱼ(0) v(0)^{1-kⱼ}/(kⱼ - 1) dμ`. -/
theorem faceId_integral_sigG_zero [IsFiniteMeasure μ] (q : ℕ) (hθp : ∀ᵐ x ∂μ, 0 < θ x) :
    ∫ σ in Ioi (0 : ℝ), sigG μ q θ D vh k 0 σ =
      ∫ x, ∑ j, D j 0 x * (((vh 0 x ^ (k j - 1) : ℝ) : ℂ)⁻¹ / ((k j : ℂ) - 1)) ∂μ := by
  have hH : Integrable (fun y : ℝ × X => sigH θ D vh k 0 y.1 y.2)
      ((volume.restrict (Ioi 0)).prod μ) := by
    refine (h.faceId_integrable_sigM_prod.const_mul (sigK₀ c₁ BD k)).mono' ?_ ?_
    · exact (h.measurable_sigH_uncurry.comp ((measurable_const (a := (0 : ℝ))).prodMk
        measurable_fst |>.prodMk measurable_snd)).aestronglyMeasurable
    · have hs : ∀ᵐ y ∂((volume.restrict (Ioi (0 : ℝ))).prod μ), y.1 ∈ Ioi (0 : ℝ) :=
        (Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [hs, (Measure.quasiMeasurePreserving_snd
        (μ := volume.restrict (Ioi (0 : ℝ))) (ν := μ)).ae h.norm_sigH_le] with y hy hb
      exact hb 0 y.1 le_rfl h.ρ₀_pos.le (le_of_lt hy)
  have hG : ∀ σ, sigG μ q θ D vh k 0 σ = ∫ x, sigH θ D vh k 0 σ x ∂μ := fun σ => by
    simp [sigG]
  simp only [hG]
  rw [integral_integral_swap hH]
  refine integral_congr_ae ?_
  filter_upwards [hθp, h.hv] with x hx hv
  have hv0 : 0 < vh 0 x := h.c₁_pos.trans_le (hv 0 le_rfl h.ρ₀_pos.le).1
  have e : ∀ σ, sigH θ D vh k 0 σ x =
      ∑ j, D j 0 x * (((θ x * ((vh 0 x + θ x * σ) ^ k j)⁻¹ : ℝ)) : ℂ) := fun σ => by
    simp only [sigH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  simp only [e]
  rw [integral_finsetSum _ fun j _ =>
    ((faceId_integral_Ioi_inv_pow hx hv0 (h.hk j)).1.ofReal).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_complex_ofReal, (faceId_integral_Ioi_inv_pow hx hv0 (h.hk j)).2]
  push_cast
  ring

end SigData

end Abstract

/-! ### The face value of a face shape -/

namespace FaceShape

variable {p q r : ℕ}

/-- **The face integral at `ρ = 0`**:
`∫_{Δ × Δ} ∑ⱼ coefJⱼ(0) · vHat(0)^{1-kⱼ}/(kⱼ - 1)` (the face value, `faceId_integral_gJ_zero`). -/
noncomputable def faceIdInt (S : FaceShape p q) (B : FaceBr r) : ℂ :=
  ∫ x in simplexSet p ×ˢ simplexSet q, ∑ j, S.coefJ B j 0 (simplexPoint x.1) (simplexPoint x.2) *
    (((S.vHat 0 (simplexPoint x.1) (simplexPoint x.2) ^ (B.k j - 1) : ℝ) : ℂ)⁻¹ /
      ((B.k j : ℂ) - 1))

theorem faceId_ae_thetaX_pos (S : FaceShape (p + 1) q) :
    ∀ᵐ x ∂(volume.restrict (simplexSet (p + 1) ×ˢ simplexSet q)), 0 < S.thetaX x := by
  have hW : ∀ᵐ w ∂(volume.restrict (simplexSet (p + 1))), 0 < simplexPoint w S.γ := by
    filter_upwards [ae_restrict_mem (measurableSet_simplexSet _),
      ae_restrict_of_ae (ae_simplexPoint_ne_zero (Nat.succ_pos p))] with w hw hne
    exact lt_of_le_of_ne ((simplexPoint_mem_stdSimplex hw).1 _) (hne _).symm
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact Measure.quasiMeasurePreserving_fst.ae hW

/-- **The face value at `ρ = 0`**: for a family satisfying `FamHyp`,
`∫₀^∞ gJ(0, σ) dσ = faceIdInt` (the `σ`-integral done exactly). -/
theorem faceId_integral_gJ_zero {ι : Type*} {S : ι → FaceShape (p + 1) q} {B : ι → FaceBr r}
    {k : Fin r → ℕ} {ρ₀ c₁ K KM : ℝ} (h : FamHyp S B k ρ₀ c₁ K KM) (s : ι) :
    ∫ σ in Ioi (0 : ℝ), (S s).gJ (B s) 0 σ = (S s).faceIdInt (B s) := by
  obtain ⟨BD, LD, LV, hS⟩ := sigData h
  simp only [gJ_eq_sigG, faceIdInt, h.hkc s]
  exact (hS s).faceId_integral_sigG_zero q (S s).faceId_ae_thetaX_pos

/-! ### The data at `ρ = 0` -/

section Zero

variable (S : FaceShape p q) {W : Fin (p + 1) → ℝ} {V : Fin (q + 1) → ℝ}

theorem faceId_c_eq_one (hW1 : ∑ i, W i = 1) : S.c W = 1 := by
  rw [← hW1, FaceShape.c]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases S.hF i with h | h <;> simp [h]

theorem faceId_uJ_zero (hW1 : ∑ i, W i = 1) (hV1 : ∑ j, V j = 1) : S.uJ 0 W V = 1 := by
  simp [uJ, uHat, aJ, a0, hV1, S.faceId_c_eq_one hW1]

theorem faceId_vHat_zero (hW1 : ∑ i, W i = 1) (hV1 : ∑ j, V j = 1) :
    S.vHat 0 W V = S.mR V - Minkowski.dot (S.P0 V) (S.P0 V) := by
  have hP : S.PJ 0 W V = S.P0 V := funext fun μ => by simp [PJ]
  simp only [vHat, hP, S.faceId_uJ_zero hW1 hV1, S.faceId_c_eq_one hW1]
  ring

theorem faceId_coefJ_zero (B : FaceBr r) (hd : B.d = p) (j : Fin r)
    (hW1 : ∑ i, W i = 1) (hV1 : ∑ j, V j = 1) :
    S.coefJ B j 0 W V = B.C j 0 1 (S.b W) 1 (S.P0 V) (S.b₁ W) := by
  have hP : S.PJ 0 W V = S.P0 V := funext fun μ => by simp [PJ]
  have ha : S.aJ 0 W V = 1 := by simp [aJ, a0, hV1]
  simp [coefJ, S.faceId_uJ_zero hW1 hV1, hP, ha, S.faceId_c_eq_one hW1, hd]

/-- **A face with more fermion lines than the order of its bracket has face integral `0`.** -/
theorem faceId_faceIdInt_eq_zero (B : FaceBr r) (hd : B.d < p) : S.faceIdInt B = 0 := by
  simp [faceIdInt, S.faceId_coefJ_zero_eq_zero B hd]

/-- **The face integral of a face of order `d = p`** (as many fermion lines in the face block as
the order of the bracket): with `Û(0) = 1`, `â = ĉ = 1` and `V̂(0) = m_R - P₀·P₀`, it is
`∫_{Δ × Δ} ∑ⱼ Cⱼ(0, 1, b, 1, P₀, b₁) (m_R - P₀·P₀)^{1-kⱼ}/(kⱼ - 1)`. -/
theorem faceId_faceIdInt_eq (B : FaceBr r) (hd : B.d = p) :
    S.faceIdInt B = ∫ x in simplexSet p ×ˢ simplexSet q, ∑ j, B.C j 0 1 (S.b (simplexPoint x.1))
        1 (S.P0 (simplexPoint x.2)) (S.b₁ (simplexPoint x.1)) *
        ((((S.mR (simplexPoint x.2) - Minkowski.dot (S.P0 (simplexPoint x.2))
          (S.P0 (simplexPoint x.2))) ^ (B.k j - 1) : ℝ) : ℂ)⁻¹ / ((B.k j : ℂ) - 1)) := by
  refine setIntegral_congr_fun measurableSet_prod fun x hx => ?_
  have hW1 := (simplexPoint_mem_stdSimplex hx.1).2
  have hV1 := (simplexPoint_mem_stdSimplex hx.2).2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [S.faceId_coefJ_zero B hd j hW1 hV1, S.faceId_vHat_zero hW1 hV1]

end Zero

end FaceShape

end QED.GradedProof.RPi4

end
