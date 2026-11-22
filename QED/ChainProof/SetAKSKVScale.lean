/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVAExp
public import QED.ChainProof.SetAKSKUVBExp

/-!
# Set (a), stage D4: the mass scaling of the finite parts of the vertex classes

Helper level for `KsCore` (Set (a) of the three-loop coefficient). The finite parts `F(M, s)`
(`ksUF`) and `F_B(M, s)` (`ksUFB`) of the two vertex classes depend on the mass `M` only through
`s/M²` and one power series in `λ = log M²` of degree two: with `s = M² t`,

  `F(M, M² t) = F(1, t) - λ c₁(1, t) + λ² c₂`,   `F_B(M, M² t) = F_B(1, t) - λ c₁B(1, t) + λ² c₂B`,

where `c₁, c₂` (`ksUc1`, `ksUc2`) and `c₁B, c₂B` (`ksUc1B`, `ksUc2B`) are the coefficients of
`log Λ` and `log² Λ` of the cutoff expansions. This is the dimensional identity
`I(M, s, Λ) = I(1, s/M², Λ/M²)` read on the finite parts; it holds pointwise on the nodes.

Main results:

* `ksW_ksUQ_scale`, `ksW_ksUb0_scale`: the pointwise identities;
* `ksW_integrable_ksUb0`: the finite-part density of `VB` is integrable on the cube;
* **`ksW_ksUF_scale`**, **`ksW_ksUFB_scale`**: the integrated identities.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace QED.ChainProof.SetAKS

/-- The unit square measure. -/
local notation "ksWν" =>
  Measure.prod (volume.restrict (Ioo (0 : ℝ) 1)) (volume.restrict (Ioo (0 : ℝ) 1))

/-- The unit cube measure in the coordinates `((ρ, β), w)`. -/
local notation "ksWν3" =>
  Measure.prod (Measure.prod (volume.restrict (Ioo (0 : ℝ) 1)) (volume.restrict (Ioo (0 : ℝ) 1)))
    (volume.restrict (Ioo (0 : ℝ) 1))

/-! ### The elementary pieces -/

theorem ksW_ksUPhiInf_scale {M A : ℝ} (Y a₀ a₁ ℓ : ℝ) (hM : 0 < M) (hA : 0 < A) :
    ksUPhiInf (M ^ 2 * A) Y (M ^ 2 * a₀) a₁ ℓ = ksUPhiInf A Y a₀ a₁ ℓ +
      2 * a₁ * Y * (-(Real.log (M ^ 2) * (ℓ + Real.log Y - Real.log A)) +
        Real.log (M ^ 2) ^ 2 / 2) := by
  have hM2 : M ^ 2 ≠ 0 := by positivity
  have h1 : M ^ 2 * a₀ * (Y / (M ^ 2 * A)) = a₀ * (Y / A) := by field_simp
  unfold ksUPhiInf
  rw [h1, Real.log_mul hM2 hA.ne']
  ring

theorem ksW_ksUPhi_scale {M A b Y : ℝ} (a₀ a₁ : ℝ) (hM : 0 < M) (hA : 0 < A) (hb : 0 < b)
    (hY : 0 < Y) :
    ksUPhi (M ^ 2 * A) (M ^ 2 * b) Y (M ^ 2 * a₀) a₁ = ksUPhi A b Y a₀ a₁ +
      Real.log (M ^ 2) * (a₀ * Y / A - 2 * a₁ * Y) := by
  have hM2 : M ^ 2 ≠ 0 := by positivity
  have hP : 0 < A + b * Y := by positivity
  have h1 : (M ^ 2 * A + M ^ 2 * b * Y) / (M ^ 2 * A) = (A + b * Y) / A := by field_simp
  have h2 : M ^ 2 * A + M ^ 2 * b * Y = M ^ 2 * (A + b * Y) := by ring
  have h3 : M ^ 2 * b * Y / (M ^ 2 * A) = b * Y / A := by field_simp
  unfold ksUPhi
  rw [h1, h3, h2, Real.log_mul hM2 hP.ne']
  field_simp
  ring

theorem ksW_ksDA_scale (M t σ : ℝ) : ksDA M (M ^ 2 * t) σ = M ^ 2 * ksDA 1 t σ := by
  unfold ksDA; ring

theorem ksW_ksDa0_scale (M x t σ : ℝ) : ksDa0 M x (M ^ 2 * t) σ = M ^ 2 * ksDa0 1 x t σ := by
  unfold ksDa0; ring

theorem ksW_ksDb_scale (M x : ℝ) : ksDb M 0 x = M ^ 2 * ksDb 1 0 x := by
  unfold ksDb; ring

theorem ksW_ksDbB_scale (M t : ℝ) (x : Fin 3 → ℝ) :
    ksDbB M 0 x (M ^ 2 * t) = M ^ 2 * ksDbB 1 0 x t := by
  unfold ksDbB ksNEB; ring

theorem ksW_ksUG0_scale (M t ρ β w : ℝ) : ksUG0 M (M ^ 2 * t) ρ β w = M ^ 2 * ksUG0 1 t ρ β w := by
  simp only [ksUG0, ksUGc, ksDEc, ksDHc, ksDcv, ksDA, Matrix.cons_val_zero]
  ring

theorem ksW_ksUR_scale {M : ℝ} (hM : 0 < M) (t ρ β w : ℝ) :
    ksUR M (M ^ 2 * t) ρ β w = ksUR 1 t ρ β w / M ^ 2 := by
  have hM2 : M ^ 2 ≠ 0 := by positivity
  unfold ksUR
  rw [ksW_ksDA_scale, ksW_ksDA_scale]
  rw [show ρ * ((1 - ρ) * (M ^ 2 * ksDA 1 t w) + ρ * (M ^ 2 * ksDA 1 t β) * ksDYmax β w) =
    M ^ 2 * (ρ * ((1 - ρ) * ksDA 1 t w + ρ * ksDA 1 t β * ksDYmax β w)) by ring]
  rw [div_mul_eq_div_div, div_right_comm]

/-! ### The pointwise identities -/

/-- **The mass scaling of the `VA` finite-part density.** -/
theorem ksW_ksUQ_scale {M t x σ : ℝ} (hM : 0 < M) (ht : -4 < t) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ksUQ M (M ^ 2 * t) x σ = ksUQ 1 t x σ - Real.log (M ^ 2) * ksUal1 1 t x σ +
      Real.log (M ^ 2) ^ 2 * ksUal2 x σ := by
  have ht' : -(4 * (1 : ℝ) ^ 2) < t := by simpa using ht
  have hA := ksD_ksDA_pos one_pos ht' (Ioo_subset_Icc_self hσ)
  have hb := ksU_ksDb_pos one_pos hx le_rfl
  have hY : 0 < 1 - σ := by linarith [hσ.2]
  unfold ksUQ
  rw [ksW_ksDA_scale, ksW_ksDa0_scale, ksW_ksDb_scale, ksW_ksUPhiInf_scale _ _ _ _ hM hA,
    ksW_ksUPhi_scale _ _ hM hA hb hY]
  unfold ksUal1 ksUal2
  ring

/-- **The mass scaling of the `VB` finite-part density.** -/
theorem ksW_ksUb0_scale {M t ρ β w : ℝ} (hM : 0 < M) (ht : -4 < t) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    ksUb0 M (M ^ 2 * t) ρ β w = ksUb0 1 t ρ β w - Real.log (M ^ 2) * ksUb1 1 t ρ β w +
      Real.log (M ^ 2) ^ 2 * ksUb2 ρ β w := by
  have ht' : -(4 * (1 : ℝ) ^ 2) < t := by simpa using ht
  have hM2 : M ^ 2 ≠ 0 := by positivity
  have hAw := ksD_ksDA_pos one_pos ht' (Ioo_subset_Icc_self hw)
  have hAb := ksD_ksDA_pos one_pos ht' (Ioo_subset_Icc_self hβ)
  have hY := ksU_ksDYmax_pos hβ hw
  have hρ0 := hρ.1
  have h1ρ : 0 < 1 - ρ := by linarith [hρ.2]
  have hR := ksU_ksUR_pos one_pos ht' hρ hβ hw
  have hb := ksU_ksDbB_ptB_pos one_pos ht' hρ hβ le_rfl (β := β)
  set l := Real.log (M ^ 2)
  set Y := ksDYmax β w
  set b := ksDbB 1 0 (ksUPtB ρ β) t with hbd
  have h1 : (1 - ρ)⁻¹ * ksUG0 M (M ^ 2 * t) ρ β w *
      ksDJ1 (ksDA M (M ^ 2 * t) w) (ksDbB M 0 (ksUPtB ρ β) (M ^ 2 * t)) Y 0 =
      (1 - ρ)⁻¹ * ksUG0 1 t ρ β w * ksDJ1 (ksDA 1 t w) b Y 0 := by
    rw [ksW_ksUG0_scale, ksW_ksDA_scale, ksW_ksDbB_scale, ← hbd]
    simp only [ksDJ1]
    rw [show (M ^ 2 * ksDA 1 t w + M ^ 2 * b * Y) / (M ^ 2 * ksDA 1 t w) =
      (ksDA 1 t w + b * Y) / ksDA 1 t w by field_simp]
    field_simp
  have h2 : Real.log ((1 - ρ) * ksUR M (M ^ 2 * t) ρ β w) =
      Real.log ((1 - ρ) * ksUR 1 t ρ β w) - l := by
    rw [ksW_ksUR_scale hM, mul_div_assoc', Real.log_div (by positivity) hM2]
  have h3 : Real.log ((1 - ρ) * ksUR M (M ^ 2 * t) ρ β w / ((1 - ρ) / ksDA M (M ^ 2 * t) β)) =
      Real.log ((1 - ρ) * ksUR 1 t ρ β w / ((1 - ρ) / ksDA 1 t β)) := by
    rw [ksW_ksUR_scale hM, ksW_ksDA_scale]
    congr 1
    field_simp
  have h4 : ksUl3 M (M ^ 2 * t) ρ β w = ksUl3 1 t ρ β w - l := by
    unfold ksUl3
    rw [ksW_ksDA_scale, show Y / (ρ * (M ^ 2 * ksDA 1 t w)) = Y / (ρ * ksDA 1 t w) / M ^ 2 by
      field_simp, Real.log_div (by positivity) hM2]
  have h5 : ksUK (ksDbB M 0 (ksUPtB ρ β) (M ^ 2 * t) * Y / ksDA M (M ^ 2 * t) w) =
      ksUK (b * Y / ksDA 1 t w) := by
    rw [ksW_ksDbB_scale, ksW_ksDA_scale, ← hbd]
    congr 1
    field_simp
  have h6 : Real.log (ksDA M (M ^ 2 * t) β)⁻¹ = Real.log (ksDA 1 t β)⁻¹ - l := by
    rw [ksW_ksDA_scale, Real.log_inv, Real.log_inv, Real.log_mul hM2 hAb.ne']
    ring
  unfold ksUb0
  rw [h1, h2, h3, h4, h5, h6]
  unfold ksUb1 ksUb2
  ring

/-! ### Integrability of the `VB` finite-part density -/

theorem ksW_ae_mem_square : ∀ᵐ p ∂ksWν, p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)

/-- The finite-part density of `VB` is integrable on the cube: it is the pointwise limit of the
remainder `ksUDr`, which is dominated uniformly in `Λ ≥ 1`. -/
theorem ksW_integrable_ksUb0 {M s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) :
    Integrable (fun z : (ℝ × ℝ) × ℝ => ksUb0 M s z.1.1 z.1.2 z.2) ksWν3 := by
  obtain ⟨C, hC⟩ := ksU_abs_ksUDr_le hM hs
  have hlim : ∀ᵐ z ∂ksWν3, Tendsto (fun n : ℕ => ksUDr M s n z.1.1 z.1.2 z.2) atTop
      (𝓝 (ksUb0 M s z.1.1 z.1.2 z.2)) := by
    filter_upwards [ksU_ae_mem_cube] with z hz
    exact (ksU_tendsto_ksUDr hM hs hz.1 hz.2.1 hz.2.2).comp tendsto_natCast_atTop_atTop
  have hmeas : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ => ksUb0 M s z.1.1 z.1.2 z.2) ksWν3 :=
    aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter ℕ))
      (fun n : ℕ => (ksU_measurable_ksUDr M s (n : ℝ)).aestronglyMeasurable) hlim
  refine Integrable.mono' (ksU_integrable_ksUg_cube.const_mul C) hmeas ?_
  filter_upwards [ksU_ae_mem_cube, hlim] with z hz hl
  rw [Real.norm_eq_abs]
  refine le_of_tendsto hl.abs ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hC n (by exact_mod_cast hn) _ hz.1 _ hz.2.1 _ hz.2.2

/-! ### The integrated identities -/

/-- **The mass scaling of the `VA` finite part**: `F(M, M² t) = F(1, t) - λ c₁(1, t) + λ² c₂`
with `λ = log M²`. -/
theorem ksW_ksUF_scale {M t : ℝ} (hM : 0 < M) (ht : -4 < t) :
    ksUF M (M ^ 2 * t) = ksUF 1 t - Real.log (M ^ 2) * ksUc1 1 t +
      Real.log (M ^ 2) ^ 2 * ksUc2 := by
  have ht' : -(4 * (1 : ℝ) ^ 2) < t := by simpa using ht
  have hs : -(4 * M ^ 2) < M ^ 2 * t := by nlinarith [sq_pos_of_pos hM]
  have hQ := ksU_integrable_ksUQ hM hs
  have hQ1 := ksU_integrable_ksUQ one_pos ht'
  have h1 := (ksU_integrable_ksUal1 one_pos ht').const_mul (Real.log (M ^ 2))
  have h2 := ksU_integrable_ksUal2.const_mul (Real.log (M ^ 2) ^ 2)
  rw [ksUF, ksUF, ksUc1, ksUc2, ← integral_prod _ hQ, ← integral_prod _ hQ1,
    ← integral_prod _ (ksU_integrable_ksUal1 one_pos ht'), ← integral_prod _ ksU_integrable_ksUal2,
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← integral_sub hQ1 h1]
  refine (integral_congr_ae ?_).trans (integral_add (hQ1.sub h1) h2)
  filter_upwards [ksW_ae_mem_square] with p hp
  exact ksW_ksUQ_scale hM ht hp.1 hp.2

/-- **The mass scaling of the `VB` finite part**:
`F_B(M, M² t) = F_B(1, t) - λ c₁B(1, t) + λ² c₂B` with `λ = log M²`. -/
theorem ksW_ksUFB_scale {M t : ℝ} (hM : 0 < M) (ht : -4 < t) :
    ksUFB M (M ^ 2 * t) = ksUFB 1 t - Real.log (M ^ 2) * ksUc1B 1 t +
      Real.log (M ^ 2) ^ 2 * ksUc2B := by
  have ht' : -(4 * (1 : ℝ) ^ 2) < t := by simpa using ht
  have hb0 := ksW_integrable_ksUb0 one_pos ht'
  have h1 := (ksU_integrable_ksUb1 one_pos ht').const_mul (Real.log (M ^ 2))
  have h2 := ksU_integrable_ksUb2.const_mul (Real.log (M ^ 2) ^ 2)
  rw [ksUFB, ksUFB, ksUc1B, ksUc2B, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul, ← integral_sub hb0 h1]
  refine (integral_congr_ae ?_).trans (integral_add (hb0.sub h1) h2)
  filter_upwards [ksU_ae_mem_cube] with z hz
  exact ksW_ksUb0_scale hM ht hz.1 hz.2.1 hz.2.2

end QED.ChainProof.SetAKS

end
