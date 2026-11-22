/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBDr
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Set (a), stage D: the cutoff expansion of the `VB` class

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). For one
flavour `M` and one `s > -4M²` the cutoff photon-mass integral of the `VB` class,
`I_B(Λ) = ∫_{(ρ,β)} ∫_w ksUDB M s Λ ρ β w`, satisfies

  `I_B(Λ) - c₂ (log Λ)² - c₁ log Λ → F_B`   (`Λ → ∞`),

with `c₂ = ∫ b₂`, `c₁ = ∫ b₁` and `F_B = ∫ b₀` over the unit cube in `((ρ, β), w)`.

The boundary-layer model `M` of `ksU_ksUDB_split` has the exact `ρ`-integral
`∫₀¹ (1 - ρ)⁻¹ f₀ log(1 + Λ(1 - ρ)/A(β)) dρ = f₀ K(Λ/A(β))` (`ksU_integral_ksUMd`), so
`I_B(Λ) - c₂ (log Λ)² - c₁ log Λ = ∫ ksUDr` for `Λ ≥ 1`, and dominated convergence
(`ksU_abs_ksUDr_le`, `ksU_tendsto_ksUDr`) gives the limit.

Main results:

* `ksU_integral_ksUMd`: the exact `ρ`-integral of the boundary-layer model;
* **`ksU_VB_sub_eq`**: `I_B(Λ) - c₂ (log Λ)² - c₁ log Λ = ∫ ksUDr` for `Λ ≥ 1`;
* **`ksU_VB_expansion`**: the limit.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace QED.ChainProof.SetAKS

/-- The unit cube measure in the coordinates `((ρ, β), w)`. -/
local notation "ksUν3" =>
  Measure.prod (Measure.prod (volume.restrict (Ioo (0 : ℝ) 1)) (volume.restrict (Ioo (0 : ℝ) 1)))
    (volume.restrict (Ioo (0 : ℝ) 1))

/-- The unit square measure. -/
local notation "ksUν2" =>
  Measure.prod (volume.restrict (Ioo (0 : ℝ) 1)) (volume.restrict (Ioo (0 : ℝ) 1))

/-! ### The exact `ρ`-integral of the boundary-layer model -/

/-- **The `ρ`-integral of the boundary-layer model**: for `A(β) > 0` and `Λ > 0`,
`∫_{(0,1)} (1 - ρ)⁻¹ f₀ log(1 + Λ(1 - ρ)/A(β)) dρ = f₀ K(Λ/A(β))`. -/
theorem ksU_integral_ksUMd {M s Λ β w : ℝ} (hAb : 0 < ksDA M s β) (hΛ : 0 < Λ) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksUMd M s Λ ρ β w = ksUf0 β w * ksUK (Λ / ksDA M s β) := by
  set c := Λ / ksDA M s β with hc
  have hc0 : 0 < c := div_pos hΛ hAb
  have e : ∀ ρ, ksUMd M s Λ ρ β w = ksUf0 β w * c * ksUKer (c * (1 - ρ)) := by
    intro ρ
    have hx : Λ * (1 - ρ) / ksDA M s β = c * (1 - ρ) := by rw [hc]; ring
    unfold ksUMd ksUKer
    rw [hx]
    rcases eq_or_ne (1 - ρ) 0 with h | h
    · simp [h]
    · field_simp
  simp_rw [e]
  rw [MeasureTheory.integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left (fun x => ksUKer (c * x)) (1 : ℝ), sub_self,
    sub_zero, mul_assoc, intervalIntegral.mul_integral_comp_mul_left, mul_zero, mul_one]
  rfl

/-! ### Fubini on the cube -/

theorem ksU_ae_mem_cube : ∀ᵐ z ∂ksUν3, z.1.1 ∈ Ioo (0 : ℝ) 1 ∧ z.1.2 ∈ Ioo (0 : ℝ) 1 ∧
    z.2 ∈ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem ((measurableSet_Ioo.prod measurableSet_Ioo).prod
    measurableSet_Ioo)] with z hz
  exact ⟨hz.1.1, hz.1.2, hz.2⟩

theorem ksU_integrable_cube_of_le {f : (ℝ × ℝ) × ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (h : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ β ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1,
      |f ((ρ, β), w)| ≤ C * (ksUg ρ * ksUg w)) : Integrable f ksUν3 := by
  refine Integrable.mono' (ksU_integrable_ksUg_cube.const_mul C) hf.aestronglyMeasurable ?_
  filter_upwards [ksU_ae_mem_cube] with z hz
  exact h _ hz.1 _ hz.2.1 _ hz.2.2

/-- The `ρ`-integral innermost: `∫_{cube} g = ∫_{(β, w)} ∫_ρ g`. -/
theorem ksU_integral_cube_eq {g : (ℝ × ℝ) × ℝ → ℝ} (hg : Integrable g ksUν3) :
    ∫ z, g z ∂ksUν3 = ∫ q : ℝ × ℝ, (∫ ρ in Ioo (0 : ℝ) 1, g ((ρ, q.1), q.2)) ∂ksUν2 := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hmp := measurePreserving_prodAssoc μ μ μ
  set e : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ := MeasurableEquiv.prodAssoc
  have h1 : ∫ z, g z ∂(μ.prod μ).prod μ = ∫ y, g (e.symm y) ∂μ.prod (μ.prod μ) := by
    rw [← hmp.integral_comp' (fun y : ℝ × ℝ × ℝ => g (e.symm y))]
    simp only [MeasurableEquiv.symm_apply_apply]
  have h2 : Integrable (fun y => g (e.symm y)) (μ.prod (μ.prod μ)) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    simpa [Function.comp_def] using hg
  rw [h1, integral_prod_symm _ h2]
  rfl

/-- The model and its integrated form have the same cube integral. -/
theorem ksU_integral_ksUMd_cube {M s Λ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hΛ : 0 < Λ)
    (h1 : Integrable (fun z : (ℝ × ℝ) × ℝ => ksUMd M s Λ z.1.1 z.1.2 z.2) ksUν3)
    (h2 : Integrable (fun z : (ℝ × ℝ) × ℝ => ksUf0 z.1.2 z.2 * ksUK (Λ / ksDA M s z.1.2))
      ksUν3) :
    ∫ z, ksUMd M s Λ z.1.1 z.1.2 z.2 ∂ksUν3 =
      ∫ z, ksUf0 z.1.2 z.2 * ksUK (Λ / ksDA M s z.1.2) ∂ksUν3 := by
  rw [ksU_integral_cube_eq h1, ksU_integral_cube_eq h2]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ q ∂ksUν2, q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  filter_upwards [hae] with q hq
  rw [ksU_integral_ksUMd (ksD_ksDA_pos hM hs (Ioo_subset_Icc_self hq.1)) hΛ, setIntegral_const,
    Real.volume_real_Ioo_of_le zero_le_one, sub_zero, one_smul]

/-! ### Measurability on the cube -/

section Meas

variable (M s : ℝ)

theorem ksU_measurable_cube_A : Measurable fun z : (ℝ × ℝ) × ℝ => ksDA M s z.2 := by
  unfold ksDA; fun_prop

theorem ksU_measurable_cube_Ab : Measurable fun z : (ℝ × ℝ) × ℝ => ksDA M s z.1.2 := by
  unfold ksDA; fun_prop

theorem ksU_measurable_cube_Y : Measurable fun z : (ℝ × ℝ) × ℝ => ksDYmax z.1.2 z.2 := by
  unfold ksDYmax; fun_prop

theorem ksU_measurable_cube_b (u : ℝ) :
    Measurable fun z : (ℝ × ℝ) × ℝ => ksDbB M u (ksUPtB z.1.1 z.1.2) s := by
  unfold ksDbB ksNEB; simp only [ksUPtB]; simp; fun_prop

theorem ksU_measurable_cube_f0 : Measurable fun z : (ℝ × ℝ) × ℝ => ksUf0 z.1.2 z.2 := by
  have := ksU_measurable_cube_Y
  unfold ksUf0; fun_prop

theorem ksU_measurable_cube_l3 : Measurable fun z : (ℝ × ℝ) × ℝ => ksUl3 M s z.1.1 z.1.2 z.2 := by
  have := ksU_measurable_cube_Y
  have := ksU_measurable_cube_A M s
  unfold ksUl3; fun_prop

theorem ksU_measurable_cube_R : Measurable fun z : (ℝ × ℝ) × ℝ => ksUR M s z.1.1 z.1.2 z.2 := by
  have := ksU_measurable_cube_Y
  have := ksU_measurable_cube_A M s
  have := ksU_measurable_cube_Ab M s
  unfold ksUR; fun_prop

theorem ksU_measurable_cube_q : Measurable fun z : (ℝ × ℝ) × ℝ => ksUq z.1.1 z.1.2 z.2 := by
  unfold ksUq; fun_prop

theorem ksU_measurable_cube_G0 : Measurable fun z : (ℝ × ℝ) × ℝ => ksUG0 M s z.1.1 z.1.2 z.2 := by
  have hρ : Measurable fun z : (ℝ × ℝ) × ℝ => z.1.1 := by fun_prop
  have hβ : Measurable fun z : (ℝ × ℝ) × ℝ => z.1.2 := by fun_prop
  have hw : Measurable fun z : (ℝ × ℝ) × ℝ => z.2 := by fun_prop
  have hE := ksU_measurable_ksDEc_ptB M hρ hβ hw 0
  have hH := ksU_measurable_ksDHc_ptB hρ hβ hw 0
  have := ksU_measurable_cube_A M s
  unfold ksUG0 ksUGc; fun_prop

theorem ksU_measurable_cube_J (u : ℝ) : Measurable fun z : (ℝ × ℝ) × ℝ =>
    ksDJ1 (ksDA M s z.2) (ksDbB M u (ksUPtB z.1.1 z.1.2) s) (ksDYmax z.1.2 z.2) 0 :=
  (ksU_measurable_J (ksU_measurable_cube_A M s) (ksU_measurable_cube_b M s u)
    ksU_measurable_cube_Y 0).1

theorem ksU_measurable_ksUDr (Λ : ℝ) :
    Measurable fun z : (ℝ × ℝ) × ℝ => ksUDr M s Λ z.1.1 z.1.2 z.2 := by
  have := ksU_measurable_cube_Y
  have := ksU_measurable_cube_A M s
  have := ksU_measurable_cube_Ab M s
  have := ksU_measurable_cube_b M s Λ
  have := ksU_measurable_cube_b M s 0
  have := ksU_measurable_cube_f0
  have := ksU_measurable_cube_l3 M s
  have := ksU_measurable_cube_R M s
  have := ksU_measurable_cube_q
  have := ksU_measurable_cube_G0 M s
  have := ksU_measurable_cube_J M s Λ
  have := ksU_measurable_cube_J M s 0
  unfold ksUDr ksUQs ksUQ1 ksUQ2 ksUQ3 ksUQ4 ksUb2 ksUb1 ksUcB
  fun_prop

theorem ksU_measurable_ksUMd (Λ : ℝ) :
    Measurable fun z : (ℝ × ℝ) × ℝ => ksUMd M s Λ z.1.1 z.1.2 z.2 := by
  have := ksU_measurable_cube_Ab M s
  have := ksU_measurable_cube_f0
  unfold ksUMd; fun_prop

theorem ksU_measurable_f0K (Λ : ℝ) :
    Measurable fun z : (ℝ × ℝ) × ℝ => ksUf0 z.1.2 z.2 * ksUK (Λ / ksDA M s z.1.2) := by
  have := ksU_measurable_cube_Ab M s
  have := ksU_measurable_cube_f0
  fun_prop

theorem ksU_measurable_ksUb2 : Measurable fun z : (ℝ × ℝ) × ℝ => ksUb2 z.1.1 z.1.2 z.2 := by
  have := ksU_measurable_cube_f0
  unfold ksUb2 ksUcB; fun_prop

theorem ksU_measurable_ksUb1 : Measurable fun z : (ℝ × ℝ) × ℝ => ksUb1 M s z.1.1 z.1.2 z.2 := by
  have := ksU_measurable_cube_Y
  have := ksU_measurable_cube_Ab M s
  have := ksU_measurable_cube_f0
  have := ksU_measurable_cube_l3 M s
  have := ksU_measurable_cube_q
  unfold ksUb1 ksUcB; fun_prop

end Meas

/-! ### The expansion -/

/-- The `(log Λ)²` coefficient of the `VB` class. -/
noncomputable def ksUc2B : ℝ := ∫ z, ksUb2 z.1.1 z.1.2 z.2 ∂ksUν3

/-- The `log Λ` coefficient of the `VB` class. -/
noncomputable def ksUc1B (M s : ℝ) : ℝ := ∫ z, ksUb1 M s z.1.1 z.1.2 z.2 ∂ksUν3

/-- The finite part of the `VB` class. -/
noncomputable def ksUFB (M s : ℝ) : ℝ := ∫ z, ksUb0 M s z.1.1 z.1.2 z.2 ∂ksUν3

section Exp

variable {M s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
include hM hs

omit hM hs in
theorem ksU_integrable_ksUb2 : Integrable (fun z : (ℝ × ℝ) × ℝ => ksUb2 z.1.1 z.1.2 z.2) ksUν3 :=
  ksU_integrable_cube_of_le ksU_measurable_ksUb2 4 fun ρ hρ β hβ w hw =>
    (ksU_abs_ksUb2_le hρ hβ hw).trans (le_mul_of_one_le_right (by norm_num)
      (ksU_logs_le_B hρ hw).1)

theorem ksU_integrable_ksUb1 :
    Integrable (fun z : (ℝ × ℝ) × ℝ => ksUb1 M s z.1.1 z.1.2 z.2) ksUν3 :=
  ksU_integrable_cube_of_le (ksU_measurable_ksUb1 M s) _ fun _ρ hρ _β hβ _w hw =>
    ksU_abs_ksUb1_le hM hs hρ hβ hw

theorem ksU_integrable_ksUMd {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    Integrable (fun z : (ℝ × ℝ) × ℝ => ksUMd M s Λ z.1.1 z.1.2 z.2) ksUν3 :=
  ksU_integrable_cube_of_le (ksU_measurable_ksUMd M s Λ) (4 * Λ * (ksUkA M s)⁻¹)
    fun ρ hρ β hβ w hw => (ksU_abs_ksUMd_le hM hs hρ hβ hw hΛ).trans
      (le_mul_of_one_le_right (by have := ksU_ksUkA_pos hM hs; positivity)
        (ksU_logs_le_B hρ hw).1)

theorem ksU_integrable_f0K {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    Integrable (fun z : (ℝ × ℝ) × ℝ => ksUf0 z.1.2 z.2 * ksUK (Λ / ksDA M s z.1.2)) ksUν3 :=
  ksU_integrable_cube_of_le (ksU_measurable_f0K M s Λ) (4 * Λ * (ksUkA M s)⁻¹)
    fun ρ hρ _β hβ w hw => (ksU_abs_f0K_le hM hs hβ hw hΛ).trans
      (le_mul_of_one_le_right (by have := ksU_ksUkA_pos hM hs; positivity)
        (ksU_logs_le_B hρ hw).1)

omit hM hs in
theorem ksU_integrable_ksUDr {C Λ : ℝ}
    (hC : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ β ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1,
      |ksUDr M s Λ ρ β w| ≤ C * (ksUg ρ * ksUg w)) :
    Integrable (fun z : (ℝ × ℝ) × ℝ => ksUDr M s Λ z.1.1 z.1.2 z.2) ksUν3 :=
  ksU_integrable_cube_of_le (ksU_measurable_ksUDr M s Λ) C hC

/-- **The `VB` integral minus its logarithms is the cube integral of the remainder** (`Λ ≥ 1`). -/
theorem ksU_VB_sub_eq {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    (∫ p : ℝ × ℝ, (∫ w in Ioo (0 : ℝ) 1, ksUDB M s Λ p.1 p.2 w) ∂ksUν2) -
        ksUc2B * Real.log Λ ^ 2 - ksUc1B M s * Real.log Λ =
      ∫ z, ksUDr M s Λ z.1.1 z.1.2 z.2 ∂ksUν3 := by
  obtain ⟨C, hC⟩ := ksU_abs_ksUDr_le hM hs
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  set L := Real.log Λ
  have hDr := ksU_integrable_ksUDr (hC Λ hΛ)
  have hb2 := ksU_integrable_ksUb2
  have hb1 := ksU_integrable_ksUb1 hM hs
  have hMd := ksU_integrable_ksUMd hM hs hΛ0
  have hfK := ksU_integrable_f0K hM hs hΛ0
  have hb2L : Integrable (fun z : (ℝ × ℝ) × ℝ => ksUb2 z.1.1 z.1.2 z.2 * L ^ 2) ksUν3 :=
    hb2.mul_const _
  have hb1L : Integrable (fun z : (ℝ × ℝ) × ℝ => ksUb1 M s z.1.1 z.1.2 z.2 * L) ksUν3 :=
    hb1.mul_const _
  have hD2 : Integrable (fun z : (ℝ × ℝ) × ℝ =>
      ksUDr M s Λ z.1.1 z.1.2 z.2 + ksUb2 z.1.1 z.1.2 z.2 * L ^ 2) ksUν3 := hDr.add hb2L
  have hR : Integrable (fun z : (ℝ × ℝ) × ℝ =>
      ksUDr M s Λ z.1.1 z.1.2 z.2 + ksUb2 z.1.1 z.1.2 z.2 * L ^ 2 +
        ksUb1 M s z.1.1 z.1.2 z.2 * L) ksUν3 := hD2.add hb1L
  have hMf : Integrable (fun z : (ℝ × ℝ) × ℝ =>
      ksUMd M s Λ z.1.1 z.1.2 z.2 - ksUf0 z.1.2 z.2 * ksUK (Λ / ksDA M s z.1.2)) ksUν3 :=
    hMd.sub hfK
  have hsplit : ∀ᵐ z ∂ksUν3, ksUDB M s Λ z.1.1 z.1.2 z.2 =
      (ksUMd M s Λ z.1.1 z.1.2 z.2 - ksUf0 z.1.2 z.2 * ksUK (Λ / ksDA M s z.1.2)) +
        (ksUDr M s Λ z.1.1 z.1.2 z.2 + ksUb2 z.1.1 z.1.2 z.2 * L ^ 2 +
          ksUb1 M s z.1.1 z.1.2 z.2 * L) := by
    filter_upwards [ksU_ae_mem_cube] with z hz
    rw [ksU_ksUDB_split hM hs hz.1 hz.2.1 hz.2.2 hΛ0]
    simp only [ksUDr, ksUQs]
    ring
  have hDB : Integrable (fun z : (ℝ × ℝ) × ℝ => ksUDB M s Λ z.1.1 z.1.2 z.2) ksUν3 :=
    (hMf.add hR).congr (hsplit.mono fun z h => h.symm)
  have hP := integral_prod _ hDB
  simp only at hP
  rw [← hP, integral_congr_ae hsplit, integral_add hMf hR,
    integral_sub hMd hfK, ksU_integral_ksUMd_cube hM hs (by linarith) hMd hfK, sub_self,
    zero_add, integral_add hD2 hb1L, integral_add hDr hb2L, MeasureTheory.integral_mul_const,
    MeasureTheory.integral_mul_const, ksUc2B, ksUc1B]
  ring

/-- **The cutoff expansion of the `VB` class** (one flavour, one `s`):
`I_B(Λ) - c₂ (log Λ)² - c₁ log Λ → F_B` as `Λ → ∞`. -/
theorem ksU_VB_expansion :
    Tendsto (fun Λ => (∫ p : ℝ × ℝ, (∫ w in Ioo (0 : ℝ) 1, ksUDB M s Λ p.1 p.2 w) ∂ksUν2) -
        ksUc2B * Real.log Λ ^ 2 - ksUc1B M s * Real.log Λ) atTop (𝓝 (ksUFB M s)) := by
  obtain ⟨C, hC⟩ := ksU_abs_ksUDr_le hM hs
  have hlim : Tendsto (fun Λ => ∫ z, ksUDr M s Λ z.1.1 z.1.2 z.2 ∂ksUν3) atTop
      (𝓝 (ksUFB M s)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => C * (ksUg z.1.1 * ksUg z.2))
      (Eventually.of_forall fun Λ => (ksU_measurable_ksUDr M s Λ).aestronglyMeasurable) ?_
      (ksU_integrable_ksUg_cube.const_mul C) ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
      filter_upwards [ksU_ae_mem_cube] with z hz
      rw [Real.norm_eq_abs]
      exact hC Λ hΛ _ hz.1 _ hz.2.1 _ hz.2.2
    · filter_upwards [ksU_ae_mem_cube] with z hz
      exact ksU_tendsto_ksUDr hM hs hz.1 hz.2.1 hz.2.2
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  exact (ksU_VB_sub_eq hM hs hΛ).symm

end Exp

end QED.ChainProof.SetAKS

end
