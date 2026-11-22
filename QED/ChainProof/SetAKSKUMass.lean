/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBExp

/-!
# Set (a), stage D: the photon-mass integral of the mass class

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). The mass class of the reduced
density `ksDQ` is `σ(e, μ, u) ksMassF e μ x s`, with
`σ(e, m, u) = -(e²/8π²) ∫₀¹ (1 - x²)/(x²m² + (1 - x)u) dx`. Its cutoff integral is

  `∫_{(0, Λ]} σ(e, m, u) du = -(e²/8π²) ∫₀¹ (1 + x) log(1 + Λ(1 - x)/(x²m²)) dx`,

and, since `∫₀¹ (1 + x) dx = 3/2`,

  `∫_{(0, Λ]} σ(e, m, u) du + (e²/8π²)(3/2) log Λ → -(e²/8π²) c_m`,
  `c_m = ∫₀¹ (1 + x) log((1 - x)/(x²m²)) dx`.

Main results:

* `ksU_integral_sigma_u`: the photon-mass integral at a fixed Feynman parameter;
* **`ksU_integral_sigma`**: the integrability and the closed form of the cutoff integral;
* **`ksU_mass_expansion`**: the limit.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace QED.ChainProof.SetAKS

open QED.GradedProof.RPi4

/-- The integrand of `σ`: `(1 - x²)/(x²m² + (1 - x)u)`. -/
noncomputable def ksUsg (m x u : ℝ) : ℝ := (1 - x ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * u)

/-- `a(x) = (1 - x)/(x²m²)`. -/
noncomputable def ksUam (m x : ℝ) : ℝ := (1 - x) / (x ^ 2 * m ^ 2)

/-- The constant of the mass class: `c_m = ∫₀¹ (1 + x) log((1 - x)/(x²m²)) dx`. -/
noncomputable def ksUcm (m : ℝ) : ℝ := ∫ x in Ioo (0 : ℝ) 1, (1 + x) * Real.log (ksUam m x)

section Fixed

variable {m x : ℝ} (hm : 0 < m) (hx : x ∈ Ioo (0 : ℝ) 1)
include hm hx

theorem ksU_ksUam_pos : 0 < ksUam m x := by
  have := hx.1; have : 0 < 1 - x := by linarith [hx.2]
  unfold ksUam; positivity

theorem ksU_sg_den_pos {u : ℝ} (hu : 0 ≤ u) : 0 < x ^ 2 * m ^ 2 + (1 - x) * u := by
  have := hx.1; have : 0 < 1 - x := by linarith [hx.2]
  positivity

theorem ksU_ksUsg_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ ksUsg m x u := by
  have := ksU_sg_den_pos hm hx hu
  have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  unfold ksUsg; positivity

theorem ksU_ksUsg_le {u : ℝ} (hu : 0 ≤ u) : ksUsg m x u ≤ (x ^ 2 * m ^ 2)⁻¹ := by
  have h0 := ksU_sg_den_pos hm hx hu
  have hp : 0 < x ^ 2 * m ^ 2 := by have := hx.1; positivity
  have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  unfold ksUsg
  rw [div_le_iff₀ h0]
  have : x ^ 2 * m ^ 2 ≤ x ^ 2 * m ^ 2 + (1 - x) * u := by
    have := mul_nonneg (by linarith [hx.2] : 0 ≤ 1 - x) hu; linarith
  calc 1 - x ^ 2 ≤ 1 := by nlinarith
    _ = (x ^ 2 * m ^ 2)⁻¹ * (x ^ 2 * m ^ 2) := (inv_mul_cancel₀ hp.ne').symm
    _ ≤ _ := by gcongr

/-- **The photon-mass integral at a fixed Feynman parameter**:
`∫_{(0, Λ]} (1 - x²)/(x²m² + (1 - x)u) du = (1 + x) log(1 + Λ a(x))`. -/
theorem ksU_integral_sigma_u {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∫ u in Ioc (0 : ℝ) Λ, ksUsg m x u = (1 + x) * Real.log (1 + Λ * ksUam m x) := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have hx0 := hx.1
  have hpos : ∀ u ∈ uIcc 0 Λ, 0 < x ^ 2 * m ^ 2 + (1 - x) * u := fun u hu => by
    rw [uIcc_of_le hΛ] at hu; exact ksU_sg_den_pos hm hx hu.1
  rw [← intervalIntegral.integral_of_le hΛ]
  have hd : ∀ u ∈ uIcc 0 Λ, HasDerivAt (fun u => (1 + x) * Real.log (x ^ 2 * m ^ 2 + (1 - x) * u))
      (ksUsg m x u) u := fun u hu => by
    have hl := ((hasDerivAt_id u).const_mul (1 - x)).const_add (x ^ 2 * m ^ 2)
    have := (hl.log (hpos u hu).ne').const_mul (1 + x)
    convert this using 1
    · rfl
    · rw [ksUsg]
      simp only [id]
      ring
  have hc : ContinuousOn (ksUsg m x) (uIcc 0 Λ) := by
    unfold ksUsg
    exact continuousOn_const.div (by fun_prop) fun u hu => (hpos u hu).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable, mul_zero,
    add_zero, ← mul_sub, ← Real.log_div (hpos _ right_mem_uIcc).ne' (by positivity)]
  congr 2
  unfold ksUam
  field_simp

end Fixed

/-- `|log a(x)| ≤ |log(1 - x)| + 2|log x| + 2|log m|`. -/
theorem ksU_abs_log_ksUam_le {m x : ℝ} (hm : 0 < m) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |Real.log (ksUam m x)| ≤ |Real.log (1 - x)| + 2 * |Real.log x| + 2 * |Real.log m| := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have hx0 := hx.1
  rw [ksUam, Real.log_div h1.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  have := abs_sub (Real.log (1 - x)) (((2 : ℕ) : ℝ) * Real.log x + ((2 : ℕ) : ℝ) * Real.log m)
  have := abs_add_le (((2 : ℕ) : ℝ) * Real.log x) (((2 : ℕ) : ℝ) * Real.log m)
  simp only [Nat.cast_ofNat, abs_mul, abs_two] at *
  linarith

theorem ksU_abs_log_ksUam_le_g {m x : ℝ} (hm : 0 < m) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |Real.log (ksUam m x)| ≤ (6 + 2 * |Real.log m|) * ksUg x := by
  have h := ksU_abs_log_ksUam_le hm hx
  have h1 := ksU_abs_log_le hx.1 hx.2.le
  have h2 := ksU_abs_log_le (by linarith [hx.2] : (0 : ℝ) < 1 - x) (by linarith [hx.1])
  have hr := ksU_rpow_le_ksUg hx
  have hg := ksU_one_le_ksUg hx
  have : |Real.log m| ≤ |Real.log m| * ksUg x := le_mul_of_one_le_right (abs_nonneg _) hg
  linarith [hr.1, hr.2]

theorem ksU_measurable_ksUam (m : ℝ) : Measurable (ksUam m) := by unfold ksUam; fun_prop

/-- The mass-class integrand in `x` at the cutoff `Λ`. -/
theorem ksU_integrableOn_mass {m Λ : ℝ} (hm : 0 < m) (hΛ : 0 ≤ Λ) :
    IntegrableOn (fun x => (1 + x) * Real.log (1 + Λ * ksUam m x)) (Ioo (0 : ℝ) 1) := by
  have hme : Measurable fun x => (1 + x) * Real.log (1 + Λ * ksUam m x) := by
    have := ksU_measurable_ksUam m; fun_prop
  refine Integrable.mono' ((ksU_integrableOn_ksUg.const_mul (2 * (1 + Λ) *
    (7 + 2 * |Real.log m|)))) hme.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have ha := ksU_ksUam_pos hm hx
  have hl0 := Real.log_nonneg (by have := mul_nonneg hΛ ha.le; linarith :
    (1 : ℝ) ≤ 1 + Λ * ksUam m x)
  have hl := ksU_log_one_add_le_abs (by positivity : 0 < (1 + Λ) * ksUam m x)
  have hle : Real.log (1 + Λ * ksUam m x) ≤ Real.log (1 + (1 + Λ) * ksUam m x) :=
    Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_mul (by positivity) ha.ne'] at hl
  have hL := ksU_abs_log_ksUam_le_g hm hx
  have hg := ksU_one_le_ksUg hx
  have hlΛ : |Real.log (1 + Λ)| ≤ Λ := by
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + Λ); linarith
  have hA := abs_add_le (Real.log (1 + Λ)) (Real.log (ksUam m x))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith [hx.1] : (0 : ℝ) < 1 + x),
    abs_of_nonneg hl0]
  have hx1 : 1 + x ≤ 2 := by linarith [hx.2]
  have hB : Real.log (1 + Λ * ksUam m x) ≤ (1 + Λ) * (7 + 2 * |Real.log m|) * ksUg x := by
    have : Λ ≤ Λ * ksUg x := le_mul_of_one_le_right hΛ hg
    have : (6 + 2 * |Real.log m|) * ksUg x ≤ (1 + Λ) * ((6 + 2 * |Real.log m|) * ksUg x) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    nlinarith [abs_nonneg (Real.log m)]
  calc (1 + x) * Real.log (1 + Λ * ksUam m x) ≤ 2 * ((1 + Λ) * (7 + 2 * |Real.log m|) *
        ksUg x) := mul_le_mul hx1 hB hl0 (by norm_num)
    _ = _ := by ring

/-- **The cutoff integral of the mass insertion**: for `m > 0`, `Λ > 0`, `σ(e, m, ·)` is
integrable on `(0, Λ]` and
`∫_{(0, Λ]} σ(e, m, u) du = -(e²/8π²) ∫₀¹ (1 + x) log(1 + Λ a(x)) dx`. -/
theorem ksU_integral_sigma {e m Λ : ℝ} (hm : 0 < m) (hΛ : 0 < Λ) :
    IntegrableOn (sigma e m) (Ioc (0 : ℝ) Λ) ∧
      ∫ u in Ioc (0 : ℝ) Λ, sigma e m u = -(e ^ 2 / (8 * Real.pi ^ 2)) *
        ∫ x in Ioo (0 : ℝ) 1, (1 + x) * Real.log (1 + Λ * ksUam m x) := by
  set μx := volume.restrict (Ioo (0 : ℝ) 1)
  set μu := volume.restrict (Ioc (0 : ℝ) Λ)
  have hmeas : Measurable fun p : ℝ × ℝ => ksUsg m p.1 p.2 := by unfold ksUsg; fun_prop
  have hint : Integrable (fun p : ℝ × ℝ => ksUsg m p.1 p.2) (μx.prod μu) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      refine Integrable.mono' (integrableOn_const (C := (x ^ 2 * m ^ 2)⁻¹)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
        (by unfold ksUsg; fun_prop : Measurable fun u => ksUsg m x u).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (ksU_ksUsg_nonneg hm hx hu.1.le)]
      exact ksU_ksUsg_le hm hx hu.1.le
    · refine (ksU_integrableOn_mass hm hΛ.le).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [← ksU_integral_sigma_u hm hx hΛ.le]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (ksU_ksUsg_nonneg hm hx hu.1.le)]
  have hsig : EqOn (sigma e m) (fun u => -(e ^ 2 / (8 * Real.pi ^ 2)) *
      ∫ x, ksUsg m x u ∂μx) (Ioc (0 : ℝ) Λ) := fun u _ => by
    rw [sigma, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rfl
  refine ⟨?_, ?_⟩
  · exact IntegrableOn.congr_fun (hint.integral_prod_right.const_mul _) hsig.symm
      measurableSet_Ioc
  · rw [setIntegral_congr_fun measurableSet_Ioc hsig, MeasureTheory.integral_const_mul]
    congr 1
    rw [← integral_integral_swap hint]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    exact ksU_integral_sigma_u hm hx hΛ.le

theorem ksU_integral_one_add : ∫ x in Ioo (0 : ℝ) 1, (1 + x) = 3 / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_add intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp
  norm_num

/-- **The cutoff expansion of the mass class**: for `m > 0`,
`∫₀¹ (1 + x) log(1 + Λ a(x)) dx - (3/2) log Λ → c_m`. -/
theorem ksU_tendsto_mass {m : ℝ} (hm : 0 < m) :
    Tendsto (fun Λ => (∫ x in Ioo (0 : ℝ) 1, (1 + x) * Real.log (1 + Λ * ksUam m x)) -
      3 / 2 * Real.log Λ) atTop (𝓝 (ksUcm m)) := by
  have hlim : Tendsto (fun Λ => ∫ x in Ioo (0 : ℝ) 1,
      (1 + x) * (Real.log (1 + Λ * ksUam m x) - Real.log Λ)) atTop (𝓝 (ksUcm m)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => 2 * (1 + 2 * ((6 + 2 * |Real.log m|) * ksUg x)))
      (Eventually.of_forall fun Λ => by
        have := ksU_measurable_ksUam m; exact (by fun_prop : Measurable fun x =>
          (1 + x) * (Real.log (1 + Λ * ksUam m x) - Real.log Λ)).aestronglyMeasurable) ?_
      ((integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).add
        ((ksU_integrableOn_ksUg.const_mul _).const_mul 2) |>.const_mul 2) ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have ha := ksU_ksUam_pos hm hx
      have h1 := ksU_abs_log_sub_le ha hΛ
      have h2 := ksU_log_one_add_le_abs ha
      have h3 := ksU_abs_log_ksUam_le_g hm hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith [hx.1] : (0 : ℝ) < 1 + x)]
      have : |Real.log (1 + Λ * ksUam m x) - Real.log Λ| ≤
          1 + 2 * ((6 + 2 * |Real.log m|) * ksUg x) := by linarith
      exact mul_le_mul (by linarith [hx.2]) this (abs_nonneg _) (by norm_num)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (ksU_tendsto_log_sub (ksU_ksUam_pos hm hx)).const_mul (1 + x)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  have hI := ksU_integrableOn_mass hm (by linarith : (0 : ℝ) ≤ Λ)
  have hc : IntegrableOn (fun x : ℝ => (1 + x) * Real.log Λ) (Ioo (0 : ℝ) 1) :=
    (by fun_prop : Continuous fun x : ℝ => (1 + x) * Real.log Λ).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  simp_rw [mul_sub]
  rw [integral_sub hI hc, MeasureTheory.integral_mul_const, ksU_integral_one_add]

/-- **The cutoff expansion of the mass insertion**: for `m > 0`,
`∫_{(0, Λ]} σ(e, m, u) du + (e²/8π²)(3/2) log Λ → -(e²/8π²) c_m`. -/
theorem ksU_mass_expansion {e m : ℝ} (hm : 0 < m) :
    Tendsto (fun Λ => (∫ u in Ioc (0 : ℝ) Λ, sigma e m u) -
      -(e ^ 2 / (8 * Real.pi ^ 2)) * (3 / 2) * Real.log Λ) atTop
      (𝓝 (-(e ^ 2 / (8 * Real.pi ^ 2)) * ksUcm m)) := by
  refine ((ksU_tendsto_mass hm).const_mul (-(e ^ 2 / (8 * Real.pi ^ 2)))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  rw [(ksU_integral_sigma (e := e) hm hΛ).2]
  ring

end QED.ChainProof.SetAKS

end
