/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUMass

/-!
# Set (a), stage D: the sum of the classes and the per-flavour limit as a finite part

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). The cutoff integral of the
reduced subtracted density,

  `T(Λ) = ∫_{(0, Λ]} ksDSub e μ x s u du
       = K (2 (I_A(s) - I_A(0)) + I_B(s) - I_B(0)) + (∫_{(0, Λ]} σ) (m(s) - m(0))`,

`K = π⁴e⁴/(2π)⁸`, is a sum of the three classes `VA`, `VB` and mass, each with a cutoff
expansion (`ksU_VA_expansion`, `ksU_VB_expansion`, `ksU_mass_expansion`). The `(log Λ)²`
coefficients cancel in the subtraction `s - 0` exactly, so `T(Λ) - b log Λ → F` for explicit
`b = ksUb1Tot`, `F = ksUFTot`. Since `T(Λ) → Re(e⁴ decT₀)` (`ksD_tendsto_integral_re`), the
logarithm coefficient vanishes and the per-flavour limit is the finite part:

  `ksUb1Tot e μ x s = 0`,   `Re(e⁴ decT₀ e μ x s) = ksUFTot e μ x s`.

Main results:

* `ksU_log_coeff_eq`: if `g → L` and `g - b log Λ → F` then `b = 0` and `L = F`;
* `ksU_tendsto_VA`: the `VA` expansion as a limit;
* **`ksU_tendsto_ksUTot_sub`**, **`ksU_tendsto_ksUTot`**;
* **`ksU_decT₀_re_eq`**: `ksUb1Tot = 0` and `Re(e⁴ decT₀) = ksUFTot`.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace QED.ChainProof.SetAKS

open QED.GradedProof.RPi4

/-- **The logarithm coefficient of a convergent function vanishes**: if `g → L` and
`g(Λ) - b log Λ → F` as `Λ → ∞`, then `b = 0` and `L = F`. -/
theorem ksU_log_coeff_eq {g : ℝ → ℝ} {b F L : ℝ} (h1 : Tendsto g atTop (𝓝 L))
    (h2 : Tendsto (fun Λ => g Λ - b * Real.log Λ) atTop (𝓝 F)) : b = 0 ∧ L = F := by
  have hb : Tendsto (fun Λ => b * Real.log Λ) atTop (𝓝 (L - F)) :=
    (h1.sub h2).congr fun Λ => by ring
  have hq : Tendsto (fun Λ => b * Real.log Λ / Real.log Λ) atTop (𝓝 0) :=
    hb.div_atTop Real.tendsto_log_atTop
  have hq' : Tendsto (fun Λ => b * Real.log Λ / Real.log Λ) atTop (𝓝 b) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Λ hΛ
    rw [mul_div_assoc, div_self (Real.log_pos hΛ).ne', mul_one]
  have hb0 : b = 0 := tendsto_nhds_unique hq' hq
  refine ⟨hb0, ?_⟩
  have h0 : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 (L - F)) := by
    simpa [hb0] using hb
  have := tendsto_nhds_unique tendsto_const_nhds h0
  linarith

/-- `(1 + log Λ)/√Λ → 0`. -/
theorem ksU_tendsto_rate : Tendsto (fun Λ => (1 + Real.log Λ) / Real.sqrt Λ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun Λ : ℝ => (Real.sqrt Λ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have h2 : Tendsto (fun Λ : ℝ => Real.log Λ / Λ ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  rw [← Real.sqrt_eq_rpow, add_div, one_div]

/-- **The `VA` expansion as a limit** (one flavour, one `s`). -/
theorem ksU_tendsto_VA {M s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) :
    Tendsto (fun Λ => (∫ x in Ioo (0 : ℝ) 1, ∫ σ in Ioo (0 : ℝ) 1, ksUDA M s Λ x σ) -
      (ksUc2 * Real.log Λ ^ 2 + ksUc1 M s * Real.log Λ)) atTop (𝓝 (ksUF M s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hr := ksU_tendsto_rate.const_mul (ksUCE M s * ksUGint)
  rw [mul_zero] at hr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hr
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  rw [Real.norm_eq_abs, sub_sub, mul_div_assoc']
  exact ksU_VA_expansion hM hs hΛ

/-! ### The flavour sums of the classes -/

section Flavour

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {s : ℝ}
  (hM : ∀ f, 0 < Φ.mass f) (hs : ∀ f, -(4 * Φ.mass f ^ 2) < s)
include hM hs

/-- The `VA` class of a flavour set. -/
theorem ksU_tendsto_NestA :
    Tendsto (fun Λ => (∫ u in Ioc (0 : ℝ) Λ, ksDNestA Φ u s) -
      ∑ f, Φ.coeff f * (ksUc2 * Real.log Λ ^ 2 + ksUc1 (Φ.mass f) s * Real.log Λ)) atTop
      (𝓝 (∑ f, Φ.coeff f * ksUF (Φ.mass f) s)) := by
  have h := tendsto_finsetSum (Finset.univ : Finset F) fun f _ =>
    (ksU_tendsto_VA (hM f) (hs f)).const_mul (Φ.coeff f)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with Λ hΛ
  obtain ⟨-, hi, he⟩ := ksU_integral_ksDNestA Φ hM hs hΛ
  rw [he, integral_finsetSum _ fun f _ => (hi f).const_mul (Φ.coeff f), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MeasureTheory.integral_const_mul, mul_sub]

/-- The `VB` class of a flavour set. -/
theorem ksU_tendsto_NestB :
    Tendsto (fun Λ => (∫ u in Ioc (0 : ℝ) Λ, ksDNestB Φ u s) -
      ∑ f, Φ.coeff f * (ksUc2B * Real.log Λ ^ 2 + ksUc1B (Φ.mass f) s * Real.log Λ)) atTop
      (𝓝 (∑ f, Φ.coeff f * ksUFB (Φ.mass f) s)) := by
  have h := tendsto_finsetSum (Finset.univ : Finset F) fun f _ =>
    (ksU_VB_expansion (hM f) (hs f)).const_mul (Φ.coeff f)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with Λ hΛ
  obtain ⟨-, hi, he⟩ := ksU_integral_ksDNestB Φ hM hs hΛ
  rw [he, integral_finsetSum _ fun f _ => (hi f).const_mul (Φ.coeff f), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MeasureTheory.integral_const_mul]
  ring

end Flavour

/-! ### The sum of the classes -/

/-- `K = π⁴e⁴/(2π)⁸`, the prefactor of the nested classes in `ksDQ`. -/
noncomputable def ksUKe (e : ℝ) : ℝ := Real.pi ^ 4 * e ^ 4 / (2 * Real.pi) ^ 8

/-- The mass-class prefactor `-(e²/8π²)`. -/
noncomputable def ksUme (e : ℝ) : ℝ := -(e ^ 2 / (8 * Real.pi ^ 2))

/-- **The `log Λ` coefficient of the cutoff integral of the reduced subtracted density.** -/
noncomputable def ksUb1Tot (e μ x s : ℝ) : ℝ :=
  ksUKe e * (2 * (∑ f, (decCfg μ x).coeff f * ksUc1 ((decCfg μ x).mass f) s -
      ∑ f, (decCfg μ x).coeff f * ksUc1 ((decCfg μ x).mass f) 0) +
    (∑ f, (decCfg μ x).coeff f * ksUc1B ((decCfg μ x).mass f) s -
      ∑ f, (decCfg μ x).coeff f * ksUc1B ((decCfg μ x).mass f) 0)) +
  ksUme e * (3 / 2) * (ksMassF e μ x s - ksMassF e μ x 0)

/-- **The finite part of the cutoff integral of the reduced subtracted density.** -/
noncomputable def ksUFTot (e μ x s : ℝ) : ℝ :=
  ksUKe e * (2 * (∑ f, (decCfg μ x).coeff f * ksUF ((decCfg μ x).mass f) s -
      ∑ f, (decCfg μ x).coeff f * ksUF ((decCfg μ x).mass f) 0) +
    (∑ f, (decCfg μ x).coeff f * ksUFB ((decCfg μ x).mass f) s -
      ∑ f, (decCfg μ x).coeff f * ksUFB ((decCfg μ x).mass f) 0)) +
  ksUme e * ksUcm μ * (ksMassF e μ x s - ksMassF e μ x 0)

section Sum

variable {e μ x s : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hs : -(4 * μ ^ 2) < s)
include hμ hx hs

omit hs in
theorem ksU_cfg_mass_pos (f : Fin 3) : 0 < (decCfg μ x).mass f :=
  hμ.trans_le (ksK_mass hμ hx f)

theorem ksU_cfg_s (f : Fin 3) : -(4 * (decCfg μ x).mass f ^ 2) < s := by
  have h := ksK_mass hμ hx f
  nlinarith

omit hs in
theorem ksU_cfg_zero (f : Fin 3) : -(4 * (decCfg μ x).mass f ^ 2) < 0 := by
  have := ksU_cfg_mass_pos hμ hx f
  nlinarith

/-- The cutoff integral of the reduced subtracted density as the sum of the classes. -/
theorem ksU_integral_ksDSub {Λ : ℝ} (hΛ : 0 < Λ) :
    IntegrableOn (ksDSub e μ x s) (Ioc (0 : ℝ) Λ) ∧
      ∫ u in Ioc (0 : ℝ) Λ, ksDSub e μ x s u =
        ksUKe e * (2 * ((∫ u in Ioc (0 : ℝ) Λ, ksDNestA (decCfg μ x) u s) -
            ∫ u in Ioc (0 : ℝ) Λ, ksDNestA (decCfg μ x) u 0) +
          ((∫ u in Ioc (0 : ℝ) Λ, ksDNestB (decCfg μ x) u s) -
            ∫ u in Ioc (0 : ℝ) Λ, ksDNestB (decCfg μ x) u 0)) +
        (∫ u in Ioc (0 : ℝ) Λ, sigma e μ u) * (ksMassF e μ x s - ksMassF e μ x 0) := by
  have hA := (ksU_integral_ksDNestA_cfg hμ hx hs hΛ.le).1
  have hA0 := (ksU_integral_ksDNestA_cfg (s := 0) hμ hx (by nlinarith) hΛ.le).1
  have hB := (ksU_integral_ksDNestB_cfg hμ hx hs hΛ.le).1
  have hB0 := (ksU_integral_ksDNestB_cfg (s := 0) hμ hx (by nlinarith) hΛ.le).1
  have hσ := (ksU_integral_sigma (e := e) hμ hΛ).1
  have hQ : ∀ t, IntegrableOn (fun u => ksDNestA (decCfg μ x) u t) (Ioc (0 : ℝ) Λ) →
      IntegrableOn (fun u => ksDNestB (decCfg μ x) u t) (Ioc (0 : ℝ) Λ) →
      IntegrableOn (fun u => ksDQ e μ x t u) (Ioc (0 : ℝ) Λ) ∧
        ∫ u in Ioc (0 : ℝ) Λ, ksDQ e μ x t u = ksUKe e *
          (2 * (∫ u in Ioc (0 : ℝ) Λ, ksDNestA (decCfg μ x) u t) +
            ∫ u in Ioc (0 : ℝ) Λ, ksDNestB (decCfg μ x) u t) +
          (∫ u in Ioc (0 : ℝ) Λ, sigma e μ u) * ksMassF e μ x t := fun t h1 h2 => by
    have i1 : IntegrableOn (fun u => 2 * ksDNestA (decCfg μ x) u t + ksDNestB (decCfg μ x) u t)
        (Ioc (0 : ℝ) Λ) := (h1.const_mul 2).add h2
    have i2 : IntegrableOn (fun u => ksUKe e * (2 * ksDNestA (decCfg μ x) u t +
        ksDNestB (decCfg μ x) u t)) (Ioc (0 : ℝ) Λ) := i1.const_mul _
    have i3 : IntegrableOn (fun u => sigma e μ u * ksMassF e μ x t) (Ioc (0 : ℝ) Λ) :=
      hσ.mul_const _
    refine ⟨i2.add i3, ?_⟩
    simp only [ksDQ]
    rw [show Real.pi ^ 4 * e ^ 4 / (2 * Real.pi) ^ 8 = ksUKe e from rfl, integral_add i2 i3,
      MeasureTheory.integral_const_mul, integral_add (h1.const_mul 2) h2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
  obtain ⟨q1, e1⟩ := hQ s hA hB
  obtain ⟨q0, e0⟩ := hQ 0 hA0 hB0
  refine ⟨q1.sub q0, ?_⟩
  simp only [ksDSub]
  rw [integral_sub q1 q0, e1, e0]
  ring

/-- **The cutoff expansion of the sum of the classes.** -/
theorem ksU_tendsto_ksUTot_sub :
    Tendsto (fun Λ => (∫ u in Ioc (0 : ℝ) Λ, ksDSub e μ x s u) -
      ksUb1Tot e μ x s * Real.log Λ) atTop (𝓝 (ksUFTot e μ x s)) := by
  set Φ := decCfg μ x
  have hM := ksU_cfg_mass_pos hμ hx
  have tA := ksU_tendsto_NestA Φ hM (ksU_cfg_s hμ hx hs)
  have tA0 := ksU_tendsto_NestA Φ hM (ksU_cfg_zero hμ hx)
  have tB := ksU_tendsto_NestB Φ hM (ksU_cfg_s hμ hx hs)
  have tB0 := ksU_tendsto_NestB Φ hM (ksU_cfg_zero hμ hx)
  have tm := (ksU_mass_expansion (e := e) hμ).mul_const (ksMassF e μ x s - ksMassF e μ x 0)
  have ht := (((((tA.sub tA0).const_mul 2).add (tB.sub tB0)).const_mul (ksUKe e)).add tm)
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  rw [(ksU_integral_ksDSub hμ hx hs hΛ).2]
  set L := Real.log Λ
  have eA : ∑ f, Φ.coeff f * (ksUc2 * L ^ 2 + ksUc1 (Φ.mass f) s * L) -
      ∑ f, Φ.coeff f * (ksUc2 * L ^ 2 + ksUc1 (Φ.mass f) 0 * L) =
      (∑ f, Φ.coeff f * ksUc1 (Φ.mass f) s - ∑ f, Φ.coeff f * ksUc1 (Φ.mass f) 0) * L := by
    rw [sub_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun f _ => by ring
  have eB : ∑ f, Φ.coeff f * (ksUc2B * L ^ 2 + ksUc1B (Φ.mass f) s * L) -
      ∑ f, Φ.coeff f * (ksUc2B * L ^ 2 + ksUc1B (Φ.mass f) 0 * L) =
      (∑ f, Φ.coeff f * ksUc1B (Φ.mass f) s - ∑ f, Φ.coeff f * ksUc1B (Φ.mass f) 0) * L := by
    rw [sub_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun f _ => by ring
  simp only [ksUb1Tot, ksUme]
  linear_combination (-(2 * ksUKe e)) * eA - ksUKe e * eB

/-- **The cutoff integral converges to the per-flavour limit.** -/
theorem ksU_tendsto_ksUTot (he : e ≠ 0) :
    Tendsto (fun Λ => ∫ u in Ioc (0 : ℝ) Λ, ksDSub e μ x s u) atTop
      (𝓝 (((e : ℂ) ^ 4 * decT₀ e μ x s).re)) := by
  set R := ((e : ℂ) ^ 4 * decT₀ e μ x s).re
  set f := ksDSub e μ x s
  have hI1 : IntegrableOn f (Ioc (0 : ℝ) 1) := (ksU_integral_ksDSub hμ hx hs one_pos).1
  have hIc : IntegrableOn f (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]; exact hI1
  have hc := intervalIntegral.continuousOn_primitive_interval_left hIc
  have hc0 : Tendsto (fun a => ∫ u in a..1, f u) (𝓝[>] 0) (𝓝 (∫ u in (0 : ℝ)..1, f u)) := by
    have h := (hc 0 left_mem_uIcc).tendsto
    rw [uIcc_of_le zero_le_one] at h
    refine h.mono_left ?_
    rw [← nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
    exact nhdsWithin_mono _ Ioo_subset_Icc_self
  have h01 : ∫ u in (0 : ℝ)..1, f u = R - ∫ u in Ioi 1, f u :=
    tendsto_nhds_unique hc0 (ksD_tendsto_integral_re he hμ hx hs)
  have hInf := intervalIntegral_tendsto_integral_Ioi 1 (ksD_integrableOn_ksDSub he hμ hx hs)
    tendsto_id
  have hR : R = (∫ u in (0 : ℝ)..1, f u) + ∫ u in Ioi 1, f u := by rw [h01, sub_add_cancel]
  have h := hInf.const_add (∫ u in (0 : ℝ)..1, f u)
  rw [← hR] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  have hIΛ : IntegrableOn f (Ioc (0 : ℝ) Λ) :=
    (ksU_integral_ksDSub hμ hx hs (by linarith)).1
  have i1 : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hI1
  have i2 : IntervalIntegrable f volume 1 Λ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hΛ).2
      (hIΛ.mono_set (Ioc_subset_Ioc_left zero_le_one))
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ Λ),
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  rfl

/-- **The per-flavour limit is the finite part of the sum of the classes**: for `e ≠ 0`,
`μ > 0`, `x ≥ μ²`, `s > -4μ²`, the `log Λ` coefficient of the cutoff integral vanishes and
`Re(e⁴ decT₀ e μ x s) = ksUFTot e μ x s`. -/
theorem ksU_decT₀_re_eq (he : e ≠ 0) :
    ksUb1Tot e μ x s = 0 ∧ ((e : ℂ) ^ 4 * decT₀ e μ x s).re = ksUFTot e μ x s :=
  ksU_log_coeff_eq (ksU_tendsto_ksUTot hμ hx hs he) (ksU_tendsto_ksUTot_sub hμ hx hs)

end Sum

end QED.ChainProof.SetAKS

end
