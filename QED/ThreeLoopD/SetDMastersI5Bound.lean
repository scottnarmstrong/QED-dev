/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5TriAsy

/-!
# Set (d), master `I₅`: the bound on `(1, ∞)`

With `K_as = Tri_as / t` (`Tri_as = QED.ThreeLoopD.i5TriAs`) and `N_ε ∫₋₁¹ (1 - z²) ^ (1/2 - ε) = 1`
(`QED.ThreeLoopD.i5Nrm_mul_wt`),

  `K - K_as = N ∫ w_ε [Tri(w) (1/w - 1/t) + (Tri(w) - Tri(t)) / t + (Tri(t) - Tri_as) / t]`,

and the three terms are `O(t ^ (-12/5))`, `O(t ^ (-239/100))` (`‖w - t‖ ≤ 2 √t`) and
`O(t ^ (-12/5))` (`QED.ThreeLoopD.norm_i5Tri_sub_asym_le`), so
`‖K - K_as‖ ≤ C t ^ (-239/100)` (`QED.ThreeLoopD.norm_i5Ker_sub_le`). Since
`i5Asym = α₀ t ^ (1 - ε) t ^ (-ε) K_as` (`QED.ThreeLoopD.i5Asym_eq`),

  `t ^ (1 - ε) b K - i5Asym = t ^ (1 - ε) (b - α₀ t ^ (-ε)) K + α₀ t ^ (1 - ε) t ^ (-ε) (K - K_as)`,

which on `‖ε‖ = 1/10`, `t > 1` is at most `C t ^ (-119/100)` (`QED.ThreeLoopD.norm_i5RemInt2_le`),
using `‖b - α₀ t ^ (-ε)‖ ≤ C t ^ (-9/10)` and `‖K‖ ≤ C t ^ (-19/10)`. This is the last analytic
input: `QED.ThreeLoopD.hasTruncLaurent_setDMasterI5_of_coeff₃` needs only `c₀, c₁, c₂`.

## Main results

* `QED.ThreeLoopD.i5Nrm_mul_wt`, `QED.ThreeLoopD.norm_i5Ker_sub_le`.
* `QED.ThreeLoopD.norm_i5RemInt2_le`, `QED.ThreeLoopD.hasTruncLaurent_setDMasterI5_of_coeff₃`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.ThreeLoopD

theorem i5_rpow_mul_le {t : ℝ} (ht : 1 ≤ t) {a b c : ℝ} (h : a + b ≤ c) :
    t ^ a * t ^ b ≤ t ^ c := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le ht h

/-! ### The angular normalization -/

theorem continuous_i5Wt (ε : ℂ) (hε : ε.re < 1 / 2) :
    Continuous fun z : ℝ => ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) :=
  continuous_iff_continuousAt.mpr fun z =>
    (continuousAt_ofReal_cpow_const _ _ (Or.inl (by simp; linarith))).comp
      (by fun_prop : Continuous fun z : ℝ => 1 - z ^ 2).continuousAt

/-- **The normalization of the angular average**: `N_ε ∫₋₁¹ (1 - z²) ^ (1/2 - ε) dz = 1`. -/
theorem i5Nrm_mul_wt {ε : ℂ} (hε : ‖ε‖ < 1 / 2) :
    i5Nrm ε * ∫ z in Ioo (-1 : ℝ) 1, ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) = 1 := by
  have hre : ε.re < 1 / 2 := (re_le_norm ε).trans_lt hε
  have hc := continuous_i5Wt ε hre
  set f := fun z : ℝ => ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) with hf
  have hev : ∀ z, f (-z) = f z := fun z => by simp [hf]
  have hsplit : ∫ z in Ioo (-1 : ℝ) 1, f z = 2 * ∫ z in Ioo (0 : ℝ) 1, f z := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have e : ∫ z in (-1 : ℝ)..0, f z = ∫ z in (0 : ℝ)..1, f z := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) f
      simp only [hev, neg_zero] at this
      exact this.symm
    rw [e]; ring
  have h8 := i8Nrm_mul_Mom0 hε
  unfold i8Nrm i8Mom0 i8Wt at h8
  rw [hsplit, i5Nrm]
  simp only [hf]
  linear_combination h8

/-! ### The kernel at large `t` -/

theorem norm_i5W_sub_le (t : ℝ) {z : ℝ} (hz : |z| ≤ 1) :
    ‖i5W t z - (t : ℂ)‖ ≤ 2 * Real.sqrt t := by
  have e : i5W t z - (t : ℂ) = -(2 * ((Real.sqrt t * z : ℝ) : ℂ) * I) := by unfold i5W; ring
  rw [e, norm_neg, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_ofNat, norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
  nlinarith [Real.sqrt_nonneg t, abs_nonneg z]

theorem integrableOn_i5KerF {ε : ℂ} (hε : ‖ε‖ ≤ 1 / 4) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (i5KerF ε t) (Ioo (-1) 1) :=
  (integrableOn_const (C := i5TriB t / t) (by simp)).mono'
    ((measurable_i5KerF_uncurry ε).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem measurableSet_Ioo fun z hz => norm_i5KerF_le hε ht hz)

theorem i5_volume_real_Ioo : volume.real (Ioo (-1 : ℝ) 1) = 2 := by
  simp [measureReal_def, Real.volume_Ioo]
  norm_num

theorem i5_nonneg_of_le_mul {x C p : ℝ} (hx : 0 ≤ x) (h : x ≤ C * p) (hp : 0 < p) : 0 ≤ C := by
  exact le_of_not_gt fun hC => by nlinarith [mul_neg_of_neg_of_pos hC hp]

/-- **The kernel at large `t`**: `‖K_ε(t)‖ ≤ C t ^ (-19/10)`. -/
theorem norm_i5Ker_le_large : ∃ C, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ∀ t : ℝ, 1 ≤ t →
    ‖i5Ker ε t‖ ≤ C * t ^ (-(19 / 10 : ℝ)) := by
  obtain ⟨CN, hN⟩ := i5Nrm_bound
  refine ⟨CN * (2 * i5CTL), fun ε hε t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hN0 : 0 ≤ CN := (norm_nonneg _).trans (hN 0 (by simp))
  have hp : t ^ (-(9 / 10 : ℝ)) * t ^ (-1 : ℝ) = t ^ (-(19 / 10 : ℝ)) := by
    rw [← Real.rpow_add ht0]; norm_num
  have hpt : ∀ z ∈ Ioo (-1 : ℝ) 1, ‖i5KerF ε t z‖ ≤ i5CTL * t ^ (-(19 / 10 : ℝ)) := by
    intro z hz
    have hwt := norm_i5Wt_le (ε := ε) (by linarith [re_le_norm ε]) hz
    have hT := norm_i5Tri_le_large hε ht (re_i5W t z)
    have hT0 : 0 ≤ i5CTL * t ^ (-(9 / 10 : ℝ)) := (norm_nonneg _).trans hT
    unfold i5KerF
    have c1 := i5_nonneg_of_le_mul (norm_nonneg _) hT (Real.rpow_pos_of_pos ht0 _)
    have htne : t ≠ 0 := ht0.ne'
    rw [norm_div, norm_mul, div_le_iff₀ (norm_pos_iff.mpr (i5W_ne_zero ht0 z)), ← hp]
    calc ‖((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε)‖ * ‖i5Tri ε t (i5W t z)‖ ≤
          1 * (i5CTL * t ^ (-(9 / 10 : ℝ))) := mul_le_mul hwt hT (norm_nonneg _) zero_le_one
      _ = i5CTL * (t ^ (-(9 / 10 : ℝ)) * t ^ (-1 : ℝ)) * t := by
          rw [Real.rpow_neg_one]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_norm_i5W t z)
          (mul_nonneg c1 (by positivity))
  have hI := norm_setIntegral_le_of_norm_le_const
    (measure_Ioo_lt_top : volume (Ioo (-1 : ℝ) 1) < ⊤) hpt
  rw [i5_volume_real_Ioo] at hI
  rw [i5Ker_eq, norm_mul]
  calc ‖i5Nrm ε‖ * ‖∫ z in Ioo (-1 : ℝ) 1, i5KerF ε t z‖ ≤
        CN * (i5CTL * t ^ (-(19 / 10 : ℝ)) * 2) := mul_le_mul (hN ε hε) hI (norm_nonneg _) hN0
    _ = _ := by ring

/-- **The kernel minus its two-region expansion**: `‖K - Tri_as / t‖ ≤ C t ^ (-239/100)`. -/
theorem norm_i5Ker_sub_le : ∃ C, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ε ≠ 0 → ∀ t : ℝ, 1 ≤ t →
    ‖i5Ker ε t - i5TriAs ε t / t‖ ≤ C * t ^ (-(239 / 100 : ℝ)) := by
  obtain ⟨CN, hN⟩ := i5Nrm_bound
  set Cp := 2 * i5CTL + 2 * i5CTD + i5CF with hCp
  refine ⟨CN * (Cp * 2), fun ε hε h0 t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hε4 : ‖ε‖ ≤ 1 / 4 := by linarith
  have hre : ε.re < 1 / 2 := by linarith [re_le_norm ε]
  have hN0 : 0 ≤ CN := (norm_nonneg _).trans (hN 0 (by simp))
  have hW : IntegrableOn (fun z : ℝ => ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε)) (Ioo (-1) 1) :=
    (continuous_i5Wt ε hre).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hNw := i5Nrm_mul_wt (ε := ε) (by linarith)
  have hK : i5Ker ε t - i5TriAs ε t / t = i5Nrm ε * ∫ z in Ioo (-1 : ℝ) 1,
      (i5KerF ε t z - ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) * (i5TriAs ε t / t)) := by
    rw [integral_sub (integrableOn_i5KerF hε4 ht0) (hW.mul_const _), integral_mul_const,
      i5Ker_eq, mul_sub, ← mul_assoc, hNw, one_mul]
  have hpos : ∀ a : ℝ, 0 < t ^ a := fun a => Real.rpow_pos_of_pos ht0 a
  have htinv : ‖(t : ℂ)⁻¹‖ = t ^ (-1 : ℝ) := by
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos ht0, Real.rpow_neg_one]
  have hsq : Real.sqrt t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
  have p1 : t ^ (-(9 / 10 : ℝ)) * t ^ (-(3 / 2 : ℝ)) ≤ t ^ (-(239 / 100 : ℝ)) :=
    i5_rpow_mul_le ht (by norm_num)
  have p2 : t ^ (1 / 2 : ℝ) * t ^ (-(189 / 100 : ℝ)) * t ^ (-1 : ℝ) ≤ t ^ (-(239 / 100 : ℝ)) := by
    rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]; norm_num
  have p3 : t ^ (-(7 / 5 : ℝ)) * t ^ (-1 : ℝ) ≤ t ^ (-(239 / 100 : ℝ)) :=
    i5_rpow_mul_le ht (by norm_num)
  have hpt : ∀ z ∈ Ioo (-1 : ℝ) 1, ‖i5KerF ε t z - ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) *
      (i5TriAs ε t / t)‖ ≤ Cp * t ^ (-(239 / 100 : ℝ)) := by
    intro z hz
    have hz1 : |z| ≤ 1 := abs_le.mpr ⟨hz.1.le, hz.2.le⟩
    have e : i5KerF ε t z - ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) * (i5TriAs ε t / t) =
        ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) *
          (i5Tri ε t (i5W t z) * ((i5W t z)⁻¹ - (t : ℂ)⁻¹) +
            (i5Tri ε t (i5W t z) - i5Tri ε t (t : ℂ)) * (t : ℂ)⁻¹ +
            (i5Tri ε t (t : ℂ) - i5TriAs ε t) * (t : ℂ)⁻¹) := by
      unfold i5KerF; ring
    have hwt := norm_i5Wt_le (ε := ε) (by linarith) hz
    have hT1 := norm_i5Tri_le_large hε ht (re_i5W t z)
    have hT2 := norm_inv_i5W_sub_le ht0 hz1
    have hT3 := norm_i5Tri_sub_le hε ht (re_i5W t z)
    have hT4 := norm_i5W_sub_le t hz1
    have hT5 := norm_i5Tri_sub_asym_le hε h0 ht
    have c1 := i5_nonneg_of_le_mul (norm_nonneg _) hT1 (hpos _)
    have c3 := i5_nonneg_of_le_mul (norm_nonneg _) hT5 (hpos _)
    have c2 : 0 ≤ i5CTD := by
      have := (norm_nonneg _).trans (norm_i5Tri_sub_le hε ht (w := (t : ℂ) + I) (by simp))
      simp only [add_sub_cancel_left, norm_I, mul_one] at this
      exact i5_nonneg_of_le_mul le_rfl (by simpa using this) (hpos (-(189 / 100 : ℝ)))
    rw [e, norm_mul]
    have hA : ‖i5Tri ε t (i5W t z) * ((i5W t z)⁻¹ - (t : ℂ)⁻¹)‖ ≤
        i5CTL * t ^ (-(9 / 10 : ℝ)) * (2 * t ^ (-(3 / 2 : ℝ))) := by
      rw [norm_mul]; exact mul_le_mul hT1 hT2 (norm_nonneg _) (by positivity)
    have hB : ‖(i5Tri ε t (i5W t z) - i5Tri ε t (t : ℂ)) * (t : ℂ)⁻¹‖ ≤
        i5CTD * (2 * t ^ (1 / 2 : ℝ)) * t ^ (-(189 / 100 : ℝ)) * t ^ (-1 : ℝ) := by
      rw [norm_mul, htinv, ← hsq]
      refine mul_le_mul_of_nonneg_right (hT3.trans ?_) (hpos _).le
      gcongr
    have hC : ‖(i5Tri ε t (t : ℂ) - i5TriAs ε t) * (t : ℂ)⁻¹‖ ≤
        i5CF * t ^ (-(7 / 5 : ℝ)) * t ^ (-1 : ℝ) := by
      rw [norm_mul, htinv]; exact mul_le_mul_of_nonneg_right hT5 (hpos _).le
    have hS := (norm_add₃_le).trans (add_le_add (add_le_add hA hB) hC)
    have hS0 : 0 ≤ i5CTL * t ^ (-(9 / 10 : ℝ)) * (2 * t ^ (-(3 / 2 : ℝ))) +
        i5CTD * (2 * t ^ (1 / 2 : ℝ)) * t ^ (-(189 / 100 : ℝ)) * t ^ (-1 : ℝ) +
        i5CF * t ^ (-(7 / 5 : ℝ)) * t ^ (-1 : ℝ) := (norm_nonneg _).trans hS
    calc _ ≤ 1 * (i5CTL * t ^ (-(9 / 10 : ℝ)) * (2 * t ^ (-(3 / 2 : ℝ))) +
          i5CTD * (2 * t ^ (1 / 2 : ℝ)) * t ^ (-(189 / 100 : ℝ)) * t ^ (-1 : ℝ) +
          i5CF * t ^ (-(7 / 5 : ℝ)) * t ^ (-1 : ℝ)) := mul_le_mul hwt hS (norm_nonneg _) zero_le_one
      _ ≤ Cp * t ^ (-(239 / 100 : ℝ)) := by
          rw [hCp]
          nlinarith [mul_le_mul_of_nonneg_left p1 c1, mul_le_mul_of_nonneg_left p2 c2,
            mul_le_mul_of_nonneg_left p3 c3]
  have hI := norm_setIntegral_le_of_norm_le_const
    (measure_Ioo_lt_top : volume (Ioo (-1 : ℝ) 1) < ⊤) hpt
  rw [i5_volume_real_Ioo] at hI
  rw [hK, norm_mul]
  calc _ ≤ CN * (Cp * t ^ (-(239 / 100 : ℝ)) * 2) := mul_le_mul (hN ε hε) hI (norm_nonneg _) hN0
    _ = _ := by ring

/-! ### The bound on `(1, ∞)` -/

/-- `i5Asym = α₀ t ^ (1 - ε) t ^ (-ε) K_as`. -/
theorem i5Asym_eq (ε : ℂ) {t : ℝ} (ht : 0 < t) :
    i5Asym ε t = i13Al0 ε * (t : ℂ) ^ (1 - ε) * (t : ℂ) ^ (-ε) * (i5TriAs ε t / t) := by
  have hT : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have p1 : (t : ℂ) ^ (-1 - 2 * ε) =
      (t : ℂ) ^ (1 - ε) * (t : ℂ) ^ (-ε) * (t : ℂ)⁻¹ * (t : ℂ)⁻¹ := by
    rw [← cpow_neg_one, ← cpow_add _ _ hT, ← cpow_add _ _ hT, ← cpow_add _ _ hT]; ring_nf
  have p2 : (t : ℂ) ^ (-1 - 3 * ε) =
      (t : ℂ) ^ (1 - ε) * (t : ℂ) ^ (-ε) * (t : ℂ) ^ (-1 - ε) * (t : ℂ)⁻¹ := by
    rw [← cpow_neg_one, ← cpow_add _ _ hT, ← cpow_add _ _ hT, ← cpow_add _ _ hT]; ring_nf
  rw [i5Asym, i5TriAs, p1, p2]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- `‖b_ε(t) - α₀ t ^ (-ε)‖ ≤ C t ^ (-9/10)` for `t ≥ 1`. -/
theorem norm_i13Bub_sub_lead_le : ∃ C, ∀ ε : ℂ, ‖ε‖ ≤ 1 / 10 → ∀ t : ℝ, 1 ≤ t →
    ‖i13Bub ε t - i13Al0 ε * (t : ℂ) ^ (-ε)‖ ≤ C * t ^ (-(9 / 10 : ℝ)) := by
  obtain ⟨Cb, hb⟩ := norm_i13Bub_sub_asym_le
  obtain ⟨Ca, hA⟩ := i13_coeff_bound
  refine ⟨Cb + 4 * Ca, fun ε hε t ht => ?_⟩
  obtain ⟨a0, a1, a2, b0, b1⟩ := hA ε hε
  have ht0 : 0 < t := by linarith
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans a0
  have hu : ‖(t : ℂ) ^ (-ε)‖ ≤ t ^ ((1 : ℝ) / 10) := by
    rw [norm_cpow_eq_rpow_re_of_pos ht0]
    obtain ⟨-, h1, -⟩ := i5_re_facts hε
    exact Real.rpow_le_rpow_of_exponent_le ht (by simp; linarith)
  have h1 : 1 ≤ t ^ ((1 : ℝ) / 10) := Real.one_le_rpow ht (by norm_num)
  have hX : ∀ a b : ℂ, ‖a‖ ≤ Ca → ‖b‖ ≤ Ca →
      ‖a * (t : ℂ) ^ (-ε) + b‖ ≤ 2 * Ca * t ^ ((1 : ℝ) / 10) :=
    fun a b ha hb => by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      nlinarith [mul_le_mul ha hu (norm_nonneg _) hCa]
  have hq : t ^ ((1 : ℝ) / 10) / t = t ^ (-(9 / 10 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
  have hd1 : ‖(i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε) / t‖ ≤ 2 * Ca * t ^ (-(9 / 10 : ℝ)) := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos ht0, ← hq, mul_div_assoc']
    exact div_le_div_of_nonneg_right (hX _ _ a1 b0) ht0.le
  have hd2 : ‖(i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / (t : ℂ) ^ 2‖ ≤
      2 * Ca * t ^ (-(9 / 10 : ℝ)) := by
    rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos ht0, ← hq, mul_div_assoc']
    exact div_le_div_of_nonneg_left (by positivity) ht0 (by nlinarith)
      |>.trans' (div_le_div_of_nonneg_right (hX _ _ a2 b1) (by positivity))
  have hb' := hb ε hε t ht
  have hp : t ^ ((1 : ℝ) / 10 - 3) ≤ t ^ (-(9 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have hCb : 0 ≤ Cb := i5_nonneg_of_le_mul (norm_nonneg _) hb' (Real.rpow_pos_of_pos ht0 _)
  have e : i13Bub ε t - i13Al0 ε * (t : ℂ) ^ (-ε) = (i13Bub ε t - i13BubAsym ε t) +
      (i13Al1 ε * (t : ℂ) ^ (-ε) + i13Be0 ε) / t +
      (i13Al2 ε * (t : ℂ) ^ (-ε) + i13Be1 ε) / (t : ℂ) ^ 2 := by
    unfold i13BubAsym; ring
  rw [e]
  refine (norm_add₃_le).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hp hCb]

/-- **The bound on `(1, ∞)`**: `‖t ^ (1 - ε) b_ε K_ε - i5Asym‖ ≤ C t ^ (-119/100)` on the circle
`‖ε‖ = 1/10`. -/
theorem norm_i5RemInt2_le : ∃ C, ∀ t ∈ Ioi (1 : ℝ), ∀ ε : ℂ, ‖ε‖ = 1 / 10 →
    ‖(t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5Asym ε t‖ ≤ C * t ^ (-(119 / 100 : ℝ)) := by
  obtain ⟨CE, hE⟩ := norm_i13Bub_sub_lead_le
  obtain ⟨CB, hB⟩ := norm_i5Ker_le_large
  obtain ⟨CC, hC⟩ := norm_i5Ker_sub_le
  obtain ⟨Ca, hA⟩ := i13_coeff_bound
  refine ⟨CE * CB + Ca * CC, fun t ht ε hε => ?_⟩
  have ht1 : 1 ≤ t := le_of_lt ht
  have ht0 : 0 < t := by linarith
  have hε' : ‖ε‖ ≤ 1 / 10 := hε.le
  have h0 : ε ≠ 0 := fun h => by rw [h, norm_zero] at hε; norm_num at hε
  have hpos : ∀ a : ℝ, 0 < t ^ a := fun a => Real.rpow_pos_of_pos ht0 a
  obtain ⟨-, h1, h2⟩ := i5_re_facts hε'
  have hP : ‖(t : ℂ) ^ (1 - ε)‖ ≤ t ^ ((11 : ℝ) / 10) := by
    rw [norm_cpow_eq_rpow_re_of_pos ht0]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by simp; linarith)
  have hu : ‖(t : ℂ) ^ (-ε)‖ ≤ t ^ ((1 : ℝ) / 10) := by
    rw [norm_cpow_eq_rpow_re_of_pos ht0]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by simp; linarith)
  have hE' := hE ε hε' t ht1
  have hB' := hB ε hε' t ht1
  have hC' := hC ε hε' h0 t ht1
  have hA' := (hA ε hε').1
  have cE := i5_nonneg_of_le_mul (norm_nonneg _) hE' (hpos _)
  have cB := i5_nonneg_of_le_mul (norm_nonneg _) hB' (hpos _)
  have cC := i5_nonneg_of_le_mul (norm_nonneg _) hC' (hpos _)
  have cA : 0 ≤ Ca := (norm_nonneg _).trans hA'
  have e : (t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5Asym ε t =
      (t : ℂ) ^ (1 - ε) * (i13Bub ε t - i13Al0 ε * (t : ℂ) ^ (-ε)) * i5Ker ε t +
        i13Al0 ε * (t : ℂ) ^ (1 - ε) * (t : ℂ) ^ (-ε) * (i5Ker ε t - i5TriAs ε t / t) := by
    rw [i5Asym_eq ε ht0]; ring
  have q1 : t ^ ((11 : ℝ) / 10) * t ^ (-(9 / 10 : ℝ)) * t ^ (-(19 / 10 : ℝ)) ≤
      t ^ (-(119 / 100 : ℝ)) := by
    rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have q2 : t ^ ((11 : ℝ) / 10) * t ^ ((1 : ℝ) / 10) * t ^ (-(239 / 100 : ℝ)) ≤
      t ^ (-(119 / 100 : ℝ)) := by
    rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]; norm_num
  have hT1 : ‖(t : ℂ) ^ (1 - ε) * (i13Bub ε t - i13Al0 ε * (t : ℂ) ^ (-ε)) * i5Ker ε t‖ ≤
      CE * CB * (t ^ ((11 : ℝ) / 10) * t ^ (-(9 / 10 : ℝ)) * t ^ (-(19 / 10 : ℝ))) := by
    rw [norm_mul, norm_mul]
    calc _ ≤ t ^ ((11 : ℝ) / 10) * (CE * t ^ (-(9 / 10 : ℝ))) * (CB * t ^ (-(19 / 10 : ℝ))) :=
          mul_le_mul (mul_le_mul hP hE' (norm_nonneg _) (hpos _).le) hB' (norm_nonneg _)
            (mul_nonneg (hpos _).le (mul_nonneg cE (hpos _).le))
      _ = _ := by ring
  have hT2 : ‖i13Al0 ε * (t : ℂ) ^ (1 - ε) * (t : ℂ) ^ (-ε) * (i5Ker ε t - i5TriAs ε t / t)‖ ≤
      Ca * CC * (t ^ ((11 : ℝ) / 10) * t ^ ((1 : ℝ) / 10) * t ^ (-(239 / 100 : ℝ))) := by
    rw [norm_mul, norm_mul, norm_mul]
    calc _ ≤ Ca * t ^ ((11 : ℝ) / 10) * t ^ ((1 : ℝ) / 10) * (CC * t ^ (-(239 / 100 : ℝ))) :=
          mul_le_mul (mul_le_mul (mul_le_mul hA' hP (norm_nonneg _) cA) hu (norm_nonneg _)
            (mul_nonneg cA (hpos _).le)) hC' (norm_nonneg _)
            (mul_nonneg (mul_nonneg cA (hpos _).le) (hpos _).le)
      _ = _ := by ring
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add hT1 hT2).trans ?_)
  nlinarith [mul_le_mul_of_nonneg_left q1 (mul_nonneg cE cB),
    mul_le_mul_of_nonneg_left q2 (mul_nonneg cA cC)]

section Coeff

open Real QED.Polylog

/-- **The master from the three coefficients alone**: all analytic bounds are proved, and
`I₅ C⁻¹` has the LR96 expansion through `ε²` once `c₀, c₁, c₂` take their target values. -/
theorem hasTruncLaurent_setDMasterI5_of_coeff₃
    (h0 : i5RemCoeff 0 = -1 / 3 * (π : ℂ) ^ 2 + 3)
    (h1 : i5RemCoeff 1 = -4 / 45 * (π : ℂ) ^ 4 - 5 / 3 * (π : ℂ) ^ 2 - 5 * (zeta3 : ℂ) + 25)
    (h2 : i5RemCoeff 2 = -29 / 40 * (π : ℂ) ^ 4 + 25 / 6 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      + 4 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 37 / 6 * (π : ℂ) ^ 2 - 36 * (zeta3 : ℂ)
      - 49 / 2 * (zeta5 : ℂ) + 143) :
    HasTruncLaurent setDMasterI5 setDLaurentI5 2 := by
  obtain ⟨C, hC⟩ := norm_i5RemInt2_le
  exact hasTruncLaurent_setDMasterI5_of_coeff₂
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(119 / 100 : ℝ) < -1) one_pos).const_mul C)
    hC h0 h1 h2

end Coeff

end QED.ThreeLoopD
