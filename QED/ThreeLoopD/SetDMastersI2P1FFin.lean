/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1FAsm
public import QED.ThreeLoopD.SetDMastersI2P1FZ

/-!
# Set (d), master `I₂`: the weights `g`, `h` and `w` on the unit square

On `(0, 1)²`, with `r = r(s, z) > 0`:

* `g(r²) - h(r²) = w(r)` (`QED.ThreeLoopD.i2P1FFin_diff`);
* `h(r²) ≥ 0`, `w(r) ≤ h(r²)`, `h(r²) ≤ max(w(r), 0) + 2 · 1[r < 1]` and
  `w(r) ≥ -1[r < 1]`;
* `r(s, z) < 1` iff `z < s`.

These bound the `h`-part of the `ℱ`-part by the positive part of `w` and an elementary term.

## Main results

* `QED.ThreeLoopD.i2P1FFin_diff`, `QED.ThreeLoopD.i2P1FFin_h_le`.
* `QED.ThreeLoopD.i2P1FFin_inner`: `∫₀¹ 2 z h(r(s, z)²) dz ≤ |I(s²)| + 3 s²`.
* `QED.ThreeLoopD.i2P1FFin_integrable`, `QED.ThreeLoopD.i2P1FFin_wt_sq`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Function
open scoped ENNReal

namespace QED.ThreeLoopD

/-- `g(r²) - h(r²) = w(r)` for `r ≥ 0`. -/
theorem i2P1FFin_diff {r : ℝ} (hr : 0 ≤ r) : i2P1Fgr (r ^ 2) - i2P1Fhr (r ^ 2) = i2P1Fw r := by
  unfold i2P1Fgr i2P1Fhr i2P1Fw
  rcases lt_or_ge r 1 with h | h
  · have h2 : r ^ 2 < 1 := by nlinarith
    rw [ite_eq_left h2, ite_eq_left h2, ite_eq_left h, Real.sqrt_sq hr,
      show 1 - r ^ 2 = (1 - r) * (1 + r) by ring, log_mul (by linarith) (by linarith)]
    ring
  · have h2 : ¬ r ^ 2 < 1 := by nlinarith
    rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right (not_lt.2 h)]
    ring

/-- `w(r) = h(r²) - 2 log (1 + r)` for `0 ≤ r < 1`. -/
theorem i2P1FFin_h_left {r : ℝ} (hr : 0 ≤ r) (h : r < 1) :
    i2P1Fhr (r ^ 2) = i2P1Fw r + 2 * log (1 + r) := by
  unfold i2P1Fhr i2P1Fw
  have h2 : r ^ 2 < 1 := by nlinarith
  rw [ite_eq_left h2, ite_eq_left h, Real.sqrt_sq hr,
    show 1 - r ^ 2 = (1 - r) * (1 + r) by ring, log_mul (by linarith) (by linarith)]
  ring

/-- `h(r²) = w(r)` for `r ≥ 1`. -/
theorem i2P1FFin_h_right {r : ℝ} (h : 1 ≤ r) : i2P1Fhr (r ^ 2) = i2P1Fw r := by
  unfold i2P1Fhr i2P1Fw
  have h2 : ¬ r ^ 2 < 1 := by nlinarith
  rw [ite_eq_right h2, ite_eq_right (not_lt.2 h)]

theorem i2P1FFin_w_right_nonneg {r : ℝ} (h : 1 ≤ r) : 0 ≤ i2P1Fw r := by
  unfold i2P1Fw
  rw [ite_eq_right (not_lt.2 h)]
  have : 0 < r ^ 2 := by positivity
  have h1 : 1 / r ^ 2 ≤ 1 := by rw [div_le_one this]; nlinarith
  have h0 : 0 ≤ 1 / r ^ 2 := by positivity
  have := log_nonpos (by linarith : (0 : ℝ) ≤ 1 - 1 / r ^ 2) (by linarith)
  linarith

/-- `w(r) ≥ -1` for `0 ≤ r < 1` (indeed `w(r) ≥ -r`). -/
theorem i2P1FFin_w_left_ge {r : ℝ} (hr : 0 ≤ r) (h : r < 1) : -1 ≤ i2P1Fw r := by
  unfold i2P1Fw
  rw [ite_eq_left h]
  have h1 := log_le_sub_one_of_pos (show 0 < 1 - r by linarith)
  have h2 := log_le_sub_one_of_pos (show 0 < 1 + r by linarith)
  linarith

theorem i2P1FFin_h_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ i2P1Fhr (r ^ 2) := by
  rcases lt_or_ge r 1 with h | h
  · rw [i2P1FFin_h_left hr h]
    unfold i2P1Fw
    rw [ite_eq_left h]
    have : log (1 - r) ≤ log (1 + r) := log_le_log (by linarith) (by linarith)
    linarith
  · rw [i2P1FFin_h_right h]
    exact i2P1FFin_w_right_nonneg h

theorem i2P1FFin_w_le_h {r : ℝ} (hr : 0 ≤ r) : i2P1Fw r ≤ i2P1Fhr (r ^ 2) := by
  rcases lt_or_ge r 1 with h | h
  · rw [i2P1FFin_h_left hr h]
    have := log_nonneg (show (1 : ℝ) ≤ 1 + r by linarith)
    linarith
  · rw [i2P1FFin_h_right h]

/-- `h(r²) ≤ max(w(r), 0) + 2` for `0 ≤ r < 1`. -/
theorem i2P1FFin_h_le {r : ℝ} (hr : 0 ≤ r) (h : r < 1) :
    i2P1Fhr (r ^ 2) ≤ max (i2P1Fw r) 0 + 2 := by
  rw [i2P1FFin_h_left hr h]
  have := log_le_sub_one_of_pos (show 0 < 1 + r by linarith)
  have := le_max_left (i2P1Fw r) 0
  linarith

theorem i2P1FFin_r_pos {s z : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 < i2P1Fr s z := by
  unfold i2P1Fr
  have : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have := hs.1
  have := hz.1
  positivity

/-- `r(s, z) < 1` iff `z < s`. -/
theorem i2P1FFin_r_lt_iff {s z : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    i2P1Fr s z < 1 ↔ z < s := by
  have p5 : 0 < -1 * z + 1 := by linarith [hz.2]
  have p6 : 0 < 1 * z + 1 := by linarith [hz.1]
  have p2 : 0 < s * z + 1 := by nlinarith [hs.1, hz.1]
  have hD : 0 < s * (-1 * z + 1) * (1 * z + 1) := by have := hs.1; positivity
  have hr1 := i2P1FZ_one_sub_r hs.1.ne' p5.ne' p6.ne'
  constructor
  · intro h
    have h' : 0 < 1 - i2P1Fr s z := by linarith
    rw [hr1] at h'
    have := (div_pos_iff_of_pos_right hD).1 h'
    exact by_contra fun hc => absurd this (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg
      (by linarith [not_lt.1 hc]) p2.le))
  · intro h
    have : 0 < 1 - i2P1Fr s z := by rw [hr1]; exact div_pos (mul_pos (by linarith) p2) hD
    linarith

theorem measurable_i2P1Fw : Measurable i2P1Fw := by
  unfold i2P1Fw
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) (by fun_prop)
    (by fun_prop)

theorem i2P1FFin_sq {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) :
    ∫⁻ z in Ioo (0 : ℝ) s, ENNReal.ofReal (2 * c * z) = ENNReal.ofReal (c * s ^ 2) := by
  rw [i2P1FW_ftc (F := fun z => c * z ^ 2) hs.le (fun z _ => by
    simpa using ((hasDerivAt_pow 2 z).const_mul c).congr_deriv (by ring)) (by fun_prop)
    (fun z hz => by have := hz.1; positivity)]
  simp

theorem i2P1FFin_ind {s c : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hc : 0 ≤ c) :
    ∫⁻ z in Ioo (0 : ℝ) 1, (Iio s).indicator (fun z => ENNReal.ofReal (2 * c * z)) z =
      ENNReal.ofReal (c * s ^ 2) := by
  rw [setLIntegral_indicator measurableSet_Iio, inter_comm, Ioo_inter_Iio, min_eq_right hs.2.le,
    i2P1FFin_sq hs.1 hc]

/-- **The inner bound**: `∫₀¹ 2 z h(r(s, z)²) dz ≤ |I(s²)| + 3 s²`. -/
theorem i2P1FFin_inner {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) * ENNReal.ofReal (i2P1Fhr (i2P1Fr s z ^ 2)) ≤
      ENNReal.ofReal (|i2P1FI (s ^ 2)| + 3 * s ^ 2) := by
  obtain ⟨hi, hv⟩ := i2P1FZ_inner hs
  set f : ℝ → ℝ := fun z => 2 * z * i2P1Fw (i2P1Fr s z) with hf
  have hfi : IntegrableOn f (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hi
  have hneg : ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (-f z) ≤ ENNReal.ofReal (1 * s ^ 2) := by
    rw [← i2P1FFin_ind hs zero_le_one]
    refine setLIntegral_mono' measurableSet_Ioo fun z hz => ?_
    have hr := i2P1FFin_r_pos hs hz
    by_cases hzs : z < s
    · rw [indicator_of_mem (show z ∈ Iio s from hzs)]
      apply ENNReal.ofReal_le_ofReal
      have := i2P1FFin_w_left_ge hr.le ((i2P1FFin_r_lt_iff hs hz).2 hzs)
      simp only [hf]
      nlinarith [hz.1]
    · rw [indicator_of_notMem (show z ∉ Iio s from hzs)]
      refine le_of_eq (ENNReal.ofReal_eq_zero.2 ?_)
      have := i2P1FFin_w_right_nonneg (not_lt.1 (mt (i2P1FFin_r_lt_iff hs hz).1 hzs))
      simp only [hf]
      nlinarith [hz.1]
  have hpos : ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (f z) ≤
      ENNReal.ofReal (i2P1FI (s ^ 2) + s ^ 2) := by
    have h1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi
    have hfin := hfi.lintegral_lt_top
    rw [← ENNReal.ofReal_toReal hfin.ne]
    apply ENNReal.ofReal_le_ofReal
    have h2 : ∫ z in Ioo (0 : ℝ) 1, f z = i2P1FI (s ^ 2) := by
      rw [← hv, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    have h3 : (∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (-f z)).toReal ≤ 1 * s ^ 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hneg
    linarith
  have hmf : Measurable fun z => ENNReal.ofReal (f z) :=
    ENNReal.measurable_ofReal.comp (by
      simp only [hf]
      exact measurable_id.const_mul 2 |>.mul (measurable_i2P1Fw.comp (by unfold i2P1Fr; fun_prop)))
  calc ∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * z) * ENNReal.ofReal (i2P1Fhr (i2P1Fr s z ^ 2))
      ≤ ∫⁻ z in Ioo (0 : ℝ) 1, (ENNReal.ofReal (f z) +
          (Iio s).indicator (fun z => ENNReal.ofReal (2 * 2 * z)) z) := by
        refine setLIntegral_mono' measurableSet_Ioo fun z hz => ?_
        have hr := i2P1FFin_r_pos hs hz
        have hz0 := hz.1
        rw [← ENNReal.ofReal_mul (by positivity)]
        by_cases hzs : z < s
        · rw [indicator_of_mem (show z ∈ Iio s from hzs)]
          have hlt := (i2P1FFin_r_lt_iff hs hz).2 hzs
          have hb := i2P1FFin_h_le hr.le hlt
          rcases le_or_gt 0 (i2P1Fw (i2P1Fr s z)) with hw | hw
          · rw [max_eq_left hw] at hb
            refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
            simp only [hf]
            nlinarith
          · rw [max_eq_right hw.le] at hb
            refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
            nlinarith
        · rw [indicator_of_notMem (show z ∉ Iio s from hzs), add_zero,
            i2P1FFin_h_right (not_lt.1 (mt (i2P1FFin_r_lt_iff hs hz).1 hzs))]
    _ = (∫⁻ z in Ioo (0 : ℝ) 1, ENNReal.ofReal (f z)) + ENNReal.ofReal (2 * s ^ 2) := by
        rw [lintegral_add_left hmf, i2P1FFin_ind hs (by norm_num)]
    _ ≤ ENNReal.ofReal (i2P1FI (s ^ 2) + s ^ 2) + ENNReal.ofReal (2 * s ^ 2) := by
        gcongr
    _ ≤ ENNReal.ofReal (|i2P1FI (s ^ 2)| + s ^ 2) + ENNReal.ofReal (2 * s ^ 2) := by
        gcongr
        exact le_abs_self _
    _ = ENNReal.ofReal (|i2P1FI (s ^ 2)| + 3 * s ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- `s ↦ 8 (1 + s²) / (s (1 - s²)) log² s · I(s²)` is integrable on `(0, 1)`. -/
theorem i2P1FFin_integrable : IntegrableOn (fun s : ℝ =>
    8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2 * i2P1FI (s ^ 2)) (Ioo 0 1) := by
  have himg : (fun s : ℝ => s ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨s, ⟨h0, h1⟩, rfl⟩
      exact ⟨by positivity, by nlinarith⟩
    · rintro ⟨h0, h1⟩
      refine ⟨Real.sqrt t, ⟨Real.sqrt_pos.2 h0, ?_⟩, Real.sq_sqrt h0.le⟩
      rw [Real.sqrt_lt' one_pos]
      linarith
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 i2P1FEnd_value.1
  rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul (f' := fun s => 2 * s)
    measurableSet_Ioo (fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt)
    (fun a ha b hb hab => (sq_eq_sq₀ ha.1.le hb.1.le).1 hab)] at h
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioo
  have h0 : s ≠ 0 := hs.1.ne'
  have h1 : 1 - s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
  simp only [smul_eq_mul, abs_of_pos (by linarith [hs.1] : (0 : ℝ) < 2 * s), log_pow]
  push_cast
  field_simp
  ring

/-- `8 (1 + s²) / (s (1 - s²)) log² s · s² ≤ 64` on `(0, 1)`. -/
theorem i2P1FFin_wt_sq {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2 * s ^ 2 ≤ 64 := by
  obtain ⟨h0, h1⟩ := hs
  have hq : 0 < 1 - s ^ 2 := by nlinarith
  have e : 8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2 * s ^ 2 =
      8 * (1 + s ^ 2) / (1 - s ^ 2) * (s * log s ^ 2) := by field_simp
  rw [e]
  have hl : log s ≤ 0 := log_nonpos h0.le h1.le
  have hA : s * log s ^ 2 < 4 := by
    have hr := abs_log_mul_self_lt (Real.sqrt s) (Real.sqrt_pos.2 h0)
      (Real.sqrt_le_one.2 h1.le)
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt h0.le
    have hlog : log (Real.sqrt s) = log s / 2 := by
      rw [Real.log_sqrt h0.le]
    rw [hlog, abs_lt] at hr
    nlinarith [Real.sqrt_nonneg s]
  have hB : -log s ≤ (1 - s) / s := by
    have := log_le_sub_one_of_pos (inv_pos.2 h0)
    rw [Real.log_inv] at this
    rw [div_eq_mul_inv, sub_mul, one_mul, mul_inv_cancel₀ h0.ne']
    linarith
  rcases le_or_gt s (1 / 2) with hs2 | hs2
  · have : 8 * (1 + s ^ 2) / (1 - s ^ 2) ≤ 14 := by
      rw [div_le_iff₀ hq]; nlinarith
    nlinarith [mul_nonneg h0.le (sq_nonneg (log s))]
  · have hB' : log s ^ 2 ≤ ((1 - s) / s) ^ 2 := by
      rw [← neg_sq]; exact pow_le_pow_left₀ (by linarith) hB 2
    have hC : s * log s ^ 2 ≤ (1 - s) ^ 2 / s := by
      calc s * log s ^ 2 ≤ s * ((1 - s) / s) ^ 2 := mul_le_mul_of_nonneg_left hB' h0.le
        _ = (1 - s) ^ 2 / s := by field_simp
    have hD : (1 - s) ^ 2 / s ≤ 2 * (1 - s) ^ 2 := by
      rw [div_le_iff₀ h0]; nlinarith [sq_nonneg (1 - s)]
    have hE : 8 * (1 + s ^ 2) / (1 - s ^ 2) * (2 * (1 - s) ^ 2) = 16 * (1 + s ^ 2) * (1 - s) /
        (1 + s) := by
      field_simp
      ring
    have hF : 16 * (1 + s ^ 2) * (1 - s) / (1 + s) ≤ 64 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc 8 * (1 + s ^ 2) / (1 - s ^ 2) * (s * log s ^ 2)
        ≤ 8 * (1 + s ^ 2) / (1 - s ^ 2) * (2 * (1 - s) ^ 2) :=
          mul_le_mul_of_nonneg_left (hC.trans hD) (by positivity)
      _ ≤ 64 := by rw [hE]; exact hF

end QED.ThreeLoopD
