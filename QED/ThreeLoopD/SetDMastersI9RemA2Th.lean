/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA2CV
public import QED.ThreeLoopD.SetDMastersI9RemA2S
import QED.Polylog.HPLCalculus
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Set (d), master `I₉`: `∫ F₂` reduced to a one-dimensional integral and `K_u`

`QED.ThreeLoopD.i9A2DensP_eq` writes `Dens' = i9A2Dens + 4 log (1 - w) i9A1Dens` as
`|det Ψ'| · Θ ∘ Ψ`. This file shows that the `K_u` density `log (1 - w) · i9A1Dens` is
integrable on the `(x, w)`-square (in the variables `(p, s)` it is `-3 log (M/E) k g`, and
`p ≤ M/E ≤ 1` bounds it by `-3 k g log p`), so `Dens'` is integrable, the change of variables
applies to `Θ`, and Fubini in `(p, s)` (with the `s`-moments of `k`) gives

  `∫∫ i9A2Dens = ∫₀¹ j - 4 ∫∫ log (1 - w) · i9A1Dens`,
  `j = K ((-6 log p - 6 log (1 - p)) g + h) - 3 g K_b`.

## Main results

* `QED.ThreeLoopD.integrableOn_log_one_sub_mul_i9A1Dens`: the `K_u` density is integrable.
* `QED.ThreeLoopD.integrableOn_and_integral_i9A2j`: `j` is integrable and `∫∫ Θ = ∫₀¹ j`.
* `QED.ThreeLoopD.integral_i9A2Dens_split`: the splitting above.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-! ### Bounds on `K` and `g` -/

theorem i9A1K_le_two {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : i9A1K p ≤ 2 := by
  have hq : 0 < 1 - p := by linarith [hp.2]
  have hl : Real.log p ≤ p - 1 := Real.log_le_sub_one_of_pos hp.1
  have e : i9A1K p = 2 * ((1 - p) + p * Real.log p) / (1 - p) ^ 2 := by
    unfold i9A1K; field_simp
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hl hp.1.le]

theorem abs_log_div_one_sub_le {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    |Real.log p| / (1 - p) ≤ 2 + 2 * |Real.log p| := by
  have hq : 0 < 1 - p := by linarith [hp.2]
  rw [div_le_iff₀ hq]
  rcases le_or_gt p (1 / 2) with h | h
  · nlinarith [abs_nonneg (Real.log p)]
  · have hl : |Real.log p| ≤ (1 - p) / p := by
      rw [abs_of_nonpos (Real.log_nonpos hp.1.le hp.2.le)]
      have := Real.one_sub_inv_le_log_of_pos hp.1
      have e : (1 - p) / p = p⁻¹ - 1 := by field_simp
      linarith
    have : (1 - p) / p ≤ 2 * (1 - p) := by
      rw [div_le_iff₀ hp.1]; nlinarith
    nlinarith [abs_nonneg (Real.log p)]

theorem i9A1g_le {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    i9A1g p ≤ 4 + 3 * |Real.log p| + Real.log p ^ 2 := by
  have hq : 0 < 1 - p := by linarith [hp.2]
  have hR := Li₂_add_Li₂_one_sub hp.1.le hp.2.le
  have hL2 : Li₂ p ≤ π ^ 2 / 6 * p := by
    have := abs_Li₂_le (y := p) (by rw [abs_of_pos hp.1]; exact hp.2.le)
    rw [abs_of_pos hp.1] at this
    exact (le_abs_self _).trans this
  have hlq : -Real.log (1 - p) ≤ p / (1 - p) := by
    have := Real.one_sub_inv_le_log_of_pos hq
    have e : (1 - p)⁻¹ - 1 = p / (1 - p) := by field_simp; ring
    linarith
  have hlp : Real.log p ≤ 0 := Real.log_nonpos hp.1.le hp.2.le
  have hlq0 : Real.log (1 - p) ≤ 0 := Real.log_nonpos hq.le (by linarith [hp.1])
  have hA := abs_log_div_one_sub_le hp
  have habs : |Real.log p| = -Real.log p := abs_of_nonpos hlp
  have hpi : π ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  -- the dilogarithm term
  have h1 : (π ^ 2 / 6 - Li₂ (1 - p)) / p ≤ 2 + |Real.log p| / (1 - p) := by
    rw [div_le_iff₀ hp.1]
    have e : π ^ 2 / 6 - Li₂ (1 - p) = Li₂ p + Real.log p * Real.log (1 - p) := by linarith
    rw [e]
    have hm : Real.log p * Real.log (1 - p) ≤ |Real.log p| / (1 - p) * p := by
      rw [habs, div_mul_eq_mul_div, le_div_iff₀ hq]
      have hlq' : -Real.log (1 - p) * (1 - p) ≤ p := by
        have := mul_le_mul_of_nonneg_right hlq hq.le
        rwa [div_mul_cancel₀ _ hq.ne'] at this
      nlinarith [mul_le_mul_of_nonneg_left hlq' (by linarith : 0 ≤ -Real.log p)]
    nlinarith [mul_le_mul_of_nonneg_right hpi hp.1.le]
  have h2 : Real.log p ^ 2 / (2 * (1 - p)) ≤ |Real.log p| * (1 + |Real.log p|) := by
    have e : Real.log p ^ 2 / (2 * (1 - p)) = |Real.log p| * (|Real.log p| / (1 - p)) / 2 := by
      rw [← sq_abs]; field_simp
    rw [e]
    nlinarith [abs_nonneg (Real.log p)]
  unfold i9A1g
  nlinarith [abs_nonneg (Real.log p), sq_abs (Real.log p)]

/-! ### Integrability of polynomials in `log p` -/

theorem integrableOn_of_abs_le_log_poly {f : ℝ → ℝ} {C : ℝ} (hc : ContinuousOn f (Ioo 0 1))
    (hf : ∀ p ∈ Ioo (0 : ℝ) 1, |f p| ≤ C * (1 + |Real.log p| ^ 3)) :
    IntegrableOn f (Ioo 0 1) := by
  obtain ⟨C3, hC3, h3⟩ := HPL.abs_log_pow_le 3 (δ := 1 / 2) (by norm_num)
  have hint : IntegrableOn (fun t : ℝ => |C| * (1 + C3) * t ^ (-(1 / 2) : ℝ)) (Ioo 0 1) := by
    have := ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (r := -(1 / 2)) (by norm_num)).const_mul (|C| * (1 + C3)))
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at this
    exact this
  refine hint.mono' (hc.aestronglyMeasurable measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_)
  rw [Real.norm_eq_abs]
  have h1 : (1 : ℝ) ≤ t ^ (-(1 / 2) : ℝ) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2.le (by norm_num)
  have h3t := h3 t ⟨ht.1, ht.2.le⟩
  calc |f t| ≤ C * (1 + |Real.log t| ^ 3) := hf t ht
    _ ≤ |C| * (1 + |Real.log t| ^ 3) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (t ^ (-(1 / 2) : ℝ) + C3 * t ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
    _ = |C| * (1 + C3) * t ^ (-(1 / 2) : ℝ) := by ring

/-! ### The `K_u` density in the variables `(p, s)` -/

/-- `log u · k g` with `u = M / E`, `M = p + s² (1 - p)`, `E = s + p (1 - s)`. -/
noncomputable def i9A2ThU (q : ℝ × ℝ) : ℝ :=
  Real.log ((q.1 + q.2 ^ 2 * (1 - q.1)) / (q.2 + q.1 * (1 - q.2))) * i9A1G q

/-- `1 - w = M / E` at `Ψ(x, w)`. -/
theorem i9A2_u_eq {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    1 - z.2 = ((i9A1Map z).1 + (i9A1Map z).2 ^ 2 * (1 - (i9A1Map z).1)) /
      ((i9A1Map z).2 + (i9A1Map z).1 * (1 - (i9A1Map z).2)) := by
  have hP := i9A1P_pos hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  obtain ⟨x, w⟩ := z
  simp only at h1 h2 h3 h4
  unfold i9A1P at hP
  have hP' : x * (1 - x) * (1 - w) ^ 2 + w ≠ 0 := hP.ne'
  have ha : 0 < 1 - x * (1 - w) := by nlinarith
  have hu : 0 < 1 - w := by linarith
  have hE : x * (1 - w) + x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w) *
      (1 - x * (1 - w)) =
      x * (1 - w) * (1 - x * (1 - w)) / (x * (1 - x) * (1 - w) ^ 2 + w) := by
    field_simp
    ring
  have hM : x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w) +
      (x * (1 - w)) ^ 2 * (1 - x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w)) =
      x * (1 - w) ^ 2 * (1 - x * (1 - w)) / (x * (1 - x) * (1 - w) ^ 2 + w) := by
    field_simp
    ring
  simp only [i9A1Map]
  rw [hE, hM]
  have ha' : 1 - (1 - w) * x ≠ 0 := by rw [mul_comm]; exact ha.ne'
  field_simp

theorem log_one_sub_mul_i9A1Dens {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    Real.log (1 - z.2) * i9A1Dens z = -3 * (|(i9A1Deriv z).det| • i9A2ThU (i9A1Map z)) := by
  rw [i9A1Dens_eq hz, i9A2_u_eq hz, i9A2ThU, smul_eq_mul, smul_eq_mul]
  ring

/-- `p ≤ M / E ≤ 1` on the square. -/
theorem i9A2_M_div_E_mem {p s : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    p ≤ (p + s ^ 2 * (1 - p)) / (s + p * (1 - s)) ∧
      (p + s ^ 2 * (1 - p)) / (s + p * (1 - s)) ≤ 1 := by
  have hE := i9A1_E_pos hp ⟨hs.1.le, hs.2.le⟩
  have hq : 0 < 1 - p := by linarith [hp.2]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hE]
    nlinarith [mul_pos hp.1 hs.1, mul_pos (mul_pos hs.1 hs.1) hq, hs.2, hp.2,
      mul_pos (mul_pos hp.1 hq) (by linarith [hs.2] : (0 : ℝ) < 1 - s)]
  · rw [div_le_one hE]
    nlinarith [mul_pos (mul_pos hs.1 hq) (by linarith [hs.2] : (0 : ℝ) < 1 - s)]

/-- An integrable `p`-weight times `k` is integrable on the square. -/
theorem integrableOn_i9A1k_mul {φ : ℝ → ℝ} (hc : ContinuousOn φ (Ioo 0 1))
    (h0 : ∀ p ∈ Ioo (0 : ℝ) 1, 0 ≤ φ p) (hK : IntegrableOn (fun p => i9A1K p * φ p) (Ioo 0 1)) :
    IntegrableOn (fun q : ℝ × ℝ => i9A1k q.2 q.1 * φ q.1) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hk : ContinuousOn (fun q : ℝ × ℝ => i9A1k q.2 q.1) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    unfold i9A1k
    refine continuousOn_const.add (ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq => ?_)
    exact (pow_pos (i9A1_E_pos hq.1 ⟨hq.2.1.le, hq.2.2.le⟩) 2).ne'
  have hcont := hk.mul (hc.comp continuousOn_fst fun q hq => hq.1)
  have hm : AEStronglyMeasurable (fun q : ℝ × ℝ => i9A1k q.2 q.1 * φ q.1)
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    hcont.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hm
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, integrable_prod_iff hm]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    have : IntegrableOn (fun s => i9A1k s p) (Icc 0 1) := (continuousOn_i9A1k hp).integrableOn_Icc
    exact (this.mono_set Ioo_subset_Icc_self).mul_const (φ p)
  · refine hK.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    have e : ∀ s ∈ Ioo (0 : ℝ) 1, ‖i9A1k (p, s).2 (p, s).1 * φ (p, s).1‖ = i9A1k s p * φ p :=
      fun s _ => Real.norm_of_nonneg (mul_nonneg (i9A1k_nonneg hp) (h0 p hp))
    rw [setIntegral_congr_fun measurableSet_Ioo e, integral_mul_const,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_i9A1k hp]

theorem continuousOn_i9A1K : ContinuousOn i9A1K (Ioo 0 1) := by
  have hl : ContinuousOn Real.log (Ioo 0 1) :=
    Real.continuousOn_log.mono fun p hp => ne_of_gt hp.1
  unfold i9A1K
  refine (continuousOn_const.div (by fun_prop) fun p hp => ?_).add
    ((continuousOn_const.mul continuousOn_id |>.mul hl).div (by fun_prop) fun p hp => ?_)
  · linarith [hp.2]
  · have : (0 : ℝ) < 1 - p := by linarith [hp.2]
    positivity

theorem integrableOn_i9A2ThU : IntegrableOn i9A2ThU (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hl : ContinuousOn Real.log (Ioo 0 1) :=
    Real.continuousOn_log.mono fun p hp => ne_of_gt hp.1
  have hφ : ContinuousOn (fun p => i9A1g p * -Real.log p) (Ioo 0 1) :=
    continuousOn_i9A1g.mul hl.neg
  have hK : IntegrableOn (fun p => i9A1K p * (i9A1g p * -Real.log p)) (Ioo 0 1) := by
    refine integrableOn_of_abs_le_log_poly (C := 2 * 8)
      (continuousOn_i9A1K.mul hφ) fun p hp => ?_
    have hK0 := i9A1K_nonneg hp
    have hK2 := i9A1K_le_two hp
    have hg0 := i9A1g_nonneg hp
    have hg := i9A1g_le hp
    have hlp : Real.log p ≤ 0 := Real.log_nonpos hp.1.le hp.2.le
    have habs : |Real.log p| = -Real.log p := abs_of_nonpos hlp
    rw [abs_of_nonneg (mul_nonneg hK0 (mul_nonneg hg0 (by linarith))), ← habs]
    set L := |Real.log p| with hL
    have hL0 : 0 ≤ L := abs_nonneg _
    have hsq : Real.log p ^ 2 = L ^ 2 := (sq_abs _).symm
    rw [hsq] at hg
    have h1 : i9A1K p * (i9A1g p * L) ≤ 2 * ((4 + 3 * L + L ^ 2) * L) :=
      mul_le_mul hK2 (mul_le_mul_of_nonneg_right hg hL0) (by positivity) (by norm_num)
    have h2 : L ≤ 1 + L ^ 3 := by nlinarith [sq_nonneg (L - 1), sq_nonneg L]
    have h3 : L ^ 2 ≤ 1 + L ^ 3 := by nlinarith [sq_nonneg (L - 1), sq_nonneg L]
    nlinarith
  have hB := integrableOn_i9A1k_mul hφ (fun p hp => mul_nonneg (i9A1g_nonneg hp)
    (by linarith [Real.log_nonpos hp.1.le hp.2.le])) hK
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hc : ContinuousOn i9A2ThU (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    refine ContinuousOn.mul ?_ continuousOn_i9A1G
    refine ContinuousOn.log (ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq => ?_)
      fun q hq => ?_
    · exact (i9A1_E_pos hq.1 ⟨hq.2.1.le, hq.2.2.le⟩).ne'
    · exact (lt_of_lt_of_le hq.1.1 (i9A2_M_div_E_mem hq.1 hq.2).1).ne'
  refine hB.mono' (hc.aestronglyMeasurable hS) ?_
  refine (ae_restrict_iff' hS).2 (ae_of_all _ fun q hq => ?_)
  obtain ⟨hm1, hm2⟩ := i9A2_M_div_E_mem hq.1 hq.2
  have hpos := lt_of_lt_of_le hq.1.1 hm1
  rw [Real.norm_eq_abs, i9A2ThU, i9A1G, abs_mul,
    abs_of_nonneg (mul_nonneg (i9A1k_nonneg hq.1) (i9A1g_nonneg hq.1)),
    abs_of_nonpos (Real.log_nonpos hpos.le hm2)]
  have hlog : -Real.log ((q.1 + q.2 ^ 2 * (1 - q.1)) / (q.2 + q.1 * (1 - q.2))) ≤
      -Real.log q.1 := by
    linarith [Real.log_le_log hq.1.1 hm1]
  have h0 := mul_nonneg (i9A1k_nonneg (s := q.2) hq.1) (i9A1g_nonneg hq.1)
  calc _ ≤ -Real.log q.1 * (i9A1k q.2 q.1 * i9A1g q.1) := mul_le_mul_of_nonneg_right hlog h0
    _ = _ := by ring

/-! ### The change of variables -/

/-- `j(p) = K ((-6 log p - 6 log (1 - p)) g + h) - 3 g K_b`, the `s`-integral of `Θ`. -/
noncomputable def i9A2j (p : ℝ) : ℝ :=
  i9A1K p * ((-6 * Real.log p - 6 * Real.log (1 - p)) * i9A1g p + i9A2h p) -
    3 * i9A1g p * i9A2Kb p

theorem i9A2_hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem i9A2_hd : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
    HasFDerivWithinAt i9A1Map (i9A1Deriv z) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) z :=
  fun _ hz => (hasFDerivAt_i9A1Map hz).hasFDerivWithinAt

/-- **The `K_u` density is integrable**: `log (1 - w) · i9A1Dens` on the `(x, w)`-square. -/
theorem integrableOn_log_one_sub_mul_i9A1Dens :
    IntegrableOn (fun z : ℝ × ℝ => Real.log (1 - z.2) * i9A1Dens z)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hI : IntegrableOn (fun z => |(i9A1Deriv z).det| • i9A2ThU (i9A1Map z))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume i9A2_hS i9A2_hd
      injOn_i9A1Map i9A2ThU).1 (by rw [image_i9A1Map]; exact integrableOn_i9A2ThU)
  exact IntegrableOn.congr_fun (hI.const_mul (-3))
    (fun z hz => (log_one_sub_mul_i9A1Dens hz).symm) i9A2_hS

theorem i9A2DensP_eq_add (z : ℝ × ℝ) :
    i9A2DensP z = i9A2Dens z.1 z.2 + 4 * (Real.log (1 - z.2) * i9A1Dens z) := by
  rw [i9A2DensP]; ring

theorem integrableOn_i9A2DensP : IntegrableOn i9A2DensP (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have h := integrableOn_i9A2Dens.add (integrableOn_log_one_sub_mul_i9A1Dens.const_mul 4)
  refine h.congr_fun (fun _ _ => ?_) i9A2_hS
  rw [i9A2DensP_eq_add]
  rfl

theorem integrableOn_i9A2Theta : IntegrableOn i9A2Theta (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [← image_i9A1Map, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume i9A2_hS
    i9A2_hd injOn_i9A1Map]
  exact integrableOn_i9A2DensP.congr_fun (fun z hz => i9A2DensP_eq hz) i9A2_hS

theorem integral_i9A2DensP :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9A2DensP z =
      ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9A2Theta q := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [setIntegral_congr_fun i9A2_hS fun z hz => i9A2DensP_eq hz,
    ← integral_image_eq_integral_abs_det_fderiv_smul volume i9A2_hS i9A2_hd injOn_i9A1Map,
    image_i9A1Map]

/-! ### The `s`-integral -/

theorem i9A2Theta_slice (p s : ℝ) :
    i9A2Theta (p, s) = ((-6 * Real.log p - 6 * Real.log (1 - p)) * i9A1g p + i9A2h p) *
        i9A1k s p +
      (-3 * i9A1g p) * (i9A1k s p * Real.log (s * (1 - s) / (s + p * (1 - s)))) := by
  simp only [i9A2Theta]
  ring

theorem integrableOn_and_integral_i9A2Theta_slice {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun s => i9A2Theta (p, s)) (Ioo 0 1) ∧
      ∫ s in Ioo (0 : ℝ) 1, i9A2Theta (p, s) = i9A2j p := by
  obtain ⟨hb, hbv⟩ := intervalIntegrable_and_integral_i9A2kLogB hp
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hb
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hbv
  have hk : IntegrableOn (fun s => i9A1k s p) (Ioo 0 1) :=
    (continuousOn_i9A1k hp).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hkv : ∫ s in Ioo (0 : ℝ) 1, i9A1k s p = i9A1K p := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_i9A1k hp]
  have h1 := hk.const_mul ((-6 * Real.log p - 6 * Real.log (1 - p)) * i9A1g p + i9A2h p)
  have h2 := hb.const_mul (-3 * i9A1g p)
  have e : (fun s => i9A2Theta (p, s)) = fun s =>
      ((-6 * Real.log p - 6 * Real.log (1 - p)) * i9A1g p + i9A2h p) * i9A1k s p +
        (-3 * i9A1g p) * (i9A1k s p * Real.log (s * (1 - s) / (s + p * (1 - s)))) :=
    funext fun s => i9A2Theta_slice p s
  rw [e]
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul, hkv, hbv, i9A2j]
  ring

/-- **Fubini for `Θ`**: `j` is integrable and `∫∫ Θ = ∫₀¹ j`. -/
theorem integrableOn_and_integral_i9A2j :
    IntegrableOn i9A2j (Ioo 0 1) ∧
      ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9A2Theta q = ∫ p in Ioo (0 : ℝ) 1, i9A2j p := by
  have hI := integrableOn_i9A2Theta
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hI
  have hae : (fun p => ∫ s in Ioo (0 : ℝ) 1, i9A2Theta (p, s)) =ᵐ[volume.restrict (Ioo 0 1)]
      i9A2j := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    exact (integrableOn_and_integral_i9A2Theta_slice hp).2
  refine ⟨hI.integral_prod_left.congr hae, ?_⟩
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hI]
  exact integral_congr_ae hae

/-- **`∫∫ i9A2Dens = ∫₀¹ j - 4 ∫∫ log (1 - w) · i9A1Dens`.** -/
theorem integral_i9A2Dens_split :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9A2Dens z.1 z.2 =
      (∫ p in Ioo (0 : ℝ) 1, i9A2j p) -
        4 * ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, Real.log (1 - z.2) * i9A1Dens z := by
  have hU := integrableOn_log_one_sub_mul_i9A1Dens
  have e : (fun z : ℝ × ℝ => i9A2Dens z.1 z.2) =
      fun z => i9A2DensP z - 4 * (Real.log (1 - z.2) * i9A1Dens z) :=
    funext fun z => by rw [i9A2DensP_eq_add]; ring
  rw [e, integral_sub integrableOn_i9A2DensP (hU.const_mul 4), integral_const_mul,
    integral_i9A2DensP, integrableOn_and_integral_i9A2j.2]

end QED.ThreeLoopD
