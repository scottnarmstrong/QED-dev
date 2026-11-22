/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA2Th
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₉`: the `K_u` integral as a one-dimensional integral

The last input of the expansion of `Rem` is `K = ∫∫ log (1 - w) · i9A1Dens` over the
`(x, w)`-square (`QED.ThreeLoopD.hasTruncLaurent_i9Rem_of_Ku`). Write `c = x (1 - x)`,
`P₀ = c (1 - w)²`, `P₁ = P₀ + w` and `p = P₀ / P₁`. At fixed `x` the `w`-derivative of
`i9A1Dens` is free of dilogarithms:

  `∂_w i9A1Dens = 3 (1 - w²) / (2 w²) · log² p`

(the terms linear in `log p` cancel identically). Integrating by parts in `w` against
`log (1 - w) = -F'(w)`, `F(w) = w + (1 - w) log (1 - w)`, whose boundary terms vanish, and
exchanging the order of integration gives

  `K = ∫₀¹ F(w) · 3 (1 - w²) / (2 w²) · (∫₀¹ log² p dx) dw`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i9A1Dens_w`: the `w`-derivative of `i9A1Dens`.
* `QED.ThreeLoopD.integral_log_one_sub_mul_i9A1Dens_eq`: `K` as the iterated integral above.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- `p = P₀ / P₁` in the variables `(x, w)`. -/
noncomputable def i9KuP (x w : ℝ) : ℝ := x * (1 - x) * (1 - w) ^ 2 / i9A1P (x, w)

/-- `w + (1 - w) log (1 - w)`, minus the antiderivative of `log (1 - w)` vanishing at `0`. -/
noncomputable def i9KuF (w : ℝ) : ℝ := w + (1 - w) * Real.log (1 - w)

/-- The `w`-derivative of `i9A1Dens` at fixed `x`. -/
noncomputable def i9KuD' (x w : ℝ) : ℝ := 3 * (1 - w ^ 2) / (2 * w ^ 2) * Real.log (i9KuP x w) ^ 2

theorem i9Ku_P1_pos {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 < x * (1 - x) * (1 - w) ^ 2 + w := by
  have : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have := hw.1
  positivity

/-- `i9A1Dens` at fixed `x`, in a form adapted to differentiation in `w`. -/
theorem i9A1Dens_eq_ku {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    i9A1Dens (x, w) = -3 / (x * (1 - x)) * (π ^ 2 / 6 - Li₂ (w / (x * (1 - x) * (1 - w) ^ 2 + w)))
      - 3 * (1 - w) ^ 2 / (2 * w) * (Real.log (x * (1 - x) * (1 - w) ^ 2 + w) -
        Real.log (x * (1 - x)) - 2 * Real.log (1 - w)) ^ 2 := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hP := i9Ku_P1_pos hx hw
  have hw0 := hw.1
  simp only [i9A1Dens, i9Poly, mul_one, mul_zero, add_zero]
  rw [Real.log_div hP.ne' (by positivity), Real.log_mul hc.ne' (by positivity), Real.log_pow]
  generalize Li₂ (w / (x * (1 - x) * (1 - w) ^ 2 + w)) = L
  generalize Real.log (x * (1 - x) * (1 - w) ^ 2 + w) = a
  generalize Real.log (x * (1 - x)) = b
  generalize Real.log (1 - w) = d
  generalize x * (1 - x) = c at hc ⊢
  field_simp
  push_cast
  ring

theorem hasDerivAt_i9A1Dens_w {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => i9A1Dens (x, w)) (i9KuD' x w) w := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hP := i9Ku_P1_pos hx hw
  have hw0 := hw.1
  set c := x * (1 - x) with hc_def
  -- the pieces
  have dP : HasDerivAt (fun w => c * (1 - w) ^ 2 + w) (c * (2 * (1 - w) * (-1)) + 1) w := by
    convert ((((hasDerivAt_id' w).const_sub 1).pow 2).const_mul c).add (hasDerivAt_id' w)
      using 1
    simp
  have dq : HasDerivAt (fun w => w / (c * (1 - w) ^ 2 + w))
      ((1 * (c * (1 - w) ^ 2 + w) - w * (c * (2 * (1 - w) * (-1)) + 1)) /
        (c * (1 - w) ^ 2 + w) ^ 2) w := (hasDerivAt_id w).div dP hP.ne'
  have hq0 : 0 < w / (c * (1 - w) ^ 2 + w) := div_pos hw0 hP
  have hq1 : w / (c * (1 - w) ^ 2 + w) < 1 := by
    rw [div_lt_one hP]; nlinarith [mul_pos hc (pow_pos hu 2)]
  have dL := (hasDerivAt_Li₂ (x := w / (c * (1 - w) ^ 2 + w))
    (by rw [abs_of_pos hq0]; exact hq1) hq0.ne').comp w dq
  have dl : HasDerivAt (fun w => Real.log (c * (1 - w) ^ 2 + w) - Real.log c -
      2 * Real.log (1 - w))
      ((c * (2 * (1 - w) * (-1)) + 1) / (c * (1 - w) ^ 2 + w) - 0 -
        2 * ((-1) / (1 - w))) w := by
    have h1 := dP.log hP.ne'
    have h2 := ((hasDerivAt_id' w).const_sub 1).log hu.ne'
    convert (h1.sub (hasDerivAt_const w (Real.log c))).sub (h2.const_mul 2) using 1
  have dr : HasDerivAt (fun w => 3 * (1 - w) ^ 2 / (2 * w))
      ((3 * (2 * (1 - w) * (-1)) * (2 * w) - 3 * (1 - w) ^ 2 * 2) / (2 * w) ^ 2) w := by
    have h1 := (((hasDerivAt_id' w).const_sub 1).pow 2).const_mul 3
    have h2 := (hasDerivAt_id' w).const_mul 2
    convert h1.div h2 (by positivity) using 1
    simp
  have dF := ((dL.const_sub (π ^ 2 / 6)).const_mul (-3 / c)).sub (dr.mul (dl.pow 2))
  have e1 : 1 - w / (c * (1 - w) ^ 2 + w) = c * (1 - w) ^ 2 / (c * (1 - w) ^ 2 + w) := by
    field_simp; ring
  have hlog1 : Real.log (1 - w / (c * (1 - w) ^ 2 + w)) =
      Real.log c + 2 * Real.log (1 - w) - Real.log (c * (1 - w) ^ 2 + w) := by
    rw [e1, Real.log_div (by positivity) hP.ne', Real.log_mul hc.ne' (by positivity),
      Real.log_pow]; push_cast; ring
  have hlogp : Real.log (i9KuP x w) =
      Real.log c + 2 * Real.log (1 - w) - Real.log (c * (1 - w) ^ 2 + w) := by
    rw [i9KuP, i9A1P, Real.log_div (by positivity) hP.ne', Real.log_mul hc.ne' (by positivity),
      Real.log_pow]; push_cast; ring
  refine (dF.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioo_mem_nhds hw.1 hw.2] with v hv
    exact i9A1Dens_eq_ku hx hv
  · rw [i9KuD', hlogp]
    rw [hlog1]
    simp only [Pi.pow_apply]
    norm_num
    generalize Real.log c = a
    generalize Real.log (1 - w) = b
    generalize Real.log (c * (1 - w) ^ 2 + w) = d
    field_simp
    ring

/-! ### Bounds and integrability -/

theorem i9KuF_mem {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) : 0 ≤ i9KuF w ∧ i9KuF w ≤ w ^ 2 := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have h1 := Real.log_le_sub_one_of_pos hu
  have h2 := Real.one_sub_inv_le_log_of_pos hu
  have e : (1 - w) * (1 - (1 - w)⁻¹) = -w := by field_simp; ring
  unfold i9KuF
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h2 hu.le]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hu.le]

theorem log_i9KuP_sq_le {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    Real.log (i9KuP x w) ^ 2 ≤
      3 * (Real.log x ^ 2 + Real.log (1 - x) ^ 2 + 4 * Real.log (1 - w) ^ 2) := by
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hc : 0 < x * (1 - x) := mul_pos hx.1 hx1
  have hP := i9Ku_P1_pos hx hw
  have hP1 : x * (1 - x) * (1 - w) ^ 2 + w ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (1 - w)), hw.1, hw.2]
  have hl : Real.log (i9KuP x w) = Real.log x + Real.log (1 - x) + 2 * Real.log (1 - w) -
      Real.log (x * (1 - x) * (1 - w) ^ 2 + w) := by
    rw [i9KuP, i9A1P, Real.log_div (by positivity) hP.ne', Real.log_mul hc.ne' (by positivity),
      Real.log_mul hx.1.ne' hx1.ne', Real.log_pow]; push_cast; ring
  have a := Real.log_nonpos hx.1.le hx.2.le
  have b := Real.log_nonpos hx1.le (by linarith [hx.1])
  have d := Real.log_nonpos hu.le (by linarith [hw.1])
  have e := Real.log_nonpos hP.le hP1
  have hp0 : 0 < i9KuP x w := by rw [i9KuP, i9A1P]; positivity
  have hp1 : i9KuP x w ≤ 1 := by
    rw [i9KuP, i9A1P, div_le_one hP]; linarith [hw.1]
  have f := Real.log_nonpos hp0.le hp1
  rw [hl] at f ⊢
  generalize Real.log x = A at *
  generalize Real.log (1 - x) = B at *
  generalize Real.log (1 - w) = D at *
  generalize Real.log (x * (1 - x) * (1 - w) ^ 2 + w) = E at *
  have h1 : (A + B + 2 * D - E) ^ 2 ≤ (A + B + 2 * D) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (A - B), sq_nonneg (A - 2 * D), sq_nonneg (B - 2 * D)]

theorem integrableOn_log_sq_i9Ku : IntegrableOn (fun t : ℝ => Real.log t ^ 2) (Ioo 0 1) := by
  refine integrableOn_of_abs_le_log_poly (C := 1) ?_ fun t ht => ?_
  · exact (Real.continuousOn_log.mono fun t ht => ht.1.ne').pow 2
  · rw [abs_of_nonneg (sq_nonneg _), one_mul]
    rcases le_or_gt |Real.log t| 1 with h | h
    · nlinarith [abs_nonneg (Real.log t), sq_abs (Real.log t),
        pow_nonneg (abs_nonneg (Real.log t)) 3]
    · nlinarith [sq_abs (Real.log t), abs_nonneg (Real.log t)]

theorem integrableOn_log_one_sub_sq_i9Ku :
    IntegrableOn (fun t : ℝ => Real.log (1 - t) ^ 2) (Ioo 0 1) := by
  have h := ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    integrableOn_log_sq_i9Ku).comp_sub_left 1
  rw [sub_zero, sub_self] at h
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h.symm

theorem continuousOn_i9KuFD :
    ContinuousOn (fun z : ℝ × ℝ => i9KuF z.2 * i9KuD' z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hu : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, (1 - z.2) ≠ 0 := fun z hz => by
    linarith [hz.2.2]
  refine ContinuousOn.mul ?_ ?_
  · unfold i9KuF
    exact (continuousOn_snd).add ((continuousOn_const.sub continuousOn_snd).mul
      (Real.continuousOn_log.comp (continuousOn_const.sub continuousOn_snd) hu))
  · unfold i9KuD' i9KuP i9A1P
    refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_)
      (ContinuousOn.pow (Real.continuousOn_log.comp (ContinuousOn.div (by fun_prop) (by fun_prop)
        fun z hz => (i9Ku_P1_pos hz.1 hz.2).ne') fun z hz => ?_) 2)
    · have := hz.2.1; positivity
    · have := i9Ku_P1_pos hz.1 hz.2
      have : 0 < z.1 * (1 - z.1) := mul_pos hz.1.1 (by linarith [hz.1.2])
      have : 0 < 1 - z.2 := by linarith [hz.2.2]
      exact (div_pos (by positivity) (i9Ku_P1_pos hz.1 hz.2)).ne'

theorem integrableOn_i9KuFD :
    IntegrableOn (fun z : ℝ × ℝ => i9KuF z.2 * i9KuD' z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hfin : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 1) := integrableOn_const (by simp)
  have g1 : IntegrableOn (fun z : ℝ × ℝ => Real.log z.1 ^ 2 * 1)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integrableOn_log_sq_i9Ku.mul_prod hfin
  have g2 : IntegrableOn (fun z : ℝ × ℝ => Real.log (1 - z.1) ^ 2 * 1)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integrableOn_log_one_sub_sq_i9Ku.mul_prod hfin
  have g3 : IntegrableOn (fun z : ℝ × ℝ => 1 * Real.log (1 - z.2) ^ 2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hfin.mul_prod integrableOn_log_one_sub_sq_i9Ku
  have hg := ((g1.add g2).add (g3.const_mul 4)).const_mul (9 / 2)
  refine hg.mono' (continuousOn_i9KuFD.aestronglyMeasurable hS) ?_
  refine (ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_)
  obtain ⟨hF0, hF1⟩ := i9KuF_mem hz.2
  have hL := log_i9KuP_sq_le hz.1 hz.2
  have hw := hz.2.1
  have hw1 : z.2 < 1 := hz.2.2
  have hr0 : 0 ≤ 3 * (1 - z.2 ^ 2) / (2 * z.2 ^ 2) := by
    apply div_nonneg _ (by positivity); nlinarith
  have hFr : i9KuF z.2 * (3 * (1 - z.2 ^ 2) / (2 * z.2 ^ 2)) ≤ 3 / 2 := by
    calc _ ≤ z.2 ^ 2 * (3 * (1 - z.2 ^ 2) / (2 * z.2 ^ 2)) := mul_le_mul_of_nonneg_right hF1 hr0
      _ = 3 / 2 * (1 - z.2 ^ 2) := by field_simp
      _ ≤ 3 / 2 := by nlinarith
  rw [Real.norm_eq_abs, i9KuD', ← mul_assoc, abs_of_nonneg (mul_nonneg (mul_nonneg hF0 hr0)
    (sq_nonneg _))]
  show _ ≤ 9 / 2 * ((Real.log z.1 ^ 2 * 1 + Real.log (1 - z.1) ^ 2 * 1) +
    4 * (1 * Real.log (1 - z.2) ^ 2))
  simp only [mul_one, one_mul]
  nlinarith [mul_le_mul hFr hL (sq_nonneg _) (by norm_num), mul_nonneg hF0 hr0, sq_nonneg
    (Real.log (i9KuP z.1 z.2))]

/-! ### The integration by parts in `w` at fixed `x` -/

theorem hasDerivAt_i9KuF {w : ℝ} (hw : w < 1) :
    HasDerivAt i9KuF (-Real.log (1 - w)) w := by
  have hu : 1 - w ≠ 0 := by linarith
  have h := (hasDerivAt_id' w).add (((hasDerivAt_id' w).const_sub 1).mul
    (((hasDerivAt_id' w).const_sub 1).log hu))
  convert h using 1
  · funext v; simp [i9KuF]
  · field_simp; ring

theorem continuous_i9KuF : Continuous i9KuF := by
  have := Real.continuous_mul_log.comp ((continuous_const (y := (1 : ℝ))).sub continuous_id)
  exact continuous_id.add this

/-- Bounds on the logarithm `ℓ = log (P₁ / P₀)` in `i9A1Dens_eq_ku`. -/
theorem i9Ku_ell_mem {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 ≤ Real.log (x * (1 - x) * (1 - w) ^ 2 + w) - Real.log (x * (1 - x)) - 2 * Real.log (1 - w) ∧
      Real.log (x * (1 - x) * (1 - w) ^ 2 + w) - Real.log (x * (1 - x)) -
        2 * Real.log (1 - w) ≤ w / (x * (1 - x) * (1 - w) ^ 2) := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hP := i9Ku_P1_pos hx hw
  have hP0 : 0 < x * (1 - x) * (1 - w) ^ 2 := by positivity
  have e : Real.log (x * (1 - x) * (1 - w) ^ 2 + w) - Real.log (x * (1 - x)) -
      2 * Real.log (1 - w) = Real.log ((x * (1 - x) * (1 - w) ^ 2 + w) /
        (x * (1 - x) * (1 - w) ^ 2)) := by
    rw [Real.log_div hP.ne' hP0.ne', Real.log_mul hc.ne' (by positivity), Real.log_pow]
    push_cast; ring
  rw [e]
  constructor
  · exact Real.log_nonneg (by rw [le_div_iff₀ hP0]; linarith [hw.1])
  · have := Real.log_le_sub_one_of_pos (div_pos hP hP0)
    have e2 : (x * (1 - x) * (1 - w) ^ 2 + w) / (x * (1 - x) * (1 - w) ^ 2) - 1 =
        w / (x * (1 - x) * (1 - w) ^ 2) := by rw [div_sub_one hP0.ne']; congr 1; ring
    linarith

theorem tendsto_i9KuF_mul_i9A1Dens_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun w => -i9KuF w * i9A1Dens (x, w)) (𝓝[>] 0) (𝓝 0) := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have hlim : Tendsto (fun w : ℝ => w ^ 2 * (π ^ 2 / (x * (1 - x)) + 6 / (x * (1 - x)) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun w : ℝ => w ^ 2 * (π ^ 2 / (x * (1 - x)) + 6 / (x * (1 - x)) ^ 2)) (𝓝 0)
        (𝓝 (0 ^ 2 * (π ^ 2 / (x * (1 - x)) + 6 / (x * (1 - x)) ^ 2))) :=
      ((continuous_pow 2).mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with w hw
  have hw' : w ∈ Ioo (0 : ℝ) 1 := ⟨hw.1, by linarith [hw.2]⟩
  have hu : 1 / 2 < 1 - w := by linarith [hw.2]
  obtain ⟨hF0, hF1⟩ := i9KuF_mem hw'
  obtain ⟨hl0, hl1⟩ := i9Ku_ell_mem hx hw'
  have hP := i9Ku_P1_pos hx hw'
  have hq : w / (x * (1 - x) * (1 - w) ^ 2 + w) ∈ Icc (-1 : ℝ) 1 :=
    ⟨by have := div_pos hw'.1 hP; linarith, by rw [div_le_one hP]; nlinarith [hw'.1]⟩
  have hL := abs_Li₂_le_of_mem hq
  rw [i9A1Dens_eq_ku hx hw']
  generalize Li₂ (w / (x * (1 - x) * (1 - w) ^ 2 + w)) = L at hL
  generalize Real.log (x * (1 - x) * (1 - w) ^ 2 + w) - Real.log (x * (1 - x)) -
    2 * Real.log (1 - w) = l at hl0 hl1 ⊢
  generalize x * (1 - x) = c at hc hl1 ⊢
  have hu2 : 1 / 4 < (1 - w) ^ 2 := by nlinarith
  have hl2 : l ^ 2 ≤ (w / (c * (1 - w) ^ 2)) ^ 2 := pow_le_pow_left₀ hl0 hl1 2
  have hD : |-3 / c * (π ^ 2 / 6 - L) - 3 * (1 - w) ^ 2 / (2 * w) * l ^ 2| ≤
      π ^ 2 / c + 6 / c ^ 2 := by
    have h1 : |-3 / c * (π ^ 2 / 6 - L)| ≤ π ^ 2 / c := by
      rw [abs_mul, abs_div, abs_neg, abs_of_pos hc, div_mul_eq_mul_div,
        div_le_div_iff_of_pos_right hc]
      have := abs_sub (π ^ 2 / 6) L
      rw [abs_of_pos (by positivity : (0 : ℝ) < π ^ 2 / 6)] at this
      norm_num at this ⊢
      nlinarith
    have h2 : 0 ≤ 3 * (1 - w) ^ 2 / (2 * w) * l ^ 2 := by
      have := hw'.1; positivity
    have h3 : 3 * (1 - w) ^ 2 / (2 * w) * l ^ 2 ≤ 6 / c ^ 2 := by
      calc _ ≤ 3 * (1 - w) ^ 2 / (2 * w) * (w / (c * (1 - w) ^ 2)) ^ 2 :=
            mul_le_mul_of_nonneg_left hl2 (by have := hw'.1; positivity)
        _ = 3 * w / (2 * c ^ 2 * (1 - w) ^ 2) := by
            have := hw'.1; have : 0 < 1 - w := by linarith
            field_simp
        _ ≤ 6 / c ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hw.2, pow_pos hc 2]
    calc _ ≤ |-3 / c * (π ^ 2 / 6 - L)| + |3 * (1 - w) ^ 2 / (2 * w) * l ^ 2| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg h2]; linarith
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hF0]
  exact mul_le_mul hF1 hD (abs_nonneg _) (sq_nonneg _)

theorem tendsto_i9KuF_mul_i9A1Dens_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun w => -i9KuF w * i9A1Dens (x, w)) (𝓝[<] 1) (𝓝 0) := by
  have hc : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  set c := x * (1 - x) with hc_def
  -- the continuous extension of `i9A1Dens (x, ·)` through `w = 1`
  set D : ℝ → ℝ := fun w => -3 / c * (π ^ 2 / 6 - Li₂ (w / (c * (1 - w) ^ 2 + w))) -
    3 / (2 * w) * ((1 - w) * (Real.log (c * (1 - w) ^ 2 + w) - Real.log c) -
      2 * ((1 - w) * Real.log (1 - w))) ^ 2 with hD
  have hq : Tendsto (fun w : ℝ => w / (c * (1 - w) ^ 2 + w)) (𝓝[<] 1) (𝓝[Icc (-1) 1] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : ContinuousAt (fun w : ℝ => w / (c * (1 - w) ^ 2 + w)) 1 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      have h1 := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
      simpa using h1
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with w hw
      have hP := i9Ku_P1_pos hx hw
      exact ⟨by have := div_pos hw.1 hP; linarith, by rw [div_le_one hP]; nlinarith [hw.1]⟩
  have hLi : Tendsto (fun w : ℝ => Li₂ (w / (c * (1 - w) ^ 2 + w))) (𝓝[<] 1) (𝓝 (π ^ 2 / 6)) := by
    rw [← Li₂_one]
    exact (continuousOn_Li₂ 1 ⟨by norm_num, le_rfl⟩).tendsto.comp hq
  have hml : Tendsto (fun w : ℝ => (1 - w) * Real.log (1 - w)) (𝓝[<] 1) (𝓝 0) := by
    have : Continuous fun w : ℝ => (1 - w) * Real.log (1 - w) :=
      Real.continuous_mul_log.comp ((continuous_const (y := (1 : ℝ))).sub continuous_id)
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlP : Tendsto (fun w : ℝ => (1 - w) * (Real.log (c * (1 - w) ^ 2 + w) - Real.log c))
      (𝓝[<] 1) (𝓝 0) := by
    have : ContinuousAt (fun w : ℝ => (1 - w) * (Real.log (c * (1 - w) ^ 2 + w) - Real.log c)) 1 :=
      ContinuousAt.mul (by fun_prop) (ContinuousAt.sub (ContinuousAt.log (by fun_prop)
        (by norm_num)) continuousAt_const)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hw2 : Tendsto (fun w : ℝ => 3 / (2 * w)) (𝓝[<] 1) (𝓝 (3 / (2 * 1))) :=
    ((continuousAt_const.div (by fun_prop) (by norm_num)).tendsto).mono_left nhdsWithin_le_nhds
  have hDl : Tendsto D (𝓝[<] 1) (𝓝 0) := by
    have := ((hLi.const_sub (π ^ 2 / 6)).const_mul (-3 / c)).sub
      (hw2.mul ((hlP.sub (hml.const_mul 2)).pow 2))
    simpa [hD] using this
  have hF : Tendsto i9KuF (𝓝[<] 1) (𝓝 (i9KuF 1)) :=
    continuous_i9KuF.tendsto 1 |>.mono_left nhdsWithin_le_nhds
  have := (hF.neg).mul hDl
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with w hw
  rw [i9A1Dens_eq_ku hx hw, ← hc_def]
  simp only [hD]
  congr 1
  have : (0 : ℝ) < w := hw.1
  field_simp

/-- **Integration by parts in `w` at fixed `x`.** -/
theorem integral_log_one_sub_mul_i9A1Dens_slice {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hA : IntegrableOn (fun w => Real.log (1 - w) * i9A1Dens (x, w)) (Ioo 0 1))
    (hB : IntegrableOn (fun w => i9KuF w * i9KuD' x w) (Ioo 0 1)) :
    ∫ w in Ioo (0 : ℝ) 1, Real.log (1 - w) * i9A1Dens (x, w) =
      ∫ w in Ioo (0 : ℝ) 1, i9KuF w * i9KuD' x w := by
  have hderiv : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun w => -i9KuF w * i9A1Dens (x, w))
      (Real.log (1 - w) * i9A1Dens (x, w) + -(i9KuF w * i9KuD' x w)) w := by
    intro w hw
    convert ((hasDerivAt_i9KuF hw.2).neg).mul (hasDerivAt_i9A1Dens_w hx hw) using 1
    simp only [Pi.neg_apply]
    ring
  have hB' : IntegrableOn (fun w => -(i9KuF w * i9KuD' x w)) (Ioo 0 1) := hB.neg
  have hint : IntervalIntegrable (fun w => Real.log (1 - w) * i9A1Dens (x, w) +
      -(i9KuF w * i9KuD' x w)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 (hA.add hB')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hderiv hint
    (tendsto_i9KuF_mul_i9A1Dens_zero hx) (tendsto_i9KuF_mul_i9A1Dens_one hx)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    integral_add hA hB', integral_neg] at h
  linarith

/-- **`∫∫ log (1 - w) · i9A1Dens = ∫∫ F(w) · ∂_w i9A1Dens`.** -/
theorem integral_log_one_sub_mul_i9A1Dens_eq_FD :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, Real.log (1 - z.2) * i9A1Dens z =
      ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9KuF z.2 * i9KuD' z.1 z.2 := by
  have hA := integrableOn_log_one_sub_mul_i9A1Dens
  have hB := integrableOn_i9KuFD
  rw [IntegrableOn, Measure.volume_eq_prod] at hA hB
  rw [Measure.volume_eq_prod, setIntegral_prod _ hA, setIntegral_prod _ hB]
  rw [← Measure.prod_restrict] at hA hB
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hA.prod_right_ae,
    (ae_restrict_iff' measurableSet_Ioo).1 hB.prod_right_ae] with x hxA hxB hx
  exact integral_log_one_sub_mul_i9A1Dens_slice hx (hxA hx) (hxB hx)

/-- **The `K_u` integral as a `w`-integral of `∫₀¹ log² p dx`.** -/
theorem integral_log_one_sub_mul_i9A1Dens_eq :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, Real.log (1 - z.2) * i9A1Dens z =
      ∫ w in Ioo (0 : ℝ) 1, i9KuF w * (3 * (1 - w ^ 2) / (2 * w ^ 2)) *
        ∫ x in Ioo (0 : ℝ) 1, Real.log (i9KuP x w) ^ 2 := by
  have hB := integrableOn_i9KuFD
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hB
  rw [integral_log_one_sub_mul_i9A1Dens_eq_FD, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_symm _ hB]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [i9KuD']
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

end QED.ThreeLoopD
