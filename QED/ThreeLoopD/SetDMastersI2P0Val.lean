/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P0Lines
public import QED.Polylog.ExtraIntegrals
import QED.Polylog.Reflection
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₂`: `P(0) = 6 ζ(3)`

By `QED.ThreeLoopD.i2PInt_zero_eq_lintegral`, `P(0) = ∫₀¹ ∫₀¹ (1 - w) Ψ(A, B, C) dw dx`. In the
logarithms `l_x = log x`, `l_y = log (1 - x)`, `l_w = log w`, `l_v = log (1 - w)`,
`l_p = log (w + (1 - w) x)`, `l_q = log (w + (1 - w)(1 - x))` the integrand is linear, since
`A + C = (1 - w) x (w + (1 - w)(1 - x))`, `B + C = (1 - w)(1 - x)(w + (1 - w) x)`,
`A B + (A + B) C = w C` and `A + B = w (1 - w)`.

**`x`.** With `u t = (1 - w) t / (w + (1 - w) t)` and
`φ(t) = Li₂ t / w + Li₂ (u t) / (1 - w) - Li₂ ((1 - w) t) / (w (1 - w))
  + (log (w + (1 - w) t) - l_w)² / (2 (1 - w))` (`QED.ThreeLoopD.i2P0Phi`),
`φ'(t) = (-(1 - w) log (1 - t) + w (log (w + (1 - w) t) - l_w) + log (1 - (1 - w) t))
  / (w (1 - w) t)`, and `x ↦ φ(x) - φ(1 - x)` is an antiderivative of the integrand
(`QED.ThreeLoopD.hasDerivAt_i2P0F`). Every dilogarithm argument stays in `[0, 1]`, so `φ` is
continuous on `[0, 1]` and the `x`-integral is `2 φ(1)`, `φ(0) = 0`.

**`w`.** `2 φ(1) = (π²/3 - 2 Li₂ (1 - w)) / w + log² w / (1 - w)`; by the reflection formula
this is `2 Li₂ w / w + 2 log w log (1 - w) / w + log² w / (1 - w)`, whose integrals are
`2 ζ(3) + 2 ζ(3) + 2 ζ(3)`.

## Main results

* `QED.ThreeLoopD.i2P0_lint_x`, `QED.ThreeLoopD.i2P0_lint_w`.
* `QED.ThreeLoopD.i2PInt_zero_eq`: `P(0) = 6 ζ(3)`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- Half of the antiderivative in `x`:
`φ(t) = Li₂ t / w + Li₂ (u t) / (1 - w) - Li₂ ((1 - w) t) / (w (1 - w))
  + (log (w + (1 - w) t) - log w)² / (2 (1 - w))`, `u t = (1 - w) t / (w + (1 - w) t)`. -/
noncomputable def i2P0Phi (w t : ℝ) : ℝ :=
  Li₂ t / w + Li₂ ((1 - w) * t / (w + (1 - w) * t)) / (1 - w) -
    Li₂ ((1 - w) * t) / (w * (1 - w)) + (log (w + (1 - w) * t) - log w) ^ 2 / (2 * (1 - w))

theorem hasDerivAt_i2P0Phi {w t : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i2P0Phi w)
      ((-(1 - w) * log (1 - t) + w * (log (w + (1 - w) * t) - log w) +
        log (1 - (1 - w) * t)) / (w * (1 - w) * t)) t := by
  obtain ⟨hw0, hw1⟩ := hw
  obtain ⟨ht0, ht1⟩ := ht
  have hv : 0 < 1 - w := by linarith
  have hD : 0 < w + (1 - w) * t := by positivity
  have h1 := hasDerivAt_Li₂' ⟨ht0, ht1⟩
  have hum : (1 - w) * t / (w + (1 - w) * t) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one hD).2 (by linarith)⟩
  have hu : HasDerivAt (fun t => (1 - w) * t / (w + (1 - w) * t))
      ((1 - w) * w / (w + (1 - w) * t) ^ 2) t := by
    have := ((hasDerivAt_id t).const_mul (1 - w)).div
      (((hasDerivAt_id t).const_mul (1 - w)).const_add w) hD.ne'
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    ring
  have h2 := (hasDerivAt_Li₂' hum).comp t hu
  have hvm : (1 - w) * t ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have h3 := (hasDerivAt_Li₂' hvm).comp t ((hasDerivAt_id t).const_mul (1 - w))
  have h4 := ((((hasDerivAt_id t).const_mul (1 - w)).const_add w).log hD.ne').sub_const
    (log w) |>.pow 2
  have h := (((h1.div_const w).add (h2.div_const (1 - w))).sub
    (h3.div_const (w * (1 - w)))).add (h4.div_const (2 * (1 - w)))
  refine h.congr_deriv ?_
  have e : 1 - (1 - w) * t / (w + (1 - w) * t) = w / (w + (1 - w) * t) := by
    field_simp
    ring
  rw [e, log_div hw0.ne' hD.ne']
  simp only [id, mul_one]
  field_simp
  ring

/-- **The `x`-antiderivative**: `d/dx (φ(x) - φ(1 - x)) = (1 - w) Ψ(A, B, C)`. -/
theorem hasDerivAt_i2P0F {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => i2P0Phi w x - i2P0Phi w (1 - x)) (i2P0Q x w) x := by
  have hx' : 1 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h := (hasDerivAt_i2P0Phi hw hx).sub
    ((hasDerivAt_i2P0Phi hw hx').comp x ((hasDerivAt_id x).const_sub 1))
  refine h.congr_deriv ?_
  obtain ⟨hw0, hw1⟩ := hw
  obtain ⟨hx0, hx1⟩ := hx
  have hv : 0 < 1 - w := by linarith
  have hy : 0 < 1 - x := by linarith
  have hP : 0 < w + (1 - w) * x := by positivity
  have hQ : 0 < w + (1 - w) * (1 - x) := by positivity
  have e1 : log (w * (1 - w) * x + (1 - w) ^ 2 * x * (1 - x)) =
      log (1 - w) + log x + log (w + (1 - w) * (1 - x)) := by
    rw [show w * (1 - w) * x + (1 - w) ^ 2 * x * (1 - x) =
      (1 - w) * x * (w + (1 - w) * (1 - x)) by ring, log_mul (by positivity) hQ.ne',
      log_mul hv.ne' hx0.ne']
  have e2 : log (w * (1 - w) * (1 - x) + (1 - w) ^ 2 * x * (1 - x)) =
      log (1 - w) + log (1 - x) + log (w + (1 - w) * x) := by
    rw [show w * (1 - w) * (1 - x) + (1 - w) ^ 2 * x * (1 - x) =
      (1 - w) * (1 - x) * (w + (1 - w) * x) by ring, log_mul (by positivity) hP.ne',
      log_mul hv.ne' hy.ne']
  have e3 : log (w * (1 - w) * x * (w * (1 - w) * (1 - x)) +
      (w * (1 - w) * x + w * (1 - w) * (1 - x)) * ((1 - w) ^ 2 * x * (1 - x))) =
      log w + 2 * log (1 - w) + log x + log (1 - x) := by
    rw [show w * (1 - w) * x * (w * (1 - w) * (1 - x)) +
      (w * (1 - w) * x + w * (1 - w) * (1 - x)) * ((1 - w) ^ 2 * x * (1 - x)) =
      w * (1 - w) ^ 2 * x * (1 - x) by ring, log_mul (by positivity) hy.ne',
      log_mul (by positivity) hx0.ne', log_mul hw0.ne' (by positivity), log_pow]
    push_cast
    ring
  have e4 : log (w * (1 - w) * x + w * (1 - w) * (1 - x)) = log w + log (1 - w) := by
    rw [show w * (1 - w) * x + w * (1 - w) * (1 - x) = w * (1 - w) by ring,
      log_mul hw0.ne' hv.ne']
  have e5 : 1 - (1 - w) * x = w + (1 - w) * (1 - x) := by ring
  have e6 : 1 - (1 - w) * (1 - x) = w + (1 - w) * x := by ring
  simp only [i2P0Q, i2P0Psi, e1, e2, e3, e4]
  rw [e5, e6, sub_sub_cancel]
  generalize log x = Lx
  generalize log (1 - x) = Ly
  generalize log w = Lw
  generalize log (1 - w) = Lv
  generalize log (w + (1 - w) * x) = Lp
  generalize log (w + (1 - w) * (1 - x)) = Lq
  field_simp
  ring

theorem continuousOn_i2P0Phi {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (i2P0Phi w) (Icc 0 1) := by
  obtain ⟨hw0, hw1⟩ := hw
  have hD : ∀ t ∈ Icc (0 : ℝ) 1, 0 < w + (1 - w) * t := fun t ht => by
    have := ht.1
    have : 0 ≤ (1 - w) * t := mul_nonneg (by linarith) this
    linarith
  have hL := continuousOn_Li₂
  have hu : ContinuousOn (fun t : ℝ => (1 - w) * t / (w + (1 - w) * t)) (Icc 0 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => (hD t ht).ne'
  have hum : MapsTo (fun t : ℝ => (1 - w) * t / (w + (1 - w) * t)) (Icc 0 1) (Icc (-1) 1) :=
    fun t ht => by
      have h0 : 0 ≤ (1 - w) * t := mul_nonneg (by linarith) ht.1
      exact ⟨by linarith [div_nonneg h0 (hD t ht).le],
        (div_le_one (hD t ht)).2 (by linarith)⟩
  have hvm : MapsTo (fun t : ℝ => (1 - w) * t) (Icc 0 1) (Icc (-1) 1) := fun t ht =>
    ⟨by nlinarith [ht.1], by nlinarith [ht.2, ht.1]⟩
  have him : MapsTo (fun t : ℝ => t) (Icc 0 1) (Icc (-1) 1) := fun t ht =>
    ⟨by linarith [ht.1], ht.2⟩
  have hl : ContinuousOn (fun t : ℝ => log (w + (1 - w) * t)) (Icc 0 1) :=
    ContinuousOn.log (by fun_prop) fun t ht => (hD t ht).ne'
  unfold i2P0Phi
  refine ((((hL.comp continuousOn_id him).div_const w).add
    ((hL.comp hu hum).div_const (1 - w))).sub
    ((hL.comp (by fun_prop) hvm).div_const (w * (1 - w)))).add
    (((hl.sub continuousOn_const).pow 2).div_const (2 * (1 - w)))

theorem i2P0Phi_zero (w : ℝ) : i2P0Phi w 0 = 0 := by
  simp [i2P0Phi]

theorem i2P0Phi_one (w : ℝ) :
    i2P0Phi w 1 = π ^ 2 / 6 / w + Li₂ (1 - w) / (1 - w) - Li₂ (1 - w) / (w * (1 - w)) +
      log w ^ 2 / (2 * (1 - w)) := by
  simp only [i2P0Phi, mul_one, show w + (1 - w) = 1 by ring, div_one, log_one, zero_sub,
    neg_sq, Li₂_one]

/-- **The `x`-integral**: `∫₀¹ (1 - w) Ψ(A, B, C) dx = 2 φ(1)`. -/
theorem i2P0_lint_x {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (i2P0Q x w) = ENNReal.ofReal (2 * i2P0Phi w 1) := by
  have hc := continuousOn_i2P0Phi hw
  have hF : ContinuousOn (fun x => i2P0Phi w x - i2P0Phi w (1 - x)) (Icc 0 1) :=
    hc.sub (hc.comp (continuousOn_const.sub continuousOn_id) fun x hx =>
      ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have hm0 : Icc (0 : ℝ) 1 ∈ 𝓝[>] 0 :=
    mem_nhdsWithin.2 ⟨Iio 1, isOpen_Iio, by norm_num, fun y hy => ⟨le_of_lt hy.2, le_of_lt hy.1⟩⟩
  have h0 := ((hF 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin hm0).tendsto
  have h1 := ((hF 1 ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT one_pos)).tendsto
  have hnn : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ i2P0Q x w := fun x hx => by
    obtain ⟨hA, -, hB, -, hC, -⟩ := QED.ThreeLoopD.i2_lines_pos hx hw
    exact mul_nonneg (by linarith [hw.2]) (i2P0Psi_nonneg hA hB hC)
  obtain ⟨hI, hv⟩ := intervalIntegrable_and_integral_eq_of_nonneg
    (fun x hx => hasDerivAt_i2P0F hw hx) hnn h0 h1
  have hIo : IntegrableOn (fun x => i2P0Q x w) (Ioo (0 : ℝ) 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hI).mono_set
      Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hIo
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using hnn x hx),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hv]
  congr 1
  simp only [sub_self, sub_zero, i2P0Phi_zero]
  ring

/-- **The `w`-integral**: `∫₀¹ 2 φ(1) dw = 6 ζ(3)`. By the reflection formula,
`2 φ(1) = 2 Li₂ w / w + 2 log w log (1 - w) / w + log² w / (1 - w)` on `(0, 1)`. -/
theorem i2P0_lint_w :
    ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * i2P0Phi w 1) = ENNReal.ofReal (6 * zeta3) := by
  set g : ℝ → ℝ := fun x => 2 * (Li₂ x / x) + 2 * (log x * log (1 - x) / x) +
    log (1 - (1 - x)) ^ 2 / (1 - x) with hg
  have hJ1 := intervalIntegrable_and_integral_Li₂_div
  have hJ2 := intervalIntegrable_and_integral_log_mul_log_one_sub_div
  have hJ3 := intervalIntegrable_and_integral_log_one_sub_sq_div
  have hJ3' : IntervalIntegrable (fun x => log (1 - (1 - x)) ^ 2 / (1 - x)) volume 0 1 := by
    have := hJ3.1.comp_sub_left 1
    rw [sub_zero, sub_self] at this
    exact this.symm
  have hgi : IntervalIntegrable g volume 0 1 :=
    ((hJ1.1.const_mul 2).add (hJ2.1.const_mul 2)).add hJ3'
  have hgv : ∫ x in (0 : ℝ)..1, g x = 6 * zeta3 := by
    rw [hg, intervalIntegral.integral_add ((hJ1.1.const_mul 2).add (hJ2.1.const_mul 2)) hJ3',
      intervalIntegral.integral_add (hJ1.1.const_mul 2) (hJ2.1.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hJ1.2, hJ2.2,
      intervalIntegral.integral_comp_sub_left (fun x => log (1 - x) ^ 2 / x) 1, sub_self,
      sub_zero, hJ3.2]
    ring
  have heq : ∀ w ∈ Ioo (0 : ℝ) 1, 2 * i2P0Phi w 1 = g w := fun w hw => by
    have hr := Li₂_add_Li₂_one_sub hw.1.le hw.2.le
    have h0 := hw.1.ne'
    have h1 : 1 - w ≠ 0 := by linarith [hw.2]
    rw [i2P0Phi_one, hg]
    simp only [sub_sub_cancel]
    rw [show Li₂ (1 - w) = π ^ 2 / 6 - log w * log (1 - w) - Li₂ w by linarith]
    field_simp
    ring
  have hnn : ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ g w := fun w hw => by
    have h1 : 0 < 1 - w := by linarith [hw.2]
    have hl1 := log_nonpos hw.1.le hw.2.le
    have hl2 := log_nonpos h1.le (by linarith [hw.1])
    have := Li₂_nonneg hw.1.le
    simp only [hg]
    have := mul_nonneg_of_nonpos_of_nonpos hl1 hl2
    have := hw.1
    positivity
  have hIo : IntegrableOn g (Ioo (0 : ℝ) 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hgi).mono_set
      Ioo_subset_Ioc_self
  rw [setLIntegral_congr_fun measurableSet_Ioo fun w hw => by rw [heq w hw],
    ← ofReal_integral_eq_lintegral_ofReal hIo
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using hnn x hx),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hgv]

theorem measurable_i2P0Q : Measurable fun p : ℝ × ℝ => i2P0Q p.1 p.2 := by
  unfold i2P0Q i2P0Psi
  fun_prop

/-- **`P(0) = 6 ζ(3)`**, the period of the tetrahedron. -/
theorem i2PInt_zero_eq : i2PInt 0 = i2P0 := by
  have hm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (i2P0Q p.1 p.2) :=
    ENNReal.measurable_ofReal.comp measurable_i2P0Q
  rw [i2PInt_zero_eq_lintegral, lintegral_lintegral_swap hm.aemeasurable,
    setLIntegral_congr_fun measurableSet_Ioo fun w hw => i2P0_lint_x hw, i2P0_lint_w,
    ENNReal.toReal_ofReal (by positivity [zeta3_pos]), i2P0]
  push_cast
  ring

end QED.ThreeLoopD
