/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import QED.Polylog.HPLBasic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.ThreeLoopD.SetDMastersI9MThreePJ
import QED.ThreeLoopD.SetDMastersI9MInner
import QED.Polylog.ExtraIntegrals
import QED.Polylog.HPLCalculus
import QED.Polylog.HPLLowWeight
import QED.Polylog.DilogPM

/-!
# Set (d), master `I₉`: the pieces `P₆`, `P₇`, `P₉` of `M₃`

Fix `w ∈ (0, 1)`, write `u = 1 - w`, `A = w + u x`, `B = 1 - u x`, `λ = log w` and
`H(v) = H(v; w)` (harmonic polylogarithms, letters `0, 1, m = -1`). We compute

* `P₆ = ∫₀¹ log A log (1 - x) / x`,
* `P₇ = ∫₀¹ log A log x / (1 - x)`,
* `P₉ = ∫₀¹ log A log B / x`

in terms of `ζ(3)`, `ζ(2) = π²/6`, `λ` and `H(v)`.

Route: `V(w) = ∫₀¹ g(w, x) dx` is differentiated under the integral sign
(`QED.ThreeLoopD.i9M3P_hasDerivAt_integral`, with a local domination of `∂_w g`); the derivative
is a weight-two `x`-integral computed in `QED.ThreeLoopD.SetDMastersI9MThreePJ`. The HPL
candidate `T(w)` has the same derivative (`QED.Polylog.HPL.hasDerivAt_hpl_cons` and the
weight-two closed forms of `QED.Polylog.HPLLowWeight`, `QED.Polylog.DilogPM`), and `V`, `T`
have the same limit as `w → 0⁺` (dominated convergence for `V`; `H(v) → 0` for `T`), so
`V = T` on `(0, 1)`.

## Main results

* `QED.ThreeLoopD.i9M3P_P6`: `P₆ = ζ₃ - 2H(0,0,1) - H(0,1,1) - H(1,0,1) + λH(0,1) + λH(1,1)
  + ζ₂H(1)`.
* `QED.ThreeLoopD.i9M3P_P7`: `P₇ = 2ζ₃ - H(0,0,1) + H(0,1,1) + H(1,0,1) + λH(0,1) - λH(1,1)
  - λ²H(1)/2 - ζ₂H(1)`.
* `QED.ThreeLoopD.i9M3P_P9`: `P₉ = ζ₃ + 2H(0,0,1) - 4H(0,0,m) - λH(0,1) + 2λH(0,m)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### `P₆ = ∫₀¹ log A log (1 - x) / x` -/

theorem i9M3P_P6_dom {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |Real.log (w + (1 - w) * x) * Real.log (1 - x) / x| ≤
      Real.log x * Real.log (1 - x) / x := by
  have hA := i9M2_A_pos hw hx.1.le
  have ha : Real.log x ≤ Real.log (w + (1 - w) * x) :=
    Real.log_le_log hx.1 (i9M3P_le_A hw hx.2.le)
  have ha0 : Real.log (w + (1 - w) * x) ≤ 0 := Real.log_nonpos hA.le (i9M2_A_le hw hx.2.le)
  have hq : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith [hx.2]) (by linarith [hx.1])
  have h0 : 0 ≤ Real.log (w + (1 - w) * x) * Real.log (1 - x) / x :=
    div_nonneg (mul_nonneg_of_nonpos_of_nonpos ha0 hq) hx.1.le
  rw [abs_of_nonneg h0]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_right ha hq) hx.1.le

theorem i9M3P_P6_cont {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - x) / x) (Ioo 0 1) := by
  intro x hx
  have hA := (i9M2_A_pos hw hx.1.le).ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hx0 := hx.1.ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

theorem i9M3P_P6_deriv_cont {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => (1 - x) / (w + (1 - w) * x) * Real.log (1 - x) / x) (Ioo 0 1) := by
  intro x hx
  have hA := (i9M2_A_pos hw hx.1.le).ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hx0 := hx.1.ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

theorem i9M3P_P6_deriv_bound {w₀ w x : ℝ} (hw₀ : w₀ ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (w₀ / 2) ((1 + w₀) / 2)) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |(1 - x) / (w + (1 - w) * x) * Real.log (1 - x) / x| ≤ 2 / w₀ := by
  have hw' := i9M3P_mem hw₀ hw
  have hA := i9M2_A_pos hw' hx.1.le
  have hwA := i9M3P_w_le_A hw' hx.1.le
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hN : (1 - x) * -Real.log (1 - x) ≤ x := by
    have := i9M3P_neg_log_le h1x
    rw [show (1 - (1 - x)) / (1 - x) = x / (1 - x) by ring, le_div_iff₀ h1x] at this
    linarith
  have hN0 : 0 ≤ (1 - x) * -Real.log (1 - x) :=
    mul_nonneg h1x.le (neg_nonneg.2 (Real.log_nonpos h1x.le (by linarith [hx.1])))
  have e : (1 - x) / (w + (1 - w) * x) * Real.log (1 - x) / x =
      -((1 - x) * -Real.log (1 - x) / ((w + (1 - w) * x) * x)) := by
    field_simp
  rw [e, abs_neg, abs_of_nonneg (div_nonneg hN0 (mul_pos hA hx.1).le),
    div_le_div_iff₀ (mul_pos hA hx.1) hw₀.1]
  nlinarith [mul_le_mul_of_nonneg_right hN hw₀.1.le, hw.1, mul_le_mul_of_nonneg_left hwA hx.1.le]

theorem i9M3P_P6_hasDerivAt {w₀ : ℝ} (hw₀ : w₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) / x)
      ((-(π ^ 2 / 6) + Li₂ (1 - w₀) / (1 - w₀)) / w₀) w₀ := by
  have hQ := intervalIntegrable_and_integral_log_mul_log_one_sub_div.1
  have h := i9M3P_hasDerivAt_integral (g := fun w x => Real.log (w + (1 - w) * x) *
      Real.log (1 - x) / x) (g' := fun w x => (1 - x) / (w + (1 - w) * x) * Real.log (1 - x) / x)
    (bnd := fun _ => 2 / w₀) (i9M3P_nhds hw₀)
    (fun w hw => i9M3P_P6_cont (i9M3P_mem hw₀ hw)) (i9M3P_P6_deriv_cont hw₀)
    (i9M3P_intervalIntegrable (i9M3P_P6_cont hw₀) hQ fun x hx => i9M3P_P6_dom hw₀ hx)
    intervalIntegrable_const
    (fun x hx w hw => by
      have hA := (i9M2_A_pos (i9M3P_mem hw₀ hw) hx.1.le).ne'
      exact (((i9M3P_hasDerivAt_Aw w x).log hA).mul_const _).div_const _)
    (fun x hx w hw => i9M3P_P6_deriv_bound hw₀ hw hx)
  rw [← (i9M3P_h6 hw₀).2]
  exact h.2

theorem i9M3P_P6_tendsto :
    Tendsto (fun w => ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) / x)
      (𝓝[>] 0) (𝓝 zeta3) := by
  have hQ := intervalIntegrable_and_integral_log_mul_log_one_sub_div
  rw [← hQ.2]
  refine i9M3P_tendsto_integral (fun w hw => i9M3P_P6_cont hw) hQ.1
    (fun w hw x hx => i9M3P_P6_dom hw hx) (fun x hx => ?_)
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hc : ContinuousAt (fun w => Real.log (w + (1 - w) * x) * Real.log (1 - x) / x) 0 :=
    (((by fun_prop : ContinuousAt (fun w : ℝ => w + (1 - w) * x) 0).log
      (by simp; exact hx.1.ne')).mul_const _).div_const _
  simpa using i9M2_tendsto_of_continuousAt (s := Ioi 0) hc

theorem i9M3P_P6_T_hasDerivAt {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => zeta3 - 2 * hpl [zero, zero, one] w - hpl [zero, one, one] w -
        hpl [one, zero, one] w + Real.log w * hpl [zero, one] w +
        Real.log w * hpl [one, one] w + π ^ 2 / 6 * hpl [one] w)
      ((-(π ^ 2 / 6) + Li₂ (1 - w) / (1 - w)) / w) w := by
  have hw0 := hw.1.ne'
  have hu : 1 - w ≠ 0 := by linarith [hw.2]
  have hl := Real.hasDerivAt_log hw0
  have h := (((((((hasDerivAt_const w zeta3).sub
    ((hasDerivAt_hpl_cons zero [zero, one] hw).const_mul 2)).sub
    (hasDerivAt_hpl_cons zero [one, one] hw)).sub (hasDerivAt_hpl_cons one [zero, one] hw)).add
    (hl.mul (hasDerivAt_hpl_cons zero [one] hw))).add
    (hl.mul (hasDerivAt_hpl_cons one [one] hw))).add
    ((hasDerivAt_hpl_cons one [] hw).const_mul (π ^ 2 / 6)))
  refine h.congr_deriv ?_
  simp only [kernel_zero, kernel_one, hpl_nil]
  rw [hpl_zero_one hw, hpl_one hw, hpl_one_one hw, ← Li_two, Li_two_one_sub' hw]
  field_simp
  ring

theorem i9M3P_P6_T_tendsto :
    Tendsto (fun w => zeta3 - 2 * hpl [zero, zero, one] w - hpl [zero, one, one] w -
        hpl [one, zero, one] w + Real.log w * hpl [zero, one] w +
        Real.log w * hpl [one, one] w + π ^ 2 / 6 * hpl [one] w) (𝓝[>] 0) (𝓝 zeta3) := by
  have h := (((((((tendsto_const_nhds (x := zeta3)).sub
    ((tendsto_hpl_zero (w := [zero, zero, one]) (by simp)).const_mul 2)).sub
    (tendsto_hpl_zero (w := [zero, one, one]) (by simp))).sub
    (tendsto_hpl_zero (w := [one, zero, one]) (by simp))).add
    (i9M3P_tendsto_log_mul (v := [zero, one]) (by simp))).add
    (i9M3P_tendsto_log_mul (v := [one, one]) (by simp))).add
    ((tendsto_hpl_zero (w := [one]) (by simp)).const_mul (π ^ 2 / 6)))
  simpa using h

/-- **`P₆ = ∫₀¹ log A log (1 - x) / x`** in harmonic polylogarithms of `w`. -/
theorem i9M3P_P6 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - x) / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) / x =
        zeta3 - 2 * hpl [zero, zero, one] w - hpl [zero, one, one] w - hpl [one, zero, one] w +
          Real.log w * hpl [zero, one] w + Real.log w * hpl [one, one] w +
          π ^ 2 / 6 * hpl [one] w :=
  ⟨i9M3P_intervalIntegrable (i9M3P_P6_cont hw)
      intervalIntegrable_and_integral_log_mul_log_one_sub_div.1 fun _ hx => i9M3P_P6_dom hw hx,
    i9M3P_eq_of_deriv (fun _ hw => i9M3P_P6_hasDerivAt hw) (fun _ hw => i9M3P_P6_T_hasDerivAt hw)
      i9M3P_P6_tendsto i9M3P_P6_T_tendsto w hw⟩

/-! ### `P₇ = ∫₀¹ log A log x / (1 - x)` -/

theorem i9M3P_P7_dom {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |Real.log (w + (1 - w) * x) * Real.log x / (1 - x)| ≤ Real.log x ^ 2 / (1 - x) := by
  have hA := i9M2_A_pos hw hx.1.le
  have ha : Real.log x ≤ Real.log (w + (1 - w) * x) :=
    Real.log_le_log hx.1 (i9M3P_le_A hw hx.2.le)
  have ha0 : Real.log (w + (1 - w) * x) ≤ 0 := Real.log_nonpos hA.le (i9M2_A_le hw hx.2.le)
  have hp : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have h0 : 0 ≤ Real.log (w + (1 - w) * x) * Real.log x / (1 - x) :=
    div_nonneg (mul_nonneg_of_nonpos_of_nonpos ha0 hp) h1x.le
  rw [abs_of_nonneg h0, sq]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_right ha hp) h1x.le

theorem i9M3P_P7_cont {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Real.log (w + (1 - w) * x) * Real.log x / (1 - x)) (Ioo 0 1) := by
  intro x hx
  have hA := (i9M2_A_pos hw hx.1.le).ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hx0 := hx.1.ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

theorem i9M3P_P7_deriv_cont {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Real.log x / (w + (1 - w) * x)) (Ioo 0 1) := by
  intro x hx
  have hA := (i9M2_A_pos hw hx.1.le).ne'
  have hx0 := hx.1.ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

theorem i9M3P_P7_deriv_bound {w₀ w x : ℝ} (hw₀ : w₀ ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (w₀ / 2) ((1 + w₀) / 2)) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |Real.log x / (w + (1 - w) * x)| ≤ 2 / w₀ * -Real.log x := by
  have hw' := i9M3P_mem hw₀ hw
  have hA := i9M2_A_pos hw' hx.1.le
  have hwA := i9M3P_w_le_A hw' hx.1.le
  have hp : 0 ≤ -Real.log x := neg_nonneg.2 (Real.log_nonpos hx.1.le hx.2.le)
  rw [abs_div, abs_of_pos hA, abs_of_nonpos (by linarith), div_le_iff₀ hA]
  have : 1 ≤ 2 / w₀ * (w + (1 - w) * x) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hw₀.1]; linarith [hw.1]
  nlinarith

theorem i9M3P_P7_hasDerivAt {w₀ : ℝ} (hw₀ : w₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log x / (1 - x))
      (-(Li₂ (1 - w₀) + Real.log w₀ ^ 2 / 2) / (1 - w₀)) w₀ := by
  have hR := i9M3P_logSq_div.1
  have h := i9M3P_hasDerivAt_integral (g := fun w x => Real.log (w + (1 - w) * x) *
      Real.log x / (1 - x)) (g' := fun w x => Real.log x / (w + (1 - w) * x))
    (bnd := fun x => 2 / w₀ * -Real.log x) (i9M3P_nhds hw₀)
    (fun w hw => i9M3P_P7_cont (i9M3P_mem hw₀ hw)) (i9M3P_P7_deriv_cont hw₀)
    (i9M3P_intervalIntegrable (i9M3P_P7_cont hw₀) hR fun x hx => i9M3P_P7_dom hw₀ hx)
    (intervalIntegral.intervalIntegrable_log'.neg.const_mul _)
    (fun x hx w hw => by
      have hA := (i9M2_A_pos (i9M3P_mem hw₀ hw) hx.1.le).ne'
      have h1 : 1 - x ≠ 0 := by linarith [hx.2]
      refine ((((i9M3P_hasDerivAt_Aw w x).log hA).mul_const _).div_const _).congr_deriv ?_
      field_simp)
    (fun x hx w hw => i9M3P_P7_deriv_bound hw₀ hw hx)
  rw [← (i9M3P_logX_divA hw₀).2]
  exact h.2

theorem i9M3P_P7_tendsto :
    Tendsto (fun w => ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log x / (1 - x))
      (𝓝[>] 0) (𝓝 (2 * zeta3)) := by
  rw [← i9M3P_logSq_div.2]
  refine i9M3P_tendsto_integral (fun w hw => i9M3P_P7_cont hw) i9M3P_logSq_div.1
    (fun w hw x hx => i9M3P_P7_dom hw hx) (fun x hx => ?_)
  have hc : ContinuousAt (fun w => Real.log (w + (1 - w) * x) * Real.log x / (1 - x)) 0 :=
    (((by fun_prop : ContinuousAt (fun w : ℝ => w + (1 - w) * x) 0).log
      (by simp; exact hx.1.ne')).mul_const _).div_const _
  have := i9M2_tendsto_of_continuousAt (s := Ioi 0) hc
  convert this using 2
  simp [sq]

theorem i9M3P_P7_T_hasDerivAt {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => 2 * zeta3 - hpl [zero, zero, one] w + hpl [zero, one, one] w +
        hpl [one, zero, one] w + Real.log w * hpl [zero, one] w -
        Real.log w * hpl [one, one] w - Real.log w ^ 2 * hpl [one] w / 2 -
        π ^ 2 / 6 * hpl [one] w)
      (-(Li₂ (1 - w) + Real.log w ^ 2 / 2) / (1 - w)) w := by
  have hw0 := hw.1.ne'
  have hu : 1 - w ≠ 0 := by linarith [hw.2]
  have hl := Real.hasDerivAt_log hw0
  have h := ((((((((hasDerivAt_const w (2 * zeta3)).sub
    (hasDerivAt_hpl_cons zero [zero, one] hw)).add
    (hasDerivAt_hpl_cons zero [one, one] hw)).add (hasDerivAt_hpl_cons one [zero, one] hw)).add
    (hl.mul (hasDerivAt_hpl_cons zero [one] hw))).sub
    (hl.mul (hasDerivAt_hpl_cons one [one] hw))).sub
    (((hl.pow 2).mul (hasDerivAt_hpl_cons one [] hw)).div_const 2)).sub
    ((hasDerivAt_hpl_cons one [] hw).const_mul (π ^ 2 / 6)))
  refine h.congr_deriv ?_
  simp only [kernel_zero, kernel_one, hpl_nil, Pi.pow_apply]
  rw [hpl_zero_one hw, hpl_one hw, hpl_one_one hw, ← Li_two, Li_two_one_sub' hw]
  field_simp
  ring

theorem i9M3P_P7_T_tendsto :
    Tendsto (fun w => 2 * zeta3 - hpl [zero, zero, one] w + hpl [zero, one, one] w +
        hpl [one, zero, one] w + Real.log w * hpl [zero, one] w -
        Real.log w * hpl [one, one] w - Real.log w ^ 2 * hpl [one] w / 2 -
        π ^ 2 / 6 * hpl [one] w) (𝓝[>] 0) (𝓝 (2 * zeta3)) := by
  have h := ((((((((tendsto_const_nhds (x := 2 * zeta3)).sub
    (tendsto_hpl_zero (w := [zero, zero, one]) (by simp))).add
    (tendsto_hpl_zero (w := [zero, one, one]) (by simp))).add
    (tendsto_hpl_zero (w := [one, zero, one]) (by simp))).add
    (i9M3P_tendsto_log_mul (v := [zero, one]) (by simp))).sub
    (i9M3P_tendsto_log_mul (v := [one, one]) (by simp))).sub
    ((i9M3P_tendsto_log_sq_mul (v := [one]) (by simp)).div_const 2)).sub
    ((tendsto_hpl_zero (w := [one]) (by simp)).const_mul (π ^ 2 / 6)))
  simpa using h

/-- **`P₇ = ∫₀¹ log A log x / (1 - x)`** in harmonic polylogarithms of `w`. -/
theorem i9M3P_P7 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log x / (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log x / (1 - x) =
        2 * zeta3 - hpl [zero, zero, one] w + hpl [zero, one, one] w + hpl [one, zero, one] w +
          Real.log w * hpl [zero, one] w - Real.log w * hpl [one, one] w -
          Real.log w ^ 2 * hpl [one] w / 2 - π ^ 2 / 6 * hpl [one] w :=
  ⟨i9M3P_intervalIntegrable (i9M3P_P7_cont hw) i9M3P_logSq_div.1
      fun _ hx => i9M3P_P7_dom hw hx,
    i9M3P_eq_of_deriv (fun _ hw => i9M3P_P7_hasDerivAt hw) (fun _ hw => i9M3P_P7_T_hasDerivAt hw)
      i9M3P_P7_tendsto i9M3P_P7_T_tendsto w hw⟩

/-! ### `P₉ = ∫₀¹ log A log B / x` -/

theorem i9M3P_P9_dom {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / x| ≤
      Real.log x * Real.log (1 - x) / x := by
  have hA := i9M2_A_pos hw hx.1.le
  have hB := i9M2_B_pos hw hx.2.le
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have ha : Real.log x ≤ Real.log (w + (1 - w) * x) :=
    Real.log_le_log hx.1 (i9M3P_le_A hw hx.2.le)
  have hb : Real.log (1 - x) ≤ Real.log (1 - (1 - w) * x) :=
    Real.log_le_log h1x (i9M3P_le_B hw hx.1.le)
  have ha0 : Real.log (w + (1 - w) * x) ≤ 0 := Real.log_nonpos hA.le (i9M2_A_le hw hx.2.le)
  have hb0 : Real.log (1 - (1 - w) * x) ≤ 0 := Real.log_nonpos hB.le (i9M2_B_le hw hx.1.le)
  have hp : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
  have h0 : 0 ≤ Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / x :=
    div_nonneg (mul_nonneg_of_nonpos_of_nonpos ha0 hb0) hx.1.le
  rw [abs_of_nonneg h0]
  refine div_le_div_of_nonneg_right ?_ hx.1.le
  calc Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x)
      ≤ Real.log x * Real.log (1 - (1 - w) * x) := mul_le_mul_of_nonpos_right ha hb0
    _ ≤ Real.log x * Real.log (1 - x) := mul_le_mul_of_nonpos_left hb hp

theorem i9M3P_P9_cont {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / x)
      (Ioo 0 1) := by
  intro x hx
  have hA := (i9M2_A_pos hw hx.1.le).ne'
  have hB := (i9M2_B_pos hw hx.2.le).ne'
  have hx0 := hx.1.ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

theorem i9M3P_P9_deriv_cont {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => ((1 - x) / (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) +
        Real.log (w + (1 - w) * x) * (x / (1 - (1 - w) * x))) / x) (Ioo 0 1) := by
  intro x hx
  have hA := (i9M2_A_pos hw hx.1.le).ne'
  have hB := (i9M2_B_pos hw hx.2.le).ne'
  have hx0 := hx.1.ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

theorem i9M3P_P9_deriv_bound {w₀ w x : ℝ} (hw₀ : w₀ ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (w₀ / 2) ((1 + w₀) / 2)) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |((1 - x) / (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) +
        Real.log (w + (1 - w) * x) * (x / (1 - (1 - w) * x))) / x| ≤
      2 / w₀ + 2 * -Real.log (w₀ / 2) / w₀ := by
  have hw' := i9M3P_mem hw₀ hw
  have hx0 := hx.1
  have hA := i9M2_A_pos hw' hx.1.le
  have hB := i9M2_B_pos hw' hx.2.le
  have hwA := i9M3P_w_le_A hw' hx.1.le
  have hwB := i9M3P_w_le_B hw' hx.2.le
  have hBx := i9M3P_le_B hw' hx.1.le
  have hw2 : 0 < w₀ / 2 := by linarith [hw₀.1]
  have e : ((1 - x) / (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) +
        Real.log (w + (1 - w) * x) * (x / (1 - (1 - w) * x))) / x =
      -((1 - x) * -Real.log (1 - (1 - w) * x) / ((w + (1 - w) * x) * x)) +
        -(-Real.log (w + (1 - w) * x) / (1 - (1 - w) * x)) := by
    field_simp
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the `log B` term
    have hb := i9M3P_neg_log_le hB
    rw [show 1 - (1 - (1 - w) * x) = (1 - w) * x by ring, le_div_iff₀ hB] at hb
    have hb0 : 0 ≤ -Real.log (1 - (1 - w) * x) :=
      neg_nonneg.2 (Real.log_nonpos hB.le (i9M2_B_le hw' hx.1.le))
    have hN : (1 - x) * -Real.log (1 - (1 - w) * x) ≤ x := by
      nlinarith [mul_le_mul_of_nonneg_right hBx hb0, hw'.1, hx.2]
    have hN0 : 0 ≤ (1 - x) * -Real.log (1 - (1 - w) * x) :=
      mul_nonneg (by linarith [hx.2]) hb0
    rw [abs_neg, abs_of_nonneg (div_nonneg hN0 (mul_pos hA hx0).le),
      div_le_div_iff₀ (mul_pos hA hx0) hw₀.1]
    nlinarith [mul_le_mul_of_nonneg_right hN hw₀.1.le, hw.1,
      mul_le_mul_of_nonneg_left hwA hx0.le]
  · -- the `log A` term
    have ha0 : 0 ≤ -Real.log (w + (1 - w) * x) :=
      neg_nonneg.2 (Real.log_nonpos hA.le (i9M2_A_le hw' hx.2.le))
    have ha : -Real.log (w + (1 - w) * x) ≤ -Real.log (w₀ / 2) := by
      have := Real.log_le_log hw2 ((le_of_lt hw.1).trans hwA)
      linarith
    have hL : 0 ≤ -Real.log (w₀ / 2) :=
      neg_nonneg.2 (Real.log_nonpos hw2.le (by linarith [hw₀.2]))
    rw [abs_neg, abs_of_nonneg (div_nonneg ha0 hB.le), div_le_div_iff₀ hB hw₀.1]
    nlinarith [mul_le_mul_of_nonneg_right ha hw₀.1.le, hw.1,
      mul_le_mul_of_nonneg_left hwB hL]

theorem i9M3P_P9_hasDerivAt {w₀ : ℝ} (hw₀ : w₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => ∫ x in (0 : ℝ)..1,
        Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / x)
      ((-Li₂ (1 - w₀) + Li₂ (1 / (1 + w₀)) - Li₂ (w₀ / (1 + w₀)) +
          Real.log w₀ * Real.log (1 + w₀)) / w₀) w₀ := by
  have hQ := intervalIntegrable_and_integral_log_mul_log_one_sub_div.1
  have h := i9M3P_hasDerivAt_integral (g := fun w x => Real.log (w + (1 - w) * x) *
      Real.log (1 - (1 - w) * x) / x)
    (g' := fun w x => ((1 - x) / (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) +
        Real.log (w + (1 - w) * x) * (x / (1 - (1 - w) * x))) / x)
    (bnd := fun _ => 2 / w₀ + 2 * -Real.log (w₀ / 2) / w₀) (i9M3P_nhds hw₀)
    (fun w hw => i9M3P_P9_cont (i9M3P_mem hw₀ hw)) (i9M3P_P9_deriv_cont hw₀)
    (i9M3P_intervalIntegrable (i9M3P_P9_cont hw₀) hQ fun x hx => i9M3P_P9_dom hw₀ hx)
    intervalIntegrable_const
    (fun x hx w hw => by
      have hA := (i9M2_A_pos (i9M3P_mem hw₀ hw) hx.1.le).ne'
      have hB := (i9M2_B_pos (i9M3P_mem hw₀ hw) hx.2.le).ne'
      exact ((((i9M3P_hasDerivAt_Aw w x).log hA).mul
        ((i9M3P_hasDerivAt_Bw w x).log hB)).div_const _))
    (fun x hx w hw => i9M3P_P9_deriv_bound hw₀ hw hx)
  rw [← (i9M3P_h9 hw₀).2]
  exact h.2

theorem i9M3P_P9_tendsto :
    Tendsto (fun w => ∫ x in (0 : ℝ)..1,
        Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / x) (𝓝[>] 0) (𝓝 zeta3) := by
  have hQ := intervalIntegrable_and_integral_log_mul_log_one_sub_div
  rw [← hQ.2]
  refine i9M3P_tendsto_integral (fun w hw => i9M3P_P9_cont hw) hQ.1
    (fun w hw x hx => i9M3P_P9_dom hw hx) (fun x hx => ?_)
  have hc : ContinuousAt (fun w => Real.log (w + (1 - w) * x) *
      Real.log (1 - (1 - w) * x) / x) 0 :=
    (((by fun_prop : ContinuousAt (fun w : ℝ => w + (1 - w) * x) 0).log
      (by simp; exact hx.1.ne')).mul
      ((by fun_prop : ContinuousAt (fun w : ℝ => 1 - (1 - w) * x) 0).log
      (by simp; linarith [hx.2]))).div_const _
  simpa using i9M2_tendsto_of_continuousAt (s := Ioi 0) hc

theorem i9M3P_P9_T_hasDerivAt {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => zeta3 + 2 * hpl [zero, zero, one] w - 4 * hpl [zero, zero, negOne] w -
        Real.log w * hpl [zero, one] w + 2 * (Real.log w * hpl [zero, negOne] w))
      ((-Li₂ (1 - w) + Li₂ (1 / (1 + w)) - Li₂ (w / (1 + w)) +
          Real.log w * Real.log (1 + w)) / w) w := by
  have hw0 := hw.1.ne'
  have hu : 1 - w ≠ 0 := by linarith [hw.2]
  have hp : 1 + w ≠ 0 := by linarith [hw.1]
  have hl := Real.hasDerivAt_log hw0
  have h := (((((hasDerivAt_const w zeta3).add
    ((hasDerivAt_hpl_cons zero [zero, one] hw).const_mul 2)).sub
    ((hasDerivAt_hpl_cons zero [zero, negOne] hw).const_mul 4)).sub
    (hl.mul (hasDerivAt_hpl_cons zero [one] hw))).add
    ((hl.mul (hasDerivAt_hpl_cons zero [negOne] hw)).const_mul 2))
  refine h.congr_deriv ?_
  simp only [kernel_zero]
  rw [hpl_zero_one hw, hpl_one hw, hpl_zero_negOne hw, hpl_negOne hw, ← Li_two,
    Li_two_one_sub' hw, Li_two_inv_one_add hw, Li_two_div_one_add hw]
  field_simp
  ring

theorem i9M3P_P9_T_tendsto :
    Tendsto (fun w => zeta3 + 2 * hpl [zero, zero, one] w - 4 * hpl [zero, zero, negOne] w -
        Real.log w * hpl [zero, one] w + 2 * (Real.log w * hpl [zero, negOne] w))
      (𝓝[>] 0) (𝓝 zeta3) := by
  have h := (((((tendsto_const_nhds (x := zeta3)).add
    ((tendsto_hpl_zero (w := [zero, zero, one]) (by simp)).const_mul 2)).sub
    ((tendsto_hpl_zero (w := [zero, zero, negOne]) (by simp)).const_mul 4)).sub
    (i9M3P_tendsto_log_mul (v := [zero, one]) (by simp))).add
    ((i9M3P_tendsto_log_mul (v := [zero, negOne]) (by simp)).const_mul 2))
  simpa using h

/-- **`P₉ = ∫₀¹ log A log B / x`** in harmonic polylogarithms of `w`. -/
theorem i9M3P_P9 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / x)
        volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / x =
        zeta3 + 2 * hpl [zero, zero, one] w - 4 * hpl [zero, zero, negOne] w -
          Real.log w * hpl [zero, one] w + 2 * (Real.log w * hpl [zero, negOne] w) :=
  ⟨i9M3P_intervalIntegrable (i9M3P_P9_cont hw)
      intervalIntegrable_and_integral_log_mul_log_one_sub_div.1 fun _ hx => i9M3P_P9_dom hw hx,
    i9M3P_eq_of_deriv (fun _ hw => i9M3P_P9_hasDerivAt hw) (fun _ hw => i9M3P_P9_T_hasDerivAt hw)
      i9M3P_P9_tendsto i9M3P_P9_T_tendsto w hw⟩

end QED.ThreeLoopD
