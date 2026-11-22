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
# Set (d), master `I₉`: the piece `P₈` of `M₃`

Fix `w ∈ (0, 1)`, write `u = 1 - w`, `A = w + u x`, `B = 1 - u x`, `λ = log w` and
`H(v) = H(v; w)` (harmonic polylogarithms, letters `0, 1, m = -1`). We compute
`P₈ = ∫₀¹ u log A log x / B` in terms of `ζ(3)`, `ζ(2) = π²/6`, `λ` and `H(v)`.
Differentiating under the integral sign gives `∫₀¹ ∂_w g`, which is turned into the weight-two
integral `∫₀¹ (u log x/(A B) + log A / B)` by an integration by parts
(`QED.ThreeLoopD.i9M3P_P8_parts`, boundary term `x log x log A / B`).

Route: `V(w) = ∫₀¹ g(w, x) dx` is differentiated under the integral sign
(`QED.ThreeLoopD.i9M3P_hasDerivAt_integral`, with a local domination of `∂_w g`); the derivative
is a weight-two `x`-integral computed in `QED.ThreeLoopD.SetDMastersI9MThreePJ`. The HPL
candidate `T(w)` has the same derivative (`QED.Polylog.HPL.hasDerivAt_hpl_cons` and the
weight-two closed forms of `QED.Polylog.HPLLowWeight`, `QED.Polylog.DilogPM`), and `V`, `T`
have the same limit as `w → 0⁺` (dominated convergence for `V`; `H(v) → 0` for `T`), so
`V = T` on `(0, 1)`.

## Main results

* `QED.ThreeLoopD.i9M3P_P8`: `P₈ = 2ζ₃ - ζ₂H(1) - 2ζ₂H(m) - H(0,0,m) + 2H(0,1,m) + 2H(0,m,1)
  + 2H(1,0,m) + 2H(m,0,1) + λH(0,m) - 2λH(1,m) - 2λH(m,1) - λ²H(m)/2`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### `P₈ = ∫₀¹ (1 - w) log A log x / B` -/

theorem i9M3P_P8_dom {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |(1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (1 - (1 - w) * x)| ≤
      Real.log x ^ 2 / (1 - x) := by
  have hA := i9M2_A_pos hw hx.1.le
  have hB := i9M2_B_pos hw hx.2.le
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hu : 0 < 1 - w := by linarith [hw.2]
  have ha : Real.log x ≤ Real.log (w + (1 - w) * x) :=
    Real.log_le_log hx.1 (i9M3P_le_A hw hx.2.le)
  have ha0 : Real.log (w + (1 - w) * x) ≤ 0 := Real.log_nonpos hA.le (i9M2_A_le hw hx.2.le)
  have hp : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
  have hap : 0 ≤ Real.log (w + (1 - w) * x) * Real.log x := mul_nonneg_of_nonpos_of_nonpos ha0 hp
  have hap2 : Real.log (w + (1 - w) * x) * Real.log x ≤ Real.log x ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonpos_right ha hp
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hu.le hap) hB.le)]
  calc (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (1 - (1 - w) * x)
      ≤ Real.log (w + (1 - w) * x) * Real.log x / (1 - (1 - w) * x) := by
        refine div_le_div_of_nonneg_right ?_ hB.le
        nlinarith [hw.1]
    _ ≤ Real.log (w + (1 - w) * x) * Real.log x / (1 - x) :=
        div_le_div_of_nonneg_left hap h1x (i9M3P_le_B hw hx.1.le)
    _ ≤ Real.log x ^ 2 / (1 - x) := div_le_div_of_nonneg_right hap2 h1x.le

theorem i9M3P_P8_cont {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) /
      (1 - (1 - w) * x)) (Ioo 0 1) := by
  intro x hx
  have hA := (i9M2_A_pos hw hx.1.le).ne'
  have hB := (i9M2_B_pos hw hx.2.le).ne'
  have hx0 := hx.1.ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

/-- The `w`-derivative of the integrand of `P₈`. -/
noncomputable def i9M3P_g8' (w x : ℝ) : ℝ :=
  -(Real.log (w + (1 - w) * x) * Real.log x) / (1 - (1 - w) * x) +
    (1 - w) * ((1 - x) / (w + (1 - w) * x) * Real.log x) / (1 - (1 - w) * x) -
    (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) * x / (1 - (1 - w) * x) ^ 2

theorem i9M3P_P8_deriv_cont {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (i9M3P_g8' w) (Ioo 0 1) := by
  intro x hx
  have hA := (i9M2_A_pos hw hx.1.le).ne'
  have hB := (i9M2_B_pos hw hx.2.le).ne'
  have hx0 := hx.1.ne'
  have hB2 : (1 - (1 - w) * x) ^ 2 ≠ 0 := pow_ne_zero 2 hB
  unfold i9M3P_g8'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

theorem i9M3P_P8_hasDerivAt_w {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) /
      (1 - (1 - w) * x)) (i9M3P_g8' w x) w := by
  have hA := (i9M2_A_pos hw hx.1.le).ne'
  have hB := (i9M2_B_pos hw hx.2.le).ne'
  have h := (((hasDerivAt_id w).const_sub 1).mul
    (((i9M3P_hasDerivAt_Aw w x).log hA).mul_const (Real.log x))).div
    (i9M3P_hasDerivAt_Bw w x) hB
  refine h.congr_deriv ?_
  unfold i9M3P_g8'
  simp only [id, Pi.mul_apply]
  field_simp

theorem i9M3P_P8_deriv_bound {w₀ w x : ℝ} (hw₀ : w₀ ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (w₀ / 2) ((1 + w₀) / 2)) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |i9M3P_g8' w x| ≤
      (-Real.log (w₀ / 2) * (2 / w₀) + 2 / w₀ * (2 / w₀) + -Real.log (w₀ / 2) * (2 / w₀) ^ 2) *
        -Real.log x := by
  have hw' := i9M3P_mem hw₀ hw
  have hx0 := hx.1
  have hA := i9M2_A_pos hw' hx.1.le
  have hB := i9M2_B_pos hw' hx.2.le
  have hw2 : 0 < w₀ / 2 := by linarith [hw₀.1]
  have hu0 : 0 ≤ 1 - w := by linarith [hw'.2]
  have hu1 : 1 - w ≤ 1 := by linarith [hw'.1]
  set L := -Real.log (w₀ / 2) with hL
  set a := -Real.log (w + (1 - w) * x) with ha_def
  set ia := 1 / (w + (1 - w) * x) with hia
  set ib := 1 / (1 - (1 - w) * x) with hib
  have hL0 : 0 ≤ L := neg_nonneg.2 (Real.log_nonpos hw2.le (by linarith [hw₀.2]))
  have ha0 : 0 ≤ a := neg_nonneg.2 (Real.log_nonpos hA.le (i9M2_A_le hw' hx.2.le))
  have haL : a ≤ L := by
    have := Real.log_le_log hw2 ((le_of_lt hw.1).trans (i9M3P_w_le_A hw' hx.1.le))
    linarith
  have hia0 : 0 ≤ ia := by positivity
  have hib0 : 0 ≤ ib := by positivity
  have hia1 : ia ≤ 2 / w₀ := by
    rw [hia, show 2 / w₀ = 1 / (w₀ / 2) by field_simp]
    exact one_div_le_one_div_of_le hw2 ((le_of_lt hw.1).trans (i9M3P_w_le_A hw' hx.1.le))
  have hib1 : ib ≤ 2 / w₀ := by
    rw [hib, show 2 / w₀ = 1 / (w₀ / 2) by field_simp]
    exact one_div_le_one_div_of_le hw2 ((le_of_lt hw.1).trans (i9M3P_w_le_B hw' hx.2.le))
  have hp : 0 ≤ -Real.log x := neg_nonneg.2 (Real.log_nonpos hx.1.le hx.2.le)
  have e : i9M3P_g8' w x = -(-Real.log x *
      (a * ib + (1 - w) * (1 - x) * ia * ib + (1 - w) * a * x * ib ^ 2)) := by
    unfold i9M3P_g8'
    rw [ha_def, hia, hib]
    field_simp
    ring
  have h1x0 : 0 ≤ 1 - x := by linarith [hx.2]
  have h1x1 : 1 - x ≤ 1 := by linarith [hx.1]
  have hK0 : 0 ≤ a * ib + (1 - w) * (1 - x) * ia * ib + (1 - w) * a * x * ib ^ 2 :=
    add_nonneg (add_nonneg (mul_nonneg ha0 hib0) (mul_nonneg (mul_nonneg (mul_nonneg hu0 h1x0)
      hia0) hib0)) (mul_nonneg (mul_nonneg (mul_nonneg hu0 ha0) hx0.le) (pow_nonneg hib0 2))
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg hp hK0), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hp
  have h2w : 0 ≤ 2 / w₀ := div_nonneg (by norm_num) hw₀.1.le
  have k1 : a * ib ≤ L * (2 / w₀) := mul_le_mul haL hib1 hib0 hL0
  have k2 : (1 - w) * (1 - x) * ia * ib ≤ 1 * 1 * (2 / w₀) * (2 / w₀) :=
    mul_le_mul (mul_le_mul (mul_le_mul hu1 h1x1 h1x0 zero_le_one) hia1 hia0
      (by norm_num)) hib1 hib0 (by rw [one_mul, one_mul]; exact h2w)
  have k3 : (1 - w) * a * x * ib ^ 2 ≤ 1 * L * 1 * (2 / w₀) ^ 2 :=
    mul_le_mul (mul_le_mul (mul_le_mul hu1 haL ha0 zero_le_one) hx.2.le hx0.le
      (by positivity)) (pow_le_pow_left₀ hib0 hib1 2) (by positivity) (by positivity)
  nlinarith

/-- Integration by parts: `∫₀¹ ∂_w (integrand of P₈) = ∫₀¹ ((1 - w) log x/(A B) + log A / B)`
(the boundary term `x log x log A / B` vanishes at both ends). -/
theorem i9M3P_P8_parts {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1)
    (hint : IntervalIntegrable (i9M3P_g8' w) volume 0 1) :
    ∫ x in (0 : ℝ)..1, i9M3P_g8' w x =
      ∫ x in (0 : ℝ)..1, ((1 - w) * Real.log x / ((w + (1 - w) * x) * (1 - (1 - w) * x)) +
        Real.log (w + (1 - w) * x) / (1 - (1 - w) * x)) := by
  have hh := (i9M3P_h8 hw).1
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun x => -(x * Real.log x * (Real.log (w + (1 - w) * x) / (1 - (1 - w) * x))))
      (i9M3P_g8' w x - ((1 - w) * Real.log x / ((w + (1 - w) * x) * (1 - (1 - w) * x)) +
        Real.log (w + (1 - w) * x) / (1 - (1 - w) * x))) x := by
    intro x hx
    have hA := (i9M2_A_pos hw hx.1.le).ne'
    have hB := (i9M2_B_pos hw hx.2.le).ne'
    have hx0 := hx.1.ne'
    have h1 := i9M2_hasDerivAt_A w x
    have h := (((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).mul
      ((h1.log hA).div (i9M2_hasDerivAt_B w x) hB)).neg
    refine h.congr_deriv ?_
    unfold i9M3P_g8'
    simp only [id, Pi.mul_apply, Pi.div_apply]
    field_simp
    ring
  have hc : ∀ y ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun x => Real.log (w + (1 - w) * x) / (1 - (1 - w) * x)) y := by
    intro y hy
    have hA := (i9M2_A_pos hw hy.1).ne'
    have hB := (i9M2_B_pos hw hy.2).ne'
    fun_prop (disch := assumption)
  have h0 : Tendsto (fun x => -(x * Real.log x * (Real.log (w + (1 - w) * x) /
      (1 - (1 - w) * x)))) (𝓝[>] 0) (𝓝 (-(0 * (Real.log (w + (1 - w) * 0) /
      (1 - (1 - w) * 0))))) :=
    (tendsto_mul_log_zero.mul (i9M2_tendsto_of_continuousAt (hc 0 ⟨le_rfl, zero_le_one⟩))).neg
  have h1 : Tendsto (fun x => -(x * Real.log x * (Real.log (w + (1 - w) * x) /
      (1 - (1 - w) * x)))) (𝓝[<] 1) (𝓝 (-(1 * Real.log 1 * (Real.log (w + (1 - w) * 1) /
      (1 - (1 - w) * 1))))) :=
    ((i9M2_tendsto_of_continuousAt (f := fun x => x * Real.log x)
      (continuousAt_id.mul (Real.continuousAt_log one_ne_zero))).mul
      (i9M2_tendsto_of_continuousAt (hc 1 ⟨zero_le_one, le_rfl⟩))).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hd
    (hint.sub hh) h0 h1
  rw [intervalIntegral.integral_sub hint hh] at h
  simp only [Real.log_one, mul_zero, zero_mul, neg_zero, sub_zero] at h
  linarith

theorem i9M3P_P8_hasDerivAt {w₀ : ℝ} (hw₀ : w₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => ∫ x in (0 : ℝ)..1,
        (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (1 - (1 - w) * x))
      ((-2 * Li₂ (1 - w₀) - Real.log w₀ ^ 2 / 2) / (1 + w₀) +
        (-Li₂ (1 / (1 + w₀)) + Li₂ (w₀ / (1 + w₀)) - Real.log w₀ * Real.log (1 + w₀)) /
          (1 - w₀)) w₀ := by
  have hR := i9M3P_logSq_div.1
  have h := i9M3P_hasDerivAt_integral (g := fun w x => (1 - w) *
      (Real.log (w + (1 - w) * x) * Real.log x) / (1 - (1 - w) * x)) (g' := i9M3P_g8')
    (bnd := fun x => (-Real.log (w₀ / 2) * (2 / w₀) + 2 / w₀ * (2 / w₀) +
      -Real.log (w₀ / 2) * (2 / w₀) ^ 2) * -Real.log x) (i9M3P_nhds hw₀)
    (fun w hw => i9M3P_P8_cont (i9M3P_mem hw₀ hw)) (i9M3P_P8_deriv_cont hw₀)
    (i9M3P_intervalIntegrable (i9M3P_P8_cont hw₀) hR fun x hx => i9M3P_P8_dom hw₀ hx)
    (intervalIntegral.intervalIntegrable_log'.neg.const_mul _)
    (fun x hx w hw => i9M3P_P8_hasDerivAt_w (i9M3P_mem hw₀ hw) hx)
    (fun x hx w hw => i9M3P_P8_deriv_bound hw₀ hw hx)
  rw [← (i9M3P_h8 hw₀).2, ← i9M3P_P8_parts hw₀ h.1]
  exact h.2

theorem i9M3P_P8_tendsto :
    Tendsto (fun w => ∫ x in (0 : ℝ)..1,
        (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (1 - (1 - w) * x))
      (𝓝[>] 0) (𝓝 (2 * zeta3)) := by
  rw [← i9M3P_logSq_div.2]
  refine i9M3P_tendsto_integral (fun w hw => i9M3P_P8_cont hw) i9M3P_logSq_div.1
    (fun w hw x hx => i9M3P_P8_dom hw hx) (fun x hx => ?_)
  have hc : ContinuousAt (fun w => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) /
      (1 - (1 - w) * x)) 0 :=
    ((continuousAt_const.sub continuousAt_id).mul
      (((by fun_prop : ContinuousAt (fun w : ℝ => w + (1 - w) * x) 0).log
      (by simp; exact hx.1.ne')).mul_const _)).div (by fun_prop)
      (by simp; linarith [hx.2])
  have := i9M2_tendsto_of_continuousAt (s := Ioi 0) hc
  convert this using 2
  simp [sq]

/-- The harmonic-polylogarithm form of `P₈`. -/
theorem i9M3P_P8_T_hasDerivAt {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => 2 * zeta3 - π ^ 2 / 6 * hpl [one] w - 2 * (π ^ 2 / 6) * hpl [negOne] w -
        hpl [zero, zero, negOne] w + 2 * hpl [zero, one, negOne] w +
        2 * hpl [zero, negOne, one] w + 2 * hpl [one, zero, negOne] w +
        2 * hpl [negOne, zero, one] w + Real.log w * hpl [zero, negOne] w -
        2 * (Real.log w * hpl [one, negOne] w) - 2 * (Real.log w * hpl [negOne, one] w) -
        Real.log w ^ 2 * hpl [negOne] w / 2)
      ((-2 * Li₂ (1 - w) - Real.log w ^ 2 / 2) / (1 + w) +
        (-Li₂ (1 / (1 + w)) + Li₂ (w / (1 + w)) - Real.log w * Real.log (1 + w)) / (1 - w)) w := by
  have hw0 := hw.1.ne'
  have hu : 1 - w ≠ 0 := by linarith [hw.2]
  have hp : 1 + w ≠ 0 := by linarith [hw.1]
  have hl := Real.hasDerivAt_log hw0
  have h := ((((((((((((hasDerivAt_const w (2 * zeta3)).sub
    ((hasDerivAt_hpl_cons one [] hw).const_mul (π ^ 2 / 6))).sub
    ((hasDerivAt_hpl_cons negOne [] hw).const_mul (2 * (π ^ 2 / 6)))).sub
    (hasDerivAt_hpl_cons zero [zero, negOne] hw)).add
    ((hasDerivAt_hpl_cons zero [one, negOne] hw).const_mul 2)).add
    ((hasDerivAt_hpl_cons zero [negOne, one] hw).const_mul 2)).add
    ((hasDerivAt_hpl_cons one [zero, negOne] hw).const_mul 2)).add
    ((hasDerivAt_hpl_cons negOne [zero, one] hw).const_mul 2)).add
    (hl.mul (hasDerivAt_hpl_cons zero [negOne] hw))).sub
    ((hl.mul (hasDerivAt_hpl_cons one [negOne] hw)).const_mul 2)).sub
    ((hl.mul (hasDerivAt_hpl_cons negOne [one] hw)).const_mul 2)).sub
    (((hl.pow 2).mul (hasDerivAt_hpl_cons negOne [] hw)).div_const 2))
  refine h.congr_deriv ?_
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, Pi.pow_apply]
  rw [hpl_zero_one hw, hpl_one hw, hpl_zero_negOne hw, hpl_negOne hw, ← Li_two,
    Li_two_one_sub' hw, Li_two_inv_one_add hw, Li_two_div_one_add hw]
  field_simp
  ring

theorem i9M3P_P8_T_tendsto :
    Tendsto (fun w => 2 * zeta3 - π ^ 2 / 6 * hpl [one] w - 2 * (π ^ 2 / 6) * hpl [negOne] w -
        hpl [zero, zero, negOne] w + 2 * hpl [zero, one, negOne] w +
        2 * hpl [zero, negOne, one] w + 2 * hpl [one, zero, negOne] w +
        2 * hpl [negOne, zero, one] w + Real.log w * hpl [zero, negOne] w -
        2 * (Real.log w * hpl [one, negOne] w) - 2 * (Real.log w * hpl [negOne, one] w) -
        Real.log w ^ 2 * hpl [negOne] w / 2) (𝓝[>] 0) (𝓝 (2 * zeta3)) := by
  have h := ((((((((((((tendsto_const_nhds (x := 2 * zeta3)).sub
    ((tendsto_hpl_zero (w := [one]) (by simp)).const_mul (π ^ 2 / 6))).sub
    ((tendsto_hpl_zero (w := [negOne]) (by simp)).const_mul (2 * (π ^ 2 / 6)))).sub
    (tendsto_hpl_zero (w := [zero, zero, negOne]) (by simp))).add
    ((tendsto_hpl_zero (w := [zero, one, negOne]) (by simp)).const_mul 2)).add
    ((tendsto_hpl_zero (w := [zero, negOne, one]) (by simp)).const_mul 2)).add
    ((tendsto_hpl_zero (w := [one, zero, negOne]) (by simp)).const_mul 2)).add
    ((tendsto_hpl_zero (w := [negOne, zero, one]) (by simp)).const_mul 2)).add
    (i9M3P_tendsto_log_mul (v := [zero, negOne]) (by simp))).sub
    ((i9M3P_tendsto_log_mul (v := [one, negOne]) (by simp)).const_mul 2)).sub
    ((i9M3P_tendsto_log_mul (v := [negOne, one]) (by simp)).const_mul 2)).sub
    ((i9M3P_tendsto_log_sq_mul (v := [negOne]) (by simp)).div_const 2))
  simpa using h

/-- **`P₈ = ∫₀¹ (1 - w) log A log x / B`** in harmonic polylogarithms of `w`. -/
theorem i9M3P_P8 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) /
        (1 - (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) /
        (1 - (1 - w) * x) =
        2 * zeta3 - π ^ 2 / 6 * hpl [one] w - 2 * (π ^ 2 / 6) * hpl [negOne] w -
          hpl [zero, zero, negOne] w + 2 * hpl [zero, one, negOne] w +
          2 * hpl [zero, negOne, one] w + 2 * hpl [one, zero, negOne] w +
          2 * hpl [negOne, zero, one] w + Real.log w * hpl [zero, negOne] w -
          2 * (Real.log w * hpl [one, negOne] w) - 2 * (Real.log w * hpl [negOne, one] w) -
          Real.log w ^ 2 * hpl [negOne] w / 2 :=
  ⟨i9M3P_intervalIntegrable (i9M3P_P8_cont hw) i9M3P_logSq_div.1
      fun _ hx => i9M3P_P8_dom hw hx,
    i9M3P_eq_of_deriv (fun _ hw => i9M3P_P8_hasDerivAt hw) (fun _ hw => i9M3P_P8_T_hasDerivAt hw)
      i9M3P_P8_tendsto i9M3P_P8_T_tendsto w hw⟩

end QED.ThreeLoopD
