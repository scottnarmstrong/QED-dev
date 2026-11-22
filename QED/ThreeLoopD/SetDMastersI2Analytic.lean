/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2Wire
public import QED.ThreeLoopD.SetDMastersI3FAnalytic
public import QED.ThreeLoopD.SetDMastersI12RestWire
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Set (d), master `I₂`: the parametric integral `P` is analytic near `ε = 0`

On the domain of `QED.ThreeLoopD.i2PInt`, with `a, b, c` the three effective lines and
`A = w(1 - w)x`, `B = w(1 - w)(1 - x)`, `C = (1 - w)² x(1 - x)` (all in `(0, 1/4]`):

* `𝒰 ≤ ℱ ≤ (1 + y₄) 𝒰`, so for `s = re ε`, `|s| ≤ 1/20`,
  `|𝒰 ^ (-2 + 4ε) ℱ ^ (-3ε)| ≤ 𝒰 ^ (-2 + s) (1 + y₄) ^ (3/20)`;
* `𝒰³ ≥ (ab)(bc)(ca)`, so `𝒰 ^ (-2 + s) ≤ (a b c) ^ (-(4/3 + t))`, `t = -2s/3`;
* for `y > 0`, `0 < A ≤ 1`, `|t| ≤ 1/30`:
  `(y + A) ^ (-(4/3 + t)) ≤ y ^ (-9/10) (1 + y) ^ (-2/5) A ^ (-7/15)`
  (`QED.ThreeLoopD.i2_factor_le`).

So the integrand is dominated by the product of one-variable functions
`(x(1 - x)) ^ (-14/15) (w(1 - w)) ^ (-14/15) y₄ ^ (-9/10) (1 + y₄) ^ (-1/4)
  ∏_{y = y₇, y₈} y ^ (-9/10) (1 + y) ^ (-2/5)` (`QED.ThreeLoopD.i2Maj`), integrable (Beta
integrals of both kinds). The integrand is holomorphic in `ε`, so `P` is complex differentiable
on `‖ε‖ < 1/40`. With Taylor's theorem this reduces the set (d) input for `I₂` to the three
Taylor coefficients of `P` (`QED.ThreeLoopD.hasTruncLaurent_setDMasterI2_of_coeffs`).

## Main results

* `QED.ThreeLoopD.analyticOnNhd_i2PInt`, `QED.ThreeLoopD.analyticAt_i2PInt`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI2_of_coeffs`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric

namespace QED.ThreeLoopD

/-! ### Real bounds -/

/-- The one-line factor: `(y + A) ^ (-(4/3 + t)) ≤ y ^ (-9/10) (1 + y) ^ (-2/5) A ^ (-7/15)`. -/
theorem i2_factor_le {y A t : ℝ} (hy : 0 < y) (hA : 0 < A) (hA1 : A ≤ 1) (ht1 : -(1 / 30) ≤ t)
    (ht2 : t ≤ 1 / 30) :
    (y + A) ^ (-(4 / 3 + t)) ≤
      y ^ (-(9 / 10) : ℝ) * (1 + y) ^ (-(2 / 5) : ℝ) * A ^ (-(7 / 15) : ℝ) := by
  have hyA : 0 < y + A := by linarith
  have hY : 0 < 1 + y := by linarith
  have hYA : 0 < (1 + y) * A := mul_pos hY hA
  have hYA' : (1 + y) * A ≤ y + A := by nlinarith
  -- `(y + A) ^ (-t) ≤ (1 + y) ^ (1/30) A ^ (-1/30)`
  have hP1 : 1 ≤ (1 + y) ^ (1 / 30 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hP2 : 1 ≤ A ^ (-(1 / 30) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hA hA1
    (by norm_num)
  have hT : (y + A) ^ (-t) ≤ (1 + y) ^ (1 / 30 : ℝ) * A ^ (-(1 / 30) : ℝ) := by
    rcases le_total t 0 with h | h
    · calc (y + A) ^ (-t) ≤ (1 + y) ^ (-t) :=
            Real.rpow_le_rpow hyA.le (by linarith) (by linarith)
        _ ≤ (1 + y) ^ (1 / 30 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hP2
    · calc (y + A) ^ (-t) ≤ A ^ (-t) :=
            Real.rpow_le_rpow_of_nonpos hA (by linarith) (by linarith)
        _ ≤ A ^ (-(1 / 30) : ℝ) := Real.rpow_le_rpow_of_exponent_ge hA hA1 (by linarith)
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hP1
  -- `(y + A) ^ (-4/3) ≤ y ^ (-9/10) ((1 + y) A) ^ (-13/30)`
  have hM : (y + A) ^ (-(4 / 3) : ℝ) ≤ y ^ (-(9 / 10) : ℝ) * ((1 + y) * A) ^ (-(13 / 30) : ℝ) := by
    rw [← rpow_mul_rpow_eq (a := -(9 / 10)) (b := -(13 / 30)) hyA (by norm_num)]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hy (by linarith) (by norm_num))
      (Real.rpow_le_rpow_of_nonpos hYA hYA' (by norm_num)) (by positivity) (by positivity)
  calc (y + A) ^ (-(4 / 3 + t)) = (y + A) ^ (-(4 / 3) : ℝ) * (y + A) ^ (-t) := by
        rw [rpow_mul_rpow_eq hyA (by ring : -(4 / 3 : ℝ) + -t = -(4 / 3 + t))]
    _ ≤ y ^ (-(9 / 10) : ℝ) * ((1 + y) * A) ^ (-(13 / 30) : ℝ) *
        ((1 + y) ^ (1 / 30 : ℝ) * A ^ (-(1 / 30) : ℝ)) :=
        mul_le_mul hM hT (by positivity) (by positivity)
    _ = _ := by
        rw [Real.mul_rpow hY.le hA.le]
        have e1 := rpow_mul_rpow_eq (a := -(13 / 30)) (b := 1 / 30) (c := -(2 / 5)) hY
          (by norm_num)
        have e2 := rpow_mul_rpow_eq (a := -(13 / 30)) (b := -(1 / 30)) (c := -(7 / 15)) hA
          (by norm_num)
        rw [← e1, ← e2]
        ring

/-- `𝒰 ^ (-2 + s) ≤ (a b c) ^ (-(4/3 + t))`, `t = -2s/3`, from `𝒰³ ≥ (ab)(bc)(ca)`. -/
theorem i2_U_le {a b c s : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : s ≤ 2) :
    (a * b + b * c + c * a) ^ (-2 + s) ≤
      a ^ (-(4 / 3 + -2 * s / 3)) * b ^ (-(4 / 3 + -2 * s / 3)) *
        c ^ (-(4 / 3 + -2 * s / 3)) := by
  set U := a * b + b * c + c * a with hU
  have habc : 0 < a * b * c := by positivity
  have hU0 : 0 < U := by positivity
  set G := (a * b * c) ^ (2 / 3 : ℝ) with hG
  have hG0 : 0 < G := Real.rpow_pos_of_pos habc _
  have hG3 : G ^ 3 = (a * b) * (b * c) * (c * a) := by
    rw [hG, ← Real.rpow_natCast, ← Real.rpow_mul habc.le]
    norm_num
    ring
  have hU3 : (a * b) * (b * c) * (c * a) ≤ U ^ 3 := by
    have h1 : a * b ≤ U := by nlinarith [mul_pos hb hc, mul_pos hc ha]
    have h2 : b * c ≤ U := by nlinarith [mul_pos ha hb, mul_pos hc ha]
    have h3 : c * a ≤ U := by nlinarith [mul_pos ha hb, mul_pos hb hc]
    have := mul_le_mul (mul_le_mul h1 h2 (by positivity) hU0.le) h3 (by positivity)
      (by positivity)
    nlinarith
  have hGU : G ≤ U := by
    rw [← hG3] at hU3
    exact le_of_pow_le_pow_left₀ (by norm_num) hU0.le hU3
  calc U ^ (-2 + s) ≤ G ^ (-2 + s) := Real.rpow_le_rpow_of_nonpos hG0 hGU (by linarith)
    _ = (a * b * c) ^ (-(4 / 3 + -2 * s / 3)) := by
        rw [hG, ← Real.rpow_mul habc.le]; congr 1; ring
    _ = _ := by rw [Real.mul_rpow (by positivity) hc.le, Real.mul_rpow ha.le hb.le]

/-- The real majorant of the integrand of `QED.ThreeLoopD.i2PInt`, a product of one-variable
functions. -/
noncomputable def i2Maj (z : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  (z.1 * (1 - z.1)) ^ (-(14 / 15) : ℝ) * ((z.2.1 * (1 - z.2.1)) ^ (-(14 / 15) : ℝ) *
    ((z.2.2.1 ^ (-(9 / 10) : ℝ) * (1 + z.2.2.1) ^ (-(1 / 4) : ℝ)) *
      ((z.2.2.2.1 ^ (-(9 / 10) : ℝ) * (1 + z.2.2.2.1) ^ (-(2 / 5) : ℝ)) *
        (z.2.2.2.2 ^ (-(9 / 10) : ℝ) * (1 + z.2.2.2.2) ^ (-(2 / 5) : ℝ)))))

theorem i2_lines_pos {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 < w * (1 - w) * x ∧ w * (1 - w) * x ≤ 1 ∧ 0 < w * (1 - w) * (1 - x) ∧
      w * (1 - w) * (1 - x) ≤ 1 ∧ 0 < (1 - w) ^ 2 * x * (1 - x) ∧
        (1 - w) ^ 2 * x * (1 - x) ≤ 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hw0, hw1⟩ := hw
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 1 - w := by linarith
  have hwq : w * (1 - w) ≤ 1 := by nlinarith
  have hxq : x * (1 - x) ≤ 1 := by nlinarith
  refine ⟨by positivity, ?_, by positivity, ?_, by positivity, ?_⟩
  · nlinarith [mul_pos hw0 h2]
  · nlinarith [mul_pos hw0 h2]
  · have : (1 - w) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_pos hx0 h1, sq_nonneg (1 - w)]

/-- **The dominating bound** (real form): for `|s| ≤ 1/20`. -/
theorem i2_integrand_le {x w y₄ y₇ y₈ s : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
    (h4 : 0 < y₄) (h7 : 0 < y₇) (h8 : 0 < y₈) (hs1 : -(1 / 20) ≤ s) (hs2 : s ≤ 1 / 20) :
    (1 - w) * i2U x w y₄ y₇ y₈ ^ (-2 + 4 * s) * i2F x w y₄ y₇ y₈ ^ (-3 * s) ≤
      i2Maj (x, w, y₄, y₇, y₈) := by
  obtain ⟨hA, hA1, hB, hB1, hC, hC1⟩ := i2_lines_pos hx hw
  have hw1 : 0 < 1 - w := by linarith [hw.2]
  have hw1' : 1 - w ≤ 1 := by linarith [hw.1]
  set A := w * (1 - w) * x with hAd
  set B := w * (1 - w) * (1 - x) with hBd
  set C := (1 - w) ^ 2 * x * (1 - x) with hCd
  have ha : 0 < y₇ + A := by linarith
  have hb : 0 < y₈ + B := by linarith
  have hc : 0 < y₄ + C := by linarith
  have hUe : i2U x w y₄ y₇ y₈ =
      (y₇ + A) * (y₈ + B) + (y₈ + B) * (y₄ + C) + (y₄ + C) * (y₇ + A) := rfl
  have hFe : i2F x w y₄ y₇ y₈ = i2U x w y₄ y₇ y₈ + y₄ ^ 2 * ((y₇ + A) + (y₈ + B)) := rfl
  set U := i2U x w y₄ y₇ y₈ with hU
  set F := i2F x w y₄ y₇ y₈ with hF
  have hU0 : 0 < U := by rw [hUe]; positivity
  have hUF : U ≤ F := by rw [hFe]; nlinarith [sq_nonneg y₄]
  have hFU : F ≤ (1 + y₄) * U := by
    rw [hFe]
    have : y₄ * ((y₇ + A) + (y₈ + B)) ≤ U := by rw [hUe]; nlinarith [mul_pos ha hb]
    nlinarith
  have hF0 : 0 < F := lt_of_lt_of_le hU0 hUF
  have hY4 : 0 < 1 + y₄ := by linarith
  -- step 1: remove `ℱ`
  have hρ1 : 1 ≤ F / U := (one_le_div hU0).mpr hUF
  have hρ2 : F / U ≤ 1 + y₄ := (div_le_iff₀ hU0).mpr hFU
  have hρ0 : 0 < F / U := by linarith
  have hS1 : U ^ (-2 + 4 * s) * F ^ (-3 * s) = U ^ (-2 + s) * (F / U) ^ (-3 * s) := by
    have hFe' : F = U * (F / U) := by field_simp
    conv_lhs => rw [hFe']
    rw [Real.mul_rpow hU0.le hρ0.le, ← mul_assoc,
      rpow_mul_rpow_eq hU0 (by ring : (-2 + 4 * s) + (-3 * s) = -2 + s)]
  have hρ : (F / U) ^ (-3 * s) ≤ (1 + y₄) ^ (3 / 20 : ℝ) :=
    calc (F / U) ^ (-3 * s) ≤ (F / U) ^ (3 / 20 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith)
      _ ≤ _ := Real.rpow_le_rpow hρ0.le hρ2 (by norm_num)
  -- step 2 and 3: the three lines
  have hU2 := i2_U_le ha hb hc (s := s) (by linarith)
  rw [← hUe] at hU2
  have ht1 : -(1 / 30) ≤ -2 * s / 3 := by linarith
  have ht2 : -2 * s / 3 ≤ 1 / 30 := by linarith
  have fa := i2_factor_le h7 hA hA1 ht1 ht2
  have fb := i2_factor_le h8 hB hB1 ht1 ht2
  have fc := i2_factor_le h4 hC hC1 ht1 ht2
  have key : (1 - w) * U ^ (-2 + 4 * s) * F ^ (-3 * s) ≤
      (1 - w) * ((y₇ ^ (-(9 / 10) : ℝ) * (1 + y₇) ^ (-(2 / 5) : ℝ) * A ^ (-(7 / 15) : ℝ)) *
        (y₈ ^ (-(9 / 10) : ℝ) * (1 + y₈) ^ (-(2 / 5) : ℝ) * B ^ (-(7 / 15) : ℝ)) *
        (y₄ ^ (-(9 / 10) : ℝ) * (1 + y₄) ^ (-(2 / 5) : ℝ) * C ^ (-(7 / 15) : ℝ))) *
        (1 + y₄) ^ (3 / 20 : ℝ) := by
    rw [mul_assoc, hS1, ← mul_assoc]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (hU2.trans ?_) hw1.le) hρ (by positivity)
      (by positivity)
    exact mul_le_mul (mul_le_mul fa fb (by positivity) (by positivity)) fc (by positivity)
      (by positivity)
  refine key.trans (le_of_eq_of_le (b := (1 - w) * ((x * (1 - x)) ^ (-(14 / 15) : ℝ) *
      w ^ (-(14 / 15) : ℝ) *
      (1 - w) ^ (-(28 / 15) : ℝ)) * ((y₄ ^ (-(9 / 10) : ℝ) * (1 + y₄) ^ (-(1 / 4) : ℝ)) *
      ((y₇ ^ (-(9 / 10) : ℝ) * (1 + y₇) ^ (-(2 / 5) : ℝ)) *
        (y₈ ^ (-(9 / 10) : ℝ) * (1 + y₈) ^ (-(2 / 5) : ℝ))))) ?_ ?_)
  · have hx0 := hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hw0 := hw.1
    rw [hAd, hBd, hCd, Real.mul_rpow (by positivity) hx0.le, Real.mul_rpow hw0.le hw1.le,
      Real.mul_rpow (by positivity) hx1.le, Real.mul_rpow hw0.le hw1.le,
      Real.mul_rpow (by positivity) hx1.le, Real.mul_rpow (by positivity) hx0.le,
      Real.mul_rpow hx0.le hx1.le, ← Real.rpow_natCast, ← Real.rpow_mul hw1.le]
    have e1 := rpow_mul_rpow_eq (a := -(7 / 15)) (b := -(7 / 15)) (c := -(14 / 15)) hx0
      (by norm_num)
    have e2 := rpow_mul_rpow_eq (a := -(7 / 15)) (b := -(7 / 15)) (c := -(14 / 15)) hx1
      (by norm_num)
    have e3 := rpow_mul_rpow_eq (a := -(7 / 15)) (b := -(7 / 15)) (c := -(14 / 15)) hw0
      (by norm_num)
    have e4 : (1 - w) ^ (-(7 / 15) : ℝ) * ((1 - w) ^ (-(7 / 15) : ℝ) *
        (1 - w) ^ (((2 : ℕ) : ℝ) * -(7 / 15))) = (1 - w) ^ (-(28 / 15) : ℝ) := by
      rw [← Real.rpow_add hw1, ← Real.rpow_add hw1]; norm_num
    have e6 := rpow_mul_rpow_eq (a := -(2 / 5)) (b := 3 / 20) (c := -(1 / 4)) hY4 (by norm_num)
    rw [← e1, ← e2, ← e3, ← e4, ← e6]
    ring
  · rw [i2Maj]
    have hx0 := hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hw0 := hw.1
    have hq : (1 - w) * (1 - w) ^ (-(28 / 15) : ℝ) ≤ (1 - w) ^ (-(14 / 15) : ℝ) := by
      rw [← Real.rpow_one_add' hw1.le (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_ge hw1 hw1' (by norm_num)
    rw [Real.mul_rpow hw0.le hw1.le]
    have hX := Real.rpow_nonneg (mul_pos hx0 hx1).le (-(14 / 15) : ℝ)
    have hW := Real.rpow_nonneg hw0.le (-(14 / 15) : ℝ)
    have hR : 0 ≤ (y₄ ^ (-(9 / 10) : ℝ) * (1 + y₄) ^ (-(1 / 4) : ℝ)) *
        ((y₇ ^ (-(9 / 10) : ℝ) * (1 + y₇) ^ (-(2 / 5) : ℝ)) *
          (y₈ ^ (-(9 / 10) : ℝ) * (1 + y₈) ^ (-(2 / 5) : ℝ))) := by positivity
    calc (1 - w) * ((x * (1 - x)) ^ (-(14 / 15) : ℝ) * w ^ (-(14 / 15) : ℝ) *
          (1 - w) ^ (-(28 / 15) : ℝ)) * ((y₄ ^ (-(9 / 10) : ℝ) * (1 + y₄) ^ (-(1 / 4) : ℝ)) *
          ((y₇ ^ (-(9 / 10) : ℝ) * (1 + y₇) ^ (-(2 / 5) : ℝ)) *
            (y₈ ^ (-(9 / 10) : ℝ) * (1 + y₈) ^ (-(2 / 5) : ℝ)))) =
        (x * (1 - x)) ^ (-(14 / 15) : ℝ) * w ^ (-(14 / 15) : ℝ) *
          ((1 - w) * (1 - w) ^ (-(28 / 15) : ℝ)) * ((y₄ ^ (-(9 / 10) : ℝ) *
          (1 + y₄) ^ (-(1 / 4) : ℝ)) * ((y₇ ^ (-(9 / 10) : ℝ) * (1 + y₇) ^ (-(2 / 5) : ℝ)) *
            (y₈ ^ (-(9 / 10) : ℝ) * (1 + y₈) ^ (-(2 / 5) : ℝ)))) := by ring
      _ ≤ (x * (1 - x)) ^ (-(14 / 15) : ℝ) * w ^ (-(14 / 15) : ℝ) *
          (1 - w) ^ (-(14 / 15) : ℝ) * ((y₄ ^ (-(9 / 10) : ℝ) *
          (1 + y₄) ^ (-(1 / 4) : ℝ)) * ((y₇ ^ (-(9 / 10) : ℝ) * (1 + y₇) ^ (-(2 / 5) : ℝ)) *
            (y₈ ^ (-(9 / 10) : ℝ) * (1 + y₈) ^ (-(2 / 5) : ℝ)))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (mul_nonneg hX hW)) hR
      _ = _ := by ring

/-! ### Integrability of the majorant -/

theorem integrableOn_i2_ypart {b : ℝ} (hb : 1 / 10 < b) :
    IntegrableOn (fun y : ℝ => y ^ (-(9 / 10) : ℝ) * (1 + y) ^ (-b)) (Ioi 0) := by
  have h := QED.DimReg.integrableOn_betaPrime (a := ((1 / 10 : ℝ) : ℂ))
    (b := ((b - 1 / 10 : ℝ) : ℂ)) (by norm_num) (by simp; linarith) one_pos
  refine IntegrableOn.congr_fun h.norm (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (0 : ℝ) < y := hy
  have hy1 : (0 : ℝ) < 1 + 1 * y := by linarith
  rw [QED.DimReg.betaPrimeIntegrand, norm_mul, norm_cpow_eq_rpow_re_of_pos hy0,
    norm_cpow_eq_rpow_re_of_pos hy1, one_mul]
  congr 2 <;> norm_num

theorem integrable_i2Maj : Integrable i2Maj (volume.restrict i2Dom) := by
  rw [i2Dom, volume_restrict_prod5]
  exact (integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
      ((integrableOn_i2_ypart (by norm_num)).mul_prod
        ((integrableOn_i2_ypart (by norm_num)).mul_prod (integrableOn_i2_ypart (by norm_num)))))

/-! ### The complex integrand -/

/-- The integrand of `QED.ThreeLoopD.i2PInt`. -/
noncomputable def i2Integrand (ε : ℂ) (z : ℝ × ℝ × ℝ × ℝ × ℝ) : ℂ :=
  ((1 - z.2.1 : ℝ) : ℂ) * ((i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 : ℝ) : ℂ) ^ (-2 + 4 * ε) *
    ((i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 : ℝ) : ℂ) ^ (-3 * ε)

theorem i2PInt_eq (ε : ℂ) : i2PInt ε = ∫ z in i2Dom, i2Integrand ε z := rfl

theorem measurable_i2Integrand (ε : ℂ) : Measurable (i2Integrand ε) := by
  unfold i2Integrand i2F i2U i2LineA i2LineB i2LineC; fun_prop

theorem i2UF_pos {z : ℝ × ℝ × ℝ × ℝ × ℝ} (hz : z ∈ i2Dom) :
    0 < i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ∧
      0 < i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 := by
  obtain ⟨hx, hw, h4, h7, h8⟩ := hz
  obtain ⟨hA, -, hB, -, hC, -⟩ := i2_lines_pos hx hw
  have h4' : (0 : ℝ) < z.2.2.1 := h4
  have h7' : (0 : ℝ) < z.2.2.2.1 := h7
  have h8' : (0 : ℝ) < z.2.2.2.2 := h8
  have hU : 0 < i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 := by
    unfold i2U i2LineA i2LineB i2LineC
    have : 0 < z.2.2.2.1 + z.2.1 * (1 - z.2.1) * z.1 := by linarith
    have : 0 < z.2.2.2.2 + z.2.1 * (1 - z.2.1) * (1 - z.1) := by linarith
    have : 0 < z.2.2.1 + (1 - z.2.1) ^ 2 * z.1 * (1 - z.1) := by linarith
    positivity
  refine ⟨hU, ?_⟩
  unfold i2F
  have : 0 ≤ z.2.2.1 ^ 2 * (i2LineA z.1 z.2.1 z.2.2.2.1 + i2LineB z.1 z.2.1 z.2.2.2.2) := by
    unfold i2LineA i2LineB
    have : 0 < z.2.2.2.1 + z.2.1 * (1 - z.2.1) * z.1 := by linarith
    have : 0 < z.2.2.2.2 + z.2.1 * (1 - z.2.1) * (1 - z.1) := by linarith
    positivity
  linarith

theorem norm_i2Integrand_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z : ℝ × ℝ × ℝ × ℝ × ℝ}
    (hz : z ∈ i2Dom) : ‖i2Integrand ε z‖ ≤ i2Maj z := by
  obtain ⟨hU, hF⟩ := i2UF_pos hz
  obtain ⟨hx, hw, h4, h7, h8⟩ := hz
  have hr := abs_le.mp ((abs_re_le_norm ε).trans hε.le)
  have hw1 : (0 : ℝ) < 1 - z.2.1 := by linarith [hw.2]
  have hb := i2_integrand_le hx hw h4 h7 h8 (s := ε.re) (by linarith) (by linarith)
  rw [i2Integrand, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hU,
    norm_cpow_eq_rpow_re_of_pos hF, Complex.norm_real, Real.norm_of_nonneg hw1.le]
  convert hb using 3 <;> simp

theorem differentiableAt_i2Integrand {z : ℝ × ℝ × ℝ × ℝ × ℝ} (hz : z ∈ i2Dom) (ε : ℂ) :
    DifferentiableAt ℂ (fun ε => i2Integrand ε z) ε := by
  obtain ⟨hU, hF⟩ := i2UF_pos hz
  unfold i2Integrand
  refine ((differentiableAt_const _).mul ?_).mul ?_
  · exact (by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => -2 + 4 * ε) ε).const_cpow
      (Or.inl (ofReal_ne_zero.mpr hU.ne'))
  · exact (by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => -3 * ε) ε).const_cpow
      (Or.inl (ofReal_ne_zero.mpr hF.ne'))

/-! ### Analyticity -/

theorem differentiableAt_i2PInt {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 40) :
    DifferentiableAt ℂ i2PInt ε₀ := by
  have hball : ∀ ε ∈ ball ε₀ (1 / 40), ‖ε‖ < 1 / 20 := fun ε hε => by
    have := norm_sub_norm_le ε ε₀
    rw [mem_ball, dist_eq_norm] at hε
    linarith
  have hS : MeasurableSet i2Dom :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod (measurableSet_Ioi.prod
      (measurableSet_Ioi.prod measurableSet_Ioi)))
  have e : i2PInt = fun ε => ∫ z in i2Dom, i2Integrand ε z := funext i2PInt_eq
  rw [e]
  refine QED.DimReg.differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 40)
    integrable_i2Maj (fun ε _ => (measurable_i2Integrand ε).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem hS fun z hz ε hε => norm_i2Integrand_le (hball ε hε) hz
  · exact ae_restrict_of_forall_mem hS fun z hz ε _ =>
      (differentiableAt_i2Integrand hz ε).differentiableWithinAt

/-- **The parametric integral is analytic near `0`.** -/
theorem analyticOnNhd_i2PInt : AnalyticOnNhd ℂ i2PInt (ball 0 (1 / 40)) := fun ε hε =>
  DifferentiableOn.analyticAt (fun ε' hε' => (differentiableAt_i2PInt
    (by simpa using hε')).differentiableWithinAt) (isOpen_ball.mem_nhds hε)

/-- **`P` is analytic at `0`.** -/
theorem analyticAt_i2PInt : AnalyticAt ℂ i2PInt 0 :=
  analyticOnNhd_i2PInt 0 (mem_ball_self (by norm_num))

/-! ### The input from the Taylor coefficients -/

/-- **The set (d) input for `I₂` from three Taylor coefficients of `P`.** -/
theorem hasTruncLaurent_setDMasterI2_of_coeffs (h0 : i2PInt 0 = i2P0)
    (h1 : iteratedDeriv 1 i2PInt 0 = i2P1) (h2 : iteratedDeriv 2 i2PInt 0 / 2 = i2P2) :
    HasTruncLaurent setDMasterI2 setDLaurentI2 2 := by
  refine hasTruncLaurent_setDMasterI2_of_P ?_
  obtain ⟨R, hR, hev⟩ := hasTruncLaurent_of_analyticAt_zero analyticAt_i2PInt 3
  refine ⟨R, hR, hev.mono fun ε hε => ?_⟩
  rw [hε, i2PLaurent, ← h0, ← h1, ← h2]
  simp [Finset.sum_range_succ]

end QED.ThreeLoopD
