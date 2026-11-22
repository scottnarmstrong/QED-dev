/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1FEnd
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₂`: the `ℱ`-part of `P'(0)` as a double integral over the unit square

The integrations over the Feynman parameters reduce the `ℱ`-part to

  `∫₀¹ ds 8 (1 + s²) / (s (1 - s²)) log² s ∫₀¹ dz 2 z w(r(s, z))`,
  `r(s, z) = (1 - s²) z / (s (1 - z²))`,
  `w(r) = -log (1 - r) / 2 - 3 log (1 + r) / 2` (`r < 1`), `w(r) = -log (1 - 1 / r²) / 2` (`r ≥ 1`).

Here we evaluate it. Since `1 - r = (s - z)(1 + s z) / (s (1 - z²))` and
`1 + r = (s + z)(1 - s z) / (s (1 - z²))`, `r < 1` iff `z < s` and `w(r(s, z))` is a sum of
logarithms of linear functions of `z` on each side of `z = s`; the primitives
`(z² - β² / α²) log (α z + β) - z² / 2 + β z / α` of `2 z log (α z + β)` give

  `∫₀¹ 2 z w(r(s, z)) dz = I(s²)`, `I` = `QED.ThreeLoopD.i2P1FI`,

and `t = s²` turns the outer integral into `QED.ThreeLoopD.i2P1FEnd_value`.

## Main definitions

* `QED.ThreeLoopD.i2P1Fw`, `QED.ThreeLoopD.i2P1Fr`.

## Main results

* `QED.ThreeLoopD.i2P1FZ_inner`: `∫₀¹ 2 z w(r(s, z)) dz = I(s²)`.
* `QED.ThreeLoopD.i2P1FZ_outer`: the outer integral of `I(s²)`.
* `QED.ThreeLoopD.i2P1FZ_value`: the double integral is `2 π⁴ / 45 - 4 ζ(3) + π² / 3`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- The weight `w(r)`: `-log (1 - r) / 2 - 3 log (1 + r) / 2` for `r < 1`,
`-log (1 - 1 / r²) / 2` for `r ≥ 1`. -/
noncomputable def i2P1Fw (r : ℝ) : ℝ :=
  if r < 1 then -log (1 - r) / 2 - 3 * log (1 + r) / 2 else -log (1 - 1 / r ^ 2) / 2

/-- The argument `r(s, z) = (1 - s²) z / (s (1 - z²))`. -/
noncomputable def i2P1Fr (s z : ℝ) : ℝ := (1 - s ^ 2) * z / (s * (1 - z ^ 2))

/-- The primitive `(z² - β² / α²) log (α z + β) - z² / 2 + β z / α` of `2 z log (α z + β)`. -/
noncomputable def i2P1FZP (α β z : ℝ) : ℝ :=
  (z ^ 2 - β ^ 2 / α ^ 2) * log (α * z + β) - z ^ 2 / 2 + β * z / α

theorem i2P1FZ_hasDerivAt_P {α β z : ℝ} (hα : α ≠ 0) (hz : 0 < α * z + β) :
    HasDerivAt (i2P1FZP α β) (2 * z * log (α * z + β)) z := by
  have hl := (((hasDerivAt_id z).const_mul α).add_const β).log hz.ne'
  have hd := ((((hasDerivAt_id z).pow 2).sub_const (β ^ 2 / α ^ 2)).mul hl).sub
    (((hasDerivAt_id z).pow 2).div_const 2) |>.add ((hasDerivAt_id z).const_mul β |>.div_const α)
  refine hd.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  field_simp
  ring

/-- `∫ₐᵇ 2 z log (α z + β) dz` when `α z + β > 0` on `[a, b]`. -/
theorem i2P1FZ_smooth {α β a b : ℝ} (hα : α ≠ 0) (hpos : ∀ z ∈ uIcc a b, 0 < α * z + β) :
    IntervalIntegrable (fun z => 2 * z * log (α * z + β)) volume a b ∧
      ∫ z in a..b, 2 * z * log (α * z + β) = i2P1FZP α β b - i2P1FZP α β a := by
  have hc : ContinuousOn (fun z => 2 * z * log (α * z + β)) (uIcc a b) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.log (by fun_prop) fun z hz => (hpos z hz).ne')
  exact ⟨hc.intervalIntegrable, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z hz => i2P1FZ_hasDerivAt_P hα (hpos z hz)) hc.intervalIntegrable⟩

/-- `∫₀ˢ 2 z log (s - z) dz = s² log s - 3 s² / 2`. -/
theorem i2P1FZ_sing_left {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun z => 2 * z * log (s - z)) volume 0 s ∧
      ∫ z in (0 : ℝ)..s, 2 * z * log (s - z) = s ^ 2 * log s - 3 * s ^ 2 / 2 := by
  set F : ℝ → ℝ := fun z => -(z + s) * ((s - z) * log (s - z)) - z ^ 2 / 2 - s * z with hF
  have hFc : Continuous F := by
    have : Continuous fun z : ℝ => (s - z) * log (s - z) :=
      continuous_mul_log.comp (by fun_prop)
    exact (((by fun_prop : Continuous fun z : ℝ => -(z + s)).mul this).sub (by fun_prop)).sub
      (by fun_prop)
  have h := intervalIntegrable_and_integral_eq_of_nonpos' (F := F)
    (f := fun z => 2 * z * log (s - z)) hs.1
    (fun z hz => by
      have h1 : 0 < s - z := by linarith [hz.2]
      have hl := ((hasDerivAt_id z).const_sub s).log h1.ne'
      have hd := ((((hasDerivAt_id z).add_const s).neg.mul
        (((hasDerivAt_id z).const_sub s).mul hl)).sub (((hasDerivAt_id z).pow 2).div_const 2)).sub
        ((hasDerivAt_id z).const_mul s)
      refine hd.congr_deriv ?_
      simp only [id, Pi.mul_apply, Pi.neg_apply]
      field_simp
      ring)
    (fun z hz => mul_nonpos_of_nonneg_of_nonpos (by linarith [hz.1])
      (log_nonpos (by linarith [hz.2]) (by linarith [hz.1, hs.2])))
    (hFc.tendsto 0 |>.mono_left nhdsWithin_le_nhds)
    (hFc.tendsto s |>.mono_left nhdsWithin_le_nhds)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [hF, sub_self, log_zero, mul_zero, sub_zero, zero_add]
  ring

/-- `∫ₛ¹ 2 z log (z - s) dz = (1 - s²) log (1 - s) - 1 / 2 - s + 3 s² / 2`. -/
theorem i2P1FZ_sing_right {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun z => 2 * z * log (z - s)) volume s 1 ∧
      ∫ z in s..1, 2 * z * log (z - s) = (1 - s ^ 2) * log (1 - s) - 1 / 2 - s + 3 * s ^ 2 / 2 := by
  set F : ℝ → ℝ := fun z => (z + s) * ((z - s) * log (z - s)) - z ^ 2 / 2 - s * z with hF
  have hFc : Continuous F := by
    have : Continuous fun z : ℝ => (z - s) * log (z - s) :=
      continuous_mul_log.comp (by fun_prop)
    exact (((by fun_prop : Continuous fun z : ℝ => z + s).mul this).sub (by fun_prop)).sub
      (by fun_prop)
  have h := intervalIntegrable_and_integral_eq_of_nonpos' (F := F)
    (f := fun z => 2 * z * log (z - s)) hs.2
    (fun z hz => by
      have h1 : 0 < z - s := by linarith [hz.1]
      have hl := ((hasDerivAt_id z).sub_const s).log h1.ne'
      have hd := ((((hasDerivAt_id z).add_const s).mul
        (((hasDerivAt_id z).sub_const s).mul hl)).sub (((hasDerivAt_id z).pow 2).div_const 2)).sub
        ((hasDerivAt_id z).const_mul s)
      refine hd.congr_deriv ?_
      simp only [id, Pi.mul_apply]
      field_simp
      ring)
    (fun z hz => mul_nonpos_of_nonneg_of_nonpos (by linarith [hz.1, hs.1])
      (log_nonpos (by linarith [hz.1]) (by linarith [hz.2, hs.1])))
    (hFc.tendsto s |>.mono_left nhdsWithin_le_nhds)
    (hFc.tendsto 1 |>.mono_left nhdsWithin_le_nhds)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [hF, sub_self, log_zero, mul_zero]
  ring

theorem i2P1FZ_one_sub_r {s z : ℝ} (hs : s ≠ 0) (h1 : -1 * z + 1 ≠ 0) (h2 : 1 * z + 1 ≠ 0) :
    1 - i2P1Fr s z = (s - z) * (s * z + 1) / (s * (-1 * z + 1) * (1 * z + 1)) := by
  have e : i2P1Fr s z = (1 - s ^ 2) * z / (s * (-1 * z + 1) * (1 * z + 1)) := by
    simp only [i2P1Fr]; ring
  rw [e, eq_div_iff (mul_ne_zero (mul_ne_zero hs h1) h2), sub_mul,
    div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero hs h1) h2)]
  ring

/-- `w(r(s, z))` for `0 < z < s < 1`. -/
theorem i2P1FZ_w_left {s z : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) s) :
    i2P1Fw (i2P1Fr s z) = -log (s - z) / 2 - log (s * z + 1) / 2 - 3 * log (1 * z + s) / 2 -
      3 * log (-s * z + 1) / 2 + 2 * log s + 2 * log (-1 * z + 1) + 2 * log (1 * z + 1) := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hz0, hzs⟩ := hz
  have p1 : 0 < s - z := by linarith
  have p2 : 0 < s * z + 1 := by positivity
  have p3 : 0 < 1 * z + s := by linarith
  have p4 : 0 < -s * z + 1 := by nlinarith
  have p5 : 0 < -1 * z + 1 := by linarith
  have p6 : 0 < 1 * z + 1 := by linarith
  have hr1 := i2P1FZ_one_sub_r hs0.ne' p5.ne' p6.ne'
  have hr2 : 1 + i2P1Fr s z = (1 * z + s) * (-s * z + 1) / (s * (-1 * z + 1) * (1 * z + 1)) := by
    have hD : s * (-1 * z + 1) * (1 * z + 1) ≠ 0 := by positivity
    have e : i2P1Fr s z = (1 - s ^ 2) * z / (s * (-1 * z + 1) * (1 * z + 1)) := by
      simp only [i2P1Fr]; ring
    rw [e, eq_div_iff hD, add_mul, div_mul_cancel₀ _ hD]
    ring
  have hlt : i2P1Fr s z < 1 := by
    have : 0 < 1 - i2P1Fr s z := by rw [hr1]; positivity
    linarith
  rw [i2P1Fw, ite_eq_left_of_eq_true _ _ (eq_true hlt), hr1, hr2,
    log_div (by positivity) (by positivity),
    log_div (by positivity) (by positivity), log_mul p1.ne' p2.ne', log_mul p3.ne' p4.ne',
    log_mul (by positivity) p6.ne', log_mul hs0.ne' p5.ne']
  ring

/-- `w(r(s, z))` for `0 < s < z < 1`. -/
theorem i2P1FZ_w_right {s z : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo s 1) :
    i2P1Fw (i2P1Fr s z) = -log (z - s) / 2 - log (s * z + 1) / 2 - log (1 * z + s) / 2 -
      log (-s * z + 1) / 2 + (log (1 - s) + log (1 + s)) + log (1 * z + 0) := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hzs, hz1⟩ := hz
  have p1 : 0 < z - s := by linarith
  have p2 : 0 < s * z + 1 := by nlinarith
  have p3 : 0 < 1 * z + s := by linarith
  have p4 : 0 < -s * z + 1 := by nlinarith
  have p5 : 0 < -1 * z + 1 := by linarith
  have p6 : 0 < 1 * z + 1 := by linarith
  have q1 : 0 < 1 - s := by linarith
  have q2 : 0 < 1 + s := by linarith
  have hz0 : 0 < z := by linarith
  have hr1 := i2P1FZ_one_sub_r hs0.ne' p5.ne' p6.ne'
  have hge : ¬ i2P1Fr s z < 1 := by
    have : 1 - i2P1Fr s z < 0 := by
      rw [hr1]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) p2) (by positivity)
    linarith
  have hq : 1 - 1 / i2P1Fr s z ^ 2 = (z - s) * (s * z + 1) * ((1 * z + s) * (-s * z + 1)) /
      ((1 - s) ^ 2 * (1 + s) ^ 2 * (1 * z + 0) ^ 2) := by
    have hD : s * (-1 * z + 1) * (1 * z + 1) ≠ 0 := by positivity
    have hN : (1 - s ^ 2) * z ≠ 0 := by
      have : 0 < 1 - s ^ 2 := by nlinarith
      positivity
    have e : i2P1Fr s z = (1 - s ^ 2) * z / (s * (-1 * z + 1) * (1 * z + 1)) := by
      simp only [i2P1Fr]; ring
    have hE : (1 - s) ^ 2 * (1 + s) ^ 2 * (1 * z + 0) ^ 2 ≠ 0 := by positivity
    rw [e, div_pow, one_div_div, eq_div_iff hE, sub_mul, div_mul_eq_mul_div,
      show (1 - s) ^ 2 * (1 + s) ^ 2 * (1 * z + 0) ^ 2 = ((1 - s ^ 2) * z) ^ 2 by ring,
      mul_div_assoc, div_self (pow_ne_zero 2 hN)]
    ring
  rw [i2P1Fw, ite_eq_right_of_eq_false _ _ (eq_false hge), hq,
    log_div (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_mul p1.ne' p2.ne', log_mul p3.ne' p4.ne',
    log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_pow, log_pow, log_pow]
  push_cast
  ring

/-- **The inner integral**: `∫₀¹ 2 z w(r(s, z)) dz = I(s²)` for `0 < s < 1`. -/
theorem i2P1FZ_inner {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun z => 2 * z * i2P1Fw (i2P1Fr s z)) volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, 2 * z * i2P1Fw (i2P1Fr s z) = i2P1FI (s ^ 2) := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨iL, vL⟩ := i2P1FZ_sing_left ⟨hs0, hs1⟩
  obtain ⟨iR, vR⟩ := i2P1FZ_sing_right ⟨hs0, hs1⟩
  have hsn : (s : ℝ) ≠ 0 := hs0.ne'
  -- the smooth part on `[0, s]`
  have uL : uIcc 0 s = Icc 0 s := uIcc_of_le hs0.le
  have uR : uIcc s 1 = Icc s 1 := uIcc_of_le hs1.le
  have pL : ∀ z ∈ uIcc 0 s, 0 < s * z + 1 ∧ 0 < 1 * z + s ∧ 0 < -s * z + 1 ∧
      0 < -1 * z + 1 ∧ 0 < 1 * z + 1 := by
    intro z hz
    rw [uL] at hz
    obtain ⟨h0, h1⟩ := hz
    refine ⟨by positivity, by linarith, by nlinarith, by linarith, by linarith⟩
  have pR : ∀ z ∈ uIcc s 1, 0 < s * z + 1 ∧ 0 < 1 * z + s ∧ 0 < -s * z + 1 ∧
      0 < 1 * z + 0 := by
    intro z hz
    rw [uR] at hz
    obtain ⟨h0, h1⟩ := hz
    refine ⟨by nlinarith, by linarith, by nlinarith, by linarith⟩
  have i1 := (i2P1FZ_smooth (α := s) (β := 1) hsn fun z hz => (pL z hz).1).1
  have i2 := (i2P1FZ_smooth (α := 1) (β := s) one_ne_zero fun z hz => (pL z hz).2.1).1
  have i3 := (i2P1FZ_smooth (α := -s) (β := 1) (neg_ne_zero.2 hsn)
    fun z hz => (pL z hz).2.2.1).1
  have i4 := (i2P1FZ_smooth (α := -1) (β := 1) (by norm_num) fun z hz => (pL z hz).2.2.2.1).1
  have i5 := (i2P1FZ_smooth (α := 1) (β := 1) one_ne_zero fun z hz => (pL z hz).2.2.2.2).1
  have i6 : IntervalIntegrable (fun z : ℝ => 2 * z) volume 0 s :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have iSL := (((((i1.const_mul (-(1 / 2))).sub (i2.const_mul (3 / 2))).sub
    (i3.const_mul (3 / 2))).add (i6.const_mul (2 * log s))).add (i4.const_mul 2)).add
    (i5.const_mul 2)
  have vSL := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun z => -(1 / 2) * i2P1FZP s 1 z - 3 / 2 * i2P1FZP 1 s z -
      3 / 2 * i2P1FZP (-s) 1 z + 2 * log s * z ^ 2 + 2 * i2P1FZP (-1) 1 z + 2 * i2P1FZP 1 1 z)
    (fun z hz => by
      obtain ⟨q1, q2, q3, q4, q5⟩ := pL z hz
      have hd := ((((((i2P1FZ_hasDerivAt_P hsn q1).const_mul (-(1 / 2))).sub
        ((i2P1FZ_hasDerivAt_P one_ne_zero q2).const_mul (3 / 2))).sub
        ((i2P1FZ_hasDerivAt_P (neg_ne_zero.2 hsn) q3).const_mul (3 / 2))).add
        (((hasDerivAt_id z).pow 2).const_mul (2 * log s))).add
        ((i2P1FZ_hasDerivAt_P (by norm_num) q4).const_mul 2)).add
        ((i2P1FZ_hasDerivAt_P one_ne_zero q5).const_mul 2)
      refine hd.congr_deriv ?_
      simp only [id]
      ring) iSL
  -- the smooth part on `[s, 1]`
  have j1 := (i2P1FZ_smooth (α := s) (β := 1) hsn fun z hz => (pR z hz).1).1
  have j2 := (i2P1FZ_smooth (α := 1) (β := s) one_ne_zero fun z hz => (pR z hz).2.1).1
  have j3 := (i2P1FZ_smooth (α := -s) (β := 1) (neg_ne_zero.2 hsn)
    fun z hz => (pR z hz).2.2.1).1
  have j4 := (i2P1FZ_smooth (α := 1) (β := 0) one_ne_zero fun z hz => (pR z hz).2.2.2).1
  have j6 : IntervalIntegrable (fun z : ℝ => 2 * z) volume s 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have iSR := ((((j1.const_mul (-(1 / 2))).sub (j2.const_mul (1 / 2))).sub
    (j3.const_mul (1 / 2))).add (j6.const_mul (log (1 - s) + log (1 + s)))).add j4
  have vSR := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun z => -(1 / 2) * i2P1FZP s 1 z - 1 / 2 * i2P1FZP 1 s z -
      1 / 2 * i2P1FZP (-s) 1 z + (log (1 - s) + log (1 + s)) * z ^ 2 + i2P1FZP 1 0 z)
    (fun z hz => by
      obtain ⟨q1, q2, q3, q4⟩ := pR z hz
      have hd := (((((i2P1FZ_hasDerivAt_P hsn q1).const_mul (-(1 / 2))).sub
        ((i2P1FZ_hasDerivAt_P one_ne_zero q2).const_mul (1 / 2))).sub
        ((i2P1FZ_hasDerivAt_P (neg_ne_zero.2 hsn) q3).const_mul (1 / 2))).add
        (((hasDerivAt_id z).pow 2).const_mul (log (1 - s) + log (1 + s)))).add
        (i2P1FZ_hasDerivAt_P one_ne_zero q4)
      refine hd.congr_deriv ?_
      simp only [id]
      ring) iSR
  -- the two halves
  have eL : EqOn (fun z => -(1 / 2) * (2 * z * log (s - z)) + (-(1 / 2) * (2 * z * log (s * z + 1))
      - 3 / 2 * (2 * z * log (1 * z + s)) - 3 / 2 * (2 * z * log (-s * z + 1)) +
      2 * log s * (2 * z) + 2 * (2 * z * log (-1 * z + 1)) + 2 * (2 * z * log (1 * z + 1))))
      (fun z => 2 * z * i2P1Fw (i2P1Fr s z)) (uIoo 0 s) := by
    intro z hz
    rw [uIoo_of_le hs0.le] at hz
    simp only [i2P1FZ_w_left ⟨hs0, hs1⟩ hz]
    ring
  have eR : EqOn (fun z => -(1 / 2) * (2 * z * log (z - s)) + (-(1 / 2) * (2 * z * log (s * z + 1))
      - 1 / 2 * (2 * z * log (1 * z + s)) - 1 / 2 * (2 * z * log (-s * z + 1)) +
      (log (1 - s) + log (1 + s)) * (2 * z) + 2 * z * log (1 * z + 0)))
      (fun z => 2 * z * i2P1Fw (i2P1Fr s z)) (uIoo s 1) := by
    intro z hz
    rw [uIoo_of_le hs1.le] at hz
    simp only [i2P1FZ_w_right ⟨hs0, hs1⟩ hz]
    ring
  have iL' := (iL.const_mul (-(1 / 2))).add iSL
  have iR' := (iR.const_mul (-(1 / 2))).add iSR
  refine ⟨(iL'.congr_uIoo eL).trans (iR'.congr_uIoo eR), ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (iL'.congr_uIoo eL)
    (iR'.congr_uIoo eR), ← intervalIntegral.integral_congr_uIoo eL,
    ← intervalIntegral.integral_congr_uIoo eR, intervalIntegral.integral_add
    (iL.const_mul _) iSL, intervalIntegral.integral_add (iR.const_mul _) iSR,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, vL, vR, vSL, vSR]
  have e1 : log (-s * s + 1) = log (1 - s) + log (1 + s) := by
    rw [← log_mul (by linarith) (by linarith)]; ring_nf
  have e2 : log (1 - s ^ 2) = log (1 - s) + log (1 + s) := by
    rw [← log_mul (by linarith) (by linarith)]; ring_nf
  have e4 : log (-1 * s + 1) = log (1 - s) := by ring_nf
  have e9 : log (s ^ 2) = 2 * log s := by rw [log_pow]; push_cast; ring
  simp only [i2P1FZP, i2P1FI, e1, e2, e4, e9, mul_zero, zero_add, mul_one, one_mul, add_zero,
    log_one]
  field_simp
  ring_nf

/-- **The outer integral**: `t = s²` turns `∫₀¹ 8 (1 + s²) / (s (1 - s²)) log² s I(s²) ds` into
`QED.ThreeLoopD.i2P1FEnd_value`. -/
theorem i2P1FZ_outer :
    ∫ s in Ioo (0 : ℝ) 1, 8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2 * i2P1FI (s ^ 2) =
      2 * π ^ 4 / 45 - 4 * zeta3 + π ^ 2 / 3 := by
  have himg : (fun s : ℝ => s ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨s, ⟨h0, h1⟩, rfl⟩
      exact ⟨by positivity, by nlinarith⟩
    · rintro ⟨h0, h1⟩
      refine ⟨Real.sqrt t, ⟨Real.sqrt_pos.2 h0, ?_⟩, Real.sq_sqrt h0.le⟩
      rw [Real.sqrt_lt' one_pos]
      linarith
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun s : ℝ => s ^ 2)
    (f' := fun s => 2 * s) (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))
    (fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt)
    (fun a ha b hb hab => (sq_eq_sq₀ ha.1.le hb.1.le).1 hab)
    (fun t => (1 + t) / (t * (1 - t)) * log t ^ 2 * i2P1FI t)
  rw [himg] at h
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    i2P1FEnd_value.2] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  have h0 : s ≠ 0 := hs.1.ne'
  have h1 : 1 - s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
  simp only [smul_eq_mul, abs_of_pos (by linarith [hs.1] : (0 : ℝ) < 2 * s), log_pow]
  push_cast
  field_simp
  ring

/-- **The `ℱ`-part as a double integral**:
`∫₀¹ ds 8 (1 + s²) / (s (1 - s²)) log² s ∫₀¹ dz 2 z w(r(s, z)) = 2 π⁴ / 45 - 4 ζ(3) + π² / 3`. -/
theorem i2P1FZ_value :
    ∫ s in Ioo (0 : ℝ) 1, 8 * (1 + s ^ 2) / (s * (1 - s ^ 2)) * log s ^ 2 *
      ∫ z in (0 : ℝ)..1, 2 * z * i2P1Fw (i2P1Fr s z) =
        2 * π ^ 4 / 45 - 4 * zeta3 + π ^ 2 / 3 := by
  rw [← i2P1FZ_outer]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  simp only [(i2P1FZ_inner hs).2]

end QED.ThreeLoopD
