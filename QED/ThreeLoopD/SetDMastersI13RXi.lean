/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13RCoef

/-!
# Set (d), master `I₁₃`: the variable `ξ` and the first bubble coefficient

For `t ≥ 0` let `ξ(t) = (t + 2 - √(t (t + 4)))/2 ∈ (0, 1]` (`QED.ThreeLoopD.i13Xi`), the root of
`ξ² - (t + 2) ξ + 1 = 0`, so that `t = (1 - ξ)²/ξ` and
`1 + x(1 - x) t = (ξ + x(1 - ξ))(1 - x(1 - ξ))/ξ`. It decreases from `1` to `0`, with
`ξ'(t) = -ξ²/(1 - ξ²)`.

In this variable the first coefficient of the bubble is elementary:

  `∫₀¹ log (1 + x(1 - x) t) dx = -2 - log ξ (1 + ξ)/(1 - ξ)` (`QED.ThreeLoopD.i13_integral_log`).

## Main results

* `QED.ThreeLoopD.i13Xi`, `QED.ThreeLoopD.hasDerivAt_i13Xi`, `QED.ThreeLoopD.i13Xi_t`.
* `QED.ThreeLoopD.i13_integral_log`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopD

/-- `ξ(t) = (t + 2 - √(t (t + 4)))/2`. -/
noncomputable def i13Xi (t : ℝ) : ℝ := (t + 2 - √(t * (t + 4))) / 2

theorem i13_sqrt_facts {t : ℝ} (ht : 0 ≤ t) :
    √(t * (t + 4)) ^ 2 = t * (t + 4) ∧ 0 ≤ √(t * (t + 4)) ∧ t ≤ √(t * (t + 4)) ∧
      √(t * (t + 4)) < t + 2 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ t * (t + 4))
  have h0 := Real.sqrt_nonneg (t * (t + 4))
  refine ⟨hs, h0, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem i13Xi_pos {t : ℝ} (ht : 0 ≤ t) : 0 < i13Xi t := by
  obtain ⟨-, -, -, h⟩ := i13_sqrt_facts ht
  unfold i13Xi; linarith

theorem i13Xi_le_one {t : ℝ} (ht : 0 ≤ t) : i13Xi t ≤ 1 := by
  obtain ⟨-, -, h, -⟩ := i13_sqrt_facts ht
  unfold i13Xi; linarith

theorem i13Xi_lt_one {t : ℝ} (ht : 0 < t) : i13Xi t < 1 := by
  obtain ⟨hs, h0, -, -⟩ := i13_sqrt_facts ht.le
  have : t < √(t * (t + 4)) := by nlinarith
  unfold i13Xi; linarith

theorem i13Xi_zero : i13Xi 0 = 1 := by unfold i13Xi; simp

/-- `ξ² - (t + 2) ξ + 1 = 0`. -/
theorem i13Xi_quad {t : ℝ} (ht : 0 ≤ t) : i13Xi t ^ 2 - (t + 2) * i13Xi t + 1 = 0 := by
  obtain ⟨hs, -, -, -⟩ := i13_sqrt_facts ht
  unfold i13Xi
  linear_combination hs / 4

/-- `t = (1 - ξ)²/ξ`. -/
theorem i13Xi_t {t : ℝ} (ht : 0 ≤ t) : t = (1 - i13Xi t) ^ 2 / i13Xi t := by
  have h0 := i13Xi_pos ht
  have hq := i13Xi_quad ht
  field_simp
  linear_combination -hq

theorem continuous_i13Xi : Continuous i13Xi := by unfold i13Xi; fun_prop

theorem i13_sqrt_eq_xi {t : ℝ} (ht : 0 ≤ t) :
    √(t * (t + 4)) = (1 - i13Xi t ^ 2) / i13Xi t := by
  have h0 := i13Xi_pos ht
  have hq := i13Xi_quad ht
  have hsdef : √(t * (t + 4)) = t + 2 - 2 * i13Xi t := by unfold i13Xi; ring
  rw [eq_div_iff h0.ne']
  linear_combination i13Xi t * hsdef - hq

theorem hasDerivAt_i13Xi {t : ℝ} (ht : 0 < t) :
    HasDerivAt i13Xi (-i13Xi t ^ 2 / (1 - i13Xi t ^ 2)) t := by
  have hpos : 0 < t * (t + 4) := by positivity
  have hd : HasDerivAt (fun t : ℝ => t * (t + 4)) (2 * t + 4) t :=
    ((hasDerivAt_id' t).mul ((hasDerivAt_id' t).add_const 4)).congr_deriv (by ring)
  have h := (((hasDerivAt_id' t).add_const 2).sub (hd.sqrt hpos.ne')).div_const 2
  show HasDerivAt (fun t => (t + 2 - √(t * (t + 4))) / 2) _ t
  refine h.congr_deriv ?_
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hq := i13Xi_quad ht.le
  have h1 : 1 - i13Xi t ^ 2 ≠ 0 := by nlinarith
  have ht2 : 2 * t + 4 = 2 * (1 + i13Xi t ^ 2) / i13Xi t := by
    field_simp; linear_combination -2 * hq
  rw [i13_sqrt_eq_xi ht.le, ht2]
  field_simp
  ring

theorem tendsto_i13Xi_atTop : Tendsto i13Xi atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_atTop.2 ⟨0, fun t ht => i13Xi_pos ht⟩⟩
  have hb : ∀ t, 0 ≤ t → i13Xi t ≤ 2 / (t + 2) := by
    intro t ht
    have h0 := i13Xi_pos ht
    have hq := i13Xi_quad ht
    rw [le_div_iff₀ (by linarith)]
    nlinarith [i13Xi_le_one ht]
  refine squeeze_zero' (eventually_atTop.2 ⟨0, fun t ht => (i13Xi_pos ht).le⟩)
    (eventually_atTop.2 ⟨0, hb⟩) ?_
  have : Tendsto (fun t : ℝ => t + 2) atTop atTop := tendsto_atTop_add_const_right _ 2 tendsto_id
  simpa [div_eq_mul_inv] using this.inv_tendsto_atTop.const_mul 2

/-! ### The first bubble coefficient -/

/-- `∫₀¹ log (1 + x(1 - x) t) dx = -2 - log ξ (1 + ξ)/(1 - ξ)` for `t > 0`. -/
theorem i13_integral_log {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioo (0 : ℝ) 1, Real.log (1 + x * (1 - x) * t) =
      -2 - Real.log (i13Xi t) * (1 + i13Xi t) / (1 - i13Xi t) := by
  set ξ := i13Xi t with hξ
  have h0 : 0 < ξ := i13Xi_pos ht.le
  have h1 : ξ < 1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  rw [← hξ] at hT
  set a := 1 - ξ with ha
  have ha0 : 0 < a := by linarith
  have hu : ∀ x ∈ Icc (0 : ℝ) 1, 0 < ξ + x * a := fun x hx => by nlinarith [hx.1]
  have hv : ∀ x ∈ Icc (0 : ℝ) 1, 0 < 1 - x * a := fun x hx => by nlinarith [hx.2]
  set G : ℝ → ℝ := fun x => ((ξ + x * a) * Real.log (ξ + x * a) - (ξ + x * a)) / a -
    ((1 - x * a) * Real.log (1 - x * a) - (1 - x * a)) / a - x * Real.log ξ
  have hG : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt G (Real.log (1 + x * (1 - x) * t)) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have hu' := hu x hx
    have hv' := hv x hx
    have d1 : HasDerivAt (fun x => ξ + x * a) a x := by
      simpa using ((hasDerivAt_id x).mul_const a).const_add ξ
    have d2 : HasDerivAt (fun x => 1 - x * a) (-a) x := by
      simpa using ((hasDerivAt_id x).mul_const a).const_sub 1
    have e1 := ((d1.mul (d1.log hu'.ne')).sub d1).div_const a
    have e2 := ((d2.mul (d2.log hv'.ne')).sub d2).div_const a
    have e3 := (hasDerivAt_id x).mul_const (Real.log ξ)
    refine ((e1.sub e2).sub e3).congr_deriv ?_
    have hprod : 1 + x * (1 - x) * t = (ξ + x * a) * (1 - x * a) / ξ := by
      rw [hT]; field_simp; ring
    rw [hprod, Real.log_div (by positivity) h0.ne', Real.log_mul hu'.ne' hv'.ne']
    have hu2 : ξ + a * x ≠ 0 := by rw [mul_comm]; exact hu'.ne'
    have hv2 : 1 - a * x ≠ 0 := by rw [mul_comm]; exact hv'.ne'
    field_simp
    ring
  have hint : IntervalIntegrable (fun x => Real.log (1 + x * (1 - x) * t)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact ContinuousOn.log (by fun_prop) fun x hx => (i13_base_pos hx ht.le).ne'
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint]
  have e1 : ξ + a = 1 := by rw [ha]; ring
  have e2 : 1 - a = ξ := by rw [ha]; ring
  simp only [G, zero_mul, add_zero, sub_zero, one_mul]
  rw [e1, e2, Real.log_one]
  field_simp
  ring

end QED.ThreeLoopD
