/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R1
public import QED.Polylog.Landen
public import QED.Polylog.Reflection
public import QED.Polylog.LiCalculus
public import QED.Polylog.Deriv

/-!
# Set (d), master `I₁₃`: the second bubble coefficient

With `ξ = ξ(t)` (`QED.ThreeLoopD.i13Xi`), `a = 1 - ξ`, `c = 1 + ξ` and `x ∈ [0, 1]`, write
`u = ξ + x a`, `v = 1 - x a`, so that `u + v = c` and `1 + x(1 - x) t = u v / ξ`. The square
`L² = (log u + log v - log ξ)²` has the primitive `N(x)/a` (`QED.ThreeLoopD.i13BetaN`), which
involves `Li₂ (u/c)`. At the endpoints `u/c` is `ξ/c` and `1/c`; Euler's reflection and Landen's
identity turn `Li₂ (1/c) - Li₂ (ξ/c)` into `π²/6 + log ξ log (1 + ξ) + 2 Li₂ (-ξ)`, so

  `∫₀¹ log² (1 + x(1 - x) t) dx
    = 8 - (1 + ξ)/(1 - ξ) (4 Li₂ (-ξ) + 4 log ξ log (1 + ξ) - log² ξ - 4 log ξ + π²/3)`

(`QED.ThreeLoopD.i13_integral_log_sq`).

## Main results

* `QED.ThreeLoopD.i13_integral_log_sq`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- The numerator of the primitive of `log² (1 + x(1 - x) t)`, `ξ = ξ(t)`. -/
noncomputable def i13BetaN (ξ x : ℝ) : ℝ :=
  let a := 1 - ξ
  let c := 1 + ξ
  let u := ξ + x * a
  let v := 1 - x * a
  Real.log ξ ^ 2 * a * x + 2 * Real.log ξ * (u - v) - 2 * c * Li₂ (u / c) +
    u * Real.log u ^ 2 - 2 * (Real.log ξ * u - c * Real.log c + 2 * u) * Real.log u -
    2 * v * Real.log u * Real.log v - v * Real.log v ^ 2 +
    2 * (Real.log ξ * v - u + v + c) * Real.log v + 6 * u - 2 * v

theorem hasDerivAt_i13BetaN {ξ x : ℝ} (h0 : 0 < ξ) (h1 : ξ < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (i13BetaN ξ) ((1 - ξ) *
      (Real.log (ξ + x * (1 - ξ)) + Real.log (1 - x * (1 - ξ)) - Real.log ξ) ^ 2) x := by
  have hc0 : 0 < 1 + ξ := by linarith
  have hu : 0 < ξ + x * (1 - ξ) := by nlinarith [hx.1]
  have hv : 0 < 1 - x * (1 - ξ) := by nlinarith [hx.2]
  have huc : ξ + x * (1 - ξ) < 1 + ξ := by nlinarith [hx.1]
  have hs0 : 0 < (ξ + x * (1 - ξ)) / (1 + ξ) := div_pos hu hc0
  have hs1 : |(ξ + x * (1 - ξ)) / (1 + ξ)| < 1 := by
    rw [abs_of_pos hs0, div_lt_one hc0]; exact huc
  have d1 : HasDerivAt (fun x => ξ + x * (1 - ξ)) (1 - ξ) x := by
    simpa using ((hasDerivAt_id x).mul_const (1 - ξ)).const_add ξ
  have d2 : HasDerivAt (fun x => 1 - x * (1 - ξ)) (-(1 - ξ)) x := by
    simpa using ((hasDerivAt_id x).mul_const (1 - ξ)).const_sub 1
  have dL := (hasDerivAt_Li₂ hs1 hs0.ne').comp x (d1.div_const (1 + ξ))
  have lu := d1.log hu.ne'
  have lv := d2.log hv.ne'
  have hX := hasDerivAt_id' x
  have e := ((((((((((hX.const_mul (Real.log ξ ^ 2 * (1 - ξ))).add
    ((d1.sub d2).const_mul (2 * Real.log ξ))).sub (dL.const_mul (2 * (1 + ξ)))).add
    (d1.mul (lu.pow 2))).sub
    (((d1.const_mul (Real.log ξ)).sub_const ((1 + ξ) * Real.log (1 + ξ))).add
    (d1.const_mul 2) |>.mul lu |>.const_mul 2)).sub ((d2.mul lu).mul lv |>.const_mul 2)).sub
    (d2.mul (lv.pow 2))).add ((((d2.const_mul (Real.log ξ)).sub d1).add d2).add_const (1 + ξ)
    |>.mul lv |>.const_mul 2)).add (d1.const_mul 6)).sub (d2.const_mul 2))
  have hlc : Real.log (1 - (ξ + x * (1 - ξ)) / (1 + ξ)) =
      Real.log (1 - x * (1 - ξ)) - Real.log (1 + ξ) := by
    rw [show 1 - (ξ + x * (1 - ξ)) / (1 + ξ) = (1 - x * (1 - ξ)) / (1 + ξ) by field_simp; ring,
      Real.log_div hv.ne' hc0.ne']
  convert e using 1
  · funext y
    simp only [i13BetaN, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    rw [hlc]
    have hv' : 1 - x * (1 - ξ) ≠ 0 := hv.ne'
    have hu' : ξ + x * (1 - ξ) ≠ 0 := hu.ne'
    have hV : 1 - x * (1 - ξ) = 1 + ξ - (ξ + x * (1 - ξ)) := by ring
    rw [hV] at hv' ⊢
    generalize ξ + x * (1 - ξ) = U at hu' hv' ⊢
    field_simp
    ring

theorem i13_log_base_eq {t ξ x : ℝ} (ht : t = (1 - ξ) ^ 2 / ξ) (h0 : 0 < ξ)
    (hu : 0 < ξ + x * (1 - ξ)) (hv : 0 < 1 - x * (1 - ξ)) :
    Real.log (1 + x * (1 - x) * t) =
      Real.log (ξ + x * (1 - ξ)) + Real.log (1 - x * (1 - ξ)) - Real.log ξ := by
  have hprod : 1 + x * (1 - x) * t = (ξ + x * (1 - ξ)) * (1 - x * (1 - ξ)) / ξ := by
    rw [ht]; field_simp; ring
  rw [hprod, Real.log_div (by positivity) h0.ne', Real.log_mul hu.ne' hv.ne']

/-- `Li₂ (1/(1 + ξ)) - Li₂ (ξ/(1 + ξ)) = π²/6 + log ξ log (1 + ξ) + 2 Li₂ (-ξ)`. -/
theorem i13_Li₂_diff {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ ≤ 1) :
    Li₂ (1 / (1 + ξ)) - Li₂ (ξ / (1 + ξ)) =
      π ^ 2 / 6 + Real.log ξ * Real.log (1 + ξ) + 2 * Li₂ (-ξ) := by
  have hc0 : 0 < 1 + ξ := by linarith
  have hR := Li₂_add_Li₂_one_sub (x := ξ / (1 + ξ)) (by positivity)
    (by rw [div_le_one hc0]; linarith)
  have hL := Li₂_one_sub_inv_add_Li₂_one_sub (x := 1 / (1 + ξ))
    (by rw [le_div_iff₀ hc0]; linarith) (by rw [div_le_one hc0]; linarith)
  have e1 : 1 - ξ / (1 + ξ) = 1 / (1 + ξ) := by field_simp; ring
  have e2 : 1 - (1 / (1 + ξ))⁻¹ = -ξ := by field_simp; ring
  have e3 : 1 - 1 / (1 + ξ) = ξ / (1 + ξ) := by field_simp; ring
  rw [e1] at hR
  rw [e2, e3] at hL
  have hl : Real.log (1 / (1 + ξ)) = -Real.log (1 + ξ) := by rw [one_div, Real.log_inv]
  rw [Real.log_div h0.ne' hc0.ne', hl] at hR
  rw [hl] at hL
  linear_combination hR - 2 * hL

/-- **The second bubble coefficient**, `t > 0`, `ξ = ξ(t)`. -/
theorem i13_integral_log_sq {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioo (0 : ℝ) 1, Real.log (1 + x * (1 - x) * t) ^ 2 =
      8 - (1 + i13Xi t) / (1 - i13Xi t) * (4 * Li₂ (-i13Xi t) +
        4 * Real.log (i13Xi t) * Real.log (1 + i13Xi t) - Real.log (i13Xi t) ^ 2 -
        4 * Real.log (i13Xi t) + π ^ 2 / 3) := by
  set ξ := i13Xi t with hξ
  have h0 : 0 < ξ := i13Xi_pos ht.le
  have h1 : ξ < 1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  rw [← hξ] at hT
  have ha0 : 0 < 1 - ξ := by linarith
  have hc0 : 0 < 1 + ξ := by linarith
  have hG : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => i13BetaN ξ x / (1 - ξ))
      (Real.log (1 + x * (1 - x) * t) ^ 2) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have hu : 0 < ξ + x * (1 - ξ) := by nlinarith [hx.1]
    have hv : 0 < 1 - x * (1 - ξ) := by nlinarith [hx.2]
    refine ((hasDerivAt_i13BetaN h0 h1 hx).div_const (1 - ξ)).congr_deriv ?_
    rw [i13_log_base_eq hT h0 hu hv]
    field_simp
  have hint : IntervalIntegrable (fun x => Real.log (1 + x * (1 - x) * t) ^ 2) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (ContinuousOn.log (by fun_prop) fun x hx => (i13_base_pos hx ht.le).ne').pow 2
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint]
  have hD := i13_Li₂_diff h0 h1.le
  simp only [i13BetaN, zero_mul, add_zero, sub_zero, one_mul]
  have e1 : ξ + (1 - ξ) = 1 := by ring
  have e2 : 1 - (1 - ξ) = ξ := by ring
  rw [e1, e2, Real.log_one]
  field_simp
  linear_combination (-6 * (1 + ξ)) * hD
end QED.ThreeLoopD
