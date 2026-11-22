/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Set (a), stage D: the elementary integrals `∫₀^Y vᵖ/(A + bv)ᵏ`, `k = 1, 2`

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification). On the outer Feynman simplex of each class the denominator is
affine in one parameter, `D = A + bv` with `A, b > 0`, and the numerators are polynomials in `v`.
The inner integrals are the elementary moments

* `ksDJ1 A b Y p = ∫₀^Y vᵖ/(A + bv) dv`, with `ksDJ1 0 = log((A + bY)/A)/b` and
  `ksDJ1 (p+1) = Y^{p+1}/((p+1)b) - (A/b) ksDJ1 p`;
* `ksDJ2 A b Y p = ∫₀^Y vᵖ/(A + bv)² dv`, with `ksDJ2 0 = Y/(A(A + bY))` and
  `ksDJ2 (p+1) = ksDJ1 p/b - (A/b) ksDJ2 p`.

Main results: `ksD_integral_J1`, `ksD_integral_J2` (for `A > 0`, `b > 0`, `Y ≥ 0`).
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

/-- The moments `∫₀^Y vᵖ/(A + bv) dv`. -/
noncomputable def ksDJ1 (A b Y : ℝ) : ℕ → ℝ
  | 0 => Real.log ((A + b * Y) / A) / b
  | p + 1 => Y ^ (p + 1) / (((p : ℝ) + 1) * b) - A / b * ksDJ1 A b Y p

/-- The moments `∫₀^Y vᵖ/(A + bv)² dv`. -/
noncomputable def ksDJ2 (A b Y : ℝ) : ℕ → ℝ
  | 0 => Y / (A * (A + b * Y))
  | p + 1 => ksDJ1 A b Y p / b - A / b * ksDJ2 A b Y p

variable {A b Y : ℝ}

theorem ksD_lin_pos (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) :
    ∀ v ∈ uIcc (0 : ℝ) Y, 0 < A + b * v := fun v hv => by
  rw [uIcc_of_le hY] at hv
  have := mul_nonneg hb.le hv.1
  linarith

theorem ksD_intervalIntegrable_J (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) (p k : ℕ) :
    IntervalIntegrable (fun v : ℝ => v ^ p / (A + b * v) ^ k) volume 0 Y := by
  refine ContinuousOn.intervalIntegrable ?_
  exact (continuousOn_pow p).div (by fun_prop) fun v hv =>
    pow_ne_zero k (ksD_lin_pos hA hb hY v hv).ne'

theorem ksD_integral_J1 (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) (p : ℕ) :
    ∫ v in (0 : ℝ)..Y, v ^ p / (A + b * v) = ksDJ1 A b Y p := by
  have hpos := ksD_lin_pos hA hb hY
  induction p with
  | zero =>
    have hderiv : ∀ v ∈ uIcc (0 : ℝ) Y,
        HasDerivAt (fun v => Real.log (A + b * v) / b) (v ^ 0 / (A + b * v)) v := by
      intro v hv
      have hL : HasDerivAt (fun v => A + b * v) b v := by
        simpa using ((hasDerivAt_id v).const_mul b).const_add A
      convert (hL.log (hpos v hv).ne').div_const b using 1
      field_simp
    have hc := ksD_intervalIntegrable_J hA hb hY 0 1
    simp only [pow_one] at hc
    rw [integral_eq_sub_of_hasDerivAt hderiv hc, ksDJ1, mul_zero, add_zero,
      Real.log_div (hpos Y right_mem_uIcc).ne' hA.ne', sub_div]
  | succ p ih =>
    have h : ∀ v ∈ uIcc (0 : ℝ) Y, v ^ (p + 1) / (A + b * v) =
        v ^ p / b - A / b * (v ^ p / (A + b * v)) := fun v hv => by
      have := (hpos v hv).ne'
      field_simp
      ring
    have hc := ksD_intervalIntegrable_J hA hb hY p 1
    simp only [pow_one] at hc
    rw [integral_congr h, integral_sub ((intervalIntegrable_pow p).div_const b)
      (hc.const_mul _), intervalIntegral.integral_div, intervalIntegral.integral_const_mul, ih,
      integral_pow,
      ksDJ1]
    simp only [zero_pow (Nat.succ_ne_zero p), sub_zero]
    field_simp

theorem ksD_integral_J2 (hA : 0 < A) (hb : 0 < b) (hY : 0 ≤ Y) (p : ℕ) :
    ∫ v in (0 : ℝ)..Y, v ^ p / (A + b * v) ^ 2 = ksDJ2 A b Y p := by
  have hpos := ksD_lin_pos hA hb hY
  induction p with
  | zero =>
    have hderiv : ∀ v ∈ uIcc (0 : ℝ) Y,
        HasDerivAt (fun v => -(1 / (b * (A + b * v)))) (v ^ 0 / (A + b * v) ^ 2) v := by
      intro v hv
      have h0 := (hpos v hv).ne'
      have hL : HasDerivAt (fun v => b * (A + b * v)) (b * b) v := by
        simpa using (((hasDerivAt_id v).const_mul b).const_add A).const_mul b
      convert ((hasDerivAt_const v (1 : ℝ)).div hL (mul_ne_zero hb.ne' h0)).neg using 1
      field_simp
      ring
    rw [integral_eq_sub_of_hasDerivAt hderiv (ksD_intervalIntegrable_J hA hb hY 0 2), ksDJ2]
    have hP := (hpos Y right_mem_uIcc).ne'
    simp only [mul_zero, add_zero]
    field_simp
    ring
  | succ p ih =>
    have h : ∀ v ∈ uIcc (0 : ℝ) Y, v ^ (p + 1) / (A + b * v) ^ 2 =
        1 / b * (v ^ p / (A + b * v)) - A / b * (v ^ p / (A + b * v) ^ 2) := fun v hv => by
      have := (hpos v hv).ne'
      field_simp
      ring
    have hc := ksD_intervalIntegrable_J hA hb hY p 1
    simp only [pow_one] at hc
    rw [integral_congr h, integral_sub (hc.const_mul _)
      ((ksD_intervalIntegrable_J hA hb hY p 2).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, ih, ksD_integral_J1 hA hb hY p, ksDJ2]
    ring

end QED.ChainProof.SetAKS

end
