/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A Hölder bound for complex powers of nonnegative reals

For `0 ≤ q, p ≤ 2` and `1/2 ≤ re z ≤ 3/2`,

  `‖p ^ z - q ^ z‖ ≤ 4 ‖z‖ √|p - q|`

(`QED.DimReg.norm_cpow_sub_cpow_le_sqrt`). This is the estimate behind the subtraction of endpoint
values in parametric integrals whose integrand contains `P ^ z` with a polynomial `P` that
vanishes on the boundary: the difference of two values of `P ^ z` is controlled by the difference
of the values of `P`, uniformly for `z` in a strip, even where `P ^ z` is not differentiable.

The proof writes `p ^ z - q ^ z = z ∫_q^p t ^ (z - 1) dt` and bounds `t ^ (re z - 1) ≤ 2 t ^ (-1/2)`
on `(0, 2]`.
-/

@[expose] public section

open Complex Set intervalIntegral

namespace QED.DimReg

theorem rpow_re_sub_one_le {t σ : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) :
    t ^ (σ - 1) ≤ 2 * t ^ (-(1 / 2 : ℝ)) := by
  have e : t ^ (σ - 1) = t ^ (-(1 / 2 : ℝ)) * t ^ (σ - 1 / 2) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  have hb : t ^ (σ - 1 / 2) ≤ 2 := by
    calc t ^ (σ - 1 / 2) ≤ (2 : ℝ) ^ (σ - 1 / 2) :=
          Real.rpow_le_rpow ht.le ht2 (by linarith)
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  rw [e, mul_comm 2]
  exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le _)

theorem norm_cpow_sub_cpow_le_sqrt_of_le {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 2) {z : ℂ}
    (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 3 / 2) :
    ‖(p : ℂ) ^ z - (q : ℂ) ^ z‖ ≤ 4 * ‖z‖ * √(p - q) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at h1; linarith
  have hint := integral_cpow (a := q) (b := p) (r := z - 1)
    (Or.inl (by simp only [sub_re, one_re]; linarith))
  rw [sub_add_cancel] at hint
  have e : (p : ℂ) ^ z - (q : ℂ) ^ z = z * ∫ t in q..p, (t : ℂ) ^ (z - 1) := by
    rw [hint]; field_simp
  have hg : IntervalIntegrable (fun t : ℝ => 2 * t ^ (-(1 / 2 : ℝ))) MeasureTheory.volume q p :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 2
  have hb : ‖∫ t in q..p, (t : ℂ) ^ (z - 1)‖ ≤ ∫ t in q..p, 2 * t ^ (-(1 / 2 : ℝ)) := by
    refine norm_integral_le_of_norm_le hqp (MeasureTheory.ae_of_all _ fun t ht => ?_) hg
    have ht0 : 0 < t := lt_of_le_of_lt hq ht.1
    rw [norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
    exact rpow_re_sub_one_le ht0 (ht.2.trans hp) h1 h2
  have hv : ∫ t in q..p, 2 * t ^ (-(1 / 2 : ℝ)) = 4 * (√p - √q) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    norm_num; ring
  have hs : √p - √q ≤ √(p - q) := by
    have hpq : 0 ≤ p - q := by linarith
    rw [sub_le_iff_le_add, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hpq, Real.sq_sqrt hq, Real.sqrt_nonneg (p - q), Real.sqrt_nonneg q]
  rw [e, norm_mul]
  calc ‖z‖ * ‖∫ t in q..p, (t : ℂ) ^ (z - 1)‖ ≤ ‖z‖ * (4 * (√p - √q)) := by
        rw [← hv]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg z)
    _ ≤ ‖z‖ * (4 * √(p - q)) := by gcongr
    _ = 4 * ‖z‖ * √(p - q) := by ring

/-- **Hölder bound for complex powers.** For `0 ≤ p, q ≤ 2` and `1/2 ≤ re z ≤ 3/2`,
`‖p ^ z - q ^ z‖ ≤ 4 ‖z‖ √|p - q|`. -/
theorem norm_cpow_sub_cpow_le_sqrt {p q : ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hp : p ≤ 2) (hq : q ≤ 2)
    {z : ℂ} (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 3 / 2) :
    ‖(p : ℂ) ^ z - (q : ℂ) ^ z‖ ≤ 4 * ‖z‖ * √|p - q| := by
  rcases le_total q p with h | h
  · rw [abs_of_nonneg (by linarith)]; exact norm_cpow_sub_cpow_le_sqrt_of_le hq0 h hp h1 h2
  · rw [norm_sub_rev, abs_of_nonpos (by linarith), neg_sub]
    exact norm_cpow_sub_cpow_le_sqrt_of_le hp0 h hq h1 h2

/-- `‖p ^ z‖ ≤ √p` for `0 ≤ p ≤ 1` and `1/2 ≤ re z`. -/
theorem norm_cpow_le_sqrt {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1) {z : ℂ} (h1 : 1 / 2 ≤ z.re) :
    ‖(p : ℂ) ^ z‖ ≤ √p := by
  rw [norm_cpow_eq_rpow_re_of_nonneg hp0 (by linarith), Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge' hp0 hp (by norm_num) h1

end QED.DimReg
