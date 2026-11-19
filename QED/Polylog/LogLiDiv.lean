/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.Polylog.LiCalculus
import QED.Polylog.LiLimits
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Weight-four integrals `∫₀¹ log x · (weight two)(±x) / x`

The weight-four part of the sixth-order set (c) integrand (`docs/HIGHER-LOOP-PLAN.md`) is
`(5/3) log s Φ(s)/s` with `Φ(s) = log s (log (1 - s) + 2 log (1 + s)) + 2 Li 2 s + 4 Li 2 (-s)`.
Its integral reduces to four classical values, each with an antiderivative built from
`P(f) = Li 4 f - log f · Li 3 f` (`QED.Polylog.hasDerivAt_Li_four_sub_comp`) at `f = ±x`:

* `∫₀¹ log x Li 2 x / x = -Li 4 1 = -π⁴/90`, antiderivative `-P(x)`;
* `∫₀¹ log x Li 2 (-x) / x = -Li 4 (-1) = 7π⁴/720`, antiderivative `-P(-x)`;
* `∫₀¹ log² x log (1 - x) / x = -2 Li 4 1 = -π⁴/45`, antiderivative
  `-(log² x Li 2 x + 2 P(x))`;
* `∫₀¹ log² x log (1 + x) / x = -2 Li 4 (-1) = 7π⁴/360`, antiderivative
  `-(log² x Li 2 (-x) + 2 P(-x))`.

Each integrand has constant sign on `(0, 1)`, so integrability comes with the value
(`QED.Polylog.intervalIntegrable_and_integral_eq_of_nonneg'`).

## Main results

* `QED.Polylog.intervalIntegrable_and_integral_log_mul_Li_two_div`
* `QED.Polylog.intervalIntegrable_and_integral_log_mul_Li_two_neg_div`
* `QED.Polylog.intervalIntegrable_and_integral_log_sq_mul_log_one_sub_div`
* `QED.Polylog.intervalIntegrable_and_integral_log_sq_mul_log_one_add_div`
* `QED.Polylog.integral_log_mul_setCPhi_div`: `∫₀¹ log s Φ(s)/s = π⁴/30`.
-/

public section

open Real Set Filter Topology MeasureTheory

namespace QED.Polylog

/-! ### Common data at `f = σ x`, `σ = ±1` -/

private theorem hasDerivAt_P (σ : ℝ) (hσ : |σ| = 1) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => Li 4 (σ * y) - log (σ * y) * Li 3 (σ * y))
      (-(log x * Li 2 (σ * x)) / x) x := by
  obtain ⟨h0, h1⟩ := hx
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  have hf : HasDerivAt (fun y => σ * y) σ x := by simpa using (hasDerivAt_id x).const_mul σ
  have ha : |σ * x| < 1 := by rw [abs_mul, hσ, one_mul, abs_of_pos h0]; exact h1
  have h := hasDerivAt_Li_four_sub_comp hf ha (mul_ne_zero hσ0 h0.ne')
  refine h.congr_deriv ?_
  have hl : log (σ * x) = log x := by
    rw [Real.log_mul hσ0 h0.ne', ← Real.log_abs σ, hσ, log_one, zero_add]
  rw [hl]
  field_simp

private theorem hasDerivAt_Q (σ : ℝ) (hσ : |σ| = 1) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y => log y ^ 2 * Li 2 (σ * y) + 2 * (Li 4 (σ * y) - log (σ * y) * Li 3 (σ * y)))
      (-(log x ^ 2 * log (1 - σ * x)) / x) x := by
  obtain ⟨h0, h1⟩ := hx
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  have hf : HasDerivAt (fun y => σ * y) σ x := by simpa using (hasDerivAt_id x).const_mul σ
  have ha : |σ * x| < 1 := by rw [abs_mul, hσ, one_mul, abs_of_pos h0]; exact h1
  have h2 := hasDerivAt_Li_two_comp hf ha (mul_ne_zero hσ0 h0.ne')
  have hl := ((hasDerivAt_log h0.ne').pow 2).mul h2
  have h := hl.add ((hasDerivAt_P σ hσ ⟨h0, h1⟩).const_mul 2)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

private theorem tendsto_zero_aux (σ : ℝ) (hσ : |σ| = 1) :
    Tendsto (fun y => Li 4 (σ * y) - log (σ * y) * Li 3 (σ * y)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun y => log y ^ 2 * Li 2 (σ * y)) (𝓝[>] 0) (𝓝 0) := by
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have hg : Tendsto (fun y => σ * y) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_const_mul σ).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hs : ∀ᶠ y in 𝓝[>] (0 : ℝ), σ * y ∈ Icc (-1 : ℝ) 1 := hev.mono fun y hy => by
    refine abs_le.1 ?_
    rw [abs_mul, hσ, one_mul, abs_of_pos hy.1]; exact hy.2.le
  refine ⟨tendsto_Li_sub_log_mul_Li_comp_zero (by norm_num) (by norm_num) hg hs, ?_⟩
  have hb : ∀ᶠ y in 𝓝[>] (0 : ℝ), |Li 2 (σ * y)| ≤ π ^ 2 / 6 * y := hev.mono fun y hy => by
    have hy1 : |σ * y| = y := by rw [abs_mul, hσ, one_mul, abs_of_pos hy.1]
    have := abs_Li_le (k := 2) (by norm_num) (y := σ * y) (by rw [hy1]; exact hy.2.le)
    rwa [hy1] at this
  exact (tendsto_mul_log_sq_of_abs_le hb).congr fun y => by ring

private theorem tendsto_one_aux (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun y => Li 4 (σ * y) - log (σ * y) * Li 3 (σ * y)) (𝓝[<] 1) (𝓝 (Li 4 σ)) ∧
      Tendsto (fun y => log y ^ 2 * Li 2 (σ * y)) (𝓝[<] 1) (𝓝 0) := by
  have hev : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have hm : σ ∈ Icc (-1 : ℝ) 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hg : Tendsto (fun y => σ * y) (𝓝[<] 1) (𝓝 σ) := by
    have := ((continuous_const_mul σ).tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hs : ∀ᶠ y in 𝓝[<] (1 : ℝ), σ * y ∈ Icc (-1 : ℝ) 1 := hev.mono fun y hy => by
    refine abs_le.1 ?_
    rw [abs_mul, hσa, one_mul, abs_of_pos hy.1]; exact hy.2.le
  have h1 := tendsto_Li_sub_log_mul_Li_comp (k := 4) (j := 3) (by norm_num) (by norm_num) hm
    hσ0 hg hs
  have hl : log σ = 0 := by rw [← Real.log_abs σ, hσa, log_one]
  rw [hl, zero_mul, sub_zero] at h1
  refine ⟨h1, ?_⟩
  have ly : Tendsto (fun y : ℝ => log y) (𝓝[<] 1) (𝓝 0) := by
    have := ((continuousAt_log one_ne_zero).tendsto).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    rwa [log_one] at this
  have := (ly.pow 2).mul (tendsto_Li_comp (k := 2) (by norm_num) hm hg hs)
  simpa using this

/-! ### The four integrals -/

/-- `∫₀¹ log x Li 2 x / x = -π⁴/90`. -/
theorem intervalIntegrable_and_integral_log_mul_Li_two_div :
    IntervalIntegrable (fun x => log x * Li 2 x / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x * Li 2 x / x = -(π ^ 4 / 90) := by
  have hσ : |(1 : ℝ)| = 1 := by norm_num
  obtain ⟨z0, -⟩ := tendsto_zero_aux 1 hσ
  obtain ⟨z1, -⟩ := tendsto_one_aux 1 (Or.inl rfl)
  have h := intervalIntegrable_and_integral_eq_of_nonpos' (a := 0) (b := 1)
    (F := fun y => -(Li 4 (1 * y) - log (1 * y) * Li 3 (1 * y)))
    (f := fun x => log x * Li 2 x / x) (A := -0) (B := -Li 4 1) zero_lt_one
    (fun x hx => by
      have := (hasDerivAt_P 1 hσ hx).neg
      refine this.congr_deriv ?_
      simp only [one_mul]; ring)
    (fun x hx => by
      have hL : 0 ≤ Li 2 x := by
        rw [Li_two, ← Li₂_zero]
        exact monotoneOn_Li₂ ⟨by norm_num, by norm_num⟩ ⟨by linarith [hx.1], hx.2.le⟩ hx.1.le
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (log_nonpos hx.1.le hx.2.le) hL) hx.1.le)
    z0.neg z1.neg
  rw [Li_four_one, neg_zero, sub_zero] at h
  exact h

/-- `∫₀¹ log x Li 2 (-x) / x = 7π⁴/720`. -/
theorem intervalIntegrable_and_integral_log_mul_Li_two_neg_div :
    IntervalIntegrable (fun x => log x * Li 2 (-x) / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x * Li 2 (-x) / x = 7 * π ^ 4 / 720 := by
  have hσ : |(-1 : ℝ)| = 1 := by norm_num
  obtain ⟨z0, -⟩ := tendsto_zero_aux (-1) hσ
  obtain ⟨z1, -⟩ := tendsto_one_aux (-1) (Or.inr rfl)
  have h := intervalIntegrable_and_integral_eq_of_nonneg' (a := 0) (b := 1)
    (F := fun y => -(Li 4 (-1 * y) - log (-1 * y) * Li 3 (-1 * y)))
    (f := fun x => log x * Li 2 (-x) / x) (A := -0) (B := -Li 4 (-1)) zero_lt_one
    (fun x hx => by
      have := (hasDerivAt_P (-1) hσ hx).neg
      refine this.congr_deriv ?_
      simp only [neg_one_mul]; ring)
    (fun x hx => by
      have hL : Li 2 (-x) ≤ 0 := by
        rw [Li_two, ← Li₂_zero]
        exact monotoneOn_Li₂ ⟨by linarith [hx.2], by linarith [hx.1]⟩ ⟨by norm_num, by norm_num⟩
          (by linarith [hx.1])
      exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (log_nonpos hx.1.le hx.2.le) hL) hx.1.le)
    z0.neg z1.neg
  rw [Li_four_neg_one, neg_zero, sub_zero] at h
  refine ⟨h.1, h.2.trans (by ring)⟩

/-- `∫₀¹ log² x log (1 - x) / x = -π⁴/45`. -/
theorem intervalIntegrable_and_integral_log_sq_mul_log_one_sub_div :
    IntervalIntegrable (fun x => log x ^ 2 * log (1 - x) / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x ^ 2 * log (1 - x) / x = -(π ^ 4 / 45) := by
  have hσ : |(1 : ℝ)| = 1 := by norm_num
  obtain ⟨z0, w0⟩ := tendsto_zero_aux 1 hσ
  obtain ⟨z1, w1⟩ := tendsto_one_aux 1 (Or.inl rfl)
  have h := intervalIntegrable_and_integral_eq_of_nonpos' (a := 0) (b := 1)
    (F := fun y => -(log y ^ 2 * Li 2 (1 * y) +
      2 * (Li 4 (1 * y) - log (1 * y) * Li 3 (1 * y))))
    (f := fun x => log x ^ 2 * log (1 - x) / x) (A := -(0 + 2 * 0))
    (B := -(0 + 2 * Li 4 1)) zero_lt_one
    (fun x hx => by
      have := (hasDerivAt_Q 1 hσ hx).neg
      refine this.congr_deriv ?_
      simp only [one_mul]; ring)
    (fun x hx => div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (log_nonpos (by linarith [hx.2]) (by linarith [hx.1]))) hx.1.le)
    (w0.add (z0.const_mul 2)).neg (w1.add (z1.const_mul 2)).neg
  rw [Li_four_one] at h
  refine ⟨h.1, h.2.trans (by ring)⟩

/-- `∫₀¹ log² x log (1 + x) / x = 7π⁴/360`. -/
theorem intervalIntegrable_and_integral_log_sq_mul_log_one_add_div :
    IntervalIntegrable (fun x => log x ^ 2 * log (1 + x) / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x ^ 2 * log (1 + x) / x = 7 * π ^ 4 / 360 := by
  have hσ : |(-1 : ℝ)| = 1 := by norm_num
  obtain ⟨z0, w0⟩ := tendsto_zero_aux (-1) hσ
  obtain ⟨z1, w1⟩ := tendsto_one_aux (-1) (Or.inr rfl)
  have h := intervalIntegrable_and_integral_eq_of_nonneg' (a := 0) (b := 1)
    (F := fun y => -(log y ^ 2 * Li 2 (-1 * y) +
      2 * (Li 4 (-1 * y) - log (-1 * y) * Li 3 (-1 * y))))
    (f := fun x => log x ^ 2 * log (1 + x) / x) (A := -(0 + 2 * 0))
    (B := -(0 + 2 * Li 4 (-1))) zero_lt_one
    (fun x hx => by
      have := (hasDerivAt_Q (-1) hσ hx).neg
      refine this.congr_deriv ?_
      simp only [neg_one_mul, sub_neg_eq_add]; ring)
    (fun x hx => div_nonneg (mul_nonneg (sq_nonneg _)
      (log_nonneg (by linarith [hx.1]))) hx.1.le)
    (w0.add (z0.const_mul 2)).neg (w1.add (z1.const_mul 2)).neg
  rw [Li_four_neg_one] at h
  refine ⟨h.1, h.2.trans (by ring)⟩

/-- The weight-two function `Φ(s) = log s (log (1 - s) + 2 log (1 + s)) + 2 Li 2 s + 4 Li 2 (-s)`
of the set (c) integrand (the bracket multiplying `R₅` in Balzani–Laporta–Passera,
arXiv:2112.05704, eq. (21), at `u = -s`). -/
noncomputable def setCPhi (s : ℝ) : ℝ :=
  log s * (log (1 - s) + 2 * log (1 + s)) + 2 * Li 2 s + 4 * Li 2 (-s)

/-- **The weight-four integral of set (c)**: `∫₀¹ log s Φ(s)/s = π⁴/30 = 3 ζ(4)`. -/
theorem integral_log_mul_setCPhi_div :
    IntervalIntegrable (fun s => log s * setCPhi s / s) volume 0 1 ∧
      ∫ s in (0 : ℝ)..1, log s * setCPhi s / s = π ^ 4 / 30 := by
  obtain ⟨iA, vA⟩ := intervalIntegrable_and_integral_log_mul_Li_two_div
  obtain ⟨iB, vB⟩ := intervalIntegrable_and_integral_log_mul_Li_two_neg_div
  obtain ⟨iC, vC⟩ := intervalIntegrable_and_integral_log_sq_mul_log_one_sub_div
  obtain ⟨iD, vD⟩ := intervalIntegrable_and_integral_log_sq_mul_log_one_add_div
  have e : (fun s => log s * setCPhi s / s) = fun s =>
      ((log s ^ 2 * log (1 - s) / s + 2 * (log s ^ 2 * log (1 + s) / s)) +
        2 * (log s * Li 2 s / s)) + 4 * (log s * Li 2 (-s) / s) := by
    funext s; unfold setCPhi; ring
  have i1 := (iC.add (iD.const_mul 2)).add (iA.const_mul 2)
  have i2 := i1.add (iB.const_mul 4)
  rw [e]
  refine ⟨i2, ?_⟩
  rw [intervalIntegral.integral_add i1 (iB.const_mul 4),
    intervalIntegral.integral_add (iC.add (iD.const_mul 2)) (iA.const_mul 2),
    intervalIntegral.integral_add iC (iD.const_mul 2), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, vA, vB, vC, vD]
  ring

end QED.Polylog
