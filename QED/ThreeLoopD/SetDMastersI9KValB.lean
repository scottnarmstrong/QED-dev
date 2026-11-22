/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9KValId
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₉`: `K₂`, `K₃` in terms of `M₂`, `M₃`

The low coefficients of `M` and `B = B(1 - ε, 1 - ε)` are `M₀ = 0`, `B₀ = 1`, `B₁ = 2`,
`B₂ = 4 - π²/6` (`∫₀¹ log² (x (1 - x)) dx = 8 - π²/3`, by an explicit antiderivative with a
`Li₂ (1 - x)` term), `B₃ = 8 - 2ζ(3) - π²/3` (from `∫₀¹ log³ x = -6` and
`∫₀¹ log² x log (1 - x) = 2ζ(3) - 6 + π²/3`). With `K₀ = -3/2`, `K₁ = -10` and
`QED.ThreeLoopD.i9KCoeff_rel` this gives `M₁ = -15/2` and

  `K₂ = M₂ + 17/2 + π²/4`,  `K₃ = M₃ - 2 M₂ + 29/2 - 3 B₃ / 2 - π²/12`.

So the targets for `K₂`, `K₃` are equivalent to `M₂ = -111/2 + 15π²/2 + 3ζ(3)` and
`M₃ = -621/2 + 235π²/4 + 147ζ(3) - π⁴/12 - 72π² log 2`.

## Main results

* `QED.ThreeLoopD.i9BCoeff_two`: `B₂ = 4 - π²/6`.
* `QED.ThreeLoopD.i9KCoeff_two_eq`, `QED.ThreeLoopD.i9KCoeff_three_eq`: `K₂`, `K₃` through `M₂`,
  `M₃`, `B₃`.
* `QED.ThreeLoopD.i9KCoeff_two_of_M`: `K₂ = -47 + 31π²/4 + 3ζ(3)` from
  `M₂ = -111/2 + 15π²/2 + 3ζ(3)`.
* `QED.ThreeLoopD.i9BCoeff_three`: `B₃ = 8 - 2ζ(3) - π²/3`.
* `QED.ThreeLoopD.hasTruncLaurent_i9K_of_M`: the expansion of `K` through `ε³`, given `M₂` and
  `M₃`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

theorem i9MCoeff_zero : i9MCoeff 0 = 0 := by
  simp [i9MCoeff, i9MCoeffFun]

theorem i9BCoeff_zero : i9BCoeff 0 = 1 := by
  simp [i9BCoeff]

theorem i9BCoeff_one : i9BCoeff 1 = 2 := by
  have hL : ∀ x ∈ Ioo (0 : ℝ) 1, Real.log (x * (1 - x)) ≤ 0 := fun x hx =>
    Real.log_nonpos (i9_c_pos hx).le (by nlinarith [hx.1, hx.2])
  have h := i9_Ioo_of_nonpos_cont (F := fun x => x * Real.log x - x -
      (1 + -1 * x) * Real.log (1 + -1 * x) - x)
    (f := fun x => Real.log (x * (1 - x)))
    (by have := Real.continuous_mul_log; have := i9_continuous_mulLog 1 (-1); fun_prop)
    (fun x hx => by
      have h1 := i9_hasDerivAt_mulLog' hx.1
      have h2 := i9_hasDerivAt_mulLog (a := 1) (b := -1) (x := x) (by linarith [hx.2])
      refine (((h1.sub (hasDerivAt_id' x)).sub h2).sub (hasDerivAt_id' x)).congr_deriv ?_
      rw [Real.log_mul hx.1.ne' (by linarith [hx.2])]
      ring_nf) hL
  rw [i9BCoeff, show (fun x : ℝ => (-Real.log (x * (1 - x))) ^ 1 / (Nat.factorial 1 : ℝ)) =
    fun x => -Real.log (x * (1 - x)) by funext x; simp, integral_neg, h.2]
  norm_num

/-- `∫₀¹ log² (x (1 - x)) dx = 8 - π²/3`. -/
theorem integral_log_mul_one_sub_sq :
    ∫ x in Ioo (0 : ℝ) 1, Real.log (x * (1 - x)) ^ 2 = 8 - π ^ 2 / 3 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => x * (Real.log x * Real.log x) -
      2 * (x * Real.log x) + 2 * x - ((1 - x) * (Real.log (1 - x) * Real.log (1 - x)) -
      2 * ((1 - x) * Real.log (1 - x)) + 2 * (1 - x)) +
      2 * (x * (Real.log x * Real.log (1 - x)) + (1 - x) * Real.log (1 - x) + x +
        Li₂ (1 - x) - x * Real.log x + x)) (Real.log (x * (1 - x)) ^ 2) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hi := hasDerivAt_id' x
    have hu := (hasDerivAt_id' x).const_sub 1
    have hl := Real.hasDerivAt_log hx0.ne'
    have hm := ((hasDerivAt_id' x).const_sub 1).log hx1.ne'
    have hLi := (hasDerivAt_Li₂' (x := 1 - x) ⟨hx1, by linarith [hx.1]⟩).comp x hu
    have hG := ((((hi.mul (hl.mul hl)).sub ((hi.mul hl).const_mul 2)).add
      (hi.const_mul 2)).sub (((hu.mul (hm.mul hm)).sub ((hu.mul hm).const_mul 2)).add
      (hu.const_mul 2))).add (((((((hi.mul (hl.mul hm)).add (hu.mul hm)).add hi).add
      hLi).sub (hi.mul hl)).add hi).const_mul 2)
    convert hG using 1
    · rfl
    simp only [Pi.mul_apply]
    rw [Real.log_mul hx0.ne' hx1.ne', sub_sub_cancel]
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ Real.log (x * (1 - x)) ^ 2 := fun x _ => sq_nonneg _
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 1)
  have hsq0 : Tendsto (fun x => x * (Real.log x * Real.log x)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_mul_log_sq_zero.congr fun x => by ring
  have hu0 : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx0
  have hu1 : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx1
  have hlog1 : Tendsto (fun x : ℝ => Real.log x) (𝓝[<] 1) (𝓝 0) := by
    simpa using ((Real.continuousAt_log one_ne_zero).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
  have hm1 : Tendsto (fun x => (1 - x) * Real.log (1 - x)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have hmsq1 : Tendsto (fun x => (1 - x) * (Real.log (1 - x) * Real.log (1 - x))) (𝓝[<] 1)
      (𝓝 0) := (tendsto_mul_log_sq_zero.comp tendsto_one_sub_nhdsLT_one).congr fun x => by
    simp only [Function.comp]; ring
  have hLi0 : Tendsto (fun x => Li₂ (1 - x)) (𝓝[>] 0) (𝓝 (Li₂ 1)) :=
    tendsto_Li₂_comp (by norm_num) hu0 eventually_one_sub_mem_Icc
  have hLi1 : Tendsto (fun x => Li₂ (1 - x)) (𝓝[<] 1) (𝓝 (Li₂ 0)) := by
    refine tendsto_Li₂_comp (by norm_num) hu1 ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hA1 := (hsq0.sub (tendsto_mul_log_zero.const_mul 2)).add (hx0.const_mul 2)
  have hA2 := ((hu0.mul (tendsto_log_one_sub_zero.mul tendsto_log_one_sub_zero)).sub
    ((hu0.mul tendsto_log_one_sub_zero).const_mul 2)).add (hu0.const_mul 2)
  have hA3 := (((((hx0.mul tendsto_log_mul_log_one_sub_zero).add
    (hu0.mul tendsto_log_one_sub_zero)).add hx0).add hLi0).sub tendsto_mul_log_zero).add hx0
  have hA := (hA1.sub hA2).add (hA3.const_mul 2)
  have hB1 := ((hx1.mul (hlog1.mul hlog1)).sub ((hx1.mul hlog1).const_mul 2)).add
    (hx1.const_mul 2)
  have hB2 := (hmsq1.sub (hm1.const_mul 2)).add (hu1.const_mul 2)
  have hB3 := (((((hx1.mul tendsto_log_mul_log_one_sub_one).add hm1).add hx1).add hLi1).sub
    (hx1.mul hlog1)).add hx1
  have hB := (hB1.sub hB2).add (hB3.const_mul 2)
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, h.2,
    Li₂_one, Li₂_zero]
  ring

/-- **`B₂ = 4 - π²/6`**. -/
theorem i9BCoeff_two : i9BCoeff 2 = 4 - π ^ 2 / 6 := by
  rw [i9BCoeff, show (fun x : ℝ => (-Real.log (x * (1 - x))) ^ 2 / (Nat.factorial 2 : ℝ)) =
    fun x => Real.log (x * (1 - x)) ^ 2 / 2 by funext x; simp [Nat.factorial],
    integral_div, integral_log_mul_one_sub_sq]
  ring

/-- **`M₁ = -15/2`**, from `K₁ = -10`. -/
theorem i9MCoeff_one : i9MCoeff 1 = -15 / 2 := by
  have h := i9KCoeff_rel.2.1
  rw [i9KCoeff_one, i9MCoeff_zero, i9BCoeff_one, i9BCoeff_zero] at h
  linarith

/-- **`K₂ = M₂ + 17/2 + π²/4`**. -/
theorem i9KCoeff_two_eq : i9KCoeff 2 = i9MCoeff 2 + 17 / 2 + π ^ 2 / 4 := by
  have h := i9KCoeff_rel.2.2.1
  rw [i9KCoeff_zero, i9MCoeff_zero, i9MCoeff_one, i9BCoeff_one, i9BCoeff_two] at h
  linarith

/-- **`K₃ = M₃ - 2 M₂ + 29/2 - 3 B₃ / 2 - π²/12`**. -/
theorem i9KCoeff_three_eq :
    i9KCoeff 3 = i9MCoeff 3 - 2 * i9MCoeff 2 + 29 / 2 - 3 * i9BCoeff 3 / 2 - π ^ 2 / 12 := by
  have h := i9KCoeff_rel.2.2.2
  rw [i9KCoeff_one, i9MCoeff_one, i9BCoeff_two] at h
  linarith

/-- **`K₂` from `M₂`**. -/
theorem i9KCoeff_two_of_M (h : i9MCoeff 2 = -111 / 2 + 15 * π ^ 2 / 2 + 3 * zeta3) :
    i9KCoeff 2 = -47 + 31 * π ^ 2 / 4 + 3 * zeta3 := by
  rw [i9KCoeff_two_eq, h]
  ring

/-! ### `B₃` -/

theorem i9_tendsto_mul_log_cube_zero :
    Tendsto (fun x : ℝ => x * (Real.log x * Real.log x * Real.log x)) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 3)).pow 3
  rw [zero_pow three_ne_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [mul_pow, ← rpow_natCast (x ^ (1 / 3 : ℝ)), ← rpow_mul hx.le]
  norm_num
  ring

/-- `∫₀¹ log³ x dx = -6`. -/
theorem i9_integral_log_cube :
    IntervalIntegrable (fun x => Real.log x * Real.log x * Real.log x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log x * Real.log x = -6 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => x * (Real.log x * Real.log x * Real.log x) -
      3 * (x * (Real.log x * Real.log x)) + 6 * (x * Real.log x) - 6 * x)
      (Real.log x * Real.log x * Real.log x) x := by
    intro x hx
    have hi := hasDerivAt_id' x
    have hl := Real.hasDerivAt_log hx.1.ne'
    have hG := (((hi.mul ((hl.mul hl).mul hl)).sub ((hi.mul (hl.mul hl)).const_mul 3)).add
      ((hi.mul hl).const_mul 6)).sub (hi.const_mul 6)
    convert hG using 1
    simp only [Pi.mul_apply]
    have : x ≠ 0 := hx.1.ne'
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, Real.log x * Real.log x * Real.log x ≤ 0 := fun x hx => by
    have := Real.log_nonpos hx.1.le hx.2.le
    nlinarith [mul_self_nonneg (Real.log x)]
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 1)
  have hlog1 : Tendsto (fun x : ℝ => Real.log x) (𝓝[<] 1) (𝓝 0) := by
    simpa using ((Real.continuousAt_log one_ne_zero).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
  have hsq0 : Tendsto (fun x => x * (Real.log x * Real.log x)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_mul_log_sq_zero.congr fun x => by ring
  have hA := ((i9_tendsto_mul_log_cube_zero.sub (hsq0.const_mul 3)).add
    (tendsto_mul_log_zero.const_mul 6)).sub (hx0.const_mul 6)
  have hB := (((hx1.mul ((hlog1.mul hlog1).mul hlog1)).sub ((hx1.mul (hlog1.mul hlog1)).const_mul
    3)).add ((hx1.mul hlog1).const_mul 6)).sub (hx1.const_mul 6)
  have h := intervalIntegrable_and_integral_eq_of_nonpos hd hf hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  norm_num

/-- `∫₀¹ log² x log (1 - x) dx = 2ζ(3) - 6 + π²/3`. -/
theorem i9_integral_log_sq_mul_log_one_sub :
    IntervalIntegrable (fun x => Real.log x * Real.log x * Real.log (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log x * Real.log (1 - x) =
        2 * zeta3 - 6 + π ^ 2 / 3 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x =>
      (x - 1) * (Real.log x * Real.log x * Real.log (1 - x)) -
      2 * (x * (Real.log x * Real.log (1 - x)) + (1 - x) * Real.log (1 - x) + x +
        Li₂ (1 - x) - x * Real.log x + x) - 2 * (Real.log x * Li₂ x) + 2 * Li₃ x -
      (x * (Real.log x * Real.log x) - 2 * (x * Real.log x) + 2 * x))
      (Real.log x * Real.log x * Real.log (1 - x)) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hi := hasDerivAt_id' x
    have hu := (hasDerivAt_id' x).const_sub 1
    have hv := (hasDerivAt_id' x).sub_const 1
    have hl := Real.hasDerivAt_log hx0.ne'
    have hm := ((hasDerivAt_id' x).const_sub 1).log hx1.ne'
    have hL2 := (hasDerivAt_Li₂' (x := 1 - x) ⟨hx1, by linarith [hx.1]⟩).comp x hu
    have hK2 := hasDerivAt_Li₂' hx
    have hK3 := hasDerivAt_Li₃' hx
    have hF := (((((hi.mul (hl.mul hm)).add (hu.mul hm)).add hi).add hL2).sub (hi.mul hl)).add hi
    have hG := (((((hv.mul ((hl.mul hl).mul hm)).sub (hF.const_mul 2)).sub
      ((hl.mul hK2).const_mul 2)).add (hK3.const_mul 2)).sub
      (((hi.mul (hl.mul hl)).sub ((hi.mul hl).const_mul 2)).add (hi.const_mul 2)))
    convert hG using 1
    try rfl
    simp only [Pi.mul_apply]
    rw [sub_sub_cancel]
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, Real.log x * Real.log x * Real.log (1 - x) ≤ 0 := fun x hx =>
    mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _)
      (Real.log_nonpos (by linarith [hx.2]) (by linarith [hx.1]))
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 1)
  have hu0 : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx0
  have hu1 : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx1
  have hlog1 : Tendsto (fun x : ℝ => Real.log x) (𝓝[<] 1) (𝓝 0) := by
    simpa using ((Real.continuousAt_log one_ne_zero).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
  have hm1 : Tendsto (fun x => (1 - x) * Real.log (1 - x)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have hsq0 : Tendsto (fun x => x * (Real.log x * Real.log x)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_mul_log_sq_zero.congr fun x => by ring
  have hLi0 : Tendsto (fun x => Li₂ (1 - x)) (𝓝[>] 0) (𝓝 (Li₂ 1)) :=
    tendsto_Li₂_comp (by norm_num) hu0 eventually_one_sub_mem_Icc
  have hLi1 : Tendsto (fun x => Li₂ (1 - x)) (𝓝[<] 1) (𝓝 (Li₂ 0)) := by
    refine tendsto_Li₂_comp (by norm_num) hu1 ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  -- the term `(x - 1) log² x log (1 - x)` at both ends
  have hT0 : Tendsto (fun x => (x - 1) * (Real.log x * Real.log x * Real.log (1 - x))) (𝓝[>] 0)
      (𝓝 0) := by
    have h := ((hx0.sub (tendsto_const_nhds (x := (1 : ℝ)))).mul
      (tendsto_mul_log_sq_zero.mul tendsto_log_one_sub_div_zero'))
    norm_num at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    field_simp
  have hT1 : Tendsto (fun x => (x - 1) * (Real.log x * Real.log x * Real.log (1 - x))) (𝓝[<] 1)
      (𝓝 0) := by
    have h := (hm1.mul (hlog1.mul hlog1)).neg
    rw [zero_mul, neg_zero] at h
    exact h.congr fun x => by ring
  have hF0 := (((((hx0.mul tendsto_log_mul_log_one_sub_zero).add
    (hu0.mul tendsto_log_one_sub_zero)).add hx0).add hLi0).sub tendsto_mul_log_zero).add hx0
  have hF1 := (((((hx1.mul tendsto_log_mul_log_one_sub_one).add hm1).add hx1).add hLi1).sub
    (hx1.mul hlog1)).add hx1
  have hA := ((((hT0.sub (hF0.const_mul 2)).sub (tendsto_log_mul_Li₂_zero.const_mul 2)).add
    (tendsto_Li₃_zero_right.const_mul 2)).sub ((hsq0.sub (tendsto_mul_log_zero.const_mul 2)).add
    (hx0.const_mul 2)))
  have hB := ((((hT1.sub (hF1.const_mul 2)).sub ((hlog1.mul tendsto_Li₂_one_left).const_mul
    2)).add (tendsto_Li₃_one_left.const_mul 2)).sub (((hx1.mul (hlog1.mul hlog1)).sub
    ((hx1.mul hlog1).const_mul 2)).add (hx1.const_mul 2)))
  have h := intervalIntegrable_and_integral_eq_of_nonpos hd hf hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2, Li₂_one, Li₂_zero]
  ring

/-- **`B₃ = 8 - 2ζ(3) - π²/3`**. -/
theorem i9BCoeff_three : i9BCoeff 3 = 8 - 2 * zeta3 - π ^ 2 / 3 := by
  obtain ⟨i1, v1⟩ := i9_integral_log_cube
  obtain ⟨i2, v2⟩ := i9_integral_log_sq_mul_log_one_sub
  have r : ∀ {f : ℝ → ℝ}, IntervalIntegrable f volume 0 1 →
      IntervalIntegrable (fun x => f (1 - x)) volume 0 1 := fun h => by
    simpa using (h.comp_sub_left 1).symm
  have e : ∀ f : ℝ → ℝ, ∫ x in (0 : ℝ)..1, f (1 - x) = ∫ x in (0 : ℝ)..1, f x := fun f => by
    simp
  have i1' := r i1
  have i2' := r i2
  simp only [sub_sub_cancel] at i1' i2'
  have v1' := e (fun x => Real.log x * Real.log x * Real.log x)
  have v2' := e (fun x => Real.log x * Real.log x * Real.log (1 - x))
  simp only [sub_sub_cancel] at v1' v2'
  have hS : ∫ x in (0 : ℝ)..1, Real.log (x * (1 - x)) ^ 3 =
      ∫ x in (0 : ℝ)..1, (Real.log x * Real.log x * Real.log x +
        Real.log (1 - x) * Real.log (1 - x) * Real.log (1 - x) +
        3 * (Real.log x * Real.log x * Real.log (1 - x)) +
        3 * (Real.log (1 - x) * Real.log (1 - x) * Real.log x)) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le zero_le_one] at hx
    rcases eq_or_ne x 1 with rfl | h1
    · simp
    · rw [Real.log_mul hx.1.ne' (sub_ne_zero.mpr h1.symm)]
      ring
  rw [i9BCoeff, show (fun x : ℝ => (-Real.log (x * (1 - x))) ^ 3 / (Nat.factorial 3 : ℝ)) =
    fun x => -(Real.log (x * (1 - x)) ^ 3 / 6) by funext x; simp [Nat.factorial]; ring,
    integral_neg, integral_div, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, hS,
    intervalIntegral.integral_add ((i1.add i1').add (i2.const_mul 3)) (i2'.const_mul 3),
    intervalIntegral.integral_add (i1.add i1') (i2.const_mul 3),
    intervalIntegral.integral_add i1 i1', intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, v1', v2', v1, v2]
  ring

/-- **`K₃` from `M₂`, `M₃`**. -/
theorem i9KCoeff_three_of_M (h2 : i9MCoeff 2 = -111 / 2 + 15 * π ^ 2 / 2 + 3 * zeta3)
    (h3 : i9MCoeff 3 = -621 / 2 + 235 * π ^ 2 / 4 + 147 * zeta3 - π ^ 4 / 12 -
      72 * π ^ 2 * Real.log 2) :
    i9KCoeff 3 = -197 + 265 * π ^ 2 / 6 + 144 * zeta3 - π ^ 4 / 12 -
      72 * π ^ 2 * Real.log 2 := by
  rw [i9KCoeff_three_eq, h3, h2, i9BCoeff_three]
  ring

/-- **`K` through `ε³`, given `M₂ = -111/2 + 15π²/2 + 3ζ(3)` and
`M₃ = -621/2 + 235π²/4 + 147ζ(3) - π⁴/12 - 72π² log 2`**. -/
theorem hasTruncLaurent_i9K_of_M
    (h2 : i9MCoeff 2 = -111 / 2 + 15 * π ^ 2 / 2 + 3 * zeta3)
    (h3 : i9MCoeff 3 = -621 / 2 + 235 * π ^ 2 / 4 + 147 * zeta3 - π ^ 4 / 12 -
      72 * π ^ 2 * Real.log 2) :
    HasTruncLaurent i9K i9KTarget 4 :=
  hasTruncLaurent_i9K_of_coeff23 (i9KCoeff_two_of_M h2) (i9KCoeff_three_of_M h2 h3)

end QED.ThreeLoopD
