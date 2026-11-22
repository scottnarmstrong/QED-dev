/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondPair
import QED.Polylog.Deriv
import QED.Polylog.ExtraIntegrals
import QED.Polylog.Landen
import QED.Polylog.Reflection

/-!
# Set (d), master `I₁₂`: the value of `B₁ + B₂ + J`

The integrands of `B₁`, `B₂` (`QED.ThreeLoopD.i12RBB1`, `QED.ThreeLoopD.i12RBB2`) and `J`
(`QED.ThreeLoopD.i12PairJ`) involve only the letters `0, 1, 2`. Their sum has, with
`L = log (1 - x/2)`, `ℓ = log 2` and
`P(t) = log t log² (1 - t) + 2 log (1 - t) Li₂ (1 - t) - 2 Li₃ (1 - t)` (an antiderivative of
`log² (1 - t) / t`, with `P(0⁺) = -2 ζ(3)`), the antiderivative

  `A(x) = 12 log x Li₂ (x/2) - 20 Li₃ (x/2) - 4 L Li₂ x - (2 + 20ℓ) Li₂ (x/2) - 10 P(x/2)
      + 4 Li₃ x + (12 + 4π² + 6ℓ²) L - 6ℓ L² + 2 L³ - 8 log x (ℓ L - L²/2)`

on `(0, 1)`. (The terms `4 log (1 - x) L / x` of `B₁` and `4 Li₂ x / (2 - x)` of `J`, which
separately need a weight-three constant outside `{ζ(3), π² ℓ, ℓ³}`, combine to the derivative of
`-4 L Li₂ x`.) With `A(0⁺) = 20 ζ(3)`, the values of `A(1⁻)` from `Li₂ (1/2)`, `Li₃ (1/2)`:

  `B₁ + B₂ + J = (-π² - 72ℓ + 6ℓ² - 20π²ℓ - 24ℓ³ - 96 ζ(3)) / 6`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12GoodPrim`.
* `QED.ThreeLoopD.integral_i12_good`.
* `QED.ThreeLoopD.deriv_i12RA3_add_deriv_i12RB3`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The antiderivative of `B₁ + B₂ + J` on `(0, 1)`. -/
noncomputable def i12GoodPrim (x : ℝ) : ℝ :=
  12 * Real.log x * Li₂ (x / 2) - 20 * Li₃ (x / 2) - 4 * Real.log (1 - x / 2) * Li₂ x -
    (2 + 20 * Real.log 2) * Li₂ (x / 2) -
    10 * ((Real.log x - Real.log 2) * Real.log (1 - x / 2) ^ 2 +
      2 * Real.log (1 - x / 2) * Li₂ (1 - x / 2) - 2 * Li₃ (1 - x / 2)) + 4 * Li₃ x +
    (12 + 4 * π ^ 2 + 6 * Real.log 2 ^ 2) * Real.log (1 - x / 2) -
    6 * Real.log 2 * Real.log (1 - x / 2) ^ 2 + 2 * Real.log (1 - x / 2) ^ 3 -
    8 * Real.log x * (Real.log 2 * Real.log (1 - x / 2) - Real.log (1 - x / 2) ^ 2 / 2)

theorem hasDerivAt_i12GoodPrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12GoodPrim (i12RBB1 x + i12RBB2 x + i12PairJ x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hh : (x / 2) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hh1 : 0 < 1 - x / 2 := by linarith
  have h2 : 0 < 2 - x := by linarith
  have hlin : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := (hasDerivAt_id' x).div_const 2
  have hL : HasDerivAt (fun y : ℝ => Real.log (1 - y / 2)) (-(1 / 2) / (1 - x / 2)) x :=
    (hlin.const_sub 1).log hh1.ne'
  have hlog := hasDerivAt_log hx0.ne'
  have hLi2h := (hasDerivAt_Li₂' hh).comp x hlin
  have hLi3h := (hasDerivAt_Li₃' hh).comp x hlin
  have hLi2 := hasDerivAt_Li₂' ⟨hx0, hx1⟩
  have hLi3 := hasDerivAt_Li₃' ⟨hx0, hx1⟩
  have hs : (1 - x / 2) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hlin' : HasDerivAt (fun y : ℝ => 1 - y / 2) (-(1 / 2)) x := by
    simpa using hlin.const_sub 1
  have hM2 := (hasDerivAt_Li₂' hs).comp x hlin'
  have hM3 := (hasDerivAt_Li₃' hs).comp x hlin'
  have hP := ((((hlog.sub_const (Real.log 2)).mul (hL.pow 2)).add
    ((hL.const_mul 2).mul hM2)).sub (hM3.const_mul 2))
  have h := ((((((((((hlog.const_mul 12).mul hLi2h).sub (hLi3h.const_mul 20)).sub
    ((hL.const_mul 4).mul hLi2)).sub (hLi2h.const_mul (2 + 20 * Real.log 2))).sub
    (hP.const_mul 10)).add (hLi3.const_mul 4)).add
    (hL.const_mul (12 + 4 * π ^ 2 + 6 * Real.log 2 ^ 2))).sub
    ((hL.pow 2).const_mul (6 * Real.log 2))).add ((hL.pow 3).const_mul 2)).sub
    ((hlog.const_mul 8).mul (((hL.const_mul (Real.log 2))).sub ((hL.pow 2).div_const 2)))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  rotate_left
  · simp only [i12GoodPrim, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
  have hx2 : Real.log (x / 2) = Real.log x - Real.log 2 := Real.log_div hx0.ne' two_ne_zero
  have hs2 : (1 : ℝ) - (1 - x / 2) = x / 2 := by ring
  have hlog4 : Real.log (4 / (2 - x)) = Real.log 2 - Real.log (1 - x / 2) := by
    rw [← Real.log_div (by norm_num) hh1.ne']
    congr 1; field_simp; ring
  have e1 : (1 : ℝ) - x / 2 ≠ 0 := hh1.ne'
  simp only [i12RBB1, i12RBB2, i12PairJ, hlog4, Function.comp_apply, Pi.pow_apply,
    Pi.sub_apply, Nat.cast_ofNat, hs2, hx2]
  norm_num
  field_simp
  ring

theorem tendsto_log_mul_Li₂_half_zero :
    Tendsto (fun x => Real.log x * Li₂ (x / 2)) (𝓝[>] 0) (𝓝 0) := by
  have hm : Tendsto (fun x : ℝ => x / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.div_const (2 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      exact div_pos hx two_pos
  have h1 := tendsto_log_mul_Li₂_zero.comp hm
  have h2 : Tendsto (fun x : ℝ => Li₂ (x / 2)) (𝓝[>] 0) (𝓝 (Li₂ 0)) :=
    tendsto_Li₂_comp (by norm_num) (hm.mono_right nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  rw [Li₂_zero] at h2
  have := h1.add (h2.const_mul (Real.log 2))
  rw [mul_zero, add_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  simp only [Function.comp_apply]
  rw [Real.log_div hx.ne' two_ne_zero]
  ring

theorem tendsto_i12GoodPrim_zero : Tendsto i12GoodPrim (𝓝[>] 0) (𝓝 (20 * zeta3)) := by
  have hm : Tendsto (fun x : ℝ => x / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.div_const (2 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      exact div_pos hx two_pos
  have hm0 := hm.mono_right nhdsWithin_le_nhds
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x / 2 ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hev1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨by linarith [hx.1], hx.2.le⟩
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hLi2h := tendsto_Li₂_comp (by norm_num) hm0 hev
  have hLi3h := tendsto_Li₃_comp (by norm_num) hm0 hev
  have hLi2 := tendsto_Li₂_comp (by norm_num) hid hev1
  have hLi3 := tendsto_Li₃_comp (by norm_num) hid hev1
  have hL : Tendsto (fun x : ℝ => Real.log (1 - x / 2)) (𝓝[>] 0) (𝓝 0) := by
    have : ContinuousAt (fun x : ℝ => Real.log (1 - x / 2)) 0 :=
      (continuousAt_const.sub (continuousAt_id.div_const 2)).log (by norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hQ : Tendsto (fun x : ℝ => Real.log x * (Real.log 2 * Real.log (1 - x / 2) -
      Real.log (1 - x / 2) ^ 2 / 2)) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => 2 * |x * Real.log x|) (𝓝[>] 0) (𝓝 (2 * |0|)) :=
      tendsto_mul_log_zero.abs.const_mul 2
    rw [abs_zero, mul_zero] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hl := abs_log_one_sub_half_le hx
    have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hv : |Real.log 2 * Real.log (1 - x / 2) - Real.log (1 - x / 2) ^ 2 / 2| ≤ 2 * x := by
      have hsq : Real.log (1 - x / 2) ^ 2 ≤ x ^ 2 := by
        have := sq_abs (Real.log (1 - x / 2)); nlinarith [abs_nonneg (Real.log (1 - x / 2))]
      have hm1 : |Real.log 2 * Real.log (1 - x / 2)| ≤ x := by
        rw [abs_mul, abs_of_pos hl20]; nlinarith [abs_nonneg (Real.log (1 - x / 2))]
      have := abs_le.1 hm1
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (Real.log (1 - x / 2)), hx.1, hx.2]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx.1]
    nlinarith [abs_nonneg (Real.log x)]
  have hQ2 : Tendsto (fun x : ℝ => Real.log x * Real.log (1 - x / 2) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => |x * Real.log x|) (𝓝[>] 0) (𝓝 |0|) :=
      tendsto_mul_log_zero.abs
    rw [abs_zero] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hl := abs_log_one_sub_half_le hx
    have hsq : Real.log (1 - x / 2) ^ 2 ≤ x := by
      have := sq_abs (Real.log (1 - x / 2))
      nlinarith [abs_nonneg (Real.log (1 - x / 2)), hx.1, hx.2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Real.log (1 - x / 2))), abs_mul,
      abs_of_pos hx.1]
    nlinarith [abs_nonneg (Real.log x)]
  have h1m : Tendsto (fun x : ℝ => 1 - x / 2) (𝓝[>] 0) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Continuous (fun x : ℝ => 1 - x / 2) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      show 1 - x / 2 < 1
      linarith
  have hM2 := tendsto_Li₂_one_left.comp h1m
  have hM3 := tendsto_Li₃_one_left.comp h1m
  have hP := (((hQ2.sub ((hL.pow 2).const_mul (Real.log 2))).add
    ((hL.const_mul 2).mul hM2)).sub (hM3.const_mul 2))
  rw [Li₂_zero] at hLi2h hLi2
  rw [Li₃_zero] at hLi3h hLi3
  have h := (((((((((((tendsto_log_mul_Li₂_half_zero.const_mul 12).sub (hLi3h.const_mul 20)).sub
    ((hL.const_mul 4).mul hLi2)).sub (hLi2h.const_mul (2 + 20 * Real.log 2))).sub
    (hP.const_mul 10)).add (hLi3.const_mul 4)).add
    (hL.const_mul (12 + 4 * π ^ 2 + 6 * Real.log 2 ^ 2))).sub
    ((hL.pow 2).const_mul (6 * Real.log 2))).add ((hL.pow 3).const_mul 2)).sub
    (hQ.const_mul 8)))
  convert h using 2
  · simp only [i12GoodPrim, Function.comp_apply]
    ring
  · ring

theorem tendsto_i12GoodPrim_one :
    Tendsto i12GoodPrim (𝓝[<] 1) (𝓝 (-20 * Li₃ (1 / 2) - 4 * (-Real.log 2) * (π ^ 2 / 6) -
      (2 + 20 * Real.log 2) * Li₂ (1 / 2) -
      10 * (-Real.log 2 * Real.log 2 ^ 2 + 2 * (-Real.log 2) * Li₂ (1 / 2) - 2 * Li₃ (1 / 2)) +
      4 * zeta3 + (12 + 4 * π ^ 2 + 6 * Real.log 2 ^ 2) * (-Real.log 2) -
      6 * Real.log 2 * Real.log 2 ^ 2 - 2 * Real.log 2 ^ 3)) := by
  have hh : ((1 : ℝ) / 2) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hlin : ContinuousAt (fun y : ℝ => y / 2) 1 := continuousAt_id.div_const 2
  have hlin' : ContinuousAt (fun y : ℝ => 1 - y / 2) 1 := continuousAt_const.sub hlin
  have hLi2 : ContinuousAt (fun y : ℝ => Li₂ (y / 2)) 1 :=
    ContinuousAt.comp (g := Li₂) (hasDerivAt_Li₂' hh).continuousAt hlin
  have hLi3 : ContinuousAt (fun y : ℝ => Li₃ (y / 2)) 1 :=
    ContinuousAt.comp (g := Li₃) (hasDerivAt_Li₃' hh).continuousAt hlin
  have hM2 : ContinuousAt (fun y : ℝ => Li₂ (1 - y / 2)) 1 :=
    ContinuousAt.comp (g := Li₂) (f := fun y : ℝ => 1 - y / 2)
      (by norm_num; exact (hasDerivAt_Li₂' hh).continuousAt) hlin'
  have hM3 : ContinuousAt (fun y : ℝ => Li₃ (1 - y / 2)) 1 :=
    ContinuousAt.comp (g := Li₃) (f := fun y : ℝ => 1 - y / 2)
      (by norm_num; exact (hasDerivAt_Li₃' hh).continuousAt) hlin'
  have hL : ContinuousAt (fun x : ℝ => Real.log (1 - x / 2)) 1 := hlin'.log (by norm_num)
  have hl : ContinuousAt Real.log 1 := continuousAt_log one_ne_zero
  have hc : ContinuousAt (fun x : ℝ => 12 * Real.log x * Li₂ (x / 2) - 20 * Li₃ (x / 2) -
      (2 + 20 * Real.log 2) * Li₂ (x / 2) -
      10 * ((Real.log x - Real.log 2) * Real.log (1 - x / 2) ^ 2 +
        2 * Real.log (1 - x / 2) * Li₂ (1 - x / 2) - 2 * Li₃ (1 - x / 2)) +
      (12 + 4 * π ^ 2 + 6 * Real.log 2 ^ 2) * Real.log (1 - x / 2) -
      6 * Real.log 2 * Real.log (1 - x / 2) ^ 2 + 2 * Real.log (1 - x / 2) ^ 3 -
      8 * Real.log x * (Real.log 2 * Real.log (1 - x / 2) - Real.log (1 - x / 2) ^ 2 / 2)) 1 := by
    fun_prop (disch := assumption)
  have hLt : Tendsto (fun x : ℝ => Real.log (1 - x / 2)) (𝓝[<] 1) (𝓝 (-Real.log 2)) := by
    have h := hL.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    rwa [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv] at h
  have h := ((hc.tendsto.mono_left nhdsWithin_le_nhds).sub
    ((hLt.const_mul 4).mul tendsto_Li₂_one_left)).add (tendsto_Li₃_one_left.const_mul 4)
  convert h using 2
  · simp only [i12GoodPrim]
    ring
  · have hl2 : Real.log (1 - 1 / 2) = -Real.log 2 := by
      rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
    rw [show Li₂ (1 - 1 / 2) = Li₂ (1 / 2) by norm_num,
      show Li₃ (1 - 1 / 2) = Li₃ (1 / 2) by norm_num]
    simp only [Real.log_one, hl2]
    ring

/-- **`B₁ + B₂ + J = (-π² - 72ℓ + 6ℓ² - 20π²ℓ - 24ℓ³ - 96 ζ(3)) / 6`.** -/
theorem integral_i12_good :
    (∫ ρ in Ioo (0 : ℝ) 1, i12RBB1 ρ) + (∫ x in Ioo (0 : ℝ) 1, i12RBB2 x) +
        (∫ ρ in Ioo (0 : ℝ) 1, i12PairJ ρ) =
      (-π ^ 2 - 72 * Real.log 2 + 6 * Real.log 2 ^ 2 - 20 * π ^ 2 * Real.log 2 -
        24 * Real.log 2 ^ 3 - 96 * zeta3) / 6 := by
  obtain ⟨h1, h2, -, -⟩ := deriv_i12RB3_zero_eq
  have hJ := integrableOn_i12PairJ
  have h12 : IntegrableOn (fun x => i12RBB1 x + i12RBB2 x) (Ioo 0 1) := h1.add h2
  have hsum : IntegrableOn (fun x => i12RBB1 x + i12RBB2 x + i12PairJ x) (Ioo 0 1) :=
    h12.add hJ
  rw [← integral_add h1 h2, ← integral_add h12 hJ, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
      (fun x hx => hasDerivAt_i12GoodPrim hx)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hsum)
      tendsto_i12GoodPrim_zero tendsto_i12GoodPrim_one]
  rw [Li₂_one_half, Li₃_one_half]
  ring

/-- **`R_A'(0) + R_B'(0) = Good + B₃ᵇ`**, with
`Good = (-π² - 72ℓ + 6ℓ² - 20π²ℓ - 24ℓ³ - 96 ζ(3)) / 6` and `B₃ᵇ` the integral of
`QED.ThreeLoopD.i12B3bad`. -/
theorem deriv_i12RA3_add_deriv_i12RB3 :
    deriv i12RA3 0 + deriv i12RB3 0 =
      (((-π ^ 2 - 72 * Real.log 2 + 6 * Real.log 2 ^ 2 - 20 * π ^ 2 * Real.log 2 -
        24 * Real.log 2 ^ 3 - 96 * zeta3) / 6 + ∫ x in Ioo (0 : ℝ) 1, i12B3bad x : ℝ) : ℂ) := by
  obtain ⟨-, -, -, hB⟩ := deriv_i12RB3_zero_eq
  obtain ⟨-, hP⟩ := deriv_i12RA3_add_i12RBB3
  rw [hB, ← integral_i12_good]
  push_cast at hP ⊢
  linear_combination hP

end QED.ThreeLoopD
