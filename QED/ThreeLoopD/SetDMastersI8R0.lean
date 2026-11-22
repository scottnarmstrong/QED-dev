/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8RemAnalytic
public import QED.ThreeLoopD.SetDMastersI13RXi
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Set (d), master `I₈`: the constant term `c₀ = 3/2` of `Rem`

**The angular average at `ε = 0`.** With `q = t + 4z²`, `s = √(t (t + 4))`, the function

  `F(z) = (t + 4)/(4s) arcsin (z √(t + 4) / √q) - arcsin z / 4`  (`QED.ThreeLoopD.i8F0`)

is a primitive of `√(1 - z²)/q` on `(-1, 1)`, continuous on `[0, 1]`, so
`J₀(t) = F(1) - F(0) = π(t + 4)/(8s) - π/8`. With `N₀ = 4/π` this gives
`t A₀(t) = t (t + 4 - s)/(2s) = 1 - ξ(t)`, `ξ = (t + 2 - s)/2` the variable of
`QED.ThreeLoopD.i13Xi` (`QED.ThreeLoopD.i8RemInt1_zero`).

**The coefficient.** At `ε = 0` the bubble is `1` and the subtraction is `1 - 1/t`, so the
integrands are `1 - ξ` on `(0, 1)` and `1/t - ξ ≥ 0` on `(1, ∞)`. A primitive of `ξ` is
`P = ξ²/2 - log ξ`, and `log t - P(t) = 2 log (1 - ξ) - ξ²/2 → 0` (as `t ξ = (1 - ξ)²`). Hence
`c₀ = (1 - P(1) + 1/2) + P(1) = 3/2` (`QED.ThreeLoopD.i8RemCoeff_zero`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8F0`, `QED.ThreeLoopD.i8J_zero`.
* `QED.ThreeLoopD.i8RemInt1_zero`, `QED.ThreeLoopD.i8RemInt2_zero`.
* `QED.ThreeLoopD.i8RemCoeff_zero : i8RemCoeff 0 = 3/2`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology Real

namespace QED.ThreeLoopD

/-! ### The angular average at `ε = 0` -/

/-- The primitive `F(z) = (t + 4)/(4s) arcsin (z √(t + 4)/√(t + 4z²)) - arcsin z / 4` of
`√(1 - z²)/(t + 4z²)`. -/
noncomputable def i8F0 (t z : ℝ) : ℝ :=
  (t + 4) / (4 * √(t * (t + 4))) * Real.arcsin (z * √(t + 4) / √(t + 4 * z ^ 2)) -
    Real.arcsin z / 4

theorem hasDerivAt_i8F0 {t : ℝ} (ht : 0 < t) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (i8F0 t) (√(1 - z ^ 2) / (t + 4 * z ^ 2)) z := by
  have hq : 0 < t + 4 * z ^ 2 := by positivity
  have hw : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  set A := √(t + 4) with hA
  set B := √(t + 4 * z ^ 2) with hB
  set T := √t with hT
  set W := √(1 - z ^ 2) with hW
  have hA0 : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hB0 : 0 < B := Real.sqrt_pos.mpr hq
  have hT0 : 0 < T := Real.sqrt_pos.mpr ht
  have hW0 : 0 < W := Real.sqrt_pos.mpr hw
  have hA2 : A ^ 2 = t + 4 := Real.sq_sqrt (by linarith)
  have hB2 : B ^ 2 = t + 4 * z ^ 2 := Real.sq_sqrt hq.le
  have hT2 : T ^ 2 = t := Real.sq_sqrt ht.le
  have hW2 : W ^ 2 = 1 - z ^ 2 := Real.sq_sqrt hw.le
  have hs : √(t * (t + 4)) = T * A := by rw [Real.sqrt_mul ht.le]
  -- the argument of the first arcsin
  have hdB : HasDerivAt (fun z : ℝ => √(t + 4 * z ^ 2)) (4 * z / B) z := by
    have h := ((hasDerivAt_pow 2 z).const_mul 4).const_add t
    refine (h.sqrt hq.ne').congr_deriv ?_
    rw [← hB]; field_simp; ring
  have hdg : HasDerivAt (fun z : ℝ => z * A / √(t + 4 * z ^ 2)) (A * t / (B ^ 2 * B)) z := by
    refine (((hasDerivAt_id z).mul_const A).div hdB hB0.ne').congr_deriv ?_
    rw [← hB]; field_simp; rw [hB2]; simp only [id]; ring
  set g := z * A / B with hg
  have hg2 : 1 - g ^ 2 = (T * W / B) ^ 2 := by
    rw [hg]; field_simp; rw [hB2, hA2, hT2, hW2]; ring
  have hg1 : g < 1 := by
    have : 0 < 1 - g ^ 2 := by rw [hg2]; positivity
    nlinarith
  have hgm : -1 < g := by
    have : 0 < 1 - g ^ 2 := by rw [hg2]; positivity
    nlinarith
  have hsq : √(1 - g ^ 2) = T * W / B := by
    rw [hg2, Real.sqrt_sq (by positivity)]
  have h1 := (Real.hasDerivAt_arcsin hgm.ne' hg1.ne).comp z hdg
  have h2 := Real.hasDerivAt_arcsin (x := z) (by linarith [hz.1]) (by linarith [hz.2])
  unfold i8F0
  refine ((h1.const_mul ((t + 4) / (4 * √(t * (t + 4))))).sub (h2.div_const 4)).congr_deriv ?_
  rw [hsq, hs, ← hB2]
  have key : A ^ 2 - B ^ 2 = 4 * W ^ 2 := by rw [hA2, hB2, hW2]; ring
  calc (t + 4) / (4 * (T * A)) * (1 / (T * W / B) * (A * t / (B ^ 2 * B))) - 1 / W / 4
      = A ^ 2 * t / (4 * T ^ 2 * W * B ^ 2) - 1 / W / 4 := by rw [← hA2]; field_simp
    _ = (A ^ 2 - B ^ 2) / (4 * W * B ^ 2) := by rw [hT2]; field_simp
    _ = W / B ^ 2 := by rw [key]; field_simp

theorem continuous_i8F0 {t : ℝ} (ht : 0 < t) : Continuous (i8F0 t) := by
  have hq : ∀ z : ℝ, √(t + 4 * z ^ 2) ≠ 0 := fun z =>
    (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold i8F0
  refine (continuous_const.mul (Real.continuous_arcsin.comp ?_)).sub
    (Real.continuous_arcsin.div_const 4)
  exact (continuous_id.mul continuous_const).div (by fun_prop) hq

theorem i8F0_one {t : ℝ} (ht : 0 < t) :
    i8F0 t 1 = (t + 4) / (4 * √(t * (t + 4))) * (π / 2) - π / 8 := by
  have hA : √(t + 4) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  unfold i8F0
  rw [one_pow, mul_one, one_mul, div_self hA, Real.arcsin_one]
  ring

theorem i8F0_zero (t : ℝ) : i8F0 t 0 = 0 := by
  unfold i8F0; simp

theorem i8Wt_zero {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : i8Wt 0 z = (√(1 - z ^ 2) : ℂ) := by
  unfold i8Wt
  rw [sub_zero, Real.sqrt_eq_rpow, ofReal_cpow (i8_one_sub_sq_pos hz).le]
  push_cast
  ring_nf

/-- `J₀(t) = π(t + 4)/(8s) - π/8`. -/
theorem i8J_zero {t : ℝ} (ht : 0 < t) :
    i8J 0 t = (((t + 4) / (4 * √(t * (t + 4))) * (π / 2) - π / 8 : ℝ) : ℂ) := by
  unfold i8J
  rw [setIntegral_congr_fun measurableSet_Ioo (g := fun z : ℝ =>
      ((√(1 - z ^ 2) / (t + 4 * z ^ 2) : ℝ) : ℂ)) fun z hz => by
      rw [i8Wt_zero hz]; push_cast; ring,
    integral_complex_ofReal, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (continuous_i8F0 ht).continuousOn
      (fun z hz => hasDerivAt_i8F0 ht ⟨by linarith [hz.1], hz.2⟩)
      ((show Continuous (fun z : ℝ => √(1 - z ^ 2) / (t + 4 * z ^ 2)) from
        Continuous.div (by fun_prop) (by fun_prop)
          (fun z => (by positivity : 0 < t + 4 * z ^ 2).ne')).intervalIntegrable 0 1),
    i8F0_one ht, i8F0_zero, sub_zero]

theorem i8Nrm_zero : i8Nrm 0 = 4 / π := by
  have g32 : Complex.Gamma (3 / 2) = 1 / 2 * Complex.Gamma (1 / 2) := by
    rw [show (3 : ℂ) / 2 = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
  have hpi : ((√Real.pi : ℝ) : ℂ) ^ 2 = Real.pi := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hne : ((√Real.pi : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold i8Nrm
  rw [sub_zero, sub_zero, g32, i13_Gamma_half, show (2 : ℂ) = 1 + 1 by norm_num,
    Gamma_add_one _ one_ne_zero, Complex.Gamma_one, ← hpi]
  field_simp
  ring

/-- `t A₀(t) = 1 - ξ(t)`. -/
theorem i8_t_mul_Ang_zero {t : ℝ} (ht : 0 < t) : (t : ℂ) * i8Ang 0 t = ((1 - i13Xi t : ℝ) : ℂ) := by
  set s := √(t * (t + 4)) with hsd
  have hs : s ^ 2 = t * (t + 4) := Real.sq_sqrt (by positivity)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hxi : 1 - i13Xi t = (s - t) / 2 := by unfold i13Xi; rw [← hsd]; ring
  have hpi := Real.pi_pos.ne'
  have hR : t * (4 / Real.pi) * ((t + 4) / (4 * s) * (Real.pi / 2) - Real.pi / 8) =
      (s - t) / 2 := by
    calc _ = t * (t + 4 - s) / (2 * s) := by field_simp; ring
      _ = (s ^ 2 - t * s) / (2 * s) := by rw [hs]; ring
      _ = (s - t) / 2 := by field_simp
  rw [i8Ang_eq, i8Nrm_zero, i8J_zero ht, ← hsd, hxi, ← hR]
  push_cast
  ring

theorem i8RemInt1_zero {t : ℝ} (ht : 0 < t) : i8RemInt1 t 0 = ((1 - i13Xi t : ℝ) : ℂ) := by
  unfold i8RemInt1
  rw [i13Bub_zero, sub_zero, cpow_one, one_pow, mul_one, i8_t_mul_Ang_zero ht]

theorem i8Asym_zero {t : ℝ} (ht : 0 < t) : i8Asym 0 t = 1 - 1 / t := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  unfold i8Asym i13Al0 i13Al1 i13Be0 i8Kap
  rw [i13G_zero]
  simp only [mul_zero, sub_zero, zero_sub, cpow_zero, cpow_neg_one]
  field_simp
  ring

theorem i8RemInt2_zero {t : ℝ} (ht : 0 < t) :
    i8RemInt2 t 0 = ((1 / t - i13Xi t : ℝ) : ℂ) := by
  have h := i8RemInt1_zero ht
  unfold i8RemInt1 at h
  unfold i8RemInt2
  rw [h, i8Asym_zero ht]
  push_cast
  ring

/-! ### The coefficient -/

/-- The primitive `P = ξ²/2 - log ξ` of `ξ`. -/
noncomputable def i8P0 (t : ℝ) : ℝ := i13Xi t ^ 2 / 2 - Real.log (i13Xi t)

theorem hasDerivAt_i8P0 {t : ℝ} (ht : 0 < t) : HasDerivAt i8P0 (i13Xi t) t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hd := hasDerivAt_i13Xi ht
  have h1 : 1 - i13Xi t ^ 2 ≠ 0 := by nlinarith
  refine (((hd.pow 2).div_const 2).sub (hd.log hx0.ne')).congr_deriv ?_
  field_simp
  ring

theorem continuousOn_i8P0 : ContinuousOn i8P0 (Ici 0) := by
  intro t ht
  have hx0 := i13Xi_pos ht
  exact ((continuous_i13Xi.pow 2).div_const 2 |>.continuousAt.sub
    (continuous_i13Xi.continuousAt.log hx0.ne')).continuousWithinAt

theorem i8P0_zero : i8P0 0 = 1 / 2 := by
  unfold i8P0; rw [i13Xi_zero]; simp

theorem i13Xi_le_inv {t : ℝ} (ht : 0 < t) : i13Xi t ≤ 1 / t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_le_one ht.le
  have hq := i13Xi_quad ht.le
  rw [le_div_iff₀ ht]
  nlinarith

theorem integral_i8_one_sub_xi : ∫ t in Ioo (0 : ℝ) 1, (1 - i13Xi t) = 3 / 2 - i8P0 1 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (f := fun t => t - i8P0 t)
      (continuous_id.continuousOn.sub (continuousOn_i8P0.mono Icc_subset_Ici_self))
      (fun t ht => (hasDerivAt_id t).sub (hasDerivAt_i8P0 ht.1))
      ((continuous_const.sub continuous_i13Xi).intervalIntegrable 0 1), i8P0_zero]
  ring

theorem tendsto_i8_log_sub_P0 : Tendsto (fun t => Real.log t - i8P0 t) atTop (𝓝 0) := by
  have hφ : ContinuousAt (fun x : ℝ => 2 * Real.log (1 - x) - x ^ 2 / 2) 0 :=
    ((continuousAt_const.sub continuousAt_id).log (by norm_num)).const_mul 2 |>.sub
      ((continuousAt_id.pow 2).div_const 2)
  have hlim : Tendsto (fun x : ℝ => 2 * Real.log (1 - x) - x ^ 2 / 2) (𝓝 0) (𝓝 0) := by
    simpa using hφ.tendsto
  refine ((hlim.comp (tendsto_nhdsWithin_iff.1 tendsto_i13Xi_atTop).1)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have hlt : Real.log t = 2 * Real.log (1 - i13Xi t) - Real.log (i13Xi t) := by
    conv_lhs => rw [hT]
    rw [Real.log_div (by nlinarith) hx0.ne', Real.log_pow]
    push_cast; ring
  simp only [Function.comp, i8P0, hlt]
  ring

theorem integral_i8_inv_sub_xi : ∫ t in Ioi (1 : ℝ), (1 / t - i13Xi t) = i8P0 1 := by
  have hd : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun t => Real.log t - i8P0 t) (1 / t - i13Xi t) t :=
    fun t ht => by
      have ht' : (1 : ℝ) < t := ht
      have h := (Real.hasDerivAt_log (by linarith : t ≠ 0)).sub
        (hasDerivAt_i8P0 (by linarith : (0 : ℝ) < t))
      rw [one_div]; exact h
  rw [integral_Ioi_of_hasDerivAt_of_nonneg
    (((Real.hasDerivAt_log one_ne_zero).sub (hasDerivAt_i8P0 one_pos)).continuousAt
      |>.continuousWithinAt) hd
    (fun t (ht : 1 < t) => by linarith [i13Xi_le_inv (by linarith : (0 : ℝ) < t)])
    tendsto_i8_log_sub_P0]
  simp

/-- **The constant term** `c₀ = 3/2`. -/
theorem i8RemCoeff_zero : i8RemCoeff 0 = 3 / 2 := by
  unfold i8RemCoeff
  simp only [i13Dsl_zero]
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i8RemInt1_zero ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i8RemInt2_zero (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, integral_i8_one_sub_xi,
    integral_i8_inv_sub_xi]
  push_cast
  ring

end QED.ThreeLoopD
