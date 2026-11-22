/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
import QED.Polylog.Deriv
import QED.Polylog.ExtraIntegrals
import QED.Polylog.ExtraIntegralsX
import QED.Polylog.Reflection

/-!
# Set (d), master `I₁₂`: the elementary part of `R₁'(0)` integrated in `y`

With `c = y (1 - y)`, `a = log y`, `b = log (1 - y)` and `β(t) = (6t³ - 15t² + 17t - 9)/(1 - t)²`,
the closed form of the function `E(c)` of `QED.ThreeLoopD.i12RE` is (`QED.ThreeLoopD.i12REcl`)

  `E = -1/c - 3 + β(y) a + β(1 - y) b - 3 (1 - c) (a² + b² + π²) - 6 ((1 - c + c²)/c) a b`,

and the integrand `-(1/6) log c + 329/36 - π² + (3 log c + 3π² - 3/2 + 3 log² c + E) / c` of the
`y`-integral of `R₁'(0)` (`QED.ThreeLoopD.i12R1Pcl`) has the antiderivative
(`QED.ThreeLoopD.i12R1PPrim`)

  `F = -6 Li₂ y + 3y a² + 3(y - 1) b² + 6 ((y³ - y² - 2y + 1)/(y(1 - y))) a b
      - ((y³ - 113y² + 151y - 36)/(6(y - 1)²)) a
      - ((y⁵ + 108y⁴ - 291y³ + 251y² - 66y - 3)/(6y²(y - 1)²)) b
      + (y⁴(72π² + 341) - 3y²(72π² + 329) + 4y(36π² + 157) + 18)/(36y(y - 1)²)`.

Writing `b = -y - y²/2 - y³/3 - y⁴/4 + R(y)` with `|R(y)| ≤ 2y⁵` (`QED.Polylog.logRem`), the poles
at `y = 0` cancel and `F(0⁺) = 4π² + 223/36`; `F(1/2) = 9π²/2 + 1705/72`, so

  `∫₀^{1/2} (integrand) = 1259/72 + π²/2`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12R1PPrim`.
* `QED.ThreeLoopD.tendsto_i12R1PPrim_zero`, `QED.ThreeLoopD.tendsto_i12R1PPrim_half`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The closed form of `E(y (1 - y))`. -/
noncomputable def i12REcl (y : ℝ) : ℝ :=
  -1 / (y * (1 - y)) - 3 + (6 * y ^ 3 - 15 * y ^ 2 + 17 * y - 9) / (1 - y) ^ 2 * log y +
    (6 * (1 - y) ^ 3 - 15 * (1 - y) ^ 2 + 17 * (1 - y) - 9) / y ^ 2 * log (1 - y) -
    3 * (1 - y * (1 - y)) * (log y ^ 2 + log (1 - y) ^ 2 + π ^ 2) -
    6 * ((1 - y * (1 - y) + (y * (1 - y)) ^ 2) / (y * (1 - y))) * log y * log (1 - y)

/-- The elementary integrand of the `y`-integral of `R₁'(0)`, with `E` in closed form. -/
noncomputable def i12R1Pcl (y : ℝ) : ℝ :=
  -(1 / 6) * log (y * (1 - y)) + 329 / 36 - π ^ 2 + (3 * log (y * (1 - y)) + 3 * π ^ 2 - 3 / 2 +
    3 * log (y * (1 - y)) ^ 2 + i12REcl y) / (y * (1 - y))

/-- An antiderivative of `QED.ThreeLoopD.i12R1Pcl` on `(0, 1)`. -/
noncomputable def i12R1PPrim (y : ℝ) : ℝ :=
  -6 * Li₂ y + 3 * y * log y ^ 2 + 3 * (y - 1) * log (1 - y) ^ 2 +
    6 * ((y ^ 3 - y ^ 2 - 2 * y + 1) / (y * (1 - y))) * log y * log (1 - y) -
    (y ^ 3 - 113 * y ^ 2 + 151 * y - 36) / (6 * (y - 1) ^ 2) * log y -
    (y ^ 5 + 108 * y ^ 4 - 291 * y ^ 3 + 251 * y ^ 2 - 66 * y - 3) / (6 * y ^ 2 * (y - 1) ^ 2) *
      log (1 - y) +
    (y ^ 4 * (72 * π ^ 2 + 341) - 3 * y ^ 2 * (72 * π ^ 2 + 329) + 4 * y * (36 * π ^ 2 + 157) +
      18) / (36 * y * (y - 1) ^ 2)

theorem hasDerivAt_i12R1PPrim {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12R1PPrim (i12R1Pcl y) y := by
  obtain ⟨hy0, hy1⟩ := hy
  have h1y : 0 < 1 - y := by linarith
  have hy1' : y - 1 ≠ 0 := by linarith
  have hi := hasDerivAt_id' y
  have hL2 := hasDerivAt_Li₂' ⟨hy0, hy1⟩
  have hl := Real.hasDerivAt_log hy0.ne'
  have hl1 := (hi.const_sub 1).log h1y.ne'
  have hr1 : HasDerivAt (fun y : ℝ => (y ^ 3 - y ^ 2 - 2 * y + 1) / (y * (1 - y)))
      (((3 * y ^ 2 - 2 * y - 2) * (y * (1 - y)) - (y ^ 3 - y ^ 2 - 2 * y + 1) * (1 - 2 * y)) /
        (y * (1 - y)) ^ 2) y := by
    have := ((((hi.pow 3).sub (hi.pow 2)).sub (hi.const_mul 2)).add_const 1).div
      (hi.mul (hi.const_sub 1)) (mul_pos hy0 h1y).ne'
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  have hr2 : HasDerivAt (fun y : ℝ => (y ^ 3 - 113 * y ^ 2 + 151 * y - 36) / (6 * (y - 1) ^ 2))
      (((3 * y ^ 2 - 226 * y + 151) * (6 * (y - 1) ^ 2) -
        (y ^ 3 - 113 * y ^ 2 + 151 * y - 36) * (12 * (y - 1))) / (6 * (y - 1) ^ 2) ^ 2) y := by
    have := ((((hi.pow 3).sub ((hi.pow 2).const_mul 113)).add (hi.const_mul 151)).sub_const
      36).div (((hi.sub_const 1).pow 2).const_mul 6)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy1'))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    ring
  have hr3 : HasDerivAt (fun y : ℝ => (y ^ 5 + 108 * y ^ 4 - 291 * y ^ 3 + 251 * y ^ 2 - 66 * y -
      3) / (6 * y ^ 2 * (y - 1) ^ 2))
      (((5 * y ^ 4 + 432 * y ^ 3 - 873 * y ^ 2 + 502 * y - 66) * (6 * y ^ 2 * (y - 1) ^ 2) -
        (y ^ 5 + 108 * y ^ 4 - 291 * y ^ 3 + 251 * y ^ 2 - 66 * y - 3) *
          (12 * y * (y - 1) ^ 2 + 12 * y ^ 2 * (y - 1))) / (6 * y ^ 2 * (y - 1) ^ 2) ^ 2) y := by
    have := ((((((hi.pow 5).add ((hi.pow 4).const_mul 108)).sub ((hi.pow 3).const_mul 291)).add
      ((hi.pow 2).const_mul 251)).sub (hi.const_mul 66)).sub_const 3).div
      (((hi.pow 2).const_mul 6).mul ((hi.sub_const 1).pow 2))
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy0.ne')) (pow_ne_zero 2 hy1'))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  have hr4 : HasDerivAt (fun y : ℝ => (y ^ 4 * (72 * π ^ 2 + 341) - 3 * y ^ 2 * (72 * π ^ 2 + 329) +
      4 * y * (36 * π ^ 2 + 157) + 18) / (36 * y * (y - 1) ^ 2))
      (((4 * y ^ 3 * (72 * π ^ 2 + 341) - 6 * y * (72 * π ^ 2 + 329) + 4 * (36 * π ^ 2 + 157)) *
        (36 * y * (y - 1) ^ 2) - (y ^ 4 * (72 * π ^ 2 + 341) - 3 * y ^ 2 * (72 * π ^ 2 + 329) +
          4 * y * (36 * π ^ 2 + 157) + 18) * (36 * (y - 1) ^ 2 + 72 * y * (y - 1))) /
        (36 * y * (y - 1) ^ 2) ^ 2) y := by
    have := (((((hi.pow 4).mul_const (72 * π ^ 2 + 341)).sub
      (((hi.pow 2).const_mul 3).mul_const (72 * π ^ 2 + 329))).add
      ((hi.const_mul 4).mul_const (36 * π ^ 2 + 157))).add_const 18).div
      ((hi.const_mul 36).mul ((hi.sub_const 1).pow 2))
      (mul_ne_zero (mul_ne_zero (by norm_num) hy0.ne') (pow_ne_zero 2 hy1'))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  have h := ((((((hL2.const_mul (-6)).add ((hi.const_mul 3).mul (hl.pow 2))).add
    (((hi.sub_const 1).const_mul 3).mul (hl1.pow 2))).add
    (((hr1.const_mul 6).mul hl).mul hl1)).sub (hr2.mul hl)).sub (hr3.mul hl1)).add hr4
  convert h using 1
  · funext v
    simp only [i12R1PPrim, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  simp only [i12R1Pcl, i12REcl, Pi.mul_apply, Pi.pow_apply]
  rw [Real.log_mul hy0.ne' h1y.ne']
  have := hy0.ne'
  have := h1y.ne'
  generalize log y = a
  generalize log (1 - y) = b
  field_simp
  ring

theorem tendsto_i12R1PPrim_zero :
    Tendsto i12R1PPrim (𝓝[>] 0) (𝓝 (4 * π ^ 2 + 223 / 36)) := by
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hR2 : Tendsto (fun y => logRem y / y ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun y : ℝ => 2 * y ^ 3) (𝓝[>] 0) (𝓝 0) := by
      have := ((by fun_prop : Continuous fun y : ℝ => 2 * y ^ 3).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hev] with y hy
    have hR := abs_logRem_le hy.1.le hy.2.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hy.1 2), div_le_iff₀ (pow_pos hy.1 2)]
    calc |logRem y| ≤ 2 * y ^ 5 := hR
      _ = 2 * y ^ 3 * y ^ 2 := by ring
  have hR1 : Tendsto (fun y => log y * logRem y / y) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using tendsto_mul_log_zero.abs.const_mul 2)
    filter_upwards [hev] with y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hR := abs_logRem_le hy0.le hy1.le
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hy0, div_le_iff₀ hy0]
    have hy4 : y ^ 5 ≤ y ^ 2 := pow_le_pow_of_le_one hy0.le (by linarith) (by norm_num)
    calc |log y| * |logRem y| ≤ |log y| * (2 * y ^ 5) :=
          mul_le_mul_of_nonneg_left hR (abs_nonneg _)
      _ ≤ |log y| * (2 * y ^ 2) := by gcongr
      _ = 2 * (y * |log y|) * y := by ring
  have hRR : Tendsto (fun y => logRem y) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun y : ℝ => y ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    have := hR2.mul hb
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [hev] with y hy
    have := hy.1.ne'
    field_simp
  have hc : ∀ f : ℝ → ℝ, ContinuousAt f 0 → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := fun f hf =>
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hq0 := hc (fun y : ℝ => (288 * π ^ 2 * y ^ 2 + 288 * π ^ 2 * y - 576 * π ^ 2 + 27 * y ^ 10 +
    18 * y ^ 9 + 39 * y ^ 8 + 120 * y ^ 7 - 162 * y ^ 6 + 662 * y ^ 5 - 244 * y ^ 4 -
    142 * y ^ 3 + 2798 * y ^ 2 - 2152 * y - 892) / (144 * (y - 1)))
    (by fun_prop (disch := norm_num))
  have hq1 := hc (fun y : ℝ => (9 * y ^ 6 - 6 * y ^ 5 - 15 * y ^ 4 + 15 * y ^ 3 - 64 * y ^ 2 +
    119 * y - 61) / (6 * (y - 1) ^ 2)) (by fun_prop (disch := norm_num))
  have hq3 := hc (fun y : ℝ => -(9 * y ^ 7 + 3 * y ^ 6 + 6 * y ^ 5 + 18 * y ^ 4 - 35 * y ^ 3 +
    110 * y ^ 2 - 72 * y - 3) / 6) (by fun_prop)
  have hq4 := hc (fun y : ℝ => -6 * (y ^ 3 - y ^ 2 - 2 * y + 1) / (y - 1))
    (by fun_prop (disch := norm_num))
  have hq5 := hc (fun y : ℝ => 3 * (y - 1)) (by fun_prop)
  have h := (((((hq0.add (tendsto_mul_log_zero.mul hq1)).add
    (tendsto_mul_log_sq_zero.const_mul 3)).add (hR2.mul hq3)).add (hR1.mul hq4)).add
    ((hRR.pow 2).mul hq5)).sub (tendsto_Li₂_zero_right.const_mul 6)
  have e : i12R1PPrim =ᶠ[𝓝[>] 0] fun y =>
      (288 * π ^ 2 * y ^ 2 + 288 * π ^ 2 * y - 576 * π ^ 2 + 27 * y ^ 10 +
        18 * y ^ 9 + 39 * y ^ 8 + 120 * y ^ 7 - 162 * y ^ 6 + 662 * y ^ 5 - 244 * y ^ 4 -
        142 * y ^ 3 + 2798 * y ^ 2 - 2152 * y - 892) / (144 * (y - 1)) +
      y * log y * ((9 * y ^ 6 - 6 * y ^ 5 - 15 * y ^ 4 + 15 * y ^ 3 - 64 * y ^ 2 +
        119 * y - 61) / (6 * (y - 1) ^ 2)) + 3 * (y * log y ^ 2) +
      logRem y / y ^ 2 * (-(9 * y ^ 7 + 3 * y ^ 6 + 6 * y ^ 5 + 18 * y ^ 4 - 35 * y ^ 3 +
        110 * y ^ 2 - 72 * y - 3) / 6) +
      log y * logRem y / y * (-6 * (y ^ 3 - y ^ 2 - 2 * y + 1) / (y - 1)) +
      logRem y ^ 2 * (3 * (y - 1)) - 6 * Li₂ y := by
    filter_upwards [hev] with y hy
    have := hy.1.ne'
    have : y - 1 ≠ 0 := by linarith [hy.2]
    have : 1 - y ≠ 0 := by linarith [hy.2]
    simp only [i12R1PPrim, logRem]
    field_simp
    ring
  refine Tendsto.congr' e.symm ?_
  convert h using 2
  norm_num
  ring

theorem continuousAt_i12R1PPrim_half : ContinuousAt i12R1PPrim (1 / 2) := by
  have h2 : ContinuousAt Li₂ (1 / 2) :=
    continuousOn_Li₂.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  unfold i12R1PPrim
  fun_prop (disch := norm_num)

theorem i12R1PPrim_half : i12R1PPrim (1 / 2) = 9 * π ^ 2 / 2 + 1705 / 72 := by
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hl : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, Real.log_inv]
  simp only [i12R1PPrim, e, hl, Li₂_one_half]
  ring

theorem tendsto_i12R1PPrim_half :
    Tendsto i12R1PPrim (𝓝[<] (1 / 2)) (𝓝 (9 * π ^ 2 / 2 + 1705 / 72)) := by
  rw [← i12R1PPrim_half]
  exact continuousAt_i12R1PPrim_half.tendsto.mono_left nhdsWithin_le_nhds

end QED.ThreeLoopD
