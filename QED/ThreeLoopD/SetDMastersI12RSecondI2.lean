/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondKcl
import QED.Polylog.Deriv
import QED.Polylog.ExtraIntegrals
import QED.Polylog.ExtraIntegralsX
import QED.Polylog.Landen
import QED.Polylog.Reflection

/-!
# Set (d), master `I₁₂`: an antiderivative of `K(y) / y` on `(0, 1/2]`

With `a = log y`, `b = log (1 - y)` the closed form `QED.ThreeLoopD.i12RKcl` of `K` has, divided
by `y`, the antiderivative (`QED.ThreeLoopD.i12RKclPrim`)

  `F(y) = (3y - 3/y) (Li₂ y + a b) + 6 a Li₂ y - 12 Li₃ y - (3y/2) a² - 3a - π² y`.

As `y → 0⁺`, `Li₂ y / y → 1` and `-3ab/y - 3a = -3 (y a) (b + y) / y² → 0`, so `F(0⁺) = -3`; with
`Li₂ (1/2)`, `Li₃ (1/2)`,

  `F(1/2) - F(0⁺) = 3 - 7π²/8 + 3ℓ - 3ℓ² + π²ℓ/2 + ℓ³ - 21 ζ(3)/2`,   `ℓ = log 2`,

which is half of `2 ∫₀^{1/2} K(y)/y dy = 6 - 7π²/4 + 6ℓ - 6ℓ² + π²ℓ + 2ℓ³ - 21 ζ(3)`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12RKclPrim`.
* `QED.ThreeLoopD.tendsto_i12RKclPrim_zero`, `QED.ThreeLoopD.tendsto_i12RKclPrim_half`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- An antiderivative of `K(y) / y` on `(0, 1)`. -/
noncomputable def i12RKclPrim (y : ℝ) : ℝ :=
  (3 * y - 3 / y) * (Li₂ y + log y * log (1 - y)) + 6 * log y * Li₂ y - 12 * Li₃ y -
    3 * y / 2 * log y ^ 2 - 3 * log y - π ^ 2 * y

theorem hasDerivAt_i12RKclPrim {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12RKclPrim (i12RKcl y / y) y := by
  obtain ⟨hy0, hy1⟩ := hy
  have h1y : 0 < 1 - y := by linarith
  have hi := hasDerivAt_id y
  have hL2 := hasDerivAt_Li₂' ⟨hy0, hy1⟩
  have hL3 := hasDerivAt_Li₃' ⟨hy0, hy1⟩
  have hl := Real.hasDerivAt_log hy0.ne'
  have hl1 := (hi.const_sub 1).log h1y.ne'
  have hinv := (hasDerivAt_inv hy0.ne').const_mul 3
  have h := (((((((hi.const_mul 3).sub hinv).mul (hL2.add (hl.mul hl1))).add
    ((hl.const_mul 6).mul hL2)).sub (hL3.const_mul 12)).sub
    (((hi.const_mul 3).div_const 2).mul (hl.pow 2))).sub (hl.const_mul 3)).sub
    (hi.const_mul (π ^ 2))
  convert h using 1
  · funext v
    simp only [i12RKclPrim, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  simp only [i12RKcl, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  have := hy0.ne'
  have := h1y.ne'
  generalize log y = a
  generalize log (1 - y) = b
  generalize Li₂ y = L
  field_simp
  ring

theorem tendsto_i12RKclPrim_zero : Tendsto i12RKclPrim (𝓝[>] 0) (𝓝 (-3)) := by
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hy : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hLy : Tendsto (fun y => Li₂ y / y) (𝓝[>] 0) (𝓝 1) := by
    refine hasDerivAt_Li₂_zero.tendsto_slope_zero_right.congr fun t => ?_
    simp only [zero_add, Li₂_zero, sub_zero, smul_eq_mul]
    ring
  have hR : Tendsto (fun y => log y * logRem y / y) (𝓝[>] 0) (𝓝 0) := by
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
  have hya := tendsto_mul_log_zero
  have h := ((((((((hy.mul tendsto_Li₂_zero_right).const_mul 3).add
    ((hy.mul tendsto_log_mul_log_one_sub_zero).const_mul 3)).sub (hLy.const_mul 3)).sub
    ((hya.mul ((hy.const_mul (-1 / 3)).add ((hy.pow 2).const_mul (-1 / 4)) |>.const_add
      (-1 / 2))).const_mul 3)).sub (hR.const_mul 3)).add
    (tendsto_log_mul_Li₂_zero.const_mul 6)).sub (tendsto_Li₃_zero_right.const_mul 12)).sub
    ((tendsto_mul_log_sq_zero.const_mul (3 / 2)).add (hy.const_mul (π ^ 2)))
  have e : i12RKclPrim =ᶠ[𝓝[>] 0] fun y => 3 * (y * Li₂ y) + 3 * (y * (log y * log (1 - y))) -
      3 * (Li₂ y / y) - 3 * (y * log y * (-1 / 2 + (-1 / 3 * y + -1 / 4 * y ^ 2))) -
      3 * (log y * logRem y / y) + 6 * (log y * Li₂ y) - 12 * Li₃ y -
      (3 / 2 * (y * log y ^ 2) + π ^ 2 * y) := by
    filter_upwards [hev] with y hy
    have := hy.1.ne'
    simp only [i12RKclPrim, logRem]
    field_simp
    ring
  refine Tendsto.congr' e.symm ?_
  convert h using 2
  norm_num

theorem continuousAt_i12RKclPrim_half : ContinuousAt i12RKclPrim (1 / 2) := by
  have h2 : ContinuousAt Li₂ (1 / 2) :=
    continuousOn_Li₂.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have h3 : ContinuousAt Li₃ (1 / 2) :=
    continuousOn_Li₃.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  unfold i12RKclPrim
  fun_prop (disch := norm_num)

theorem i12RKclPrim_half : i12RKclPrim (1 / 2) =
    -7 * π ^ 2 / 8 + 3 * log 2 - 3 * log 2 ^ 2 + π ^ 2 * log 2 / 2 + log 2 ^ 3 -
      21 / 2 * zeta3 := by
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hl : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, Real.log_inv]
  simp only [i12RKclPrim, e, hl, Li₂_one_half, Li₃_one_half]
  ring

theorem tendsto_i12RKclPrim_half : Tendsto i12RKclPrim (𝓝[<] (1 / 2))
    (𝓝 (-7 * π ^ 2 / 8 + 3 * log 2 - 3 * log 2 ^ 2 + π ^ 2 * log 2 / 2 + log 2 ^ 3 -
      21 / 2 * zeta3)) := by
  rw [← i12RKclPrim_half]
  exact continuousAt_i12RKclPrim_half.tendsto.mono_left nhdsWithin_le_nhds

end QED.ThreeLoopD
