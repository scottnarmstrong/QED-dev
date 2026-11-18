/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegralsC
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Fourth-order expansions of `log (1 - x)` and `Li₂ x` at `x = 0`

Endpoint expansions used in the exact evaluation of the crossed-ladder unit X (section 4.5 of
`docs/TWO-LOOP-UNITS.md`). Its one-dimensional kernel `K_X` and the boundary function `G` of the
integration by parts (4.8) have poles of order four and three at `Y = 1`; the poles cancel, and
the cancellation is controlled by expansions with explicit fifth-order remainders. The remainders
are

* `logRem x = log (1 - x) + x + x²/2 + x³/3 + x⁴/4`, with `|logRem x| ≤ 2 x⁵` on `[0, 1/2]`
  (`abs_logRem_le`, from Mathlib's `Real.abs_log_sub_add_sum_range_le`);
* `li2Rem x = Li₂ x - (x + x²/4 + x³/9 + x⁴/16)`, with `|li2Rem x| ≤ 2 x⁵` on `[0, 1/2]`
  (`abs_li2Rem_le`; its derivative is `-logRem x / x`).

The bounds come from the mean value theorem in the form `abs_le_mul_pow_of_abs_deriv_le`: a
function vanishing at `0` whose derivative is at most `M xⁿ` is at most `M xⁿ⁺¹`. A function
bounded by `M x⁵` near `0` is `o(x⁴)`, also after multiplication by `log x`
(`tendsto_div_pow_four_of_abs_le`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.Polylog

/-- **Mean value bound.** If `f` is continuous on `[0, c]`, vanishes at `0`, and its derivative
on `(0, c)` is bounded by `M xⁿ`, then `|f x| ≤ M xⁿ⁺¹` on `[0, c]`. -/
theorem abs_le_mul_pow_of_abs_deriv_le {f f' : ℝ → ℝ} {c M : ℝ} {n : ℕ}
    (hc : ContinuousOn f (Icc 0 c)) (hd : ∀ x ∈ Ioo 0 c, HasDerivAt f (f' x) x)
    (hb : ∀ x ∈ Ioo 0 c, |f' x| ≤ M * x ^ n) (h0 : f 0 = 0) :
    ∀ x ∈ Icc 0 c, |f x| ≤ M * x ^ (n + 1) := by
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hx0
  · simp [h0]
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f f' hx0
    (hc.mono (Icc_subset_Icc le_rfl hx.2)) (fun y hy => hd y ⟨hy.1, hy.2.trans_le hx.2⟩)
  rw [h0, sub_zero, sub_zero] at hξeq
  have hfx : f x = f' ξ * x := by
    rw [hξeq]
    field_simp
  have hb' := hb ξ ⟨hξ.1, hξ.2.trans_le hx.2⟩
  have hM : 0 ≤ M := by
    have h1 : 0 < ξ ^ n := pow_pos hξ.1 n
    by_contra h
    have : M * ξ ^ n < 0 := mul_neg_of_neg_of_pos (not_le.1 h) h1
    linarith [abs_nonneg (f' ξ)]
  rw [hfx, abs_mul, abs_of_pos hx0, pow_succ]
  calc |f' ξ| * x ≤ M * ξ ^ n * x := mul_le_mul_of_nonneg_right hb' hx0.le
    _ ≤ M * x ^ n * x := by
      gcongr
      · exact hξ.1.le
      · exact hξ.2.le
    _ = M * (x ^ n * x) := by ring

/-! ### `log (1 - x)` -/

/-- The fourth-order remainder of `log (1 - x)` at `0`. -/
noncomputable def logRem (x : ℝ) : ℝ := log (1 - x) + x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4

/-- `|log (1 - x) + x + x²/2 + x³/3 + x⁴/4| ≤ 2 x⁵` on `[0, 1/2]`. -/
theorem abs_logRem_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : |logRem x| ≤ 2 * x ^ 5 := by
  have ha : |x| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le ha 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg h0] at h
  have he : logRem x = 0 + x ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + x ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) +
      x ^ (2 + 1) / ((2 : ℕ) + 1 : ℝ) + x ^ (3 + 1) / ((3 : ℕ) + 1 : ℝ) + log (1 - x) := by
    unfold logRem
    push_cast
    ring
  rw [he]
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith), show x ^ (4 + 1) = x ^ 5 by norm_num]
  nlinarith [mul_nonneg (pow_nonneg h0 5) (by linarith : (0 : ℝ) ≤ 1 / 2 - x)]

/-! ### `Li₂ x` -/

/-- The fourth-order remainder of `Li₂ x` at `0`. -/
noncomputable def li2Rem (x : ℝ) : ℝ := Li₂ x - (x + x ^ 2 / 4 + x ^ 3 / 9 + x ^ 4 / 16)

theorem hasDerivAt_li2Rem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt li2Rem (-logRem x / x) x := by
  have h := (hasDerivAt_Li₂' hx).sub
    (((((hasDerivAt_id' x).add ((hasDerivAt_pow 2 x).div_const 4)).add
      ((hasDerivAt_pow 3 x).div_const 9)).add ((hasDerivAt_pow 4 x).div_const 16)))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => rfl)
  have := hx.1.ne'
  unfold logRem
  push_cast
  field_simp
  ring

/-- `|Li₂ x - (x + x²/4 + x³/9 + x⁴/16)| ≤ 2 x⁵` on `[0, 1/2]`. -/
theorem abs_li2Rem_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : |li2Rem x| ≤ 2 * x ^ 5 := by
  have hc : ContinuousOn li2Rem (Icc 0 (1 / 2)) := by
    have : ContinuousOn Li₂ (Icc 0 (1 / 2)) :=
      continuousOn_Li₂.mono (Icc_subset_Icc (by norm_num) (by norm_num))
    exact this.sub (by fun_prop)
  refine abs_le_mul_pow_of_abs_deriv_le (n := 4) hc
    (fun y hy => hasDerivAt_li2Rem ⟨hy.1, by linarith [hy.2]⟩) (fun y hy => ?_) ?_ x ⟨h0, h1⟩
  · rw [abs_div, abs_neg, abs_of_pos hy.1, div_le_iff₀ hy.1]
    have := abs_logRem_le hy.1.le hy.2.le
    nlinarith
  · simp [li2Rem, Li₂_zero]

/-! ### Remainders are `o(x⁴)` -/

/-- A function bounded by `M x⁵` on `(0, c)` is `o(x⁴)` at `0⁺`, also after multiplication by
`log x`. -/
theorem tendsto_div_pow_four_of_abs_le {R : ℝ → ℝ} {c M : ℝ} (hc : 0 < c)
    (hR : ∀ x ∈ Ioo 0 c, |R x| ≤ M * x ^ 5) :
    Tendsto (fun x => R x / x ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x => R x * log x / x ^ 4) (𝓝[>] 0) (𝓝 0) := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 c := Ioo_mem_nhdsGT hc
  have hx : Tendsto (fun x : ℝ => |M| * x) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => |M| * x) (𝓝 0) (𝓝 (|M| * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hxl : Tendsto (fun x : ℝ => |M| * |x * log x|) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_mul_log_zero.abs).const_mul |M|
    simpa using this
  refine ⟨squeeze_zero_norm' ?_ hx, squeeze_zero_norm' ?_ hxl⟩
  · filter_upwards [hev] with x hx'
    have h4 : 0 < x ^ 4 := pow_pos hx'.1 4
    rw [Real.norm_eq_abs, abs_div, abs_of_pos h4, div_le_iff₀ h4]
    calc |R x| ≤ M * x ^ 5 := hR x hx'
      _ ≤ |M| * x ^ 5 := mul_le_mul_of_nonneg_right (le_abs_self M) (pow_pos hx'.1 5).le
      _ = |M| * x * x ^ 4 := by ring
  · filter_upwards [hev] with x hx'
    have h4 : 0 < x ^ 4 := pow_pos hx'.1 4
    rw [Real.norm_eq_abs, abs_div, abs_of_pos h4, div_le_iff₀ h4, abs_mul, abs_mul,
      abs_of_pos hx'.1]
    calc |R x| * |log x| ≤ |M| * x ^ 5 * |log x| := by
          refine mul_le_mul_of_nonneg_right ((hR x hx').trans ?_) (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_abs_self M) (pow_pos hx'.1 5).le
      _ = |M| * (x * |log x|) * x ^ 4 := by ring

end QED.Polylog
