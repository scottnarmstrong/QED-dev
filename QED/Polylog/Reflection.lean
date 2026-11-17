/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import QED.Polylog.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Euler's reflection formula for the dilogarithm

## Main results

* `QED.Polylog.Li₂_add_Li₂_one_sub`: `Li₂ x + Li₂ (1 - x) = π ^ 2 / 6 - log x log (1 - x)` for
  `0 ≤ x ≤ 1`.
* `QED.Polylog.Li₂_one_half`: `Li₂ (1 / 2) = π ^ 2 / 12 - (log 2) ^ 2 / 2`.

The left side minus the right side has derivative `0` on `(0, 1)`, so it is constant there; its
limit at `0` is `0`, by continuity of `Li₂` on `[-1, 1]` and `x log x → 0`.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog

/-- On `(0, 1)` the function `Li₂ x + Li₂ (1 - x) + log x log (1 - x)` has derivative `0`. -/
private lemma hasDerivAt_reflection {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Li₂ y + Li₂ (1 - y) + log y * log (1 - y)) 0 x := by
  have habs : |x| < 1 := abs_lt.mpr ⟨by linarith, hx1⟩
  have habs' : |1 - x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have h1 := hasDerivAt_Li₂ habs hx0.ne'
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have h2 : HasDerivAt (fun y => Li₂ (1 - y)) (-log (1 - (1 - x)) / (1 - x) * (-1)) x :=
    (hasDerivAt_Li₂ habs' (by linarith)).comp x hsub
  have h3 : HasDerivAt (fun y => log y) x⁻¹ x := Real.hasDerivAt_log hx0.ne'
  have h4 : HasDerivAt (fun y => log (1 - y)) (-1 / (1 - x)) x :=
    hsub.log (by linarith)
  convert (h1.add h2).add (h3.mul h4) using 1
  have : 1 - x ≠ 0 := by linarith
  rw [sub_sub_cancel]
  field_simp
  ring

/-- `log x log (1 - x) → 0` as `x → 0` within `(0, 1)`. -/
private lemma tendsto_log_mul_log_one_sub :
    Tendsto (fun y => log y * log (1 - y)) (𝓝[Ioo 0 1] 0) (𝓝 0) := by
  have hg : Tendsto (fun y : ℝ => |y * log y| / (1 - |y|)) (𝓝[Ioo 0 1] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun y : ℝ => |y * log y| / (1 - |y|)) 0 :=
      (continuous_mul_log.abs.continuousAt).div (continuous_const.sub continuous_abs).continuousAt
        (by simp)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun y hy => ?_) hg
  have hy1 : |y| < 1 := abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩
  have hb := Real.abs_log_sub_add_sum_range_le hy1 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_one] at hb
  have hpos : 0 < 1 - |y| := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, mul_div_assoc]
  calc |log y| * |log (1 - y)| ≤ |log y| * (|y| / (1 - |y|)) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = |y| * (|log y| / (1 - |y|)) := by ring

/-- Euler's reflection formula for the dilogarithm:
`Li₂ x + Li₂ (1 - x) = π ^ 2 / 6 - log x log (1 - x)` for `0 ≤ x ≤ 1`. -/
theorem Li₂_add_Li₂_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Li₂ x + Li₂ (1 - x) = π ^ 2 / 6 - log x * log (1 - x) := by
  set F : ℝ → ℝ := fun y => Li₂ y + Li₂ (1 - y) + log y * log (1 - y) with hF
  -- `F` is constant on `(0, 1)`.
  have hconst : ∀ y ∈ Ioo (0 : ℝ) 1, F y = F (1 / 2) := fun y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun z hz => (hasDerivAt_reflection hz.1 hz.2).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hasDerivAt_reflection hz.1 hz.2).deriv) hy
      ⟨by norm_num, by norm_num⟩
  -- The limit of `F` at `0` from the right is `π ^ 2 / 6`.
  have hlim : Tendsto F (𝓝[Ioo 0 1] 0) (𝓝 (π ^ 2 / 6)) := by
    have hmem0 : (0 : ℝ) ∈ Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
    have hmem1 : (1 : ℝ) ∈ Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
    have hsub : Ioo (0 : ℝ) 1 ⊆ Icc (-1) 1 := fun y hy => ⟨by linarith [hy.1], hy.2.le⟩
    have t1 : Tendsto Li₂ (𝓝[Ioo 0 1] 0) (𝓝 0) := by
      simpa using ((continuousOn_Li₂ 0 hmem0).mono hsub).tendsto
    have t2 : Tendsto (fun y => Li₂ (1 - y)) (𝓝[Ioo 0 1] 0) (𝓝 (π ^ 2 / 6)) := by
      have hc : ContinuousWithinAt (fun y : ℝ => 1 - y) (Ioo 0 1) 0 :=
        (continuous_const.sub continuous_id).continuousWithinAt
      have := (continuousOn_Li₂ 1 hmem1).comp_of_eq hc
        (fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩) (by norm_num)
      simpa [Function.comp_def, Li₂_one] using this.tendsto
    simpa [hF] using (t1.add t2).add tendsto_log_mul_log_one_sub
  have hF0 : F (1 / 2) = π ^ 2 / 6 := by
    have := left_nhdsWithin_Ioo_neBot (zero_lt_one (α := ℝ))
    refine tendsto_nhds_unique ?_ hlim
    exact tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hconst y hy).symm)
  rcases hx0.eq_or_lt with rfl | hx0
  · simp [Li₂_one]
  rcases hx1.eq_or_lt with rfl | hx1
  · simp [Li₂_one]
  have := hconst x ⟨hx0, hx1⟩
  rw [hF0] at this
  simp only [hF] at this
  linarith

/-- `Li₂ (1 / 2) = ζ(2) / 2 - (log 2) ^ 2 / 2 = π ^ 2 / 12 - (log 2) ^ 2 / 2`. -/
theorem Li₂_one_half : Li₂ (1 / 2) = π ^ 2 / 12 - log 2 ^ 2 / 2 := by
  have h := Li₂_add_Li₂_one_sub (x := 1 / 2) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, Real.log_inv] at h
  linarith

end QED.Polylog
