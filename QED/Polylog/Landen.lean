/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import QED.Polylog.Deriv
import QED.Polylog.Reflection
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.LinearCombination

/-!
# Landen's identities and `Li₃ (1 / 2)`

## Main results

* `QED.Polylog.Li₂_one_sub_inv_add_Li₂_one_sub`: Landen's identity
  `Li₂ (1 - 1 / x) + Li₂ (1 - x) = -(log x) ^ 2 / 2` for `1 / 2 ≤ x ≤ 1`.
* `QED.Polylog.Li₃_add_Li₃_one_sub_add_Li₃_one_sub_inv`: Landen's identity for the trilogarithm,
  `Li₃ x + Li₃ (1 - x) + Li₃ (1 - 1 / x)
    = ζ(3) + (log x) ^ 3 / 6 + (π ^ 2 / 6) log x - (log x) ^ 2 log (1 - x) / 2`
  for `1 / 2 ≤ x ≤ 1`.
* `QED.Polylog.Li₃_one_half`:
  `Li₃ (1 / 2) = (7 / 8) ζ(3) - (π ^ 2 / 12) log 2 + (log 2) ^ 3 / 6`.

On `[1 / 2, 1]` all arguments lie in `[-1, 1]`. Each identity is proved by showing that the
difference of the two sides is continuous on `[1 / 2, 1]` with derivative `0` on `(1 / 2, 1)`,
and evaluating it at `x = 1`.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog

/-- A function continuous on `[a, b]` with derivative `0` on `(a, b)` equals its value at `b`
on `[a, b]`. -/
private lemma eq_right_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) :
    ∀ x ∈ Icc a b, f x = f b := by
  intro x hx
  rcases hx.2.eq_or_lt with rfl | hxb
  · rfl
  obtain ⟨c, _, hc'⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hxb
    (hc.mono (Icc_subset_Icc hx.1 le_rfl)) fun y hy => hd y ⟨hx.1.trans_lt hy.1, hy.2⟩
  have : b - x ≠ 0 := sub_ne_zero.mpr hxb.ne'
  rw [eq_comm, div_eq_zero_iff] at hc'
  rcases hc' with h | h
  · linarith
  · exact absurd h this

/-- For `1 / 2 ≤ x ≤ 1`, the argument `1 - 1 / x` lies in `[-1, 0]`. -/
private lemma one_sub_inv_mem {x : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 1) :
    -1 ≤ 1 - x⁻¹ ∧ 1 - x⁻¹ ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx2
  have h2 : x⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
  constructor <;> linarith

/-- For `1 / 2 < x < 1`, the argument `1 - 1 / x` lies in `(-1, 0)`. -/
private lemma one_sub_inv_mem_Ioo {x : ℝ} (hx1 : 1 / 2 < x) (hx2 : x < 1) :
    -1 < 1 - x⁻¹ ∧ 1 - x⁻¹ < 0 := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 < x⁻¹ := (one_lt_inv₀ hx0).mpr hx2
  have h2 : x⁻¹ < 2 := inv_lt_of_inv_lt₀ (by norm_num) (by linarith)
  constructor <;> linarith

/-- `x ↦ 1 - 1 / x` maps `[1 / 2, 1]` into `[-1, 1]` continuously. -/
private lemma continuousOn_one_sub_inv :
    ContinuousOn (fun x : ℝ => 1 - x⁻¹) (Icc (1 / 2) 1) :=
  continuousOn_const.sub (continuousOn_inv₀.mono fun x hx => by
    simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.1])

private lemma mapsTo_one_sub_inv :
    MapsTo (fun x : ℝ => 1 - x⁻¹) (Icc (1 / 2) 1) (Icc (-1) 1) := fun x hx =>
  ⟨(one_sub_inv_mem hx.1 hx.2).1, by linarith [(one_sub_inv_mem hx.1 hx.2).2]⟩

private lemma mapsTo_one_sub : MapsTo (fun x : ℝ => 1 - x) (Icc (1 / 2) 1) (Icc (-1) 1) :=
  fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩

private lemma mapsTo_id : MapsTo (fun x : ℝ => x) (Icc (1 / 2) 1) (Icc (-1) 1) :=
  fun x hx => ⟨by linarith [hx.1], hx.2⟩

private lemma continuousOn_log_Icc : ContinuousOn log (Icc (1 / 2 : ℝ) 1) :=
  continuousOn_log.mono fun x hx => by
    simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.1]

/-- Landen's identity for the dilogarithm: `Li₂ (1 - 1 / x) + Li₂ (1 - x) = -(log x) ^ 2 / 2` for
`1 / 2 ≤ x ≤ 1`. -/
theorem Li₂_one_sub_inv_add_Li₂_one_sub {x : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 1) :
    Li₂ (1 - x⁻¹) + Li₂ (1 - x) = -log x ^ 2 / 2 := by
  set H : ℝ → ℝ := fun y => Li₂ (1 - y⁻¹) + Li₂ (1 - y) + log y ^ 2 / 2 with hH
  have hc : ContinuousOn H (Icc (1 / 2) 1) :=
    ((continuousOn_Li₂.comp continuousOn_one_sub_inv mapsTo_one_sub_inv).add
      (continuousOn_Li₂.comp (continuousOn_const.sub continuousOn_id) mapsTo_one_sub)).add
      ((continuousOn_log_Icc.pow 2).div_const 2)
  have hd : ∀ y ∈ Ioo (1 / 2 : ℝ) 1, HasDerivAt H 0 y := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have hy1 : 1 - y ≠ 0 := by linarith [hy.2]
    have hy1' : y - 1 ≠ 0 := by linarith [hy.2]
    obtain ⟨hu1, hu2⟩ := one_sub_inv_mem_Ioo hy.1 hy.2
    have hsub : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have hinv : HasDerivAt (fun z : ℝ => 1 - z⁻¹) (-(-(y ^ 2)⁻¹)) y :=
      (hasDerivAt_inv hy0).const_sub 1
    have h1 := (hasDerivAt_Li₂ (abs_lt.mpr ⟨hu1, by linarith⟩) hu2.ne).comp y hinv
    have h2 := (hasDerivAt_Li₂ (abs_lt.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩) hy1).comp
      y hsub
    have h3 := ((Real.hasDerivAt_log hy0).pow 2).div_const 2
    refine ((h1.add h2).add h3).congr_deriv ?_
    rw [sub_sub_cancel, sub_sub_cancel, Real.log_inv]
    have : 1 - y⁻¹ = (y - 1) / y := by field_simp
    rw [this]
    field_simp
    ring
  have := eq_right_of_hasDerivAt_zero hc hd x ⟨hx1, hx2⟩
  simp only [hH, inv_one, sub_self, Li₂_zero, log_one] at this
  linarith

/-- `(log x) ^ 2 log (1 - x)` is continuous on `[1 / 2, 1]`; at `x = 1` it tends to `0`. -/
private lemma continuousOn_log_sq_mul_log_one_sub :
    ContinuousOn (fun x => log x ^ 2 * log (1 - x)) (Icc (1 / 2 : ℝ) 1) := by
  intro x hx
  rcases hx.2.eq_or_lt with rfl | hx1
  · rw [ContinuousWithinAt, log_one]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun y hy => ?_) ?_
      (a := fun y => 4 * (1 - y) * |(1 - y) * log (1 - y)|)
    · have hy0 : 0 < y := by linarith [hy.1]
      have hlog : |log y| ≤ 2 * (1 - y) := by
        have h1 := Real.one_sub_inv_le_log_of_pos hy0
        have h2 : log y ≤ 0 := log_nonpos hy0.le hy.2
        have h3 : y⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith [hy.1])
        have h4 : (1 - y) * y⁻¹ ≤ (1 - y) * 2 :=
          mul_le_mul_of_nonneg_left h3 (by linarith [hy.2])
        have h5 : y⁻¹ - 1 = (1 - y) * y⁻¹ := by field_simp
        rw [abs_of_nonpos h2]
        linarith
      have hsq : |log y| ^ 2 ≤ (2 * (1 - y)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlog 2
      have h1y : 0 ≤ 1 - y := by linarith [hy.2]
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_mul, abs_of_nonneg h1y]
      calc |log y| ^ 2 * |log (1 - y)| ≤ (2 * (1 - y)) ^ 2 * |log (1 - y)| :=
            mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
        _ = 4 * (1 - y) * ((1 - y) * |log (1 - y)|) := by ring
    · have hc : Continuous fun y : ℝ => 4 * (1 - y) * |(1 - y) * log (1 - y)| :=
        (continuous_const.mul (continuous_const.sub continuous_id)).mul
          (continuous_mul_log.comp (continuous_const.sub continuous_id)).abs
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  · have hx0 : x ≠ 0 := by linarith [hx.1]
    have hx1' : 1 - x ≠ 0 := by linarith
    exact ((continuousAt_log hx0).pow 2).continuousWithinAt.mul
      ((continuousAt_log hx1').comp (continuous_const.sub continuous_id).continuousAt).continuousWithinAt

/-- Landen's identity for the trilogarithm: for `1 / 2 ≤ x ≤ 1`,
`Li₃ x + Li₃ (1 - x) + Li₃ (1 - 1 / x)
  = ζ(3) + (log x) ^ 3 / 6 + (π ^ 2 / 6) log x - (log x) ^ 2 log (1 - x) / 2`. -/
theorem Li₃_add_Li₃_one_sub_add_Li₃_one_sub_inv {x : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 1) :
    Li₃ x + Li₃ (1 - x) + Li₃ (1 - x⁻¹) =
      zeta3 + log x ^ 3 / 6 + π ^ 2 / 6 * log x - log x ^ 2 * log (1 - x) / 2 := by
  set K : ℝ → ℝ := fun y => Li₃ y + Li₃ (1 - y) + Li₃ (1 - y⁻¹) -
    (log y ^ 3 / 6 + π ^ 2 / 6 * log y - log y ^ 2 * log (1 - y) / 2) with hK
  have hc : ContinuousOn K (Icc (1 / 2) 1) :=
    (((continuousOn_Li₃.comp continuousOn_id mapsTo_id).add
      (continuousOn_Li₃.comp (continuousOn_const.sub continuousOn_id) mapsTo_one_sub)).add
      (continuousOn_Li₃.comp continuousOn_one_sub_inv mapsTo_one_sub_inv)).sub
      ((((continuousOn_log_Icc.pow 3).div_const 6).add
        (continuousOn_const.mul continuousOn_log_Icc)).sub
        (continuousOn_log_sq_mul_log_one_sub.div_const 2))
  have hd : ∀ y ∈ Ioo (1 / 2 : ℝ) 1, HasDerivAt K 0 y := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have hy1 : 1 - y ≠ 0 := by linarith [hy.2]
    have hy1' : y - 1 ≠ 0 := by linarith [hy.2]
    obtain ⟨hu1, hu2⟩ := one_sub_inv_mem_Ioo hy.1 hy.2
    have hsub : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have hinv : HasDerivAt (fun z : ℝ => 1 - z⁻¹) (-(-(y ^ 2)⁻¹)) y :=
      (hasDerivAt_inv hy0).const_sub 1
    have d1 := hasDerivAt_Li₃ (abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩) hy0
    have d2 := (hasDerivAt_Li₃ (abs_lt.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩) hy1).comp
      y hsub
    have d3 := (hasDerivAt_Li₃ (abs_lt.mpr ⟨hu1, by linarith⟩) hu2.ne).comp y hinv
    have hlog := Real.hasDerivAt_log hy0
    have hlog1 : HasDerivAt (fun z => log (1 - z)) (-1 / (1 - y)) y := hsub.log hy1
    have e1 := (hlog.pow 3).div_const 6
    have e2 := hlog.const_mul (π ^ 2 / 6)
    have e3 := ((hlog.pow 2).mul hlog1).div_const 2
    refine (((d1.add d2).add d3).sub ((e1.add e2).sub e3)).congr_deriv ?_
    have hL := Li₂_one_sub_inv_add_Li₂_one_sub hy.1.le hy.2.le
    have hR := Li₂_add_Li₂_one_sub (by linarith [hy.1] : (0 : ℝ) ≤ y) hy.2.le
    have : 1 - y⁻¹ = (y - 1) / y := by field_simp
    rw [this] at hL ⊢
    rw [show Li₂ ((y - 1) / y) = -log y ^ 2 / 2 - Li₂ (1 - y) by linarith,
      show Li₂ y = π ^ 2 / 6 - log y * log (1 - y) - Li₂ (1 - y) by linarith]
    simp only [Pi.pow_apply]
    push_cast
    field_simp
    ring
  have := eq_right_of_hasDerivAt_zero hc hd x ⟨hx1, hx2⟩
  simp only [hK, inv_one, sub_self, Li₃_zero, log_one, Li₃_one] at this
  norm_num at this
  linarith

/-- `Li₃ (1 / 2) = (7 / 8) ζ(3) - (π ^ 2 / 12) log 2 + (log 2) ^ 3 / 6`. -/
theorem Li₃_one_half :
    Li₃ (1 / 2) = 7 / 8 * zeta3 - π ^ 2 / 12 * log 2 + log 2 ^ 3 / 6 := by
  have h := Li₃_add_Li₃_one_sub_add_Li₃_one_sub_inv (x := 1 / 2) le_rfl (by norm_num)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) - (1 / 2)⁻¹ = -1 by norm_num,
    Li₃_neg_one, one_div, Real.log_inv] at h
  rw [one_div]
  linear_combination h / 2

end QED.Polylog
