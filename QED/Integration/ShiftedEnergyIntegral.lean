/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.EnergyIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Shifted energy integrals and boundary values

This module extends `QED.Integration.EnergyIntegral` in two directions.

First, it evaluates the loop-energy integral of a quadratic numerator against a shifted
denominator, `∫ (α t² + β t + γ) (-(t + a)² + w)⁻³ dt`, for `-w` in the slit plane. The shift
`t ↦ t + a` reduces it to the three moments `∫ tᵏ (-t² + w)⁻³ dt`, `k = 0, 1, 2`; the odd moment
vanishes by symmetry and the even moments are the two forms of obligation O-7.

Second, it controls the principal powers `(-W + ε i)^{-s}` that these formulas produce when
`w = W - ε i` with `W > 0` and `ε > 0`: their boundary value as `ε → 0⁺`, a norm bound uniform in
`ε`, and a Lipschitz bound in `W` uniform in `ε > 0`.

## Main statements

* `QED.Integration.integral_mul_neg_sq_add_zpow_three`: `∫ t (-t² + w)⁻³ dt = 0`.
* `QED.Integration.integrable_pow_mul_neg_sq_add_zpow_three`: `tᵏ (-t² + w)⁻³` is integrable
  for `k ≤ 2`.
* `QED.Integration.integral_quadratic_mul_shifted`: the quadratic numerator against the
  shifted denominator.
* `QED.Integration.tendsto_cpow_neg_add_mul_I`: `(-W + ε i)^s → (-W)^s` as `ε → 0⁺`.
* `QED.Integration.norm_cpow_neg_add_mul_I_le`: `‖(-W + ε i)^{-s}‖ ≤ W^{-s}` for `s ≥ 0`.
* `QED.Integration.norm_cpow_sub_cpow_le`: the Lipschitz bound in `W`, used for the
  Pauli–Villars difference.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory
open scoped Real

namespace QED.Integration

/-- The odd moment vanishes: `∫ t (-t² + w)⁻³ dt = 0`. The integrand is odd, so no
integrability hypothesis is needed. -/
theorem integral_mul_neg_sq_add_zpow_three {w : ℂ} :
    ∫ t : ℝ, (t : ℂ) * (-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ) = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => (t : ℂ) * (-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ)) volume
  simp only [ofReal_neg, neg_sq, neg_mul, integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- The moments `tᵏ (-t² + w)⁻³` are integrable for `k ≤ 2` when `-w` lies in the slit plane. -/
theorem integrable_pow_mul_neg_sq_add_zpow_three {w : ℂ} (hw : -w ∈ slitPlane) {k : ℕ}
    (hk : k ≤ 2) :
    Integrable fun t : ℝ => (t : ℂ) ^ k * (-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ) := by
  have hX : ∀ t : ℝ, -(t : ℂ) ^ 2 + w = -((t : ℂ) ^ 2 + -w) := fun t => by ring
  have i2 : Integrable fun t : ℝ => ((t : ℂ) ^ 2 + -w) ^ (-2 : ℤ) := by
    simpa using integrable_sq_add_zpow hw 2 (by norm_num)
  have i3 : Integrable fun t : ℝ => ((t : ℂ) ^ 2 + -w) ^ (-3 : ℤ) := by
    simpa using integrable_sq_add_zpow hw 3 (by norm_num)
  have h0 : Integrable fun t : ℝ => (-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ) := by
    refine i3.neg.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, hX, Odd.neg_zpow (by decide : Odd (-3 : ℤ))]
  -- `t² (t² + z)⁻³ = (t² + z)⁻² - z (t² + z)⁻³` with `z = -w`
  have h2 : Integrable fun t : ℝ => (t : ℂ) ^ 2 * (-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ) := by
    refine (i2.neg.add (i3.const_mul (-w))).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, Pi.add_apply, hX, Odd.neg_zpow (by decide : Odd (-3 : ℤ))]
    rw [show (-2 : ℤ) = 1 + -3 by norm_num, zpow_add' (Or.inr (Or.inl (by norm_num))),
      zpow_one]
    ring
  interval_cases k
  · simpa using h0
  · -- `|t| ≤ 1 + t²` dominates the first moment by the zeroth and second moments
    refine (h0.norm.add h2.norm).mono'
      ((continuous_ofReal.pow 1).aestronglyMeasurable.mul h0.aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    simp only [pow_one, norm_mul, norm_pow, Pi.add_apply]
    have hx : ‖(t : ℂ)‖ ≤ 1 + ‖(t : ℂ)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖(t : ℂ)‖ - 1), norm_nonneg (t : ℂ)]
    calc ‖(t : ℂ)‖ * ‖(-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ)‖
        ≤ (1 + ‖(t : ℂ)‖ ^ 2) * ‖(-(t : ℂ) ^ 2 + w) ^ (-3 : ℤ)‖ := by gcongr
      _ = _ := by ring
  · exact h2

/-- The quadratic numerator against the shifted denominator is integrable. -/
theorem integrable_quadratic_mul_shifted {w : ℂ} (hw : -w ∈ slitPlane) (a : ℝ) (α β γ : ℂ) :
    Integrable fun t : ℝ =>
      (α * (t : ℂ) ^ 2 + β * t + γ) * (-((t : ℂ) + a) ^ 2 + w) ^ (-3 : ℤ) := by
  have i0 : Integrable fun s : ℝ => (-(s : ℂ) ^ 2 + w) ^ (-3 : ℤ) := by
    simpa using integrable_pow_mul_neg_sq_add_zpow_three hw (k := 0) (by norm_num)
  have i1 : Integrable fun s : ℝ => (s : ℂ) * (-(s : ℂ) ^ 2 + w) ^ (-3 : ℤ) := by
    simpa using integrable_pow_mul_neg_sq_add_zpow_three hw (k := 1) (by norm_num)
  have i2 := integrable_pow_mul_neg_sq_add_zpow_three hw (k := 2) (by norm_num)
  refine ((((i2.const_mul α).add (i1.const_mul (β - 2 * a * α))).add
    (i0.const_mul (α * a ^ 2 - β * a + γ))).comp_add_right a).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, ofReal_add]
  ring

/-- **Quadratic numerator against a shifted denominator.** For `-w` in the slit plane,
`∫ (α t² + β t + γ) (-(t + a)² + w)⁻³ dt
  = -(π/8) α (-w)^{-3/2} - (3π/8) (α a² - β a + γ) (-w)^{-5/2}`. -/
theorem integral_quadratic_mul_shifted {w : ℂ} (hw : -w ∈ slitPlane) (a : ℝ) (α β γ : ℂ) :
    ∫ t : ℝ, (α * (t : ℂ) ^ 2 + β * t + γ) * (-((t : ℂ) + a) ^ 2 + w) ^ (-3 : ℤ)
      = -((π / 8 : ℂ) * α * (-w) ^ (-(3 / 2 : ℂ)))
        - (3 * π / 8 : ℂ) * (α * (a : ℂ) ^ 2 - β * a + γ) * (-w) ^ (-(5 / 2 : ℂ)) := by
  have i0 : Integrable fun s : ℝ => (-(s : ℂ) ^ 2 + w) ^ (-3 : ℤ) := by
    simpa using integrable_pow_mul_neg_sq_add_zpow_three hw (k := 0) (by norm_num)
  have i1 : Integrable fun s : ℝ => (s : ℂ) * (-(s : ℂ) ^ 2 + w) ^ (-3 : ℤ) := by
    simpa using integrable_pow_mul_neg_sq_add_zpow_three hw (k := 1) (by norm_num)
  have i2 := integrable_pow_mul_neg_sq_add_zpow_three hw (k := 2) (by norm_num)
  -- In the variable `s = t + a`, the numerator is `α s² + (β - 2aα) s + (αa² - βa + γ)`.
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ,
      G = (fun s : ℝ => α * ((s : ℂ) ^ 2 * (-(s : ℂ) ^ 2 + w) ^ (-3 : ℤ)))
        + (fun s : ℝ => (β - 2 * a * α) * ((s : ℂ) * (-(s : ℂ) ^ 2 + w) ^ (-3 : ℤ)))
        + (fun s : ℝ => (α * a ^ 2 - β * a + γ) * (-(s : ℂ) ^ 2 + w) ^ (-3 : ℤ)) :=
    ⟨_, rfl⟩
  have hpt : ∀ t : ℝ, (α * (t : ℂ) ^ 2 + β * t + γ) * (-((t : ℂ) + a) ^ 2 + w) ^ (-3 : ℤ)
      = G (t + a) := fun t => by
    simp only [hG, Pi.add_apply, ofReal_add]
    ring
  simp_rw [hpt]
  rw [integral_add_right_eq_self G a, hG, integral_add' ((i2.const_mul _).add (i1.const_mul _))
    (i0.const_mul _), integral_add' (i2.const_mul _) (i1.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_sq_mul_neg_sq_add_zpow_three hw,
    integral_mul_neg_sq_add_zpow_three, integral_neg_sq_add_zpow_three hw]
  ring

/-- **Boundary value from the upper half plane.** For `W > 0`, the principal power
`(-W + ε i)^s` tends to `(-W)^s` as `ε → 0⁺`. -/
theorem tendsto_cpow_neg_add_mul_I {W : ℝ} (hW : 0 < W) (s : ℂ) :
    Tendsto (fun ε : ℝ => (-(W : ℂ) + ε * I) ^ s) (𝓝[>] 0) (𝓝 ((-(W : ℂ)) ^ s)) := by
  have hre : (-(W : ℂ)).re < 0 := by simp [hW]
  have him : (-(W : ℂ)).im = 0 := by simp
  have hne : ∀ ε : ℝ, -(W : ℂ) + ε * I ≠ 0 := fun ε h => by
    have := congrArg re h
    simp at this
    linarith
  have hpath : Tendsto (fun ε : ℝ => -(W : ℂ) + ε * I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-(W : ℂ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun ε : ℝ => -(W : ℂ) + ε * I) (𝓝 0) (𝓝 (-(W : ℂ) + (0 : ℝ) * I)) :=
        (continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto 0
      rw [ofReal_zero, zero_mul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa using le_of_lt hε
  have hlog := (continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto.comp hpath
  have hexp := (continuous_exp.tendsto _).comp (hlog.mul_const s)
  rw [cpow_def_of_ne_zero (by simpa using hW.ne')]
  refine hexp.congr fun ε => ?_
  simp only [Function.comp_apply]
  rw [cpow_def_of_ne_zero (hne ε)]

/-- **Norm bound, uniform in `ε`.** For `W > 0` and `s ≥ 0`, `‖(-W + ε i)^{-s}‖ ≤ W^{-s}`. -/
theorem norm_cpow_neg_add_mul_I_le {W ε s : ℝ} (hW : 0 < W) (hs : 0 ≤ s) :
    ‖(-(W : ℂ) + ε * I) ^ (-(s : ℂ))‖ ≤ W ^ (-s) := by
  rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
  refine Real.rpow_le_rpow_of_nonpos hW ?_ (by linarith)
  calc W = |(-(W : ℂ) + ε * I).re| := by simp [abs_of_pos hW]
    _ ≤ ‖-(W : ℂ) + ε * I‖ := abs_re_le_norm _

/-- **Lipschitz bound in `W`, uniform in `ε > 0`** (used for the Pauli–Villars difference):
`‖(-W₁ + ε i)^{-s} - (-W₂ + ε i)^{-s}‖ ≤ s |W₁ - W₂| (min W₁ W₂)^{-(s+1)}`. -/
theorem norm_cpow_sub_cpow_le {W₁ W₂ ε s : ℝ} (h₁ : 0 < W₁) (h₂ : 0 < W₂) (hε : 0 < ε)
    (hs : 0 < s) :
    ‖(-(W₁ : ℂ) + ε * I) ^ (-(s : ℂ)) - (-(W₂ : ℂ) + ε * I) ^ (-(s : ℂ))‖
      ≤ s * |W₁ - W₂| * (min W₁ W₂) ^ (-(s + 1)) := by
  have hm0 : 0 < min W₁ W₂ := lt_min h₁ h₂
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (-(x : ℂ) + ε * I) ^ (-(s : ℂ)))
      (-(s : ℂ) * (-(x : ℂ) + ε * I) ^ (-(s : ℂ) - 1) * (-1)) x := by
    intro x
    have hmem : -(x : ℂ) + ε * I ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      right
      simp [hε.ne']
    have hφ : HasDerivAt (fun y : ℂ => -y + ε * I) (-1) (x : ℂ) :=
      ((hasDerivAt_id (x : ℂ)).neg).add_const (ε * I)
    exact ((Complex.hasStrictDerivAt_cpow_const hmem).hasDerivAt.comp (x : ℂ) hφ).comp_ofReal
  -- on `[min W₁ W₂, ∞)`, `‖-x + ε i‖ ≥ x ≥ min W₁ W₂`
  have hbound : ∀ x ∈ Set.Ici (min W₁ W₂),
      ‖-(s : ℂ) * (-(x : ℂ) + ε * I) ^ (-(s : ℂ) - 1) * (-1)‖
        ≤ s * (min W₁ W₂) ^ (-(s + 1)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hm0 hx
    rw [show -(s : ℂ) - 1 = -((s + 1 : ℝ) : ℂ) by push_cast; ring, norm_mul, norm_mul, norm_neg,
      norm_neg, norm_one, mul_one, norm_real, Real.norm_of_nonneg hs.le]
    have h1 := norm_cpow_neg_add_mul_I_le (ε := ε) hx0 (by linarith : 0 ≤ s + 1)
    have h2 : x ^ (-(s + 1)) ≤ (min W₁ W₂) ^ (-(s + 1)) :=
      Real.rpow_le_rpow_of_nonpos hm0 hx (by linarith)
    gcongr
    exact h1.trans h2
  have key := (convex_Ici (min W₁ W₂)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hderiv x).hasDerivWithinAt) hbound (min_le_right W₁ W₂) (min_le_left W₁ W₂)
  rw [Real.norm_eq_abs] at key
  calc _ ≤ s * (min W₁ W₂) ^ (-(s + 1)) * |W₁ - W₂| := key
    _ = _ := by ring

end QED.Integration

end
