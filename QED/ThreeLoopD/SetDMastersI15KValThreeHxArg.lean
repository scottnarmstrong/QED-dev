/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValThreeG
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiLimits
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Set (d), master `I₁₅`: the arguments of the `x`-primitive of `A₂₃,₃`

For `u ∈ (0, 1)` the `x`-slice of `A₂₃,₃ = (v² b₁³ + b₂³) / (6 u)` (`v = 1 - u`) is a
polynomial in `log x`, `log (1 - x)`, `A = log (1 + v x / u)` and `B = log (1 - v x)`
(`QED.ThreeLoopD.i15HxF`), since `u + v x = u e^A` and the polynomial `P` of `b₁` factors as
`(u + v x)(1 - v x)`. Its primitive in `x` uses `G(X) = Li₃ X - Li₂ X log X` and `Li₂ X` at the
twenty cross-ratios `X ∈ (0, 1)` of the points `0, 1, -u/v, 1/v, ∞` with `x`
(`QED.ThreeLoopD.i15HxX0`, ..., `QED.ThreeLoopD.i15HxX19`). This file gives, for each, the
positivity, the complement `1 - X`, the logarithm in `log x`, `log (1 - x)`, `A`, `B`, `log u`,
`log (1 - u)`, `log (1 + u)`, the values at `x = 0` and `x = 1` and the continuity on `[0, 1]`;
and the limit at `0⁺` of a polynomial in `x`, `log x` and three functions that are `O(x)` near
`0` (`QED.ThreeLoopD.i15Hx_tendsto_poly`).

## Main results

* `QED.ThreeLoopD.i15HxX0_log`, ..., `QED.ThreeLoopD.i15HxX19_log`: the logarithms of the
  arguments.
* `QED.ThreeLoopD.i15Hx_tendsto_poly`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- `A = log (1 + v x / u)`, so that `log (u + v x) = log u + A`. -/
noncomputable def i15HxA (u t : ℝ) : ℝ := log (1 + (1 - u) * t / u)

/-- `B = log (1 - v x)`. -/
noncomputable def i15HxB (u t : ℝ) : ℝ := log (1 - (1 - u) * t)

/-- The `x`-slice of `A₂₃,₃` in the logarithms `log x`, `log (1 - x)`, `A`, `B`. -/
noncomputable def i15HxF (u t : ℝ) : ℝ :=
  ((1 - u) ^ 2 * (log t + log (1 - t) - log u - 2 * i15HxA u t - 2 * i15HxB u t) ^ 3 +
    (log t + log (1 - t) - log u) ^ 3) / (6 * u)

theorem i15Hx_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < u ∧ 0 < 1 - u ∧ 0 < 1 + u ∧ 0 < t ∧ 0 < 1 - t ∧ 0 < u + (1 - u) * t ∧
      0 < 1 - (1 - u) * t ∧ 0 < 1 + (1 - u) * t / u := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨ht0, ht1⟩ := ht
  have h1 : 0 < 1 - u := by linarith
  have h4 : 0 < 1 - t := by linarith
  have h5 : 0 < u + (1 - u) * t := by nlinarith [mul_pos h1 ht0]
  have h6 : 0 < 1 - (1 - u) * t := by nlinarith [mul_pos h1 h4]
  have h7 : 0 < 1 + (1 - u) * t / u := by have := div_pos (mul_pos h1 ht0) hu0; linarith
  exact ⟨hu0, h1, by linarith, ht0, h4, h5, h6, h7⟩

theorem i15Hx_den_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < u + (1 - u) * t ∧ 0 < 1 - (1 - u) * t ∧ 0 < 1 + u := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨ht0, ht1⟩ := ht
  have h1 : 0 < 1 - u := by linarith
  have h2 : 0 ≤ 1 - t := by linarith
  exact ⟨by nlinarith [mul_nonneg h1.le ht0], by nlinarith [mul_nonneg h1.le h2], by linarith⟩

/-- The argument `X0`. -/
noncomputable def i15HxX0 (u t : ℝ) : ℝ := u * (1 - t) / (u + (1 - u) * t)

/-- The argument `X1`. -/
noncomputable def i15HxX1 (u t : ℝ) : ℝ := t / (u + (1 - u) * t)

/-- The argument `X2`. -/
noncomputable def i15HxX2 (u t : ℝ) : ℝ := (1 - t) / (1 - (1 - u) * t)

/-- The argument `X3`. -/
noncomputable def i15HxX3 (u t : ℝ) : ℝ := u * t / (1 - (1 - u) * t)

/-- The argument `X4`. -/
noncomputable def i15HxX4 (_u t : ℝ) : ℝ := 1 - t

/-- The argument `X5`. -/
noncomputable def i15HxX5 (_u t : ℝ) : ℝ := t

/-- The argument `X6`. -/
noncomputable def i15HxX6 (u t : ℝ) : ℝ := u * (1 - (1 - u) * t) / (u + (1 - u) * t)

/-- The argument `X7`. -/
noncomputable def i15HxX7 (u t : ℝ) : ℝ := t * ((1 - u) * (1 + u)) / (u + (1 - u) * t)

/-- The argument `X8`. -/
noncomputable def i15HxX8 (u t : ℝ) : ℝ := u / (u + (1 - u) * t)

/-- The argument `X9`. -/
noncomputable def i15HxX9 (u t : ℝ) : ℝ := t * (1 - u) / (u + (1 - u) * t)

/-- The argument `X10`. -/
noncomputable def i15HxX10 (u t : ℝ) : ℝ := 1 - (1 - u) * t

/-- The argument `X11`. -/
noncomputable def i15HxX11 (u t : ℝ) : ℝ := t * (1 - u)

/-- The argument `X12`. -/
noncomputable def i15HxX12 (u t : ℝ) : ℝ := u * (u + (1 - u) * t) / (1 - (1 - u) * t)

/-- The argument `X13`. -/
noncomputable def i15HxX13 (u t : ℝ) : ℝ := (1 - u) * (1 + u) * (1 - t) / (1 - (1 - u) * t)

/-- The argument `X14`. -/
noncomputable def i15HxX14 (u t : ℝ) : ℝ := u + (1 - u) * t

/-- The argument `X15`. -/
noncomputable def i15HxX15 (u t : ℝ) : ℝ := (1 - u) * (1 - t)

/-- The argument `X16`. -/
noncomputable def i15HxX16 (u t : ℝ) : ℝ := u / (1 - (1 - u) * t)

/-- The argument `X17`. -/
noncomputable def i15HxX17 (u t : ℝ) : ℝ := (1 - u) * (1 - t) / (1 - (1 - u) * t)

/-- The argument `X18`. -/
noncomputable def i15HxX18 (u t : ℝ) : ℝ := (1 - (1 - u) * t) / (1 + u)

/-- The argument `X19`. -/
noncomputable def i15HxX19 (u t : ℝ) : ℝ := (u + (1 - u) * t) / (1 + u)

theorem i15Hx_expA {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    exp (i15HxA u t) = (u + (1 - u) * t) / u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  rw [i15HxA, exp_log h7]
  field_simp

theorem i15HxX0_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX0 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX0
  positivity

theorem i15HxX1_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX1 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX1
  positivity

theorem i15HxX2_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX2 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX2
  positivity

theorem i15HxX3_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX3 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX3
  positivity

theorem i15HxX4_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX4 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX4
  positivity

theorem i15HxX5_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX5 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX5
  positivity

theorem i15HxX6_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX6 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX6
  positivity

theorem i15HxX7_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX7 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX7
  positivity

theorem i15HxX8_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX8 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX8
  positivity

theorem i15HxX9_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX9 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX9
  positivity

theorem i15HxX10_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX10 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX10
  positivity

theorem i15HxX11_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX11 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX11
  positivity

theorem i15HxX12_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX12 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX12
  positivity

theorem i15HxX13_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX13 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX13
  positivity

theorem i15HxX14_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX14 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX14
  positivity

theorem i15HxX15_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX15 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX15
  positivity

theorem i15HxX16_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX16 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX16
  positivity

theorem i15HxX17_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX17 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX17
  positivity

theorem i15HxX18_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX18 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX18
  positivity

theorem i15HxX19_pos {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < i15HxX19 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxX19
  positivity

theorem i15HxX0_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX0 u t = i15HxX1 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX0 i15HxX1
  rw [eq_div_iff h5', sub_mul, one_mul, div_mul_cancel₀ _ h5']
  ring

theorem i15HxX0_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX0 u t) = log (1 - t) + -i15HxA u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX0_pos hu ht)]
  simp only [i15HxX0, exp_add, exp_neg, i15Hx_expA hu ht, exp_log h4]
  field_simp

theorem i15HxX0_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX0 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX0_pos hu ht, by linarith [i15HxX0_one_sub hu ht, i15HxX1_pos hu ht]⟩

theorem i15HxX1_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX1 u t = i15HxX0 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX1 i15HxX0
  rw [eq_div_iff h5', sub_mul, one_mul, div_mul_cancel₀ _ h5']
  ring

theorem i15HxX1_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX1 u t) = log t + -i15HxA u t + (-log u) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX1_pos hu ht)]
  simp only [i15HxX1, exp_add, exp_neg, i15Hx_expA hu ht, exp_log h0, exp_log h3]
  field_simp

theorem i15HxX1_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX1 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX1_pos hu ht, by linarith [i15HxX1_one_sub hu ht, i15HxX0_pos hu ht]⟩

theorem i15HxX2_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX2 u t = i15HxX3 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX2 i15HxX3
  rw [eq_div_iff h6', sub_mul, one_mul, div_mul_cancel₀ _ h6']
  ring

theorem i15HxX2_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX2 u t) = log (1 - t) + -i15HxB u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX2_pos hu ht)]
  simp only [i15HxX2, exp_add, exp_neg, i15HxB, exp_log h6, exp_log h4]
  field_simp

theorem i15HxX2_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX2 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX2_pos hu ht, by linarith [i15HxX2_one_sub hu ht, i15HxX3_pos hu ht]⟩

theorem i15HxX3_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX3 u t = i15HxX2 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX3 i15HxX2
  rw [eq_div_iff h6', sub_mul, one_mul, div_mul_cancel₀ _ h6']
  ring

theorem i15HxX3_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX3 u t) = log t + -i15HxB u t + (log u) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX3_pos hu ht)]
  simp only [i15HxX3, exp_add, exp_neg, i15HxB, exp_log h6, exp_log h0, exp_log h3]
  field_simp

theorem i15HxX3_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX3 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX3_pos hu ht, by linarith [i15HxX3_one_sub hu ht, i15HxX2_pos hu ht]⟩

theorem i15HxX4_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX4 u t = i15HxX5 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX4 i15HxX5
  ring

theorem i15HxX4_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX4 u t) = log (1 - t) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX4_pos hu ht)]
  simp only [i15HxX4, exp_log h4]

theorem i15HxX4_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX4 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX4_pos hu ht, by linarith [i15HxX4_one_sub hu ht, i15HxX5_pos hu ht]⟩

theorem i15HxX5_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX5 u t = i15HxX4 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX5 i15HxX4
  ring

theorem i15HxX5_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX5 u t) = log t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX5_pos hu ht)]
  simp only [i15HxX5, exp_log h3]

theorem i15HxX5_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX5 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX5_pos hu ht, by linarith [i15HxX5_one_sub hu ht, i15HxX4_pos hu ht]⟩

theorem i15HxX6_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX6 u t = i15HxX7 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX6 i15HxX7
  rw [eq_div_iff h5', sub_mul, one_mul, div_mul_cancel₀ _ h5']
  ring

theorem i15HxX6_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX6 u t) = -i15HxA u t + i15HxB u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX6_pos hu ht)]
  simp only [i15HxX6, exp_add, exp_neg, i15Hx_expA hu ht, i15HxB, exp_log h6]
  field_simp

theorem i15HxX6_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX6 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX6_pos hu ht, by linarith [i15HxX6_one_sub hu ht, i15HxX7_pos hu ht]⟩

theorem i15HxX7_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX7 u t = i15HxX6 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX7 i15HxX6
  rw [eq_div_iff h5', sub_mul, one_mul, div_mul_cancel₀ _ h5']
  ring

theorem i15HxX7_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX7 u t) = log t + -i15HxA u t + (-log u + log (1 - u) + log (1 + u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX7_pos hu ht)]
  simp only [i15HxX7, exp_add, exp_neg, i15Hx_expA hu ht, exp_log h0, exp_log h1, exp_log h2,
      exp_log h3]
  field_simp

theorem i15HxX7_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX7 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX7_pos hu ht, by linarith [i15HxX7_one_sub hu ht, i15HxX6_pos hu ht]⟩

theorem i15HxX8_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX8 u t = i15HxX9 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX8 i15HxX9
  rw [eq_div_iff h5', sub_mul, one_mul, div_mul_cancel₀ _ h5']
  ring

theorem i15HxX8_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX8 u t) = -i15HxA u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX8_pos hu ht)]
  simp only [i15HxX8, exp_neg, i15Hx_expA hu ht]
  field_simp

theorem i15HxX8_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX8 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX8_pos hu ht, by linarith [i15HxX8_one_sub hu ht, i15HxX9_pos hu ht]⟩

theorem i15HxX9_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX9 u t = i15HxX8 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX9 i15HxX8
  rw [eq_div_iff h5', sub_mul, one_mul, div_mul_cancel₀ _ h5']
  ring

theorem i15HxX9_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX9 u t) = log t + -i15HxA u t + (-log u + log (1 - u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX9_pos hu ht)]
  simp only [i15HxX9, exp_add, exp_neg, i15Hx_expA hu ht, exp_log h0, exp_log h1, exp_log h3]
  field_simp

theorem i15HxX9_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX9 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX9_pos hu ht, by linarith [i15HxX9_one_sub hu ht, i15HxX8_pos hu ht]⟩

theorem i15HxX10_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX10 u t = i15HxX11 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX10 i15HxX11
  ring

theorem i15HxX10_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX10 u t) = i15HxB u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX10_pos hu ht)]
  simp only [i15HxX10, i15HxB, exp_log h6]

theorem i15HxX10_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX10 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX10_pos hu ht, by linarith [i15HxX10_one_sub hu ht, i15HxX11_pos hu ht]⟩

theorem i15HxX11_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX11 u t = i15HxX10 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX11 i15HxX10
  ring

theorem i15HxX11_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX11 u t) = log t + (log (1 - u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX11_pos hu ht)]
  simp only [i15HxX11, exp_add, exp_log h1, exp_log h3]

theorem i15HxX11_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX11 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX11_pos hu ht, by linarith [i15HxX11_one_sub hu ht, i15HxX10_pos hu ht]⟩

theorem i15HxX12_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX12 u t = i15HxX13 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX12 i15HxX13
  rw [eq_div_iff h6', sub_mul, one_mul, div_mul_cancel₀ _ h6']
  ring

theorem i15HxX12_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX12 u t) = i15HxA u t + -i15HxB u t + (log u + log u) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX12_pos hu ht)]
  simp only [i15HxX12, exp_add, exp_neg, i15Hx_expA hu ht, i15HxB, exp_log h6, exp_log h0]
  field_simp

theorem i15HxX12_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX12 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX12_pos hu ht, by linarith [i15HxX12_one_sub hu ht, i15HxX13_pos hu ht]⟩

theorem i15HxX13_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX13 u t = i15HxX12 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX13 i15HxX12
  rw [eq_div_iff h6', sub_mul, one_mul, div_mul_cancel₀ _ h6']
  ring

theorem i15HxX13_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX13 u t) = log (1 - t) + -i15HxB u t + (log (1 - u) + log (1 + u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX13_pos hu ht)]
  simp only [i15HxX13, exp_add, exp_neg, i15HxB, exp_log h6, exp_log h1, exp_log h2, exp_log h4]
  field_simp

theorem i15HxX13_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX13 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX13_pos hu ht, by linarith [i15HxX13_one_sub hu ht, i15HxX12_pos hu ht]⟩

theorem i15HxX14_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX14 u t = i15HxX15 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX14 i15HxX15
  ring

theorem i15HxX14_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX14 u t) = i15HxA u t + (log u) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX14_pos hu ht)]
  simp only [i15HxX14, exp_add, i15Hx_expA hu ht, exp_log h0]
  field_simp

theorem i15HxX14_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX14 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX14_pos hu ht, by linarith [i15HxX14_one_sub hu ht, i15HxX15_pos hu ht]⟩

theorem i15HxX15_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX15 u t = i15HxX14 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX15 i15HxX14
  ring

theorem i15HxX15_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX15 u t) = log (1 - t) + (log (1 - u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX15_pos hu ht)]
  simp only [i15HxX15, exp_add, exp_log h1, exp_log h4]
  field_simp

theorem i15HxX15_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX15 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX15_pos hu ht, by linarith [i15HxX15_one_sub hu ht, i15HxX14_pos hu ht]⟩

theorem i15HxX16_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX16 u t = i15HxX17 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX16 i15HxX17
  rw [eq_div_iff h6', sub_mul, one_mul, div_mul_cancel₀ _ h6']
  ring

theorem i15HxX16_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX16 u t) = -i15HxB u t + (log u) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX16_pos hu ht)]
  simp only [i15HxX16, exp_add, exp_neg, i15HxB, exp_log h6, exp_log h0]
  field_simp

theorem i15HxX16_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX16 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX16_pos hu ht, by linarith [i15HxX16_one_sub hu ht, i15HxX17_pos hu ht]⟩

theorem i15HxX17_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX17 u t = i15HxX16 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX17 i15HxX16
  rw [eq_div_iff h6', sub_mul, one_mul, div_mul_cancel₀ _ h6']
  ring

theorem i15HxX17_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX17 u t) = log (1 - t) + -i15HxB u t + (log (1 - u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX17_pos hu ht)]
  simp only [i15HxX17, exp_add, exp_neg, i15HxB, exp_log h6, exp_log h1, exp_log h4]
  field_simp

theorem i15HxX17_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX17 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX17_pos hu ht, by linarith [i15HxX17_one_sub hu ht, i15HxX16_pos hu ht]⟩

theorem i15HxX18_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX18 u t = i15HxX19 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX18 i15HxX19
  rw [eq_div_iff h2', sub_mul, one_mul, div_mul_cancel₀ _ h2']
  ring

theorem i15HxX18_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX18 u t) = i15HxB u t + (-log (1 + u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX18_pos hu ht)]
  simp only [i15HxX18, exp_add, exp_neg, i15HxB, exp_log h6, exp_log h2]
  field_simp

theorem i15HxX18_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX18 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX18_pos hu ht, by linarith [i15HxX18_one_sub hu ht, i15HxX19_pos hu ht]⟩

theorem i15HxX19_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - i15HxX19 u t = i15HxX18 u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  unfold i15HxX19 i15HxX18
  rw [eq_div_iff h2', sub_mul, one_mul, div_mul_cancel₀ _ h2']
  ring

theorem i15HxX19_log {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    log (i15HxX19 u t) = i15HxA u t + (log u + -log (1 + u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have h0' := h0.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h5' := h5.ne'
  have h6' := h6.ne'
  rw [← exp_eq_exp, exp_log (i15HxX19_pos hu ht)]
  simp only [i15HxX19, exp_add, exp_neg, i15Hx_expA hu ht, exp_log h0, exp_log h2]
  field_simp

theorem i15HxX19_mem {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxX19 u t ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15HxX19_pos hu ht, by linarith [i15HxX19_one_sub hu ht, i15HxX18_pos hu ht]⟩

theorem i15HxX0_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX0 u 0 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX0
  simp [h0]

theorem i15HxX0_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX0 u 1 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX0
  simp

theorem continuousAt_i15HxX0 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX0 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX0
  exact ContinuousAt.div (by fun_prop) (by fun_prop) ha.ne'

theorem i15HxX1_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX1 u 0 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX1
  simp

theorem i15HxX1_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX1 u 1 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX1
  simp

theorem continuousAt_i15HxX1 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX1 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX1
  exact ContinuousAt.div (by fun_prop) (by fun_prop) ha.ne'

theorem i15HxX2_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX2 u 0 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX2
  simp

theorem i15HxX2_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX2 u 1 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX2
  simp

theorem continuousAt_i15HxX2 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX2 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX2
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hb.ne'

theorem i15HxX3_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX3 u 0 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX3
  simp

theorem i15HxX3_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX3 u 1 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX3
  simp [h0]

theorem continuousAt_i15HxX3 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX3 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX3
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hb.ne'

theorem i15HxX4_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX4 u 0 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX4
  simp

theorem i15HxX4_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX4 u 1 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX4
  simp

theorem continuousAt_i15HxX4 (u t : ℝ) : ContinuousAt (i15HxX4 u) t := by
  unfold i15HxX4
  fun_prop

theorem i15HxX5_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX5 u 0 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX5
  simp

theorem i15HxX5_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX5 u 1 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX5
  simp

theorem continuousAt_i15HxX5 (u t : ℝ) : ContinuousAt (i15HxX5 u) t := by
  unfold i15HxX5
  fun_prop

theorem i15HxX6_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX6 u 0 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX6
  simp [h0]

theorem i15HxX6_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX6 u 1 = u ^ 2 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX6
  field_simp
  ring

theorem continuousAt_i15HxX6 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX6 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX6
  exact ContinuousAt.div (by fun_prop) (by fun_prop) ha.ne'

theorem i15HxX7_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX7 u 0 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX7
  simp

theorem i15HxX7_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX7 u 1 = (1 - u) * (1 + u) := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX7
  simp

theorem continuousAt_i15HxX7 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX7 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX7
  exact ContinuousAt.div (by fun_prop) (by fun_prop) ha.ne'

theorem i15HxX8_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX8 u 0 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX8
  simp [h0]

theorem i15HxX8_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX8 u 1 = u := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX8
  simp

theorem continuousAt_i15HxX8 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX8 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX8
  exact ContinuousAt.div (by fun_prop) (by fun_prop) ha.ne'

theorem i15HxX9_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX9 u 0 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX9
  simp

theorem i15HxX9_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX9 u 1 = 1 - u := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX9
  simp

theorem continuousAt_i15HxX9 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX9 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX9
  exact ContinuousAt.div (by fun_prop) (by fun_prop) ha.ne'

theorem i15HxX10_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX10 u 0 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX10
  simp

theorem i15HxX10_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX10 u 1 = u := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX10
  simp

theorem continuousAt_i15HxX10 (u t : ℝ) : ContinuousAt (i15HxX10 u) t := by
  unfold i15HxX10
  fun_prop

theorem i15HxX11_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX11 u 0 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX11
  simp

theorem i15HxX11_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX11 u 1 = 1 - u := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX11
  simp

theorem continuousAt_i15HxX11 (u t : ℝ) : ContinuousAt (i15HxX11 u) t := by
  unfold i15HxX11
  fun_prop

theorem i15HxX12_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX12 u 0 = u ^ 2 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX12
  field_simp
  ring

theorem i15HxX12_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX12 u 1 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX12
  simp [h0]

theorem continuousAt_i15HxX12 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX12 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX12
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hb.ne'

theorem i15HxX13_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX13 u 0 = (1 - u) * (1 + u) := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX13
  simp

theorem i15HxX13_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX13 u 1 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX13
  simp

theorem continuousAt_i15HxX13 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX13 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX13
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hb.ne'

theorem i15HxX14_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX14 u 0 = u := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX14
  simp

theorem i15HxX14_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX14 u 1 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX14
  simp

theorem continuousAt_i15HxX14 (u t : ℝ) : ContinuousAt (i15HxX14 u) t := by
  unfold i15HxX14
  fun_prop

theorem i15HxX15_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX15 u 0 = 1 - u := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX15
  simp

theorem i15HxX15_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX15 u 1 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX15
  simp

theorem continuousAt_i15HxX15 (u t : ℝ) : ContinuousAt (i15HxX15 u) t := by
  unfold i15HxX15
  fun_prop

theorem i15HxX16_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX16 u 0 = u := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX16
  simp

theorem i15HxX16_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX16 u 1 = 1 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX16
  simp [h0]

theorem continuousAt_i15HxX16 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX16 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX16
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hb.ne'

theorem i15HxX17_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX17 u 0 = 1 - u := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX17
  simp

theorem i15HxX17_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX17 u 1 = 0 := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX17
  simp

theorem continuousAt_i15HxX17 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX17 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX17
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hb.ne'

theorem i15HxX18_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX18 u 0 = 1 / (1 + u) := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX18
  simp

theorem i15HxX18_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX18 u 1 = u / (1 + u) := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX18
  simp

theorem continuousAt_i15HxX18 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX18 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX18
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hc.ne'

theorem i15HxX19_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX19 u 0 = u / (1 + u) := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX19
  simp

theorem i15HxX19_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15HxX19 u 1 = 1 / (1 + u) := by
  have h0 : u ≠ 0 := hu.1.ne'
  have h2 : 1 + u ≠ 0 := by linarith [hu.1]
  unfold i15HxX19
  simp

theorem continuousAt_i15HxX19 {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (i15HxX19 u) t := by
  obtain ⟨ha, hb, hc⟩ := i15Hx_den_pos hu ht
  unfold i15HxX19
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hc.ne'

theorem i15Hx_abs_log_one_sub_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    |log (1 - y)| ≤ 2 * y := by
  have hp : 0 < 1 - y := by linarith
  rw [abs_of_nonpos (log_nonpos hp.le (by linarith))]
  have h := one_sub_inv_le_log_of_pos hp
  have e : 1 - (1 - y)⁻¹ = -(y / (1 - y)) := by field_simp; ring
  have h2 : y / (1 - y) ≤ 2 * y := by rw [div_le_iff₀ hp]; nlinarith
  linarith

/-- The limit at `0⁺` of a polynomial in `t`, `log t` and three functions that are `O(t)` on
`(0, 1/2)`, with no pure powers of `log t`. -/
theorem i15Hx_tendsto_poly (P : List (ℝ × (ℕ × ℕ × ℕ × ℕ × ℕ))) {a b c : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), |a t| ≤ C * t)
    (hb : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), |b t| ≤ C * t) (hc : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), |c t| ≤ C * t)
    (hP : ∀ e ∈ P.map Prod.snd, e.2.1 ≠ 0 → e.1 + e.2.2.1 + e.2.2.2.1 + e.2.2.2.2 ≠ 0) :
    Tendsto (fun t => i15TPoly P t (log t) (a t) (b t) (c t)) (𝓝[>] 0)
      (𝓝 (i15TPoly P 0 1 0 0 0)) := by
  have hcut : ∀ f : ℝ → ℝ, (∀ t ∈ Ioo (0 : ℝ) (1 / 2), |f t| ≤ C * t) →
      ∀ t ∈ Ioo (0 : ℝ) 1, |(fun s => if s < 1 / 2 then f s else 0) t| ≤ C * t := by
    intro f hf t ht
    by_cases h : t < 1 / 2
    · simp only [h, ↓reduceIte]; exact hf t ⟨ht.1, h⟩
    · simp only [h, ↓reduceIte, abs_zero]; exact mul_nonneg hC ht.1.le
  have h := tendsto_i15TPoly_zero' P (hcut a ha) (hcut b hb) (hcut c hc) hP
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
  simp only [ht.2, ↓reduceIte]

theorem i15Hx_bounds {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∀ t ∈ Ioo (0 : ℝ) (1 / 2), |log (1 - t)| ≤ (2 + u⁻¹) * t) ∧
      (∀ t ∈ Ioo (0 : ℝ) (1 / 2), |i15HxA u t| ≤ (2 + u⁻¹) * t) ∧
      (∀ t ∈ Ioo (0 : ℝ) (1 / 2), |i15HxB u t| ≤ (2 + u⁻¹) * t) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hq : 0 < u⁻¹ := inv_pos.2 hu0
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have := i15Hx_abs_log_one_sub_le ht.1.le ht.2.le
    nlinarith [ht.1]
  · have h1 : 0 ≤ (1 - u) * t / u := div_nonneg (mul_nonneg (by linarith) ht.1.le) hu0.le
    have h := abs_log_one_add_le h1
    unfold i15HxA
    refine h.trans ?_
    have e : (1 - u) * t / u = (1 - u) * (u⁻¹ * t) := by field_simp
    rw [e]
    nlinarith [mul_pos hq ht.1, ht.1]
  · have h := i15Hx_abs_log_one_sub_le (y := (1 - u) * t) (mul_nonneg (by linarith) ht.1.le)
      (by nlinarith [ht.1, ht.2])
    unfold i15HxB
    refine h.trans ?_
    nlinarith [mul_pos hq ht.1, ht.1]

theorem i15Hx_val_mem {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    u ^ 2 ∈ Ioc (0 : ℝ) 1 ∧ (1 - u) * (1 + u) ∈ Ioc (0 : ℝ) 1 ∧ u ∈ Ioc (0 : ℝ) 1 ∧
      1 - u ∈ Ioc (0 : ℝ) 1 ∧ 1 / (1 + u) ∈ Ioc (0 : ℝ) 1 ∧ u / (1 + u) ∈ Ioc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hu
  have hp : 0 < 1 + u := by linarith
  refine ⟨⟨by positivity, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩, ⟨h0, h1.le⟩,
    ⟨by linarith, by linarith⟩, ⟨by positivity, by rw [div_le_one hp]; linarith⟩,
    ⟨by positivity, by rw [div_le_one hp]; linarith⟩⟩

end QED.ThreeLoopD
