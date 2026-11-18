/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXKernelBasic
import QED.Polylog.Reflection
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Endpoint limits of the crossed-ladder boundary function and kernel (helper level, O2-25)

The boundary function `G` of eq. (4.8) of `docs/TWO-LOOP-UNITS.md` (`crossedBoundary`) has
coefficients with poles of order one at `Y = 0` and order three at `Y = 1`; the regular part
`crossedKernelReg` of the kernel `K_X` has poles of order two and four. The poles cancel. This file
proves the one-sided limits

* `QED.TwoLoop.Units.tendsto_crossedBoundary_zero`: `G(0⁺) = 17/24 + ζ(2)/4`;
* `QED.TwoLoop.Units.tendsto_crossedBoundary_one`: `G(1⁻) = 1/3 + ζ(2)/12` (eq. (4.10));
* `QED.TwoLoop.Units.tendsto_crossedKernelReg_zero`, `…_one`: the regular part of `K_X` tends to
  `-7/4 - ζ(2)/2` at `0⁺` and to `(ζ(2) - 1)/12` at `1⁻`.

## Method

Near `Y = 0` put `s = Y`; near `Y = 1` put `s = 1 - Y` and use `Li₂ (1 - s) = ζ(2) - log s log
(1 - s) - Li₂ s` (Euler's reflection, `Li₂_add_Li₂_one_sub`) and `D(1 - s) = -D(s)`. In both cases
the functions of `s` are replaced by their expansions to order `s⁴` with remainders

* `li2Rem s = Li₂ s - (s + s²/4 + s³/9 + s⁴/16)`,
* `crossedDRem s = D(s) + log s log (1 - 2s) - (π²/4 - 2s + (7/9) s³ + (5/3) s⁴)`,
* `logRem s`, `logRem (2s)` for `log (1 - s)`, `log (1 - 2s)`,

each `O(s⁵)` (`QED.Polylog.abs_li2Rem_le`, `abs_crossedDRem_le`, `QED.Polylog.abs_logRem_le`).
This gives an exact identity on `(0, 1/4)` of the shape `endpointForm`:
`U(s) + V(s) s log s + W(s) s log² s + Σ cᵢ(s) rᵢ(s)`, where `U, V, W, cᵢ` are rational functions
continuous at `0` and `rᵢ(s)` are the remainders divided by `s⁴` (some times `log s`), which tend
to `0` (`tendsto_endpointForm`). The limit is `U(0)`. The rational functions were computed in exact
arithmetic (sympy, from the Lean forms of `G` and `K_X`); each identity is checked here by
`field_simp` and `ring`.

Here `ζ(2) = π²/6`.
-/

public section

open Real Set Filter Topology QED.Polylog

namespace QED.TwoLoop.Units

/-- The shape of the endpoint expansions: a rational part `U`, logarithmic parts `V s log s` and
`W s log² s`, and six remainder terms, each a coefficient times a remainder divided by `s⁴`. -/
noncomputable def endpointForm (U V W c₁ c₂ c₃ c₄ c₅ c₆ : ℝ → ℝ) (s : ℝ) : ℝ :=
  U s + V s * (s * log s) + W s * (s * log s ^ 2) + c₁ s * (li2Rem s / s ^ 4) +
    c₂ s * (crossedDRem s / s ^ 4) + c₃ s * (logRem (2 * s) * log s / s ^ 4) +
    c₄ s * (logRem s / s ^ 4) + c₅ s * (logRem s * log s / s ^ 4) + c₆ s * (logRem s ^ 2 / s ^ 4)

/-- The six remainder terms of `endpointForm` tend to `0` at `0⁺`. -/
theorem tendsto_endpointForm_remainders :
    Tendsto (fun s => li2Rem s / s ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun s => crossedDRem s / s ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun s => logRem (2 * s) * log s / s ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun s => logRem s / s ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun s => logRem s * log s / s ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun s => logRem s ^ 2 / s ^ 4) (𝓝[>] 0) (𝓝 0) := by
  have hL := tendsto_div_pow_four_of_abs_le (c := 1 / 2) (M := 2) (by norm_num)
    (fun x hx => abs_li2Rem_le hx.1.le hx.2.le)
  have hD := tendsto_div_pow_four_of_abs_le (c := 1 / 4) (M := 110) (by norm_num)
    (fun x hx => abs_crossedDRem_le ⟨hx.1.le, hx.2.le⟩)
  have h2 := tendsto_div_pow_four_of_abs_le (R := fun s => logRem (2 * s)) (c := 1 / 4) (M := 64)
    (by norm_num) (fun x hx => by
      have := abs_logRem_le (x := 2 * x) (by linarith [hx.1]) (by linarith [hx.2])
      linarith [show 2 * (2 * x) ^ 5 = 64 * x ^ 5 by ring])
  have h1 := tendsto_div_pow_four_of_abs_le (c := 1 / 2) (M := 2) (by norm_num)
    (fun x hx => abs_logRem_le hx.1.le hx.2.le)
  have h11 := tendsto_div_pow_four_of_abs_le (R := fun s => logRem s ^ 2) (c := 1 / 2) (M := 4)
    (by norm_num) (fun x hx => by
      have h := abs_logRem_le hx.1.le hx.2.le
      have hx5 : x ^ 5 ≤ 1 := pow_le_one₀ hx.1.le (by linarith [hx.2])
      have hp : 0 < x ^ 5 := pow_pos hx.1 5
      rw [abs_pow]
      have := pow_le_pow_left₀ (abs_nonneg _) h 2
      nlinarith)
  exact ⟨hL.1, hD.1, h2.2, h1.1, h1.2, h11.1⟩

/-- **The limit of an endpoint form** is the value of its rational part at `0`. -/
theorem tendsto_endpointForm {U V W c₁ c₂ c₃ c₄ c₅ c₆ : ℝ → ℝ} (hU : ContinuousAt U 0)
    (hV : ContinuousAt V 0) (hW : ContinuousAt W 0) (h₁ : ContinuousAt c₁ 0)
    (h₂ : ContinuousAt c₂ 0) (h₃ : ContinuousAt c₃ 0) (h₄ : ContinuousAt c₄ 0)
    (h₅ : ContinuousAt c₅ 0) (h₆ : ContinuousAt c₆ 0) :
    Tendsto (endpointForm U V W c₁ c₂ c₃ c₄ c₅ c₆) (𝓝[>] 0) (𝓝 (U 0)) := by
  have c : ∀ {g : ℝ → ℝ}, ContinuousAt g 0 → Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
    fun hg => hg.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆⟩ := tendsto_endpointForm_remainders
  have h := ((((((((c hU).add ((c hV).mul tendsto_mul_log_zero)).add
    ((c hW).mul tendsto_mul_log_sq_zero)).add ((c h₁).mul r₁)).add ((c h₂).mul r₂)).add
    ((c h₃).mul r₃)).add ((c h₄).mul r₄)).add ((c h₅).mul r₅)).add ((c h₆).mul r₆)
  simp only [mul_zero, add_zero] at h
  exact h

/-- The endpoint form of `crossedBoundary` at `0⁺`, an exact
identity on `(0, 1/4)`. -/
theorem endpointForm_eventuallyEq_crossedBoundary_zero :
    endpointForm
      (fun s => (-1224 + 3960 * s - 7940 * s ^ 2 + 10503 * s ^ 3 - 7957 * s ^ 4 + 2424 * s ^ 5 -
        933 * s ^ 6 + 2758 * s ^ 7 + 2318 * s ^ 8 - 2013 * s ^ 9 - 72 * π ^ 2 + 348 * s * π ^ 2 -
        720 * s ^ 2 * π ^ 2 + 432 * s ^ 3 * π ^ 2 + 360 * s ^ 4 * π ^ 2 - 252 * s ^ 5 * π ^ 2) /
        (1728 * (-1 + s) ^ 3))
      (fun s => (24 - 226 * s - 45 * s ^ 2 + 299 * s ^ 3 + 109 * s ^ 4 - 297 * s ^ 5 + 732 * s ^ 6 +
        228 * s ^ 7 - 312 * s ^ 8) / (144 * (-1 + s) ^ 3))
      (fun s => (-4 - 4 * s + 21 * s ^ 2 - 10 * s ^ 3 + s ^ 4) / (24 * (-1 + s) ^ 3))
      (fun s => (-7 * s ^ 3 + 15 * s ^ 4 - 10 * s ^ 5 - 5 * s ^ 6 + 30 * s ^ 8 - 15 * s ^ 9) /
        (12 * (-1 + s) ^ 3))
      (fun s => (-s ^ 3 + 6 * s ^ 5 - 16 * s ^ 6 + 12 * s ^ 7 + 10 * s ^ 8 - 7 * s ^ 9) /
        (12 * (-1 + s) ^ 3))
      (fun s => (s ^ 3 - 6 * s ^ 5 + 16 * s ^ 6 - 12 * s ^ 7 - 10 * s ^ 8 + 7 * s ^ 9) /
        (12 * (-1 + s) ^ 3))
      (fun s => (-s ^ 3 - 14 * s ^ 4 + 42 * s ^ 5 - 30 * s ^ 6 + 11 * s ^ 7) / (24 * (-1 + s)))
      (fun s => (7 * s ^ 3 - 4 * s ^ 5 - 8 * s ^ 6) / 12)
      (fun _ => 0)
      =ᶠ[𝓝[>] 0] crossedBoundary := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
  obtain ⟨hs0, hs1⟩ := hs
  have h0 : s ≠ 0 := hs0.ne'
  have h1 : -1 + s ≠ 0 := by linarith
  have h1' : s - 1 ≠ 0 := by linarith
  have h1'' : (1 : ℝ) - s ≠ 0 := by linarith
  unfold crossedBoundary
  unfold endpointForm li2Rem crossedDRem logRem
  field_simp
  ring

/-- The endpoint form of `crossedBoundary` at `1⁻` (in `s = 1 - Y`), an exact
identity on `(0, 1/4)`. -/
theorem endpointForm_eventuallyEq_crossedBoundary_one :
    endpointForm
      (fun s => (-1152 + 1728 * s + 8904 * s ^ 2 - 13552 * s ^ 3 + 4998 * s ^ 4 + 14250 * s ^ 5 -
        16396 * s ^ 6 + 4135 * s ^ 7 - 8 * s ^ 8 + 22 * s ^ 9 + 60 * s ^ 10 + 9 * s ^ 11 -
        48 * π ^ 2 - 504 * s * π ^ 2 + 576 * s ^ 2 * π ^ 2 - 216 * s ^ 3 * π ^ 2) /
        (3456 * (-1 + s)))
      (fun s => (-72 + 480 * s - 850 * s ^ 2 + 328 * s ^ 3 + 1165 * s ^ 4 - 1244 * s ^ 5 +
        315 * s ^ 6) / (144 * (-1 + s)))
      (fun _ => 0)
      (fun s => (-8 * s + 40 * s ^ 2 - 50 * s ^ 3 - 5 * s ^ 4 + 75 * s ^ 5 - 60 * s ^ 6 +
        15 * s ^ 7) / (12 * (-1 + s)))
      (fun s => (-4 * s + 20 * s ^ 2 - 25 * s ^ 3 - 8 * s ^ 4 + 43 * s ^ 5 - 32 * s ^ 6 +
        7 * s ^ 7) / (12 * (-1 + s)))
      (fun s => (4 * s - 20 * s ^ 2 + 25 * s ^ 3 + 8 * s ^ 4 - 43 * s ^ 5 + 32 * s ^ 6 -
        7 * s ^ 7) / (12 * (-1 + s)))
      (fun s => (96 * s ^ 2 - 216 * s ^ 3 - 104 * s ^ 4 + 368 * s ^ 5 - 84 * s ^ 6 + 21 * s ^ 7 +
        s ^ 8 - 19 * s ^ 9 - 3 * s ^ 10) / 144)
      (fun s => (8 * s - 32 * s ^ 2 + 18 * s ^ 3 + 18 * s ^ 4 - 25 * s ^ 5 + 7 * s ^ 6) / 12)
      (fun s => (-4 * s + 16 * s ^ 2 - 9 * s ^ 3 - 9 * s ^ 4 + 5 * s ^ 5 + s ^ 6) / 24)
      =ᶠ[𝓝[>] 0] (fun s => crossedBoundary (1 - s)) := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
  obtain ⟨hs0, hs1⟩ := hs
  have h0 : s ≠ 0 := hs0.ne'
  have h1 : -1 + s ≠ 0 := by linarith
  have h1' : s - 1 ≠ 0 := by linarith
  have h1'' : (1 : ℝ) - s ≠ 0 := by linarith
  have hr : Li₂ (1 - s) = π ^ 2 / 6 - log s * log (1 - s) - Li₂ s := by
    have := Li₂_add_Li₂_one_sub hs0.le (by linarith)
    linarith
  unfold crossedBoundary
  rw [hr, crossedD_one_sub, sub_sub_cancel, show (1 : ℝ) - s - 1 = -s by ring]
  unfold endpointForm li2Rem crossedDRem logRem
  field_simp
  ring

/-- The endpoint form of `crossedKernelReg` at `0⁺`, an exact
identity on `(0, 1/4)`. -/
theorem endpointForm_eventuallyEq_crossedKernelReg_zero :
    endpointForm
      (fun s => (-3024 + 14344 * s - 21701 * s ^ 2 + 15758 * s ^ 3 - 10165 * s ^ 4 + 14530 * s ^ 5 -
        20225 * s ^ 6 - 2346 * s ^ 7 + 11167 * s ^ 8 - 4026 * s ^ 9 - 144 * π ^ 2 +
        1104 * s * π ^ 2 - 2136 * s ^ 2 * π ^ 2 + 1200 * s ^ 3 * π ^ 2 - 360 * s ^ 4 * π ^ 2 +
        48 * s ^ 5 * π ^ 2) / (1728 * (-1 + s) ^ 4))
      (fun s => (-40 + 977 * s - 1358 * s ^ 2 - 546 * s ^ 3 + 2332 * s ^ 4 - 4083 * s ^ 5 +
        210 * s ^ 6 + 1596 * s ^ 7 - 624 * s ^ 8) / (144 * (-1 + s) ^ 4))
      (fun s => (22 - 53 * s + 26 * s ^ 2 - 9 * s ^ 3 + 2 * s ^ 4) / (24 * (-1 + s) ^ 4))
      (fun s => (-7 * s ^ 2 + 38 * s ^ 3 - 95 * s ^ 4 + 150 * s ^ 5 - 95 * s ^ 6 - 90 * s ^ 7 +
        105 * s ^ 8 - 30 * s ^ 9) / (12 * (-1 + s) ^ 4))
      (fun s => (-s ^ 2 + 14 * s ^ 3 - 56 * s ^ 4 + 110 * s ^ 5 - 90 * s ^ 6 - 20 * s ^ 7 +
        45 * s ^ 8 - 14 * s ^ 9) / (12 * (-1 + s) ^ 4))
      (fun s => (s ^ 2 - 14 * s ^ 3 + 56 * s ^ 4 - 110 * s ^ 5 + 90 * s ^ 6 + 20 * s ^ 7 -
        45 * s ^ 8 + 14 * s ^ 9) / (12 * (-1 + s) ^ 4))
      (fun s => (-s ^ 2 + 30 * s ^ 3 - 88 * s ^ 4 + 80 * s ^ 5 - 67 * s ^ 6 + 22 * s ^ 7) /
        (24 * (-1 + s) ^ 2))
      (fun s => (-7 * s ^ 2 + 10 * s ^ 3 - 4 * s ^ 4 - 16 * s ^ 5) / 12)
      (fun _ => 0)
      =ᶠ[𝓝[>] 0] crossedKernelReg := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
  obtain ⟨hs0, hs1⟩ := hs
  have h0 : s ≠ 0 := hs0.ne'
  have h1 : -1 + s ≠ 0 := by linarith
  have h1' : s - 1 ≠ 0 := by linarith
  have h1'' : (1 : ℝ) - s ≠ 0 := by linarith
  unfold crossedKernelReg crossedRho
  unfold endpointForm li2Rem crossedDRem logRem
  field_simp
  ring

/-- The endpoint form of `crossedKernelReg` at `1⁻` (in `s = 1 - Y`), an exact
identity on `(0, 1/4)`. -/
theorem endpointForm_eventuallyEq_crossedKernelReg_one :
    endpointForm
      (fun s => (-288 + 4608 * s + 12264 * s ^ 2 - 18320 * s ^ 3 - 1844 * s ^ 4 - 9676 * s ^ 5 +
        24389 * s ^ 6 - 7796 * s ^ 7 - 208 * s ^ 8 - 110 * s ^ 9 - 3 * s ^ 10 - 18 * s ^ 11 +
        48 * π ^ 2 - 2112 * s * π ^ 2 + 2544 * s ^ 2 * π ^ 2 - 672 * s ^ 3 * π ^ 2) /
        (3456 * (-1 + s) ^ 2))
      (fun s => (-900 + 2442 * s - 1820 * s ^ 2 - 215 * s ^ 3 - 748 * s ^ 4 + 1993 * s ^ 5 -
        630 * s ^ 6) / (144 * (-1 + s) ^ 2))
      (fun _ => 0)
      (fun s => (24 - 112 * s + 170 * s ^ 2 - 80 * s ^ 3 + 20 * s ^ 4 - 90 * s ^ 5 + 105 * s ^ 6 -
        30 * s ^ 7) / (12 * (-1 + s) ^ 2))
      (fun s => (12 - 56 * s + 85 * s ^ 2 - 40 * s ^ 3 + 5 * s ^ 4 - 44 * s ^ 5 + 53 * s ^ 6 -
        14 * s ^ 7) / (12 * (-1 + s) ^ 2))
      (fun s => (-12 + 56 * s - 85 * s ^ 2 + 40 * s ^ 3 - 5 * s ^ 4 + 44 * s ^ 5 - 53 * s ^ 6 +
        14 * s ^ 7) / (12 * (-1 + s) ^ 2))
      (fun s => (-288 * s + 696 * s ^ 2 - 240 * s ^ 3 - 4 * s ^ 4 - 224 * s ^ 5 + 35 * s ^ 6 +
        47 * s ^ 7 + 33 * s ^ 8 - s ^ 9 + 6 * s ^ 10) / (144 * (-1 + s)))
      (fun s => (24 - 64 * s + 18 * s ^ 2 + 20 * s ^ 3 + 25 * s ^ 4 - 14 * s ^ 5) / 12)
      (fun s => (-12 + 32 * s - 9 * s ^ 2 - 10 * s ^ 3 + s ^ 4 - 2 * s ^ 5) / 24)
      =ᶠ[𝓝[>] 0] (fun s => crossedKernelReg (1 - s)) := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
  obtain ⟨hs0, hs1⟩ := hs
  have h0 : s ≠ 0 := hs0.ne'
  have h1 : -1 + s ≠ 0 := by linarith
  have h1' : s - 1 ≠ 0 := by linarith
  have h1'' : (1 : ℝ) - s ≠ 0 := by linarith
  have hr : Li₂ (1 - s) = π ^ 2 / 6 - log s * log (1 - s) - Li₂ s := by
    have := Li₂_add_Li₂_one_sub hs0.le (by linarith)
    linarith
  unfold crossedKernelReg crossedRho
  rw [hr, crossedD_one_sub, sub_sub_cancel, show (1 : ℝ) - s - 1 = -s by ring]
  unfold endpointForm li2Rem crossedDRem logRem
  field_simp
  ring

/-- **`G(0⁺) = 17/24 + ζ(2)/4`** (eq. (4.10)). -/
theorem tendsto_crossedBoundary_zero :
    Tendsto crossedBoundary (𝓝[>] 0) (𝓝 (17 / 24 + π ^ 2 / 24)) := by
  have h := Tendsto.congr' endpointForm_eventuallyEq_crossedBoundary_zero (tendsto_endpointForm
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)))
  convert h using 2
  norm_num
  ring

/-- **`G(1⁻) = 1/3 + ζ(2)/12`** (eq. (4.10)). -/
theorem tendsto_crossedBoundary_one :
    Tendsto crossedBoundary (𝓝[<] 1) (𝓝 (1 / 3 + π ^ 2 / 72)) := by
  have h := Tendsto.congr' endpointForm_eventuallyEq_crossedBoundary_one (tendsto_endpointForm
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)))
  have h' := h.comp tendsto_one_sub_nhdsLT_one
  have e : (fun s => crossedBoundary (1 - s)) ∘ (fun Y : ℝ => 1 - Y) = crossedBoundary := by
    funext Y
    simp
  rw [e] at h'
  convert h' using 2
  norm_num
  ring

/-- The regular part of `K_X` tends to `-7/4 - ζ(2)/2` at `0⁺`. -/
theorem tendsto_crossedKernelReg_zero :
    Tendsto crossedKernelReg (𝓝[>] 0) (𝓝 (-(7 / 4) - π ^ 2 / 12)) := by
  have h := Tendsto.congr' endpointForm_eventuallyEq_crossedKernelReg_zero (tendsto_endpointForm
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)))
  convert h using 2
  norm_num
  ring

/-- The regular part of `K_X` tends to `(ζ(2) - 1)/12` at `1⁻`. -/
theorem tendsto_crossedKernelReg_one :
    Tendsto crossedKernelReg (𝓝[<] 1) (𝓝 (-(1 / 12) + π ^ 2 / 72)) := by
  have h := Tendsto.congr' endpointForm_eventuallyEq_crossedKernelReg_one (tendsto_endpointForm
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))
      (by fun_prop (disch := norm_num)))
  have h' := h.comp tendsto_one_sub_nhdsLT_one
  have e : (fun s => crossedKernelReg (1 - s)) ∘ (fun Y : ℝ => 1 - Y) = crossedKernelReg := by
    funext Y
    simp
  rw [e] at h'
  convert h' using 2
  norm_num
  ring

end QED.TwoLoop.Units
