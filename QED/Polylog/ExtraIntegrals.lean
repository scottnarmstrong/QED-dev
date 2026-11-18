/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.Polylog.Deriv
import QED.Polylog.Integral
import QED.Polylog.Landen
import QED.Polylog.Reflection
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ExtendFrom

/-!
# Weight-three logarithmic integrals over `[0, 1]`

Classical definite integrals used in the exact evaluation of the crossed-ladder unit
(section 4.5 of `docs/TWO-LOOP-UNITS.md`).

## Main results

* `QED.Polylog.integral_Li₂_div`: `∫₀¹ Li₂ x / x = ζ(3)`.
* `QED.Polylog.integral_log_mul_log_one_sub_div`: `∫₀¹ log x log (1 - x) / x = ζ(3)`.
* `QED.Polylog.integral_log_one_sub_sq_div`: `∫₀¹ log (1 - x) ² / x = 2 ζ(3)` (`J₁`).
* `QED.Polylog.integral_log_one_sub_sq_sq_div`: `∫₀¹ log (1 - x²) ² / x = ζ(3)`.
* `QED.Polylog.integral_log_one_add_sq_div`: `∫₀¹ log (1 + x) ² / x = ζ(3) / 4` (`J₃`).
* `QED.Polylog.integral_log_one_sub_mul_log_one_add_div`:
  `∫₀¹ log (1 - x) log (1 + x) / x = -(5/8) ζ(3)` (`J₂`).
* `QED.Polylog.intervalIntegrable_and_integral_log_one_sub_div`: `∫₀¹ log (1 - x) / x = -π²/6`.
* `QED.Polylog.intervalIntegrable_and_integral_A₁` … `_A₄`:
  `∫₀¹ (Li₂ x - π²/6)/(1 - x) = -2 ζ(3)`, `∫₀¹ (Li₂ (-x) + π²/12)/(1 - x) = (5/8) ζ(3)`,
  `∫₀¹ Li₂ x/(1 + x) = (π²/6) log 2 - (5/8) ζ(3)`, `∫₀¹ Li₂ (-x)/(1 + x) = ζ(3)/4 - (π²/12) log 2`,
  with antiderivatives `primA₁` … `primA₄` (one integration by parts against `∓ log (1 ∓ x)`).
* `QED.Polylog.monotoneOn_Li₂`: `Li₂` is monotone on `[-1, 1]`; hence `-π²/12 ≤ Li₂ ≤ π²/6`
  there (`neg_pi_sq_div_twelve_le_Li₂`, `Li₂_le_pi_sq_div_six`).

Each comes with its `IntervalIntegrable` companion. The integrands have constant sign on
`(0, 1)`, so integrability follows from an antiderivative with one-sided limits at `0` and `1`
(`intervalIntegrable_and_integral_eq_of_nonneg`). The antiderivatives are

* `Li₃ x` and `Li₃ x - log x Li₂ x`;
* `F₁ x = log x log (1 - x)² + 2 log (1 - x) Li₂ (1 - x) - 2 Li₃ (1 - x)` (`logOneSubSqPrim`),
  with `F₁ (0⁺) = -2 ζ(3)` and `F₁ (1⁻) = 0`;
* `F₁ (x²) / 2`;
* `F₃ x = log x log (1 + x)² - (2/3) log (1 + x)³ - 2 log (1 + x) Li₂ (1/(1+x))
  - 2 Li₃ (1/(1+x))` (`logOneAddSqPrim`), with `F₃ (0⁺) = -2 ζ(3)` and
  `F₃ (1) = -(2/3) log³ 2 - 2 log 2 Li₂ (1/2) - 2 Li₃ (1/2) = -(7/4) ζ(3)`; this is where
  `Li₂_one_half` and `Li₃_one_half` (Landen) enter.

`J₂` follows from `log (1 - x) log (1 + x) = ½ (log (1 - x²)² - log (1 - x)² - log (1 + x)²)`.
-/

public section

open Real Set Filter Topology MeasureTheory

namespace QED.Polylog

/-! ### Tools -/

/-- A nonnegative function on `(0,1)` with an antiderivative having one-sided limits at `0` and
`1` is interval integrable on `[0,1]`, with integral the difference of the limits. -/
theorem intervalIntegrable_and_integral_eq_of_nonneg {F f : ℝ → ℝ} {A B : ℝ}
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x)
    (h0 : Tendsto F (𝓝[>] 0) (𝓝 A)) (h1 : Tendsto F (𝓝[<] 1) (𝓝 B)) :
    IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = B - A := by
  have hFc : ContinuousOn F (Ioo 0 1) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  set G := extendFrom (Ioo (0 : ℝ) 1) F with hG
  have hGc : ContinuousOn G (Icc 0 1) := continuousOn_Icc_extendFrom_Ioo hFc h0 h1
  have hGd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (f x) x := by
    intro x hx
    refine (hd x hx).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact extendFrom_extends hFc y hy
  have hint : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (intervalIntegral.integrableOn_deriv_of_nonneg hGc hGd hf)
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hd hint h0 h1⟩

/-- `Li₂ ∘ g` tends to `Li₂ a` when `g → a ∈ [-1, 1]` eventually inside `[-1, 1]`. -/
theorem tendsto_Li₂_comp {α : Type*} {l : Filter α} {g : α → ℝ} {a : ℝ}
    (ha : a ∈ Icc (-1 : ℝ) 1) (hg : Tendsto g l (𝓝 a)) (hgs : ∀ᶠ x in l, g x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun x => Li₂ (g x)) l (𝓝 (Li₂ a)) :=
  (continuousOn_Li₂ a ha).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hg, hgs⟩)

/-- `Li₃ ∘ g` tends to `Li₃ a` when `g → a ∈ [-1, 1]` eventually inside `[-1, 1]`. -/
theorem tendsto_Li₃_comp {α : Type*} {l : Filter α} {g : α → ℝ} {a : ℝ}
    (ha : a ∈ Icc (-1 : ℝ) 1) (hg : Tendsto g l (𝓝 a)) (hgs : ∀ᶠ x in l, g x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun x => Li₃ (g x)) l (𝓝 (Li₃ a)) :=
  (continuousOn_Li₃ a ha).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hg, hgs⟩)

/-- `Li₂` is nonnegative on `[0, 1]`. -/
theorem Li₂_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Li₂ x :=
  tsum_nonneg fun n => by positivity

/-- `|Li₂ y| ≤ π²/6` on `[-1, 1]`. -/
theorem abs_Li₂_le_of_mem {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : |Li₂ y| ≤ π ^ 2 / 6 := by
  have h1 : |y| ≤ 1 := abs_le.2 hy
  calc |Li₂ y| ≤ π ^ 2 / 6 * |y| := abs_Li₂_le h1
    _ ≤ π ^ 2 / 6 * 1 := by gcongr
    _ = π ^ 2 / 6 := mul_one _

/-- `x ↦ 1 - x` maps `𝓝[>] 0` to `𝓝[<] 1`. -/
theorem tendsto_one_sub_nhdsGT_zero : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 (1 - 0)) :=
      (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    show 1 - x < 1
    linarith

/-- `x ↦ 1 - x` maps `𝓝[<] 1` to `𝓝[>] 0`. -/
theorem tendsto_one_sub_nhdsLT_one : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 (1 - 1)) :=
      (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
    show 0 < 1 - x
    linarith

/-- `x log x → 0` as `x → 0⁺`. -/
theorem tendsto_mul_log_zero : Tendsto (fun x : ℝ => x * log x) (𝓝[>] 0) (𝓝 0) := by
  have := (continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa using this

/-- `x log² x → 0` as `x → 0⁺`. -/
theorem tendsto_mul_log_sq_zero : Tendsto (fun x : ℝ => x * log x ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 2)).pow 2
  rw [zero_pow two_ne_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [mul_pow, ← rpow_natCast (x ^ (1 / 2 : ℝ)), ← rpow_mul hx.le]
  norm_num
  ring

/-- `log (1 - x) / x → -1` as `x → 0⁺`. -/
theorem tendsto_log_one_sub_div_zero' :
    Tendsto (fun x => log (1 - x) / x) (𝓝[>] 0) (𝓝 (-1)) := by
  have hd : HasDerivAt (fun y : ℝ => log (1 - y)) (-1) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_sub 1).log (by norm_num)
    simpa using this
  refine hd.tendsto_slope_zero_right.congr fun t => ?_
  simp only [zero_add, sub_zero, log_one, smul_eq_mul]
  ring

/-- `log (1 + x) / x → 1` as `x → 0⁺`. -/
theorem tendsto_log_one_add_div_zero :
    Tendsto (fun x => log (1 + x) / x) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt (fun y : ℝ => log (1 + y)) 1 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_add 1).log (by norm_num)
    simpa using this
  refine hd.tendsto_slope_zero_right.congr fun t => ?_
  simp only [zero_add, add_zero, log_one, smul_eq_mul, sub_zero]
  ring

/-- `log x Li₂ x → 0` as `x → 0⁺`. -/
theorem tendsto_log_mul_Li₂_zero : Tendsto (fun x => log x * Li₂ x) (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ ((tendsto_mul_log_zero.abs.const_mul (π ^ 2 / 6)).trans ?_)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
    have hy' : |y| ≤ 1 := by rw [abs_of_pos hy.1]; exact hy.2.le
    rw [Real.norm_eq_abs, abs_mul]
    calc |log y| * |Li₂ y| ≤ |log y| * (π ^ 2 / 6 * |y|) :=
          mul_le_mul_of_nonneg_left (abs_Li₂_le hy') (abs_nonneg _)
      _ = π ^ 2 / 6 * |y * log y| := by rw [abs_mul]; ring
  · simp

/-- `log x · log (1 - x) → 0` as `x → 0⁺`. -/
theorem tendsto_log_mul_log_one_sub_zero :
    Tendsto (fun x => log x * log (1 - x)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_mul_log_zero.mul tendsto_log_one_sub_div_zero'
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  field_simp

/-- `log x · log (1 - x) → 0` as `x → 1⁻`. -/
theorem tendsto_log_mul_log_one_sub_one :
    Tendsto (fun x => log x * log (1 - x)) (𝓝[<] 1) (𝓝 0) := by
  have h := tendsto_log_mul_log_one_sub_zero.comp tendsto_one_sub_nhdsLT_one
  refine h.congr' ?_
  filter_upwards with x
  simp only [Function.comp_apply, sub_sub_cancel]
  ring

/-! ### `∫₀¹ Li₂ x / x = ζ(3)` and `∫₀¹ log x log (1 - x) / x = ζ(3)` -/

theorem tendsto_Li₂_one_left : Tendsto Li₂ (𝓝[<] 1) (𝓝 (π ^ 2 / 6)) := by
  rw [← Li₂_one]
  have h := tendsto_Li₂_comp (l := 𝓝[<] (1 : ℝ)) (g := id) (a := 1) (by norm_num)
    (tendsto_id.mono_left nhdsWithin_le_nhds) ?_
  · exact h
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with x hx
    exact Ioo_subset_Icc_self hx

theorem tendsto_Li₃_one_left : Tendsto Li₃ (𝓝[<] 1) (𝓝 zeta3) := by
  rw [← Li₃_one]
  have h := tendsto_Li₃_comp (l := 𝓝[<] (1 : ℝ)) (g := id) (a := 1) (by norm_num)
    (tendsto_id.mono_left nhdsWithin_le_nhds) ?_
  · exact h
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with x hx
    exact Ioo_subset_Icc_self hx

theorem tendsto_Li₃_zero_right : Tendsto Li₃ (𝓝[>] 0) (𝓝 0) := by
  have h := ((continuousOn_Li₃.continuousAt (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1))).tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rwa [Li₃_zero] at h

theorem tendsto_Li₂_zero_right : Tendsto Li₂ (𝓝[>] 0) (𝓝 0) := by
  have h := ((continuousOn_Li₂.continuousAt (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1))).tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rwa [Li₂_zero] at h

theorem hasDerivAt_Li₂' {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt Li₂ (-log (1 - x) / x) x :=
  hasDerivAt_Li₂ (by rw [abs_of_pos hx.1]; exact hx.2) hx.1.ne'

theorem hasDerivAt_Li₃' {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt Li₃ (Li₂ x / x) x :=
  hasDerivAt_Li₃ (by rw [abs_of_pos hx.1]; exact hx.2) hx.1.ne'

theorem intervalIntegrable_and_integral_Li₂_div :
    IntervalIntegrable (fun x => Li₂ x / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Li₂ x / x = zeta3 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg (F := Li₃) (f := fun x => Li₂ x / x)
    (fun x hx => hasDerivAt_Li₃' hx) (fun x hx => div_nonneg (Li₂_nonneg hx.1.le) hx.1.le)
    tendsto_Li₃_zero_right tendsto_Li₃_one_left
  rwa [sub_zero] at h

/-- `∫₀¹ Li₂ x / x = ζ(3)`. -/
theorem integral_Li₂_div : ∫ x in (0 : ℝ)..1, Li₂ x / x = zeta3 :=
  intervalIntegrable_and_integral_Li₂_div.2

theorem intervalIntegrable_and_integral_log_mul_log_one_sub_div :
    IntervalIntegrable (fun x => log x * log (1 - x) / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x * log (1 - x) / x = zeta3 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg (F := fun x => Li₃ x - log x * Li₂ x)
    (f := fun x => log x * log (1 - x) / x) (A := 0 - 0) (B := zeta3 - 0 * (π ^ 2 / 6)) ?_ ?_
    (tendsto_Li₃_zero_right.sub tendsto_log_mul_Li₂_zero) ?_
  · simpa using h
  · intro x hx
    have := (hasDerivAt_Li₃' hx).sub ((hasDerivAt_log hx.1.ne').mul (hasDerivAt_Li₂' hx))
    refine this.congr_deriv ?_
    have := hx.1.ne'
    field_simp
    ring
  · intro x hx
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (log_nonpos hx.1.le hx.2.le)
      (log_nonpos (by linarith [hx.2]) (by linarith [hx.1]))) hx.1.le
  · have hl : Tendsto log (𝓝[<] 1) (𝓝 0) := by
      have := ((continuousAt_log one_ne_zero).tendsto).mono_left (nhdsWithin_le_nhds (s := Iio 1))
      simpa using this
    exact tendsto_Li₃_one_left.sub (hl.mul tendsto_Li₂_one_left)

/-- `∫₀¹ log x log (1 - x) / x = ζ(3)`. -/
theorem integral_log_mul_log_one_sub_div :
    ∫ x in (0 : ℝ)..1, log x * log (1 - x) / x = zeta3 :=
  intervalIntegrable_and_integral_log_mul_log_one_sub_div.2

/-! ### `J₁ = ∫₀¹ log (1 - x)² / x = 2 ζ(3)` -/

/-- The antiderivative `F₁ x = log x log (1 - x)² + 2 log (1 - x) Li₂ (1 - x) - 2 Li₃ (1 - x)` of
`log (1 - x)² / x` on `(0, 1)`. -/
noncomputable def logOneSubSqPrim (x : ℝ) : ℝ :=
  log x * log (1 - x) ^ 2 + 2 * log (1 - x) * Li₂ (1 - x) - 2 * Li₃ (1 - x)

theorem hasDerivAt_logOneSubSqPrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt logOneSubSqPrim (log (1 - x) ^ 2 / x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hs : (1 : ℝ) - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h1x : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  have hl1 : HasDerivAt (fun y : ℝ => log (1 - y)) (-1 / (1 - x)) x := h1x.log hs.1.ne'
  have hL2 := (hasDerivAt_Li₂' hs).comp x h1x
  have hL3 := (hasDerivAt_Li₃' hs).comp x h1x
  have h := (((hasDerivAt_log hx0.ne').mul (hl1.pow 2)).add ((hl1.const_mul 2).mul hL2)).sub
    (hL3.const_mul 2)
  refine h.congr_deriv ?_
  rw [sub_sub_cancel]
  have h1 : (1 : ℝ) - x ≠ 0 := hs.1.ne'
  have h0 : x ≠ 0 := hx0.ne'
  simp only [Function.comp_apply, Pi.pow_apply]
  field_simp
  ring

/-- `log (1 - x) → 0` as `x → 0⁺`. -/
theorem tendsto_log_one_sub_zero : Tendsto (fun x : ℝ => log (1 - x)) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun x : ℝ => log (1 - x)) (𝓝 0) (𝓝 (log (1 - 0))) :=
    ((continuousAt_log (by norm_num)).tendsto).comp (tendsto_const_nhds.sub tendsto_id)
  simpa using this.mono_left nhdsWithin_le_nhds

/-- Eventually near `0⁺`, `1 - x ∈ [-1, 1]`. -/
theorem eventually_one_sub_mem_Icc :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), 1 - x ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem tendsto_logOneSubSqPrim_zero :
    Tendsto logOneSubSqPrim (𝓝[>] 0) (𝓝 (-2 * zeta3)) := by
  have h1 : Tendsto (fun x => 1 - x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_one_sub_nhdsGT_zero.mono_right nhdsWithin_le_nhds
  have hL2 := tendsto_Li₂_comp (a := 1) (by norm_num) h1 eventually_one_sub_mem_Icc
  have hL3 := tendsto_Li₃_comp (a := 1) (by norm_num) h1 eventually_one_sub_mem_Icc
  have h := ((tendsto_log_mul_log_one_sub_zero.mul tendsto_log_one_sub_zero).add
    ((tendsto_log_one_sub_zero.const_mul 2).mul hL2)).sub (hL3.const_mul 2)
  rw [Li₃_one] at h
  convert h using 2
  · simp only [logOneSubSqPrim]
    ring
  · ring

theorem tendsto_logOneSubSqPrim_one : Tendsto logOneSubSqPrim (𝓝[<] 1) (𝓝 0) := by
  have hA := (tendsto_log_one_sub_div_zero'.mul tendsto_mul_log_sq_zero).comp
    tendsto_one_sub_nhdsLT_one
  have hB := tendsto_log_mul_Li₂_zero.comp tendsto_one_sub_nhdsLT_one
  have hC := tendsto_Li₃_zero_right.comp tendsto_one_sub_nhdsLT_one
  have h := (hA.add (hB.const_mul 2)).sub (hC.const_mul 2)
  simp only [mul_zero, sub_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith
  simp only [Function.comp_apply, sub_sub_cancel, logOneSubSqPrim]
  field_simp

theorem intervalIntegrable_and_integral_log_one_sub_sq_div :
    IntervalIntegrable (fun x => log (1 - x) ^ 2 / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log (1 - x) ^ 2 / x = 2 * zeta3 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg (fun x hx => hasDerivAt_logOneSubSqPrim hx)
    (fun x hx => div_nonneg (sq_nonneg _) hx.1.le) tendsto_logOneSubSqPrim_zero
    tendsto_logOneSubSqPrim_one
  rwa [show (0 : ℝ) - -2 * zeta3 = 2 * zeta3 by ring] at h

/-- `J₁ = ∫₀¹ log (1 - x)² / x = 2 ζ(3)`. -/
theorem integral_log_one_sub_sq_div : ∫ x in (0 : ℝ)..1, log (1 - x) ^ 2 / x = 2 * zeta3 :=
  intervalIntegrable_and_integral_log_one_sub_sq_div.2

/-! ### `∫₀¹ log (1 - x²)² / x = ζ(3)` -/

theorem hasDerivAt_logOneSubSqPrim_sq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => logOneSubSqPrim (y ^ 2) / 2) (log (1 - x ^ 2) ^ 2 / x) x := by
  have hx2 : x ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨by have := hx.1; positivity, by nlinarith [hx.1, hx.2]⟩
  have h := ((hasDerivAt_logOneSubSqPrim hx2).comp (h := fun y : ℝ => y ^ 2) x
    (hasDerivAt_pow 2 x)).div_const 2
  refine h.congr_deriv ?_
  have := hx.1.ne'
  field_simp
  ring

theorem tendsto_sq_nhdsGT_zero : Tendsto (fun x : ℝ => x ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (continuous_pow 2).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact pow_pos hx 2

theorem tendsto_sq_nhdsLT_one : Tendsto (fun x : ℝ => x ^ 2) (𝓝[<] 1) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun x : ℝ => x ^ 2) (𝓝 1) (𝓝 (1 ^ 2)) := (continuous_pow 2).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    show x ^ 2 < 1
    nlinarith [hx.1, hx.2]

theorem intervalIntegrable_and_integral_log_one_sub_sq_sq_div :
    IntervalIntegrable (fun x => log (1 - x ^ 2) ^ 2 / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log (1 - x ^ 2) ^ 2 / x = zeta3 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg
    (fun x hx => hasDerivAt_logOneSubSqPrim_sq hx)
    (fun x hx => div_nonneg (sq_nonneg _) hx.1.le)
    ((tendsto_logOneSubSqPrim_zero.comp tendsto_sq_nhdsGT_zero).div_const 2)
    ((tendsto_logOneSubSqPrim_one.comp tendsto_sq_nhdsLT_one).div_const 2)
  rwa [show (0 : ℝ) / 2 - -2 * zeta3 / 2 = zeta3 by ring] at h

/-- `∫₀¹ log (1 - x²)² / x = ζ(3)`. -/
theorem integral_log_one_sub_sq_sq_div :
    ∫ x in (0 : ℝ)..1, log (1 - x ^ 2) ^ 2 / x = zeta3 :=
  intervalIntegrable_and_integral_log_one_sub_sq_sq_div.2

/-! ### `J₃ = ∫₀¹ log (1 + x)² / x = ζ(3) / 4` -/

/-- The antiderivative `F₃ x = log x log (1 + x)² - (2/3) log (1 + x)³
- 2 log (1 + x) Li₂ (1/(1+x)) - 2 Li₃ (1/(1+x))` of `log (1 + x)² / x` on `(0, 1)`. -/
noncomputable def logOneAddSqPrim (x : ℝ) : ℝ :=
  log x * log (1 + x) ^ 2 - 2 / 3 * log (1 + x) ^ 3 - 2 * log (1 + x) * Li₂ (1 + x)⁻¹ -
    2 * Li₃ (1 + x)⁻¹

theorem hasDerivAt_logOneAddSqPrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt logOneAddSqPrim (log (1 + x) ^ 2 / x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hp : (0 : ℝ) < 1 + x := by linarith
  have hu : (1 + x)⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.2 hp, inv_lt_one_of_one_lt₀ (by linarith)⟩
  have h1x : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_id' x).const_add 1
  have hl1 : HasDerivAt (fun y : ℝ => log (1 + y)) (1 / (1 + x)) x := h1x.log hp.ne'
  have hinv : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-1 / (1 + x) ^ 2) x :=
    ((hasDerivAt_inv hp.ne').comp x h1x).congr_deriv (by field_simp)
  have hL2 := (hasDerivAt_Li₂' hu).comp x hinv
  have hL3 := (hasDerivAt_Li₃' hu).comp x hinv
  have h := ((((hasDerivAt_log hx0.ne').mul (hl1.pow 2)).sub ((hl1.pow 3).const_mul (2 / 3))).sub
    ((hl1.const_mul 2).mul hL2)).sub (hL3.const_mul 2)
  refine h.congr_deriv ?_
  have hlog : log (1 - (1 + x)⁻¹) = log x - log (1 + x) := by
    rw [show (1 : ℝ) - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring]
    exact log_div hx0.ne' hp.ne'
  simp only [Function.comp_apply, Pi.pow_apply]
  rw [hlog]
  have h0 : x ≠ 0 := hx0.ne'
  have h1 : (1 : ℝ) + x ≠ 0 := hp.ne'
  field_simp
  ring

theorem tendsto_logOneAddSqPrim_zero :
    Tendsto logOneAddSqPrim (𝓝[>] 0) (𝓝 (-2 * zeta3)) := by
  unfold logOneAddSqPrim
  have hl : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => log (1 + x)) (𝓝 0) (𝓝 (log (1 + 0))) :=
      ((continuousAt_log (by norm_num)).tendsto).comp (tendsto_const_nhds.add tendsto_id)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ => (1 + x)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun x : ℝ => (1 + x)⁻¹) (𝓝 0) (𝓝 (1 + 0)⁻¹) :=
      (tendsto_const_nhds.add tendsto_id).inv₀ (by norm_num)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hus : ∀ᶠ x in 𝓝[>] (0 : ℝ), (1 + x)⁻¹ ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact ⟨by have : 0 < (1 + x)⁻¹ := inv_pos.2 (by linarith); linarith,
      inv_le_one_of_one_le₀ (by linarith)⟩
  have hL2 := tendsto_Li₂_comp (a := 1) (by norm_num) hu hus
  have hL3 := tendsto_Li₃_comp (a := 1) (by norm_num) hu hus
  have hA : Tendsto (fun x => log x * log (1 + x) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_mul_log_zero.mul tendsto_log_one_add_div_zero).mul hl
    rw [zero_mul, zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    field_simp
  have h := ((hA.sub ((hl.pow 3).const_mul (2 / 3))).sub ((hl.const_mul 2).mul hL2)).sub
    (hL3.const_mul 2)
  rw [Li₃_one] at h
  convert h using 2
  ring

theorem tendsto_logOneAddSqPrim_one :
    Tendsto logOneAddSqPrim (𝓝[<] 1) (𝓝 (-(7 / 4) * zeta3)) := by
  unfold logOneAddSqPrim
  have hc : ContinuousAt (fun x : ℝ => (1 + x)⁻¹) 1 :=
    (continuousAt_const.add continuousAt_id).inv₀ (by norm_num)
  have hu : Tendsto (fun x : ℝ => (1 + x)⁻¹) (𝓝[<] 1) (𝓝 (1 / 2)) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    norm_num at this ⊢
    exact this
  have hus : ∀ᶠ x in 𝓝[<] (1 : ℝ), (1 + x)⁻¹ ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by have : 0 < (1 + x)⁻¹ := inv_pos.2 (by linarith [hx.1]); linarith,
      inv_le_one_of_one_le₀ (by linarith [hx.1])⟩
  have hL2 := tendsto_Li₂_comp (a := 1 / 2) (by norm_num) hu hus
  have hL3 := tendsto_Li₃_comp (a := 1 / 2) (by norm_num) hu hus
  have hlog : Tendsto log (𝓝[<] 1) (𝓝 0) := by
    have := ((continuousAt_log one_ne_zero).tendsto).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hl : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[<] 1) (𝓝 (log 2)) := by
    have : Tendsto (fun x : ℝ => log (1 + x)) (𝓝 1) (𝓝 (log (1 + 1))) :=
      ((continuousAt_log (by norm_num)).tendsto).comp (tendsto_const_nhds.add tendsto_id)
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := (((hlog.mul (hl.pow 2)).sub ((hl.pow 3).const_mul (2 / 3))).sub
    ((hl.const_mul 2).mul hL2)).sub (hL3.const_mul 2)
  rw [Li₂_one_half, Li₃_one_half] at h
  convert h using 2
  ring

theorem intervalIntegrable_and_integral_log_one_add_sq_div :
    IntervalIntegrable (fun x => log (1 + x) ^ 2 / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log (1 + x) ^ 2 / x = zeta3 / 4 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg (fun x hx => hasDerivAt_logOneAddSqPrim hx)
    (fun x hx => div_nonneg (sq_nonneg _) hx.1.le) tendsto_logOneAddSqPrim_zero
    tendsto_logOneAddSqPrim_one
  rwa [show -(7 / 4) * zeta3 - -2 * zeta3 = zeta3 / 4 by ring] at h

/-- `J₃ = ∫₀¹ log (1 + x)² / x = ζ(3) / 4`. -/
theorem integral_log_one_add_sq_div : ∫ x in (0 : ℝ)..1, log (1 + x) ^ 2 / x = zeta3 / 4 :=
  intervalIntegrable_and_integral_log_one_add_sq_div.2

/-! ### `J₂ = ∫₀¹ log (1 - x) log (1 + x) / x = -(5/8) ζ(3)` -/

theorem intervalIntegrable_and_integral_log_one_sub_mul_log_one_add_div :
    IntervalIntegrable (fun x => log (1 - x) * log (1 + x) / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log (1 - x) * log (1 + x) / x = -(5 / 8) * zeta3 := by
  obtain ⟨i1, v1⟩ := intervalIntegrable_and_integral_log_one_sub_sq_div
  obtain ⟨i2, v2⟩ := intervalIntegrable_and_integral_log_one_sub_sq_sq_div
  obtain ⟨i3, v3⟩ := intervalIntegrable_and_integral_log_one_add_sq_div
  have heq : EqOn (fun x => 1 / 2 * (log (1 - x ^ 2) ^ 2 / x - log (1 - x) ^ 2 / x -
      log (1 + x) ^ 2 / x)) (fun x => log (1 - x) * log (1 + x) / x) (uIoo 0 1) := by
    intro x hx
    rw [uIoo_of_le zero_le_one] at hx
    have h1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have h2 : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    simp only
    rw [show (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) by ring, log_mul h1 h2]
    ring
  have hi : IntervalIntegrable (fun x => 1 / 2 * (log (1 - x ^ 2) ^ 2 / x - log (1 - x) ^ 2 / x -
      log (1 + x) ^ 2 / x)) volume 0 1 := ((i2.sub i1).sub i3).const_mul _
  refine ⟨hi.congr_uIoo heq, ?_⟩
  rw [← intervalIntegral.integral_congr_uIoo heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (i2.sub i1) i3, intervalIntegral.integral_sub i2 i1, v1, v2, v3]
  ring

/-- `J₂ = ∫₀¹ log (1 - x) log (1 + x) / x = -(5/8) ζ(3)`. -/
theorem integral_log_one_sub_mul_log_one_add_div :
    ∫ x in (0 : ℝ)..1, log (1 - x) * log (1 + x) / x = -(5 / 8) * zeta3 :=
  intervalIntegrable_and_integral_log_one_sub_mul_log_one_add_div.2

/-! ### Monotonicity and bounds of `Li₂` on `[-1, 1]` -/

/-- `Li₂` is monotone on `[-1, 1]`: its derivative `-log (1 - x) / x` (and `1` at `0`) is
nonnegative. -/
theorem monotoneOn_Li₂ : MonotoneOn Li₂ (Icc (-1) 1) := by
  have hdiff : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt Li₂ (deriv Li₂ x) x := by
    intro x hx
    have habs : |x| < 1 := abs_lt.2 hx
    rcases eq_or_ne x 0 with rfl | h0
    · exact hasDerivAt_Li₂_zero.differentiableAt.hasDerivAt
    · exact (hasDerivAt_Li₂ habs h0).differentiableAt.hasDerivAt
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) continuousOn_Li₂ ?_ ?_
  · rw [interior_Icc]
    exact fun x hx => (hdiff x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    have habs : |x| < 1 := abs_lt.2 hx
    have hm := mul_deriv_Li₂ habs
    rcases lt_trichotomy x 0 with h | rfl | h
    · have : 0 ≤ log (1 - x) := log_nonneg (by linarith)
      nlinarith
    · rw [hasDerivAt_Li₂_zero.deriv]
      norm_num
    · have : log (1 - x) ≤ 0 := log_nonpos (by linarith [hx.2]) (by linarith)
      nlinarith

/-- `-π²/12 ≤ Li₂ y` on `[-1, 1]`. -/
theorem neg_pi_sq_div_twelve_le_Li₂ {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : -(π ^ 2 / 12) ≤ Li₂ y := by
  have h := monotoneOn_Li₂ (show (-1 : ℝ) ∈ Icc (-1) 1 by norm_num) hy hy.1
  rwa [Li₂_neg_one, neg_div] at h

/-- `Li₂ y ≤ π²/6` on `[-1, 1]`. -/
theorem Li₂_le_pi_sq_div_six {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) : Li₂ y ≤ π ^ 2 / 6 :=
  (abs_le.1 (abs_Li₂_le_of_mem hy)).2

/-- `Li₂ y ≤ 0` on `[-1, 0]`. -/
theorem Li₂_nonpos {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 0) : Li₂ y ≤ 0 := by
  have h := monotoneOn_Li₂ ⟨hy.1, by linarith [hy.2]⟩ (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num) hy.2
  rwa [Li₂_zero] at h

/-! ### Boundary behaviour at `1⁻` -/

/-- `log x log (1 - x)² → 0` as `x → 1⁻`. -/
theorem tendsto_log_mul_log_one_sub_sq_one :
    Tendsto (fun x => log x * log (1 - x) ^ 2) (𝓝[<] 1) (𝓝 0) := by
  have h := (tendsto_log_one_sub_div_zero'.mul tendsto_mul_log_sq_zero).comp
    tendsto_one_sub_nhdsLT_one
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith
  simp only [Function.comp_apply, sub_sub_cancel]
  field_simp

theorem tendsto_log_one_sub_mul_Li₂_one_sub_one :
    Tendsto (fun x => log (1 - x) * Li₂ (1 - x)) (𝓝[<] 1) (𝓝 0) :=
  tendsto_log_mul_Li₂_zero.comp tendsto_one_sub_nhdsLT_one

/-- `log (1 - x) (Li₂ x - π²/6) → 0` as `x → 1⁻` (Euler reflection). -/
theorem tendsto_log_one_sub_mul_Li₂_sub_one :
    Tendsto (fun x => log (1 - x) * (Li₂ x - π ^ 2 / 6)) (𝓝[<] 1) (𝓝 0) := by
  have h := (tendsto_log_one_sub_mul_Li₂_one_sub_one.add tendsto_log_mul_log_one_sub_sq_one).neg
  rw [add_zero, neg_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
  have hr := Li₂_add_Li₂_one_sub hx.1.le hx.2.le
  have : Li₂ x - π ^ 2 / 6 = -Li₂ (1 - x) - log x * log (1 - x) := by linarith
  rw [this]
  ring

theorem tendsto_log_one_add_one : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[<] 1) (𝓝 (log 2)) := by
  have : Tendsto (fun x : ℝ => log (1 + x)) (𝓝 1) (𝓝 (log (1 + 1))) :=
    ((continuousAt_log (by norm_num)).tendsto).comp (tendsto_const_nhds.add tendsto_id)
  norm_num at this
  exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_log_one_add_zero : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun x : ℝ => log (1 + x)) (𝓝 0) (𝓝 (log (1 + 0))) :=
    ((continuousAt_log (by norm_num)).tendsto).comp (tendsto_const_nhds.add tendsto_id)
  simpa using this.mono_left nhdsWithin_le_nhds

/-- `log (1 - x) (Li₂ (-x) + π²/12) → 0` as `x → 1⁻`, via `Li₂ x + Li₂ (-x) = Li₂ (x²) / 2`. -/
theorem tendsto_log_one_sub_mul_Li₂_neg_add_one :
    Tendsto (fun x => log (1 - x) * (Li₂ (-x) + π ^ 2 / 12)) (𝓝[<] 1) (𝓝 0) := by
  have hA := tendsto_log_one_sub_mul_Li₂_sub_one
  have hB := tendsto_log_one_sub_mul_Li₂_sub_one.comp tendsto_sq_nhdsLT_one
  have hC := tendsto_log_one_add_one.mul
    ((tendsto_Li₂_one_left.comp tendsto_sq_nhdsLT_one).sub_const (π ^ 2 / 6))
  rw [sub_self, mul_zero] at hC
  have h := ((hB.sub hC).div_const 2).sub hA
  simp only [sub_self, zero_div] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  have h2 : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
  have hn := Li₂_add_Li₂_neg (x := x) (by rw [abs_of_pos hx.1]; exact hx.2.le)
  have hl : log (1 - x ^ 2) = log (1 - x) + log (1 + x) := by
    rw [show (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) by ring, log_mul h1 h2]
  simp only [Function.comp_apply]
  rw [hl, show Li₂ (-x) = Li₂ (x ^ 2) / 2 - Li₂ x by linarith]
  ring

/-! ### The antiderivative `Ψ` of `log (1 - x) log (1 + x) / x` -/

/-- `Ψ x = (F₁ (x²)/2 - F₁ x - F₃ x)/2`, an antiderivative of `log (1 - x) log (1 + x) / x` on
`(0, 1)`. -/
noncomputable def logOneSubMulLogOneAddPrim (x : ℝ) : ℝ :=
  (logOneSubSqPrim (x ^ 2) / 2 - logOneSubSqPrim x - logOneAddSqPrim x) / 2

theorem hasDerivAt_logOneSubMulLogOneAddPrim {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt logOneSubMulLogOneAddPrim (log (1 - x) * log (1 + x) / x) x := by
  have h := (((hasDerivAt_logOneSubSqPrim_sq hx).sub (hasDerivAt_logOneSubSqPrim hx)).sub
    (hasDerivAt_logOneAddSqPrim hx)).div_const 2
  refine h.congr_deriv ?_
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  have h2 : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
  rw [show (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) by ring, log_mul h1 h2]
  have := hx.1.ne'
  field_simp
  ring

theorem tendsto_logOneSubMulLogOneAddPrim_zero :
    Tendsto logOneSubMulLogOneAddPrim (𝓝[>] 0) (𝓝 (3 / 2 * zeta3)) := by
  have h := ((((tendsto_logOneSubSqPrim_zero.comp tendsto_sq_nhdsGT_zero).div_const 2).sub
    tendsto_logOneSubSqPrim_zero).sub tendsto_logOneAddSqPrim_zero).div_const 2
  rw [show (-2 * zeta3 / 2 - -2 * zeta3 - -2 * zeta3) / 2 = 3 / 2 * zeta3 by ring] at h
  exact h

theorem tendsto_logOneSubMulLogOneAddPrim_one :
    Tendsto logOneSubMulLogOneAddPrim (𝓝[<] 1) (𝓝 (7 / 8 * zeta3)) := by
  have h := ((((tendsto_logOneSubSqPrim_one.comp tendsto_sq_nhdsLT_one).div_const 2).sub
    tendsto_logOneSubSqPrim_one).sub tendsto_logOneAddSqPrim_one).div_const 2
  rw [show (0 / 2 - 0 - -(7 / 4) * zeta3) / 2 = 7 / 8 * zeta3 by ring] at h
  exact h

/-! ### The four integrals `A₁, …, A₄` -/

/-- The nonpositive version of `intervalIntegrable_and_integral_eq_of_nonneg`. -/
theorem intervalIntegrable_and_integral_eq_of_nonpos {F f : ℝ → ℝ} {A B : ℝ}
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ≤ 0)
    (h0 : Tendsto F (𝓝[>] 0) (𝓝 A)) (h1 : Tendsto F (𝓝[<] 1) (𝓝 B)) :
    IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = B - A := by
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_eq_of_nonneg (F := fun x => -F x)
    (f := fun x => -f x) (fun x hx => (hd x hx).neg) (fun x hx => neg_nonneg.2 (hf x hx)) h0.neg
    h1.neg
  have hi' : IntervalIntegrable (fun x => - -f x) volume 0 1 := hi.neg
  refine ⟨by simpa only [neg_neg] using hi', ?_⟩
  rw [intervalIntegral.integral_neg] at hv
  linarith

theorem hasDerivAt_Li₂_neg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => Li₂ (-y)) (-log (1 + x) / x) x := by
  have hn : |-x| < 1 := by rw [abs_neg, abs_of_pos hx.1]; exact hx.2
  have h := (hasDerivAt_Li₂ hn (neg_ne_zero.2 hx.1.ne')).comp x (hasDerivAt_neg x)
  refine h.congr_deriv ?_
  have := hx.1.ne'
  rw [sub_neg_eq_add]
  field_simp

theorem tendsto_Li₂_neg_zero : Tendsto (fun x => Li₂ (-x)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_Li₂_comp (l := 𝓝[>] (0 : ℝ)) (g := fun x => -x) (a := 0) (by norm_num) ?_ ?_
  · rwa [Li₂_zero] at h
  · have : Tendsto (fun x : ℝ => -x) (𝓝 0) (𝓝 (-0)) := tendsto_neg 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem tendsto_Li₂_neg_one : Tendsto (fun x => Li₂ (-x)) (𝓝[<] 1) (𝓝 (-(π ^ 2 / 12))) := by
  have h := tendsto_Li₂_comp (l := 𝓝[<] (1 : ℝ)) (g := fun x => -x) (a := -1) (by norm_num) ?_ ?_
  · rwa [Li₂_neg_one, neg_div] at h
  · have : Tendsto (fun x : ℝ => -x) (𝓝 1) (𝓝 (-1)) := tendsto_neg 1
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- `H₁ x = -log (1 - x) (Li₂ x - π²/6) - F₁ x`, an antiderivative of `(Li₂ x - π²/6)/(1 - x)`. -/
noncomputable def primA₁ (x : ℝ) : ℝ := -log (1 - x) * (Li₂ x - π ^ 2 / 6) - logOneSubSqPrim x

/-- `H₂ x = -log (1 - x) (Li₂ (-x) + π²/12) - Ψ x`, an antiderivative of
`(Li₂ (-x) + π²/12)/(1 - x)`. -/
noncomputable def primA₂ (x : ℝ) : ℝ :=
  -log (1 - x) * (Li₂ (-x) + π ^ 2 / 12) - logOneSubMulLogOneAddPrim x

/-- `H₃ x = log (1 + x) Li₂ x + Ψ x`, an antiderivative of `Li₂ x / (1 + x)`. -/
noncomputable def primA₃ (x : ℝ) : ℝ := log (1 + x) * Li₂ x + logOneSubMulLogOneAddPrim x

/-- `H₄ x = log (1 + x) Li₂ (-x) + F₃ x`, an antiderivative of `Li₂ (-x) / (1 + x)`. -/
noncomputable def primA₄ (x : ℝ) : ℝ := log (1 + x) * Li₂ (-x) + logOneAddSqPrim x

theorem hasDerivAt_log_one_sub {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y : ℝ => log (1 - y)) (-1 / (1 - x)) x := by
  have h1x : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  exact h1x.log (by linarith)

theorem hasDerivAt_log_one_add {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y : ℝ => log (1 + y)) (1 / (1 + x)) x := by
  have h1x : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_id' x).const_add 1
  exact h1x.log (by linarith)

theorem hasDerivAt_primA₁ {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt primA₁ ((Li₂ x - π ^ 2 / 6) / (1 - x)) x := by
  have h := (((hasDerivAt_log_one_sub hx.2).neg).mul ((hasDerivAt_Li₂' hx).sub_const
    (π ^ 2 / 6))).sub (hasDerivAt_logOneSubSqPrim hx)
  refine h.congr_deriv ?_
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  have := hx.1.ne'
  simp only [Pi.neg_apply]
  field_simp
  ring

theorem hasDerivAt_primA₂ {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt primA₂ ((Li₂ (-x) + π ^ 2 / 12) / (1 - x)) x := by
  have h := (((hasDerivAt_log_one_sub hx.2).neg).mul ((hasDerivAt_Li₂_neg hx).add_const
    (π ^ 2 / 12))).sub (hasDerivAt_logOneSubMulLogOneAddPrim hx)
  refine h.congr_deriv ?_
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  have := hx.1.ne'
  simp only [Pi.neg_apply]
  field_simp
  ring

theorem hasDerivAt_primA₃ {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt primA₃ (Li₂ x / (1 + x)) x := by
  have h := ((hasDerivAt_log_one_add (by linarith [hx.1])).mul (hasDerivAt_Li₂' hx)).add
    (hasDerivAt_logOneSubMulLogOneAddPrim hx)
  refine h.congr_deriv ?_
  have h1 : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
  have := hx.1.ne'
  field_simp
  ring

theorem hasDerivAt_primA₄ {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt primA₄ (Li₂ (-x) / (1 + x)) x := by
  have h := ((hasDerivAt_log_one_add (by linarith [hx.1])).mul (hasDerivAt_Li₂_neg hx)).add
    (hasDerivAt_logOneAddSqPrim hx)
  refine h.congr_deriv ?_
  have h1 : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
  have := hx.1.ne'
  field_simp
  ring

theorem tendsto_primA₁_zero : Tendsto primA₁ (𝓝[>] 0) (𝓝 (2 * zeta3)) := by
  unfold primA₁
  have h := (tendsto_log_one_sub_zero.neg.mul (tendsto_Li₂_zero_right.sub_const (π ^ 2 / 6))).sub
    tendsto_logOneSubSqPrim_zero
  convert h using 2
  ring

theorem tendsto_primA₁_one : Tendsto primA₁ (𝓝[<] 1) (𝓝 0) := by
  have h := tendsto_log_one_sub_mul_Li₂_sub_one.neg.sub tendsto_logOneSubSqPrim_one
  rw [neg_zero, sub_zero] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp only [primA₁]
  ring

theorem tendsto_primA₂_zero : Tendsto primA₂ (𝓝[>] 0) (𝓝 (-(3 / 2) * zeta3)) := by
  unfold primA₂
  have h := (tendsto_log_one_sub_zero.neg.mul (tendsto_Li₂_neg_zero.add_const (π ^ 2 / 12))).sub
    tendsto_logOneSubMulLogOneAddPrim_zero
  convert h using 2
  ring

theorem tendsto_primA₂_one : Tendsto primA₂ (𝓝[<] 1) (𝓝 (-(7 / 8) * zeta3)) := by
  unfold primA₂
  have h := tendsto_log_one_sub_mul_Li₂_neg_add_one.neg.sub tendsto_logOneSubMulLogOneAddPrim_one
  rw [neg_zero, zero_sub, ← neg_mul] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  ring

theorem tendsto_primA₃_zero : Tendsto primA₃ (𝓝[>] 0) (𝓝 (3 / 2 * zeta3)) := by
  unfold primA₃
  have h := (tendsto_log_one_add_zero.mul tendsto_Li₂_zero_right).add
    tendsto_logOneSubMulLogOneAddPrim_zero
  convert h using 2
  ring

theorem tendsto_primA₃_one :
    Tendsto primA₃ (𝓝[<] 1) (𝓝 (π ^ 2 / 6 * log 2 + 7 / 8 * zeta3)) := by
  unfold primA₃
  have h := (tendsto_log_one_add_one.mul tendsto_Li₂_one_left).add
    tendsto_logOneSubMulLogOneAddPrim_one
  convert h using 2
  ring

theorem tendsto_primA₄_zero : Tendsto primA₄ (𝓝[>] 0) (𝓝 (-2 * zeta3)) := by
  unfold primA₄
  have h := (tendsto_log_one_add_zero.mul tendsto_Li₂_neg_zero).add tendsto_logOneAddSqPrim_zero
  convert h using 2
  ring

theorem tendsto_primA₄_one :
    Tendsto primA₄ (𝓝[<] 1) (𝓝 (-(π ^ 2 / 12) * log 2 - 7 / 4 * zeta3)) := by
  unfold primA₄
  have h := (tendsto_log_one_add_one.mul tendsto_Li₂_neg_one).add tendsto_logOneAddSqPrim_one
  convert h using 2
  ring

/-- `A₁ = ∫₀¹ (Li₂ x - π²/6)/(1 - x) = -2 ζ(3)`. -/
theorem intervalIntegrable_and_integral_A₁ :
    IntervalIntegrable (fun x => (Li₂ x - π ^ 2 / 6) / (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (Li₂ x - π ^ 2 / 6) / (1 - x) = -2 * zeta3 := by
  have h := intervalIntegrable_and_integral_eq_of_nonpos (fun x hx => hasDerivAt_primA₁ hx)
    (fun x hx => div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.2 (Li₂_le_pi_sq_div_six ⟨by linarith [hx.1], hx.2.le⟩)) (by linarith [hx.2]))
    tendsto_primA₁_zero tendsto_primA₁_one
  rwa [show (0 : ℝ) - 2 * zeta3 = -2 * zeta3 by ring] at h

/-- `A₂ = ∫₀¹ (Li₂ (-x) + π²/12)/(1 - x) = (5/8) ζ(3)`. -/
theorem intervalIntegrable_and_integral_A₂ :
    IntervalIntegrable (fun x => (Li₂ (-x) + π ^ 2 / 12) / (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (Li₂ (-x) + π ^ 2 / 12) / (1 - x) = 5 / 8 * zeta3 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg (fun x hx => hasDerivAt_primA₂ hx)
    (fun x hx => by
      have hb := neg_pi_sq_div_twelve_le_Li₂ (y := -x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      exact div_nonneg (by linarith) (by linarith [hx.2]))
    tendsto_primA₂_zero tendsto_primA₂_one
  rwa [show -(7 / 8) * zeta3 - -(3 / 2) * zeta3 = 5 / 8 * zeta3 by ring] at h

/-- `A₃ = ∫₀¹ Li₂ x / (1 + x) = (π²/6) log 2 - (5/8) ζ(3)`. -/
theorem intervalIntegrable_and_integral_A₃ :
    IntervalIntegrable (fun x => Li₂ x / (1 + x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Li₂ x / (1 + x) = π ^ 2 / 6 * log 2 - 5 / 8 * zeta3 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg (fun x hx => hasDerivAt_primA₃ hx)
    (fun x hx => div_nonneg (Li₂_nonneg hx.1.le) (by linarith [hx.1]))
    tendsto_primA₃_zero tendsto_primA₃_one
  rwa [show π ^ 2 / 6 * log 2 + 7 / 8 * zeta3 - 3 / 2 * zeta3 =
    π ^ 2 / 6 * log 2 - 5 / 8 * zeta3 by ring] at h

/-- `A₄ = ∫₀¹ Li₂ (-x) / (1 + x) = ζ(3)/4 - (π²/12) log 2`. -/
theorem intervalIntegrable_and_integral_A₄ :
    IntervalIntegrable (fun x => Li₂ (-x) / (1 + x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Li₂ (-x) / (1 + x) = zeta3 / 4 - π ^ 2 / 12 * log 2 := by
  have h := intervalIntegrable_and_integral_eq_of_nonpos (fun x hx => hasDerivAt_primA₄ hx)
    (fun x hx => div_nonpos_of_nonpos_of_nonneg
      (Li₂_nonpos ⟨by linarith [hx.2], by linarith [hx.1]⟩) (by linarith [hx.1]))
    tendsto_primA₄_zero tendsto_primA₄_one
  rwa [show -(π ^ 2 / 12) * log 2 - 7 / 4 * zeta3 - -2 * zeta3 =
    zeta3 / 4 - π ^ 2 / 12 * log 2 by ring] at h

/-! ### `∫₀¹ log (1 - x) / x = -π²/6` -/

theorem intervalIntegrable_and_integral_log_one_sub_div :
    IntervalIntegrable (fun x => log (1 - x) / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log (1 - x) / x = -(π ^ 2 / 6) := by
  have h := intervalIntegrable_and_integral_eq_of_nonpos (F := fun x => -Li₂ x)
    (fun x hx => (hasDerivAt_Li₂' hx).neg.congr_deriv (by ring))
    (fun x hx => div_nonpos_of_nonpos_of_nonneg
      (log_nonpos (by linarith [hx.2]) (by linarith [hx.1])) hx.1.le)
    tendsto_Li₂_zero_right.neg tendsto_Li₂_one_left.neg
  rwa [neg_zero, sub_zero] at h

end QED.Polylog
