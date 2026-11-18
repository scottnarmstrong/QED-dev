/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact values of the ladder and self-energy kernels (helper level, O2-25)

Section 3 of `docs/TWO-LOOP-UNITS.md` represents the limit of the ladder unit L as
`1/6 + ∫₀¹ K_L` (eq. (3.6)) and section 5 represents the finite part of the self-energy unit S
as `b_S = 2 ∫₀¹ K_S` (eq. (5.5)), with the explicit kernels

* `K_L(Y) = (Y³+3Y²-2Y-2) log(1-Y)/(12Y²) + (-7Y³+11Y²+Y-6) log Y/(12(1-Y)²)
    - (23Y³-41Y²+16Y+4)/(24Y(1-Y))`,
* `K_S(Y) = (1-Y)(3Y²+2Y+1) log(1-Y)/(12Y²) + (3Y²-3Y+2)/(24Y) + Y(9Y-8) log Y/(12(1-Y))`.

This file evaluates these two explicit integrals:
`∫₀¹ K_L = 1/16 + π²/18` and `∫₀¹ K_S = 11/48 - π²/36`, so that
`1/6 + ∫₀¹ K_L = 11/48 + π²/18` (`= 11/48 + ζ(2)/3`) and `2 ∫₀¹ K_S = 11/24 - π²/18`
(`= 11/24 - ζ(2)/3`), the BMR-I p. 852 values.

**Scope.** These are helper-level evaluations of explicit one-dimensional integrals. That they
are the limits of the model's L and S units requires the chain of section 8 of
`docs/TWO-LOOP-UNITS.md` (from the frozen model to the parametric integrand, Cheng–Wu, the
splitting identity, the `b`-integral and the two regulator limits), which is **not proved**.

## Endpoint behaviour

`K_L(Y) = -½ log Y - 7/12 + O(Y log Y)` at `Y → 0` and `K_L → 1/4` at `Y → 1`; `K_S → -1/4` at
`Y → 0` and `K_S → 0` at `Y → 1`. The `1/Y`, `1/Y²`, `1/(1-Y)` and `1/(1-Y)²` poles of the
individual terms cancel. In Lean the kernels take junk values at `Y = 0, 1` (division by
zero), a null set.

## Route (sections 3.5 and 5.5 of the document)

On `(0,1)` each kernel is a linear combination of the pieces
`(a + bY) log Y`, `(a + b(1-Y)) log(1-Y)`, `a + bY`,
`P₁(Y) = log(1-Y)/Y`, `P₂(Y) = (log(1-Y) + Y)/Y²`, `P₁(1-Y)` and `P₂(1-Y)`
(`ladderKernel_eq`, `selfEnergyKernel_eq`). The pieces `P₁, P₂` are nonpositive with
antiderivatives `-Li₂ Y` and `-(1-Y) log(1-Y)/Y`, whose one-sided limits at `0` and `1` give
both integrability and the values `∫₀¹ P₁ = -π²/6` (via `Li₂_one`) and `∫₀¹ P₂ = -1`
(`hasIntegralOnUnit_of_hasDerivAt_of_nonpos`). The reflected pieces follow by `Y ↦ 1 - Y`.

## Main statements

* `QED.TwoLoop.Units.intervalIntegrable_ladderKernel`,
  `QED.TwoLoop.Units.integral_ladderKernel`: `∫₀¹ K_L = 1/16 + π²/18`.
* `QED.TwoLoop.Units.ladderUnit_value`: `1/6 + ∫₀¹ K_L = 11/48 + π²/18`.
* `QED.TwoLoop.Units.intervalIntegrable_selfEnergyKernel`,
  `QED.TwoLoop.Units.integral_selfEnergyKernel`: `∫₀¹ K_S = 11/48 - π²/36`.
* `QED.TwoLoop.Units.selfEnergyUnit_finitePart_value`: `2 ∫₀¹ K_S = 11/24 - π²/18`.
-/

public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.TwoLoop.Units

/-! ### The kernels -/

/-- The ladder kernel `K_L` of eq. (3.6) of `docs/TWO-LOOP-UNITS.md`. -/
noncomputable def ladderKernel (Y : ℝ) : ℝ :=
  (Y ^ 3 + 3 * Y ^ 2 - 2 * Y - 2) * log (1 - Y) / (12 * Y ^ 2) +
    (-7 * Y ^ 3 + 11 * Y ^ 2 + Y - 6) * log Y / (12 * (1 - Y) ^ 2) -
    (23 * Y ^ 3 - 41 * Y ^ 2 + 16 * Y + 4) / (24 * Y * (1 - Y))

/-- The self-energy kernel `K_S` of eq. (5.5) of `docs/TWO-LOOP-UNITS.md`. -/
noncomputable def selfEnergyKernel (Y : ℝ) : ℝ :=
  (1 - Y) * (3 * Y ^ 2 + 2 * Y + 1) * log (1 - Y) / (12 * Y ^ 2) +
    (3 * Y ^ 2 - 3 * Y + 2) / (24 * Y) + Y * (9 * Y - 8) * log Y / (12 * (1 - Y))

/-! ### Integrals over `[0,1]` -/

/-- `f` is interval integrable on `[0,1]` with integral `a`. -/
def HasIntegralOnUnit (f : ℝ → ℝ) (a : ℝ) : Prop :=
  IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = a

namespace HasIntegralOnUnit

variable {f g : ℝ → ℝ} {a b : ℝ}

theorem add (hf : HasIntegralOnUnit f a) (hg : HasIntegralOnUnit g b) :
    HasIntegralOnUnit (fun x => f x + g x) (a + b) :=
  ⟨hf.1.add hg.1, by rw [intervalIntegral.integral_add hf.1 hg.1, hf.2, hg.2]⟩

theorem sub (hf : HasIntegralOnUnit f a) (hg : HasIntegralOnUnit g b) :
    HasIntegralOnUnit (fun x => f x - g x) (a - b) :=
  ⟨hf.1.sub hg.1, by rw [intervalIntegral.integral_sub hf.1 hg.1, hf.2, hg.2]⟩

theorem const_mul (hf : HasIntegralOnUnit f a) (c : ℝ) :
    HasIntegralOnUnit (fun x => c * f x) (c * a) :=
  ⟨hf.1.const_mul c, by rw [intervalIntegral.integral_const_mul, hf.2]⟩

/-- Changing the function on `(0,1)` only up to equality, and the value up to equality. -/
theorem congr (hf : HasIntegralOnUnit f a) (hfg : ∀ x ∈ Ioo (0 : ℝ) 1, f x = g x)
    (hab : a = b) : HasIntegralOnUnit g b := by
  have h : EqOn f g (uIoo 0 1) := by
    rw [uIoo_of_le zero_le_one]
    exact hfg
  exact ⟨hf.1.congr_uIoo h, by rw [← intervalIntegral.integral_congr_uIoo h, hf.2, hab]⟩

/-- The reflection `x ↦ 1 - x`. -/
theorem comp_one_sub (hf : HasIntegralOnUnit f a) : HasIntegralOnUnit (fun x => f (1 - x)) a := by
  refine ⟨?_, ?_⟩
  · have h := hf.1.comp_sub_left 1
    rw [sub_zero, sub_self] at h
    exact h.symm
  · rw [intervalIntegral.integral_comp_sub_left, sub_zero, sub_self, hf.2]

end HasIntegralOnUnit

/-- A nonnegative function on `(0,1)` with an antiderivative having one-sided limits at `0`
and `1` is integrable, with integral the difference of the limits. -/
theorem hasIntegralOnUnit_of_hasDerivAt_of_nonneg {F f : ℝ → ℝ} {A B : ℝ}
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x)
    (h0 : Tendsto F (𝓝[>] 0) (𝓝 A)) (h1 : Tendsto F (𝓝[<] 1) (𝓝 B)) :
    HasIntegralOnUnit f (B - A) := by
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

/-- The nonpositive version of `hasIntegralOnUnit_of_hasDerivAt_of_nonneg`. -/
theorem hasIntegralOnUnit_of_hasDerivAt_of_nonpos {F f : ℝ → ℝ} {A B : ℝ}
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo (0 : ℝ) 1, f x ≤ 0)
    (h0 : Tendsto F (𝓝[>] 0) (𝓝 A)) (h1 : Tendsto F (𝓝[<] 1) (𝓝 B)) :
    HasIntegralOnUnit f (B - A) := by
  have h := hasIntegralOnUnit_of_hasDerivAt_of_nonneg (F := fun x => -F x) (f := fun x => -f x)
    (fun x hx => (hd x hx).neg) (fun x hx => neg_nonneg.2 (hf x hx)) h0.neg h1.neg
  refine (h.const_mul (-1)).congr (fun x _ => by ring) (by ring)

/-! ### The pieces -/

/-- `∫₀¹ log = -1`. -/
theorem hasIntegralOnUnit_log : HasIntegralOnUnit log (-1) :=
  ⟨intervalIntegral.intervalIntegrable_log', by rw [integral_log]; simp⟩

/-- `∫₀¹ Y log Y = -1/4`. -/
theorem hasIntegralOnUnit_mul_log : HasIntegralOnUnit (fun x => x * log x) (-1 / 4) := by
  have hc : Continuous fun x : ℝ => x * (x * log x) / 2 - x ^ 2 / 4 :=
    (continuous_id.mul continuous_mul_log).div_const 2 |>.sub (by fun_prop)
  have h := hasIntegralOnUnit_of_hasDerivAt_of_nonpos
    (F := fun x : ℝ => x * (x * log x) / 2 - x ^ 2 / 4) (f := fun x => x * log x)
    (A := 0) (B := -1 / 4) ?_ ?_ ?_ ?_
  · exact h.congr (fun _ _ => rfl) (by ring)
  · intro x hx
    have h1 := ((hasDerivAt_id' x).mul ((hasDerivAt_id' x).mul
      (hasDerivAt_log hx.1.ne'))).div_const 2 |>.sub ((hasDerivAt_pow 2 x).div_const 4)
    refine h1.congr_deriv ?_
    have := hx.1.ne'
    simp only [Pi.mul_apply]
    field_simp
    ring
  · intro x hx
    exact mul_nonpos_of_nonneg_of_nonpos hx.1.le (log_nonpos hx.1.le hx.2.le)
  · have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  · have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    convert this using 2
    norm_num

/-- `∫₀¹ (a + bY) log Y = -a - b/4`. -/
theorem hasIntegralOnUnit_linear_mul_log (a b : ℝ) :
    HasIntegralOnUnit (fun x => (a + b * x) * log x) (-a - b / 4) :=
  ((hasIntegralOnUnit_log.const_mul a).add (hasIntegralOnUnit_mul_log.const_mul b)).congr
    (fun _ _ => by ring) (by ring)

/-- `∫₀¹ (a + b(1-Y)) log(1-Y) = -a - b/4`. -/
theorem hasIntegralOnUnit_linear_mul_log_one_sub (a b : ℝ) :
    HasIntegralOnUnit (fun x => (a + b * (1 - x)) * log (1 - x)) (-a - b / 4) :=
  (hasIntegralOnUnit_linear_mul_log a b).comp_one_sub

/-- `∫₀¹ (a + bY) = a + b/2`. -/
theorem hasIntegralOnUnit_linear (a b : ℝ) : HasIntegralOnUnit (fun x => a + b * x) (a + b / 2) := by
  refine ⟨(by fun_prop : Continuous fun x : ℝ => a + b * x).intervalIntegrable 0 1, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => a * x + b * (x ^ 2 / 2))
    (fun x _ => ?_) ((by fun_prop : Continuous fun x : ℝ => a + b * x).intervalIntegrable 0 1)]
  · ring
  · have := ((hasDerivAt_id' x).const_mul a).add (((hasDerivAt_pow 2 x).div_const 2).const_mul b)
    refine this.congr_deriv ?_
    push_cast
    ring

/-- The first dilogarithmic piece: `∫₀¹ log(1-Y)/Y = -π²/6`. -/
theorem hasIntegralOnUnit_log_one_sub_div :
    HasIntegralOnUnit (fun x => log (1 - x) / x) (-(π ^ 2 / 6)) := by
  have h := hasIntegralOnUnit_of_hasDerivAt_of_nonpos (F := fun x => -Li₂ x)
    (f := fun x => log (1 - x) / x) (A := -0) (B := -(π ^ 2 / 6)) ?_ ?_ ?_ ?_
  · exact h.congr (fun _ _ => rfl) (by ring)
  · intro x hx
    have := (hasDerivAt_Li₂ (by rw [abs_of_pos hx.1]; exact hx.2) hx.1.ne').neg
    refine this.congr_deriv ?_
    ring
  · intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (log_nonpos (by linarith [hx.2]) (by linarith [hx.1]))
      hx.1.le
  · have h := (continuousOn_Li₂.continuousAt
      (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))).tendsto
    have h0 : Li₂ 0 = 0 := by simp [Li₂]
    rw [h0] at h
    exact (h.mono_left nhdsWithin_le_nhds).neg
  · have hLi : ContinuousWithinAt Li₂ (Iio 1) 1 :=
      (continuousOn_Li₂ 1 (by norm_num)).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)) Ioo_subset_Icc_self)
    have h := hLi.tendsto.neg
    rwa [Li₂_one] at h

/-- `log(1-Y)/Y → -1` as `Y → 0⁺`. -/
theorem tendsto_log_one_sub_div_zero :
    Tendsto (fun x => log (1 - x) / x) (𝓝[>] 0) (𝓝 (-1)) := by
  have hd : HasDerivAt (fun y : ℝ => log (1 - y)) (-1) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_sub 1).log (by norm_num)
    simpa using this
  refine hd.tendsto_slope_zero_right.congr fun t => ?_
  simp only [zero_add, sub_zero, log_one, smul_eq_mul]
  ring

/-- The second piece: `∫₀¹ (log(1-Y) + Y)/Y² = -1`. -/
theorem hasIntegralOnUnit_log_one_sub_add_div_sq :
    HasIntegralOnUnit (fun x => (log (1 - x) + x) / x ^ 2) (-1) := by
  have h := hasIntegralOnUnit_of_hasDerivAt_of_nonpos
    (F := fun x => -((1 - x) * log (1 - x)) / x) (f := fun x => (log (1 - x) + x) / x ^ 2)
    (A := 1) (B := -0 / 1) ?_ ?_ ?_ ?_
  · exact h.congr (fun _ _ => rfl) (by ring)
  · intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hne : (1 : ℝ) - x ≠ 0 := by linarith
    have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub 1
    have := (hs.mul (hs.log hne)).neg.div (hasDerivAt_id' x) hx0.ne'
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.neg_apply]
    field_simp
    ring
  · intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - x)
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg x)
  · have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_id (x := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds)).mul
        tendsto_log_one_sub_div_zero
    refine (h.neg.congr' ?_).trans ?_
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      simp only [id]
      ring
    · norm_num
  · have hL : Continuous fun y : ℝ => (1 - y) * log (1 - y) :=
      continuous_mul_log.comp (continuous_const.sub continuous_id)
    have h := ((hL.neg.continuousAt (x := 1)).div continuousAt_id one_ne_zero).tendsto
    have := h.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    convert this using 2
    simp only [Pi.div_apply, Pi.neg_apply, id]
    norm_num

/-! ### The decompositions -/

/-- On `(0,1)`, `K_L` is the combination of the pieces of section 3.5 of the document. -/
theorem ladderKernel_eq {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ladderKernel Y =
      1 / 12 * ((4 + -1 * (1 - Y)) * log (1 - Y)) - 1 / 6 * (log (1 - Y) / Y) -
        1 / 6 * ((log (1 - Y) + Y) / Y ^ 2) -
        1 / 12 * ((log (1 - (1 - Y)) + (1 - Y)) / (1 - Y) ^ 2) -
        1 / 6 * (log (1 - (1 - Y)) / (1 - Y)) + 1 / 12 * ((-3 + -7 * Y) * log Y) +
        (-18 / 24 + 23 / 24 * Y) := by
  obtain ⟨hY0, hY1⟩ := hY
  have h1 : (1 : ℝ) - Y ≠ 0 := by linarith
  have h0 : Y ≠ 0 := hY0.ne'
  rw [sub_sub_cancel]
  unfold ladderKernel
  field_simp
  ring

/-- On `(0,1)`, `K_S` is the combination of the pieces of section 5.5 of the document. -/
theorem selfEnergyKernel_eq {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    selfEnergyKernel Y =
      1 / 12 * ((-2 + 3 * (1 - Y)) * log (1 - Y)) + 1 / 12 * (log (1 - Y) / Y) +
        1 / 12 * ((log (1 - Y) + Y) / Y ^ 2) + (-1 / 8 + 1 / 8 * Y) +
        1 / 12 * (log (1 - (1 - Y)) / (1 - Y)) + 1 / 12 * ((-1 + -9 * Y) * log Y) := by
  obtain ⟨hY0, hY1⟩ := hY
  have h1 : (1 : ℝ) - Y ≠ 0 := by linarith
  have h0 : Y ≠ 0 := hY0.ne'
  rw [sub_sub_cancel]
  unfold selfEnergyKernel
  field_simp
  ring

/-! ### Main statements -/

theorem hasIntegralOnUnit_ladderKernel : HasIntegralOnUnit ladderKernel (1 / 16 + π ^ 2 / 18) := by
  have h := ((((((hasIntegralOnUnit_linear_mul_log_one_sub 4 (-1)).const_mul (1 / 12)).sub
    (hasIntegralOnUnit_log_one_sub_div.const_mul (1 / 6))).sub
    (hasIntegralOnUnit_log_one_sub_add_div_sq.const_mul (1 / 6))).sub
    (hasIntegralOnUnit_log_one_sub_add_div_sq.comp_one_sub.const_mul (1 / 12))).sub
    (hasIntegralOnUnit_log_one_sub_div.comp_one_sub.const_mul (1 / 6))).add
    ((hasIntegralOnUnit_linear_mul_log (-3) (-7)).const_mul (1 / 12)) |>.add
    (hasIntegralOnUnit_linear (-18 / 24) (23 / 24))
  exact h.congr (fun Y hY => (ladderKernel_eq hY).symm) (by ring)

theorem hasIntegralOnUnit_selfEnergyKernel :
    HasIntegralOnUnit selfEnergyKernel (11 / 48 - π ^ 2 / 36) := by
  have h := (((((hasIntegralOnUnit_linear_mul_log_one_sub (-2) 3).const_mul (1 / 12)).add
    (hasIntegralOnUnit_log_one_sub_div.const_mul (1 / 12))).add
    (hasIntegralOnUnit_log_one_sub_add_div_sq.const_mul (1 / 12))).add
    (hasIntegralOnUnit_linear (-1 / 8) (1 / 8))).add
    (hasIntegralOnUnit_log_one_sub_div.comp_one_sub.const_mul (1 / 12)) |>.add
    ((hasIntegralOnUnit_linear_mul_log (-1) (-9)).const_mul (1 / 12))
  exact h.congr (fun Y hY => (selfEnergyKernel_eq hY).symm) (by ring)

/-- The ladder kernel `K_L` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_ladderKernel : IntervalIntegrable ladderKernel volume 0 1 :=
  hasIntegralOnUnit_ladderKernel.1

/-- **The ladder kernel integral.** `∫₀¹ K_L = 1/16 + π²/18`. -/
theorem integral_ladderKernel : ∫ Y in (0 : ℝ)..1, ladderKernel Y = 1 / 16 + π ^ 2 / 18 :=
  hasIntegralOnUnit_ladderKernel.2

/-- The representation (3.6) of the ladder unit evaluates to `11/48 + π²/18 = 11/48 + ζ(2)/3`.
Helper level: that this is the limit of the model's L unit is not proved here. -/
theorem ladderUnit_value : 1 / 6 + ∫ Y in (0 : ℝ)..1, ladderKernel Y = 11 / 48 + π ^ 2 / 18 := by
  rw [integral_ladderKernel]
  ring

/-- The self-energy kernel `K_S` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_selfEnergyKernel : IntervalIntegrable selfEnergyKernel volume 0 1 :=
  hasIntegralOnUnit_selfEnergyKernel.1

/-- **The self-energy kernel integral.** `∫₀¹ K_S = 11/48 - π²/36`. -/
theorem integral_selfEnergyKernel :
    ∫ Y in (0 : ℝ)..1, selfEnergyKernel Y = 11 / 48 - π ^ 2 / 36 :=
  hasIntegralOnUnit_selfEnergyKernel.2

/-- The finite part `b_S = 2 ∫₀¹ K_S` of (5.5) evaluates to `11/24 - π²/18 = 11/24 - ζ(2)/3`.
Helper level: that this is the finite part of the model's S unit is not proved here. -/
theorem selfEnergyUnit_finitePart_value :
    2 * ∫ Y in (0 : ℝ)..1, selfEnergyKernel Y = 11 / 24 - π ^ 2 / 18 := by
  rw [integral_selfEnergyKernel]
  ring

end QED.TwoLoop.Units
