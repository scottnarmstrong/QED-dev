/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ExtendFrom

/-!
# Master integrals of the crossed-ladder unit (helper level, O2-25)

Section 4.5 of `docs/TWO-LOOP-UNITS.md` reduces the crossed-ladder unit X to the one-dimensional
integral `X = ∫₀¹ K_X` (eq. (4.7)) and then, by integration by parts (eqs. (4.8)–(4.10)), to
eight master integrals over `(0, 1)` (eq. (4.9) and the table of 4.5.4). With
`D(Y) = Li₂ (1 - 2Y) - Li₂ (2Y - 1)` (`crossedD`) they are

* `M₁ = ∫ Li₂ Y / Y = ζ(3)`, `M₂ = ∫ log Y log (1 - Y) / Y = ζ(3)`,
* `M₃ = ∫ (D(Y) - π²/4) / Y = -(π²/2) log 2 - (7/4) ζ(3)`, the only one with `log 2`,
* `M₃' = ∫ (D(Y) + π²/4) / (Y - 1) = M₃`,
* `M₄ = ∫ (Li₂ Y - π²/6) / (Y - 1) = 2 ζ(3)`, `M₅ = ∫ log² Y / (Y - 1) = -2 ζ(3)`,
* `M₆ = ∫ log Y / (Y - 1) = π²/6`, `M₇ = ∫ log (1 - Y) / Y = -π²/6`,
* `M₈ = ∫ (log Y - log (1 - Y)) / (2Y - 1) = π²/4`.

All eight are proved with integrability: `M₁`, `M₂`, `M₇` in `QED.Polylog.ExtraIntegrals`
(`intervalIntegrable_and_integral_Li₂_div`, `…_log_mul_log_one_sub_div`, `…_log_one_sub_div`),
the others here. This file also proves the arithmetic of the final assembly
(4.12): the combination of the masters, together with the boundary values `G(0⁺)`, `G(1⁻)` and
`∫ p` of (4.10), equals BMR's value `1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)`
(`crossedUnit_assembly`).

**Scope.** Helper level. Not proved here: the representation (4.4) of X and its link to the
model (section 8 of the document), the `ξ`-integration giving `K_X` (4.7), the identity
`K_X = G' + p + K_m` (4.8), the limits (4.10) and the integrability of `K_X`. Those steps are
derived in exact rational arithmetic and checked numerically (mode `crossedexact` of
`scripts/numerics/two_loop_unit_integrals.py`), not proved.

## Route for `M₃`

On `(0, 1/2)` put `x = 1 - 2Y`; then `(D(Y) - π²/4) / Y = 2 g(x)/(1 - x)` with
`g(x) = Li₂ x - Li₂ (-x) - π²/4`, and `-(H₁ - H₂)(1 - 2Y)` is an antiderivative, where
`H₁ = primA₁`, `H₂ = primA₂` are the antiderivatives of `(Li₂ x - π²/6)/(1-x)` and
`(Li₂ (-x) + π²/12)/(1-x)` from `QED.Polylog.ExtraIntegrals`. On `(1/2, 1)` put `v = 2Y - 1`;
then `(-H₃ + H₄)(v) - (π²/4) log (1 + v)` is an antiderivative (`H₃ = primA₃`, `H₄ = primA₄`).
The integrand is nonpositive (`Li₂ ≤ π²/6` and `Li₂ ≥ -π²/12` on `[-1, 1]`), which gives
integrability. The values come from the one-sided limits of `H₁, …, H₄`, which involve
`Li₂ (1/2)` and `Li₃ (1/2)` through `F₃`.
-/

public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.TwoLoop.Units

/-! ### Tools on a general interval -/

/-- A nonnegative function on `(a, b)` with an antiderivative having one-sided limits at `a` and
`b` is interval integrable, with integral the difference of the limits. -/
theorem intervalIntegrable_and_integral_eq_of_nonneg_Ioo {a b : ℝ} (hab : a < b) {F f : ℝ → ℝ}
    {A B : ℝ} (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo a b, 0 ≤ f x)
    (h0 : Tendsto F (𝓝[>] a) (𝓝 A)) (h1 : Tendsto F (𝓝[<] b) (𝓝 B)) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = B - A := by
  have hFc : ContinuousOn F (Ioo a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hGc : ContinuousOn (extendFrom (Ioo a b) F) (Icc a b) :=
    continuousOn_Icc_extendFrom_Ioo hFc h0 h1
  have hGd : ∀ x ∈ Ioo a b, HasDerivAt (extendFrom (Ioo a b) F) (f x) x := by
    intro x hx
    refine (hd x hx).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact extendFrom_extends hFc y hy
  have hint : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      (intervalIntegral.integrableOn_deriv_of_nonneg hGc hGd hf)
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hd hint h0 h1⟩

/-- The nonpositive version of `intervalIntegrable_and_integral_eq_of_nonneg_Ioo`. -/
theorem intervalIntegrable_and_integral_eq_of_nonpos_Ioo {a b : ℝ} (hab : a < b) {F f : ℝ → ℝ}
    {A B : ℝ} (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo a b, f x ≤ 0)
    (h0 : Tendsto F (𝓝[>] a) (𝓝 A)) (h1 : Tendsto F (𝓝[<] b) (𝓝 B)) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = B - A := by
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_eq_of_nonneg_Ioo hab (F := fun x => -F x)
    (f := fun x => -f x) (fun x hx => (hd x hx).neg) (fun x hx => neg_nonneg.2 (hf x hx)) h0.neg
    h1.neg
  have hi' : IntervalIntegrable (fun x => - -f x) volume a b := hi.neg
  refine ⟨by simpa only [neg_neg] using hi', ?_⟩
  rw [intervalIntegral.integral_neg] at hv
  linarith

/-- Two adjacent pieces `[0, 1/2]` and `[1/2, 1]` give the integral over `[0, 1]`. -/
theorem unitIntegral_of_halves {f : ℝ → ℝ} {a b : ℝ}
    (h₁ : IntervalIntegrable f volume 0 (1 / 2) ∧ ∫ x in (0 : ℝ)..1 / 2, f x = a)
    (h₂ : IntervalIntegrable f volume (1 / 2) 1 ∧ ∫ x in (1 / 2 : ℝ)..1, f x = b) :
    IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = a + b :=
  ⟨h₁.1.trans h₂.1, by rw [← intervalIntegral.integral_add_adjacent_intervals h₁.1 h₂.1, h₁.2, h₂.2]⟩

/-- Changing the integrand on `(0, 1)` and the value up to equality. -/
theorem unitIntegral_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = a)
    (hfg : ∀ x ∈ Ioo (0 : ℝ) 1, f x = g x) (hab : a = b) :
    IntervalIntegrable g volume 0 1 ∧ ∫ x in (0 : ℝ)..1, g x = b := by
  have h : EqOn f g (uIoo 0 1) := by
    rw [uIoo_of_le zero_le_one]
    exact hfg
  exact ⟨hf.1.congr_uIoo h, by rw [← intervalIntegral.integral_congr_uIoo h, hf.2, hab]⟩

/-- The reflection `x ↦ 1 - x`. -/
theorem unitIntegral_comp_one_sub {f : ℝ → ℝ} {a : ℝ}
    (hf : IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = a) :
    IntervalIntegrable (fun x => f (1 - x)) volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f (1 - x) = a := by
  refine ⟨?_, ?_⟩
  · have h := hf.1.comp_sub_left 1
    rw [sub_zero, sub_self] at h
    exact h.symm
  · rw [intervalIntegral.integral_comp_sub_left, sub_zero, sub_self, hf.2]

/-- Multiplication by a constant. -/
theorem unitIntegral_const_mul {f : ℝ → ℝ} {a : ℝ}
    (hf : IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = a) (c : ℝ) :
    IntervalIntegrable (fun x => c * f x) volume 0 1 ∧ ∫ x in (0 : ℝ)..1, c * f x = c * a :=
  ⟨hf.1.const_mul c, by rw [intervalIntegral.integral_const_mul, hf.2]⟩

/-- An affine map `Y ↦ c + s Y` sends a one-sided neighbourhood to a one-sided neighbourhood. -/
theorem tendsto_affine_nhdsWithin {c s p q : ℝ} {S T : Set ℝ}
    (hq : c + s * p = q) (hST : ∀ᶠ Y in 𝓝[S] p, c + s * Y ∈ T) :
    Tendsto (fun Y => c + s * Y) (𝓝[S] p) (𝓝[T] q) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, hST⟩
  have : Tendsto (fun Y => c + s * Y) (𝓝 p) (𝓝 (c + s * p)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
  rw [hq] at this
  exact this.mono_left nhdsWithin_le_nhds

/-! ### The function `D` -/

/-- `D(Y) = Li₂ (1 - 2Y) - Li₂ (2Y - 1)` (section 4.5.2 of the document). -/
noncomputable def crossedD (Y : ℝ) : ℝ := Li₂ (1 - 2 * Y) - Li₂ (2 * Y - 1)

theorem crossedD_one_sub (Y : ℝ) : crossedD (1 - Y) = -crossedD Y := by
  unfold crossedD
  rw [show 1 - 2 * (1 - Y) = 2 * Y - 1 by ring, show 2 * (1 - Y) - 1 = 1 - 2 * Y by ring]
  ring

/-- `D(Y) ≤ π²/4` on `[0, 1]`. -/
theorem crossedD_le {Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) 1) : crossedD Y ≤ π ^ 2 / 4 := by
  have h1 := Li₂_le_pi_sq_div_six (y := 1 - 2 * Y) ⟨by linarith [hY.2], by linarith [hY.1]⟩
  have h2 := neg_pi_sq_div_twelve_le_Li₂ (y := 2 * Y - 1) ⟨by linarith [hY.1], by linarith [hY.2]⟩
  unfold crossedD
  linarith

theorem continuousOn_crossedD : ContinuousOn crossedD (Icc 0 1) := by
  have m1 : MapsTo (fun Y : ℝ => 1 - 2 * Y) (Icc 0 1) (Icc (-1) 1) :=
    fun Y hY => ⟨by linarith [hY.2], by linarith [hY.1]⟩
  have m2 : MapsTo (fun Y : ℝ => 2 * Y - 1) (Icc 0 1) (Icc (-1) 1) :=
    fun Y hY => ⟨by linarith [hY.1], by linarith [hY.2]⟩
  exact (continuousOn_Li₂.comp (by fun_prop : Continuous fun Y : ℝ => 1 - 2 * Y).continuousOn m1).sub
    (continuousOn_Li₂.comp (by fun_prop : Continuous fun Y : ℝ => 2 * Y - 1).continuousOn m2)

theorem crossedD_zero : crossedD 0 = π ^ 2 / 4 := by
  simp only [crossedD, mul_zero, sub_zero, zero_sub, Li₂_one, Li₂_neg_one]
  ring

theorem crossedD_half : crossedD (1 / 2) = 0 := by
  simp [crossedD]

theorem crossedD_one : crossedD 1 = -(π ^ 2 / 4) := by
  have h := crossedD_one_sub 0
  rw [sub_zero, crossedD_zero] at h
  exact h

/-- For `Y ∈ (0, 1)`, `Y ≠ 1/2`: `D'(Y) = 2 (log Y - log (1 - Y)) / (1 - 2Y)`. -/
theorem hasDerivAt_crossedD {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hh : Y ≠ 1 / 2) :
    HasDerivAt crossedD (2 * (log Y - log (1 - Y)) / (1 - 2 * Y)) Y := by
  obtain ⟨hY0, hY1⟩ := hY
  have hne : (1 : ℝ) - 2 * Y ≠ 0 := fun h => hh (by linarith)
  have hne' : (2 : ℝ) * Y - 1 ≠ 0 := fun h => hh (by linarith)
  have ha : |1 - 2 * Y| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  have hb : |2 * Y - 1| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  have d1 : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) Y := by
    simpa using ((hasDerivAt_id' Y).const_mul 2).const_sub 1
  have d2 : HasDerivAt (fun y : ℝ => 2 * y - 1) 2 Y := by
    simpa using ((hasDerivAt_id' Y).const_mul 2).sub_const 1
  have h := ((hasDerivAt_Li₂ ha hne).comp Y d1).sub ((hasDerivAt_Li₂ hb hne').comp Y d2)
  refine h.congr_deriv ?_
  rw [show (1 : ℝ) - (1 - 2 * Y) = 2 * Y by ring, show (1 : ℝ) - (2 * Y - 1) = 2 * (1 - Y) by ring,
    log_mul two_ne_zero hY0.ne', log_mul two_ne_zero (by linarith : (1 : ℝ) - Y ≠ 0)]
  field_simp
  ring

/-! ### The masters `M₁, M₂, M₄, …, M₇` -/

/-- `M₄ = ∫₀¹ (Li₂ Y - π²/6)/(Y - 1) = 2 ζ(3)` (`= -A₁`). -/
theorem intervalIntegrable_and_integral_Li₂_sub_div_sub_one :
    IntervalIntegrable (fun Y => (Li₂ Y - π ^ 2 / 6) / (Y - 1)) volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, (Li₂ Y - π ^ 2 / 6) / (Y - 1) = 2 * zeta3 := by
  refine unitIntegral_congr (unitIntegral_const_mul intervalIntegrable_and_integral_A₁ (-1))
    (fun Y hY => ?_) (by ring)
  have : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
  have : Y - 1 ≠ 0 := by linarith [hY.2]
  field_simp
  ring

/-- `M₅ = ∫₀¹ log² Y/(Y - 1) = -2 ζ(3)` (`= -J₁`). -/
theorem intervalIntegrable_and_integral_log_sq_div_sub_one :
    IntervalIntegrable (fun Y => log Y ^ 2 / (Y - 1)) volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, log Y ^ 2 / (Y - 1) = -2 * zeta3 := by
  refine unitIntegral_congr (unitIntegral_const_mul
    (unitIntegral_comp_one_sub intervalIntegrable_and_integral_log_one_sub_sq_div) (-1))
    (fun Y hY => ?_) (by ring)
  have : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
  have : Y - 1 ≠ 0 := by linarith [hY.2]
  rw [sub_sub_cancel]
  field_simp
  ring

/-- `M₆ = ∫₀¹ log Y/(Y - 1) = π²/6`. -/
theorem intervalIntegrable_and_integral_log_div_sub_one :
    IntervalIntegrable (fun Y => log Y / (Y - 1)) volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, log Y / (Y - 1) = π ^ 2 / 6 := by
  refine unitIntegral_congr (unitIntegral_const_mul
    (unitIntegral_comp_one_sub intervalIntegrable_and_integral_log_one_sub_div) (-1))
    (fun Y hY => ?_) (by ring)
  have : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
  have : Y - 1 ≠ 0 := by linarith [hY.2]
  rw [sub_sub_cancel]
  field_simp
  ring

/-! ### `M₈ = ∫₀¹ (log Y - log (1 - Y))/(2Y - 1) = π²/4` -/

theorem intervalIntegrable_and_integral_log_sub_log_div :
    IntervalIntegrable (fun Y => (log Y - log (1 - Y)) / (2 * Y - 1)) volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, (log Y - log (1 - Y)) / (2 * Y - 1) = π ^ 2 / 4 := by
  have hd : ∀ Y ∈ Ioo (0 : ℝ) 1, Y ≠ 1 / 2 →
      HasDerivAt (fun y => -crossedD y / 2) ((log Y - log (1 - Y)) / (2 * Y - 1)) Y := by
    intro Y hY hh
    refine ((hasDerivAt_crossedD hY hh).neg.div_const 2).congr_deriv ?_
    have hne : (1 : ℝ) - 2 * Y ≠ 0 := fun h => hh (by linarith)
    have hne' : (2 : ℝ) * Y - 1 ≠ 0 := fun h => hh (by linarith)
    field_simp
    ring
  have hc : ContinuousOn (fun y => -crossedD y / 2) (Icc 0 1) :=
    continuousOn_crossedD.neg.div_const 2
  have lim : ∀ p ∈ Icc (0 : ℝ) 1, ∀ S : Set ℝ, Icc 0 1 ∈ 𝓝[S] p →
      Tendsto (fun y => -crossedD y / 2) (𝓝[S] p) (𝓝 (-crossedD p / 2)) :=
    fun p hp S hS => (hc p hp).tendsto.mono_left (nhdsWithin_le_of_mem hS)
  have h₁ := intervalIntegrable_and_integral_eq_of_nonneg_Ioo (by norm_num : (0 : ℝ) < 1 / 2)
    (fun Y hY => hd Y ⟨hY.1, by linarith [hY.2]⟩ (by linarith [hY.2]))
    (fun Y hY => div_nonneg_of_nonpos
      (sub_nonpos.2 (log_le_log hY.1 (by linarith [hY.2]))) (by linarith [hY.2]))
    (lim 0 (by norm_num) _ (mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
      Ioo_subset_Icc_self))
    (lim (1 / 2) (by norm_num) _ (mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2))
      fun y hy => ⟨hy.1.le, by linarith [hy.2]⟩))
  have h₂ := intervalIntegrable_and_integral_eq_of_nonneg_Ioo (by norm_num : (1 / 2 : ℝ) < 1)
    (fun Y hY => hd Y ⟨by linarith [hY.1], hY.2⟩ (by linarith [hY.1]))
    (fun Y hY => div_nonneg
      (sub_nonneg.2 (log_le_log (by linarith [hY.2]) (by linarith [hY.1]))) (by linarith [hY.1]))
    (lim (1 / 2) (by norm_num) _ (mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (1 / 2 : ℝ) < 1))
      fun y hy => ⟨by linarith [hy.1], hy.2.le⟩))
    (lim 1 (by norm_num) _ (mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
      Ioo_subset_Icc_self))
  refine unitIntegral_congr (unitIntegral_of_halves h₁ h₂) (fun _ _ => rfl) ?_
  rw [crossedD_zero, crossedD_half, crossedD_one]
  ring

/-! ### `M₃ = ∫₀¹ (D(Y) - π²/4)/Y = -(π²/2) log 2 - (7/4) ζ(3)` -/

/-- The `M₃` integrand is nonpositive on `(0, 1)`. -/
theorem crossedD_sub_div_nonpos {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    (crossedD Y - π ^ 2 / 4) / Y ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (crossedD_le ⟨hY.1.le, hY.2.le⟩)) hY.1.le

/-- The first half: `∫₀^{1/2} (D(Y) - π²/4)/Y = -(21/8) ζ(3)`, with antiderivative
`-(H₁ - H₂)(1 - 2Y)`. -/
theorem crossedM₃_first_half :
    IntervalIntegrable (fun Y => (crossedD Y - π ^ 2 / 4) / Y) volume 0 (1 / 2) ∧
      ∫ Y in (0 : ℝ)..1 / 2, (crossedD Y - π ^ 2 / 4) / Y = -(21 / 8) * zeta3 := by
  have hd : ∀ Y ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt (fun y => -(primA₁ (1 - 2 * y) -
      primA₂ (1 - 2 * y))) ((crossedD Y - π ^ 2 / 4) / Y) Y := by
    intro Y hY
    have hx : 1 - 2 * Y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hY.2], by linarith [hY.1]⟩
    have d1 : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) Y := by
      simpa using ((hasDerivAt_id' Y).const_mul 2).const_sub 1
    have h := (((hasDerivAt_primA₁ hx).comp Y d1).sub ((hasDerivAt_primA₂ hx).comp Y d1)).neg
    refine h.congr_deriv ?_
    have h1 : (1 : ℝ) - (1 - 2 * Y) ≠ 0 := by linarith [hY.1]
    have h0 : Y ≠ 0 := hY.1.ne'
    unfold crossedD
    rw [show -(1 - 2 * Y) = 2 * Y - 1 by ring, show (1 : ℝ) - (1 - 2 * Y) = 2 * Y by ring]
    field_simp
    ring
  have t0 : Tendsto (fun y : ℝ => 1 - 2 * y) (𝓝[>] 0) (𝓝[<] 1) := by
    have := tendsto_affine_nhdsWithin (c := 1) (s := -2) (p := 0) (q := 1) (S := Ioi 0) (T := Iio 1)
      (by ring) (by
        filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
        show 1 + -2 * y < 1
        linarith)
    simpa [sub_eq_add_neg, neg_mul] using this
  have t1 : Tendsto (fun y : ℝ => 1 - 2 * y) (𝓝[<] (1 / 2)) (𝓝[>] 0) := by
    have := tendsto_affine_nhdsWithin (c := 1) (s := -2) (p := 1 / 2) (q := 0) (S := Iio (1 / 2))
      (T := Ioi 0) (by ring) (by
        filter_upwards [self_mem_nhdsWithin] with y (hy : y < 1 / 2)
        show 0 < 1 + -2 * y
        linarith)
    simpa [sub_eq_add_neg, neg_mul] using this
  have h := intervalIntegrable_and_integral_eq_of_nonpos_Ioo (by norm_num : (0 : ℝ) < 1 / 2) hd
    (fun Y hY => crossedD_sub_div_nonpos ⟨hY.1, by linarith [hY.2]⟩)
    (((tendsto_primA₁_one.comp t0).sub (tendsto_primA₂_one.comp t0)).neg)
    (((tendsto_primA₁_zero.comp t1).sub (tendsto_primA₂_zero.comp t1)).neg)
  rwa [show -(2 * zeta3 - -(3 / 2) * zeta3) - -(0 - -(7 / 8) * zeta3) = -(21 / 8) * zeta3 by ring]
    at h

/-- The second half: `∫_{1/2}^1 (D(Y) - π²/4)/Y = -(π²/2) log 2 + (7/8) ζ(3)`, with
antiderivative `(-H₃ + H₄)(2Y - 1) - (π²/4) log (2Y)`. -/
theorem crossedM₃_second_half :
    IntervalIntegrable (fun Y => (crossedD Y - π ^ 2 / 4) / Y) volume (1 / 2) 1 ∧
      ∫ Y in (1 / 2 : ℝ)..1, (crossedD Y - π ^ 2 / 4) / Y =
        -(π ^ 2 / 2) * log 2 + 7 / 8 * zeta3 := by
  have hd : ∀ Y ∈ Ioo (1 / 2 : ℝ) 1, HasDerivAt (fun y => -primA₃ (2 * y - 1) +
      primA₄ (2 * y - 1) - π ^ 2 / 4 * log (1 + (2 * y - 1))) ((crossedD Y - π ^ 2 / 4) / Y) Y := by
    intro Y hY
    have hv : 2 * Y - 1 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hY.1], by linarith [hY.2]⟩
    have d2 : HasDerivAt (fun y : ℝ => 2 * y - 1) 2 Y := by
      simpa using ((hasDerivAt_id' Y).const_mul 2).sub_const 1
    have hl := ((hasDerivAt_log_one_add (by linarith [hv.1])).comp Y d2).const_mul (π ^ 2 / 4)
    have h := (((hasDerivAt_primA₃ hv).comp Y d2).neg.add ((hasDerivAt_primA₄ hv).comp Y d2)).sub hl
    refine h.congr_deriv ?_
    have h1 : (1 : ℝ) + (2 * Y - 1) ≠ 0 := by linarith [hY.1]
    have h0 : Y ≠ 0 := by linarith [hY.1]
    unfold crossedD
    rw [show -(2 * Y - 1) = 1 - 2 * Y by ring, show (1 : ℝ) + (2 * Y - 1) = 2 * Y by ring]
    field_simp
    ring
  have t0 : Tendsto (fun y : ℝ => 2 * y - 1) (𝓝[>] (1 / 2)) (𝓝[>] 0) := by
    have := tendsto_affine_nhdsWithin (c := -1) (s := 2) (p := 1 / 2) (q := 0) (S := Ioi (1 / 2))
      (T := Ioi 0) (by ring) (by
        filter_upwards [self_mem_nhdsWithin] with y (hy : 1 / 2 < y)
        show 0 < -1 + 2 * y
        linarith)
    refine this.congr fun y => ?_
    ring
  have t1 : Tendsto (fun y : ℝ => 2 * y - 1) (𝓝[<] 1) (𝓝[<] 1) := by
    have := tendsto_affine_nhdsWithin (c := -1) (s := 2) (p := 1) (q := 1) (S := Iio 1)
      (T := Iio 1) (by ring) (by
        filter_upwards [self_mem_nhdsWithin] with y (hy : y < 1)
        show -1 + 2 * y < 1
        linarith)
    refine this.congr fun y => ?_
    ring
  have hl0 : Tendsto (fun y : ℝ => log (1 + (2 * y - 1))) (𝓝[>] (1 / 2)) (𝓝 0) :=
    tendsto_log_one_add_zero.comp t0
  have hl1 : Tendsto (fun y : ℝ => log (1 + (2 * y - 1))) (𝓝[<] 1) (𝓝 (log 2)) :=
    tendsto_log_one_add_one.comp t1
  have h := intervalIntegrable_and_integral_eq_of_nonpos_Ioo (by norm_num : (1 / 2 : ℝ) < 1) hd
    (fun Y hY => crossedD_sub_div_nonpos ⟨by linarith [hY.1], hY.2⟩)
    ((((tendsto_primA₃_zero.comp t0).neg.add (tendsto_primA₄_zero.comp t0)).sub
      (hl0.const_mul (π ^ 2 / 4))))
    ((((tendsto_primA₃_one.comp t1).neg.add (tendsto_primA₄_one.comp t1)).sub
      (hl1.const_mul (π ^ 2 / 4))))
  rw [h.2]
  exact ⟨h.1, by ring⟩

/-- **The master `M₃`.** `∫₀¹ (Li₂ (1 - 2Y) - Li₂ (2Y - 1) - π²/4)/Y = -(π²/2) log 2 - (7/4) ζ(3)`,
that is `-3 ζ(2) log 2 - (7/4) ζ(3)`. -/
theorem intervalIntegrable_and_integral_crossedD_sub_div :
    IntervalIntegrable (fun Y => (crossedD Y - π ^ 2 / 4) / Y) volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, (crossedD Y - π ^ 2 / 4) / Y = -(π ^ 2 / 2) * log 2 - 7 / 4 * zeta3 :=
  unitIntegral_congr (unitIntegral_of_halves crossedM₃_first_half crossedM₃_second_half)
    (fun _ _ => rfl) (by ring)

/-- **The master `M₃'`.** `∫₀¹ (D(Y) + π²/4)/(Y - 1) = M₃`, by `Y ↦ 1 - Y` and `D(1-Y) = -D(Y)`. -/
theorem intervalIntegrable_and_integral_crossedD_add_div_sub_one :
    IntervalIntegrable (fun Y => (crossedD Y + π ^ 2 / 4) / (Y - 1)) volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, (crossedD Y + π ^ 2 / 4) / (Y - 1) =
        -(π ^ 2 / 2) * log 2 - 7 / 4 * zeta3 := by
  refine unitIntegral_congr (unitIntegral_comp_one_sub
    intervalIntegrable_and_integral_crossedD_sub_div) (fun Y hY => ?_) rfl
  have : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
  have : Y - 1 ≠ 0 := by linarith [hY.2]
  rw [crossedD_one_sub]
  field_simp
  ring

/-! ### The assembly (4.12) -/

/-- **Arithmetic of the assembly (4.12).** With the boundary values `G(1⁻) = 1/3 + ζ(2)/12`,
`G(0⁺) = 17/24 + ζ(2)/4` and `∫₀¹ p = 13/24 + 7 ζ(2)/4` of (4.10) (derived, not proved here),
the combination of the master integrals in (4.12) is BMR's value of the crossed-ladder unit,
`1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)` with `ζ(2) = π²/6`. -/
theorem crossedUnit_assembly :
    (1 / 3 + π ^ 2 / 72) - (17 / 24 + π ^ 2 / 24) + (13 / 24 + 7 * π ^ 2 / 24) +
        5 / 6 * ((∫ Y in (0 : ℝ)..1, Li₂ Y / Y) + (∫ Y in (0 : ℝ)..1, log Y * log (1 - Y) / Y) +
          (∫ Y in (0 : ℝ)..1, (crossedD Y - π ^ 2 / 4) / Y) +
          2 * (∫ Y in (0 : ℝ)..1, (Li₂ Y - π ^ 2 / 6) / (Y - 1)) +
          (∫ Y in (0 : ℝ)..1, (crossedD Y + π ^ 2 / 4) / (Y - 1))) +
        5 / 12 * ((∫ Y in (0 : ℝ)..1, log Y ^ 2 / (Y - 1)) + (∫ Y in (0 : ℝ)..1, log Y / (Y - 1))) +
        11 / 6 * (∫ Y in (0 : ℝ)..1, log (1 - Y) / Y) +
        4 / 3 * (∫ Y in (0 : ℝ)..1, (log Y - log (1 - Y)) / (2 * Y - 1)) =
      1 / 6 - 5 * (π ^ 2 / 6) * log 2 + 13 / 6 * (π ^ 2 / 6) + 5 / 4 * zeta3 := by
  rw [integral_Li₂_div, integral_log_mul_log_one_sub_div,
    intervalIntegrable_and_integral_crossedD_sub_div.2,
    intervalIntegrable_and_integral_Li₂_sub_div_sub_one.2,
    intervalIntegrable_and_integral_crossedD_add_div_sub_one.2,
    intervalIntegrable_and_integral_log_sq_div_sub_one.2,
    intervalIntegrable_and_integral_log_div_sub_one.2,
    intervalIntegrable_and_integral_log_one_sub_div.2,
    intervalIntegrable_and_integral_log_sub_log_div.2]
  ring

end QED.TwoLoop.Units
