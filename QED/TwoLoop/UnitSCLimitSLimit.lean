/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitSBound
public import QED.TwoLoop.UnitLClose
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The self-energy unit S: the regulator limits of its graph half

Sections 5.3 and 5.4 of `docs/TWO-LOOP-UNITS.md`, stages (2) and (3) of the `S + C` link for the
self-energy pair (the analogue of `QED/TwoLoop/UnitLCloseLimit.lean` and
`QED/TwoLoop/UnitLLinkDominated.lean`). After the `a`-integration the graph half is `∬ G_Σ`
(`QED.TwoLoop.UnitSCLimit.integral_selfDocSum_eq_gsum`). This file proves:

* `integral_selfGSum_eq_rep`: **the decomposition**, for `0 < λ ≤ 1 ≤ Λ`,
  `∬ G_Σ = ∬ G_S(λ) + ∫₀¹ ((1-Y)/2 V_k(λ) + V_m(λ)) log M_Λ(Y) dY - Err_S(λ, Λ)`,
  with `G_S(λ) = selfR λ` the integrand of eq. (5.3) and `Err_S` (`selfErr`) the integral of the
  inner term `e₁` and of the outer Pauli–Villars pair: the large logarithm `log M_Λ` of the inner
  subdivergence appears with exactly the coefficient of the `δ₂, δ_m` counterterms at the same `Y`
  (section 2.3 of the document);
* `abs_selfErr_le`: `|Err_S(λ, Λ)| ≤ (79 + 19 log Λ)/Λ²`, **uniformly in `λ`**
  (`tendsto_selfErrBound`: the bound tends to `0`);
* `tendsto_integral_integral_selfR`: **`∬ G_S(λ) → ∫₀¹ K_S = 11/48 - π²/36` as `λ → 0⁺`**
  (dominated convergence with `|G_S| ≤ 4 + 5 ℓ`, and `∫₀¹ G_S(0; Y, x) dx = K_S(Y)`).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.TwoLoop.UnitSCLimit

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCClose QED.TwoLoop.Units

/-! ### Measurability -/

theorem measurable_selfGm_uncurry (la lb : ℝ) : Measurable (uncurry (selfGm la lb)) := by
  change Measurable fun p : ℝ × ℝ => selfGm la lb p.1 p.2
  unfold selfGm sForm selfK1 selfK2 ladderInnerMass
  fun_prop

theorem measurable_selfR_uncurry (lam : ℝ) : Measurable (uncurry (selfR lam)) := by
  change Measurable fun p : ℝ × ℝ => selfR lam p.1 p.2
  unfold selfR selfGm sForm selfK1 selfK2 ladderInnerMass
  fun_prop

theorem measurable_selfE1_uncurry (lam Lam : ℝ) : Measurable (uncurry (selfE1 lam Lam)) := by
  change Measurable fun p : ℝ × ℝ => selfE1 lam Lam p.1 p.2
  unfold selfE1 selfEll selfGm sForm selfK1 selfK2 ladderInnerMass
  fun_prop

theorem measurable_selfGm (la lb Y : ℝ) : Measurable (selfGm la lb Y) := by
  unfold selfGm sForm selfK1 selfK2 ladderInnerMass
  fun_prop

theorem measurable_selfR (lam Y : ℝ) : Measurable (selfR lam Y) := by
  unfold selfR selfGm sForm selfK1 selfK2 ladderInnerMass
  fun_prop

theorem measurable_selfE1 (lam Lam Y : ℝ) : Measurable (selfE1 lam Lam Y) := by
  unfold selfE1 selfEll selfGm sForm selfK1 selfK2 ladderInnerMass
  fun_prop

/-! ### Integrals over `x` -/

theorem selfR_x_bound {lam Y : ℝ} (hlam : lam ^ 2 ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (selfR lam Y) volume 0 1 ∧
      |∫ x in (0 : ℝ)..1, selfR lam Y x| ≤ 9 + 5 * log 2 - 5 * log Y - 5 * log (1 - Y) := by
  have hg : IntervalIntegrable (fun x => 5 * (4 / 5 + ladderEll Y x)) volume 0 1 :=
    (intervalIntegrable_add_ladderEll (4 / 5) Y).const_mul 5
  have hmeas : Measurable (selfR lam Y) := measurable_selfR lam Y
  obtain ⟨h1, h2⟩ := intervalIntegrable_of_abs_le hmeas hg
    fun x hx => by have := abs_selfR_le hlam hY hx; linarith
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [intervalIntegral.integral_const_mul, integral_add_ladderEll]
  ring

theorem selfE1_x_bound {lam Lam Y : ℝ} (hLam : 1 ≤ Lam) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (selfE1 lam Lam Y) volume 0 1 ∧
      |∫ x in (0 : ℝ)..1, selfE1 lam Lam Y x| ≤
        (10 + 9 * log Lam + 5 * log 2 - 5 * log Y - 5 * log (1 - Y)) / Lam ^ 2 := by
  have hg : IntervalIntegrable
      (fun x => 5 * ((5 + 9 * log Lam) / 5 + ladderEll Y x) / Lam ^ 2) volume 0 1 :=
    ((intervalIntegrable_add_ladderEll _ Y).const_mul 5).div_const _
  have hmeas : Measurable (selfE1 lam Lam Y) := measurable_selfE1 lam Lam Y
  obtain ⟨h1, h2⟩ := intervalIntegrable_of_abs_le hmeas hg
    fun x hx => by
      have := abs_selfE1_le (lam := lam) hLam hY hx
      refine this.trans (le_of_eq ?_)
      ring
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_add_ladderEll]
  ring

theorem selfOuter_x_bound {Λ μ Y : ℝ} (hΛ : 1 ≤ Λ) (hμ : 0 < μ) (hμΛ : μ ≤ Λ)
    (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (selfGm Λ μ Y) volume 0 1 ∧
      |∫ x in (0 : ℝ)..1, selfGm Λ μ Y x| ≤
        (12 + 5 * log Λ + 5 * log 2 - 5 * log Y - 5 * log (1 - Y)) / Λ ^ 2 := by
  have hg : IntervalIntegrable
      (fun x => 5 * ((7 + 5 * log Λ) / 5 + ladderEll Y x) / Λ ^ 2) volume 0 1 :=
    ((intervalIntegrable_add_ladderEll _ Y).const_mul 5).div_const _
  have hmeas : Measurable (selfGm Λ μ Y) := measurable_selfGm Λ μ Y
  obtain ⟨h1, h2⟩ := intervalIntegrable_of_abs_le hmeas hg
    fun x hx => by
      have := abs_selfGm_outer_le hΛ hμ hμΛ hY hx
      refine this.trans (le_of_eq ?_)
      ring
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_add_ladderEll]
  ring

/-- **The coefficient of `log M_Λ`, integrated over `x`**:
`∫₀¹ ℓ(λ; Y, x) dx = (1-Y)/2 V_k(λ) + V_m(λ)`. -/
theorem integral_selfEll {lam : ℝ} (hlam : 0 < lam) (Y : ℝ) :
    IntervalIntegrable (selfEll lam Y) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, selfEll lam Y x = (1 - Y) / 2 * selfVk lam + selfVm lam := by
  have iVk := intervalIntegrable_vkIntegrand hlam
  have iVm := intervalIntegrable_vmIntegrand hlam
  have i := (iVk.const_mul ((1 - Y) / 2)).add iVm
  refine ⟨i.congr_uIoo fun x hx => ?_, ?_⟩
  · rw [uIoo_of_le zero_le_one] at hx
    exact (selfEll_eq hlam hx).symm
  · rw [selfVk, selfVm, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (iVk.const_mul _) iVm]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ladder_ae_ne_one] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    exact selfEll_eq hlam ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

theorem selfGSum_eq (lam Lam Y x : ℝ) :
    selfGSum lam Lam Y x = selfR lam Y x - selfE1 lam Lam Y x +
      selfEll lam Y x * log (ladderInnerMass 1 Lam Y) -
        (selfGm Lam lam Y x - selfGm Lam Lam Y x) := by
  unfold selfGSum selfR selfE1
  ring

/-- **The decomposition at fixed `Y`** (`0 < λ ≤ 1 ≤ Λ`). -/
theorem integral_selfGSum_eq {lam Lam Y : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hLam : 1 ≤ Lam) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, selfGSum lam Lam Y x =
      (∫ x in (0 : ℝ)..1, selfR lam Y x) +
        ((1 - Y) / 2 * selfVk lam + selfVm lam) * log (ladderInnerMass 1 Lam Y) -
        ((∫ x in (0 : ℝ)..1, selfE1 lam Lam Y x) +
          ((∫ x in (0 : ℝ)..1, selfGm Lam lam Y x) - ∫ x in (0 : ℝ)..1, selfGm Lam Lam Y x)) := by
  have iR := (selfR_x_bound (lam := lam) (by nlinarith) hY).1
  have iE := (selfE1_x_bound (lam := lam) hLam hY).1
  have iO1 := (selfOuter_x_bound hLam hlam (by linarith) hY).1
  have iO2 := (selfOuter_x_bound hLam (by linarith) le_rfl hY).1
  obtain ⟨iL, hL⟩ := integral_selfEll hlam Y
  have e : (fun x => selfGSum lam Lam Y x) = fun x =>
      (selfR lam Y x + selfEll lam Y x * log (ladderInnerMass 1 Lam Y)) -
        (selfE1 lam Lam Y x + (selfGm Lam lam Y x - selfGm Lam Lam Y x)) := by
    funext x; rw [selfGSum_eq]; ring
  rw [e, intervalIntegral.integral_sub (iR.add (iL.mul_const _)) (iE.add (iO1.sub iO2)),
    intervalIntegral.integral_add iR (iL.mul_const _), intervalIntegral.integral_mul_const, hL,
    intervalIntegral.integral_add iE (iO1.sub iO2), intervalIntegral.integral_sub iO1 iO2]

/-! ### Integrals over `Y` -/

theorem integral_log_one_sub_unit : ∫ Y in (0 : ℝ)..1, log (1 - Y) = -1 := by
  rw [intervalIntegral.integral_comp_sub_left (fun Y => log Y) 1]
  norm_num [integral_log]

/-- `∫₀¹ (a - log Y - log(1 - Y)) dY = a + 2`. -/
theorem integral_ellY (a : ℝ) : ∫ Y in (0 : ℝ)..1, (a - log Y - log (1 - Y)) = a + 2 := by
  rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub
      intervalIntegral.intervalIntegrable_log') intervalIntegrable_log_one_sub,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
    integral_log_one_sub_unit, integral_log, intervalIntegral.integral_const]
  simp
  ring

/-- **The error term of the self-energy graph half**: the `Y`-integral of the inner term `e₁` and of
the outer Pauli–Villars pair. -/
noncomputable def selfErr (lam Lam : ℝ) : ℝ :=
  ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, selfE1 lam Lam Y x) +
    ((∫ x in (0 : ℝ)..1, selfGm Lam lam Y x) - ∫ x in (0 : ℝ)..1, selfGm Lam Lam Y x))

theorem selfErr_integrand_bound {lam Lam Y : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hLam : 1 ≤ Lam) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    |(∫ x in (0 : ℝ)..1, selfE1 lam Lam Y x) +
      ((∫ x in (0 : ℝ)..1, selfGm Lam lam Y x) - ∫ x in (0 : ℝ)..1, selfGm Lam Lam Y x)| ≤
      15 * ((34 + 19 * log Lam + 15 * log 2) / 15 - log Y - log (1 - Y)) / Lam ^ 2 := by
  have b1 := (selfE1_x_bound (lam := lam) hLam hY).2
  have b2 := (selfOuter_x_bound hLam hlam (by linarith) hY).2
  have b3 := (selfOuter_x_bound hLam (by linarith) le_rfl hY).2
  have e : 15 * ((34 + 19 * log Lam + 15 * log 2) / 15 - log Y - log (1 - Y)) / Lam ^ 2 =
      (10 + 9 * log Lam + 5 * log 2 - 5 * log Y - 5 * log (1 - Y)) / Lam ^ 2 +
      (12 + 5 * log Lam + 5 * log 2 - 5 * log Y - 5 * log (1 - Y)) / Lam ^ 2 +
      (12 + 5 * log Lam + 5 * log 2 - 5 * log Y - 5 * log (1 - Y)) / Lam ^ 2 := by ring
  rw [e, show ∀ a b c : ℝ, a + (b - c) = a + b + -c from fun a b c => by ring]
  refine (abs_add_three _ _ _).trans ?_
  rw [abs_neg]
  linarith

theorem measurable_integral_selfErr (lam Lam : ℝ) :
    Measurable fun Y => (∫ x in (0 : ℝ)..1, selfE1 lam Lam Y x) +
      ((∫ x in (0 : ℝ)..1, selfGm Lam lam Y x) - ∫ x in (0 : ℝ)..1, selfGm Lam Lam Y x) :=
  (measurable_intervalIntegral_of_uncurry (measurable_selfE1_uncurry lam Lam)).add
    ((measurable_intervalIntegral_of_uncurry (measurable_selfGm_uncurry Lam lam)).sub
      (measurable_intervalIntegral_of_uncurry (measurable_selfGm_uncurry Lam Lam)))

theorem selfErr_integrable_and_le {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hLam : 1 ≤ Lam) :
    IntervalIntegrable (fun Y => (∫ x in (0 : ℝ)..1, selfE1 lam Lam Y x) +
      ((∫ x in (0 : ℝ)..1, selfGm Lam lam Y x) - ∫ x in (0 : ℝ)..1, selfGm Lam Lam Y x))
        volume 0 1 ∧
      |selfErr lam Lam| ≤ (79 + 19 * log Lam) / Lam ^ 2 := by
  have hg : IntervalIntegrable
      (fun Y => 15 * ((34 + 19 * log Lam + 15 * log 2) / 15 - log Y - log (1 - Y)) / Lam ^ 2)
      volume 0 1 := ((intervalIntegrable_ellY _).const_mul 15).div_const _
  obtain ⟨h1, h2⟩ := intervalIntegrable_of_abs_le (measurable_integral_selfErr lam Lam) hg
    fun Y hY => selfErr_integrand_bound hlam hlam1 hLam hY
  refine ⟨h1, h2.trans ?_⟩
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_ellY]
  have hl2 := log_two_le_one
  have hL : 0 < Lam ^ 2 := by positivity
  exact (div_le_div_iff_of_pos_right hL).mpr (by linarith)

theorem tendsto_selfErrBound :
    Tendsto (fun Lam : ℝ => (79 + 19 * log Lam) / Lam ^ 2) atTop (𝓝 0) := by
  have := (tendsto_const_div_sq 79).add (tendsto_log_div_sq.const_mul 19)
  simp only [add_zero, mul_zero] at this
  refine this.congr fun Lam => ?_
  ring

theorem intervalIntegrable_selfLogTerm {lam Lam : ℝ} (hLam : 0 < Lam) :
    IntervalIntegrable (fun Y => ((1 - Y) / 2 * selfVk lam + selfVm lam) *
      log (ladderInnerMass 1 Lam Y)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  exact (by fun_prop : ContinuousOn (fun Y : ℝ => (1 - Y) / 2 * selfVk lam + selfVm lam)
    (Icc 0 1)).mul ((by unfold ladderInnerMass; fun_prop :
      ContinuousOn (fun Y => ladderInnerMass 1 Lam Y) (Icc 0 1)).log
      fun Y hY => (ladderInnerMass_pos one_pos hLam hY).ne')

theorem intervalIntegrable_integral_selfR {lam : ℝ} (hlam : lam ^ 2 ≤ 1) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, selfR lam Y x) volume 0 1 ∧
      ∀ Y ∈ Ioo (0 : ℝ) 1, ‖∫ x in (0 : ℝ)..1, selfR lam Y x‖ ≤
        5 * ((9 + 5 * log 2) / 5 - log Y - log (1 - Y)) := by
  have hg : IntervalIntegrable (fun Y => 5 * ((9 + 5 * log 2) / 5 - log Y - log (1 - Y)))
      volume 0 1 := (intervalIntegrable_ellY _).const_mul 5
  have hb : ∀ Y ∈ Ioo (0 : ℝ) 1, |∫ x in (0 : ℝ)..1, selfR lam Y x| ≤
      5 * ((9 + 5 * log 2) / 5 - log Y - log (1 - Y)) := fun Y hY => by
    have := (selfR_x_bound hlam hY).2
    linarith
  exact ⟨(intervalIntegrable_of_abs_le
    (measurable_intervalIntegral_of_uncurry (measurable_selfR_uncurry lam)) hg hb).1,
    fun Y hY => by rw [Real.norm_eq_abs]; exact hb Y hY⟩

/-- **The self-energy graph half, decomposed** (`0 < λ ≤ 1 ≤ Λ`):
`∬ G_Σ = ∬ G_S(λ) + ∫₀¹ ((1-Y)/2 V_k(λ) + V_m(λ)) log M_Λ(Y) dY - Err_S(λ, Λ)`. -/
theorem integral_selfGSum_eq_rep {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hLam : 1 ≤ Lam) :
    ∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, selfGSum lam Lam Y x =
      (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfR lam Y x) +
        (∫ Y in (0 : ℝ)..1, ((1 - Y) / 2 * selfVk lam + selfVm lam) *
          log (ladderInnerMass 1 Lam Y)) - selfErr lam Lam := by
  have iR := (intervalIntegrable_integral_selfR (lam := lam) (by nlinarith)).1
  have iL := intervalIntegrable_selfLogTerm (lam := lam) (by linarith : (0 : ℝ) < Lam)
  have iE := (selfErr_integrable_and_le hlam hlam1 hLam).1
  simp only [setIntegral_Ioo_eq_intervalIntegral]
  rw [selfErr, ← intervalIntegral.integral_add iR iL, ← intervalIntegral.integral_sub (iR.add iL) iE]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ladder_ae_ne_one] with Y hY1 hY
  rw [uIoc_of_le zero_le_one] at hY
  rw [integral_selfGSum_eq hlam hlam1 hLam ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩]

/-! ### The limit `λ → 0` -/

theorem continuousAt_selfR {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (fun lam => selfR lam Y x) 0 := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have h1Y : 0 < 1 - Y := by linarith
  have h1x : 0 < 1 - x := by linarith
  unfold selfR selfGm sForm selfK1 selfK2 ladderInnerMass
  fun_prop (disch := (apply ne_of_gt; simp only [one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero]; positivity))

theorem self_eventually_mem : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Ioo (0 : ℝ) 1 :=
  Ioo_mem_nhdsGT (by norm_num)

/-- `∫₀¹ G_S(λ; Y, x) dx → K_S(Y)` as `λ → 0⁺`, for `0 < Y < 1`. -/
theorem tendsto_integral_selfR {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun lam => ∫ x in (0 : ℝ)..1, selfR lam Y x) (𝓝[>] 0) (𝓝 (selfEnergyKernel Y)) := by
  rw [← integral_selfR_zero hY]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => 5 * (4 / 5 + ladderEll Y x))
    (Eventually.of_forall fun lam =>
      (measurable_selfR lam Y).aestronglyMeasurable)
    ?_ ((intervalIntegrable_add_ladderEll (4 / 5) Y).const_mul 5) ?_
  · filter_upwards [self_eventually_mem] with lam hlam
    filter_upwards [ladder_ae_ne_one] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    have hl : lam ^ 2 ≤ 1 := by nlinarith [hlam.1, hlam.2]
    have := abs_selfR_le hl hY ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    rw [Real.norm_eq_abs]
    linarith
  · filter_upwards [ladder_ae_ne_one] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    exact (continuousAt_selfR hY ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩).tendsto.mono_left
      nhdsWithin_le_nhds

/-- **`∬ G_S(λ) → ∫₀¹ K_S = 11/48 - π²/36` as `λ → 0⁺`**: the two-loop part of the self-energy
unit, `b_S/2` of eq. (5.5). -/
theorem tendsto_integral_integral_selfR :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfR lam Y x) (𝓝[>] 0)
      (𝓝 (11 / 48 - π ^ 2 / 36)) := by
  rw [← integral_selfEnergyKernel]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => 5 * ((9 + 5 * log 2) / 5 - log Y - log (1 - Y)))
    (Eventually.of_forall fun lam => (measurable_intervalIntegral_of_uncurry
      (measurable_selfR_uncurry lam)).aestronglyMeasurable)
    ?_ ((intervalIntegrable_ellY _).const_mul 5) ?_
  · filter_upwards [self_eventually_mem] with lam hlam
    filter_upwards [ladder_ae_ne_one] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hl : lam ^ 2 ≤ 1 := by nlinarith [hlam.1, hlam.2]
    exact (intervalIntegrable_integral_selfR hl).2 Y ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
  · filter_upwards [ladder_ae_ne_one] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact tendsto_integral_selfR ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩

end QED.TwoLoop.UnitSCLimit

end
