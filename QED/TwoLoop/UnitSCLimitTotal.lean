/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitSLimit
public import QED.TwoLoop.UnitSCLimitAssembly
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The unit `S + C`: the joint limit, given the corner graph half

Sections 5.4, 6.4 and 7 of `docs/TWO-LOOP-UNITS.md`. With the self-energy graph half decomposed
(`QED.TwoLoop.UnitSCLimit.integral_selfGSum_eq_rep`), the function
`SC(λ, Λ) = 2 ∬ G_Σ^S + 2 ∫_{y₃,y₄} ∫ G_Σ^C - Σ(λ, Λ)(V_m(λ) - V_m(Λ))` (`scTotal`) is, for
`0 < λ < 1 ≤ Λ` (`scTotal_eq`),

`SC = 2 ∬ G_S(λ) - 2 Err_S + C(λ, Λ) - F₂⁽²⁾(λ) ∫₀¹ (1-2Y) log M_Λ + V_m(λ) ∫₀¹ (1+Y) log M_λ
  + Σ(λ, Λ) V_m(Λ)`,

where `C(λ, Λ) = 2 ∫_{y₃,y₄} ∫ G_Σ^C - F₂⁽²⁾(λ) ∫₀¹ Y log M_Λ(Y) dY` (`cornerPart`) is the corner
graph half with its inner subdivergence `∫ ℓ_C log M_Λ = (Y/2) F₂⁽²⁾ log M_Λ` removed. The large
logarithms of the self-energy graph, of the corner graph and of the mass counterterm combine, by
`V_k + V_m + F₂⁽²⁾ = 0`, into `-F₂⁽²⁾(λ) ∫ (1-2Y) log M_Λ`, in which `log Λ²` has coefficient
`∫₀¹ (1-2Y) dY = 0`. This file proves:

* `tendsto_integral_one_sub_two_mul_log`: `∫₀¹ (1-2Y) log M_Λ(Y) dY → 1/2` as `Λ → ∞`;
* `tendsto_integral_one_add_mul_log`: `∫₀¹ (1+Y) log M_λ(Y) dY → -5/2` as `λ → 0⁺`;
* `abs_scMassCt_le`, `abs_selfVm_le`: `|Σ(λ, Λ)| ≤ 4 + 4 log Λ`, `|V_m(Λ)| ≤ 3/(2Λ²)`;
* `scTotalLimit_of_cornerPart`: **`SCTotalLimit` follows from the joint limit of the corner part**
  `C(λ, Λ) → -31/24 + 2 ζ(2) log 2 + ζ(2)/3 - ζ(3)/2` (`CornerPartLimit`, `= 2 ∫∫∫ G_C(0)`, i.e.
  `b_C + 3/2` of eq. (6.5)); the self-energy part tends to `2 ∫₀¹ K_S = 11/24 - ζ(2)/3` and the
  counterterm constants give `-1/4 - 5/4 = -3/2`;
* `scUnitLimitOne_of_sCtHalf_cornerPart`: **the `S + C` link at `m = 1`**, given the `δ₂, δ_m` half
  (`SCtHalfFormula`) and `CornerPartLimit`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.TwoLoop.UnitSCLimit

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCClose QED.TwoLoop.Units QED.TwoLoop.UnitXGraph
open QED.TwoLoop.HeadlineAssembly

/-! ### Integrals of `log M_μ` -/

theorem continuousOn_logMass {μ : ℝ} (hμ : 0 < μ) :
    ContinuousOn (fun Y => log (ladderInnerMass 1 μ Y)) (Icc 0 1) :=
  (by unfold ladderInnerMass; fun_prop :
    ContinuousOn (fun Y => ladderInnerMass 1 μ Y) (Icc 0 1)).log
    fun Y hY => (ladderInnerMass_pos one_pos hμ hY).ne'

theorem intervalIntegrable_mul_logMass {μ : ℝ} (hμ : 0 < μ) {p : ℝ → ℝ} (hp : Continuous p) :
    IntervalIntegrable (fun Y => p Y * log (ladderInnerMass 1 μ Y)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  exact hp.continuousOn.mul (continuousOn_logMass hμ)

theorem integral_linear_mul_logMass {μ : ℝ} (hμ : 0 < μ) (a b : ℝ) :
    ∫ Y in (0 : ℝ)..1, (a + b * Y) * log (ladderInnerMass 1 μ Y) =
      a * (∫ Y in (0 : ℝ)..1, log (ladderInnerMass 1 μ Y)) +
        b * ∫ Y in (0 : ℝ)..1, Y * log (ladderInnerMass 1 μ Y) := by
  have i1 := intervalIntegrable_mul_logMass hμ (p := fun _ => 1) continuous_const
  have i2 := intervalIntegrable_mul_logMass hμ (p := fun Y => Y) continuous_id
  simp only [one_mul] at i1
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (i1.const_mul a) (i2.const_mul b)]
  congr 1
  funext Y
  ring

theorem scMassCt_eq {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 < Lam) :
    scMassCt lam Lam = (∫ Y in (0 : ℝ)..1, (1 + 1 * Y) * log (ladderInnerMass 1 Lam Y)) -
      ∫ Y in (0 : ℝ)..1, (1 + 1 * Y) * log (ladderInnerMass 1 lam Y) := by
  rw [scMassCt, ← intervalIntegral.integral_sub
    (intervalIntegrable_mul_logMass hLam (by fun_prop))
    (intervalIntegrable_mul_logMass hlam (by fun_prop))]
  refine intervalIntegral.integral_congr fun Y hY => ?_
  rw [uIcc_of_le zero_le_one] at hY
  rw [log_div (ladderInnerMass_pos one_pos hLam hY).ne' (ladderInnerMass_pos one_pos hlam hY).ne']
  ring

/-! ### `∫₀¹ (1 - 2Y) log M_Λ → 1/2` -/

theorem integral_one_sub_two_mul_log_one_sub :
    ∫ Y in (0 : ℝ)..1, (1 - 2 * Y) * log (1 - Y) = 1 / 2 := by
  have hF : ∀ Y ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun Y => Y * ((1 - Y) * log (1 - Y)) + Y ^ 2 / 2) ((1 - 2 * Y) * log (1 - Y)) Y := by
    intro Y hY
    have h1 : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
    have hl : HasDerivAt (fun Y => log (1 - Y)) (-1 / (1 - Y)) Y := by
      have := ((hasDerivAt_const Y (1 : ℝ)).sub (hasDerivAt_id Y)).log h1
      simpa using this
    have h := ((hasDerivAt_id Y).mul (((hasDerivAt_const Y (1 : ℝ)).sub (hasDerivAt_id Y)).mul
      hl)).add ((hasDerivAt_pow 2 Y).div_const 2)
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, id_eq]
    norm_num
    field_simp
    ring
  have hc : ContinuousOn (fun Y : ℝ => Y * ((1 - Y) * log (1 - Y)) + Y ^ 2 / 2) (Icc 0 1) := by
    have : Continuous fun Y : ℝ => (1 - Y) * log (1 - Y) :=
      continuous_mul_log.comp (continuous_const.sub continuous_id)
    exact ((continuous_id.mul this).add (by fun_prop)).continuousOn
  have hi : IntervalIntegrable (fun Y : ℝ => (1 - 2 * Y) * log (1 - Y)) volume 0 1 :=
    intervalIntegrable_log_one_sub.continuousOn_mul (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hF hi]
  norm_num

theorem integral_one_sub_two_mul (c : ℝ) : ∫ Y in (0 : ℝ)..1, (1 - 2 * Y) * c = 0 := by
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_id.const_mul 2), intervalIntegral.integral_const_mul,
    integral_id]
  norm_num

theorem log_mass_eq {Lam Y : ℝ} (hLam : 0 < Lam) (hY : Y ∈ Icc (0 : ℝ) 1) :
    log (ladderInnerMass 1 Lam Y) = 2 * log Lam + log (1 - Y + Y ^ 2 / Lam ^ 2) := by
  have hp := ladderInnerMass_pos one_pos hLam hY
  have e : ladderInnerMass 1 Lam Y = Lam ^ 2 * (1 - Y + Y ^ 2 / Lam ^ 2) := by
    unfold ladderInnerMass; field_simp; ring
  have hq : 0 < 1 - Y + Y ^ 2 / Lam ^ 2 := by
    rw [e] at hp; exact pos_of_mul_pos_right hp (by positivity)
  rw [e, log_mul (by positivity) hq.ne', log_pow]
  push_cast
  ring

/-- **`∫₀¹ (1 - 2Y) log M_Λ(Y) dY → 1/2` as `Λ → ∞`**: the coefficient of `log Λ²` is
`∫₀¹ (1 - 2Y) dY = 0`. -/
theorem tendsto_integral_one_sub_two_mul_log :
    Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1, (1 - 2 * Y) * log (ladderInnerMass 1 Lam Y)) atTop
      (𝓝 (1 / 2)) := by
  rw [← integral_one_sub_two_mul_log_one_sub]
  have hT : Tendsto (fun Lam => ∫ Y in (0 : ℝ)..1, (1 - 2 * Y) * log (1 - Y + Y ^ 2 / Lam ^ 2))
      atTop (𝓝 (∫ Y in (0 : ℝ)..1, (1 - 2 * Y) * log (1 - Y))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun Y => -log (1 - Y)) (Eventually.of_forall fun Lam => by
        exact (by fun_prop : Measurable fun Y : ℝ =>
          (1 - 2 * Y) * log (1 - Y + Y ^ 2 / Lam ^ 2)).aestronglyMeasurable) ?_
      intervalIntegrable_log_one_sub.neg ?_
    · filter_upwards [eventually_ge_atTop 1] with Lam hLam
      filter_upwards [ladder_ae_ne_one] with Y hY1 hY
      rw [uIoc_of_le zero_le_one] at hY
      have hY' : Y < 1 := lt_of_le_of_ne hY.2 hY1
      have hL2 : 1 ≤ Lam ^ 2 := by nlinarith
      have hq : Y ^ 2 / Lam ^ 2 ≤ Y := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [hY.1]
      have hq0 : 0 ≤ Y ^ 2 / Lam ^ 2 := by positivity
      have hlo : log (1 - Y) ≤ log (1 - Y + Y ^ 2 / Lam ^ 2) :=
        log_le_log (by linarith) (by linarith)
      have hhi : log (1 - Y + Y ^ 2 / Lam ^ 2) ≤ 0 := log_nonpos (by linarith) (by linarith)
      have h12 : |1 - 2 * Y| ≤ 1 := abs_le.mpr ⟨by linarith [hY'], by linarith [hY.1]⟩
      rw [Real.norm_eq_abs, abs_mul]
      calc |1 - 2 * Y| * |log (1 - Y + Y ^ 2 / Lam ^ 2)| ≤ 1 * -log (1 - Y) := by
            refine mul_le_mul h12 ?_ (abs_nonneg _) zero_le_one
            rw [abs_of_nonpos hhi]; linarith
        _ = -log (1 - Y) := one_mul _
    · filter_upwards [ladder_ae_ne_one] with Y hY1 hY
      rw [uIoc_of_le zero_le_one] at hY
      have hY' : Y < 1 := lt_of_le_of_ne hY.2 hY1
      have h0 : Tendsto (fun Lam : ℝ => Y ^ 2 / Lam ^ 2) atTop (𝓝 0) := tendsto_const_div_sq _
      have h1 : Tendsto (fun Lam : ℝ => 1 - Y + Y ^ 2 / Lam ^ 2) atTop (𝓝 (1 - Y)) := by
        simpa using (tendsto_const_nhds (x := 1 - Y)).add h0
      exact ((continuousAt_log (by linarith)).tendsto.comp h1).const_mul _
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Lam hLam
  have hi1 : IntervalIntegrable (fun Y : ℝ => (1 - 2 * Y) * (2 * log Lam)) volume 0 1 :=
    (by fun_prop : Continuous fun Y : ℝ => (1 - 2 * Y) * (2 * log Lam)).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun Y : ℝ => (1 - 2 * Y) * log (1 - Y + Y ^ 2 / Lam ^ 2))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.log (by fun_prop) fun Y hY => ?_)
    have : 0 ≤ Y ^ 2 / Lam ^ 2 := by positivity
    rcases eq_or_lt_of_le hY.2 with h | h
    · subst h; positivity
    · linarith
  have e : ∫ Y in (0 : ℝ)..1, (1 - 2 * Y) * log (ladderInnerMass 1 Lam Y) =
      ∫ Y in (0 : ℝ)..1, ((1 - 2 * Y) * (2 * log Lam) +
        (1 - 2 * Y) * log (1 - Y + Y ^ 2 / Lam ^ 2)) := by
    refine intervalIntegral.integral_congr fun Y hY => ?_
    rw [uIcc_of_le zero_le_one] at hY
    rw [log_mass_eq hLam hY]
    ring
  rw [e, intervalIntegral.integral_add hi1 hi2, integral_one_sub_two_mul, zero_add]

/-! ### `∫₀¹ (1 + Y) log M_λ → -5/2` -/

theorem integral_one_add_mul_log_sq :
    ∫ Y in (0 : ℝ)..1, (1 + 1 * Y) * log (ladderInnerMass 1 0 Y) = -5 / 2 := by
  have hF : ∀ Y ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun Y => 2 * ((1 + Y / 2) * (Y * log Y) - Y - Y ^ 2 / 4))
      ((1 + 1 * Y) * log (ladderInnerMass 1 0 Y)) Y := by
    intro Y hY
    have hY0 : Y ≠ 0 := hY.1.ne'
    have hM : ladderInnerMass 1 0 Y = Y ^ 2 := by unfold ladderInnerMass; ring
    rw [hM, log_pow]
    have h := ((((hasDerivAt_const Y (1 : ℝ)).add ((hasDerivAt_id Y).div_const 2)).mul
      ((hasDerivAt_id Y).mul (hasDerivAt_log hY0))).sub (hasDerivAt_id Y)).sub
      ((hasDerivAt_pow 2 Y).div_const 4) |>.const_mul 2
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.add_apply, id_eq]
    norm_num
    field_simp
    ring
  have hc : ContinuousOn (fun Y : ℝ => 2 * ((1 + Y / 2) * (Y * log Y) - Y - Y ^ 2 / 4))
      (Icc 0 1) :=
    (continuous_const.mul ((((continuous_const.add (continuous_id.div_const 2)).mul
      continuous_mul_log).sub continuous_id).sub (by fun_prop))).continuousOn
  have hi : IntervalIntegrable (fun Y : ℝ => (1 + 1 * Y) * log (ladderInnerMass 1 0 Y))
      volume 0 1 := by
    have e : (fun Y : ℝ => (1 + 1 * Y) * log (ladderInnerMass 1 0 Y)) =
        fun Y => log Y * (2 * (1 + Y)) := by
      funext Y
      have hM : ladderInnerMass 1 0 Y = Y ^ 2 := by unfold ladderInnerMass; ring
      rw [hM, log_pow]; push_cast; ring
    rw [e]
    exact intervalIntegral.intervalIntegrable_log'.mul_continuousOn (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hF hi]
  norm_num

/-- **`∫₀¹ (1 + Y) log M_λ(Y) dY → -5/2` as `λ → 0⁺`.** -/
theorem tendsto_integral_one_add_mul_log :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, (1 + 1 * Y) * log (ladderInnerMass 1 lam Y))
      (𝓝[>] 0) (𝓝 (-5 / 2)) := by
  rw [← integral_one_add_mul_log_sq]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => 2 * (-(2 * log Y))) (Eventually.of_forall fun lam => by
      exact (by unfold ladderInnerMass; fun_prop : Measurable fun Y : ℝ =>
        (1 + 1 * Y) * log (ladderInnerMass 1 lam Y)).aestronglyMeasurable) ?_
    ((intervalIntegral.intervalIntegrable_log'.const_mul 2).neg.const_mul 2) ?_
  · filter_upwards [self_eventually_mem] with lam hlam
    filter_upwards [ladder_ae_ne_one] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hY' : Y ∈ Ioo (0 : ℝ) 1 := ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩
    have hlo := selfM_ge (μ := lam) hY'
    have hhi : ladderInnerMass 1 lam Y ≤ 1 := by
      have : lam ^ 2 ≤ 1 := by nlinarith [hlam.1, hlam.2]
      have : (1 - Y) * lam ^ 2 ≤ 1 - Y := by nlinarith [hY'.2]
      have : Y ^ 2 ≤ Y := by nlinarith [hY'.1, hY'.2]
      unfold ladderInnerMass; simp only [one_pow, mul_one]; linarith
    have hY2 : 0 < Y ^ 2 := by have := hY.1; positivity
    have l1 : 2 * log Y ≤ log (ladderInnerMass 1 lam Y) := by
      have e : log (Y ^ 2) = 2 * log Y := by rw [log_pow]; norm_num
      rw [← e]; exact log_le_log hY2 hlo
    have l2 : log (ladderInnerMass 1 lam Y) ≤ 0 := log_nonpos (hY2.le.trans hlo) hhi
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith [hY.1] : (0 : ℝ) < 1 + 1 * Y),
      abs_of_nonpos l2]
    have hlY : log Y ≤ 0 := log_nonpos hY.1.le hY.2
    nlinarith [hY.2]
  · filter_upwards [ladder_ae_ne_one] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    have hY2 : 0 < ladderInnerMass 1 0 Y := by
      rw [show ladderInnerMass 1 0 Y = Y ^ 2 by unfold ladderInnerMass; ring]
      have := hY.1; positivity
    have hc : ContinuousAt (fun lam => ladderInnerMass 1 lam Y) 0 := by
      unfold ladderInnerMass; fun_prop
    exact ((hc.log hY2.ne').tendsto.mono_left nhdsWithin_le_nhds).const_mul _

/-! ### The error bounds -/

theorem abs_scMassCt_le {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam) :
    |scMassCt lam Lam| ≤ 4 + 4 * log Lam := by
  have hg : IntervalIntegrable (fun x => 4 * log Lam - 4 * log x) volume 0 1 :=
    intervalIntegrable_const.sub (intervalIntegral.intervalIntegrable_log'.const_mul 4)
  have hm : Measurable fun x => (1 + x) * log (ladderInnerMass 1 Lam x / ladderInnerMass 1 lam x) := by
    unfold ladderInnerMass; fun_prop
  obtain ⟨-, h2⟩ := intervalIntegrable_of_abs_le hm hg fun x hx => by
    have hlo1 := selfM_ge (μ := Lam) hx
    have hlo2 := selfM_ge (μ := lam) hx
    have hx2 : 0 < x ^ 2 := by have := hx.1; positivity
    have hL2 : 1 ≤ Lam ^ 2 := by nlinarith
    have hhi1 : ladderInnerMass 1 Lam x ≤ Lam ^ 2 := by
      unfold ladderInnerMass; nlinarith [hx.1, hx.2]
    have hhi2 : ladderInnerMass 1 lam x ≤ 1 := by
      have : lam ^ 2 ≤ 1 := by nlinarith
      have : (1 - x) * lam ^ 2 ≤ 1 - x := by nlinarith [hx.2]
      have : x ^ 2 ≤ x := by nlinarith [hx.1, hx.2]
      unfold ladderInnerMass; simp only [one_pow, mul_one]; linarith
    have e2 : log (x ^ 2) = 2 * log x := by rw [log_pow]; norm_num
    have eL : log (Lam ^ 2) = 2 * log Lam := by rw [log_pow]; norm_num
    have a1 : 2 * log x ≤ log (ladderInnerMass 1 Lam x) := e2 ▸ log_le_log hx2 hlo1
    have a2 : log (ladderInnerMass 1 Lam x) ≤ 2 * log Lam := eL ▸ log_le_log (hx2.trans_le hlo1) hhi1
    have a3 : 2 * log x ≤ log (ladderInnerMass 1 lam x) := e2 ▸ log_le_log hx2 hlo2
    have a4 : log (ladderInnerMass 1 lam x) ≤ 0 := log_nonpos (hx2.le.trans hlo2) hhi2
    have hlx : log x ≤ 0 := log_nonpos hx.1.le hx.2.le
    have hlL : 0 ≤ log Lam := log_nonneg hLam
    rw [log_div (hx2.trans_le hlo1).ne' (hx2.trans_le hlo2).ne', abs_mul,
      abs_of_pos (by linarith [hx.1] : (0 : ℝ) < 1 + x)]
    have hb : |log (ladderInnerMass 1 Lam x) - log (ladderInnerMass 1 lam x)| ≤
        2 * log Lam - 2 * log x := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2x : 1 + x ≤ 2 := by linarith [hx.2]
    nlinarith [abs_nonneg (log (ladderInnerMass 1 Lam x) - log (ladderInnerMass 1 lam x))]
  refine h2.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_log'.const_mul 4), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_log]
  simp
  ring

theorem abs_selfVm_le {Lam : ℝ} (hLam : 1 ≤ Lam) : |selfVm Lam| ≤ 3 / 2 / Lam ^ 2 := by
  have hL : 0 < Lam ^ 2 := by positivity
  have hm : Measurable (vmIntegrand Lam) := by unfold vmIntegrand ladderInnerMass; fun_prop
  obtain ⟨-, h2⟩ := intervalIntegrable_of_abs_le hm
    (intervalIntegrable_const (c := 3 / 2 / Lam ^ 2)) fun x hx => by
    obtain ⟨hx0, hx1⟩ := hx
    have hm0 : 0 < ladderInnerMass 1 Lam x := ladderInnerMass_pos one_pos (by linarith)
      ⟨hx0.le, hx1.le⟩
    have hmx : (1 - x) * Lam ^ 2 ≤ ladderInnerMass 1 Lam x := by
      unfold ladderInnerMass; nlinarith [sq_nonneg x]
    have hnum : 2 * x ^ 2 + 3 * Lam ^ 2 * (1 - x) ≤ 3 * ladderInnerMass 1 Lam x := by
      unfold ladderInnerMass; nlinarith [sq_nonneg x]
    have hnn : 0 ≤ vmIntegrand Lam x := by
      unfold vmIntegrand
      have : 0 ≤ x ^ 2 * (1 - x) * (2 * x ^ 2 + 3 * Lam ^ 2 * (1 - x)) := by
        have : 0 ≤ 1 - x := by linarith
        positivity
      positivity
    rw [abs_of_nonneg hnn]
    unfold vmIntegrand
    rw [div_le_div_iff₀ (by positivity) hL]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have h1 : x ^ 2 * (1 - x) * (2 * x ^ 2 + 3 * Lam ^ 2 * (1 - x)) * Lam ^ 2 ≤
        x ^ 2 * (1 - x) * (3 * ladderInnerMass 1 Lam x) * Lam ^ 2 := by
      have : 0 ≤ x ^ 2 * (1 - x) := mul_nonneg (by positivity) (by linarith)
      gcongr
    have h2 : x ^ 2 * (1 - x) * Lam ^ 2 ≤ ladderInnerMass 1 Lam x := by nlinarith
    nlinarith
  refine (show |selfVm Lam| ≤ ∫ x in (0 : ℝ)..1, 3 / 2 / Lam ^ 2 from h2).trans (le_of_eq ?_)
  simp

/-! ### The joint limit -/

/-- **The corner part**: the corner graph half with its inner subdivergence removed,
`C(λ, Λ) = 2 ∫_{y₃,y₄} ∫₀¹ G_Σ^C - F₂⁽²⁾(λ) ∫₀¹ Y log M_Λ(Y) dY`. -/
noncomputable def cornerPart (lam Lam : ℝ) : ℝ :=
  2 * (∫ p in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGSum lam Lam p.1 p.2 x) -
    oneLoopF2 1 lam * ∫ Y in (0 : ℝ)..1, Y * log (ladderInnerMass 1 Lam Y)

/-- **The remaining statement for the corner graph** (stages 2–4 for `C`): the corner part tends to
`2 ∫∫∫ G_C(0) = 2 ∫₀¹ K_C = -31/24 + 2 ζ(2) log 2 + ζ(2)/3 - ζ(3)/2` jointly. -/
def CornerPartLimit : Prop :=
  Tendsto (fun p : ℝ × ℝ => cornerPart p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
    (𝓝 (-(31 / 24) + 2 * (π ^ 2 / 6) * Real.log 2 + π ^ 2 / 6 / 3 - QED.Polylog.zeta3 / 2))

/-- **`SC(λ, Λ)` decomposed** (`0 < λ ≤ 1 ≤ Λ`). -/
theorem scTotal_eq {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam) :
    scTotal lam Lam =
      2 * (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfR lam Y x) - 2 * selfErr lam Lam +
        cornerPart lam Lam -
        oneLoopF2 1 lam * (∫ Y in (0 : ℝ)..1, (1 - 2 * Y) * log (ladderInnerMass 1 Lam Y)) +
        selfVm lam * (∫ Y in (0 : ℝ)..1, (1 + 1 * Y) * log (ladderInnerMass 1 lam Y)) +
        scMassCt lam Lam * selfVm Lam := by
  have hL0 : 0 < Lam := by linarith
  have hIR := selfVk_add_selfVm_add_oneLoopF2 hlam
  have e1 : ∫ Y in (0 : ℝ)..1, ((1 - Y) / 2 * selfVk lam + selfVm lam) *
      log (ladderInnerMass 1 Lam Y) = ∫ Y in (0 : ℝ)..1,
        ((selfVk lam / 2 + selfVm lam) + (-(selfVk lam / 2)) * Y) *
          log (ladderInnerMass 1 Lam Y) := by
    congr 1; funext Y; ring
  have e2 : ∫ Y in (0 : ℝ)..1, (1 - 2 * Y) * log (ladderInnerMass 1 Lam Y) =
      ∫ Y in (0 : ℝ)..1, (1 + (-2) * Y) * log (ladderInnerMass 1 Lam Y) := by
    congr 1; funext Y; ring
  rw [scTotal, integral_selfGSum_eq_rep hlam hlam1 hLam, cornerPart, e2, e1,
    integral_linear_mul_logMass hL0, integral_linear_mul_logMass hL0,
    scMassCt_eq hlam hL0, integral_linear_mul_logMass hL0,
    show selfVk lam = -selfVm lam - oneLoopF2 1 lam by linarith]
  ring

/-- **`SCTotalLimit` from the corner part**: the self-energy part, the counterterm constants and the
error terms are proved; only the corner graph half remains. -/
theorem scTotalLimit_of_cornerPart (hC : CornerPartLimit) : SCTotalLimit := by
  set F := 𝓝[>] (0 : ℝ) ×ˢ (atTop : Filter ℝ)
  have hev : ∀ᶠ p : ℝ × ℝ in F, p.1 ∈ Ioo (0 : ℝ) 1 ∧ 1 ≤ p.2 :=
    (self_eventually_mem.prod_inl _).and ((eventually_ge_atTop (1 : ℝ)).prod_inr _)
  have hS : Tendsto (fun p : ℝ × ℝ => 2 * ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, selfR p.1 Y x) F
      (𝓝 (2 * (11 / 48 - π ^ 2 / 36))) :=
    (tendsto_integral_integral_selfR.comp tendsto_fst).const_mul 2
  have hE : Tendsto (fun p : ℝ × ℝ => 2 * selfErr p.1 p.2) F (𝓝 0) := by
    have hb : Tendsto (fun p : ℝ × ℝ => 2 * ((79 + 19 * log p.2) / p.2 ^ 2)) F (𝓝 0) := by
      simpa using (tendsto_selfErrBound.comp tendsto_snd).const_mul 2
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hev] with p hp
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left
      (selfErr_integrable_and_le hp.1.1 hp.1.2.le hp.2).2 zero_le_two
  have hF2 : Tendsto (fun p : ℝ × ℝ => oneLoopF2 1 p.1 *
      ∫ Y in (0 : ℝ)..1, (1 - 2 * Y) * log (ladderInnerMass 1 p.2 Y)) F (𝓝 (1 / 2 * (1 / 2))) :=
    (tendsto_oneLoopF2_one.comp tendsto_fst).mul
      (tendsto_integral_one_sub_two_mul_log.comp tendsto_snd)
  have hVm : Tendsto (fun p : ℝ × ℝ => selfVm p.1 *
      ∫ Y in (0 : ℝ)..1, (1 + 1 * Y) * log (ladderInnerMass 1 p.1 Y)) F (𝓝 (1 / 2 * (-5 / 2))) :=
    (tendsto_selfVm.comp tendsto_fst).mul (tendsto_integral_one_add_mul_log.comp tendsto_fst)
  have hM : Tendsto (fun p : ℝ × ℝ => scMassCt p.1 p.2 * selfVm p.2) F (𝓝 0) := by
    have hb : Tendsto (fun p : ℝ × ℝ => (4 + 4 * log p.2) * (3 / 2 / p.2 ^ 2)) F (𝓝 0) := by
      have h1 : Tendsto (fun Lam : ℝ => (4 + 4 * log Lam) * (3 / 2 / Lam ^ 2)) atTop (𝓝 0) := by
        have := ((tendsto_const_div_sq 6).add (tendsto_log_div_sq.const_mul 6))
        simp only [add_zero, mul_zero] at this
        refine this.congr fun Lam => ?_
        ring
      exact h1.comp tendsto_snd
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hev] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_scMassCt_le hp.1.1 hp.1.2.le hp.2) (abs_selfVm_le hp.2) (abs_nonneg _)
      (by have := log_nonneg hp.2; linarith)
  have hsum := ((((hS.sub hE).add hC).sub hF2).add hVm).add hM
  have hval : 2 * (11 / 48 - π ^ 2 / 36) - 0 +
      (-(31 / 24) + 2 * (π ^ 2 / 6) * Real.log 2 + π ^ 2 / 6 / 3 - QED.Polylog.zeta3 / 2) -
      1 / 2 * (1 / 2) + 1 / 2 * (-5 / 2) + 0 =
      -(7 / 3) + 2 * (π ^ 2 / 6) * Real.log 2 - QED.Polylog.zeta3 / 2 := by ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [hev] with p hp
  exact (scTotal_eq hp.1.1 hp.1.2.le hp.2).symm

/-- **The `S + C` link at `m = 1`, given the `δ₂, δ_m` half and the corner part.** -/
theorem scUnitLimitOne_of_sCtHalf_cornerPart (hct : SCtHalfFormula) (hC : CornerPartLimit) :
    SCUnitLimitOne :=
  scUnitLimitOne_of_sCtHalf hct (scTotalLimit_of_cornerPart hC)

end QED.TwoLoop.UnitSCLimit

end
