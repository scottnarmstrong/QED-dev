/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLCloseSubst
public import QED.TwoLoop.UnitLCloseBound
public import QED.TwoLoop.UnitLLinkDominated
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder unit L at finite regulators: the decomposition for the limit

Section 2.3 of `docs/TWO-LOOP-UNITS.md`, stage (2) of the L link, step 2. At photon mass `λ` and
Pauli–Villars mass `Λ` the L unit, normalized to the coefficient of `r²`, is

`L(λ, Λ) = ∬ G_Σ(λ, Λ) + δ₁ (F₂⁽²⁾(λ) - F₂⁽²⁾(Λ))` (`ladderTotal`)

(`QED.TwoLoop.UnitLLink.sixteen_pi_pow_four_mul_graphHalf_eq_gsum` and the counterterm half).
This file splits it, for `0 < λ ≤ 1 ≤ Λ`, as (`ladderTotal_eq`)

`L(λ, Λ) = Rep(λ) - ∬ e₁ + ∬ (G(Λ,Λ) - G(Λ,λ)) + F₂⁽²⁾(λ) S(Λ) + F₂⁽²⁾(Λ) (J(λ) + ∫ CT(λ))
  - F₂⁽²⁾(Λ) ∫ CT(Λ)`,

with `Rep(λ)` the document's representation (3.4) at `Λ = ∞` (the left side of
`QED.TwoLoop.UnitLLink.tendsto_ladderRep`) and `S(Λ) = ∫₀¹ ((Y/2) log M_Λ + CT(Λ; Y)) dY`: the large
logarithm `log M_Λ` of the inner subdivergence cancels between the graph and the counterterm
inside `S(Λ)`, at the same inner parameter `Y` (section 2.3 of the document). The integrability
facts needed come from the bounds of `QED.TwoLoop.UnitLCloseBound`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.TwoLoop.UnitLLink

/-! ### Integration helpers on `(0, 1)` -/

theorem setIntegral_Ioo_eq_intervalIntegral (f : ℝ → ℝ) :
    ∫ x in Ioo (0 : ℝ) 1, f x = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- A measurable function bounded on `(0, 1)` by an integrable one is integrable, with the
corresponding bound on its integral. -/
theorem intervalIntegrable_of_abs_le {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : IntervalIntegrable g volume 0 1) (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ g x) :
    IntervalIntegrable f volume 0 1 ∧ |∫ x in (0 : ℝ)..1, f x| ≤ ∫ x in (0 : ℝ)..1, g x := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioc (0 : ℝ) 1 → ‖f x‖ ≤ g x := by
    filter_upwards [ladder_ae_ne_one] with x hx1 hx
    rw [Real.norm_eq_abs]
    exact hb x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  refine ⟨hg.mono_fun' hf.aestronglyMeasurable ?_, ?_⟩
  · rw [uIoc_of_le zero_le_one]
    exact (ae_restrict_iff' measurableSet_Ioc).2 hae
  · rw [← Real.norm_eq_abs]
    exact intervalIntegral.norm_integral_le_of_norm_le zero_le_one hae hg

theorem measurable_intervalIntegral_of_uncurry {f : ℝ → ℝ → ℝ} (hf : Measurable (uncurry f)) :
    Measurable fun Y => ∫ x in (0 : ℝ)..1, f Y x := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact hf.stronglyMeasurable.integral_prod_right.measurable

/-! ### The logarithmic weight, integrated -/

theorem intervalIntegrable_add_ladderEll (a Y : ℝ) :
    IntervalIntegrable (fun x => a + ladderEll Y x) volume 0 1 := by
  have := (intervalIntegrable_const (c := a + log 2 - log Y - log (1 - Y))).sub
    (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
  refine this.congr_uIoo fun x _ => ?_
  simp only [ladderEll]
  ring

theorem integral_add_ladderEll (a Y : ℝ) :
    ∫ x in (0 : ℝ)..1, (a + ladderEll Y x) = a + 1 + log 2 - log Y - log (1 - Y) := by
  have e : (fun x => a + ladderEll Y x) = fun x => (a + log 2 - log Y - log (1 - Y)) - log x := by
    funext x; simp only [ladderEll]; ring
  rw [e, intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
    integral_log, intervalIntegral.integral_const]
  simp
  ring

theorem intervalIntegrable_log_one_sub :
    IntervalIntegrable (fun Y : ℝ => log (1 - Y)) volume 0 1 := by
  have := (intervalIntegral.intervalIntegrable_log' (a := 1) (b := 0)).comp_sub_left 1
  simpa using this

/-- `a - log Y - log(1 - Y)` is integrable on `(0, 1)`. -/
theorem intervalIntegrable_ellY (a : ℝ) :
    IntervalIntegrable (fun Y : ℝ => a - log Y - log (1 - Y)) volume 0 1 :=
  (intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log').sub intervalIntegrable_log_one_sub

/-! ### Measurability -/

theorem measurable_ladderGm_uncurry (la lb : ℝ) : Measurable (uncurry (ladderGm la lb)) := by
  change Measurable fun p : ℝ × ℝ => ladderGm la lb p.1 p.2
  unfold ladderGm ladderInnerMass
  fun_prop

theorem measurable_ladderE1_uncurry (lam Lam : ℝ) : Measurable (uncurry (ladderE1 lam Lam)) := by
  change Measurable fun p : ℝ × ℝ => ladderE1 lam Lam p.1 p.2
  unfold ladderE1 ladderE1Explicit ladderGm ladderInnerMass
  fun_prop

/-! ### Integrals over `x` -/

/-- **The outer-`Λ` terms, integrated over `x`**:
`|∫₀¹ G(Λ, μ; Y, x) dx| ≤ (13 + log Λ + log 2 - log Y - log(1-Y))/Λ²`. -/
theorem outer_x_bound {Λ μ Y : ℝ} (hΛ : 1 ≤ Λ) (hμ : 0 < μ) (hμΛ : μ ≤ Λ)
    (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (ladderGm Λ μ Y) volume 0 1 ∧
      |∫ x in (0 : ℝ)..1, ladderGm Λ μ Y x| ≤
        (13 + log Λ + log 2 - log Y - log (1 - Y)) / Λ ^ 2 := by
  have hg : IntervalIntegrable (fun x => (12 + log Λ + ladderEll Y x) / Λ ^ 2) volume 0 1 :=
    (intervalIntegrable_add_ladderEll (12 + log Λ) Y).div_const _
  obtain ⟨h1, h2⟩ := intervalIntegrable_of_abs_le
    ((measurable_ladderGm_uncurry Λ μ).comp (measurable_const.prodMk measurable_id)) hg
    fun x hx => abs_ladderGm_outer_le hΛ hμ hμΛ hY hx
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [intervalIntegral.integral_div, integral_add_ladderEll]
  ring

/-- **`e₁`, integrated over `x`**: `|∫₀¹ e₁(λ, Λ; Y, x) dx| ≤ 6 (2 + log 2 - log Y - log(1-Y))/√M_Λ`. -/
theorem e1_x_bound {lam Lam Y : ℝ} (hlam : 0 < lam) (hLam : 1 ≤ Lam) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (ladderE1 lam Lam Y) volume 0 1 ∧
      |∫ x in (0 : ℝ)..1, ladderE1 lam Lam Y x| ≤
        6 * (2 + log 2 - log Y - log (1 - Y)) / √(ladderInnerMass 1 Lam Y) := by
  have hg : IntervalIntegrable
      (fun x => 6 * (1 + ladderEll Y x) / √(ladderInnerMass 1 Lam Y)) volume 0 1 :=
    ((intervalIntegrable_add_ladderEll 1 Y).const_mul 6).div_const _
  obtain ⟨h1, h2⟩ := intervalIntegrable_of_abs_le
    ((measurable_ladderE1_uncurry lam Lam).comp (measurable_const.prodMk measurable_id)) hg
    fun x hx => abs_ladderE1_le hlam hLam hY hx
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_add_ladderEll]
  ring

theorem continuousOn_x_part {lam : ℝ} (hlam : 0 < lam) (p : ℝ → ℝ) (hp : Continuous p) :
    ContinuousOn (fun x => p x / ladderInnerMass 1 lam x) (uIcc 0 1) := by
  rw [uIcc_of_le zero_le_one]
  exact hp.continuousOn.div (by unfold ladderInnerMass; fun_prop)
    fun x hx => (ladderInnerMass_pos one_pos hlam hx).ne'

/-- **The explicit part, integrated over `x`**:
`∫₀¹ E(λ, Λ; Y, x) dx = (Y/2) log M_Λ · F₂⁽²⁾(λ) + (Y²(1-Y)/M_Λ) · J(λ)`. -/
theorem integral_ladderE1Explicit {lam : ℝ} (hlam : 0 < lam) (Lam Y : ℝ) :
    IntervalIntegrable (ladderE1Explicit lam Lam Y) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, ladderE1Explicit lam Lam Y x =
        Y / 2 * log (ladderInnerMass 1 Lam Y) * oneLoopF2 1 lam +
          Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y * outerSoftJ lam := by
  have i1 : IntervalIntegrable (fun x => x ^ 2 * (1 - x) * 1 ^ 2 / ladderInnerMass 1 lam x)
      volume 0 1 := (continuousOn_x_part hlam _ (by fun_prop)).intervalIntegrable
  have i2 : IntervalIntegrable (fun x => x * (1 - x) ^ 3 / ladderInnerMass 1 lam x) volume 0 1 :=
    (continuousOn_x_part hlam _ (by fun_prop)).intervalIntegrable
  refine ⟨(i1.const_mul _).add (i2.const_mul _), ?_⟩
  unfold ladderE1Explicit
  rw [intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, oneLoopF2,
    outerSoftJ]

theorem intervalIntegrable_ladderG {lam Y : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) : IntervalIntegrable (ladderG lam Y) volume 0 1 := by
  have habs : |lam| ≤ 1 := by rw [abs_of_pos hlam]; exact hlam1
  refine ((intervalIntegrable_ladderR habs hY).add (intervalIntegrable_ladderT1 hlam Y)).congr_uIoo
    fun x _ => ?_
  simp only [ladderR]
  ring

/-- **The decomposition at fixed `Y`**: `∫₀¹ G_Σ = ∫₀¹ G(λ,λ) - ∫₀¹ e₁ + ∫₀¹ E + ∫₀¹ (G(Λ,Λ) - G(Λ,λ))`. -/
theorem integral_ladderGSum_eq {lam Lam Y : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam)
    (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, ladderGSum lam Lam Y x =
      (∫ x in (0 : ℝ)..1, ladderG lam Y x) - (∫ x in (0 : ℝ)..1, ladderE1 lam Lam Y x) +
        (Y / 2 * log (ladderInnerMass 1 Lam Y) * oneLoopF2 1 lam +
          Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y * outerSoftJ lam) +
        ((∫ x in (0 : ℝ)..1, ladderGm Lam Lam Y x) - ∫ x in (0 : ℝ)..1, ladderGm Lam lam Y x) := by
  have iG := intervalIntegrable_ladderG hlam hlam1 hY
  have iE1 := (e1_x_bound hlam hLam hY).1
  obtain ⟨iEx, hEx⟩ := integral_ladderE1Explicit hlam Lam Y
  have iO1 := (outer_x_bound hLam (by linarith) le_rfl hY).1
  have iO2 := (outer_x_bound hLam hlam (by linarith) hY).1
  have e : (fun x => ladderGSum lam Lam Y x) = fun x =>
      ladderG lam Y x - ladderE1 lam Lam Y x + ladderE1Explicit lam Lam Y x +
        (ladderGm Lam Lam Y x - ladderGm Lam lam Y x) := by
    funext x
    simp only [ladderGSum, ladderE1, ← ladderGm_self]
    ring
  rw [e, intervalIntegral.integral_add ((iG.sub iE1).add iEx) (iO1.sub iO2),
    intervalIntegral.integral_add (iG.sub iE1) iEx, intervalIntegral.integral_sub iG iE1,
    intervalIntegral.integral_sub iO1 iO2, hEx]

/-! ### Integrals over `Y` -/

theorem ladderInnerMass_ge_three_quarters {Lam Y : ℝ} (hLam : 1 ≤ Lam) (hY : Y ∈ Icc (0 : ℝ) 1) :
    3 / 4 ≤ ladderInnerMass 1 Lam Y := by
  unfold ladderInnerMass
  have : (1 - Y) * 1 ≤ (1 - Y) * Lam ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith [hY.2])
  nlinarith [sq_nonneg (Y - 1 / 2)]

theorem ladderInnerMass_le_sq {Lam Y : ℝ} (hLam : 1 ≤ Lam) (hY : Y ∈ Icc (0 : ℝ) 1) :
    ladderInnerMass 1 Lam Y ≤ Lam ^ 2 := by
  unfold ladderInnerMass
  have h1 : 1 ≤ Lam ^ 2 := by nlinarith
  have h2 : Y ^ 2 ≤ Y := by nlinarith [hY.1, hY.2]
  have h3 : Y * 1 ≤ Y * Lam ^ 2 := mul_le_mul_of_nonneg_left h1 hY.1
  nlinarith

theorem intervalIntegrable_integral_ladderG {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, ladderG lam Y x) volume 0 1 := by
  have habs : |lam| ≤ 1 := by rw [abs_of_pos hlam]; exact hlam1
  refine ((intervalIntegrable_integral_ladderR habs).add
    (intervalIntegrable_integral_ladderT1 hlam)).congr_uIoo fun Y hY => ?_
  rw [uIoo_of_le zero_le_one] at hY
  simp only
  rw [← intervalIntegral.integral_add (intervalIntegrable_ladderR habs hY)
    (intervalIntegrable_ladderT1 hlam Y)]
  congr 1
  funext x
  simp only [ladderR]
  ring

/-- The dominating function of `∫ e₁ dx`: `6 (2 + log 2 - log Y - log(1-Y))/√M_Λ(Y)`. -/
noncomputable def e1Dom (Lam Y : ℝ) : ℝ :=
  6 * (2 + log 2 - log Y - log (1 - Y)) / √(ladderInnerMass 1 Lam Y)

theorem intervalIntegrable_e1Dom {Lam : ℝ} (hLam : 1 ≤ Lam) :
    IntervalIntegrable (e1Dom Lam) volume 0 1 := by
  have hc : ContinuousOn (fun Y => 1 / √(ladderInnerMass 1 Lam Y)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.div continuousOn_const
      (by unfold ladderInnerMass; fun_prop) fun Y hY => ?_
    have := ladderInnerMass_ge_three_quarters hLam hY
    exact (Real.sqrt_pos.mpr (by linarith)).ne'
  refine (((intervalIntegrable_ellY (2 + log 2)).const_mul 6).mul_continuousOn hc).congr_uIoo
    fun Y _ => ?_
  simp only [e1Dom]
  ring

theorem e1_Y_bound {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 1 ≤ Lam) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, ladderE1 lam Lam Y x) volume 0 1 ∧
      |∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderE1 lam Lam Y x| ≤
        ∫ Y in (0 : ℝ)..1, e1Dom Lam Y :=
  intervalIntegrable_of_abs_le (measurable_intervalIntegral_of_uncurry
    (measurable_ladderE1_uncurry lam Lam)) (intervalIntegrable_e1Dom hLam)
    fun _ hY => (e1_x_bound hlam hLam hY).2

theorem outer_Y_bound {Λ μ : ℝ} (hΛ : 1 ≤ Λ) (hμ : 0 < μ) (hμΛ : μ ≤ Λ) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, ladderGm Λ μ Y x) volume 0 1 ∧
      |∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderGm Λ μ Y x| ≤
        ∫ Y in (0 : ℝ)..1, (13 + log Λ + log 2 - log Y - log (1 - Y)) / Λ ^ 2 :=
  intervalIntegrable_of_abs_le (measurable_intervalIntegral_of_uncurry
    (measurable_ladderGm_uncurry Λ μ)) ((intervalIntegrable_ellY (13 + log Λ + log 2)).div_const _)
    fun _ hY => (outer_x_bound hΛ hμ hμΛ hY).2

theorem continuousOn_ladderInnerMass_Y {Lam : ℝ} (hLam : 0 < Lam) (p : ℝ → ℝ) (hp : Continuous p) :
    ContinuousOn (fun Y => p Y / ladderInnerMass 1 Lam Y) (uIcc 0 1) := by
  rw [uIcc_of_le zero_le_one]
  exact hp.continuousOn.div (by unfold ladderInnerMass; fun_prop)
    fun Y hY => (ladderInnerMass_pos one_pos hLam hY).ne'

theorem intervalIntegrable_half_log {Lam : ℝ} (hLam : 0 < Lam) :
    IntervalIntegrable (fun Y => Y / 2 * log (ladderInnerMass 1 Lam Y)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  exact (continuousOn_id.div_const 2).mul ((by unfold ladderInnerMass; fun_prop :
    ContinuousOn (fun Y => ladderInnerMass 1 Lam Y) (Icc 0 1)).log
      fun Y hY => (ladderInnerMass_pos one_pos hLam hY).ne')

/-! ### The global decomposition -/

/-- **The L unit at finite regulators**, normalized to the coefficient of `r²`:
`L(λ, Λ) = ∬ G_Σ + δ₁ (F₂⁽²⁾(λ) - F₂⁽²⁾(Λ))`. -/
noncomputable def ladderTotal (lam Lam : ℝ) : ℝ :=
  (∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, ladderGSum lam Lam Y x) +
    ladderDeltaOne 1 lam Lam * (oneLoopF2 1 lam - oneLoopF2 1 Lam)

/-- **The representation (3.4) of the document** at photon mass `λ` (`Λ = ∞`). -/
noncomputable def ladderRep (lam : ℝ) : ℝ :=
  ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, ladderG lam Y x) - oneLoopF2 1 lam * ladderCtBracket lam Y)

/-- `S(Λ) = ∫₀¹ ((Y/2) log M_Λ + CT(Λ; Y)) dY`: the inner logarithm of the graph, at the same inner
parameter as the counterterm. -/
noncomputable def ladderS1 (Lam : ℝ) : ℝ :=
  ∫ Y in (0 : ℝ)..1, (Y / 2 * log (ladderInnerMass 1 Lam Y) + ladderCtBracket Lam Y)

/-- `δ₁ = -∫₀¹ CT(λ) + ∫₀¹ CT(Λ)`. -/
theorem ladderDeltaOne_eq {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 < Lam) :
    ladderDeltaOne 1 lam Lam =
      -(∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y) + ∫ Y in (0 : ℝ)..1, ladderCtBracket Lam Y := by
  rw [ladderDeltaOne]
  have : ∫ Y in (0 : ℝ)..1, (Y * (Y ^ 2 + 2 * Y - 2) / 2 *
        (1 ^ 2 / ladderInnerMass 1 lam Y - 1 ^ 2 / ladderInnerMass 1 Lam Y) -
      Y / 2 * log (ladderInnerMass 1 lam Y / ladderInnerMass 1 Lam Y)) =
      ∫ Y in (0 : ℝ)..1, (ladderCtBracket lam Y - ladderCtBracket Lam Y) := by
    refine intervalIntegral.integral_congr fun Y hY => ?_
    rw [uIcc_of_le zero_le_one] at hY
    have h1 := ladderInnerMass_pos one_pos hlam hY
    have h2 := ladderInnerMass_pos one_pos hLam hY
    simp only [ladderCtBracket]
    rw [log_div h1.ne' h2.ne']
    field_simp
    ring
  rw [this, intervalIntegral.integral_sub (intervalIntegrable_ladderCtBracket hlam)
    (intervalIntegrable_ladderCtBracket hLam)]
  ring

theorem ladderRep_split {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ladderRep lam = (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderG lam Y x) -
      oneLoopF2 1 lam * ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y := by
  rw [ladderRep, intervalIntegral.integral_sub (intervalIntegrable_integral_ladderG hlam hlam1)
    ((intervalIntegrable_ladderCtBracket hlam).const_mul _), intervalIntegral.integral_const_mul]

/-- **The decomposition of the L unit at finite regulators** (`0 < λ ≤ 1 ≤ Λ`):
`L(λ, Λ) = Rep(λ) - ∬ e₁ + ∬ (G(Λ,Λ) - G(Λ,λ)) + F₂⁽²⁾(λ) S(Λ) + F₂⁽²⁾(Λ)(J(λ) + ∫ CT(λ))
  - F₂⁽²⁾(Λ) ∫ CT(Λ)`. -/
theorem ladderTotal_eq {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam) :
    ladderTotal lam Lam = ladderRep lam -
      (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderE1 lam Lam Y x) +
      ((∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderGm Lam Lam Y x) -
        ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderGm Lam lam Y x) +
      oneLoopF2 1 lam * ladderS1 Lam +
      oneLoopF2 1 Lam * (outerSoftJ lam + ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y) -
      oneLoopF2 1 Lam * ∫ Y in (0 : ℝ)..1, ladderCtBracket Lam Y := by
  have hLam0 : 0 < Lam := by linarith
  have iG := intervalIntegrable_integral_ladderG hlam hlam1
  have iE1 := (e1_Y_bound hlam hLam).1
  have iO1 := (outer_Y_bound hLam hLam0 le_rfl).1
  have iO2 := (outer_Y_bound hLam hlam (by linarith)).1
  have ia := intervalIntegrable_half_log hLam0
  have ib : IntervalIntegrable (fun Y => Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y)
      volume 0 1 := (continuousOn_ladderInnerMass_Y hLam0 _ (by fun_prop)).intervalIntegrable
  have iCl := intervalIntegrable_ladderCtBracket hlam
  have iCL := intervalIntegrable_ladderCtBracket hLam0
  have hsum : ∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, ladderGSum lam Lam Y x =
      ∫ Y in (0 : ℝ)..1, ((∫ x in (0 : ℝ)..1, ladderG lam Y x) -
        (∫ x in (0 : ℝ)..1, ladderE1 lam Lam Y x) +
        (Y / 2 * log (ladderInnerMass 1 Lam Y) * oneLoopF2 1 lam +
          Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y * outerSoftJ lam) +
        ((∫ x in (0 : ℝ)..1, ladderGm Lam Lam Y x) - ∫ x in (0 : ℝ)..1, ladderGm Lam lam Y x)) := by
    simp only [setIntegral_Ioo_eq_intervalIntegral]
    refine intervalIntegral.integral_congr_uIoo fun Y hY => ?_
    rw [uIoo_of_le zero_le_one] at hY
    exact integral_ladderGSum_eq hlam hlam1 hLam hY
  have hab := (ia.mul_const (oneLoopF2 1 lam)).add (ib.mul_const (outerSoftJ lam))
  rw [ladderTotal, hsum, intervalIntegral.integral_add ((iG.sub iE1).add hab) (iO1.sub iO2),
    intervalIntegral.integral_add (iG.sub iE1) hab, intervalIntegral.integral_sub iG iE1,
    intervalIntegral.integral_sub iO1 iO2,
    intervalIntegral.integral_add (ia.mul_const _) (ib.mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    ladderDeltaOne_eq hlam hLam0, ladderRep_split hlam hlam1, ladderS1,
    intervalIntegral.integral_add ia iCL]
  have hF : ∫ Y in (0 : ℝ)..1, Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 Lam Y =
      oneLoopF2 1 Lam := rfl
  rw [hF]
  ring

end QED.TwoLoop.UnitLLink

end
