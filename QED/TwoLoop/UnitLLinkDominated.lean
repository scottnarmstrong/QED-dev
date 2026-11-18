/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLLinkDominatedBound
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder unit L: the limit `λ → 0` of the representation (3.4)

Section 3.4 of `docs/TWO-LOOP-UNITS.md`, stage (3) of the L link, completed. The uniform bound
`|R(λ; Y, x)| ≤ 153 Y^(-3/4) x^(-3/4)` (`abs_ladderR_le_rpow`, valid for `|λ| ≤ 1`) dominates the
remainder `R = G - T₁` on the square. This file proves:

* `intervalIntegrable_ladderR`, `intervalIntegrable_integral_ladderR`: for `|λ| ≤ 1`,
  `R(λ; Y, ·)` is integrable on `(0, 1)` for every `Y ∈ (0, 1)`, and `Y ↦ ∫₀¹ R(λ; Y, x) dx` is
  integrable on `(0, 1)`;
* `integrable_ladderR_prod`, `integral_prod_ladderR`: `R(λ)` is integrable on the square
  `(0,1]²` for the product measure, and its double integral is the iterated one (Fubini); the
  same for `R₀` (`integrable_ladderR0_prod`, `integral_prod_ladderR0`);
* `tendsto_integral_integral_ladderR`: `∬ R(λ) → ∬ R₀` as `λ → 0⁺` (dominated convergence,
  first in `x` at fixed `Y`, then in `Y`), which is the hypothesis of
  `tendsto_of_tendsto_integral_ladderR`;
* `ladderRep_eq`: for `0 < λ ≤ 1`, the representation (3.4) splits as
  `∫₀¹ dY {∫₀¹ G dx - F₂⁽²⁾(λ) CT(λ; Y)} = ∬ R(λ) - F₂⁽²⁾(λ)(J(λ) + ∫₀¹ CT(λ; Y) dY)`;
* `tendsto_ladderRep`: **the representation (3.4) tends to `11/48 + π²/18` as `λ → 0⁺`**, the
  value `L = 1/6 + ∫₀¹ K_L` of eq. (3.6).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function
open scoped Interval

namespace QED.TwoLoop.UnitLLink

open QED.TwoLoop.Units

/-! ### The dominating function -/

/-- The dominating function `153 Y^(-3/4) x^(-3/4)` of the remainder. -/
noncomputable def ladderDom (Y x : ℝ) : ℝ := 153 * (Y ^ (-(3 / 4) : ℝ) * x ^ (-(3 / 4) : ℝ))

theorem ladderDom_nonneg {Y x : ℝ} (hY : 0 ≤ Y) (hx : 0 ≤ x) : 0 ≤ ladderDom Y x := by
  unfold ladderDom
  have := Real.rpow_nonneg hY (-(3 / 4) : ℝ)
  have := Real.rpow_nonneg hx (-(3 / 4) : ℝ)
  positivity

/-- `∫₀¹ x^(-3/4) dx`, finite. -/
noncomputable def ladderDomConst : ℝ := ∫ x in (0 : ℝ)..1, x ^ (-(3 / 4) : ℝ)

theorem intervalIntegrable_rpow_neg_three_quarters :
    IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4) : ℝ)) volume 0 1 :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num)

theorem intervalIntegrable_ladderDom (Y : ℝ) : IntervalIntegrable (ladderDom Y) volume 0 1 :=
  (intervalIntegrable_rpow_neg_three_quarters.const_mul (Y ^ (-(3 / 4) : ℝ))).const_mul 153

theorem integral_ladderDom (Y : ℝ) :
    ∫ x in (0 : ℝ)..1, ladderDom Y x = 153 * Y ^ (-(3 / 4) : ℝ) * ladderDomConst := by
  simp only [ladderDom, intervalIntegral.integral_const_mul, ladderDomConst]
  ring

theorem ladderR_one_right (lam Y : ℝ) : ladderR lam Y 1 = 0 := by
  simp [ladderR, ladderG, ladderT1]

theorem ladderR0_one_right (Y : ℝ) : ladderR0 Y 1 = 0 := by
  simp [ladderR0]

/-- The uniform bound on `(0,1) × (0,1]`. -/
theorem abs_ladderR_le_ladderDom {lam Y x : ℝ} (hlam : |lam| ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioc (0 : ℝ) 1) : |ladderR lam Y x| ≤ ladderDom Y x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h, ladderR_one_right, abs_zero]
    exact ladderDom_nonneg hY.1.le zero_le_one
  · exact abs_ladderR_le_rpow hlam hY ⟨hx.1, h⟩

/-- The same bound for the limit `R₀`, by passing to the limit `λ → 0`. -/
theorem abs_ladderR0_le_ladderDom {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioc (0 : ℝ) 1) :
    |ladderR0 Y x| ≤ ladderDom Y x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h, ladderR0_one_right, abs_zero]
    exact ladderDom_nonneg hY.1.le zero_le_one
  · have hlim := (tendsto_ladderR hY ⟨hx.1, h⟩).abs
    refine le_of_tendsto hlim ?_
    have : ∀ᶠ lam in 𝓝 (0 : ℝ), lam ∈ Icc (-1 : ℝ) 1 := Icc_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with lam hlam
    exact abs_ladderR_le_ladderDom (abs_le.mpr hlam) hY hx

/-! ### Measurability -/

theorem measurable_ladderR_uncurry (lam : ℝ) : Measurable (uncurry (ladderR lam)) := by
  change Measurable fun p : ℝ × ℝ => ladderR lam p.1 p.2
  unfold ladderR ladderG ladderT1 ladderInnerMass
  fun_prop

theorem measurable_ladderR0_uncurry : Measurable (uncurry ladderR0) := by
  change Measurable fun p : ℝ × ℝ => ladderR0 p.1 p.2
  unfold ladderR0 ladderW ladderP
  fun_prop

theorem measurable_ladderR (lam Y : ℝ) : Measurable (ladderR lam Y) :=
  (measurable_ladderR_uncurry lam).comp (measurable_const.prodMk measurable_id)

theorem stronglyMeasurable_integral_ladderR (lam : ℝ) :
    StronglyMeasurable fun Y => ∫ x in (0 : ℝ)..1, ladderR lam Y x := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact (measurable_ladderR_uncurry lam).stronglyMeasurable.integral_prod_right

/-- Almost every point of the line differs from `1`. -/
theorem ladder_ae_ne_one : ∀ᵐ Y ∂(volume : Measure ℝ), Y ≠ 1 := by
  have := measure_eq_zero_iff_ae_notMem.mp (measure_singleton (μ := volume) (1 : ℝ))
  simpa using this

/-! ### Integrability -/

/-- **`R(λ; Y, ·)` is integrable on `(0, 1)`** for `|λ| ≤ 1`, `Y ∈ (0, 1)`. -/
theorem intervalIntegrable_ladderR {lam Y : ℝ} (hlam : |lam| ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (ladderR lam Y) volume 0 1 := by
  refine (intervalIntegrable_ladderDom Y).mono_fun' (measurable_ladderR lam Y).aestronglyMeasurable
    ?_
  rw [uIoc_of_le zero_le_one]
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
  change ‖ladderR lam Y x‖ ≤ ladderDom Y x
  rw [Real.norm_eq_abs]
  exact abs_ladderR_le_ladderDom hlam hY hx

/-- `|∫₀¹ R(λ; Y, x) dx| ≤ 153 Y^(-3/4) ∫₀¹ x^(-3/4) dx`. -/
theorem norm_integral_ladderR_le {lam Y : ℝ} (hlam : |lam| ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    ‖∫ x in (0 : ℝ)..1, ladderR lam Y x‖ ≤ 153 * Y ^ (-(3 / 4) : ℝ) * ladderDomConst := by
  rw [← integral_ladderDom]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (ae_of_all _ fun x hx => ?_) (intervalIntegrable_ladderDom Y)
  rw [Real.norm_eq_abs]
  exact abs_ladderR_le_ladderDom hlam hY hx

theorem intervalIntegrable_ladderDomOuter :
    IntervalIntegrable (fun Y : ℝ => 153 * Y ^ (-(3 / 4) : ℝ) * ladderDomConst) volume 0 1 :=
  (intervalIntegrable_rpow_neg_three_quarters.const_mul 153).mul_const _

/-- The outer bound holds almost everywhere on `Ι 0 1`. -/
theorem ae_norm_integral_ladderR_le {lam : ℝ} (hlam : |lam| ≤ 1) :
    ∀ᵐ Y ∂(volume : Measure ℝ), Y ∈ Ι (0 : ℝ) 1 →
      ‖∫ x in (0 : ℝ)..1, ladderR lam Y x‖ ≤ 153 * Y ^ (-(3 / 4) : ℝ) * ladderDomConst := by
  filter_upwards [ladder_ae_ne_one] with Y hY1 hY
  rw [uIoc_of_le zero_le_one] at hY
  exact norm_integral_ladderR_le hlam ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩

/-- **`Y ↦ ∫₀¹ R(λ; Y, x) dx` is integrable on `(0, 1)`** for `|λ| ≤ 1`. -/
theorem intervalIntegrable_integral_ladderR {lam : ℝ} (hlam : |lam| ≤ 1) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, ladderR lam Y x) volume 0 1 := by
  refine intervalIntegrable_ladderDomOuter.mono_fun'
    (stronglyMeasurable_integral_ladderR lam).aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_uIoc).2 (ae_norm_integral_ladderR_le hlam)

/-! ### Fubini on the square -/

/-- The unit square `(0,1]²` with the product of the restricted Lebesgue measures. -/
noncomputable abbrev ladderSquareMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))

theorem squareMeasure_eq :
    ladderSquareMeasure = (volume.prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
  rw [ladderSquareMeasure]
  nth_rewrite 1 [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
  rw [Measure.prod_restrict]

theorem integrable_ladderDom_prod : Integrable (uncurry ladderDom) ladderSquareMeasure := by
  have h := ((intervalIntegrable_rpow_neg_three_quarters.def'.integrable).mul_prod
    (intervalIntegrable_rpow_neg_three_quarters.def'.integrable)).const_mul 153
  rw [uIoc_of_le zero_le_one] at h
  exact h.congr (ae_of_all _ fun z => rfl)

theorem ladder_ae_square_mem : ∀ᵐ z ∂ladderSquareMeasure, z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
  rw [squareMeasure_eq]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)

/-- **`R(λ)` is integrable on the square** for `|λ| ≤ 1`. -/
theorem integrable_ladderR_prod {lam : ℝ} (hlam : |lam| ≤ 1) :
    Integrable (uncurry (ladderR lam)) ladderSquareMeasure := by
  refine integrable_ladderDom_prod.mono' (measurable_ladderR_uncurry lam).aestronglyMeasurable ?_
  filter_upwards [ladder_ae_square_mem] with z hz
  rw [Real.norm_eq_abs]
  exact abs_ladderR_le_ladderDom hlam hz.1 hz.2

/-- **`R₀` is integrable on the square**. -/
theorem integrable_ladderR0_prod : Integrable (uncurry ladderR0) ladderSquareMeasure := by
  refine integrable_ladderDom_prod.mono' measurable_ladderR0_uncurry.aestronglyMeasurable ?_
  filter_upwards [ladder_ae_square_mem] with z hz
  rw [Real.norm_eq_abs]
  exact abs_ladderR0_le_ladderDom hz.1 hz.2

/-- **Fubini for `R(λ)`**: the double integral over the square is the iterated one of (3.4). -/
theorem integral_prod_ladderR {lam : ℝ} (hlam : |lam| ≤ 1) :
    ∫ z, ladderR lam z.1 z.2 ∂ladderSquareMeasure =
      ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR lam Y x := by
  rw [integral_prod (fun z : ℝ × ℝ => ladderR lam z.1 z.2) (integrable_ladderR_prod hlam)]
  simp only [intervalIntegral.integral_of_le zero_le_one]

/-- **Fubini for `R₀`**. -/
theorem integral_prod_ladderR0 :
    ∫ z, ladderR0 z.1 z.2 ∂ladderSquareMeasure =
      ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR0 Y x := by
  rw [integral_prod (fun z : ℝ × ℝ => ladderR0 z.1 z.2) integrable_ladderR0_prod]
  simp only [intervalIntegral.integral_of_le zero_le_one]

/-! ### Dominated convergence -/

theorem ladder_eventually_mem_Ioo : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Ioo (0 : ℝ) 1 ∧ |lam| ≤ 1 := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with lam hlam
  exact ⟨hlam, by rw [abs_of_pos hlam.1]; exact hlam.2.le⟩

/-- **The inner limit**: `∫₀¹ R(λ; Y, x) dx → ∫₀¹ R₀(Y, x) dx` for `Y ∈ (0, 1)`. -/
theorem tendsto_integral_ladderR {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun lam => ∫ x in (0 : ℝ)..1, ladderR lam Y x) (𝓝[>] 0)
      (𝓝 (∫ x in (0 : ℝ)..1, ladderR0 Y x)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (ladderDom Y)
    (Eventually.of_forall fun lam => (measurable_ladderR lam Y).aestronglyMeasurable) ?_
    (intervalIntegrable_ladderDom Y) ?_
  · filter_upwards [ladder_eventually_mem_Ioo] with lam hlam
    refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs]
    exact abs_ladderR_le_ladderDom hlam.2 hY hx
  · refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h
      simp only [ladderR_one_right, ladderR0_one_right]
      exact tendsto_const_nhds
    · exact (tendsto_ladderR hY ⟨hx.1, h⟩).mono_left nhdsWithin_le_nhds

/-- **`∬ R(λ) → ∬ R₀` as `λ → 0⁺`**. -/
theorem tendsto_integral_integral_ladderR :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR lam Y x) (𝓝[>] 0)
      (𝓝 (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR0 Y x)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun Y => 153 * Y ^ (-(3 / 4) : ℝ) * ladderDomConst)
    (Eventually.of_forall fun lam => (stronglyMeasurable_integral_ladderR lam).aestronglyMeasurable)
    ?_ intervalIntegrable_ladderDomOuter ?_
  · filter_upwards [ladder_eventually_mem_Ioo] with lam hlam
    exact ae_norm_integral_ladderR_le hlam.2
  · filter_upwards [ladder_ae_ne_one] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact tendsto_integral_ladderR ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩

/-- **Stage (3) without hypotheses**: `∬ R(λ) - F₂⁽²⁾(λ)(J(λ) + ∫ CT) → 11/48 + π²/18`. -/
theorem tendsto_ladderRemainderTotal :
    Tendsto (fun lam => (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR lam Y x) -
        oneLoopF2 1 lam * (outerSoftJ lam + ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y))
      (𝓝[>] 0) (𝓝 (11 / 48 + π ^ 2 / 18)) :=
  tendsto_of_tendsto_integral_ladderR tendsto_integral_integral_ladderR

/-! ### The representation (3.4) -/

theorem continuousOn_ladderInnerMass (lam : ℝ) :
    ContinuousOn (fun Y => ladderInnerMass 1 lam Y) (Icc 0 1) := by
  unfold ladderInnerMass; fun_prop

theorem intervalIntegrable_ladderT1 {lam : ℝ} (hlam : 0 < lam) (Y : ℝ) :
    IntervalIntegrable (fun x => ladderT1 lam Y x) volume 0 1 := by
  simp_rw [ladderT1_eq]
  refine IntervalIntegrable.const_mul ?_ _
  exact (ContinuousOn.div (by fun_prop) (continuousOn_ladderInnerMass lam) fun x hx =>
    (ladderInnerMass_pos one_pos hlam hx).ne').intervalIntegrable_of_Icc zero_le_one

theorem integral_ladderT1 (lam Y : ℝ) :
    ∫ x in (0 : ℝ)..1, ladderT1 lam Y x =
      -(Y ^ 2 * (1 - Y) * 1 ^ 2 / ladderInnerMass 1 lam Y) * outerSoftJ lam := by
  simp only [ladderT1_eq, intervalIntegral.integral_const_mul, outerSoftJ]

theorem intervalIntegrable_integral_ladderT1 {lam : ℝ} (hlam : 0 < lam) :
    IntervalIntegrable (fun Y => ∫ x in (0 : ℝ)..1, ladderT1 lam Y x) volume 0 1 := by
  simp_rw [integral_ladderT1]
  refine IntervalIntegrable.mul_const ?_ _
  exact (ContinuousOn.neg (ContinuousOn.div (by fun_prop) (continuousOn_ladderInnerMass lam)
    fun x hx => (ladderInnerMass_pos one_pos hlam hx).ne')).intervalIntegrable_of_Icc
    zero_le_one

theorem intervalIntegrable_ladderCtBracket {lam : ℝ} (hlam : 0 < lam) :
    IntervalIntegrable (ladderCtBracket lam) volume 0 1 := by
  have hM : ∀ Y ∈ Icc (0 : ℝ) 1, 0 < ladderInnerMass 1 lam Y := fun Y hY =>
    ladderInnerMass_pos one_pos hlam hY
  have hMc := continuousOn_ladderInnerMass lam
  refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
  exact (ContinuousOn.div (by fun_prop) (continuousOn_const.mul hMc) fun Y hY =>
    mul_ne_zero two_ne_zero (hM Y hY).ne').sub
    ((by fun_prop : ContinuousOn (fun Y : ℝ => Y / 2) (Icc 0 1)).mul
      (hMc.log fun Y hY => (hM Y hY).ne'))

/-- **The representation (3.4) splits**: for `0 < λ ≤ 1`,
`∫₀¹ dY {∫₀¹ G dx - F₂⁽²⁾(λ) CT(λ; Y)} = ∬ R(λ) - F₂⁽²⁾(λ)(J(λ) + ∫₀¹ CT(λ; Y) dY)`. -/
theorem ladderRep_eq {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) :
    ∫ Y in (0 : ℝ)..1,
        ((∫ x in (0 : ℝ)..1, ladderG lam Y x) - oneLoopF2 1 lam * ladderCtBracket lam Y) =
      (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ladderR lam Y x) -
        oneLoopF2 1 lam * (outerSoftJ lam + ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y) := by
  have hlam0 := hlam.1
  have habs : |lam| ≤ 1 := by rw [abs_of_pos hlam0]; exact hlam.2
  have hG : ∀ᵐ Y ∂(volume : Measure ℝ), Y ∈ Ι (0 : ℝ) 1 →
      (∫ x in (0 : ℝ)..1, ladderG lam Y x) - oneLoopF2 1 lam * ladderCtBracket lam Y =
        ((∫ x in (0 : ℝ)..1, ladderR lam Y x) + ∫ x in (0 : ℝ)..1, ladderT1 lam Y x) -
          oneLoopF2 1 lam * ladderCtBracket lam Y := by
    filter_upwards [ladder_ae_ne_one] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    rw [← intervalIntegral.integral_add
      (intervalIntegrable_ladderR habs ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩)
      (intervalIntegrable_ladderT1 hlam0 Y)]
    congr 2
    funext x
    simp only [ladderR]
    ring
  rw [intervalIntegral.integral_congr_ae hG,
    intervalIntegral.integral_sub ((intervalIntegrable_integral_ladderR habs).add
      (intervalIntegrable_integral_ladderT1 hlam0))
      ((intervalIntegrable_ladderCtBracket hlam0).const_mul _),
    intervalIntegral.integral_add (intervalIntegrable_integral_ladderR habs)
      (intervalIntegrable_integral_ladderT1 hlam0),
    intervalIntegral.integral_const_mul, integral_integral_ladderT1]
  ring

/-- **The limit `λ → 0⁺` of the representation (3.4)**:
`∫₀¹ dY {∫₀¹ G(λ; Y, x) dx - F₂⁽²⁾(λ) CT(λ; Y)} → 11/48 + π²/18 = 11/48 + ζ(2)/3`. -/
theorem tendsto_ladderRep :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1,
        ((∫ x in (0 : ℝ)..1, ladderG lam Y x) - oneLoopF2 1 lam * ladderCtBracket lam Y))
      (𝓝[>] 0) (𝓝 (11 / 48 + π ^ 2 / 18)) := by
  refine tendsto_ladderRemainderTotal.congr' ?_
  filter_upwards [ladder_eventually_mem_Ioo] with lam hlam
  exact (ladderRep_eq ⟨hlam.1.1, hlam.1.2.le⟩).symm

end QED.TwoLoop.UnitLLink

end
