/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerMainBound
public import QED.TwoLoop.UnitSCCornerReduce
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner unit C: the main term of the limit `λ → 0`

Section 6.4 of `docs/TWO-LOOP-UNITS.md`, stage 3 of the `S + C` link for the corner pair. This file
proves `QED.TwoLoop.UnitSCCorner.cornerMainLimit : CornerMainLimit` (helpers in namespace
`QED.TwoLoop.UnitSCCornerMain`):

* `(y₃, y₄) ↦ ∫₀¹ G_C dx` (`cornerZeroInt`, `G_C = cornerGm 0 0`) is integrable on the triangle;
* `∫_{y₃,y₄} ∫₀¹ cornerGm λ λ dx → ∫_{y₃,y₄} ∫₀¹ G_C dx` as `λ → 0⁺`.

Both follow by dominated convergence (in `x` for each `(y₃, y₄)`, then on the triangle) from the
bound of `QED/TwoLoop/UnitSCCornerMainBound.lean`,
`|cornerGm λ λ y₃ y₄ x| ≤ C/((y₃ + y₄) √x √(y₃ (1 - y₃ - y₄)))` for `λ² ≤ 1`: its `x`-integral is
`C J/((y₃ + y₄) √g)` with `J = ∫₀¹ dx/√x`, which in the variables `(Y, ξ)` of
`QED.TwoLoop.UnitXClose.integrableOn_triangle_iff` is `C J/(√Y √(1-Y) √ξ)` against `dY dξ`
(`integrableOn_cornerW`). The pointwise limit is the continuity of the closed form at `λ = 0`
(`continuousAt_cornerGm`), where `M = Y² > 0` and `h = x > 0`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.TwoLoop.UnitSCCornerMain

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink QED.TwoLoop.UnitXClose QED.TwoLoop.UnitXGraph
open QED.TwoLoop.UnitSCCorner

/-! ### Measurability and continuity -/

theorem continuous_cornerCoeffs :
    (Continuous fun q : (ℝ × ℝ) × ℝ => cornerA0 q.2 q.1.1 q.1.2) ∧
    (Continuous fun q : (ℝ × ℝ) × ℝ => cornerA1 q.2 q.1.1 q.1.2) ∧
    (Continuous fun q : (ℝ × ℝ) × ℝ => cornerA2 q.2 q.1.1 q.1.2) ∧
    (Continuous fun q : (ℝ × ℝ) × ℝ => cornerC0 q.2) ∧
    (Continuous fun q : (ℝ × ℝ) × ℝ => cornerC1 q.2 q.1.1 q.1.2) ∧
    (Continuous fun q : (ℝ × ℝ) × ℝ => cornerC2 q.2 q.1.1 q.1.2) ∧
    (Continuous fun q : (ℝ × ℝ) × ℝ => cornerC3 q.2 q.1.1 q.1.2) ∧
    (Continuous fun q : (ℝ × ℝ) × ℝ => cornerG q.1.1 q.1.2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cornerA0 UnitSCReduce.cornerP1; fun_prop
  · unfold cornerA1 cornerQ cornerG UnitSCReduce.cornerP1; fun_prop
  · unfold cornerA2 cornerQ cornerG; fun_prop
  · unfold cornerC0; fun_prop
  · unfold cornerC1 cornerG UnitSCReduce.cornerP2; fun_prop
  · unfold cornerC2 cornerR cornerG UnitSCReduce.cornerP2; fun_prop
  · unfold cornerC3 cornerR cornerG; fun_prop
  · unfold cornerG; fun_prop

theorem measurable_cForm {α : Type*} [MeasurableSpace α]
    {a₀ a₁ a₂ c₀ c₁ c₂ c₃ β h M A L : α → ℝ} (h0 : Measurable a₀) (h1 : Measurable a₁)
    (h2 : Measurable a₂) (h3 : Measurable c₀) (h4 : Measurable c₁) (h5 : Measurable c₂)
    (h6 : Measurable c₃) (hβ : Measurable β) (hh : Measurable h) (hM : Measurable M)
    (hA : Measurable A) (hL : Measurable L) :
    Measurable fun q => cForm (a₀ q) (a₁ q) (a₂ q) (c₀ q) (c₁ q) (c₂ q) (c₃ q) (β q) (h q) (M q)
      (A q) (L q) := by
  unfold cForm
  fun_prop

theorem measurable_cornerGm_uncurry (lam : ℝ) :
    Measurable fun q : (ℝ × ℝ) × ℝ => cornerGm lam lam q.1.1 q.1.2 q.2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, hg⟩ := continuous_cornerCoeffs
  have mβ : Measurable fun q : (ℝ × ℝ) × ℝ => betaG (cornerG q.1.1 q.1.2) (q.1.1 * q.1.2) q.2 := by
    have := hg.measurable
    unfold betaG
    fun_prop
  have mh : Measurable fun q : (ℝ × ℝ) × ℝ => ladderInnerMass 1 lam q.2 / q.2 := by
    unfold ladderInnerMass; fun_prop
  have mM : Measurable fun q : (ℝ × ℝ) × ℝ => cornerMass lam lam q.1.1 q.1.2 := by
    unfold cornerMass; fun_prop
  exact measurable_cForm h0.measurable h1.measurable h2.measurable h3.measurable h4.measurable
    h5.measurable h6.measurable mβ mh mM (mM.add (mβ.mul mh)).log
    ((measurable_const.add (mM.div (mβ.mul mh))).log)

theorem measurable_cornerGm (lam y3 y4 : ℝ) : Measurable (cornerGm lam lam y3 y4) := by
  have h := (measurable_cornerGm_uncurry lam).comp
    (measurable_const.prodMk measurable_id : Measurable fun x : ℝ => ((y3, y4), x))
  simpa only [Function.comp_def] using h

/-- **Continuity at `λ = 0`** of the closed form, for `(y₃, y₄)` in the triangle and `0 < x < 1`. -/
theorem continuousAt_cornerGm {y3 y4 x : ℝ} (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    ContinuousAt (fun lam => cornerGm lam lam y3 y4 x) 0 := by
  have hg : 0 < cornerG y3 y4 := by
    unfold cornerG; have : 0 < 1 - y3 - y4 := by linarith
    positivity
  have hβ : 0 < betaG (cornerG y3 y4) (y3 * y4) x := betaG_pos hg
  have h1x : 0 < 1 - x := by linarith
  have h1Y : 0 < 1 - (y3 + y4) := by linarith
  unfold cornerGm cForm cornerMass ladderInnerMass
  generalize betaG (cornerG y3 y4) (y3 * y4) x = β at hβ ⊢
  fun_prop (disch := (apply ne_of_gt; first
    | (simp only [one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, zero_mul, add_zero, sub_zero]; positivity)
    | positivity))

/-! ### The dominating function -/

theorem integrableOn_inv_sqrt : IntegrableOn (fun x : ℝ => (√x)⁻¹) (Ioo 0 1) := by
  refine ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(1 / 2 : ℝ)) zero_lt_one).mpr
    (by norm_num)).congr_fun (fun x hx => rpow_neg_half' hx.1) measurableSet_Ioo

theorem integrableOn_inv_sqrt_one_sub : IntegrableOn (fun x : ℝ => (√(1 - x))⁻¹) (Ioo 0 1) := by
  have h := ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (show -1 < -(1 / 2 : ℝ) by norm_num)).comp_sub_left 1).symm
  simp only [sub_zero, sub_self] at h
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioo
  exact rpow_neg_half' (by linarith [hx.2])

theorem inv_sqrt_mul_le {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    (√Y * √(1 - Y))⁻¹ ≤ (√Y)⁻¹ + (√(1 - Y))⁻¹ := by
  have ha : 0 < √Y := sqrt_pos.mpr hY.1
  have hb : 0 < √(1 - Y) := sqrt_pos.mpr (by linarith [hY.2])
  have ha2 : √Y ^ 2 = Y := sq_sqrt hY.1.le
  have hb2 : √(1 - Y) ^ 2 = 1 - Y := sq_sqrt (by linarith [hY.2])
  have hab : 1 ≤ √Y + √(1 - Y) := by nlinarith [mul_pos ha hb]
  rw [mul_inv, show (√Y)⁻¹ + (√(1 - Y))⁻¹ = (√Y)⁻¹ * (√(1 - Y))⁻¹ * (√Y + √(1 - Y)) by
    field_simp; ring]
  exact le_mul_of_one_le_right (by positivity) hab

theorem integrableOn_inv_sqrt_mul :
    IntegrableOn (fun Y : ℝ => (√Y * √(1 - Y))⁻¹) (Ioo 0 1) := by
  refine (integrableOn_inv_sqrt.add integrableOn_inv_sqrt_one_sub).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun Y : ℝ => (√Y * √(1 - Y))⁻¹).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with Y hY
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_sqrt_mul_le hY

/-- The `(y₃, y₄)`-factor `1/((y₃ + y₄) √g)` of the dominating function. -/
noncomputable def cornerW (p : ℝ × ℝ) : ℝ := ((p.1 + p.2) * √(cornerG p.1 p.2))⁻¹

theorem cornerMaj_eq (y3 y4 x : ℝ) : cornerMaj y3 y4 x = cornerW (y3, y4) * (√x)⁻¹ := by
  simp only [cornerMaj, cornerW, mul_inv]
  ring

/-- **The dominating function is integrable on the triangle**: in `(Y, ξ)` it is
`1/(√Y √(1-Y) √ξ)`. -/
theorem integrableOn_cornerW : IntegrableOn cornerW innerTriangle := by
  rw [integrableOn_triangle_iff]
  have hprod : IntegrableOn (fun q : ℝ × ℝ => (√q.1 * √(1 - q.1))⁻¹ * (√q.2)⁻¹) unitSquare := by
    rw [unitSquare, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integrableOn_inv_sqrt_mul.mul_prod integrableOn_inv_sqrt
  refine hprod.congr_fun (fun q hq => ?_) measurableSet_unitSquare
  obtain ⟨⟨hY0, hY1⟩, hξ0, -⟩ := hq
  have e1 : q.1 * q.2 + (q.1 - q.1 * q.2) = q.1 := by ring
  have e2 : cornerG (q.1 * q.2) (q.1 - q.1 * q.2) = q.1 * q.2 * (1 - q.1) := by
    unfold cornerG; ring
  simp only [yxiMap, cornerW, e1, e2]
  have h1Y : 0 < 1 - q.1 := by linarith
  rw [sqrt_mul (by positivity), sqrt_mul (by positivity)]
  have := sqrt_pos.mpr hY0
  have := sqrt_pos.mpr hξ0
  have := sqrt_pos.mpr h1Y
  field_simp

/-! ### Dominated convergence -/

/-- The bound on the `x`-integral, uniform in `λ² ≤ 1`. -/
theorem norm_integral_cornerGm_le {C : ℝ}
    (hC : ∀ lam y3 y4 x : ℝ, lam ^ 2 ≤ 1 → 0 < y3 → 0 < y4 → y3 + y4 < 1 → 0 < x → x < 1 →
      |cornerGm lam lam y3 y4 x| ≤ C * cornerMaj y3 y4 x)
    {lam : ℝ} (hl : lam ^ 2 ≤ 1) {p : ℝ × ℝ} (hp : p ∈ innerTriangle) :
    ‖∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam p.1 p.2 x‖ ≤
      C * (∫ x in Ioo (0 : ℝ) 1, (√x)⁻¹) * cornerW p := by
  obtain ⟨h3, h4, hY⟩ := hp
  have hint : IntegrableOn (fun x => C * (cornerW p * (√x)⁻¹)) (Ioo 0 1) :=
    (integrableOn_inv_sqrt.const_mul _).const_mul _
  calc ‖∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam p.1 p.2 x‖ ≤
        ∫ x in Ioo (0 : ℝ) 1, C * (cornerW p * (√x)⁻¹) := by
        refine norm_integral_le_of_norm_le hint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        rw [Real.norm_eq_abs, ← cornerMaj_eq]
        exact hC lam p.1 p.2 x hl h3 h4 hY hx.1 hx.2
    _ = C * (∫ x in Ioo (0 : ℝ) 1, (√x)⁻¹) * cornerW p := by
        rw [integral_const_mul, integral_const_mul]; ring

theorem aestronglyMeasurable_integral_cornerGm (lam : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam p.1 p.2 x)
      (volume.restrict innerTriangle) :=
  (measurable_cornerGm_uncurry lam).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioo (0 : ℝ) 1)) |>.aestronglyMeasurable

/-- **The pointwise limit** of the `x`-integral, for `(y₃, y₄)` in the triangle. -/
theorem tendsto_integral_cornerGm {C : ℝ}
    (hC : ∀ lam y3 y4 x : ℝ, lam ^ 2 ≤ 1 → 0 < y3 → 0 < y4 → y3 + y4 < 1 → 0 < x → x < 1 →
      |cornerGm lam lam y3 y4 x| ≤ C * cornerMaj y3 y4 x)
    {p : ℝ × ℝ} (hp : p ∈ innerTriangle) :
    Tendsto (fun lam : ℝ => ∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam p.1 p.2 x) (𝓝[>] 0)
      (𝓝 (cornerZeroInt p)) := by
  obtain ⟨h3, h4, hY⟩ := hp
  refine tendsto_integral_filter_of_dominated_convergence (fun x => C * (cornerW p * (√x)⁻¹))
    (Eventually.of_forall fun lam => (measurable_cornerGm lam p.1 p.2).aestronglyMeasurable) ?_
    ((integrableOn_inv_sqrt.const_mul _).const_mul _) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, ← cornerMaj_eq]
    exact hC lam p.1 p.2 x (by nlinarith [hlam.1, hlam.2]) h3 h4 hY hx.1 hx.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (continuousAt_cornerGm h3 h4 hY hx.1 hx.2).tendsto.mono_left nhdsWithin_le_nhds

end QED.TwoLoop.UnitSCCornerMain

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCCornerMain QED.TwoLoop.UnitXGraph

/-- **`CornerMainLimit`**: the `x`-integral of `G_C` is integrable on the triangle, and
`∫_{y₃,y₄} ∫₀¹ G(λ, λ) dx → ∫_{y₃,y₄} ∫₀¹ G_C dx` as `λ → 0⁺`. -/
theorem cornerMainLimit : CornerMainLimit := by
  obtain ⟨C, hC⟩ := exists_abs_cornerGm_le
  have hB : Integrable (fun p => C * (∫ x in Ioo (0 : ℝ) 1, (√x)⁻¹) * cornerW p)
      (volume.restrict innerTriangle) :=
    integrableOn_cornerW.const_mul _
  refine ⟨?_, ?_⟩
  · refine hB.mono' (aestronglyMeasurable_integral_cornerGm 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_innerTriangle] with p hp
    exact norm_integral_cornerGm_le hC (by norm_num) hp
  · refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall aestronglyMeasurable_integral_cornerGm) ?_ hB ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
      filter_upwards [ae_restrict_mem measurableSet_innerTriangle] with p hp
      exact norm_integral_cornerGm_le hC (by nlinarith [hlam.1, hlam.2]) hp
    · filter_upwards [ae_restrict_mem measurableSet_innerTriangle] with p hp
      exact tendsto_integral_cornerGm hC hp

end QED.TwoLoop.UnitSCCorner

end
