/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerErrDom
public import QED.TwoLoop.UnitXCloseYXi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner error terms: the joint limit

With the domination and the pointwise decay of `QED/TwoLoop/UnitSCCornerErrDom.lean`:

* `integrableOn_cornerErrDom`: the dominating function `20 - 3 log y₃ - 6 log(1 - Y) + 1/Y + 5/(Y √g)`
  is integrable on the triangle (in the variables `(Y, ξ)` of
  `QED.TwoLoop.UnitXClose.integrableOn_triangle_iff` it is a sum of products of integrable functions
  of one variable, with `1/√(Y(1-Y)) ≤ 1/√Y + 1/√(1-Y)`);
* `integrable_cornerErr`: for `0 < λ ≤ 1 ≤ Λ` the error integrand `e(λ, Λ) + O(Λ; λ, Λ)` is
  integrable on the triangle times `(0, 1)`;
* `tendsto_integral_cornerErr`: **`∫_{y₃,y₄} ∫₀¹ (e(λ, Λ) + O(Λ; λ, Λ)) dx → 0` as
  `(λ, Λ) → (0⁺, ∞)`**, by dominated convergence on the product.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Function

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitXClose

/-! ### One-variable integrability on `(0, 1)` -/

theorem integrableOn_inv_sqrt : IntegrableOn (fun Y : ℝ => 1 / √Y) (Ioo (0 : ℝ) 1) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (by norm_num : (-1 : ℝ) < -(1 / 2))).1
  refine (h.mono_set Ioo_subset_Ioc_self).congr_fun (fun Y hY => ?_) measurableSet_Ioo
  show Y ^ (-(1 / 2 : ℝ)) = 1 / √Y
  rw [Real.rpow_neg hY.1.le, ← Real.sqrt_eq_rpow, one_div]

theorem integrableOn_inv_sqrt_one_sub :
    IntegrableOn (fun Y : ℝ => 1 / √(1 - Y)) (Ioo (0 : ℝ) 1) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := 0)
    (by norm_num : (-1 : ℝ) < -(1 / 2))).comp_sub_left 1
  simp only [sub_self, sub_zero] at h
  have h' := h.1
  refine (h'.mono_set Ioo_subset_Ioc_self).congr_fun (fun Y hY => ?_) measurableSet_Ioo
  have : 0 ≤ 1 - Y := by linarith [hY.2]
  show (1 - Y) ^ (-(1 / 2 : ℝ)) = 1 / √(1 - Y)
  rw [Real.rpow_neg this, ← Real.sqrt_eq_rpow, one_div]

theorem integrableOn_abs_log : IntegrableOn (fun Y : ℝ => |log Y|) (Ioo (0 : ℝ) 1) := by
  have h := intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h
  exact h.abs

theorem integrableOn_abs_log_one_sub :
    IntegrableOn (fun Y : ℝ => |log (1 - Y)|) (Ioo (0 : ℝ) 1) := by
  have h := intervalIntegrable_log_one_sub
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h
  exact h.abs

theorem integrableOn_const_unit (c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Ioo (0 : ℝ) 1) :=
  integrableOn_const (by simp)

/-! ### The dominating function is integrable on the triangle -/

/-- The majorant of `Y · cornerErrDom(Y ξ, Y (1 - ξ))` on the unit square. -/
noncomputable def cornerErrMaj (p : ℝ × ℝ) : ℝ :=
  21 * 1 + |log p.1| * 3 + 1 * (3 * |log p.2|) + |log (1 - p.1)| * 6 +
    (5 * (1 / √p.1 + 1 / √(1 - p.1))) * (1 / √p.2)

theorem integrableOn_cornerErrMaj : IntegrableOn cornerErrMaj unitSquare := by
  unfold IntegrableOn unitSquare
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have i1 := integrableOn_const_unit 1
  have t1 := (integrableOn_const_unit 21).mul_prod i1
  have t2 := integrableOn_abs_log.mul_prod (integrableOn_const_unit 3)
  have t3 := (integrableOn_const_unit 1).mul_prod (integrableOn_abs_log.const_mul 3)
  have t4 := integrableOn_abs_log_one_sub.mul_prod (integrableOn_const_unit 6)
  have t5 := ((integrableOn_inv_sqrt.add integrableOn_inv_sqrt_one_sub).const_mul 5).mul_prod
    integrableOn_inv_sqrt
  exact (((t1.add t2).add t3).add t4).add t5

theorem one_div_sqrt_mul_le {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    1 / (√Y * √(1 - Y)) ≤ 1 / √Y + 1 / √(1 - Y) := by
  have h1 := Real.sqrt_pos.2 hY.1
  have h2 := Real.sqrt_pos.2 (by linarith [hY.2] : (0 : ℝ) < 1 - Y)
  have hs : 1 ≤ √Y + √(1 - Y) := by
    have e1 := Real.sq_sqrt hY.1.le
    have e2 := Real.sq_sqrt (by linarith [hY.2] : (0 : ℝ) ≤ 1 - Y)
    nlinarith [mul_pos h1 h2]
  rw [div_add_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h1 h2]

theorem cornerErrDom_yxi_le {p : ℝ × ℝ} (hp : p ∈ unitSquare) :
    ‖p.1 * cornerErrDom (yxiMap p).1 (yxiMap p).2‖ ≤ cornerErrMaj p := by
  unfold cornerErrMaj
  obtain ⟨⟨hY0, hY1⟩, hξ0, hξ1⟩ := hp
  set Y := p.1
  set ξ := p.2
  have e : cornerErrDom (yxiMap p).1 (yxiMap p).2 = 20 - 3 * log (Y * ξ) - 6 * log (1 - Y) +
      1 / Y + 5 / (Y * √(Y * ξ * (1 - Y))) := by
    have eY : (yxiMap p).1 + (yxiMap p).2 = Y := by simp only [yxiMap, Y]; ring
    have eg : cornerG (yxiMap p).1 (yxiMap p).2 = Y * ξ * (1 - Y) := by
      simp only [yxiMap, cornerG, Y, ξ]; ring
    unfold cornerErrDom
    rw [eY, eg]
    rfl
  rw [e]
  have h1Y : 0 < 1 - Y := by linarith
  have hlY : log Y ≤ 0 := log_nonpos hY0.le hY1.le
  have hlξ : log ξ ≤ 0 := log_nonpos hξ0.le hξ1.le
  have hl1Y : log (1 - Y) ≤ 0 := log_nonpos h1Y.le (by linarith)
  have hlog : log (Y * ξ) = log Y + log ξ := log_mul hY0.ne' hξ0.ne'
  have hsq : √(Y * ξ * (1 - Y)) = √Y * √ξ * √(1 - Y) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hY0.le]
  have hsY := Real.sqrt_pos.2 hY0
  have hsξ := Real.sqrt_pos.2 hξ0
  have hs1Y := Real.sqrt_pos.2 h1Y
  have e5 : Y * (5 / (Y * (√Y * √ξ * √(1 - Y)))) = 5 * (1 / (√Y * √(1 - Y))) * (1 / √ξ) := by
    field_simp
  have hnonneg : 0 ≤ Y * (20 - 3 * log (Y * ξ) - 6 * log (1 - Y) + 1 / Y +
      5 / (Y * √(Y * ξ * (1 - Y)))) := by
    rw [hlog]
    have : 0 ≤ 5 / (Y * √(Y * ξ * (1 - Y))) := by positivity
    have : 0 ≤ 1 / Y := by positivity
    have : 0 ≤ 20 - 3 * (log Y + log ξ) - 6 * log (1 - Y) + 1 / Y +
        5 / (Y * √(Y * ξ * (1 - Y))) := by linarith
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hsq, mul_add, e5, hlog]
  have hmaj := one_div_sqrt_mul_le ⟨hY0, hY1⟩
  have k5 : 5 * (1 / (√Y * √(1 - Y))) * (1 / √ξ) ≤ 5 * (1 / √Y + 1 / √(1 - Y)) * (1 / √ξ) := by
    gcongr
  rw [abs_of_nonpos hlY, abs_of_nonpos hlξ, abs_of_nonpos hl1Y]
  have : Y * (1 / Y) = 1 := by field_simp
  have : Y * (20 - 3 * (log Y + log ξ) - 6 * log (1 - Y)) ≤
      20 - 3 * log Y - 3 * log ξ - 6 * log (1 - Y) := by
    have : 0 ≤ -3 * log Y - 3 * log ξ - 6 * log (1 - Y) := by linarith
    nlinarith
  rw [mul_add Y]
  linarith

theorem measurable_cornerErrDom : Measurable fun p : ℝ × ℝ => cornerErrDom p.1 p.2 := by
  unfold cornerErrDom cornerG
  fun_prop

/-- **The dominating function is integrable on the triangle.** -/
theorem integrableOn_cornerErrDom :
    IntegrableOn (fun p : ℝ × ℝ => cornerErrDom p.1 p.2) innerTriangle := by
  rw [integrableOn_triangle_iff]
  refine Integrable.mono' integrableOn_cornerErrMaj ?_ ?_
  · have : Measurable fun x : ℝ × ℝ => x.1 * cornerErrDom (yxiMap x).1 (yxiMap x).2 := by
      have hy : Measurable yxiMap := by unfold yxiMap; fun_prop
      exact measurable_fst.mul (measurable_cornerErrDom.comp hy)
    exact this.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_unitSquare] with p hp
    exact cornerErrDom_yxi_le hp

/-! ### Measurability -/

theorem measurable_cornerE (lam Lam : ℝ) :
    Measurable fun q : (ℝ × ℝ) × ℝ => cornerE lam Lam q.1.1 q.1.2 q.2 := by
  unfold cornerE cornerGm cForm cornerA0 cornerA1 cornerA2 cornerC0 cornerC1 cornerC2 cornerC3
    cornerQ cornerR cornerG cornerMass betaG ladderInnerMass UnitSCReduce.cornerP1
    UnitSCReduce.cornerP2
  fun_prop

theorem measurable_cornerAX (la lb : ℝ) :
    Measurable fun r : ((ℝ × ℝ) × ℝ) × ℝ => cornerAX la lb r.1.1.1 r.1.1.2 r.1.2 r.2 := by
  simp only [cornerAX, UnitSCReduce.cornerTerm, UnitSCReduce.gCW, UnitSCReduce.gCM1,
    UnitSCReduce.gCM2, UnitSCReduce.gCU, UnitSCReduce.gCE, UnitSCReduce.gCEn, cornerG,
    UnitSCGraph.cpM1pa, UnitSCGraph.cpM1pb, UnitSCGraph.cpM1pc, UnitSCGraph.cpM1pd,
    UnitSCGraph.cpM2pa, UnitSCGraph.cpM2pb, UnitSCGraph.cpM2pc, UnitSCGraph.cpM2pd]
  fun_prop

theorem measurable_cornerOut_integrand (lam Lam : ℝ) :
    Measurable (uncurry fun (q : (ℝ × ℝ) × ℝ) (z : ℝ) =>
      cornerAX Lam lam q.1.1 q.1.2 q.2 (z + betaG (cornerG q.1.1 q.1.2) (q.1.1 * q.1.2) q.2) -
        cornerAX Lam Lam q.1.1 q.1.2 q.2 (z + betaG (cornerG q.1.1 q.1.2) (q.1.1 * q.1.2) q.2)) := by
  have hφ : Measurable fun r : ((ℝ × ℝ) × ℝ) × ℝ =>
      (r.1, r.2 + betaG (cornerG r.1.1.1 r.1.1.2) (r.1.1.1 * r.1.1.2) r.1.2) := by
    unfold betaG cornerG; fun_prop
  exact ((measurable_cornerAX Lam lam).comp hφ).sub ((measurable_cornerAX Lam Lam).comp hφ)

theorem stronglyMeasurable_cornerOut (lam Lam : ℝ) :
    StronglyMeasurable fun q : (ℝ × ℝ) × ℝ => cornerOut Lam lam Lam q.1.1 q.1.2 q.2 := by
  unfold cornerOut
  exact (measurable_cornerOut_integrand lam Lam).stronglyMeasurable.integral_prod_right

/-! ### Dominated convergence on the product -/

/-- The measure `dy₃ dy₄ dx` on the triangle times `(0, 1)`. -/
noncomputable abbrev cornerErrMeasure : Measure ((ℝ × ℝ) × ℝ) :=
  (volume.restrict innerTriangle).prod (volume.restrict (Ioo (0 : ℝ) 1))

theorem ae_mem_cornerErrMeasure :
    ∀ᵐ q ∂cornerErrMeasure, q.1 ∈ innerTriangle ∧ q.2 ∈ Ioo (0 : ℝ) 1 := by
  rw [cornerErrMeasure, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_innerTriangle.prod measurableSet_Ioo)] with q hq
  exact hq

theorem integrable_cornerErrDom_prod :
    Integrable (fun q : (ℝ × ℝ) × ℝ => cornerErrDom q.1.1 q.1.2) cornerErrMeasure := by
  have := integrableOn_cornerErrDom.mul_prod (integrableOn_const_unit 1)
  simpa only [mul_one] using this

theorem aestronglyMeasurable_cornerErr (lam Lam : ℝ) :
    AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      cornerE lam Lam q.1.1 q.1.2 q.2 + cornerOut Lam lam Lam q.1.1 q.1.2 q.2) cornerErrMeasure :=
  ((measurable_cornerE lam Lam).stronglyMeasurable.add
    (stronglyMeasurable_cornerOut lam Lam)).aestronglyMeasurable

theorem ae_abs_cornerErr_le {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam) :
    ∀ᵐ q ∂cornerErrMeasure, ‖cornerE lam Lam q.1.1 q.1.2 q.2 +
      cornerOut Lam lam Lam q.1.1 q.1.2 q.2‖ ≤ cornerErrDom q.1.1 q.1.2 := by
  filter_upwards [ae_mem_cornerErrMeasure] with q hq
  obtain ⟨⟨h3, h4, hY⟩, hx⟩ := hq
  rw [Real.norm_eq_abs]
  exact abs_cornerErr_le_dom hlam hlam1 hLam hx h3 h4 hY

/-- **The error integrand is integrable** on the triangle times `(0, 1)` (`0 < λ ≤ 1 ≤ Λ`). -/
theorem integrable_cornerErr {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam) :
    Integrable (fun q : (ℝ × ℝ) × ℝ =>
      cornerE lam Lam q.1.1 q.1.2 q.2 + cornerOut Lam lam Lam q.1.1 q.1.2 q.2) cornerErrMeasure :=
  integrable_cornerErrDom_prod.mono' (aestronglyMeasurable_cornerErr lam Lam)
    (ae_abs_cornerErr_le hlam hlam1 hLam)

/-- **The error terms vanish in the joint limit**:
`∫_{y₃,y₄} ∫₀¹ (e(λ, Λ) + O(Λ; λ, Λ)) dx → 0` as `(λ, Λ) → (0⁺, ∞)`. -/
theorem tendsto_integral_cornerErr :
    Tendsto (fun p : ℝ × ℝ => ∫ q in innerTriangle, ∫ x in Ioo (0 : ℝ) 1,
      (cornerE p.1 p.2 q.1 q.2 x + cornerOut p.2 p.1 p.2 q.1 q.2 x)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  have hl : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, p.1 ∈ Ioo (0 : ℝ) 1 ∧ 1 ≤ p.2 :=
    hl.prod_mk (eventually_ge_atTop 1)
  have hD := tendsto_integral_filter_of_dominated_convergence (μ := cornerErrMeasure)
    (l := 𝓝[>] (0 : ℝ) ×ˢ atTop)
    (F := fun p q => cornerE p.1 p.2 q.1.1 q.1.2 q.2 + cornerOut p.2 p.1 p.2 q.1.1 q.1.2 q.2)
    (f := fun _ => 0) (fun q => cornerErrDom q.1.1 q.1.2)
    (Eventually.of_forall fun p => aestronglyMeasurable_cornerErr p.1 p.2)
    (hev.mono fun p hp => ae_abs_cornerErr_le hp.1.1 hp.1.2.le hp.2)
    integrable_cornerErrDom_prod
    (by
      filter_upwards [ae_mem_cornerErrMeasure] with q hq
      obtain ⟨⟨h3, h4, hY⟩, hx⟩ := hq
      exact tendsto_cornerErr hx h3 h4 hY)
  rw [integral_zero] at hD
  refine hD.congr' ?_
  filter_upwards [hev] with p hp
  exact integral_prod _ (integrable_cornerErr hp.1.1 hp.1.2.le hp.2)

end QED.TwoLoop.UnitSCCorner

end
