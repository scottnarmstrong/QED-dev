/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerErrSplit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner error terms: `CornerErrLimit`

Sections 2.3 and 6.3 of `docs/TWO-LOOP-UNITS.md`. The corner part minus its main term,
`C(λ, Λ) - 2 ∫_{y₃,y₄} ∫₀¹ G(λ, λ)`, is (`cornerErr_eq`, for `0 < λ ≤ 1 ≤ Λ`, `λ < Λ`)

`-2 ∫_{y₃,y₄} ∫₀¹ (e(λ, Λ) + O(Λ; λ, Λ)) dx`,

since `G_Σ = G(λ, λ) + ℓ_C log M_Λ - (e + O)` pointwise and the counterterm logarithm cancels:
`∫₀¹ ℓ_C dx = F₂⁽²⁾(λ)/2` (`QED.TwoLoop.UnitSCCorner.integral_cornerEll`) and
`∫_{y₃,y₄} log M_Λ(y₃ + y₄) = ∫₀¹ Y log M_Λ(Y) dY` (`integral_triangle_logMass`). The splitting
uses the integrability of `G_Σ` from the model (`QED.TwoLoop.UnitSCCorner.integrable_cornerGSum`) and
of the error terms (`QED.TwoLoop.UnitSCCorner.integrable_cornerErr`). With
`QED.TwoLoop.UnitSCCorner.tendsto_integral_cornerErr` this proves

* `cornerErrLimit : CornerErrLimit`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Function

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitXClose

/-! ### The coefficient of the counterterm logarithm -/

theorem integrableOn_cornerEll (lam : ℝ) :
    IntegrableOn (fun x => cornerC0 x / (ladderInnerMass 1 lam x / x)) (Ioo (0 : ℝ) 1) := by
  refine Integrable.mono' (integrableOn_const_unit (1 / 2)) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    unfold cornerC0 ladderInnerMass
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hh := selfH_ge (μ := lam) hx
    have hc := cornerC0_nonneg hx
    have hx0 := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hc (hx0.le.trans hh))]
    calc cornerC0 x / (ladderInnerMass 1 lam x / x) ≤ cornerC0 x / x :=
          div_le_div_of_nonneg_left hc hx0 hh
      _ ≤ 1 / 2 := by
          unfold cornerC0
          rw [div_le_iff₀ hx0]
          nlinarith

theorem setIntegral_cornerEll {lam : ℝ} (hlam : 0 < lam) :
    ∫ x in Ioo (0 : ℝ) 1, cornerC0 x / (ladderInnerMass 1 lam x / x) = oneLoopF2 1 lam / 2 := by
  rw [← integral_cornerEll hlam, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

/-! ### The counterterm logarithm on the triangle -/

theorem volume_innerTriangle_lt_top : volume innerTriangle < ⊤ := by
  have hsub : innerTriangle ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := fun p hp => by
    obtain ⟨h1, h2, h3⟩ := hp
    exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩⟩
  refine (measure_mono hsub).trans_lt ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem integrableOn_logMass_triangle {Lam : ℝ} (hLam : 1 ≤ Lam) :
    IntegrableOn (fun p : ℝ × ℝ => log (ladderInnerMass 1 Lam (p.1 + p.2))) innerTriangle := by
  refine Integrable.mono' (integrableOn_const (C := 1 + log (Lam ^ 2))
    volume_innerTriangle_lt_top.ne) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    unfold ladderInnerMass
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_innerTriangle] with p hp
    obtain ⟨h3, h4, hY⟩ := hp
    have hL2 : 1 ≤ Lam ^ 2 := by nlinarith
    have hlo : 3 / 4 ≤ ladderInnerMass 1 Lam (p.1 + p.2) := by
      unfold ladderInnerMass
      nlinarith [sq_nonneg (p.1 + p.2 - 1 / 2)]
    have hhi : ladderInnerMass 1 Lam (p.1 + p.2) ≤ Lam ^ 2 := by
      unfold ladderInnerMass
      nlinarith
    have hm : 0 < ladderInnerMass 1 Lam (p.1 + p.2) := by linarith
    have l1 : log (ladderInnerMass 1 Lam (p.1 + p.2)) ≤ log (Lam ^ 2) := log_le_log hm hhi
    have l2 : -1 ≤ log (ladderInnerMass 1 Lam (p.1 + p.2)) := by
      have := log_le_sub_one_of_pos (inv_pos.2 hm)
      rw [log_inv] at this
      have : (ladderInnerMass 1 Lam (p.1 + p.2))⁻¹ ≤ 4 / 3 := by
        rw [inv_le_comm₀ hm (by norm_num)]; linarith
      linarith
    have l3 : 0 ≤ log (Lam ^ 2) := log_nonneg hL2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith

/-- `∫_{y₃,y₄} log M_Λ(y₃ + y₄) = ∫₀¹ Y log M_Λ(Y) dY`. -/
theorem integral_triangle_logMass {Lam : ℝ} (hLam : 1 ≤ Lam) :
    ∫ p in innerTriangle, log (ladderInnerMass 1 Lam (p.1 + p.2)) =
      ∫ Y in (0 : ℝ)..1, Y * log (ladderInnerMass 1 Lam Y) := by
  rw [integral_triangle_eq_yxi (integrableOn_logMass_triangle hLam),
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun Y _ => ?_
  have e : ∀ ξ : ℝ, Y * log (ladderInnerMass 1 Lam (Y * ξ + Y * (1 - ξ))) =
      Y * log (ladderInnerMass 1 Lam Y) := fun ξ => by
    rw [show Y * ξ + Y * (1 - ξ) = Y by ring]
  simp only [e, setIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal zero_le_one,
    one_smul, measureReal_def]

/-! ### The splitting -/

theorem cornerGSum_eq_split (lam Lam y3 y4 x : ℝ) :
    cornerGSum lam Lam y3 y4 x = cornerGm lam lam y3 y4 x +
      cornerC0 x / (ladderInnerMass 1 lam x / x) * log (ladderInnerMass 1 Lam (y3 + y4)) -
      (cornerE lam Lam y3 y4 x + cornerOut Lam lam Lam y3 y4 x) := by
  unfold cornerGSum cornerE
  ring

/-- **The corner part minus its main term is the error integral** (`0 < λ ≤ 1 ≤ Λ`, `λ < Λ`). -/
theorem cornerErr_eq {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hLam : 1 ≤ Lam)
    (hΛ : lam < Lam) :
    cornerPart lam Lam - 2 * ∫ q in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam q.1 q.2 x =
      -2 * ∫ q in innerTriangle, ∫ x in Ioo (0 : ℝ) 1,
        (cornerE lam Lam q.1 q.2 x + cornerOut Lam lam Lam q.1 q.2 x) := by
  obtain ⟨haeS, hIS⟩ := integrable_cornerGSum hlam hlam1 hΛ
  have hErr := integrable_cornerErr hlam hlam1 hLam
  have haeE := hErr.prod_right_ae
  have hIE := hErr.integral_prod_left
  have hell := integrableOn_cornerEll lam
  have hellI := setIntegral_cornerEll hlam
  have hLM := integrableOn_logMass_triangle hLam
  set ell := fun x => cornerC0 x / (ladderInnerMass 1 lam x / x) with hell_def
  have hpt : ∀ᵐ y ∂(volume.restrict innerTriangle),
      ∫ x in Ioo (0 : ℝ) 1, cornerGSum lam Lam y.1 y.2 x =
        (∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam y.1 y.2 x) +
          log (ladderInnerMass 1 Lam (y.1 + y.2)) * (oneLoopF2 1 lam / 2) -
          ∫ x in Ioo (0 : ℝ) 1, (cornerE lam Lam y.1 y.2 x + cornerOut Lam lam Lam y.1 y.2 x) := by
    filter_upwards [haeS, haeE] with y hS hE
    have hE' : IntegrableOn (fun x => cornerE lam Lam y.1 y.2 x + cornerOut Lam lam Lam y.1 y.2 x)
        (Ioo (0 : ℝ) 1) := hE
    have hellM := hell.mul_const (log (ladderInnerMass 1 Lam (y.1 + y.2)))
    have hG : IntegrableOn (fun x => cornerGm lam lam y.1 y.2 x) (Ioo (0 : ℝ) 1) := by
      refine ((hS.sub hellM).add hE').congr_fun (fun x _ => ?_) measurableSet_Ioo
      simp only [Pi.add_apply, Pi.sub_apply, cornerGSum_eq_split, hell_def]
      ring
    have e : (fun x => cornerGSum lam Lam y.1 y.2 x) = fun x => (cornerGm lam lam y.1 y.2 x +
        ell x * log (ladderInnerMass 1 Lam (y.1 + y.2))) -
        (cornerE lam Lam y.1 y.2 x + cornerOut Lam lam Lam y.1 y.2 x) := by
      funext x; rw [cornerGSum_eq_split]
    have hGB : IntegrableOn (fun x => cornerGm lam lam y.1 y.2 x +
        ell x * log (ladderInnerMass 1 Lam (y.1 + y.2))) (Ioo (0 : ℝ) 1) := hG.add hellM
    rw [e, integral_sub hGB hE', integral_add hG hellM, integral_mul_const, hellI]
    ring
  have hIE' : IntegrableOn (fun y : ℝ × ℝ => ∫ x in Ioo (0 : ℝ) 1,
      (cornerE lam Lam y.1 y.2 x + cornerOut Lam lam Lam y.1 y.2 x)) innerTriangle := hIE
  have hIG : IntegrableOn (fun y : ℝ × ℝ => ∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam y.1 y.2 x)
      innerTriangle := by
    refine ((hIS.sub (hLM.mul_const (oneLoopF2 1 lam / 2))).add hIE').congr ?_
    filter_upwards [hpt] with y hy
    simp only [Pi.add_apply, Pi.sub_apply, hy]
    ring
  have hsplit : ∫ y in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGSum lam Lam y.1 y.2 x =
      (∫ y in innerTriangle, ∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam y.1 y.2 x) +
        (∫ y in innerTriangle, log (ladderInnerMass 1 Lam (y.1 + y.2))) * (oneLoopF2 1 lam / 2) -
        ∫ y in innerTriangle, ∫ x in Ioo (0 : ℝ) 1,
          (cornerE lam Lam y.1 y.2 x + cornerOut Lam lam Lam y.1 y.2 x) := by
    have hGL : IntegrableOn (fun y : ℝ × ℝ => (∫ x in Ioo (0 : ℝ) 1, cornerGm lam lam y.1 y.2 x) +
        log (ladderInnerMass 1 Lam (y.1 + y.2)) * (oneLoopF2 1 lam / 2)) innerTriangle :=
      hIG.add (hLM.mul_const _)
    rw [integral_congr_ae hpt, integral_sub hGL hIE', integral_add hIG (hLM.mul_const _),
      integral_mul_const]
  rw [cornerPart, hsplit, integral_triangle_logMass hLam]
  ring

/-- **The error terms of the corner part vanish in the joint limit.** -/
theorem cornerErrLimit : CornerErrLimit := by
  unfold CornerErrLimit
  have h := tendsto_integral_cornerErr.const_mul (-2)
  rw [mul_zero] at h
  refine h.congr' ?_
  have hl : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [hl.prod_mk (eventually_ge_atTop (2 : ℝ))] with p hp
  obtain ⟨⟨h0, h1⟩, h2⟩ := hp
  exact (cornerErr_eq h0 h1.le (by linarith) (by linarith)).symm

end QED.TwoLoop.UnitSCCorner

end
