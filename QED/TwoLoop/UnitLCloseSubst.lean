/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLCloseMasters
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder graph half after the integration over the outer electron parameter

Section 3.3 of `docs/TWO-LOOP-UNITS.md`, stage (2) of the L link, step 1, assembled. Starting
from the graph half in the variables of eq. (3.1)
(`QED.TwoLoop.UnitLGraphReduce.sixteen_pi_pow_four_mul_graphHalf_eq_doc`), substitute
`z_a = a(1-x)/x` at fixed `a = z_A + Y(1-Y)` (`integral_Ioi_eq_subst`), exchange the order of the
integrations over `z_A` and `x` (Fubini, `integral_subst_swap`; the integrability on the new
domain is transported from the old one slice by slice), and integrate over `z_A` by the masters
(`QED.TwoLoop.UnitLLink.hasIoiInt_ladderAX_sub`), keeping the sum over the inner photon masses
inside the integral. The result:

* `sixteen_pi_pow_four_mul_graphHalf_eq_gsum`: for `m = e = 1` and `0 < m_γ < Λ`,
  `16π⁴ · graphHalf P = ∫_{0<Y<1} ∫_{0<x<1} G_Σ(Y, x)`, with
  `G_Σ = G(m_γ, m_γ) - G(m_γ, Λ) - G(Λ, m_γ) + G(Λ, Λ)` (`ladderGSum`), `G(la, lb)` the
  `x`-integrand of eq. (3.4) at outer photon mass `la` and inner photon mass `lb`
  (`ladderGm`).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.TwoLoop.UnitLLink

open QED.TwoLoop.UnitLGraphReduce QED.WickModel

/-! ### The substitution `z_a = a (1 - x)/x` -/

section Subst

variable {a : ℝ}

theorem image_subst (ha : 0 < a) : (fun x => a * (1 - x) / x) '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext z
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    have : 0 < 1 - x := by linarith
    positivity
  · intro hz
    refine ⟨a / (a + z), ⟨by positivity, (div_lt_one (by positivity)).mpr (by linarith)⟩, ?_⟩
    have : a + z ≠ 0 := by positivity
    field_simp
    ring

theorem injOn_subst (ha : 0 < a) : InjOn (fun x => a * (1 - x) / x) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  simp only at hxy
  have := hx.1.ne'
  have := hy.1.ne'
  field_simp at hxy
  linear_combination -hxy

theorem hasDerivWithinAt_subst {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fun x => a * (1 - x) / x) (-(a / x ^ 2)) (Ioo 0 1) x := by
  have hx0 := hx.1.ne'
  have : HasDerivAt (fun x => a * (1 - x) / x)
      (((a * (0 - 1)) * x - a * (1 - x) * 1) / x ^ 2) x :=
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).const_mul a).div (hasDerivAt_id x) hx0
  refine (this.congr_deriv ?_).hasDerivWithinAt
  field_simp
  ring

theorem abs_subst_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    |-(a / x ^ 2)| = a / x ^ 2 := by
  have := hx.1
  rw [abs_neg, abs_of_pos (by positivity)]

/-- **The substitution `z_a = a(1-x)/x`**: `∫_{z_a > 0} f = ∫_0^1 f(a(1-x)/x) a/x² dx`. -/
theorem integral_Ioi_eq_subst (ha : 0 < a) (f : ℝ → ℝ) :
    ∫ z in Ioi (0 : ℝ), f z = ∫ x in Ioo (0 : ℝ) 1, f (a * (1 - x) / x) * (a / x ^ 2) := by
  rw [← image_subst ha, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => hasDerivWithinAt_subst hx) (injOn_subst ha)]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  simp only [abs_subst_deriv hx ha, smul_eq_mul]
  ring

theorem integrableOn_Ioi_iff_subst (ha : 0 < a) (f : ℝ → ℝ) :
    IntegrableOn f (Ioi 0) ↔
      IntegrableOn (fun x => f (a * (1 - x) / x) * (a / x ^ 2)) (Ioo (0 : ℝ) 1) := by
  rw [← image_subst ha, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun x hx => hasDerivWithinAt_subst hx) (injOn_subst ha)]
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioo
  simp only [abs_subst_deriv hx ha, smul_eq_mul]
  ring

end Subst

/-! ### Exchange of the integrations over `z_A` and `x` -/

/-- The integrand after the substitution `z_a = (z_A + c)(1-x)/x`, with its Jacobian. -/
noncomputable def substT (F : ℝ → ℝ → ℝ) (c zA x : ℝ) : ℝ :=
  F zA ((zA + c) * (1 - x) / x) * ((zA + c) / x ^ 2)

/-- **Fubini after the substitution**: if `F` is integrable on `(0, ∞)²`, then the substituted
integrand is integrable on `(0, ∞) × (0, 1)` and
`∫_{z_A > 0} ∫_{z_a > 0} F = ∫_0^1 dx ∫_{z_A > 0} F(z_A, (z_A + c)(1-x)/x) (z_A + c)/x² dz_A`. -/
theorem integral_subst_swap {F : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hF : Measurable (uncurry F))
    (hint : Integrable (uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ))))) :
    Integrable (uncurry (substT F c)) ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) ∧
      ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ), F zA za =
        ∫ x in Ioo (0 : ℝ) 1, ∫ zA in Ioi (0 : ℝ), substT F c zA x := by
  have hmeas : Measurable (uncurry (substT F c)) := by
    change Measurable fun p : ℝ × ℝ => F p.1 ((p.1 + c) * (1 - p.2) / p.2) * ((p.1 + c) / p.2 ^ 2)
    have h1 : Measurable fun p : ℝ × ℝ => (p.1 + c) * (1 - p.2) / p.2 := by fun_prop
    have h2 : Measurable fun p : ℝ × ℝ => (p.1 + c) / p.2 ^ 2 := by fun_prop
    exact (hF.comp (measurable_fst.prodMk h1)).mul h2
  have hpos : ∀ zA ∈ Ioi (0 : ℝ), 0 < zA + c := fun zA hz => by
    simp only [mem_Ioi] at hz; linarith
  have hT : Integrable (uncurry (substT F c)) ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [hint.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with zA hzA hz
      exact (integrableOn_Ioi_iff_subst (hpos zA hz) (F zA)).mp hzA
    · refine hint.integral_norm_prod_left.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with zA hz
      change ∫ za in Ioi (0 : ℝ), ‖F zA za‖ = ∫ x in Ioo (0 : ℝ) 1, ‖substT F c zA x‖
      rw [integral_Ioi_eq_subst (hpos zA hz) (fun za => ‖F zA za‖)]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have := hx.1
      have := hpos zA hz
      simp only [substT, norm_mul, Real.norm_eq_abs (_ / _), abs_of_pos (by positivity :
        0 < (zA + c) / x ^ 2)]
  refine ⟨hT, ?_⟩
  rw [← integral_integral_swap hT]
  refine setIntegral_congr_fun measurableSet_Ioi fun zA hz => ?_
  exact integral_Ioi_eq_subst (hpos zA hz) (F zA)

/-! ### The graph half -/

/-- **The `x`-integrand after the `a`-integration, summed over the photon masses with the
Pauli–Villars signs**: `G(m_γ, m_γ) - G(m_γ, Λ) - G(Λ, m_γ) + G(Λ, Λ)` (outer mass first). -/
noncomputable def ladderGSum (mγ Λ Y x : ℝ) : ℝ :=
  ladderGm mγ mγ Y x - ladderGm mγ Λ Y x - ladderGm Λ mγ Y x + ladderGm Λ Λ Y x

theorem measurable_ladderDocSum (P : Params) (Y : ℝ) :
    Measurable (uncurry fun zA za => ladderDocSum P Y zA za) := by
  change Measurable fun p : ℝ × ℝ => ladderDocSum P Y p.1 p.2
  unfold ladderDocSum ladderDocF
  fun_prop

theorem substT_ladderDocSum (P : Params) (Y x zA : ℝ) :
    substT (fun zA za => ladderDocSum P Y zA za) (Y * (1 - Y)) zA x =
      (ladderAX P.mγ P.mγ Y x (zA + Y * (1 - Y)) - ladderAX P.mγ P.Λ Y x (zA + Y * (1 - Y))) -
        (ladderAX P.Λ P.mγ Y x (zA + Y * (1 - Y)) - ladderAX P.Λ P.Λ Y x (zA + Y * (1 - Y))) := by
  simp only [substT, ladderDocSum, ladderAX]
  ring

/-- The inner integral over `z_A` is `G_Σ(Y, x)`. -/
theorem integral_substT_ladderDocSum (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {Y x : ℝ}
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ zA in Ioi (0 : ℝ), substT (fun zA za => ladderDocSum P Y zA za) (Y * (1 - Y)) zA x =
      ladderGSum P.mγ P.Λ Y x := by
  have h := (hasIoiInt_ladderAX_sub hY hx hmγ hmγ hΛ).sub (hasIoiInt_ladderAX_sub hY hx hΛ hmγ hΛ)
  simp only [substT_ladderDocSum]
  rw [h.2, ladderGSum]
  ring

/-- For almost every `Y ∈ (0, 1)`, the slice of the integrand of eq. (3.1) is integrable on
`(0, ∞)²`. -/
theorem ae_integrable_ladderDocSum_slice {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    ∀ᵐ Y ∂(volume.restrict (Ioo (0 : ℝ) 1)), Integrable (uncurry fun zA za => ladderDocSum P Y zA za)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨hI, -⟩ := sixteen_pi_pow_four_mul_graphHalf_eq_doc hm he hmγ hΛ
  have he' := QED.Integration.ChengWu.measurePreserving_splitOne.symm
  have hint := (he'.integrableOn_comp_preimage
    QED.Integration.ChengWu.splitOne.symm.measurableEmbedding).mpr hI
  rw [QED.Integration.ChengWu.preimage_splitOne_symm] at hint
  have hint' : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      ladderDocSum P (QED.Integration.ChengWu.splitOne.symm q 1)
        (QED.Integration.ChengWu.splitOne.symm q 0) (QED.Integration.ChengWu.splitOne.symm q 2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]; exact hint
  filter_upwards [hint'.prod_right_ae] with Y hY
  refine hY.congr (ae_of_all _ fun p => ?_)
  simp [QED.Integration.ChengWu.splitOne_symm_apply, uncurry]

/-- **The ladder graph half after the `a`-integration** (`m = e = 1`, `0 < m_γ < Λ`):
`16π⁴ · graphHalf P = ∫_{0<Y<1} ∫_{0<x<1} G_Σ(Y, x)`. -/
theorem sixteen_pi_pow_four_mul_graphHalf_eq_gsum {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    16 * (π : ℂ) ^ 4 * graphHalf P =
      ((∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, ladderGSum P.mγ P.Λ Y x : ℝ) : ℂ) := by
  rw [sixteen_pi_pow_four_mul_graphHalf_eq_doc_iterated hm he hmγ hΛ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_integrable_ladderDocSum_slice hm he hmγ hΛ,
    ae_restrict_mem measurableSet_Ioo] with Y hY hYm
  have hc : 0 < Y * (1 - Y) := mul_pos hYm.1 (by linarith [hYm.2])
  rw [(integral_subst_swap hc (measurable_ladderDocSum P Y) hY).2]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  exact integral_substT_ladderDocSum P hmγ (hmγ.trans hΛ) hYm hx

end QED.TwoLoop.UnitLLink

end
