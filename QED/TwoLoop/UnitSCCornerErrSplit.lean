/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerErrLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner error terms: integrability of the corner graph half

The `x`-integrand `G_Σ = cornerGSum` of the corner graph half comes from the model integrand
`cornerF4`, which is integrable on the triangle times `(0, ∞)²`
(`QED.TwoLoop.UnitSCReduce.sixteen_pi_pow_four_mul_openZero_Cp_eq_chengWu`). This file transfers that
integrability through the exchange of the integrations (`QED.TwoLoop.UnitSCLimit.integral_substB_swap`)
(`integrable_cornerGSum`): for `0 < λ ≤ 1`, `λ < Λ`,

* for almost every `(y₃, y₄)` in the triangle, `x ↦ G_Σ(λ, Λ; y₃, y₄, x)` is integrable on `(0, 1)`;
* `(y₃, y₄) ↦ ∫₀¹ G_Σ dx` is integrable on the triangle.

These are what allow the integral of `G_Σ` to be split into the main term, the counterterm
logarithm and the error terms.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory Function

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink QED.TwoLoop.UnitXGraph QED.WickModel
open QED.TwoLoop.UnitSCReduce

/-- The parameters at `m = e = 1` with photon masses `λ`, `Λ` (the other fields play no role). -/
def cornerParams (lam Lam : ℝ) : Params where
  e := 1
  δ₁ := 0
  δ₂ := 0
  δm := 0
  δ₃ := 0
  m := 1
  mγ := lam
  Λ := Lam
  ε := 0
  M₁ := 0
  M₂ := 0
  c₁ := 0
  c₂ := 0

/-- The model integrand on the triangle times `(0, ∞)²`. -/
theorem integrable_cornerF4_prod {lam Lam : ℝ} (hlam : 0 < lam) (hΛ : lam < Lam) :
    Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      cornerF4 (cornerParams lam Lam) ![q.2.1, q.1.1, q.1.2, q.2.2, 1 - (q.1.1 + q.1.2)])
      ((volume.restrict innerTriangle).prod
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) := by
  set P := cornerParams lam Lam
  obtain ⟨hI, -⟩ := sixteen_pi_pow_four_mul_openZero_Cp_eq_chengWu (P := P) rfl rfl hlam hΛ
  have he' := measurePreserving_splitInner.symm
  have hint := (he'.integrableOn_comp_preimage splitInner.symm.measurableEmbedding).mpr hI
  rw [preimage_splitInner_symm] at hint
  have hint' : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      cornerF4 P (Fin.snoc (splitInner.symm q) (1 - (splitInner.symm q 1 + splitInner.symm q 2))))
      ((volume.restrict innerTriangle).prod
        ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]; exact hint
  rw [Measure.prod_restrict (Ioi (0 : ℝ)) (Ioi (0 : ℝ))]
  refine hint'.congr (ae_of_all _ fun q => ?_)
  simp only [splitInner_symm_apply]
  rfl

/-- After the exchange of the integrations, the inner `z`-integral of the model integrand is
`G_Σ` for almost every `x`. -/
theorem ae_integral_substB_eq {lam Lam y3 y4 : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1)
    (hp : Integrable (uncurry fun zo za =>
      cornerF4 (cornerParams lam Lam) ![zo, y3, y4, za, 1 - (y3 + y4)])
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) :
    (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∫ z in Ioi (0 : ℝ),
      substB (fun zo za => cornerF4 (cornerParams lam Lam) ![zo, y3, y4, za, 1 - (y3 + y4)])
        (cornerG y3 y4) (y3 * y4) x z = cornerGSum lam Lam y3 y4 x) := by
  set P := cornerParams lam Lam
  have hg := cornerG_pos h3 hY
  obtain ⟨hae, -⟩ := integral_substB_swap hg (mul_pos h3 h4) (measurable_cornerSlice P y3 y4) hp
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  have hm2 : P.mγ ^ 2 ≤ 1 := by
    show lam ^ 2 ≤ 1
    nlinarith
  have hin := hasIoiInt_cornerAX_sub h3 hY hxm (show 0 < P.mγ from hlam)
    (cornerMass_pos h3 h4 hY.le hm2) (cornerMass_pos h3 h4 hY.le hm2) (lb₁ := P.mγ) (lb₂ := P.Λ)
  have hout : IntegrableOn (fun z =>
      cornerAX P.Λ P.mγ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x) -
        cornerAX P.Λ P.Λ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x)) (Ioi 0) := by
    refine (hin.1.sub hx).congr_fun (fun z _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, substB_cornerSlice]
    ring
  have e : (fun z => substB (fun zo za => cornerF4 P ![zo, y3, y4, za, 1 - (y3 + y4)])
      (cornerG y3 y4) (y3 * y4) x z) = fun z =>
      (cornerAX P.mγ P.mγ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x) -
          cornerAX P.mγ P.Λ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x)) -
        (cornerAX P.Λ P.mγ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x) -
          cornerAX P.Λ P.Λ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x)) := by
    funext z
    exact substB_cornerSlice P y3 y4 x z
  rw [e, integral_sub hin.1 hout, hin.2, cornerGSum, cornerOut]
  rfl

/-- **The corner graph half is integrable** (`0 < λ ≤ 1`, `λ < Λ`): `x ↦ G_Σ` on `(0, 1)` for almost
every point of the triangle, and its `x`-integral on the triangle. -/
theorem integrable_cornerGSum {lam Lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hΛ : lam < Lam) :
    (∀ᵐ y ∂(volume.restrict innerTriangle),
      IntegrableOn (cornerGSum lam Lam y.1 y.2) (Ioo (0 : ℝ) 1)) ∧
    IntegrableOn (fun y : ℝ × ℝ => ∫ x in Ioo (0 : ℝ) 1, cornerGSum lam Lam y.1 y.2 x)
      innerTriangle := by
  set P := cornerParams lam Lam
  have hint := integrable_cornerF4_prod hlam hΛ
  refine ⟨?_, ?_⟩
  · filter_upwards [hint.prod_right_ae, ae_restrict_mem measurableSet_innerTriangle] with y hy hym
    obtain ⟨h3, h4, hY⟩ := hym
    have hp : Integrable (uncurry fun zo za =>
        cornerF4 P ![zo, y.1, y.2, za, 1 - (y.1 + y.2)])
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := hy
    have hT := integrable_substH (cornerG_pos h3 hY) (mul_pos h3 h4)
      (measurable_cornerSlice P y.1 y.2) hp
    refine hT.integral_prod_right.congr ?_
    filter_upwards [ae_integral_substB_eq hlam hlam1 h3 h4 hY hp,
      ae_restrict_mem measurableSet_Ioo] with x hx hxm
    simp only [uncurry_apply_pair]
    rw [integral_substH_eq_substB hxm, hx]
  · refine hint.integral_prod_left.congr ?_
    filter_upwards [hint.prod_right_ae, ae_restrict_mem measurableSet_innerTriangle] with y hy hym
    obtain ⟨h3, h4, hY⟩ := hym
    have hp : Integrable (uncurry fun zo za =>
        cornerF4 P ![zo, y.1, y.2, za, 1 - (y.1 + y.2)])
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := hy
    have hsw := (integral_substB_swap (cornerG_pos h3 hY) (mul_pos h3 h4)
      (measurable_cornerSlice P y.1 y.2) hp).2
    change ∫ q, (uncurry fun zo za => cornerF4 P ![zo, y.1, y.2, za, 1 - (y.1 + y.2)]) q
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) = _
    rw [integral_prod _ hp]
    simp only [uncurry_apply_pair]
    rw [hsw]
    exact integral_congr_ae (ae_integral_substB_eq hlam hlam1 h3 h4 hY hp)

end QED.TwoLoop.UnitSCCorner

end
