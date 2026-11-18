/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseLimit
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The massless crossed-ladder integrand: Fubini in the hierarchical variables

Given that `T(0, 0)` is integrable on `Δ₄` (from the domination,
`QED.TwoLoop.UnitXClose.tendsto_integral_crossedFour`), the Cheng–Wu change of variables makes
`(z₂, z₃, z_A, z_a) ↦ T(0, 0)(z_A, z₂, z₃, z_a, 1 - z₂ - z₃)` integrable on
`triangle × (0, ∞)²`, so for almost every `(z₂, z₃)` in the triangle:

* `a ↦ T(0, 0)` is integrable on `(0, ∞)` for almost every `z_A > 0`;
* `z_A ↦ ∫₀^∞ T(0, 0) dz_a` is integrable on `(0, ∞)`
  (`ae_integrableOn_inner`). These are the hypotheses of the fundamental theorem of calculus on
  `(0, ∞)` used for the outer integrations of section 4.2 of `docs/TWO-LOOP-UNITS.md`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace QED.TwoLoop.UnitXClose

open QED.TwoLoop.UnitXGraph
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- The massless integrand in the order `((z₂, z₃), (z_A, z_a))`. -/
noncomputable def crossedZeroH (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  crossedTerm 0 0 q.2.1 q.1.1 q.1.2 q.2.2 (1 - (q.1.1 + q.1.2))

/-- **Integrability on `triangle × (0, ∞)²`**, given integrability on `Δ₄`. -/
theorem integrableOn_crossedZeroH
    (hI : IntegrableOn (fun y => crossedZero (simplexPoint y)) (simplexSet 4)) :
    Integrable crossedZeroH ((volume.restrict innerTriangle).prod
      ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) := by
  have hF : ∀ z : Fin 5 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      crossedZero (t • z) = (t ^ 5)⁻¹ • crossedZero z := fun z hz t ht => crossedZero_smul hz ht
  have hCWi := (integrableOn_simplex_chengWuSet_iff (by norm_num) innerSet crossedZero hF).mp hI
  simp only [sum_innerSet] at hCWi
  have he := measurePreserving_splitInner.symm
  have hint := (he.integrableOn_comp_preimage splitInner.symm.measurableEmbedding).mpr hCWi
  rw [preimage_splitInner_symm] at hint
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  refine hint.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.comp_apply, splitInner_symm_apply]
  rfl

/-- **Fubini for the two outer integrations**: for almost every `(z₂, z₃)` in the triangle,
`z_a ↦ T(0, 0)` is integrable on `(0, ∞)` for almost every `z_A > 0`, and
`z_A ↦ ∫₀^∞ T(0, 0) dz_a` is integrable on `(0, ∞)`. -/
theorem ae_integrableOn_inner
    (hI : IntegrableOn (fun y => crossedZero (simplexPoint y)) (simplexSet 4)) :
    ∀ᵐ p ∂(volume.restrict innerTriangle),
      (∀ᵐ A ∂(volume.restrict (Ioi (0 : ℝ))),
        IntegrableOn (fun a => crossedTerm 0 0 A p.1 p.2 a (1 - (p.1 + p.2))) (Ioi 0)) ∧
      IntegrableOn (fun A => ∫ a in Ioi (0 : ℝ), crossedTerm 0 0 A p.1 p.2 a (1 - (p.1 + p.2)))
        (Ioi 0) := by
  filter_upwards [(integrableOn_crossedZeroH hI).prod_right_ae] with p hp
  rw [← Measure.prod_restrict] at hp
  exact ⟨hp.prod_right_ae, hp.integral_prod_left⟩

/-- **Two outer integrations by explicit antiderivatives**: if `H A` is an antiderivative of
`f A` on `(0, ∞)` tending to `0` at `∞` and continuous at `0⁺`, and `K` an antiderivative of
`A ↦ -H A 0` with the same properties, then `∫₀^∞ ∫₀^∞ f = -K 0`, given the integrability of
`f A` for almost every `A` and of `A ↦ ∫ f A`. -/
theorem iterated_Ioi_eq_of_prim {f H : ℝ → ℝ → ℝ} {K : ℝ → ℝ}
    (hH : ∀ A ∈ Ioi (0 : ℝ), ∀ a ∈ Ioi (0 : ℝ), HasDerivAt (H A) (f A a) a)
    (hH0 : ∀ A ∈ Ioi (0 : ℝ), ContinuousWithinAt (H A) (Ici 0) 0)
    (hHinf : ∀ A ∈ Ioi (0 : ℝ), Tendsto (H A) atTop (𝓝 0))
    (hK : ∀ A ∈ Ioi (0 : ℝ), HasDerivAt K (-H A 0) A) (hK0 : ContinuousWithinAt K (Ici 0) 0)
    (hKinf : Tendsto K atTop (𝓝 0))
    (hint1 : ∀ᵐ A ∂(volume.restrict (Ioi (0 : ℝ))), IntegrableOn (f A) (Ioi 0))
    (hint2 : IntegrableOn (fun A => ∫ a in Ioi (0 : ℝ), f A a) (Ioi 0)) :
    ∫ A in Ioi (0 : ℝ), ∫ a in Ioi (0 : ℝ), f A a = -K 0 := by
  have hae : (fun A => ∫ a in Ioi (0 : ℝ), f A a) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun A => -H A 0 := by
    filter_upwards [hint1, ae_restrict_mem measurableSet_Ioi] with A hA hA0
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (hH0 A hA0) (hH A hA0) hA (hHinf A hA0), zero_sub]
  rw [integral_congr_ae hae, integral_Ioi_of_hasDerivAt_of_tendsto hK0 hK
    (hint2.congr_fun_ae hae) hKinf, zero_sub]

end QED.TwoLoop.UnitXClose

end
