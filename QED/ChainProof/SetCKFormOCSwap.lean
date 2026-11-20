/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCFub

/-!
# Set (c), Stage K, closed forms: the outer-massive corner weight as an iterated integral

Helper level (no frozen statement). Step 1 of the `ρ_oC` route (Stage K notes, Session 29+).
For an integrable function `f` on the cube `(0, 1)³` with coordinates `(Y, (a, x))` and
`μ = volume|(0, 1)` (**`formOC_integral_swap`**):

`∫ f = ∫_x ∫_a ∫_Y f(Y, a, x)`,

and the inner `Y`-integral is integrable in `(a, x)` (**`formOC_integrable_swap`**). Applied to
`formOCKer X` this writes `H_oC(X)` as `2 ∫_x ∫_a ∫_Y` (**`formOC_scOutCH_ae_eq_iter`**).
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The inner `Y`-integral of an integrable function on the cube is integrable in `(a, x)`. -/
theorem formOC_integrable_swap {f : ℝ × ℝ × ℝ → ℝ}
    (hf : Integrable f ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))) :
    Integrable (fun q : ℝ × ℝ => ∫ Y in Ioo (0 : ℝ) 1, f (Y, q))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
  hf.integral_prod_right

/-- **The cube integral as the iterated integral `∫_x ∫_a ∫_Y`.** -/
theorem formOC_integral_swap {f : ℝ × ℝ × ℝ → ℝ}
    (hf : Integrable f ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))) :
    ∫ p, f p ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) =
      ∫ x in Ioo (0 : ℝ) 1, ∫ a in Ioo (0 : ℝ) 1, ∫ Y in Ioo (0 : ℝ) 1, f (Y, a, x) := by
  rw [integral_prod_symm f hf]
  exact integral_prod_symm (fun q : ℝ × ℝ => ∫ Y in Ioo (0 : ℝ) 1, f (Y, q))
    (formOC_integrable_swap hf)

/-- **`H_oC` as an iterated integral**: for almost every `X ∈ (0, 1)`,
`H_oC(X) = 2 ∫_x ∫_a ∫_Y formOCKer X (Y, a, x)`, and the `Y`-integral is integrable in
`(a, x)`. -/
theorem formOC_scOutCH_ae_eq_iter :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Integrable (fun q : ℝ × ℝ => ∫ Y in Ioo (0 : ℝ) 1, formOCKer X (Y, q))
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) ∧
        scOutCH X = 2 * ∫ x in Ioo (0 : ℝ) 1, ∫ a in Ioo (0 : ℝ) 1, ∫ Y in Ioo (0 : ℝ) 1,
          formOCKer X (Y, a, x) := by
  filter_upwards [formOC_scOutCH_ae_eq] with X hX
  exact ⟨formOC_integrable_swap hX.1, by rw [hX.2, formOC_integral_swap hX.1]⟩

end QED.ChainProof.SetCK

end
