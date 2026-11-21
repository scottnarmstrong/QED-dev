/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCNInt
public import QED.ChainProof.SetCKFormOCAFub

/-!
# Set (c), Stage K, closed forms: `J_K + J_A = ∫₀¹ N(a, X') da`

Helper level (no frozen statement). Item 4 of the `ρ_oC` route (Stage K notes, Session 30+).
The node form of `H_oC` (`formOC_scOutCH_node`) carries, at each `X'`, the `(a, x)`-integrals
`J_K = ∫ formOCIK X'` and `J_A = ∫ formOCIA X'` over `(0, 1)²`. By Fubini (`a` outer) and since
both vanish for `x ≥ X'`, **`formOC_JK_add_JA`**: if both are integrable and `X' < 1`, then
`(a ↦ formOCN a X')` is integrable on `(0, 1)` and `J_K + J_A = ∫_{a ∈ (0, 1)} formOCN a X'`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

section

variable {X' : ℝ}

/-- The `x`-section of `formOCIK + formOCIA` is the `N`-integrand cut at `X'`. -/
theorem formOC_IKA_section (a : ℝ) (hX' : X' < 1) :
    ∫ x in Ioo (0 : ℝ) 1, (formOCIK X' (a, x) + formOCIA X' (a, x)) = formOCN a X' := by
  have e : (fun x => formOCIK X' (a, x) + formOCIA X' (a, x)) = (Iio X').indicator
      (fun x => formOCgk x a (scOutVX x X') + formOCSA a x (scOutVX x X')) := by
    funext x
    by_cases h : x < X'
    · simp [formOCIK, formOCIA, h]
    · simp [formOCIK, formOCIA, h]
  have es : Ioo (0 : ℝ) 1 ∩ Iio X' = Ioo 0 X' := by
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨⟨h0, -⟩, h1⟩
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      exact ⟨⟨h0, by linarith⟩, h1⟩
  rw [e, setIntegral_indicator measurableSet_Iio, es, formOCN]

/-- **`J_K + J_A = ∫₀¹ N(a, X') da`.** -/
theorem formOC_JK_add_JA (hX' : X' < 1)
    (hK : Integrable (formOCIK X') ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))))
    (hA : Integrable (formOCIA X') ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)))) :
    IntegrableOn (fun a => formOCN a X') (Ioo 0 1) ∧
      (∫ q, formOCIK X' q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)))) +
        ∫ q, formOCIA X' q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1))) = ∫ a in Ioo (0 : ℝ) 1, formOCN a X' := by
  have hKA : Integrable (fun q => formOCIK X' q + formOCIA X' q)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := hK.add hA
  have e : (fun a => ∫ x in Ioo (0 : ℝ) 1, (formOCIK X' (a, x) + formOCIA X' (a, x))) =
      fun a => formOCN a X' := funext fun a => formOC_IKA_section a hX'
  refine ⟨?_, ?_⟩
  · have h := hKA.integral_prod_left
    rw [e] at h
    exact h
  · rw [← integral_add hK hA, integral_prod _ hKA, e]

end

end QED.ChainProof.SetCK

end
