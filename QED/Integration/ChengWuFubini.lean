/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.ChengWu
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Iterated integrals over a three-dimensional Cheng–Wu domain

For `g` integrable on `D = chengWuSet 1 = {w ∈ ℝ³ : w₀ > 0, 0 < w₁ < 1, w₂ > 0}`,
`∫_D g = ∫₀¹ dY ∫₀^∞ dz_A ∫₀^∞ dz_a g(z_A, Y, z_a)` (`integral_chengWuSet_one`), Fubini through
the measure-preserving `ℝ³ ≃ ℝ × ℝ × ℝ`, `w ↦ (w₁, w₀, w₂)`.
-/

public section

open MeasureTheory Set

namespace QED.Integration.ChengWu

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The measurable equivalence `w ↦ (w₁, (w₀, w₂))`. -/
noncomputable def splitOne : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)

theorem measurePreserving_splitOne :
    MeasurePreserving splitOne volume (volume.prod (volume.prod volume)) :=
  ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 1)

theorem splitOne_symm_apply (q : ℝ × (ℝ × ℝ)) : splitOne.symm q = ![q.2.1, q.1, q.2.2] := by
  funext i
  fin_cases i <;> rfl

theorem preimage_splitOne_symm :
    splitOne.symm ⁻¹' chengWuSet (1 : Fin 3) = Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  ext q
  simp only [Set.mem_preimage, splitOne_symm_apply, mem_chengWuSet, Fin.forall_fin_succ,
    Set.mem_prod, Set.mem_Ioo, Set.mem_Ioi]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  constructor
  · rintro ⟨⟨h0, h1, h2, -⟩, h3⟩
    exact ⟨⟨h1, h3⟩, h0, h2⟩
  · rintro ⟨⟨h1, h3⟩, h0, h2⟩
    exact ⟨⟨h0, h1, h2, fun i => i.elim0⟩, h3⟩

/-- **Fubini on the Cheng–Wu domain**:
`∫_{chengWuSet 1} g = ∫₀¹ dY ∫₀^∞ dz_A ∫₀^∞ dz_a g(z_A, Y, z_a)` for `g` integrable. -/
theorem integral_chengWuSet_one {g : (Fin 3 → ℝ) → E}
    (hg : IntegrableOn g (chengWuSet (1 : Fin 3))) :
    ∫ w in chengWuSet (1 : Fin 3), g w =
      ∫ Y in Ioo (0 : ℝ) 1, ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ), g ![zA, Y, za] := by
  have he := measurePreserving_splitOne.symm
  have h1 := he.setIntegral_preimage_emb splitOne.symm.measurableEmbedding g (chengWuSet 1)
  have hint := (he.integrableOn_comp_preimage splitOne.symm.measurableEmbedding).mpr hg
  rw [preimage_splitOne_symm] at h1 hint
  rw [← h1, setIntegral_prod (fun q => g (splitOne.symm q)) hint]
  have hint' : Integrable (fun q : ℝ × (ℝ × ℝ) => g (splitOne.symm q))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]; exact hint
  refine integral_congr_ae ?_
  filter_upwards [hint'.prod_right_ae] with Y hY
  rw [setIntegral_prod _ hY]
  simp only [splitOne_symm_apply]

end QED.Integration.ChengWu

end
