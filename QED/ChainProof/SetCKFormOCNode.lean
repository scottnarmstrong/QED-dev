/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCAFub
public import QED.ChainProof.SetCKFormOCSplit

/-!
# Set (c), Stage K, closed forms: `H_oC` in node form

Helper level (no frozen statement). End of step 3 of the `ρ_oC` route (Stage K notes,
Session 29+). For `a, x ∈ (0, 1)` with the `Y`-integrand integrable, the `Y`-integral of the
outer-massive corner kernel splits (**`formOC_Y_split`**) as

`∫_Y formOCKer X = G_K(a, x) + G_A(a, x) + φ_X(a, x)`,

where `G_K = formOCGK`, `G_A = formOCGA` (the `Â`-increment) and
`φ_X = 1{x < X} (Â(a, x, 0) + x²/4 (1 - log D₀) - β_c log v(x, X))` (**`formOCPhi`**). With
`formOC_K_part` and `formOC_A_part`, for almost every `X ∈ (0, 1)` (**`formOC_scOutCH_node`**):

`H_oC(X) = 2 (∫_{X'} 1{X' < X} Q'(X') ∫ (I_K(X') + I_A(X')) + ∫ φ_X)`,

with `I_K = formOCIK`, `I_A = formOCIA`, and every integral finite.
-/

@[expose] public section

open Real Set Filter MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The `v`-independent remainder** `φ_X(a, x)`. -/
noncomputable def formOCPhi (X : ℝ) (q : ℝ × ℝ) : ℝ :=
  if q.2 < X then formOCAhR q.1 q.2 0 + q.2 ^ 2 / 4 * (1 - log (formOCD0 q.1 q.2)) -
    formOCbeta q.1 q.2 * log (scOutVX q.2 X) else 0

section

variable {X a x : ℝ}

/-- **The `Y`-integral of the kernel, split.** -/
theorem formOC_Y_split (hX : X < 1) (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hint : IntegrableOn (fun Y => formOCKer X (Y, a, x)) (Ioo 0 1)) :
    ∫ Y in Ioo (0 : ℝ) 1, formOCKer X (Y, a, x) =
      formOCGK X (a, x) + formOCGA X (a, x) + formOCPhi X (a, x) := by
  by_cases h : x < X
  · have hv : 0 < scOutVX x X := sub_pos.2 (setCKQ_lt hx.1.le h hX)
    obtain ⟨hki, hkv⟩ := formOC_integral_kap ha hx hv
    obtain ⟨hpi, hpv⟩ := formOC_integral_P ha hx
    have e : EqOn (fun Y => formOCKer X (Y, a, x)) (fun Y => (Y * scOutCK (cornerC0 x)
        (cornerC1 x (a * Y) (Y - a * Y)) (cornerC2 x (a * Y) (Y - a * Y))
        (cornerC3 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x) (a * Y * (Y - a * Y))
        (scOutRho x) (scOutCs Y (a * Y) x) (scOutVX x X) +
        Y * scOutCkap (cornerA0 x (a * Y) (Y - a * Y)) (cornerA1 x (a * Y) (Y - a * Y))
          (cornerA2 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x) (a * Y * (Y - a * Y))
          (scOutRho x) (scOutCs Y (a * Y) x) (scOutVX x X)) +
        Y * -(cornerC0 x * scOutRho x * log (scOutCm Y (a * Y) x))) (Ioo 0 1) :=
      fun Y hY => formOC_ker_eq hY.1 ha.2 h
    have hint' := hint.congr_fun e measurableSet_Ioo
    have hKi : IntegrableOn (fun Y => Y * scOutCK (cornerC0 x) (cornerC1 x (a * Y) (Y - a * Y))
        (cornerC2 x (a * Y) (Y - a * Y)) (cornerC3 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x)
        (a * Y * (Y - a * Y)) (scOutRho x) (scOutCs Y (a * Y) x) (scOutVX x X)) (Ioo 0 1) :=
      ((hint'.sub hpi).sub hki).congr_fun (fun Y _ => by
      simp only [Pi.sub_apply]
      ring) measurableSet_Ioo
    have h1 := integral_add (hKi.add hki) hpi
    have h2 := integral_add hKi hki
    simp only [Pi.add_apply] at h1
    rw [setIntegral_congr_fun measurableSet_Ioo e, h1, h2, hkv, hpv]
    have hA := formOCAh_eq ha hx hv
    unfold formOCAh at hA
    simp only [formOCGK, formOCGA, formOCPhi, h, ↓reduceIte]
    linarith
  · have e : ∀ Y, formOCKer X (Y, a, x) = 0 := fun Y => by
      simp only [formOCKer, scOutCKer]
      rw [ite_eq_right_iff.2 fun h' => absurd h'.2 h, mul_zero]
    simp only [e, integral_zero, formOCGK, formOCGA, formOCPhi, h, ↓reduceIte, add_zero]

/-- **`H_oC` in node form.** -/
theorem formOC_scOutCH_node :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Integrable (formOCPhi X) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1))) ∧
      (∀ᵐ X' ∂(volume.restrict (Ioo (0 : ℝ) 1)), X' < X →
        Integrable (formOCIK X') ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1))) ∧
        Integrable (formOCIA X') ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)))) ∧
      scOutCH X = 2 * ((∫ X' in Ioo (0 : ℝ) 1, if X' < X then setCKdQ X' *
          ∫ q, formOCIK X' q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
            (volume.restrict (Ioo (0 : ℝ) 1))) else 0) +
        (∫ X' in Ioo (0 : ℝ) 1, if X' < X then setCKdQ X' *
          ∫ q, formOCIA X' q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
            (volume.restrict (Ioo (0 : ℝ) 1))) else 0) +
        ∫ q, formOCPhi X q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  filter_upwards [formOC_scOutCH_ae_eq, ae_restrict_mem measurableSet_Ioo] with X hX hXm
  obtain ⟨hKi, hIK, hKv⟩ := formOC_K_part hXm
  obtain ⟨hAi, hIA, hAv⟩ := formOC_A_part hXm
  have hin := formOC_integrable_swap hX.1
  have hsplit : (fun q => ∫ Y in Ioo (0 : ℝ) 1, formOCKer X (Y, q)) =ᵐ[(volume.restrict
      (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))]
      fun q => formOCGK X q + formOCGA X q + formOCPhi X q := by
    filter_upwards [formOC_ae_mem2, hX.1.prod_left_ae] with q hq hY
    exact formOC_Y_split hXm.2 hq.1 hq.2 hY
  have hPhi : Integrable (formOCPhi X) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
    refine ((hin.sub hKi).sub hAi).congr ?_
    filter_upwards [hsplit] with q hq
    simp only [Pi.sub_apply, hq]
    ring
  refine ⟨hPhi, ?_, ?_⟩
  · filter_upwards [hIK, hIA] with X' h1 h2 hlt
    exact ⟨h1 hlt, h2 hlt⟩
  · rw [hX.2, integral_prod_symm _ hX.1, integral_congr_ae hsplit,
      integral_add (f := fun q => formOCGK X q + formOCGA X q) (hKi.add hAi) hPhi,
      integral_add hKi hAi, hKv, hAv]

end

end QED.ChainProof.SetCK

end
