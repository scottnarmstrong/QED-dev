/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOSK
public import QED.ChainProof.SetCKScOutSH
public import QED.ChainProof.SetCKValue

/-!
# Set (c), Stage K, closed forms: the outer self-energy group has the density `ρ_oS`

Helper level (no frozen statement). The weight `H_oS = scOutSH` of the outer self-energy group
(`SetCKScOutSH`, including the atom `X³(1 - X)/2`) is `H_ρ` of the closed-form density
`ρ_oS = rhoScOutS` (`SetCKFormOSK`):

**`scOutSH_ae_eq_setCKRhoH`**: `H_oS(X) = ∫₀^X ρ_oS Q` for almost every `X ∈ (0, 1)`.

Proof: at a node `X` where the kernel section `(Y, x) ↦ 1{x < X} W(Y, x, Q(X) - Q(x))` is
integrable on the square (almost every `X`, from the Fubini hypothesis
`integrable_scOutSKerT` at `t = 1`), Fubini gives `H_k(X) = ∫₀^X ∫₀¹ W dY dx`, the `Y`-integral
is `formOSF` (`integral_scOutSW_Y`), the `x`-integral is `E(X)` (`integral_formOSF_x`), and
`E(X) + X³(1 - X)/2 = K(X) = H_ρ(X)` (`setCKRhoH_rhoScOutS`)
(**`scOutSHk_eq_formOSE`**, a pointwise statement under the integrability hypothesis).

The a.e. form is what the value theorem consumes: **`isSetCKStieltjes_of_hTot_ae`** is
`isSetCKStieltjes_of_hTot` (`SetCKValue`) with the identity `H_tot = H_λ` required only almost
everywhere on `(0, 1)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.Chain QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The kernel part of `H_oS` at a node with an integrable section**: `H_k(X) = E(X)`. -/
theorem scOutSHk_eq_formOSE {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1)
    (hI : Integrable (fun p : ℝ × ℝ => scOutSKer p.1 p.2 X)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :
    scOutSHk X = formOSE X := by
  have hsec : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ Y in Ioo (0 : ℝ) 1, scOutSKer Y x X =
      (Iio X).indicator (fun x => formOSF x (setCKQ X - setCKQ x)) x := fun x hx => by
    by_cases h : x < X
    · have hv : 0 < setCKQ X - setCKQ x := sub_pos.2 (setCKQ_lt hx.1.le h hX.2)
      simp only [scOutSKer, h, ↓reduceIte, scOutVX, indicator_of_mem (show x ∈ Iio X from h)]
      exact (integral_scOutSW_Y hx hv).2
    · simp [scOutSKer, h]
  have hU : Ioo (0 : ℝ) 1 ∩ Iio X = Ioo 0 X := by
    ext y
    simp only [mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.trans hX.2⟩, h.2⟩
  unfold scOutSHk
  rw [integral_prod_symm _ hI, setIntegral_congr_fun measurableSet_Ioo hsec,
    setIntegral_indicator measurableSet_Iio, hU]
  exact (integral_formOSF_x hX).2

/-- Almost every node has an integrable kernel section. -/
theorem ae_integrable_scOutSKer :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Integrable (fun p : ℝ × ℝ => scOutSKer p.1 p.2 X)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  filter_upwards [(integrable_scOutSKerT one_pos).prod_left_ae,
    ae_restrict_mem measurableSet_Ioo] with X hI hX
  have hw : 0 < setCKdQ X / (setCKQ X + 1) ^ 2 := by
    have := setCKdQ_pos hX
    have := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
    positivity
  refine (hI.div_const (setCKdQ X / (setCKQ X + 1) ^ 2)).congr
    (Eventually.of_forall fun p => ?_)
  simp only [scOutSKerT]
  exact mul_div_cancel_right₀ _ hw.ne'

/-- **The outer self-energy group has the density `ρ_oS`**: `H_oS = H_ρ` a.e. on `(0, 1)`. -/
theorem scOutSH_ae_eq_setCKRhoH :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), scOutSH X = setCKRhoH rhoScOutS X := by
  filter_upwards [ae_integrable_scOutSKer, ae_restrict_mem measurableSet_Ioo] with X hI hX
  rw [scOutSH, scOutSHk_eq_formOSE hX hI, setCKRhoH_rhoScOutS hX, formOSK_eq]

/-- `isSetCKStieltjes_of_hTot` with the identity `H_tot = H_λ` almost everywhere on `(0, 1)`. -/
theorem isSetCKStieltjes_of_hTot_ae
    (hH : ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), setCKHTot X = setCKRhoH setCLambda X) :
    IsSetCKStieltjes := by
  intro t ht
  rw [setCKKernelSum_eq' ht, (setCKStieltjes_eq_rhoH ht (integrableOn_setCLambda_mul ht)).2,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact integral_congr_ae (hH.mono fun X hX => by simp only [hX])

end QED.ChainProof.SetCK

end
