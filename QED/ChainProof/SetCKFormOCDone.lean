/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCE
public import QED.ChainProof.SetCKFormOCG
public import QED.ChainProof.SetCKFormOCNFub
public import QED.ChainProof.SetCKAsmTot

/-!
# Set (c), Stage K: the outer corner identity from the `a`-integral of `G`

Helper level (no frozen statement). Instantiates the `ρ_oC` assembly
`scOutCH_ae_eq_setCKRhoH_of_formOCG` with `N = formOCN` (`formOC_JK_add_JA`) and `G = formOCG`
(`formOCG_eq`), and feeds the result to `setCKDisp_eq_aSetC_of_scOutCH`. The one remaining input
is the `a`-integral of the closed form `G` (item 5, the dilogarithm antiderivative):

* **`formOC_scOutCH_ae_eq_of_int`**: if `∫₀¹ G(a, X) da = ρ_oC(X) Q(X)/2` on `(0, 1)`, then
  `scOutCH = setCKRhoH rhoScOutC` a.e. on `(0, 1)`;
* **`setCKDisp_eq_aSetC_of_formOCG_int`**: under the same hypothesis, `setCKDisp = aSetC`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

/-- **The outer corner identity**, given the `a`-integral of `G`. -/
theorem formOC_scOutCH_ae_eq_of_int
    (hGi : ∀ X ∈ Ioo (0 : ℝ) 1, ∫ a in Ioo (0 : ℝ) 1, formOCG a X = rhoScOutC X * setCKQ X / 2) :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), scOutCH X = setCKRhoH rhoScOutC X :=
  scOutCH_ae_eq_setCKRhoH_of_formOCG (N := formOCN) (G := formOCG)
    (fun _ hX' hK hA => formOC_JK_add_JA hX' hK hA)
    (fun a ha h12 X hX => formOCG_eq ha (fun h => h12 (by linarith)) hX) hGi

/-- **Set (c)'s value**, given the `a`-integral of `G`. -/
theorem setCKDisp_eq_aSetC_of_formOCG_int
    (hGi : ∀ X ∈ Ioo (0 : ℝ) 1, ∫ a in Ioo (0 : ℝ) 1, formOCG a X = rhoScOutC X * setCKQ X / 2) :
    setCKDisp = QED.Chain.aSetC :=
  setCKDisp_eq_aSetC_of_scOutCH (formOC_scOutCH_ae_eq_of_int hGi)

end QED.ChainProof.SetCK

end
