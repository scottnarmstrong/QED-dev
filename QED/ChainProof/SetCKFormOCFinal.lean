/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCDone
public import QED.ChainProof.SetCKFormOCH4

/-!
# Set (c), Stage K: the value, unconditionally

Helper level (no frozen statement). The `a`-integral of the closed form `G`
(`integral_formOCG_eq`, `SetCKFormOCH4`) is the one input of `setCKDisp_eq_aSetC_of_formOCG_int`
(`SetCKFormOCDone`). With it:

* **`isSetCKStieltjes_proved`**: the Stieltjes identity (S) of the set (c) kernel,
  `A_(c)(t) = ∫₀¹ λ⁽⁴⁾(x) Q(x)/(Q(x) + t) dx` for every `t > 0`, holds;
* **`setCKDisp_eq_aSetC_proved`**: the set (c) dispersion integral equals `aSetC`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

/-- **The Stieltjes identity (S)** for the set (c) kernels. -/
theorem isSetCKStieltjes_proved : IsSetCKStieltjes :=
  isSetCKStieltjes_of_scOutCH (formOC_scOutCH_ae_eq_of_int fun _ hX => integral_formOCG_eq hX)

/-- **Set (c)'s value**: `setCKDisp = aSetC`, with no hypotheses. -/
theorem setCKDisp_eq_aSetC_proved : setCKDisp = QED.Chain.aSetC :=
  setCKDisp_eq_aSetC_of_formOCG_int fun _ hX => integral_formOCG_eq hX

end QED.ChainProof.SetCK

end
