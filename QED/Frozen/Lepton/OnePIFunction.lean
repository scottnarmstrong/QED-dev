/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.ContractionValue
public import QED.Frozen.WickModel.FermionSign
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.Wick.VertexKindOrder
public import QED.Frozen.Wick.VertexKindFintype

@[expose] public section

open QED.WickModel (Params Contraction IsOnePI fermionSign)

namespace QED.Lepton

open scoped Classical in
/-- (F₈) **The 1PI function with the flavours `Φ`**, the successor of (T₁₁): the sum over the 1PI
Wick contractions of the terms of `exp(i ∫ L₁)` of total order at most `K` in `e`, with the
factor `1/N!` and the fermionic signs, of the value (F₇). Source-facing as for (T₁₁):
`nf + nA ≥ 1`, `ε > 0`, momentum conservation and `K ≤ 2 nf + nA + 3`. -/
noncomputable def onePIFunction₂ (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F)
    (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ

end QED.Lepton

end
