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
/-- (C₂) **The 1PI function of a family of contractions** (decision D-49.4; plan Q3, O3-3): the
flavoured 1PI function (F₈) restricted to the contractions satisfying the family predicate `Fam`.
It is the text of (F₈) with the filter `IsOnePI` replaced by `IsOnePI ∧ Fam`: the sum over the
1PI Wick contractions in `Fam` of the terms of `exp(i ∫ L₁) = ∑_N (i ∫ L₁)^N / N!` of total order
at most `K` in `e`, with the factor `1/N!`, the fermionic sign (X₅) and the value (F₇) (all
flavours of a contraction summed inside one integrand, `L = loopCount C` loop momenta, joint
energy-first prescription at the fixed `ε`; `0` when a stage is not integrable). With
`Fam = True` it is (F₈) (theorem (M₁)). A family term is a term of (F₈): this is a partial sum,
with the coefficients of (F₈), not a new amplitude. Source-facing only for named families whose
proper divergent subgraphs are all one loop (the vacuum-polarization chains (C₁)), at `ε > 0`, with
momentum conservation, and with `K` the order of the family; it is not a renormalized amplitude
for other families, since the model's counterterms are single real numbers of order `e²`
(D-37.3). -/
noncomputable def onePIFamilyFunction₂ (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) (nf nA : ℕ)
    (Fam : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Prop)
    (K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K),
      ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => IsOnePI C ∧ Fam C),
        ((fermionSign C : ℤ) : ℂ) * contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ

end QED.Lepton

end
