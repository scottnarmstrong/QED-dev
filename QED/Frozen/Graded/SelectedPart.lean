/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.GradedOrder
public import QED.Frozen.Graded.ContractionValue
public import QED.Frozen.WickModel.FermionSign
public import QED.Frozen.Wick.VertexKindFintype

@[expose] public section

open QED.WickModel (Params Contraction fermionSign)

namespace QED.Graded

open scoped Classical in
/-- (G₆) **The part of order exactly `K` of a selected sum of graded Wick terms** (successor of
(F₈) and (C₂); plan Q5 (ii): order separation by definition). The sum over the terms of
`exp(i ∫ L₁) = ∑_N (i ∫ L₁)^N / N!`, with `L₁` the gauge vertex and the counterterm vertices of
every level and flavour, whose graded vertex sequence `(κ, g)` has order (G₂″) exactly `K`, over
the contractions `C` with `Sel C g`, of `1/N!` times the fermionic sign (X₅) times the value
(G₅). Every vertex has order at least `1`, so `N ≤ K`; every level is at most `K`, so the
finite range `0, …, K` of each level loses no term. Because the coefficients are
`e^{2(k+1)} d` with `e`-free `d`, the result is `e^K` times an `e`-independent number (theorem
(G-hom)). The selection may read the grading (needed for later families, ruling S5). -/
noncomputable def selectedPart (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Grading κ → Prop)
    (K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ : Fin N → Wick.VertexKind,
      ∑ g ∈ (Fintype.piFinset fun _ : CtVertex κ => Finset.range (K + 1)).filter
          (fun g => gradedOrder κ g = K),
        ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => Sel C g),
          ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D C g pOut pIn kIn αOut βIn μ

end QED.Graded

end
