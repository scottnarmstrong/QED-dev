/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPart
import QED.GradedProof.Homogeneity

/-!
# Provider for `QED.Graded.selectedPart_eq_pow_mul`

Proves the frozen theorem goal `QED.Graded.selectedPart_eq_pow_mul` (Phase 5 Stage 2 packet,
decision D-57) as `QED.Provider.Graded.selectedPart_eq_pow_mul`, with the binder convention of
decision D-13, from the helper in `QED.GradedProof.Homogeneity`. The anchor is sealed (D-57 seal
note).
-/

public section

open QED.WickModel (Params Contraction)
open QED.Graded

namespace QED.Provider.Graded

/-- The frozen goal with implicit data binders (decision D-13). -/
theorem selectedPart_eq_pow_mul {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {nf nA : ℕ}
    {Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Grading κ → Prop}
    {K : ℕ} {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    {αOut βIn : Fin nf → Fin 4} {μ : Fin nA → Fin 4} :
    selectedPart P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ =
      (P.e : ℂ) ^ K * selectedPart { P with e := 1 } Φ D nf nA Sel K pOut pIn kIn αOut βIn μ :=
  QED.GradedProof.selectedPart_eq_pow_mul' P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ

end QED.Provider.Graded

end
