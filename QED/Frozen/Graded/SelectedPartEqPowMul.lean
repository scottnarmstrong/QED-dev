-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPart
public import QED.Provider.Graded.SelectedPartEqPowMul

@[expose] public section

open QED.WickModel (Params Contraction)

namespace QED.Graded

/-- (G-hom) **Order separation is definitional** (plan Q5 (ii); ruling S3; the graded successor
of obligation O2-27): the order-`K` part (G₆) at charge `e` is `e^K` times the same part at
`e = 1`, for every selection, all data and all external arguments. So `e^{-K}` times (G₆) is the
coefficient `[e^K]` of the graded model, with no condition on the counterterms. -/
theorem selectedPart_eq_pow_mul (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Grading κ → Prop)
    (K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    selectedPart P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ =
      (P.e : ℂ) ^ K * selectedPart { P with e := 1 } Φ D nf nA Sel K pOut pIn kIn αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.selectedPart_eq_pow_mul
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
