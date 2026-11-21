/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPart

@[expose] public section

open QED.WickModel (Params Contraction)

namespace QED.Graded

/-- (Gs₁) **The order-`e^{2n}` self-energy of flavour `f` restricted to a selection** (the text
of (G₈ₛ) with the filter `IsOnePI` replaced by the selection `Sel`, ruling S5 of the Stage 2
design note): `(1/i)` times the order-`2n` part (G₆) of the sum over the graded contractions with
one external fermion pair of flavour `f` and no external photon that satisfy `Sel`, outgoing index
as row and incoming as column. With `Sel C g := IsOnePI C` it is (G₈ₛ). -/
noncomputable def selfEnergySelPart (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 0 κ → Grading κ → Prop)
    (f : F) (n : ℕ) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => (1 / Complex.I) *
    selectedPart P { Φ with openLine := f } D 1 0 Sel (2 * n) ![p] ![p] ![] ![α] ![β] ![]

end QED.Graded

end
