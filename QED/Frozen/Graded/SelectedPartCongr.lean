-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPart
public import QED.Provider.Graded.SelectedPartCongr

@[expose] public section

open QED.WickModel (Params Contraction)

namespace QED.Graded

/-- (G-loc) **The order-`K` part reads only the levels below `K/2`** (memo (G-loc)): a
counterterm vertex of level `k` has order at least `2 (k + 1)`, so (G₆) at order `K` does not
depend on the counterterm data of the levels `k` with `2 k + 2 > K`. Hence the order-`2n`
conditions (G₉)–(G₁₁) read only the levels `≤ n - 1`, and a statement at order `K` reads finitely
many levels. -/
theorem selectedPart_congr (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F) (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Grading κ → Prop)
    (K : ℕ)
    (h : ∀ f k, 2 * k + 2 ≤ K →
      D.d₁ f k = D'.d₁ f k ∧ D.d₂ f k = D'.d₂ f k ∧ D.dm f k = D'.dm f k)
    (h₃ : ∀ k, 2 * k + 2 ≤ K → D.d₃ k = D'.d₃ k)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    selectedPart P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ =
      selectedPart P Φ D' nf nA Sel K pOut pIn kIn αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.selectedPart_congr
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
