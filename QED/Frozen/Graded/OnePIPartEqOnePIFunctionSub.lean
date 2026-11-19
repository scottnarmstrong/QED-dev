-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.OnePIPart
public import QED.Frozen.Lepton.OnePIFunction
public import QED.Provider.Graded.OnePIPartEqOnePIFunctionSub

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (E-G₁) **Embedding: with one-loop counterterms only, the graded 1PI part is the order part
of (F₈)** (decision D-49.4: each successor has an embedding theorem; memo (E-G₁)). Let the
graded data have no level `≥ 1`, let its level `0` at the open-line flavour be the counterterms of
`P` divided by `e²`, and let the open-line mass be `P.m` (the coherence of (F₀)). Then for
`nf ≥ 1` and `K + 1 ≤ 2 nf + nA + 3`, the order-`(K+1)` part (G₆′) is the difference of (F₈) at
orders `K + 1` and `K`. In this range no counterterm vertex lies on a closed fermion loop of a 1PI
contraction (such a loop needs two photon lines to the open line, hence two loops, and its order
is then at least `2 nf + nA + 4`), so the per-flavour counterterms of (G₁) reduce to the open-line
counterterms of (F₁). For `nf = 0` the range is smaller: the order-`4` vacuum polarization has
counterterm vertices on its loop, and only order `2` agrees (theorem (E-G₂ₚ)). -/
theorem onePIPart_eq_onePIFunction₂_sub (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (hmass : Φ.mass Φ.openLine = P.m)
    (h₁ : P.δ₁ = P.e ^ 2 * D.d₁ Φ.openLine 0) (h₂ : P.δ₂ = P.e ^ 2 * D.d₂ Φ.openLine 0)
    (hm : P.δm = P.e ^ 2 * D.dm Φ.openLine 0) (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0) (nf nA K : ℕ) (hnf : 1 ≤ nf)
    (hK : K + 1 ≤ 2 * nf + nA + 3) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    onePIPart P Φ D nf nA (K + 1) pOut pIn kIn αOut βIn μ =
      Lepton.onePIFunction₂ P Φ nf nA (K + 1) pOut pIn kIn αOut βIn μ -
        Lepton.onePIFunction₂ P Φ nf nA K pOut pIn kIn αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.onePIPart_eq_onePIFunction₂_sub
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
