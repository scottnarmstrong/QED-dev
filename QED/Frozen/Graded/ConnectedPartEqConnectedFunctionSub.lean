-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.ConnectedPart
public import QED.Frozen.WickModel.ConnectedFunction
public import QED.Provider.Graded.ConnectedPartEqConnectedFunctionSub

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (E-G₅) **Embedding of the connected part: with T1's flavours and one-loop counterterms only,
(G₆″) is the order part of (X₂₉)** (decision D-49.4; at `nf = nA = 1`, `K = 2` it identifies the
order-`3` input of (G-L₁) with the input of the frozen (L₁), (X₂₉) at order `3`, minus its order-`1`
tree term). Take T1's flavours `⟨![m, M₁, M₂], ![1, c₁, c₂], 0⟩` ((X₀′), (X₀″)), the level-`0` data
at the electron equal to the counterterms of `P` divided by `e²`, and no level `≥ 1`. Then for
`K + 1 ≤ 2 nf + nA + 1` the order-`(K+1)` connected part is the difference of T1's connected
function (X₂₉) at orders `K + 1` and `K`. In this range every contraction has at most one loop, and
a counterterm vertex on a closed loop would need order at least `2 L + 2 nf + nA ≥ 2 nf + nA + 2`
(two more than the gauge vertices of the loop), so the per-flavour counterterms of (G₁) reduce to
the electron counterterms of (X₁); for one loop (T₁₀) is (X₂₇) (T₁₃). -/
theorem connectedPart_eq_connectedFunction_sub (P : Params) (D : Counterterms (Fin 3))
    (h₁ : P.δ₁ = P.e ^ 2 * D.d₁ 0 0) (h₂ : P.δ₂ = P.e ^ 2 * D.d₂ 0 0)
    (hm : P.δm = P.e ^ 2 * D.dm 0 0) (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0) (nf nA K : ℕ) (hK : K + 1 ≤ 2 * nf + nA + 1)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    connectedPart P ⟨P.mass, P.loopCoeff, 0⟩ D nf nA (K + 1) pOut pIn kIn αOut βIn μ =
      WickModel.connectedFunction P nf nA (K + 1) pOut pIn kIn αOut βIn μ -
        WickModel.connectedFunction P nf nA K pOut pIn kIn αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.connectedPart_eq_connectedFunction_sub
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
