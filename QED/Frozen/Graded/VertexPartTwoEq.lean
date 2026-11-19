-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.VertexPart
public import QED.Frozen.Lepton.VertexOrderFive
public import QED.Provider.Graded.VertexPartTwoEq

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (E-G₃) **The graded order-`e⁵` vertex is (F₉) plus the two-loop vertex counterterm** (memo
(E-G₃)): with the level-`0` data at the open-line flavour equal to the counterterms of `P` divided
by `e²` and the open-line mass `P.m`, the order-`5` vertex (G₈ᵥ) at the open-line flavour is the
frozen vertex (F₉) plus the tree term `e⁴ d₁ e γ^μ` of the level-`1` vertex counterterm of that
flavour. No other level-`1` term is 1PI at this order (a level-`1` `fermionCt` or `photonCt` would
sit on an external leg), and no counterterm vertex lies on a closed loop, so the counterterms of
the other flavours and of the levels `≥ 2` do not enter. -/
theorem vertexPart_two_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (hmass : Φ.mass Φ.openLine = P.m)
    (h₁ : P.δ₁ = P.e ^ 2 * D.d₁ Φ.openLine 0) (h₂ : P.δ₂ = P.e ^ 2 * D.d₂ Φ.openLine 0)
    (hm : P.δm = P.e ^ 2 * D.dm Φ.openLine 0) (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0)
    (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    vertexPart P Φ D Φ.openLine 2 p' p μ =
      Lepton.vertexOrderFive P Φ p' p μ +
        ((P.e ^ 4 * D.d₁ Φ.openLine 1 * P.e : ℝ) : ℂ) • Dirac.gamma μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
