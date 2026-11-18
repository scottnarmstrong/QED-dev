-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.OnePIFunction
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Provider.TwoLoop.JointEnergyFirstIntegrableVertexOrderFive

@[expose] public section

open QED.WickModel (Params Contraction IsOnePI loopCount regulatedAmplitude₂ lineMomentum₂)

namespace QED.TwoLoop

/-- (HV₀) **Every term of the order-`e⁵` vertex is a genuine integral** (decision D-44, item 2;
obligation O2-7). Let `ε > 0` and let the regulator fermions satisfy the Pauli–Villars conditions
`1 + c₁ + c₂ = 0` and `m² + c₁ M₁² + c₂ M₂² = 0`. Then for every 1PI contraction `C` with one
external fermion pair and one external photon whose vertices have total order exactly `5` in `e`
(the contractions summed in (HV₁)), at all external momenta with momentum conservation and all
external indices, the integrand of its value (T₁₀) satisfies (T₉′): both stages of the joint
energy-first integral (T₉) converge absolutely. So no term of (HV₁) is `0` by default. -/
theorem jointEnergyFirstIntegrable_vertexOrderFive (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order = 5)
    (C : Contraction 1 1 κ) (hC : IsOnePI C) {pOut pIn : Fin 1 → Fin 4 → ℝ}
    {kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.TwoLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
