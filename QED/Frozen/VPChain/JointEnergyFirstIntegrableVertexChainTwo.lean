-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Frozen.TwoLoop.RegulatedAmplitude
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Provider.VPChain.JointEnergyFirstIntegrableVertexChainTwo

@[expose] public section

open QED.WickModel (Params Contraction loopCount lineMomentum₂ regulatedAmplitude₂)

namespace QED.VPChain

/-- (HC₀) **Every term of the set (b) chain vertex is a genuine integral** (obligation O3-5; the
analogue of (HV₀)). Let `ε > 0` and let the regulator fermions satisfy the Pauli–Villars
conditions `1 + c₁ + c₂ = 0` and `m² + c₁ M₁² + c₂ M₂² = 0`. Then for every contraction `C` in the
chain family (C₁) with two insertions (the contractions summed in (C₃) at `n = 2`: three loops for
two bubbles, two for one bubble and one `photonCt`, one for two `photonCt`), at all external
momenta with momentum conservation and all external indices, the integrand of its value (T₁₀)
(which is (F₇) at T1's flavours, theorem (M₃)) satisfies (T₉′): both stages of the joint
energy-first integral (T₉) converge absolutely, with `loopCount C` loop momenta. No mass, cutoff or
on-shell condition is assumed: at `ε > 0` every propagator is bounded, each bubble is
flavour-summed under the two Pauli–Villars conditions, and the photon propagator is regulated. -/
theorem jointEnergyFirstIntegrable_vertexChain_two (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (hC : IsVPChain 2 C)
    {pOut pIn : Fin 1 → Fin 4 → ℝ} {kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.VPChain

end
-- FROZEN_ANCHOR_SUFFIX_END
