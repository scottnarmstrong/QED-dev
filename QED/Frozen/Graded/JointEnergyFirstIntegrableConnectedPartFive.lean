-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.GradedOrder
public import QED.Frozen.Graded.RegulatedAmplitude
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.ExternalsAttached
public import QED.Frozen.WickModel.VerticesConnected
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Provider.Graded.JointEnergyFirstIntegrableConnectedPartFive

@[expose] public section

open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount lineMomentum₂)

namespace QED.Graded

/-- (X₀) **Every term of the order-`e⁵` connected part is a genuine integral** (decision D-44.2; the
analogue of (HV₀) and (HC₀) for the contractions behind (X₁) and (X₂)). Let `ε > 0` and let the
counterterm scheme `rep` have Pauli–Villars blocks, as in (G-Π₂): `rep` idempotent, the level-`0`
fermion counterterm data constant on its classes, and on each class `∑ c_f = 0` and
`∑ c_f M_f² = 0`. Then for every contraction `C` with one external fermion pair and one external
photon whose externals are attached and whose vertices are connected, at any grading of graded order
exactly `5` (the terms of (G₆″) at `K = 5`: the order-`e⁵` 1PI vertex graphs, the leg corrections
through order `e⁴`, the photon-leg bubbles through order `e⁴` including the two-loop bubbles and the
one-loop bubbles with a level-`0` counterterm on the loop, and the tadpoles), at all external
momenta with momentum conservation and all external indices, the integrand of its value (G₅)
satisfies (T₉′). No mass, cutoff or on-shell condition is assumed. Counterterms of level `≥ 1` enter
only tree contractions at this order (a level-`1` vertex has order `4` or `5`), so only level `0` is
constrained. Power counting (design note §8, R2): a counterterm on a closed loop is made integrable
by the block conditions (the one-loop bubble then decays like `|ℓ⃗|⁻⁵`, D-55 revised); in the
two-loop bubble every subgraph containing the photon line converges by the photon regulator alone,
the fermion loop at fixed photon momentum needs `∑ c_f = 0`, and the overall degree is `0` (the
regulated photon propagator decays like `k⁻⁴`), lowered to `-2` by `∑ c_f = 0`. -/
theorem jointEnergyFirstIntegrable_connectedPart_five (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Grading κ) (hg : gradedOrder κ g = 5)
    (C : Contraction 1 1 κ) (hC : ExternalsAttached C ∧ VerticesConnected C)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.jointEnergyFirstIntegrable_connectedPart_five
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
