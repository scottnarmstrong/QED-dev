-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.Graded.RegulatedAmplitude
public import QED.Frozen.Graded.GradedOrder
public import QED.Provider.ThreeLoop.JointEnergyFirstIntegrableSetA

@[expose] public section

open QED.WickModel (Params Contraction loopCount lineMomentum₂)

namespace QED.ThreeLoop

/-- (HA₀) **Every term of the set (a) vertex is a genuine integral** (the analogue of (HC₀) and
(X₀)). Let `ε > 0` and let the counterterm scheme `rep` have Pauli–Villars blocks, as in (X₀):
`rep` idempotent, the level-`0` fermion counterterm data constant on its classes, and on each class
`∑ c_f = 0` and `∑ c_f M_f² = 0`. Then for every contraction `C` in the set (a) family (A₁), at
any grading of graded order exactly `7` (the terms of (HA₆)'s vertex: three loops for the
two-loop-bubble graphs, two for the graphs with a level-`0` counterterm on the loop, one for the
level-`1` photon counterterm), at all external momenta with momentum conservation and all external
indices, the integrand of its value (G₅) satisfies (T₉′). No mass, cutoff or on-shell condition
is assumed. Counterterm data of level `≥ 1` enter only the one-loop `photonCt` graph, whose
integrability does not depend on them. Power counting: the inner two-loop bubble is integrable at
fixed photon momentum under the block conditions (as in (G-Π₂)), and the two regulated photon
propagators of the outer loop decay like `k⁻⁴` each. -/
theorem jointEnergyFirstIntegrable_setA (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Graded.Grading κ)
    (hg : Graded.gradedOrder κ g = 7) (C : Contraction 1 1 κ) (hC : IsSetA C)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
