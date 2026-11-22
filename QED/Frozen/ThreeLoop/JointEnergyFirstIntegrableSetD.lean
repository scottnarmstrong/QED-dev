-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetD
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.Graded.RegulatedAmplitude
public import QED.Frozen.Graded.GradedOrder
public import QED.Provider.ThreeLoop.JointEnergyFirstIntegrableSetD

@[expose] public section

open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)

namespace QED.ThreeLoop

/-- (HD₀) **Every term of the set (d) vertex is a genuine integral** (the analogue of (HA₀),
(HS₀)). Under the hypotheses of (X₀) (`ε > 0`, Pauli–Villars blocks of `rep`, level-`0` fermion
counterterms constant on its classes), for every 1PI contraction `C` in (Sd₁) at any grading of
graded order exactly `7` (the six three-loop light-by-light graphs), at all external momenta with
momentum conservation and all external indices, the integrand of its value (G₅) satisfies (T₉′).
No mass, cutoff or on-shell condition is assumed. No counterterm datum enters (Sd₁), so the
hypotheses on `D` and `rep` beyond the Pauli–Villars blocks are kept only to give the statement
the hypotheses of (HA₀) and (HS₀). Power counting: the flavour-summed four-photon loop converges
under `∑ c_f = 0` and `∑ c_f M_f² = 0` (its superficial degree is `0`), and the regulated photon
propagators decay like `k⁻⁴` each. -/
theorem jointEnergyFirstIntegrable_setD (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Graded.Grading κ)
    (hg : Graded.gradedOrder κ g = 7) (C : Contraction 1 1 κ) (hC₁ : IsOnePI C)
    (hC : IsSetD C)
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
