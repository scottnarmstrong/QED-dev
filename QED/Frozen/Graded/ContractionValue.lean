/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.RegulatedAmplitude
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral

@[expose] public section

open QED.WickModel (Params Contraction loopCount lineMomentum₂)

namespace QED.Graded

/-- (G₅) **The value of a graded contraction**, the successor of (F₇): the regulated amplitude
(G₄) at the line momenta of the routing (T₄), times `(2π)^{-4L}`, `L = loopCount C`, integrated
with the joint energy-first prescription (T₉) at the fixed `ε`; `0` when a stage is not
integrable. Source-facing statements assert the integrability (T₉′) of the terms they sum (the
goals (G-Σ₂), (G-Π₂)); the grading changes only scalar coefficients, not the integrand's
structure. -/
noncomputable def contractionValue (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (g : Grading κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  QED.TwoLoop.jointEnergyFirstIntegral (loopCount C) fun ℓ =>
    (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ

end QED.Graded

end
