/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.RegulatedAmplitude
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral

@[expose] public section

open QED.WickModel (Params Contraction loopCount lineMomentum₂)

namespace QED.Lepton

/-- (F₇) The value of a contraction, the successor of (T₁₀): the regulated amplitude (F₆) at the
line momenta of the routing (T₄), times `(2π)^{-4L}`, `L = loopCount C`, integrated with the
joint energy-first prescription (T₉) at the fixed `ε`; `0` when a stage is not integrable. -/
noncomputable def contractionValue₂ (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F)
    {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  QED.TwoLoop.jointEnergyFirstIntegral (loopCount C) fun ℓ =>
    (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P Φ C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ

end QED.Lepton

end
