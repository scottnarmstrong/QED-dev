/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkInt
public import QED.ChainProof.SetALinkIntP
public import QED.ChainProof.SetALinkIntG
public import QED.ChainProof.SetALinkIntF
public import QED.ChainProof.SetALinkIntVA
public import QED.ChainProof.SetALinkIntVB
public import QED.ChainProof.SetALinkIntVC

/-!
# (HA₀) unconditionally

`jointEnergyFirstIntegrable_setA_final`: the integrability of every term of the set (a) vertex
(decision D-58, goal (HA₀)), with exactly the hypotheses and conclusion of the frozen goal
`QED.ThreeLoop.jointEnergyFirstIntegrable_setA`. It discharges the nine class obligations of
`jointEnergyFirstIntegrable_setA_of_classes`: the photon-counterterm classes
(`classIntA_repP`), the gauge-counterterm classes (`classIntA_repGW`, `classIntA_repGU`), the
fermion-counterterm classes (`classIntA_repFA`, `classIntA_repFB`) and the three-loop
vertex-type classes (`classIntA_repVA`, `classIntA_repVB`, `classIntA_repVC`).
-/

@[expose] public section

open QED.WickModel (Params Contraction loopCount lineMomentum₂)

namespace QED.ChainProof.SetALink

/-- **(HA₀)**, with exactly the hypotheses and conclusion of
`QED.ThreeLoop.jointEnergyFirstIntegrable_setA`. -/
theorem jointEnergyFirstIntegrable_setA_final
    (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Graded.Grading κ)
    (hg : Graded.gradedOrder κ g = 7) (C : Contraction 1 1 κ) (hC : QED.ThreeLoop.IsSetA C)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ :=
  jointEnergyFirstIntegrable_setA_of_classes classIntA_repP classIntA_repGW classIntA_repGU
    classIntA_repFA classIntA_repFB SetALinkV.classIntA_repVA SetALinkV.classIntA_repVB
    SetALinkV.classIntA_repVC
    P Φ D rep hε hrep hPV₁ hPV₂ hD g hg C hC pOut pIn kIn hmom αOut βIn μ

end QED.ChainProof.SetALink

end
