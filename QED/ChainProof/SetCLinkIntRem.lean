/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntOne
public import QED.ChainProof.SetCLinkIntCB

/-!
# The integrability goal (HS₀) from the remaining class obligations

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58). Of the 56 class obligations (`QED.ChainProof.SetCLink.ClassesC`), fourteen are
proved:

* `S0`–`S4` and `CD2`–`CD4` (one loop, `QED/ChainProof/SetCLinkIntOne.lean`);
* `CB2`–`CB4` (two loops, `gaugeCt` on the open line, `QED/ChainProof/SetCLinkIntCB.lean`).

The remaining ones (`RemainingC`), grouped by integrand shape:

* `B` (12 orbits): three loops, seven `gauge` vertices (the two-loop vertex with a bubble);
* `D` (24 orbits): two loops, a `photonCt` vertex on a photon line of the two-loop vertex; the
  numerator has degree `4 + 2 = 6`, beyond the degree-`4` two-loop theorems of (X₀), which are
  moreover stated for `gauge` vertices only;
* `CB0`, `CB1`: two loops, a `fermionCt` vertex on the open line and the bubble;
* `CD0 s`, `CD1 s` (4 orbits): one loop, a `fermionCt` and a `photonCt` vertex; the one-loop test
  fails, the numerator degree being `3 + 1 + 2 = 6 > 4`.

`jointEnergyFirstIntegrable_setC_of_remaining` is (HS₀), with exactly its hypotheses and
conclusion, after the remaining class obligations.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.ChainProof.SetALink

/-- **The class obligations of (HS₀) not yet proved.** -/
structure RemainingC : Prop where
  hB : ∀ i, ClassIntA (repB i) 0
  hD : ∀ i s, ClassIntA (repD i s) 0
  hCB0 : ClassIntA repCB0 0
  hCB1 : ClassIntA repCB1 0
  hCD0 : ∀ s, ClassIntA (repCD0 s) 0
  hCD1 : ∀ s, ClassIntA (repCD1 s) 0

/-- The remaining obligations give all class obligations. -/
theorem classesC_of_remaining (h : RemainingC) : ClassesC :=
  ⟨h.hB, h.hD, h.hCB0, h.hCB1, classIntA_repCB2, classIntA_repCB3, classIntA_repCB4, h.hCD0,
    h.hCD1, classIntA_repCD2, classIntA_repCD3, classIntA_repCD4, classIntA_repS0,
    classIntA_repS1, classIntA_repS2, classIntA_repS3, classIntA_repS4⟩

/-- **(HS₀) from the remaining class obligations**, with exactly the hypotheses and conclusion of
`QED.ThreeLoop.jointEnergyFirstIntegrable_setC` after them. -/
theorem jointEnergyFirstIntegrable_setC_of_remaining (h : RemainingC)
    (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Graded.Grading κ)
    (hg : Graded.gradedOrder κ g = 7) (C : Contraction 1 1 κ) (hC₁ : IsOnePI C)
    (hC : QED.ThreeLoop.IsSetC C g)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ :=
  jointEnergyFirstIntegrable_setC_of_classes (classesC_of_remaining h) P Φ D rep hε hrep hPV₁
    hPV₂ hD g hg C hC₁ hC pOut pIn kIn hmom αOut βIn μ

end QED.ChainProof.SetCLink

end
