/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPlumbPiece
public import QED.GradedProof.X1CCountPeelIn
public import QED.GradedProof.X1CCountOut
public import QED.GradedProof.X1CCountP

/-!
# (X₁) piece C: the three peels with their (T₉′) inputs discharged

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. `selectedPart_peelIn_t9`, `selectedPart_peelOut_t9`,
`selectedPart_peelP_t9`: the peels `selectedPart_peelIn`, `selectedPart_peelOut`,
`selectedPart_peelP` at an order `K ≤ 5`, with the (T₉′) hypotheses `hT₁`, `hT₂` supplied from
`T9Hyps` (`plumb_t9_vertex`, `plumb_t9_selfEnergy`, `plumb_t9_vacuumPolarization`). What remains
are the class condition (the class consists of attached connected contractions) and the
graph-theoretic bijection hypotheses `hmem`, `hinj`, `hsurj`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Params Contraction loopCount lineMomentum₂ VerticesConnected
  ExternalsAttached IsOnePI)
open QED.Graded
open Complex

variable {P : Params} {F : Type} [Fintype F] [DecidableEq F] {Φ : Lepton.Flavors F}
  {D : Counterterms F} {rep : F → F} {m₀ : ℝ}

/-- **The in-leg peel at order `K ≤ 5`**, (T₉′) discharged. -/
theorem selectedPart_peelIn_t9 (H : T9Hyps P Φ D rep m₀) (SelG Red : CountSel 1 1)
    (hG : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ),
      SelG C g → ExternalsAttached C ∧ VerticesConnected C) (K : ℕ) (hK : K ≤ 5)
    (hmem : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ x ∈ countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g,
        SelG (glueIn x.2.1 x.2.2.1 x.2.2.2) g ∧ Red (glueIn x.2.1 x.2.2.1 x.2.2.2) g)
    (hinj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueIn x.2.1 x.2.2.1 x.2.2.2)
        (countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g))
    (hsurj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ C : Contraction 1 1 κ, SelG C g → Red C g →
        ∃ x ∈ countIdxSet SelG (countOnePI (nf := 1) (nA := 0)) g,
          glueIn x.2.1 x.2.2.1 x.2.2.2 = C)
    {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (αOut βIn μ : Fin 1 → Fin 4) :
    selectedPart P Φ D 1 1 SelG K ![r'] ![r] ![q] αOut βIn μ =
      selectedPart P Φ D 1 1 (fun C g => SelG C g ∧ ¬ Red C g) K ![r'] ![r] ![q] αOut βIn μ +
      ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
        selectedPart P Φ D 1 1 SelG p.1 ![r'] ![r] ![q] αOut ![γ] μ *
          ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r γ δ) *
          onePIPart P Φ D 1 0 p.2 ![r] ![r] ![] ![δ] βIn ![] :=
  selectedPart_peelIn P Φ D SelG Red hG K hmem hinj hsurj hmom αOut βIn μ
    (fun _ g₁ C₁ h₁ hle γ => plumb_t9_vertex H C₁ (hG C₁ g₁ h₁).1 (hG C₁ g₁ h₁).2 g₁
      (hle.trans hK) hmom αOut ![γ] μ)
    (fun _ g₂ C₂ h₂ hle δ => plumb_t9_selfEnergy H C₂ h₂ g₂ (hle.trans hK) r ![δ] βIn)

/-- **The out-leg peel at order `K ≤ 5`**, (T₉′) discharged. -/
theorem selectedPart_peelOut_t9 (H : T9Hyps P Φ D rep m₀) (SelH Red : CountSel 1 1)
    (hH : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ),
      SelH C g → ExternalsAttached C ∧ VerticesConnected C) (K : ℕ) (hK : K ≤ 5)
    (hmem : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ x ∈ countIdxSet SelH (countOnePI (nf := 1) (nA := 0)) g,
        SelH (glueOut x.2.1 x.2.2.1 x.2.2.2) g ∧ Red (glueOut x.2.1 x.2.2.1 x.2.2.2) g)
    (hinj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueOut x.2.1 x.2.2.1 x.2.2.2)
        (countIdxSet SelH (countOnePI (nf := 1) (nA := 0)) g))
    (hsurj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ C : Contraction 1 1 κ, SelH C g → Red C g →
        ∃ x ∈ countIdxSet SelH (countOnePI (nf := 1) (nA := 0)) g,
          glueOut x.2.1 x.2.2.1 x.2.2.2 = C)
    {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (αOut βIn μ : Fin 1 → Fin 4) :
    selectedPart P Φ D 1 1 SelH K ![r'] ![r] ![q] αOut βIn μ =
      selectedPart P Φ D 1 1 (fun C g => SelH C g ∧ ¬ Red C g) K ![r'] ![r] ![q] αOut βIn μ +
      ∑ p ∈ antidiagonal K, ∑ γ, ∑ δ,
        onePIPart P Φ D 1 0 p.2 ![r'] ![r'] ![] αOut ![γ] ![] *
          ((1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r' γ δ) *
          selectedPart P Φ D 1 1 SelH p.1 ![r'] ![r] ![q] ![δ] βIn μ :=
  selectedPart_peelOut P Φ D SelH Red hH K hmem hinj hsurj hmom αOut βIn μ
    (fun _ g₁ C₁ h₁ hle δ => plumb_t9_vertex H C₁ (hH C₁ g₁ h₁).1 (hH C₁ g₁ h₁).2 g₁
      (hle.trans hK) hmom ![δ] βIn μ)
    (fun _ g₂ C₂ h₂ hle γ => plumb_t9_selfEnergy H C₂ h₂ g₂ (hle.trans hK) r' αOut ![γ])

/-- **The photon-leg peel at order `K ≤ 5`**, (T₉′) discharged. -/
theorem selectedPart_peelP_t9 (H : T9Hyps P Φ D rep m₀) (SelJ Red : CountSel 1 1)
    (hJ : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) (g : Grading κ),
      SelJ C g → ExternalsAttached C ∧ VerticesConnected C) (K : ℕ) (hK : K ≤ 5)
    (hmem : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ x ∈ countIdxSet SelJ (countOnePI (nf := 0) (nA := 2)) g,
        SelJ (glueP x.2.1 x.2.2.1 x.2.2.2) g ∧ Red (glueP x.2.1 x.2.2.1 x.2.2.2) g)
    (hinj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      Set.InjOn (fun x : CountIdx 1 1 0 2 κ => glueP x.2.1 x.2.2.1 x.2.2.2)
        (countIdxSet SelJ (countOnePI (nf := 0) (nA := 2)) g))
    (hsurj : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ C : Contraction 1 1 κ, SelJ C g → Red C g →
        ∃ x ∈ countIdxSet SelJ (countOnePI (nf := 0) (nA := 2)) g,
          glueP x.2.1 x.2.2.1 x.2.2.2 = C)
    {r' r q : Fin 4 → ℝ} (hmom : r' = r + q) (αOut βIn μ : Fin 1 → Fin 4) :
    selectedPart P Φ D 1 1 SelJ K ![r'] ![r] ![q] αOut βIn μ =
      selectedPart P Φ D 1 1 (fun C g => SelJ C g ∧ ¬ Red C g) K ![r'] ![r] ![q] αOut βIn μ +
      ∑ p ∈ antidiagonal K, ∑ ν, ∑ ρ,
        selectedPart P Φ D 1 1 SelJ p.1 ![r'] ![r] ![q] αOut βIn ![ν] *
          ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q ν ρ) *
          onePIPart P Φ D 0 2 p.2 ![] ![] ![q, -q] ![] ![] ![μ 0, ρ] :=
  selectedPart_peelP P Φ D SelJ Red hJ K hmem hinj hsurj hmom αOut βIn μ
    (fun _ g₁ C₁ h₁ hle ν => plumb_t9_vertex H C₁ (hJ C₁ g₁ h₁).1 (hJ C₁ g₁ h₁).2 g₁
      (hle.trans hK) hmom αOut βIn ![ν])
    (fun _ g₂ C₂ h₂ hle ρ => plumb_t9_vacuumPolarization H C₂ h₂ g₂ (hle.trans hK) q (μ 0) ρ)

end QED.GradedProof.X1C

end
