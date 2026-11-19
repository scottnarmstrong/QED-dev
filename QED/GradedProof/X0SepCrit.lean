/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0SepAmp

/-!
# (X₀): the decidable test for separated contractions with closed loops

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). `SepClosedCrit C`
collects, as decidable propositions on the contraction, the hypotheses of the three theorems of
`X0SepAmp` (`ShapeOK` for `ClosedShape`, `ShapeOK₂` for `ClosedShape₂`, `ClosedGrpOK` and
`OpenGrpOK` for the groups), and `jointEnergyFirstIntegrable_of_sepClosedCrit` gives (X₀) from
it. Each piece has its own `Decidable` instance (one instance for the whole test fails to
synthesize).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- `Z` (extended by `false` on the external field) is invariant under the fermion pairing. -/
def InvOK (C : Contraction 1 nA κ) (Z : Wick.FermionVertex κ → Prop) [DecidablePred Z] : Prop :=
  ∀ x, isZ Z (C.1.1 x) = isZ Z x

instance (C : Contraction 1 nA κ) (Z : Wick.FermionVertex κ → Prop) [DecidablePred Z] :
    Decidable (InvOK C Z) := by
  unfold InvOK; infer_instance

/-- `Z` is one nonempty cycle of the fermion pairing. -/
def CycOK (C : Contraction 1 nA κ) (Z : Wick.FermionVertex κ → Prop) [DecidablePred Z] : Prop :=
  ∃ t₀, Z t₀ ∧ ∀ t, Z t → C.1.1.SameCycle (.inr t) (.inr t₀)

instance (C : Contraction 1 nA κ) (Z : Wick.FermionVertex κ → Prop) [DecidablePred Z] :
    Decidable (CycOK C Z) := by
  unfold CycOK; infer_instance

/-- Every vertex outside `Z₁` and `Z₂` lies on the cycle of the external field. -/
def OpenOK (C : Contraction 1 nA κ) (Z₁ Z₂ : Wick.FermionVertex κ → Prop) [DecidablePred Z₁]
    [DecidablePred Z₂] : Prop :=
  ∀ t, ¬ Z₁ t → ¬ Z₂ t → C.1.1.SameCycle (.inr t) (.inl 0)

instance (C : Contraction 1 nA κ) (Z₁ Z₂ : Wick.FermionVertex κ → Prop) [DecidablePred Z₁]
    [DecidablePred Z₂] : Decidable (OpenOK C Z₁ Z₂) := by
  unfold OpenOK; infer_instance

/-- `ClosedShape` as a decidable proposition. -/
def ShapeOK (C : Contraction 1 nA κ) (Z : Wick.FermionVertex κ → Prop) [DecidablePred Z] :
    Prop :=
  InvOK C Z ∧ OpenOK C Z (fun _ => False) ∧ CycOK C Z

instance (C : Contraction 1 nA κ) (Z : Wick.FermionVertex κ → Prop) [DecidablePred Z] :
    Decidable (ShapeOK C Z) := by
  unfold ShapeOK; infer_instance

/-- `ClosedShape₂` as a decidable proposition. -/
def ShapeOK₂ (C : Contraction 1 nA κ) (Z₁ Z₂ : Wick.FermionVertex κ → Prop) [DecidablePred Z₁]
    [DecidablePred Z₂] : Prop :=
  InvOK C Z₁ ∧ InvOK C Z₂ ∧ (∀ t, Z₁ t → ¬ Z₂ t) ∧ OpenOK C Z₁ Z₂ ∧ CycOK C Z₁ ∧ CycOK C Z₂

instance (C : Contraction 1 nA κ) (Z₁ Z₂ : Wick.FermionVertex κ → Prop) [DecidablePred Z₁]
    [DecidablePred Z₂] : Decidable (ShapeOK₂ C Z₁ Z₂) := by
  unfold ShapeOK₂; infer_instance

/-- The lines along `ℓ_j` are a closed loop of one to four lines and no photon line. -/
def ClosedGrpOK (C : Contraction 1 nA κ) (j : ℕ) : Prop :=
  (∀ g : PhotonLine C, loopCoeff C (.inr g) j = 0) ∧ 1 ≤ Fintype.card (ZLine C (grpZ C j)) ∧
    Fintype.card (ZLine C (grpZ C j)) ≤ 4

instance (C : Contraction 1 nA κ) (j : ℕ) : Decidable (ClosedGrpOK C j) := by
  unfold ClosedGrpOK; infer_instance

/-- The lines along `ℓ_j` pass the one-loop count. -/
def OpenGrpOK (C : Contraction 1 nA κ) (j : ℕ) : Prop :=
  (grpF C j).card ≤ 3 ∧ 4 < (grpF C j).card + 4 * (grpG C j).card

instance (C : Contraction 1 nA κ) (j : ℕ) : Decidable (OpenGrpOK C j) := by
  unfold OpenGrpOK; infer_instance

/-- Closed loop along `ℓ₀`, open group along `ℓ₁`. -/
def SepCase₀ (C : Contraction 1 nA κ) : Prop :=
  ShapeOK C (grpZ C 0) ∧ ClosedGrpOK C 0 ∧ OpenGrpOK C 1

instance (C : Contraction 1 nA κ) : Decidable (SepCase₀ C) := by
  unfold SepCase₀; infer_instance

/-- Closed loop along `ℓ₁`, open group along `ℓ₀`. -/
def SepCase₁ (C : Contraction 1 nA κ) : Prop :=
  ShapeOK C (grpZ C 1) ∧ ClosedGrpOK C 1 ∧ OpenGrpOK C 0

instance (C : Contraction 1 nA κ) : Decidable (SepCase₁ C) := by
  unfold SepCase₁; infer_instance

/-- Two closed loops. -/
def SepCase₂ (C : Contraction 1 nA κ) : Prop :=
  ShapeOK₂ C (grpZ C 0) (grpZ C 1) ∧ ClosedGrpOK C 0 ∧ ClosedGrpOK C 1

instance (C : Contraction 1 nA κ) : Decidable (SepCase₂ C) := by
  unfold SepCase₂; infer_instance

/-- **The separated closed-loop test.** -/
def SepClosedCrit (C : Contraction 1 nA κ) : Prop :=
  SepCase₀ C ∨ SepCase₁ C ∨ SepCase₂ C

instance (C : Contraction 1 nA κ) : Decidable (SepClosedCrit C) := by
  unfold SepClosedCrit; infer_instance

/-- **(X₀) for a separated contraction passing the test.** -/
theorem jointEnergyFirstIntegrable_of_sepClosedCrit (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hε : 0 < P.ε) (hκ : ∀ t, κ t = .gauge) (C : Contraction 1 1 κ) (hL : loopCount C = 2)
    (hF : SepLines C) (hcrit : SepClosedCrit C) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) := by
  rcases hcrit with ⟨⟨s1, s2, s3⟩, ⟨g1, g2, g3⟩, o1, o2⟩ | ⟨⟨s1, s2, s3⟩, ⟨g1, g2, g3⟩, o1, o2⟩ |
    ⟨⟨s1, s2, s3, s4, s5, s6⟩, ⟨g1, g2, g3⟩, ⟨g1', g2', g3'⟩⟩
  · exact jointEnergyFirstIntegrable_sepClosed₀ P Φ D rep hrep hPV₁ hPV₂ hε hκ C hL hF
      ⟨s1, fun t ht => s2 t ht not_false, s3⟩ g1 g2 g3 o1 o2 pOut pIn kIn αOut βIn μ
  · exact jointEnergyFirstIntegrable_sepClosed₁ P Φ D rep hrep hPV₁ hPV₂ hε hκ C hL hF
      ⟨s1, fun t ht => s2 t ht not_false, s3⟩ g1 g2 g3 o1 o2 pOut pIn kIn αOut βIn μ
  · exact jointEnergyFirstIntegrable_sepClosed₂ P Φ D rep hrep hPV₁ hPV₂ hε hκ C hL hF
      ⟨s1, s2, s3, s4, s5, s6⟩ g1 g1' g2 g3 g2' g3' pOut pIn kIn αOut βIn μ

end QED.GradedProof.X0

end
