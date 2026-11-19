/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0ClosedFlavor

/-!
# (X₀): the flavour sum of a contraction with two closed fermion loops

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), for the two-loop
contractions of `TwoLoopClosedGoal` with two closed fermion loops `Z₁`, `Z₂` (`ClosedShape₂`).
The preserved flavourings are `φ_{f₁ f₂}` (`closedFlavoring₂`: `f₁` on `Z₁`, `f₂` on `Z₂`, the
open-line flavour elsewhere), their weight is `c_{f₁} c_{f₂}`, and the regulated amplitude (G₄)
is `∑_{f₁, f₂} c_{f₁} c_{f₂} A(φ_{f₁ f₂})` (`regulatedAmplitude_eq_closed₂`).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel (Params Contraction ClosedLoop)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type} (Φ : Lepton.Flavors F)

/-- The flavouring with `f₁` on `Z₁`, `f₂` on `Z₂` and the open-line flavour elsewhere. -/
def closedFlavoring₂ (Z₁ Z₂ : Wick.FermionVertex κ → Prop) [DecidablePred Z₁]
    [DecidablePred Z₂] (f₁ f₂ : F) : Flavoring F κ :=
  fun t => if Z₁ t then f₁ else if Z₂ t then f₂ else Φ.openLine

/-- The shape of a contraction with two closed fermion loops `Z₁`, `Z₂`. -/
structure ClosedShape₂ (C : Contraction 1 nA κ) (Z₁ Z₂ : Wick.FermionVertex κ → Prop)
    [DecidablePred Z₁] [DecidablePred Z₂] : Prop where
  inv₁ : ∀ x, isZ Z₁ (C.1.1 x) = isZ Z₁ x
  inv₂ : ∀ x, isZ Z₂ (C.1.1 x) = isZ Z₂ x
  disj : ∀ t, Z₁ t → ¬ Z₂ t
  open_cycle : ∀ t, ¬ Z₁ t → ¬ Z₂ t → C.1.1.SameCycle (.inr t) (.inl 0)
  loop₁ : ∃ t₀, Z₁ t₀ ∧ ∀ t, Z₁ t → C.1.1.SameCycle (.inr t) (.inr t₀)
  loop₂ : ∃ t₀, Z₂ t₀ ∧ ∀ t, Z₂ t → C.1.1.SameCycle (.inr t) (.inr t₀)

variable {C : Contraction 1 nA κ} {Z₁ Z₂ : Wick.FermionVertex κ → Prop} [DecidablePred Z₁]
  [DecidablePred Z₂]

theorem fermionFlavor_closed₂ (f₁ f₂ : F)
    (a : Fin 1 ⊕ Wick.FermionVertex κ) :
    fermionFlavor Φ (closedFlavoring₂ Φ Z₁ Z₂ f₁ f₂) a =
      if isZ Z₁ a then f₁ else if isZ Z₂ a then f₂ else Φ.openLine := by
  rcases a with i | t
  · rfl
  · by_cases h₁ : Z₁ t
    · simp [fermionFlavor, closedFlavoring₂, isZ, h₁]
    · simp [fermionFlavor, closedFlavoring₂, isZ, h₁]

theorem preserves_closed₂ (hC : ClosedShape₂ C Z₁ Z₂) (f₁ f₂ : F) :
    Preserves Φ C (closedFlavoring₂ Φ Z₁ Z₂ f₁ f₂) := fun a => by
  rw [fermionFlavor_closed₂ Φ, fermionFlavor_closed₂ Φ, hC.inv₁, hC.inv₂]

theorem eq_closed₂_of_preserves (hC : ClosedShape₂ C Z₁ Z₂) {t₁ t₂ : Wick.FermionVertex κ}
    (ht₁ : ∀ t, Z₁ t → C.1.1.SameCycle (.inr t) (.inr t₁))
    (ht₂ : ∀ t, Z₂ t → C.1.1.SameCycle (.inr t) (.inr t₂)) {φ : Flavoring F κ}
    (hφ : Preserves Φ C φ) : φ = closedFlavoring₂ Φ Z₁ Z₂ (φ t₁) (φ t₂) := by
  funext t
  unfold closedFlavoring₂
  split_ifs with h₁ h₂
  · exact fermionFlavor_eq_of_sameCycle hφ (ht₁ t h₁)
  · exact fermionFlavor_eq_of_sameCycle hφ (ht₂ t h₂)
  · exact fermionFlavor_eq_of_sameCycle hφ (hC.open_cycle t h₁ h₂)

theorem eq_zLoop_or (hC : ClosedShape₂ C Z₁ Z₂) {t₁ t₂ : Wick.FermionVertex κ} (h₁ : Z₁ t₁)
    (h₂ : Z₂ t₂) (ht₁ : ∀ t, Z₁ t → C.1.1.SameCycle (.inr t) (.inr t₁))
    (ht₂ : ∀ t, Z₂ t → C.1.1.SameCycle (.inr t) (.inr t₂)) (q : ClosedLoop C) :
    q = zLoop hC.inv₁ t₁ h₁ ∨ q = zLoop hC.inv₂ t₂ h₂ := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases x with i | t
  · exact absurd rfl (hq i)
  · by_cases hz₁ : Z₁ t
    · exact Or.inl (Subtype.ext (Quotient.sound (ht₁ t hz₁)))
    · by_cases hz₂ : Z₂ t
      · exact Or.inr (Subtype.ext (Quotient.sound (ht₂ t hz₂)))
      · exact absurd (Quotient.sound (hC.open_cycle t hz₁ hz₂)).symm (hq 0)

theorem isZ_out_zLoop {Z : Wick.FermionVertex κ → Prop} [DecidablePred Z]
    (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) {t₀ : Wick.FermionVertex κ} (h₀ : Z t₀) :
    isZ Z (zLoop hZ t₀ h₀).1.out = true := by
  have h1 : C.1.1.SameCycle (zLoop hZ t₀ h₀).1.out (.inr t₀) :=
    Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid C.1.1) (Sum.inr t₀)
  rw [isZ_of_sameCycle hZ h1]
  simp [isZ, h₀]

theorem isZ_out_zLoop_other {Z Z' : Wick.FermionVertex κ → Prop} [DecidablePred Z]
    [DecidablePred Z'] (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x)
    (hZ' : ∀ x, isZ Z' (C.1.1 x) = isZ Z' x) {t₀ : Wick.FermionVertex κ} (h₀ : Z t₀)
    (h₀' : ¬ Z' t₀) : isZ Z' (zLoop hZ t₀ h₀).1.out = false := by
  have h1 : C.1.1.SameCycle (zLoop hZ t₀ h₀).1.out (.inr t₀) :=
    Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid C.1.1) (Sum.inr t₀)
  rw [isZ_of_sameCycle hZ' h1]
  simp [isZ, h₀']

open scoped Classical in
theorem loopWeight_closed₂ (hC : ClosedShape₂ C Z₁ Z₂) (f₁ f₂ : F) :
    loopWeight Φ C (closedFlavoring₂ Φ Z₁ Z₂ f₁ f₂) = Φ.coeff f₁ * Φ.coeff f₂ := by
  obtain ⟨t₁, h₁, ht₁⟩ := hC.loop₁
  obtain ⟨t₂, h₂, ht₂⟩ := hC.loop₂
  set q₁ := zLoop hC.inv₁ t₁ h₁
  set q₂ := zLoop hC.inv₂ t₂ h₂
  have hne : q₁ ≠ q₂ := fun h => by
    have := isZ_out_zLoop hC.inv₁ h₁
    have hq : zLoop hC.inv₁ t₁ h₁ = zLoop hC.inv₂ t₂ h₂ := h
    rw [hq, isZ_out_zLoop_other hC.inv₂ hC.inv₁ h₂
      (fun h' => hC.disj t₂ h' h₂)] at this
    exact absurd this (by decide)
  have huniv : (Finset.univ : Finset (ClosedLoop C)) = {q₁, q₂} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact eq_zLoop_or hC h₁ h₂ ht₁ ht₂ q
  rw [loopWeight, huniv, Finset.prod_pair hne, fermionFlavor_closed₂ Φ,
    fermionFlavor_closed₂ Φ, isZ_out_zLoop hC.inv₁ h₁, isZ_out_zLoop hC.inv₂ h₂,
    isZ_out_zLoop_other hC.inv₂ hC.inv₁ h₂ (fun h' => hC.disj t₂ h' h₂)]
  rfl

/-- **The flavour sum of a contraction with two closed loops.** -/
theorem regulatedAmplitude_eq_closed₂ (P : Params) [Fintype F] [DecidableEq F]
    (D : Counterterms F) (hC : ClosedShape₂ C Z₁ Z₂) (g : Grading κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ =
      ∑ f₁, ∑ f₂, (Φ.coeff f₁ : ℂ) * (Φ.coeff f₂ : ℂ) *
        contractionAmplitude P Φ D C (closedFlavoring₂ Φ Z₁ Z₂ f₁ f₂) g pIn kIn k αOut βIn μ := by
  classical
  obtain ⟨t₁, h₁, ht₁⟩ := hC.loop₁
  obtain ⟨t₂, h₂, ht₂⟩ := hC.loop₂
  have h₁₂ : ¬ Z₂ t₁ := hC.disj t₁ h₁
  unfold regulatedAmplitude
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_nbij' (fun φ => (φ t₁, φ t₂))
    (fun x => closedFlavoring₂ Φ Z₁ Z₂ x.1 x.2) (fun _ _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_closed₂ Φ hC x.1 x.2⟩)
    (fun φ hφ => (eq_closed₂_of_preserves Φ hC ht₁ ht₂ (Finset.mem_filter.mp hφ).2).symm)
    (fun x _ => by
      have h₂₁ : ¬ Z₁ t₂ := fun h => hC.disj t₂ h h₂
      simp only [closedFlavoring₂, h₁, h₂, h₂₁, ite_true, ite_false]) (fun φ hφ => ?_)
  have h := eq_closed₂_of_preserves Φ hC ht₁ ht₂ (Finset.mem_filter.mp hφ).2
  conv_lhs => rw [h]
  rw [loopWeight_closed₂ Φ hC]
  push_cast
  ring

end QED.GradedProof.X0

end
