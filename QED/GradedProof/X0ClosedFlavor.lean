/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.Embed

/-!
# (X₀): the flavour sum of a contraction with one closed fermion loop

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). Let `C` have one
external fermion pair and one closed fermion loop: a set `Z` of fermion vertices such that
`Z` (extended by `false` on the external slot) is invariant under the fermion pairing `σ`, every
vertex outside `Z` lies on the cycle of the external field, and `Z` is one cycle of `σ`. Then the
preserved flavourings are `φ_f` (`closedFlavoring`: `f` on `Z`, the open-line flavour elsewhere),
their weight is `c_f`, and the regulated amplitude (G₄) is `∑_f c_f A(φ_f)`
(`regulatedAmplitude_eq_closed`). Model: `QED.GradedProof.VP2.regulatedAmplitude_of_oneLoop`
(no external fermion).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel (Params Contraction ClosedLoop)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type} (Φ : Lepton.Flavors F)

/-- `Z`, extended by `false` on the external field. -/
def isZ (Z : Wick.FermionVertex κ → Prop) [DecidablePred Z] :
    Fin 1 ⊕ Wick.FermionVertex κ → Bool
  | .inl _ => false
  | .inr t => decide (Z t)

/-- The flavouring with flavour `f` on the closed loop `Z` and the open-line flavour elsewhere. -/
def closedFlavoring (Z : Wick.FermionVertex κ → Prop) [DecidablePred Z] (f : F) :
    Flavoring F κ :=
  fun t => if Z t then f else Φ.openLine

/-- The shape of a contraction with one closed fermion loop `Z`. -/
structure ClosedShape (C : Contraction 1 nA κ) (Z : Wick.FermionVertex κ → Prop)
    [DecidablePred Z] : Prop where
  inv : ∀ x, isZ Z (C.1.1 x) = isZ Z x
  open_cycle : ∀ t, ¬ Z t → C.1.1.SameCycle (.inr t) (.inl 0)
  loop_cycle : ∃ t₀, Z t₀ ∧ ∀ t, Z t → C.1.1.SameCycle (.inr t) (.inr t₀)

variable {C : Contraction 1 nA κ} {Z : Wick.FermionVertex κ → Prop} [DecidablePred Z]

theorem isZ_zpow (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) (z : ℤ) (x : Fin 1 ⊕ Wick.FermionVertex κ) :
    isZ Z ((C.1.1 ^ z) x) = isZ Z x := by
  induction z using Int.induction_on generalizing x with
  | zero => rfl
  | succ z ih => rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hZ]
  | pred z ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    have := hZ (C.1.1⁻¹ x)
    rwa [show C.1.1 (C.1.1⁻¹ x) = x by simp, eq_comm] at this

theorem isZ_of_sameCycle (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x)
    {x y : Fin 1 ⊕ Wick.FermionVertex κ} (h : C.1.1.SameCycle x y) : isZ Z x = isZ Z y := by
  obtain ⟨z, rfl⟩ := h
  exact (isZ_zpow hZ z x).symm

theorem fermionFlavor_closed (f : F) (a : Fin 1 ⊕ Wick.FermionVertex κ) :
    fermionFlavor Φ (closedFlavoring Φ Z f) a = if isZ Z a then f else Φ.openLine := by
  rcases a with i | t
  · rfl
  · simp [fermionFlavor, closedFlavoring, isZ]

theorem preserves_closed (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) (f : F) :
    Preserves Φ C (closedFlavoring Φ Z f) := fun a => by
  rw [fermionFlavor_closed, fermionFlavor_closed, hZ]

theorem eq_closed_of_preserves (hC : ClosedShape C Z) {t₀ : Wick.FermionVertex κ}
    (ht₀ : ∀ t, Z t → C.1.1.SameCycle (.inr t) (.inr t₀)) {φ : Flavoring F κ}
    (hφ : Preserves Φ C φ) : φ = closedFlavoring Φ Z (φ t₀) := by
  funext t
  unfold closedFlavoring
  split_ifs with h
  · exact fermionFlavor_eq_of_sameCycle hφ (ht₀ t h)
  · exact fermionFlavor_eq_of_sameCycle hφ (hC.open_cycle t h)

/-- The closed loop through `t₀ ∈ Z`. -/
def zLoop (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) (t₀ : Wick.FermionVertex κ) (h₀ : Z t₀) :
    ClosedLoop C :=
  ⟨Quotient.mk _ (.inr t₀), fun i h => by
    have := isZ_of_sameCycle hZ (Quotient.exact h)
    simp [isZ, h₀] at this⟩

theorem eq_zLoop (hC : ClosedShape C Z) {t₀ : Wick.FermionVertex κ} (h₀ : Z t₀)
    (ht₀ : ∀ t, Z t → C.1.1.SameCycle (.inr t) (.inr t₀)) (q : ClosedLoop C) :
    q = zLoop hC.inv t₀ h₀ := by
  obtain ⟨q, hq⟩ := q
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases x with i | t
  · exact absurd rfl (hq i)
  · by_cases h : Z t
    · exact Quotient.sound (ht₀ t h)
    · exact absurd (Quotient.sound (hC.open_cycle t h)).symm (hq 0)

open scoped Classical in
theorem loopWeight_closed (hC : ClosedShape C Z) (f : F) :
    loopWeight Φ C (closedFlavoring Φ Z f) = Φ.coeff f := by
  obtain ⟨t₀, h₀, ht₀⟩ := hC.loop_cycle
  rw [loopWeight, Fintype.prod_eq_single (zLoop hC.inv t₀ h₀)
    fun q hq => absurd (eq_zLoop hC h₀ ht₀ q) hq]
  have hout : isZ Z (zLoop hC.inv t₀ h₀).1.out = true := by
    have h1 : C.1.1.SameCycle (zLoop hC.inv t₀ h₀).1.out (.inr t₀) :=
      Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid C.1.1) (Sum.inr t₀)
    rw [isZ_of_sameCycle hC.inv h1]
    simp [isZ, h₀]
  rw [fermionFlavor_closed, hout]
  rfl

/-- **The flavour sum of a contraction with one closed loop.** -/
theorem regulatedAmplitude_eq_closed (P : Params) [Fintype F] [DecidableEq F]
    (D : Counterterms F) (hC : ClosedShape C Z) (g : Grading κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ =
      ∑ f, (Φ.coeff f : ℂ) *
        contractionAmplitude P Φ D C (closedFlavoring Φ Z f) g pIn kIn k αOut βIn μ := by
  classical
  obtain ⟨t₀, h₀, ht₀⟩ := hC.loop_cycle
  unfold regulatedAmplitude
  refine Finset.sum_nbij' (fun φ => φ t₀) (fun f => closedFlavoring Φ Z f)
    (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_closed Φ hC.inv f⟩)
    (fun φ hφ => (eq_closed_of_preserves Φ hC ht₀ (Finset.mem_filter.mp hφ).2).symm)
    (fun f _ => by simp only [closedFlavoring, h₀, ite_true]) (fun φ hφ => ?_)
  have h := eq_closed_of_preserves Φ hC ht₀ (Finset.mem_filter.mp hφ).2
  conv_lhs => rw [h]
  rw [loopWeight_closed Φ hC]

end QED.GradedProof.X0

end
