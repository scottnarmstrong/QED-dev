/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLoopWIn
public import QED.GradedProof.X1CGlueP

/-!
# (X₁) piece C: flavours and closed loops of `glueP`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3. The fermion pairing of `glueP e C₁ C₂` is the disjoint union
of those of the pieces, so `glueP` preserves a flavouring iff the pieces preserve its
restrictions (`preserves_glueP_iff`), and its closed loops are those of the pieces
(`loopMapP_bijective`), so the regulator weight is multiplicative (`loopWeight_glueP`).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction ClosedLoop)
open QED.Graded
open Equiv.Perm (SameCycle)

theorem zpow_apply_of_comm_all {X Y : Type*} {σ : Equiv.Perm X} {τ : Equiv.Perm Y} {f : X → Y}
    (hcomm : ∀ z, τ (f z) = f (σ z)) (n : ℤ) (z : X) : (τ ^ n) (f z) = f ((σ ^ n) z) := by
  induction n using Int.induction_on generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hcomm, ih]
  | pred n ih =>
    have h1 : τ.symm (f z) = f (σ.symm z) := by
      rw [Equiv.symm_apply_eq, hcomm, Equiv.apply_symm_apply]
    rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def, Equiv.Perm.inv_def, h1, ih]

variable {N N₁ N₂ : ℕ} {F : Type} {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 1 (leftKinds κ e)) (C₂ : Contraction 0 2 (rightKinds κ e))

theorem glueP_comm_right (z : Fin 0 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    (glueP e C₁ C₂).1.1 (fL κ e 1 (.inr z)) = fL κ e 1 (.inr (C₂.1.1 z)) :=
  dsum_apply_inr _ _ _ _

theorem fermionFlavor_fLr (Φ : Lepton.Flavors F) (φ : Flavoring F κ)
    (z : Fin 0 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    fermionFlavor Φ φ (fL κ e 1 (.inr z)) = fermionFlavor Φ (flR κ e φ) z := by
  rcases z with i | t
  · exact i.elim0
  · rfl

/-- **`glueP` preserves a flavouring iff the pieces preserve its restrictions.** -/
theorem preserves_glueP_iff (Φ : Lepton.Flavors F) (φ : Flavoring F κ) :
    Preserves Φ (glueP e C₁ C₂) φ ↔
      Preserves Φ C₁ (flL κ e φ) ∧ Preserves Φ C₂ (flR κ e φ) := by
  constructor
  · intro hφ
    refine ⟨fun z => ?_, fun z => ?_⟩
    · have := hφ (fL κ e 1 (.inl z))
      rwa [glueP_fermion_left, fermionFlavor_fL, fermionFlavor_fL] at this
    · have := hφ (fL κ e 1 (.inr z))
      rwa [glueP_comm_right, fermionFlavor_fLr, fermionFlavor_fLr] at this
  · rintro ⟨h₁, h₂⟩ z
    obtain ⟨w, rfl⟩ := (fL κ e 1).surjective z
    rcases w with w | w
    · rw [glueP_fermion_left, fermionFlavor_fL, fermionFlavor_fL]
      exact h₁ w
    · rw [glueP_comm_right, fermionFlavor_fLr, fermionFlavor_fLr]
      exact h₂ w

/-- The closed loops of the pieces, as closed loops of `glueP e C₁ C₂`. -/
noncomputable def loopMapP : ClosedLoop C₁ ⊕ ClosedLoop C₂ → ClosedLoop (glueP e C₁ C₂)
  | .inl q => ⟨Quotient.mk _ (fL κ e 1 (.inl q.1.out)), fun i h => by
      rw [Subsingleton.elim i 0] at h
      obtain ⟨n, hn⟩ := Quotient.exact h
      rw [show (Sum.inl 0 : Fin 1 ⊕ Wick.FermionVertex κ) = fL κ e 1 (.inl (.inl 0)) from rfl,
        zpow_apply_of_comm_all (glueP_fermion_left e C₁ C₂)] at hn
      exact not_sameCycle_closed q 0
        (Equiv.Perm.SameCycle.symm ⟨n, Sum.inl_injective ((fL κ e 1).injective hn)⟩)⟩
  | .inr q => ⟨Quotient.mk _ (fL κ e 1 (.inr q.1.out)), fun i h => by
      obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.symm (Quotient.exact h)
      rw [zpow_apply_of_comm_all (glueP_comm_right C₁ C₂),
        show (Sum.inl i : Fin 1 ⊕ Wick.FermionVertex κ) = fL κ e 1 (.inl (.inl i)) from rfl]
        at hn
      exact Sum.inr_ne_inl ((fL κ e 1).injective hn)⟩

theorem loopMapP_bijective : Function.Bijective (loopMapP C₁ C₂ (e := e)) := by
  have hc₁ := zpow_apply_of_comm_all (glueP_fermion_left e C₁ C₂)
  have hc₂ := zpow_apply_of_comm_all (glueP_comm_right C₁ C₂)
  constructor
  · rintro (q | q) (q' | q') h <;> obtain ⟨n, hn⟩ := Quotient.exact (congrArg Subtype.val h)
    · rw [hc₁] at hn
      exact congrArg Sum.inl (closedLoop_eq ⟨n, Sum.inl_injective ((fL κ e 1).injective hn)⟩)
    · rw [hc₁] at hn
      exact absurd ((fL κ e 1).injective hn) Sum.inl_ne_inr
    · rw [hc₂] at hn
      exact absurd ((fL κ e 1).injective hn) Sum.inr_ne_inl
    · rw [hc₂] at hn
      exact congrArg Sum.inr (closedLoop_eq ⟨n, Sum.inr_injective ((fL κ e 1).injective hn)⟩)
  · intro Q
    have hQ := not_sameCycle_closed Q 0
    obtain ⟨w, hw⟩ := (fL κ e 1).surjective Q.1.out
    rcases w with w | w
    · have hw' : ¬ SameCycle C₁.1.1 w (.inl 0) := fun ⟨n, hn⟩ => hQ ⟨n, by
        rw [← hw, hc₁, hn]
        rfl⟩
      let q : ClosedLoop C₁ := ⟨Quotient.mk _ w, fun i h => by
        rw [Subsingleton.elim i 0] at h
        exact hw' (Equiv.Perm.SameCycle.symm (Quotient.exact h))⟩
      refine ⟨.inl q, closedLoop_eq ?_⟩
      have h1 : SameCycle (glueP e C₁ C₂).1.1 (loopMapP C₁ C₂ (.inl q)).1.out
          (fL κ e 1 (.inl q.1.out)) := Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      obtain ⟨n, hn⟩ : SameCycle C₁.1.1 q.1.out w :=
        Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      refine h1.trans ⟨n, ?_⟩
      rw [hc₁, hn, hw]
    · let q : ClosedLoop C₂ := ⟨Quotient.mk _ w, fun i => i.elim0⟩
      refine ⟨.inr q, closedLoop_eq ?_⟩
      have h1 : SameCycle (glueP e C₁ C₂).1.1 (loopMapP C₁ C₂ (.inr q)).1.out
          (fL κ e 1 (.inr q.1.out)) := Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      obtain ⟨n, hn⟩ : SameCycle C₂.1.1 q.1.out w :=
        Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      refine h1.trans ⟨n, ?_⟩
      rw [hc₂, hn, hw]

open scoped Classical in
/-- **The regulator weight of `glueP` is multiplicative** for a preserved flavouring. -/
theorem loopWeight_glueP (Φ : Lepton.Flavors F) {φ : Flavoring F κ}
    (hφ : Preserves Φ (glueP e C₁ C₂) φ) :
    loopWeight Φ (glueP e C₁ C₂) φ =
      loopWeight Φ C₁ (flL κ e φ) * loopWeight Φ C₂ (flR κ e φ) := by
  unfold loopWeight
  rw [← Fintype.prod_bijective _ (loopMapP_bijective C₁ C₂) _ _ fun _ => rfl,
    Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun q _ => ?_
    have h : SameCycle (glueP e C₁ C₂).1.1 (loopMapP C₁ C₂ (.inl q)).1.out
        (fL κ e 1 (.inl q.1.out)) := Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
    rw [fermionFlavor_eq_of_sameCycle hφ h, fermionFlavor_fL]
  · refine Finset.prod_congr rfl fun q _ => ?_
    have h : SameCycle (glueP e C₁ C₂).1.1 (loopMapP C₁ C₂ (.inr q)).1.out
        (fL κ e 1 (.inr q.1.out)) := Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
    rw [fermionFlavor_eq_of_sameCycle hφ h, fermionFlavor_fLr]

end QED.GradedProof.X1C

end
