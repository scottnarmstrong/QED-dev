/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLoopIn

/-!
# (X₁) piece C: the regulator weight of `glueIn` is multiplicative

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization).

The closed fermion loops of `glueIn e C₁ C₂` are those of `C₁` and those of `C₂`
(`loopMapIn`, a bijection by `loopMapIn_bijective`): off the open cycle the fermion pairing of
the glue is that of the pieces, and the open cycles of the pieces lie on the open cycle of the
glue. Hence `loopWeight_glueIn`: for a preserved flavouring the regulator weight (G₁‴) of the
glue is the product of those of the pieces.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction ClosedLoop)
open QED.Graded
open Equiv.Perm (SameCycle)

variable {N N₁ N₂ nA : ℕ} {F : Type} {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c)

include ha in
theorem hcommIn_left (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e))
    (hz : ¬ SameCycle C₁.1.1 z (.inl 0)) :
    (glueIn e C₁ C₂).1.1 (fL κ e 1 (.inl z)) = fL κ e 1 (.inl (C₁.1.1 z)) := by
  refine glueIn_comm_left C₁ C₂ ha fun h => hz ?_
  subst h
  exact ⟨1, by simp [ha]⟩

theorem hcommIn_right (z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e))
    (hz : ¬ SameCycle C₂.1.1 z (.inl 0)) :
    (glueIn e C₁ C₂).1.1 (fR κ e 1 (.inr z)) = fR κ e 1 (.inr (C₂.1.1 z)) := by
  rcases z with i | t
  · exact absurd (by rw [Subsingleton.elim i 0]) hz
  · exact glueIn_comm_right C₁ C₂ t

theorem fL_eq_fR_inl {w : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)}
    {w' : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)}
    (h : fL κ e 1 (.inl w) = fR κ e 1 (.inr w')) : ∃ i, w = .inl i := by
  rcases w with i | t
  · exact ⟨i, rfl⟩
  · rcases w' with j | t' <;> simp [fL, fR, Equiv.sumAssoc] at h

theorem not_sameCycle_closed {M nf nA' : ℕ} {κ' : Fin M → Wick.VertexKind}
    {C : Contraction nf nA' κ'} (q : ClosedLoop C) (i : Fin nf) :
    ¬ SameCycle C.1.1 q.1.out (.inl i) := fun h =>
  q.2 i ((Quotient.sound (Equiv.Perm.SameCycle.symm h)).trans (Quotient.out_eq q.1))

theorem closedLoop_eq {M nf nA' : ℕ} {κ' : Fin M → Wick.VertexKind}
    {C : Contraction nf nA' κ'} {q q' : ClosedLoop C} (h : SameCycle C.1.1 q.1.out q'.1.out) :
    q = q' :=
  Subtype.ext ((Quotient.out_eq q.1).symm.trans ((Quotient.sound h).trans (Quotient.out_eq q'.1)))

include ha in
theorem not_sameCycle_left (q : ClosedLoop C₁) :
    ¬ SameCycle (glueIn e C₁ C₂).1.1 (fL κ e 1 (.inl q.1.out)) (.inl 0) :=
  not_sameCycle_map (hcommIn_left C₁ C₂ ha)
    (fun _ _ h => Sum.inl_injective ((fL κ e 1).injective h))
    (not_sameCycle_closed q 0)

theorem not_sameCycle_right (q : ClosedLoop C₂) :
    ¬ SameCycle (glueIn e C₁ C₂).1.1 (fR κ e 1 (.inr q.1.out)) (.inl 0) :=
  not_sameCycle_map (hcommIn_right C₁ C₂)
    (fun _ _ h => Sum.inr_injective ((fR κ e 1).injective h))
    (not_sameCycle_closed q 0)

include ha in
/-- The closed loops of the pieces, as closed loops of `glueIn e C₁ C₂`. -/
noncomputable def loopMapIn : ClosedLoop C₁ ⊕ ClosedLoop C₂ → ClosedLoop (glueIn e C₁ C₂)
  | .inl q => ⟨Quotient.mk _ (fL κ e 1 (.inl q.1.out)), fun i h => by
      rw [Subsingleton.elim i 0] at h
      exact not_sameCycle_left C₁ C₂ ha q (Equiv.Perm.SameCycle.symm (Quotient.exact h))⟩
  | .inr q => ⟨Quotient.mk _ (fR κ e 1 (.inr q.1.out)), fun i h => by
      rw [Subsingleton.elim i 0] at h
      exact not_sameCycle_right C₁ C₂ q (Equiv.Perm.SameCycle.symm (Quotient.exact h))⟩

theorem loopMapIn_out_left (q : ClosedLoop C₁) :
    SameCycle (glueIn e C₁ C₂).1.1 (loopMapIn C₁ C₂ ha (.inl q)).1.out (fL κ e 1 (.inl q.1.out)) :=
  Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _

theorem loopMapIn_out_right (q : ClosedLoop C₂) :
    SameCycle (glueIn e C₁ C₂).1.1 (loopMapIn C₁ C₂ ha (.inr q)).1.out
      (fR κ e 1 (.inr q.1.out)) :=
  Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _

include hc in
theorem loopMapIn_bijective : Function.Bijective (loopMapIn C₁ C₂ ha) := by
  have hf₁ : Function.Injective fun z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e) =>
      fL κ e 1 (.inl z) := fun _ _ h => Sum.inl_injective ((fL κ e 1).injective h)
  have hf₂ : Function.Injective fun z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e) =>
      fR κ e 1 (.inr z) := fun _ _ h => Sum.inr_injective ((fR κ e 1).injective h)
  constructor
  · rintro (q | q) (q' | q') h <;> have h' := Quotient.exact (congrArg Subtype.val h)
    · exact congrArg Sum.inl (closedLoop_eq (sameCycle_of_map (hcommIn_left C₁ C₂ ha) hf₁
        (not_sameCycle_closed q 0) h'))
    · exfalso
      obtain ⟨n, hn⟩ := h'
      rw [zpow_apply_of_comm (hcommIn_left C₁ C₂ ha) n _ (not_sameCycle_closed q 0)] at hn
      obtain ⟨i, hi⟩ := fL_eq_fR_inl hn
      refine not_sameCycle_closed q 0 ?_
      rw [Subsingleton.elim i 0] at hi
      exact ⟨n, hi⟩
    · exfalso
      obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.symm h'
      rw [zpow_apply_of_comm (hcommIn_left C₁ C₂ ha) n _ (not_sameCycle_closed q' 0)] at hn
      obtain ⟨i, hi⟩ := fL_eq_fR_inl hn
      refine not_sameCycle_closed q' 0 ?_
      rw [Subsingleton.elim i 0] at hi
      exact ⟨n, hi⟩
    · exact congrArg Sum.inr (closedLoop_eq (sameCycle_of_map (hcommIn_right C₁ C₂) hf₂
        (not_sameCycle_closed q 0) h'))
  · intro Q
    have hQ := not_sameCycle_closed Q 0
    obtain ⟨z, hz⟩ : ∃ z, Q.1.out = z := ⟨_, rfl⟩
    rw [hz] at hQ
    rcases z with i | t
    · exact absurd (by rw [Subsingleton.elim i 0]) hQ
    obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
    rcases x with t | t
    · have hw : ¬ SameCycle C₁.1.1 (.inr t) (.inl 0) := fun h => by
        obtain ⟨m, hm⟩ := (Equiv.Perm.SameCycle.symm h).exists_nat_pow_eq
        have := openPathIn_left C₁ C₂ ha m
        rw [hm] at this
        exact hQ this
      let q : ClosedLoop C₁ := ⟨Quotient.mk _ (.inr t), fun i h => by
        rw [Subsingleton.elim i 0] at h
        exact hw (Equiv.Perm.SameCycle.symm (Quotient.exact h))⟩
      refine ⟨.inl q, closedLoop_eq ?_⟩
      have h1 := loopMapIn_out_left C₁ C₂ ha q
      have h2 : SameCycle C₁.1.1 q.1.out (.inr t) :=
        Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      refine h1.trans ((sameCycle_map (hcommIn_left C₁ C₂ ha) (not_sameCycle_closed q 0)
        h2).trans ?_)
      rw [hz]
      rfl
    · have hw : ¬ SameCycle C₂.1.1 (.inr t) (.inl 0) := fun h => by
        obtain ⟨m, hm⟩ := (Equiv.Perm.SameCycle.symm h).exists_nat_pow_eq
        have := openPathIn_right C₁ C₂ ha hc m
        rw [hm] at this
        exact hQ this
      let q : ClosedLoop C₂ := ⟨Quotient.mk _ (.inr t), fun i h => by
        rw [Subsingleton.elim i 0] at h
        exact hw (Equiv.Perm.SameCycle.symm (Quotient.exact h))⟩
      refine ⟨.inr q, closedLoop_eq ?_⟩
      have h1 := loopMapIn_out_right C₁ C₂ ha q
      have h2 : SameCycle C₂.1.1 q.1.out (.inr t) :=
        Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      refine h1.trans ((sameCycle_map (hcommIn_right C₁ C₂) (not_sameCycle_closed q 0)
        h2).trans ?_)
      rw [hz]
      rfl

include ha hc in
open scoped Classical in
/-- **The regulator weight of `glueIn` is multiplicative** for a preserved flavouring. -/
theorem loopWeight_glueIn (Φ : Lepton.Flavors F) {φ : Flavoring F κ}
    (hφ : Preserves Φ (glueIn e C₁ C₂) φ) :
    loopWeight Φ (glueIn e C₁ C₂) φ =
      loopWeight Φ C₁ (flL κ e φ) * loopWeight Φ C₂ (flR κ e φ) := by
  unfold loopWeight
  rw [← Fintype.prod_bijective _ (loopMapIn_bijective C₁ C₂ ha hc) _ _ fun _ => rfl,
    Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun q _ => ?_
    rw [fermionFlavor_eq_of_sameCycle hφ (loopMapIn_out_left C₁ C₂ ha q), fermionFlavor_fL]
  · refine Finset.prod_congr rfl fun q _ => ?_
    rw [fermionFlavor_eq_of_sameCycle hφ (loopMapIn_out_right C₁ C₂ ha q), fermionFlavor_fR]

end QED.GradedProof.X1C

end
