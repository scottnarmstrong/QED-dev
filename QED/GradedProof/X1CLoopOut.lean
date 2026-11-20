/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLoopWIn
public import QED.GradedProof.X1CLinesOut

/-!
# (X₁) piece C: flavours and closed loops of `glueOut`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3; the mirror of `X1CLoopIn`, `X1CLoopWIn`. On the open cycle of
`glueOut e C₁ C₂` the self-energy piece `C₂` comes first (from the outgoing external to the
bridge), then `C₁`.

* `openPathOut_left`, `openPathOut_right`: the open cycles of the pieces lie on that of the glue.
* `preserves_glueOut_iff`, `loopWeight_glueOut`: as for `glueIn`.
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
  (ha : C₁.1.1 (.inl 0) = .inr a) (hc : C₂.1.1 (.inr c) = .inl 0)

theorem glueOut_comm_left (z : Wick.FermionVertex (leftKinds κ e)) :
    (glueOut e C₁ C₂).1.1 (fL κ e 1 (.inl (.inr z))) = fL κ e 1 (.inl (C₁.1.1 (.inr z))) := by
  rw [fL_inl_inr, glueOut_left]

include hc in
theorem glueOut_comm_right {z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)} (hz : z ≠ .inr c) :
    (glueOut e C₁ C₂).1.1 (fR κ e 1 (.inr z)) = fR κ e 1 (.inr (C₂.1.1 z)) := by
  rcases h : C₂.1.1 z with i | t
  · refine absurd (C₂.1.1.injective ?_) hz
    rw [h, hc, Subsingleton.elim i 0]
  · rw [glueOut_right C₁ C₂ h, fR_inr_inr]

include hc in
theorem openPathOut_right (n : ℕ) :
    SameCycle (glueOut e C₁ C₂).1.1 (fR κ e 1 (.inr ((C₂.1.1 ^ n) (.inl 0)))) (.inl 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    by_cases hw : (C₂.1.1 ^ n) (.inl 0) = .inr c
    · rw [hw, hc]
      rfl
    · rw [← glueOut_comm_right C₁ C₂ hc hw, Equiv.Perm.sameCycle_apply_left]
      exact ih

include ha hc in
theorem openPathOut_left (n : ℕ) :
    SameCycle (glueOut e C₁ C₂).1.1 (fL κ e 1 (.inl ((C₁.1.1 ^ n) (.inl 0)))) (.inl 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rcases hw : (C₁.1.1 ^ n) (.inl 0) with i | t
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rw [ha, fL_inl_inr]
      rw [← glueOut_bridge C₁ C₂ ha hc, Equiv.Perm.sameCycle_apply_left]
      have h3 : C₂.1.1.SameCycle (.inl 0) (.inr c) :=
        Equiv.Perm.SameCycle.symm (⟨1, by simp [hc]⟩ : C₂.1.1.SameCycle (.inr c) (.inl 0))
      obtain ⟨m, hm⟩ := h3.exists_nat_pow_eq
      have h4 := openPathOut_right C₁ C₂ hc m
      rwa [hm] at h4
    · rw [← glueOut_comm_left C₁ C₂ t, Equiv.Perm.sameCycle_apply_left]
      rw [hw] at ih
      exact ih

include ha hc in
/-- **`glueOut` preserves a flavouring iff the pieces preserve its restrictions.** -/
theorem preserves_glueOut_iff (Φ : Lepton.Flavors F) (φ : Flavoring F κ) :
    Preserves Φ (glueOut e C₁ C₂) φ ↔
      Preserves Φ C₁ (flL κ e φ) ∧ Preserves Φ C₂ (flR κ e φ) := by
  have hCc : SameCycle (glueOut e C₁ C₂).1.1 (fR κ e 1 (.inr (.inr c))) (.inl 0) := by
    have h3 : C₂.1.1.SameCycle (.inl 0) (.inr c) :=
      Equiv.Perm.SameCycle.symm (⟨1, by simp [hc]⟩ : C₂.1.1.SameCycle (.inr c) (.inl 0))
    obtain ⟨m, hm⟩ := h3.exists_nat_pow_eq
    have h4 := openPathOut_right C₁ C₂ hc m
    rwa [hm] at h4
  have hAa : SameCycle (glueOut e C₁ C₂).1.1 (fL κ e 1 (.inl (.inr a))) (.inl 0) := by
    have h := openPathOut_left C₁ C₂ ha hc 1
    rwa [pow_one, ha] at h
  constructor
  · intro hφ
    have hfa : flL κ e φ a = Φ.openLine := by
      have := fermionFlavor_eq_of_sameCycle hφ hAa
      rwa [fermionFlavor_fL] at this
    have hfc : flR κ e φ c = Φ.openLine := by
      have := fermionFlavor_eq_of_sameCycle hφ hCc
      rwa [fermionFlavor_fR] at this
    refine ⟨fun z => ?_, fun z => ?_⟩
    · rcases z with i | t
      · have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rw [ha]
        exact hfa
      · have := hφ (fL κ e 1 (.inl (.inr t)))
        rwa [glueOut_comm_left, fermionFlavor_fL, fermionFlavor_fL] at this
    · by_cases hz : z = .inr c
      · subst hz
        rw [hc]
        exact hfc.symm
      · have := hφ (fR κ e 1 (.inr z))
        rwa [glueOut_comm_right C₁ C₂ hc hz, fermionFlavor_fR, fermionFlavor_fR] at this
  · rintro ⟨h₁, h₂⟩ z
    rcases z with i | t
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have := h₂ (.inl 0)
      rw [← fermionFlavor_fR Φ φ, ← fermionFlavor_fR Φ φ,
        ← glueOut_comm_right C₁ C₂ hc (by simp)] at this
      exact this
    · obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
      rcases x with t | t
      · have := h₁ (.inr t)
        rw [← fermionFlavor_fL Φ φ, ← fermionFlavor_fL Φ φ, ← glueOut_comm_left] at this
        exact this
      · by_cases ht : t = c
        · subst ht
          rw [glueOut_bridge C₁ C₂ ha hc]
          have h1 := h₁ (.inl 0)
          have h2 := h₂ (.inr t)
          rw [ha] at h1
          rw [hc] at h2
          change flL κ e φ a = flR κ e φ t
          exact h1.trans h2
        · have := h₂ (.inr t)
          rw [← fermionFlavor_fR Φ φ, ← fermionFlavor_fR Φ φ,
            ← glueOut_comm_right C₁ C₂ hc (by simpa using ht)] at this
          exact this

/-! ### Closed loops -/

theorem hcommOut_left (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e))
    (hz : ¬ SameCycle C₁.1.1 z (.inl 0)) :
    (glueOut e C₁ C₂).1.1 (fL κ e 1 (.inl z)) = fL κ e 1 (.inl (C₁.1.1 z)) := by
  rcases z with i | t
  · exact absurd (by rw [Subsingleton.elim i 0]) hz
  · exact glueOut_comm_left C₁ C₂ t

include hc in
theorem hcommOut_right (z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e))
    (hz : ¬ SameCycle C₂.1.1 z (.inl 0)) :
    (glueOut e C₁ C₂).1.1 (fR κ e 1 (.inr z)) = fR κ e 1 (.inr (C₂.1.1 z)) := by
  refine glueOut_comm_right C₁ C₂ hc fun h => hz ?_
  subst h
  exact ⟨1, by simp [hc]⟩

include hc in
/-- The closed loops of the pieces, as closed loops of `glueOut e C₁ C₂`. -/
noncomputable def loopMapOut : ClosedLoop C₁ ⊕ ClosedLoop C₂ → ClosedLoop (glueOut e C₁ C₂)
  | .inl q => ⟨Quotient.mk _ (fL κ e 1 (.inl q.1.out)), fun i h => by
      rw [Subsingleton.elim i 0] at h
      exact not_sameCycle_map (hcommOut_left C₁ C₂)
        (fun _ _ h => Sum.inl_injective ((fL κ e 1).injective h)) (not_sameCycle_closed q 0)
        (Equiv.Perm.SameCycle.symm (Quotient.exact h))⟩
  | .inr q => ⟨Quotient.mk _ (fR κ e 1 (.inr q.1.out)), fun i h => by
      rw [Subsingleton.elim i 0] at h
      exact not_sameCycle_map (hcommOut_right C₁ C₂ hc)
        (fun _ _ h => Sum.inr_injective ((fR κ e 1).injective h)) (not_sameCycle_closed q 0)
        (Equiv.Perm.SameCycle.symm (Quotient.exact h))⟩

include ha in
theorem loopMapOut_bijective : Function.Bijective (loopMapOut C₁ C₂ hc) := by
  have hf₁ : Function.Injective fun z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e) =>
      fL κ e 1 (.inl z) := fun _ _ h => Sum.inl_injective ((fL κ e 1).injective h)
  have hf₂ : Function.Injective fun z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e) =>
      fR κ e 1 (.inr z) := fun _ _ h => Sum.inr_injective ((fR κ e 1).injective h)
  constructor
  · rintro (q | q) (q' | q') h <;> have h' := Quotient.exact (congrArg Subtype.val h)
    · exact congrArg Sum.inl (closedLoop_eq (sameCycle_of_map (hcommOut_left C₁ C₂) hf₁
        (not_sameCycle_closed q 0) h'))
    · exfalso
      obtain ⟨n, hn⟩ := h'
      rw [zpow_apply_of_comm (hcommOut_left C₁ C₂) n _ (not_sameCycle_closed q 0)] at hn
      obtain ⟨i, hi⟩ := fL_eq_fR_inl hn
      refine not_sameCycle_closed q 0 ?_
      rw [Subsingleton.elim i 0] at hi
      exact ⟨n, hi⟩
    · exfalso
      obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.symm h'
      rw [zpow_apply_of_comm (hcommOut_left C₁ C₂) n _ (not_sameCycle_closed q' 0)] at hn
      obtain ⟨i, hi⟩ := fL_eq_fR_inl hn
      refine not_sameCycle_closed q' 0 ?_
      rw [Subsingleton.elim i 0] at hi
      exact ⟨n, hi⟩
    · exact congrArg Sum.inr (closedLoop_eq (sameCycle_of_map (hcommOut_right C₁ C₂ hc) hf₂
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
        have := openPathOut_left C₁ C₂ ha hc m
        rw [hm] at this
        exact hQ this
      let q : ClosedLoop C₁ := ⟨Quotient.mk _ (.inr t), fun i h => by
        rw [Subsingleton.elim i 0] at h
        exact hw (Equiv.Perm.SameCycle.symm (Quotient.exact h))⟩
      refine ⟨.inl q, closedLoop_eq ?_⟩
      have h1 : SameCycle (glueOut e C₁ C₂).1.1 (loopMapOut C₁ C₂ hc (.inl q)).1.out
          (fL κ e 1 (.inl q.1.out)) := Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      have h2 : SameCycle C₁.1.1 q.1.out (.inr t) :=
        Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      refine h1.trans ((sameCycle_map (hcommOut_left C₁ C₂) (not_sameCycle_closed q 0)
        h2).trans ?_)
      rw [hz]
      rfl
    · have hw : ¬ SameCycle C₂.1.1 (.inr t) (.inl 0) := fun h => by
        obtain ⟨m, hm⟩ := (Equiv.Perm.SameCycle.symm h).exists_nat_pow_eq
        have := openPathOut_right C₁ C₂ hc m
        rw [hm] at this
        exact hQ this
      let q : ClosedLoop C₂ := ⟨Quotient.mk _ (.inr t), fun i h => by
        rw [Subsingleton.elim i 0] at h
        exact hw (Equiv.Perm.SameCycle.symm (Quotient.exact h))⟩
      refine ⟨.inr q, closedLoop_eq ?_⟩
      have h1 : SameCycle (glueOut e C₁ C₂).1.1 (loopMapOut C₁ C₂ hc (.inr q)).1.out
          (fR κ e 1 (.inr q.1.out)) := Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      have h2 : SameCycle C₂.1.1 q.1.out (.inr t) :=
        Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
      refine h1.trans ((sameCycle_map (hcommOut_right C₁ C₂ hc) (not_sameCycle_closed q 0)
        h2).trans ?_)
      rw [hz]
      rfl

include ha hc in
open scoped Classical in
/-- **The regulator weight of `glueOut` is multiplicative** for a preserved flavouring. -/
theorem loopWeight_glueOut (Φ : Lepton.Flavors F) {φ : Flavoring F κ}
    (hφ : Preserves Φ (glueOut e C₁ C₂) φ) :
    loopWeight Φ (glueOut e C₁ C₂) φ =
      loopWeight Φ C₁ (flL κ e φ) * loopWeight Φ C₂ (flR κ e φ) := by
  unfold loopWeight
  rw [← Fintype.prod_bijective _ (loopMapOut_bijective C₁ C₂ ha hc) _ _ fun _ => rfl,
    Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun q _ => ?_
    have h : SameCycle (glueOut e C₁ C₂).1.1 (loopMapOut C₁ C₂ hc (.inl q)).1.out
        (fL κ e 1 (.inl q.1.out)) := Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
    rw [fermionFlavor_eq_of_sameCycle hφ h, fermionFlavor_fL]
  · refine Finset.prod_congr rfl fun q _ => ?_
    have h : SameCycle (glueOut e C₁ C₂).1.1 (loopMapOut C₁ C₂ hc (.inr q)).1.out
        (fR κ e 1 (.inr q.1.out)) := Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid _) _
    rw [fermionFlavor_eq_of_sameCycle hφ h, fermionFlavor_fR]

end QED.GradedProof.X1C

end
