/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCCovConj
public import QED.ChainProof.GradedMirrorInv
public import QED.TwoLoop.LoopBoundTwoExact

/-!
# The charge-conjugate contraction: graph, graded flavours and the `fermionCt` momentum

Helper level, generic; the combinatorial part of the graded charge conjugation
(`QED/ChainProof/GradedMirrorConj.lean`). The charge-conjugate contraction
`QED.ChainProof.Conj.ccC C` reverses every fermion line and keeps the vertices, the vertex kinds
(so every grading) and the photon pairing.

* `isOnePI_ccC`, `loopCount_ccC`: the underlying graph is unchanged up to the orientation of the
  fermion lines, so one-particle irreducibility (X₁₈) and the loop number (T₂) are kept.
* `preserves_ccC_iff`, `loopWeight_ccC`: the graded flavourings (G₁) preserved by `C` and by
  `ccC C` agree, with the same regulator weight (G₁‴).
* `psiMomentum₂_ccC_of_fermionCt`: for a line-momentum assignment of `ccC C` whose pull-back to
  `C` is conserved, the momentum (T₅) entering a `fermionCt` vertex of `ccC C` is minus the one
  entering it in `C`: such a vertex has no photon field, so what enters it leaves it.
-/

@[expose] public section

open Complex Matrix
open QED.WickModel (Params Contraction Line FermionLine PhotonLine psiMomentum₂ Joined
  externalMomentum IsOnePI IsBridge VerticesConnected loopCount)

namespace QED.ChainProof.GradedMirror

open QED.ChainProof.Conj QED.TwoLoop.Routing

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### The graph of the charge-conjugate contraction -/

theorem ends_corrCC_iff (C : Contraction nf nA κ) (f : Line C) (u w : Fin N) :
    (((corrCC C).line f).ends = (u, w) ∨ ((corrCC C).line f).ends = (w, u)) ↔
      (f.ends = (u, w) ∨ f.ends = (w, u)) := by
  have h := (corrCC C).ends_line f
  rcases hfe : f.ends with ⟨a, b⟩
  rw [hfe] at h
  split_ifs at h <;> rw [h] <;> simp only [corrCC, Equiv.refl_apply, Prod.mk.injEq]
  tauto

theorem joined_ccC_iff (C : Contraction nf nA κ) (S : Set (Line (ccC C))) (u w : Fin N) :
    Joined (ccC C) S u w ↔ Joined C ((corrCC C).line ⁻¹' S) u w := by
  constructor
  · rintro ⟨f', hf', he⟩
    refine ⟨(corrCC C).line.symm f', by simpa using hf', ?_⟩
    rw [← ends_corrCC_iff, Equiv.apply_symm_apply]
    exact he
  · rintro ⟨f, hf, he⟩
    exact ⟨(corrCC C).line f, hf, (ends_corrCC_iff C f u w).mpr he⟩

theorem joined_symm {C : Contraction nf nA κ} {S : Set (Line C)} {u w : Fin N}
    (h : Joined C S u w) : Joined C S w u := by
  obtain ⟨f, hf, he⟩ := h
  exact ⟨f, hf, he.symm⟩

theorem verticesConnected_ccC {C : Contraction nf nA κ} (hV : VerticesConnected C) :
    VerticesConnected (ccC C) := fun u w =>
  Relation.ReflTransGen.mono (fun a b h => (joined_ccC_iff C ∅ a b).mpr (by simpa using h))
    _ _ (hV u w)

/-- **Charge conjugation keeps one-particle irreducibility.** -/
theorem isOnePI_ccC {C : Contraction nf nA κ} (hC : IsOnePI C) : IsOnePI (ccC C) := by
  obtain ⟨⟨hA₁, hA₂⟩, hV, hB⟩ := hC
  refine ⟨⟨fun i j h => hA₁ j i ((ccC_apply_eq_iff C _ _).mp h), fun i j h => hA₂ i j h⟩,
    verticesConnected_ccC hV, fun f' hf' => ?_⟩
  set f := (corrCC C).line.symm f'
  have hff : (corrCC C).line f = f' := Equiv.apply_symm_apply _ _
  have hS : (corrCC C).line ⁻¹' {f'} = {f} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, f]
    exact (Equiv.eq_symm_apply _).symm
  have hR : Relation.ReflTransGen (Joined C {f}) f.ends.1 f.ends.2 := not_not.mp (hB f)
  have hR' : Relation.ReflTransGen (Joined (ccC C) {f'}) f.ends.1 f.ends.2 :=
    Relation.ReflTransGen.mono (fun a b h => (joined_ccC_iff C {f'} a b).mpr (by rw [hS]; exact h))
      _ _ hR
  apply hf'
  have he := (ends_corrCC_iff C f f.ends.1 f.ends.2).mpr (Or.inl rfl)
  rw [hff] at he
  rcases he with he | he <;> rw [he]
  · exact hR'
  · exact Relation.ReflTransGen.mono (fun _ _ h => joined_symm h) _ _
      (Relation.ReflTransGen.swap _ _ hR')

theorem isOnePI_ccC_iff (C : Contraction nf nA κ) : IsOnePI (ccC C) ↔ IsOnePI C :=
  ⟨fun h => by simpa using isOnePI_ccC h, isOnePI_ccC⟩

/-- **Charge conjugation keeps the loop number**, for connected vertices. -/
theorem loopCount_ccC {C : Contraction nf nA κ} (hV : VerticesConnected C) :
    loopCount (ccC C) = loopCount C := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : ∀ {C' : Contraction nf nA κ}, loopCount C' = 0 := fun {C'} => by
      unfold loopCount
      refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun f _ => ?_)
      rcases f with f | g
      · exact f.1.1.elim0
      · exact g.1.1.elim0
    rw [h0, h0]
  · have h := QED.TwoLoop.LoopBoundTwo.loopCount_add_eq hV hN
    have h' := QED.TwoLoop.LoopBoundTwo.loopCount_add_eq (verticesConnected_ccC hV) hN
    have hc : Nat.card (Line (ccC C)) = Nat.card (Line C) := (Nat.card_congr (corrCC C).line).symm
    omega

/-! ### Graded flavours -/

section Flavour

variable {F : Type} (Φ : QED.Lepton.Flavors F)

theorem preserves_ccC_iff (C : Contraction nf nA κ) (φ : Graded.Flavoring F κ) :
    Graded.Preserves Φ (ccC C) φ ↔ Graded.Preserves Φ C φ := by
  constructor
  · intro h a
    have := h (C.1.1 a)
    rw [ccC_fst, perm_inv_apply] at this
    exact this.symm
  · intro h a
    have := h (C.1.1⁻¹ a)
    rw [perm_apply_inv] at this
    exact this.symm

theorem fermionFlavor_zpow {C : Contraction nf nA κ} {φ : Graded.Flavoring F κ}
    (hφ : Graded.Preserves Φ C φ) (x : Fin nf ⊕ Wick.FermionVertex κ) (i : ℤ) :
    Graded.fermionFlavor Φ φ ((C.1.1 ^ i) x) = Graded.fermionFlavor Φ φ x := by
  induction i using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [add_comm (i : ℤ) 1, _root_.zpow_one_add, Equiv.Perm.mul_apply, hφ, ih]
  | pred i ih =>
    rw [show -(i : ℤ) - 1 = -1 + -(i : ℤ) by ring, _root_.zpow_add, _root_.zpow_neg_one,
      Equiv.Perm.mul_apply, ← ih]
    have := hφ (C.1.1⁻¹ ((C.1.1 ^ (-(i : ℤ))) x))
    rw [perm_apply_inv] at this
    exact this.symm

theorem fermionFlavor_of_sameCycle {C : Contraction nf nA κ} {φ : Graded.Flavoring F κ}
    (hφ : Graded.Preserves Φ C φ) {x y : Fin nf ⊕ Wick.FermionVertex κ}
    (h : Equiv.Perm.SameCycle C.1.1 x y) :
    Graded.fermionFlavor Φ φ x = Graded.fermionFlavor Φ φ y := by
  obtain ⟨i, rfl⟩ := h
  exact (fermionFlavor_zpow Φ hφ x i).symm

open scoped Classical in
theorem loopWeight_ccC (C : Contraction nf nA κ) {φ : Graded.Flavoring F κ}
    (hφ : Graded.Preserves Φ C φ) :
    Graded.loopWeight Φ (ccC C) φ = Graded.loopWeight Φ C φ := by
  unfold Graded.loopWeight
  refine Fintype.prod_equiv (closedLoopEquiv C) _ _ fun q => ?_
  congr 1
  refine fermionFlavor_of_sameCycle Φ hφ ?_
  have h1 : (closedLoopEquiv C q).1 = Quotient.mk _ q.1.out := by
    show Quotient.congrRight _ q.1 = _
    conv_lhs => rw [← Quotient.out_eq q.1]
    rfl
  have h2 : Quotient.mk (Equiv.Perm.SameCycle.setoid C.1.1) (closedLoopEquiv C q).1.out =
      Quotient.mk _ q.1.out := by
    rw [Quotient.out_eq, h1]
  exact (Quotient.exact h2).symm

end Flavour

/-! ### The momentum of a `fermionCt` vertex -/

section Momentum

open scoped Classical in
/-- The momentum (T₅) entering vertex `t` through its `Ψ` field, as a sum over the lines and the
external `Ψ̄` fields. -/
theorem psiMomentum₂_eq_sum (C : Contraction nf nA κ) (pIn : Fin nf → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (t : Wick.FermionVertex κ) :
    psiMomentum₂ C pIn k t = (∑ f : FermionLine C, if f.1 = t then k (.inl f) else 0) +
      ∑ i, if C.1.1 (.inr t) = .inl i then pIn i else 0 := by
  unfold psiMomentum₂
  split
  · rename_i i h
    have h1 : (∑ f : FermionLine C, if f.1 = t then k (.inl f) else 0) = 0 := by
      refine Finset.sum_eq_zero fun f _ => ite_eq_right fun hf => ?_
      have := f.2
      rw [hf, h] at this
      exact absurd this (by simp)
    simp only [h, Sum.inl.injEq, h1, zero_add]
    rw [Finset.sum_ite_eq]
    simp
  · rename_i s h
    have h2 : (∑ i, if C.1.1 (.inr t) = .inl i then pIn i else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => ite_eq_right (by rw [h]; simp)
    rw [h2, add_zero, Finset.sum_eq_single ⟨t, by simp [h]⟩]
    · simp
    · intro f _ hf
      exact ite_eq_right fun h' => hf (Subtype.ext h')
    · simp

theorem photonSlot_ne_of_fermionCt {t : Fin N} (ht : κ t = .fermionCt) (a : Wick.PhotonSlot κ) :
    a.1 ≠ t := by
  obtain ⟨v, j⟩ := a
  rintro (rfl : v = t)
  have : (κ v).photonSlots = 0 := by rw [ht]; rfl
  exact (this ▸ j).elim0

open scoped Classical in
/-- The line momentum entering a `fermionCt` vertex: the incoming fermion line minus the
outgoing one (no photon line ends there). -/
theorem inflow_of_fermionCt (C : Contraction nf nA κ) (P : Line C → Fin 4 → ℝ)
    (t : Wick.FermionVertex κ) (ht : κ t.1 = .fermionCt) :
    inflow P t.1 = (∑ f : FermionLine C, if f.1 = t then P (.inl f) else 0) -
      ∑ f : FermionLine C, if f.tail = t then P (.inl f) else 0 := by
  unfold inflow
  rw [Fintype.sum_sum_type]
  have hph : ∀ g : PhotonLine C,
      ((if (QED.WickModel.Line.ends (Sum.inr g : Line C)).2 = t.1 then P (.inr g) else 0) -
        (if (QED.WickModel.Line.ends (Sum.inr g : Line C)).1 = t.1 then P (.inr g) else 0)) =
        0 := fun g => by
    have h1 := photonSlot_ne_of_fermionCt ht g.head
    have h2 := photonSlot_ne_of_fermionCt ht g.1
    simp [QED.WickModel.Line.ends, h1, h2]
  rw [Finset.sum_eq_zero fun g _ => hph g, add_zero, Finset.sum_sub_distrib]
  simp only [QED.WickModel.Line.ends, ← Subtype.ext_iff]

open scoped Classical in
/-- The external momentum entering a `fermionCt` vertex. -/
theorem externalMomentum_of_fermionCt (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (t : Wick.FermionVertex κ) (ht : κ t.1 = .fermionCt) :
    externalMomentum C pOut pIn kIn t.1 =
      (∑ i, if C.1.1 (.inr t) = .inl i then pIn i else 0) -
        ∑ i, if C.1.1 (.inl i) = .inr t then pOut i else 0 := by
  have hex : ∀ X : Wick.FermionVertex κ → Prop,
      (∃ t' : Wick.FermionVertex κ, t'.1 = t.1 ∧ X t') ↔ X t := fun X =>
    ⟨fun ⟨t', h1, h2⟩ => Subtype.ext h1 ▸ h2, fun h => ⟨t, rfl, h⟩⟩
  have hph : ∀ j, ¬ ∃ a : Wick.PhotonSlot κ, a.1 = t.1 ∧ C.1.2 (.inl j) = .inr a :=
    fun j ⟨a, ha, _⟩ => photonSlot_ne_of_fermionCt ht a ha
  unfold externalMomentum
  simp only [hex, hph, ite_false, Finset.sum_const_zero, add_zero]

open scoped Classical in
/-- **The momentum of a `fermionCt` vertex reverses under charge conjugation**: for line
momenta `k'` of `ccC C` whose pull-back to `C` is conserved, the momentum (T₅) entering a
`fermionCt` vertex in `ccC C` (with external `Ψ̄` momenta `-pOut`) is minus the momentum entering
it in `C`. -/
theorem psiMomentum₂_ccC_of_fermionCt (C : Contraction nf nA κ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (ccC C) → Fin 4 → ℝ)
    (hk : IsConserved C pOut pIn kIn ((corrCC C).pull k')) (t : Wick.FermionVertex κ)
    (ht : κ t.1 = .fermionCt) :
    psiMomentum₂ (ccC C) (-pOut) k' t = -psiMomentum₂ C pIn ((corrCC C).pull k') t := by
  set P := (corrCC C).pull k'
  have hc := hk t.1
  rw [inflow_of_fermionCt C P t ht, externalMomentum_of_fermionCt C pOut pIn kIn t ht] at hc
  have h1 : (∑ f' : FermionLine (ccC C), if f'.1 = t then k' (.inl f') else 0) =
      -∑ f : FermionLine C, if f.tail = t then P (.inl f) else 0 := by
    rw [← Equiv.sum_comp (fermEquiv C), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [fermEquiv_apply, lineCC_val]
    split_ifs
    · simp only [P]
      rw [pull_inl, neg_neg]
    · rw [neg_zero]
  have h2 : (∑ i, if (ccC C).1.1 (.inr t) = .inl i then (-pOut) i else 0) =
      -∑ i, if C.1.1 (.inl i) = .inr t then pOut i else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ccC_apply_eq_iff, Pi.neg_apply]
    split_ifs <;> simp
  rw [psiMomentum₂_eq_sum, psiMomentum₂_eq_sum, h1, h2]
  have h3 : ∀ a b c d : Fin 4 → ℝ, a - b + (c - d) = 0 → -b + -d = -(a + c) := fun a b c d h => by
    rw [← neg_add, neg_inj]
    have : a + c = b + d := by
      have := congrArg (· + (b + d)) h
      simp only [zero_add] at this
      rw [← this]
      abel
    exact this.symm
  exact h3 _ _ _ _ hc

end Momentum

end QED.ChainProof.GradedMirror

end
