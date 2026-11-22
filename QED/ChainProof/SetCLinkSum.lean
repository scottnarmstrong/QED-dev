/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkClassMain
public import QED.ChainProof.SetALinkSum

/-!
# The set (c) family summed with coefficient one per class

Helper for the set (c) headline (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(decision D-58), the enumeration step. The relabellings `relabelK π hκ R.rep` of the
representatives `R ∈ repsC N`, at the transported gradings, are exactly the 1PI graded
contractions of `N` vertices of graded order `7` satisfying (Sc₃) `QED.ThreeLoop.IsSetC`
(`QED.ChainProof.SetCLink.exists_rep_setC`), and they are pairwise distinct
(`relabelK_repC_inj`): no orbit has a nontrivial automorphism and distinct representatives give
distinct orbits.

Distinctness uses an intrinsic vertex list `vlistC C`, read off the contraction by following the
fermion pairing from the external field (the open line), then the external photon, the photon
pairing from the open line and the fermion pairing once more (the element), each vertex at its
first occurrence. It is carried along by relabelling, and it is `0, 1, …, N - 1` for every
representative, so it determines the permutation. The raw list, the slot indices of the photon
partners of the open line, and the kinds then separate the representatives.

## Main statements

* `QED.ChainProof.SetCLink.isSetC_relabelK`: (Sc₃) is invariant under relabelling.
* `QED.ChainProof.SetCLink.relabelK_repC_inj`: the relabelled representatives are pairwise
  distinct.
* `QED.ChainProof.SetCLink.sum_setC`: for every `G` invariant under relabelling 1PI graded
  contractions, the sum over the kind sequences of `N` vertices, their gradings of graded order
  `7` (levels in `0, …, 7`) and their 1PI set (c) contractions of `fermionSign C * G C g` is `N!`
  times the signed sum of `G` over the representatives with `N` vertices.
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum QED.GradedProof.VP2
open QED.ChainProof.SetALink (fvt fstep pstep pidx)

variable {N : ℕ} {κ κ' : Fin N → Wick.VertexKind}

/-! ### Invariance of (Sc₃) -/

/-- **(Sc₃) is invariant under relabelling.** -/
theorem isSetC_relabelK (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t)
    {C : Contraction 1 1 κ} {g : Graded.Grading κ} (hC : QED.ThreeLoop.IsSetC C g) :
    QED.ThreeLoop.IsSetC (relabelK π hκ C) (gradMap π hκ g) := by
  have hsc := SetALink.sameCycle_relabelK π hκ C
  obtain ⟨hph, hD | hB | hS⟩ := hC
  · refine ⟨fun t ht => hph _ (by show κ (π.symm t.1) = _; rw [kind_symm_apply π hκ]; exact ht), ?_⟩
    obtain ⟨t₀, k0, hexh⟩ := hD
    refine Or.inl ⟨π t₀, by rw [hκ, k0], fun t => ?_⟩
    obtain ⟨t, rfl⟩ := π.surjective t
    rcases hexh t with rfl | ⟨v, rfl, hv⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨fvMap π hκ v, rfl, (hsc (.inl 0) (.inr v)).2 hv⟩
  · refine ⟨fun t ht => hph _ (by show κ (π.symm t.1) = _; rw [kind_symm_apply π hκ]; exact ht), ?_⟩
    obtain ⟨u, w, ku, kw, huw, su, sw, hexh⟩ := hB
    refine Or.inr (Or.inl ⟨fvMap π hκ u, fvMap π hκ w, by rw [fvMap_val, hκ, ku],
      by rw [fvMap_val, hκ, kw], (fvMap π hκ).injective.ne huw,
      by rw [relabelK_fst_inr', su, extFK_inr], by rw [relabelK_fst_inr', sw, extFK_inr],
      fun t => ?_⟩)
    obtain ⟨t, rfl⟩ := π.surjective t
    simp only [fvMap_val, π.injective.eq_iff]
    rcases hexh t with h | h | ⟨v, rfl, hv⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨fvMap π hκ v, rfl, (hsc (.inl 0) (.inr v)).2 hv⟩)
  · refine ⟨fun t ht => hph _ (by show κ (π.symm t.1) = _; rw [kind_symm_apply π hκ]; exact ht), ?_⟩
    obtain ⟨hall, t₀, hg1, hu⟩ := hS
    refine Or.inr (Or.inr ⟨fun t => ?_, ctMap π hκ t₀, ?_, fun t => ?_⟩)
    · obtain ⟨t, rfl⟩ := π.surjective t
      obtain ⟨v, rfl, hv⟩ := hall t
      exact ⟨fvMap π hκ v, rfl, (hsc (.inl 0) (.inr v)).2 hv⟩
    · simp only [gradMap, Equiv.symm_apply_apply, hg1]
    · rw [← (ctMap π hκ).apply_symm_apply t, hu ((ctMap π hκ).symm t)]

/-! ### The intrinsic vertex list -/

/-- The open line: five steps of the fermion pairing from `Ψ(x)`. -/
def openC (C : Contraction 1 1 κ) : List (Fin N) :=
  let o₀ := fvt (C.1.1 (.inl 0))
  let o₁ := o₀.flatMap (fstep C)
  let o₂ := o₁.flatMap (fstep C)
  let o₃ := o₂.flatMap (fstep C)
  o₀ ++ o₁ ++ o₂ ++ o₃ ++ o₃.flatMap (fstep C)

/-- The vertex of the photon partner of the external photon. -/
def extC (C : Contraction 1 1 κ) : List (Fin N) :=
  Sum.elim (fun _ => []) (fun s => [s.1]) (C.1.2 (.inl 0))

/-- The raw vertex list: the open line, the vertex of the external photon, the vertices of the
photon partners of the open line, and their fermion partners. -/
def rawC (C : Contraction 1 1 κ) : List (Fin N) :=
  openC C ++ extC C ++ (openC C).flatMap (pstep C) ++
    ((openC C).flatMap (pstep C)).flatMap (fstep C)

/-- The vertex list: the raw list, each vertex at its first occurrence. -/
def vlistC (C : Contraction 1 1 κ) : List (Fin N) := (rawC C).reverse.dedup.reverse

/-- The slot indices of the photon partners of the open line. -/
def idxC (C : Contraction 1 1 κ) : List ℕ := (openC C).flatMap (pidx C)

section Equivariance

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 1 κ)

theorem openC_relabelK : openC (relabelK π hκ C) = (openC C).map π := by
  have hf := SetALink.flatMap_map_map π (SetALink.fstep_relabelK π hκ C)
  simp only [openC, SetALink.fvt_relabelK_inl, hf, List.map_append]

theorem extC_relabelK : extC (relabelK π hκ C) = (extC C).map π := by
  unfold extC
  rw [relabelK_snd_inl]
  rcases C.1.2 (.inl 0) with j | s <;> rfl

theorem rawC_relabelK : rawC (relabelK π hκ C) = (rawC C).map π := by
  have hf := SetALink.flatMap_map_map π (SetALink.fstep_relabelK π hκ C)
  have hp := SetALink.flatMap_map_map π (SetALink.pstep_relabelK π hκ C)
  simp only [rawC, openC_relabelK, extC_relabelK, hf, hp, List.map_append]

theorem vlistC_relabelK : vlistC (relabelK π hκ C) = (vlistC C).map π := by
  rw [vlistC, vlistC, rawC_relabelK, ← List.map_reverse,
    List.dedup_map_of_injective π.injective, List.map_reverse]

theorem idxC_relabelK : idxC (relabelK π hκ C) = idxC C := by
  rw [idxC, idxC, openC_relabelK, SetALink.flatMap_map_of π (SetALink.pidx_relabelK π hκ C)]

end Equivariance

/-! ### Properties of the representatives -/

theorem repsC_cases (P : ∀ N, RepC N → Prop) (h3 : ∀ R ∈ repsC 3, P 3 R)
    (h4 : ∀ R ∈ repsC 4, P 4 R) (h5 : ∀ R ∈ repsC 5, P 5 R) (h6 : ∀ R ∈ repsC 6, P 6 R)
    (h7 : ∀ R ∈ repsC 7, P 7 R) : ∀ R ∈ repsC N, P N R := by
  by_cases e3 : N = 3
  · subst e3; exact h3
  by_cases e4 : N = 4
  · subst e4; exact h4
  by_cases e5 : N = 5
  · subst e5; exact h5
  by_cases e6 : N = 6
  · subst e6; exact h6
  by_cases e7 : N = 7
  · subst e7; exact h7
  rw [repsC, repsCZ_eq_nil e4 e5 e6 e7, repsCS_eq_nil e3 e4]
  simp

/-- The properties of the representatives used by the count. -/
def RepCProps {N : ℕ} (R : RepC N) : Prop :=
  IsOnePI R.rep ∧ QED.ThreeLoop.IsSetC R.rep R.grad ∧ Graded.gradedOrder R.kinds R.grad = 7 ∧
    (∀ t, R.grad t ≤ 1) ∧ vlistC R.rep = List.finRange N

theorem vlistC_repB : ∀ i, vlistC (repB i) = List.finRange 7 := by decide +kernel

theorem vlistC_repD : ∀ i s, vlistC (repD i s) = List.finRange 6 := by decide +kernel

theorem vlistC_repC6 : vlistC repCB0 = List.finRange 6 ∧ vlistC repCB1 = List.finRange 6 := by
  decide +kernel

theorem vlistC_repC5 : vlistC repCB2 = List.finRange 5 ∧ vlistC repCB3 = List.finRange 5 ∧
    vlistC repCB4 = List.finRange 5 ∧ (∀ s, vlistC (repCD0 s) = List.finRange 5) ∧
    ∀ s, vlistC (repCD1 s) = List.finRange 5 := by
  decide +kernel

theorem vlistC_repC4 : (∀ s, vlistC (repCD2 s) = List.finRange 4) ∧
    (∀ s, vlistC (repCD3 s) = List.finRange 4) ∧ (∀ s, vlistC (repCD4 s) = List.finRange 4) ∧
    vlistC repS0 = List.finRange 4 ∧ vlistC repS1 = List.finRange 4 := by
  decide +kernel

theorem vlistC_repC3 : vlistC repS2 = List.finRange 3 ∧ vlistC repS3 = List.finRange 3 ∧
    vlistC repS4 = List.finRange 3 := by
  decide +kernel

theorem zero_le_one' {N : ℕ} {κ : Fin N → Wick.VertexKind} :
    ∀ t, (0 : Graded.Grading κ) t ≤ 1 := fun _ => Nat.zero_le _

theorem gOne_le {N : ℕ} {κ : Fin N → Wick.VertexKind} : ∀ t, gOne κ t ≤ 1 := fun _ => le_rfl

theorem repsC_props : ∀ R ∈ repsC N, RepCProps R := by
  refine repsC_cases (fun _ R => RepCProps R) ?_ ?_ ?_ ?_ ?_
  · simp only [repsC, repsCZ, repsCS, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false]
    obtain ⟨v2, v3, v4⟩ := vlistC_repC3
    rintro R (rfl | rfl | rfl)
    · exact ⟨isOnePI_repS2, isSetC_repS2, gradedOrder_kS2, gOne_le, v2⟩
    · exact ⟨isOnePI_repS3, isSetC_repS3, gradedOrder_kS3, gOne_le, v3⟩
    · exact ⟨isOnePI_repS4, isSetC_repS4, gradedOrder_kS4, gOne_le, v4⟩
  · simp only [repsC, repsCZ, repsCS, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    obtain ⟨d2, d3, d4, s0, s1⟩ := vlistC_repC4
    rintro R (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨isOnePI_repCD2 0, isSetC_repCD2 0, gradedOrder_kCD2, zero_le_one', d2 0⟩
    · exact ⟨isOnePI_repCD2 1, isSetC_repCD2 1, gradedOrder_kCD2, zero_le_one', d2 1⟩
    · exact ⟨isOnePI_repCD3 0, isSetC_repCD3 0, gradedOrder_kCD3, zero_le_one', d3 0⟩
    · exact ⟨isOnePI_repCD3 1, isSetC_repCD3 1, gradedOrder_kCD3, zero_le_one', d3 1⟩
    · exact ⟨isOnePI_repCD4 0, isSetC_repCD4 0, gradedOrder_kCD4, zero_le_one', d4 0⟩
    · exact ⟨isOnePI_repCD4 1, isSetC_repCD4 1, gradedOrder_kCD4, zero_le_one', d4 1⟩
    · exact ⟨isOnePI_repS0, isSetC_repS0, gradedOrder_kS0, gOne_le, s0⟩
    · exact ⟨isOnePI_repS1, isSetC_repS1, gradedOrder_kS1, gOne_le, s1⟩
  · simp only [repsC, repsCZ, repsCS, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    obtain ⟨b2, b3, b4, d0, d1⟩ := vlistC_repC5
    rintro R (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨isOnePI_repCB2, isSetC_repCB2, gradedOrder_kCB2, zero_le_one', b2⟩
    · exact ⟨isOnePI_repCB3, isSetC_repCB3, gradedOrder_kCB3, zero_le_one', b3⟩
    · exact ⟨isOnePI_repCB4, isSetC_repCB4, gradedOrder_kCB4, zero_le_one', b4⟩
    · exact ⟨isOnePI_repCD0 0, isSetC_repCD0 0, gradedOrder_kCD0, zero_le_one', d0 0⟩
    · exact ⟨isOnePI_repCD0 1, isSetC_repCD0 1, gradedOrder_kCD0, zero_le_one', d0 1⟩
    · exact ⟨isOnePI_repCD1 0, isSetC_repCD1 0, gradedOrder_kCD1, zero_le_one', d1 0⟩
    · exact ⟨isOnePI_repCD1 1, isSetC_repCD1 1, gradedOrder_kCD1, zero_le_one', d1 1⟩
  · simp only [repsC, repsCZ, repsCS, List.append_nil, List.mem_append, List.mem_flatMap,
      List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil, or_false]
    obtain ⟨b0, b1⟩ := vlistC_repC6
    rintro R (⟨i, rfl | rfl⟩ | rfl | rfl)
    · exact ⟨isOnePI_repD i 0, isSetC_repD i 0, gradedOrder_kD, zero_le_one', vlistC_repD i 0⟩
    · exact ⟨isOnePI_repD i 1, isSetC_repD i 1, gradedOrder_kD, zero_le_one', vlistC_repD i 1⟩
    · exact ⟨isOnePI_repCB0, isSetC_repCB0, gradedOrder_kCB0, zero_le_one', b0⟩
    · exact ⟨isOnePI_repCB1, isSetC_repCB1, gradedOrder_kCB1, zero_le_one', b1⟩
  · simp only [repsC, repsCZ, repsCS, List.append_nil, List.mem_map, List.mem_finRange,
      true_and]
    rintro R ⟨i, rfl⟩
    exact ⟨isOnePI_repB i, isSetC_repB i 0, gradedOrder_kB 0, zero_le_one', vlistC_repB i⟩

/-- The signature of a representative: its kinds, raw vertex list and slot indices. -/
def sigC (R : RepC N) : (Fin N → Wick.VertexKind) × List (Fin N) × List ℕ :=
  (R.kinds, rawC R.rep, idxC R.rep)

/-- The signatures of the representatives with `N` vertices are pairwise distinct. -/
theorem nodup_sigC : ((repsC N).map sigC).Nodup := by
  by_cases e3 : N = 3
  · subst e3; decide +kernel
  by_cases e4 : N = 4
  · subst e4; decide +kernel
  by_cases e5 : N = 5
  · subst e5; decide +kernel
  by_cases e6 : N = 6
  · subst e6; decide +kernel
  by_cases e7 : N = 7
  · subst e7; decide +kernel
  rw [repsC, repsCZ_eq_nil e4 e5 e6 e7, repsCS_eq_nil e3 e4]
  exact List.nodup_nil

/-! ### Distinct orbits, no automorphism -/

/-- **The relabelled representatives are pairwise distinct**: if two relabellings of
representatives with `N` vertices are the same contraction, the representatives (as positions
in `repsC N`) and the permutations agree. -/
theorem relabelK_repC_inj {i j : Fin (repsC N).length} {π π' : Equiv.Perm (Fin N)}
    (hκ : ∀ t, κ (π t) = ((repsC N).get i).kinds t)
    (hκ' : ∀ t, κ (π' t) = ((repsC N).get j).kinds t)
    (h : relabelK π hκ ((repsC N).get i).rep = relabelK π' hκ' ((repsC N).get j).rep) :
    i = j ∧ π = π' := by
  set R := (repsC N).get i with hR
  set R' := (repsC N).get j with hR'
  have hv := (repsC_props R (List.get_mem _ _)).2.2.2.2
  have hv' := (repsC_props R' (List.get_mem _ _)).2.2.2.2
  have hππ : π = π' := by
    have e := congrArg vlistC h
    rw [vlistC_relabelK, vlistC_relabelK, hv, hv'] at e
    ext t
    rw [List.map_inj_left.mp e t (List.mem_finRange t)]
  subst hππ
  refine ⟨?_, rfl⟩
  have hsig : sigC R = sigC R' := by
    refine Prod.ext (funext fun t => (hκ t).symm.trans (hκ' t)) (Prod.ext ?_ ?_)
    · have e := congrArg rawC h
      rw [rawC_relabelK, rawC_relabelK] at e
      exact List.map_injective_iff.mpr π.injective e
    · have e := congrArg idxC h
      rwa [idxC_relabelK, idxC_relabelK] at e
  have hn := nodup_sigC (N := N)
  have hi : ((repsC N).map sigC).get (i.cast (List.length_map _).symm) = sigC R := by
    simp [hR]
  have hj : ((repsC N).map sigC).get (j.cast (List.length_map _).symm) = sigC R' := by
    simp [hR']
  have := (List.Nodup.get_inj_iff hn).mp (hi.trans (hsig.trans hj.symm))
  exact Fin.ext (by simpa using congrArg Fin.val this)

/-! ### The count -/

/-- **Each orbit has `N!` members.** For every function `G` of the graded contractions with `N`
vertices invariant under relabelling 1PI contractions across kind sequences (at the transported
grading), the sum over the kind sequences, their gradings of graded order `7` with levels in
`0, …, 7`, and their 1PI set (c) contractions of `fermionSign C * G C g` is `N!` times the signed
sum of `G` over the representatives with `N` vertices, at their gradings. The instances are
arbitrary (in particular the classical ones of (G₆)). -/
theorem sum_setC {instF : ∀ κ : Fin N → Wick.VertexKind, Fintype (Contraction 1 1 κ)}
    {instCF : ∀ κ : Fin N → Wick.VertexKind, Fintype (Graded.CtVertex κ)}
    {instCE : ∀ κ : Fin N → Wick.VertexKind, DecidableEq (Graded.CtVertex κ)}
    {instG : ∀ κ : Fin N → Wick.VertexKind,
      DecidablePred fun g : Graded.Grading κ => Graded.gradedOrder κ g = 7}
    {instC : ∀ (κ : Fin N → Wick.VertexKind) (g : Graded.Grading κ),
      DecidablePred fun C : Contraction 1 1 κ => IsOnePI C ∧ QED.ThreeLoop.IsSetC C g}
    (G : ∀ {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Graded.Grading κ → ℂ)
    (hG : ∀ {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
      (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 1 κ) (g : Graded.Grading κ), IsOnePI C →
        G (relabelK π hκ C) (gradMap π hκ g) = G C g) :
    ∑ κ : Fin N → Wick.VertexKind,
      ∑ g ∈ (Fintype.piFinset fun _ : Graded.CtVertex κ => Finset.range (7 + 1)).filter
          (fun g => Graded.gradedOrder κ g = 7),
        ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter
            (fun C => IsOnePI C ∧ QED.ThreeLoop.IsSetC C g),
          ((fermionSign C : ℤ) : ℂ) * G C g =
      (N.factorial : ℂ) * ∑ i : Fin (repsC N).length,
        ((fermionSign ((repsC N).get i).rep : ℤ) : ℂ) *
          G ((repsC N).get i).rep ((repsC N).get i).grad := by
  set R : Fin (repsC N).length → RepC N := fun i => (repsC N).get i with hRdef
  have hR : ∀ i, R i ∈ repsC N := fun i => List.get_mem _ _
  set gk : Fin (repsC N).length × Equiv.Perm (Fin N) → (Fin N → Wick.VertexKind) :=
    fun p => (R p.1).kinds ∘ p.2.symm with hgk
  set F : Fin (repsC N).length × Equiv.Perm (Fin N) → ℂ :=
    fun p => ((fermionSign (R p.1).rep : ℤ) : ℂ) * G (R p.1).rep (R p.1).grad with hF
  have hκ_of : ∀ {κ : Fin N → Wick.VertexKind} {p}, gk p = κ →
      ∀ t, κ (p.2 t) = (R p.1).kinds t :=
    fun {κ} {p} hp t => by rw [← hp]; simp [hgk]
  have inner : ∀ κ : Fin N → Wick.VertexKind,
      ∑ g ∈ (Fintype.piFinset fun _ : Graded.CtVertex κ => Finset.range (7 + 1)).filter
          (fun g => Graded.gradedOrder κ g = 7),
        ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter
            (fun C => IsOnePI C ∧ QED.ThreeLoop.IsSetC C g),
          ((fermionSign C : ℤ) : ℂ) * G C g =
        ∑ p ∈ (Finset.univ : Finset (Fin (repsC N).length × Equiv.Perm (Fin N))).filter
          (fun p => gk p = κ), F p := by
    intro κ
    rw [Finset.sum_sigma']
    symm
    refine Finset.sum_bij
      (fun p hp => (⟨gradMap p.2 (hκ_of (Finset.mem_filter.mp hp).2) (R p.1).grad,
        relabelK p.2 (hκ_of (Finset.mem_filter.mp hp).2) (R p.1).rep⟩ :
          (_ : Graded.Grading κ) × Contraction 1 1 κ)) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨h1, h2, h3, h4, -⟩ := repsC_props _ (hR p.1)
      refine Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr fun s => ?_, ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
      · have := h4 ((ctMap p.2 (hκ_of (Finset.mem_filter.mp hp).2)).symm s)
        exact Finset.mem_range.mpr (by simp only [gradMap]; omega)
      · rw [SetALink.gradedOrder_gradMap, h3]
      · exact (isOnePI_relabelK_iff _ _ _).mpr h1
      · exact isSetC_relabelK _ _ h2
    · intro p _ q _ hpq
      obtain ⟨h1, h2⟩ := relabelK_repC_inj _ _ (eq_of_heq (Sigma.mk.inj_iff.mp hpq).2)
      exact Prod.ext h1 h2
    · rintro ⟨g, C⟩ hgC
      obtain ⟨hg, hC⟩ := Finset.mem_sigma.mp hgC
      have hg7 := (Finset.mem_filter.mp hg).2
      obtain ⟨h1, hCC⟩ := (Finset.mem_filter.mp hC).2
      obtain ⟨R', hR', π, hκ, rfl, rfl⟩ := exists_rep_setC g hg7 h1 hCC
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hR'
      refine ⟨(i, π), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      funext s
      simp only [hgk, hRdef, Function.comp_apply]
      rw [← hκ, Equiv.apply_symm_apply]
    · intro p _
      obtain ⟨h1, -⟩ := repsC_props _ (hR p.1)
      simp only [hF, fermionSign_relabelK, hG _ _ _ _ h1]
  rw [Finset.sum_congr rfl fun κ _ => inner κ, Finset.sum_fiberwise Finset.univ gk F,
    Fintype.sum_prod_type]
  simp only [hF, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]
  rfl

end QED.ChainProof.SetCLink

end
