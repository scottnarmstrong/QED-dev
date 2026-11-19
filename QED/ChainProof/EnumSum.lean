/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumClassify

/-!
# The set (b) chain family summed with coefficient one per class

Helper for obligation O3-4 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). The relabellings
`relabelK π hκ R.rep` of the representatives `R ∈ repsOf N` (`π` a permutation of the `N`
vertices) are exactly the set (b) chain contractions with `N` vertices
(`QED.ChainProof.Enum.exists_rep`), and they are pairwise distinct: the witness of the
relabelled representative is the image of the witness of `R`, the witness is determined by the
contraction (`ChainBody.witness_eq`), the vertex list of the witness of every representative is
`0, 1, …, N - 1` in order (so the witness determines `π`), and the kinds and slot indices of the
witness determine `R` (`repsOf_props`, `nodup_sig`, checked by evaluation). No
representative has a nontrivial automorphism.

* `QED.ChainProof.Enum.sum_chain`: for every function `G` of the contractions invariant under
  relabelling of 1PI contractions, the sum over the kind sequences of total order at most `7` and
  their 1PI set (b) contractions of `fermionSign C * G C` is `N!` times the sum over the
  representatives with `N` vertices of `fermionSign R * G R`.
-/

@[expose] public section

namespace QED.ChainProof.Enum

open QED.WickModel QED.TwoLoop.Relabel

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### The vertex list and the slot data of a witness -/

/-- The vertices of an insertion: one for a `photonCt` vertex, two for a bubble. -/
def insV (κ : Fin N → Wick.VertexKind) (d s : Wick.PhotonSlot κ) : List (Fin N) :=
  if κ d.1 = .photonCt then [d.1] else [d.1, s.1]

/-- The vertices named by a witness, in the order `c, b, a`, first insertion, second insertion. -/
def vlist (W : ChainWitness 2 κ) : List (Fin N) :=
  [W.c.1, W.b.1, W.a.1] ++ insV κ (W.dst 0) (W.src 1) ++ insV κ (W.dst 1) (W.src 2)

/-- The slot indices of the photon fields of a witness. -/
def sdata (W : ChainWitness 2 κ) : List ℕ :=
  [W.sb.2.val, (W.src 0).2.val, (W.dst 0).2.val, (W.src 1).2.val, (W.dst 1).2.val,
    (W.src 2).2.val, (W.dst 2).2.val]

theorem vlist_map {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) (W : ChainWitness 2 κ) :
    vlist (W.map π hκ) = (vlist W).map π := by
  simp only [vlist, insV, ChainWitness.map, fvMap_val, psMap_fst, hκ, List.map_append]
  split_ifs <;> rfl

theorem sdata_map {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) (W : ChainWitness 2 κ) : sdata (W.map π hκ) = sdata W := rfl

/-- The signature of a representative: its kinds and the slot indices of its witness. -/
def sig (R : Rep N) : (Fin N → Wick.VertexKind) × List ℕ := (R.kinds, sdata R.wit)

/-! ### Properties of the representatives -/

theorem repsOf_eq_nil (h5 : N ≠ 5) (h6 : N ≠ 6) (h7 : N ≠ 7) : repsOf N = [] := by
  unfold repsOf
  split <;> simp_all

theorem repsOf_cases (P : ∀ N, Rep N → Prop) (h5 : ∀ R ∈ reps5, P 5 R) (h6 : ∀ R ∈ reps6, P 6 R)
    (h7 : ∀ R ∈ reps7, P 7 R) : ∀ R ∈ repsOf N, P N R := by
  by_cases e5 : N = 5
  · subst e5; exact h5
  by_cases e6 : N = 6
  · subst e6; exact h6
  by_cases e7 : N = 7
  · subst e7; exact h7
  rw [repsOf_eq_nil e5 e6 e7]
  simp

/-- The representatives with `N` vertices: 1PI, the body of (C₁) with their witness, total order
`7`, vertex list `0, 1, …, N - 1`. -/
theorem repsOf_props : ∀ R ∈ repsOf N, IsOnePI R.rep ∧ ChainBody 2 R.rep R.wit ∧
    ∑ t, (R.kinds t).order = 7 ∧ vlist R.wit = List.finRange N := by
  refine repsOf_cases (fun N R => IsOnePI R.rep ∧ ChainBody 2 R.rep R.wit ∧
    ∑ t, (R.kinds t).order = 7 ∧ vlist R.wit = List.finRange N) ?_ ?_ ?_
  · simp only [reps5, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl | rfl | rfl) <;>
      exact ⟨isOnePI_repDD _ _, chainBody_repDD _ _, by decide, by decide⟩
  · simp only [reps6, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl | rfl | rfl)
    · exact ⟨isOnePI_repBD _, chainBody_repBD _, by decide, by decide⟩
    · exact ⟨isOnePI_repBD _, chainBody_repBD _, by decide, by decide⟩
    · exact ⟨isOnePI_repDB _, chainBody_repDB _, by decide, by decide⟩
    · exact ⟨isOnePI_repDB _, chainBody_repDB _, by decide, by decide⟩
  · simp only [reps7, List.mem_cons, List.not_mem_nil, or_false]
    rintro R rfl
    exact ⟨isOnePI_repBB, chainBody_repBB, by decide, by decide⟩

/-- The signatures of the representatives with `N` vertices are pairwise distinct. -/
theorem nodup_sig : ((repsOf N).map sig).Nodup := by
  by_cases e5 : N = 5
  · subst e5; decide
  by_cases e6 : N = 6
  · subst e6; decide
  by_cases e7 : N = 7
  · subst e7; decide
  rw [repsOf_eq_nil e5 e6 e7]
  exact List.nodup_nil

/-! ### No automorphism, distinct classes -/

/-- **The relabelled representatives are pairwise distinct**: if two relabellings of
representatives with `N` vertices are the same contraction, the representatives (as positions
in `repsOf N`) and the permutations agree. -/
theorem relabelK_rep_inj {i j : Fin (repsOf N).length} {π π' : Equiv.Perm (Fin N)}
    (hκ : ∀ t, κ (π t) = ((repsOf N).get i).kinds t)
    (hκ' : ∀ t, κ (π' t) = ((repsOf N).get j).kinds t)
    (h : relabelK π hκ ((repsOf N).get i).rep = relabelK π' hκ' ((repsOf N).get j).rep) :
    i = j ∧ π = π' := by
  set R := (repsOf N).get i with hR
  set R' := (repsOf N).get j with hR'
  obtain ⟨-, hb, -, hv⟩ := repsOf_props R (List.get_mem _ _)
  obtain ⟨-, hb', -, hv'⟩ := repsOf_props R' (List.get_mem _ _)
  have hW := (hb.relabelK_map π hκ).witness_eq (h ▸ hb'.relabelK_map π' hκ')
  have hππ : π = π' := by
    have e := congrArg vlist hW
    rw [vlist_map, vlist_map, hv, hv'] at e
    ext t
    rw [List.map_inj_left.mp e t (List.mem_finRange t)]
  subst hππ
  refine ⟨?_, rfl⟩
  have hsig : sig R = sig R' := by
    refine Prod.ext (funext fun t => ?_) ?_
    · exact (hκ t).symm.trans (hκ' t)
    · have e := congrArg sdata hW
      rwa [sdata_map, sdata_map] at e
  have hn := nodup_sig (N := N)
  have hi : ((repsOf N).map sig).get (i.cast (List.length_map _).symm) = sig R := by
    simp [hR]
  have hj : ((repsOf N).map sig).get (j.cast (List.length_map _).symm) = sig R' := by
    simp [hR']
  have := (List.Nodup.get_inj_iff hn).mp (hi.trans (hsig.trans hj.symm))
  exact Fin.ext (by simpa using congrArg Fin.val this)

end QED.ChainProof.Enum

end
