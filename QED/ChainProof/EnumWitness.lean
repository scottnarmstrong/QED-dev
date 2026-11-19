/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVPChain
public import QED.TwoLoop.RelabelCountertermLines

/-!
# The chain witness of (C₁): transport under relabelling, and the contraction it determines

Helper for obligation O3-4 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). The frozen predicate
(C₁) `QED.VPChain.IsVPChain n C` asserts the existence of a witness: the vertices `a, b, c` of the
open line, the external-photon field `sb`, and the photon fields `src i`, `dst i` of the chain.
This file packages the witness as a structure and proves two facts, for every `n`:

* `QED.ChainProof.Enum.ChainBody.relabelK`: the body of (C₁) is transported by a relabelling of the
  vertices across kind sequences (`QED.TwoLoop.Relabel.relabelK`), to any witness whose vertices
  are the images and whose photon fields have the same slot indices; in particular (C₁) is
  invariant under relabelling (`isVPChain_relabelK`).
* `QED.ChainProof.Enum.ChainBody.eq`: **the witness determines the contraction.** Two
  contractions of the same kind sequence satisfying the body with the same witness are equal.
  Every field of every vertex is fixed by a clause of the body, and the last clause lists all
  vertices.
-/

@[expose] public section

namespace QED.ChainProof.Enum

open QED.WickModel QED.TwoLoop.Relabel

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Fields -/

theorem fv_ext {t t' : Wick.FermionVertex κ} (h : t.1 = t'.1) : t = t' := Subtype.ext h

theorem ps_ext {s s' : Wick.PhotonSlot κ} (h1 : s.1 = s'.1) (h2 : s.2.val = s'.2.val) :
    s = s' := by
  rcases s with ⟨t, i⟩
  rcases s' with ⟨t', i'⟩
  simp only at h1
  subst h1
  exact Sigma.ext rfl (heq_of_eq (Fin.ext h2))

/-- A gauge vertex has a single photon field. -/
theorem ps_eq_of_gauge {s s' : Wick.PhotonSlot κ} (h : s.1 = s'.1) (hg : κ s.1 = .gauge) :
    s = s' := by
  refine ps_ext h ?_
  have h1 : s.2.val < (κ s.1).photonSlots := s.2.isLt
  have h2 : s'.2.val < (κ s'.1).photonSlots := s'.2.isLt
  have e1 : (κ s.1).photonSlots = 1 := by rw [hg]; rfl
  have e2 : (κ s'.1).photonSlots = 1 := by rw [← h, hg]; rfl
  omega

theorem ps_val_eq_zero_of_gauge (s : Wick.PhotonSlot κ) (hg : κ s.1 = .gauge) : s.2.val = 0 := by
  have h1 : s.2.val < (κ s.1).photonSlots := s.2.isLt
  have e1 : (κ s.1).photonSlots = 1 := by rw [hg]; rfl
  omega

theorem ps_val_lt_two_of_photonCt (s : Wick.PhotonSlot κ) (hg : κ s.1 = .photonCt) :
    s.2.val < 2 := by
  have h1 : s.2.val < (κ s.1).photonSlots := s.2.isLt
  have e1 : (κ s.1).photonSlots = 2 := by rw [hg]; rfl
  omega

/-- A `photonCt` vertex has exactly two photon fields. -/
theorem ps_eq_or_of_photonCt {x y s : Wick.PhotonSlot κ} (hx : x.1 = s.1) (hy : y.1 = s.1)
    (hxy : x ≠ y) (hc : κ s.1 = .photonCt) : s = x ∨ s = y := by
  have hs := ps_val_lt_two_of_photonCt s hc
  have hxv := ps_val_lt_two_of_photonCt x (hx ▸ hc)
  have hyv := ps_val_lt_two_of_photonCt y (hy ▸ hc)
  have hne : x.2.val ≠ y.2.val := fun h => hxy (ps_ext (hx.trans hy.symm) h)
  rcases (by omega : s.2.val = x.2.val ∨ s.2.val = y.2.val) with h | h
  · exact Or.inl (ps_ext hx.symm h)
  · exact Or.inr (ps_ext hy.symm h)

theorem tau_symm (C : Contraction 1 1 κ) {x y : Fin 1 ⊕ Wick.PhotonSlot κ}
    (h : C.1.2 x = y) : C.1.2 y = x := by
  rw [← h]
  exact (C.2 x).1

/-! ### The witness -/

/-- The data of the chain predicate (C₁): the open line `a, b, c`, the external-photon field
`sb`, and the photon fields `src i`, `dst i` of the chain. -/
structure ChainWitness (n : ℕ) (κ : Fin N → Wick.VertexKind) where
  /-- the vertex contracted with the external `Ψ(x)` -/
  a : Wick.FermionVertex κ
  /-- the middle vertex of the open line -/
  b : Wick.FermionVertex κ
  /-- the vertex contracted with the external `Ψ̄(y)` -/
  c : Wick.FermionVertex κ
  /-- the photon field of `b` contracted with the external photon -/
  sb : Wick.PhotonSlot κ
  /-- the field where photon line `i` starts -/
  src : Fin (n + 1) → Wick.PhotonSlot κ
  /-- the field where photon line `i` ends -/
  dst : Fin (n + 1) → Wick.PhotonSlot κ

/-- The insertion clause of (C₁) for insertion `i`, with its witness fields. -/
def InsClause (C : Contraction 1 1 κ) (d s : Wick.PhotonSlot κ) : Prop :=
  (κ d.1 = .gauge ∧ κ s.1 = .gauge ∧ d.1 ≠ s.1 ∧
    ∃ u w : Wick.FermionVertex κ, u.1 = d.1 ∧ w.1 = s.1 ∧
      C.1.1 (.inr u) = .inr w ∧ C.1.1 (.inr w) = .inr u) ∨
  (κ d.1 = .photonCt ∧ s.1 = d.1 ∧ s ≠ d)

/-- The body of (C₁) for a witness, with named clauses. -/
structure ChainBody (n : ℕ) (C : Contraction 1 1 κ) (W : ChainWitness n κ) : Prop where
  ka : κ W.a.1 = .gauge
  kb : κ W.b.1 = .gauge
  kc : κ W.c.1 = .gauge
  s0a : C.1.1 (.inl 0) = .inr W.a
  sab : C.1.1 (.inr W.a) = .inr W.b
  sbc : C.1.1 (.inr W.b) = .inr W.c
  sc0 : C.1.1 (.inr W.c) = .inl 0
  sbv : W.sb.1 = W.b.1
  tsb : C.1.2 (.inl 0) = .inr W.sb
  src0 : (W.src 0).1 = W.a.1
  dstn : (W.dst (Fin.last n)).1 = W.c.1
  line : ∀ i, C.1.2 (.inr (W.src i)) = .inr (W.dst i)
  ins : ∀ i : Fin n, InsClause C (W.dst i.castSucc) (W.src i.succ)
  exh : ∀ t : Fin N, t = W.a.1 ∨ t = W.b.1 ∨ t = W.c.1 ∨
    ∃ i : Fin n, t = (W.dst i.castSucc).1 ∨ t = (W.src i.succ).1

theorem isVPChain_iff (n : ℕ) (C : Contraction 1 1 κ) :
    QED.VPChain.IsVPChain n C ↔ ∃ W : ChainWitness n κ, ChainBody n C W := by
  constructor
  · rintro ⟨a, b, c, sb, src, dst, ka, kb, kc, s0a, sab, sbc, sc0, sbv, tsb, src0, dstn, line,
      ins, exh⟩
    exact ⟨⟨a, b, c, sb, src, dst⟩,
      ⟨ka, kb, kc, s0a, sab, sbc, sc0, sbv, tsb, src0, dstn, line, ins, exh⟩⟩
  · rintro ⟨⟨a, b, c, sb, src, dst⟩, ⟨ka, kb, kc, s0a, sab, sbc, sc0, sbv, tsb, src0, dstn, line,
      ins, exh⟩⟩
    exact ⟨a, b, c, sb, src, dst, ka, kb, kc, s0a, sab, sbc, sc0, sbv, tsb, src0, dstn, line,
      ins, exh⟩

/-! ### Transport under relabelling -/

section Relabel

variable {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t)

/-- The image of a witness under the relabelling. -/
def ChainWitness.map {n : ℕ} (W : ChainWitness n κ) : ChainWitness n κ' where
  a := fvMap π hκ W.a
  b := fvMap π hκ W.b
  c := fvMap π hκ W.c
  sb := psMap π hκ W.sb
  src i := psMap π hκ (W.src i)
  dst i := psMap π hκ (W.dst i)

theorem relabelK_fst_inr' (C : Contraction 1 1 κ) (t : Wick.FermionVertex κ) :
    (relabelK π hκ C).1.1 (.inr (fvMap π hκ t)) = extFK π hκ (C.1.1 (.inr t)) := by
  have := relabelK_fst_apply π hκ C (.inr t)
  simpa only [extFK_inr] using this

theorem relabelK_snd_inr' (C : Contraction 1 1 κ) (s : Wick.PhotonSlot κ) :
    (relabelK π hκ C).1.2 (.inr (psMap π hκ s)) = extPK π hκ (C.1.2 (.inr s)) := by
  have := relabelK_snd_apply π hκ C (.inr s)
  simpa only [extPK_inr] using this

/-- **The body of (C₁) is transported by relabelling**, to the image witness. -/
theorem ChainBody.relabelK_map {n : ℕ} {C : Contraction 1 1 κ} {W : ChainWitness n κ}
    (h : ChainBody n C W) : ChainBody n (relabelK π hκ C) (W.map π hκ) where
  ka := by simp only [ChainWitness.map, fvMap_val, hκ, h.ka]
  kb := by simp only [ChainWitness.map, fvMap_val, hκ, h.kb]
  kc := by simp only [ChainWitness.map, fvMap_val, hκ, h.kc]
  s0a := by simp only [ChainWitness.map, relabelK_fst_inl, h.s0a, extFK_inr]
  sab := by simp only [ChainWitness.map, relabelK_fst_inr', h.sab, extFK_inr]
  sbc := by simp only [ChainWitness.map, relabelK_fst_inr', h.sbc, extFK_inr]
  sc0 := by simp only [ChainWitness.map, relabelK_fst_inr', h.sc0, extFK_inl]
  sbv := by simp only [ChainWitness.map, psMap_fst, fvMap_val, h.sbv]
  tsb := by simp only [ChainWitness.map, relabelK_snd_inl, h.tsb, extPK_inr]
  src0 := by simp only [ChainWitness.map, psMap_fst, fvMap_val, h.src0]
  dstn := by simp only [ChainWitness.map, psMap_fst, fvMap_val, h.dstn]
  line i := by simp only [ChainWitness.map, relabelK_snd_inr', h.line, extPK_inr]
  ins i := by
    rcases h.ins i with ⟨k1, k2, hne, u, w, hu, hw, huw, hwu⟩ | ⟨k1, hs, hne⟩
    · refine Or.inl ⟨?_, ?_, ?_, fvMap π hκ u, fvMap π hκ w, ?_, ?_, ?_, ?_⟩
      · simp only [ChainWitness.map, psMap_fst, hκ, k1]
      · simp only [ChainWitness.map, psMap_fst, hκ, k2]
      · simp only [ChainWitness.map, psMap_fst, ne_eq, π.injective.eq_iff, hne,
          not_false_eq_true]
      · simp only [ChainWitness.map, psMap_fst, fvMap_val, hu]
      · simp only [ChainWitness.map, psMap_fst, fvMap_val, hw]
      · simp only [relabelK_fst_inr', huw, extFK_inr]
      · simp only [relabelK_fst_inr', hwu, extFK_inr]
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · simp only [ChainWitness.map, psMap_fst, hκ, k1]
      · simp only [ChainWitness.map, psMap_fst, hs]
      · simp only [ChainWitness.map, ne_eq, (psMap π hκ).injective.eq_iff, hne,
          not_false_eq_true]
  exh t := by
    obtain ⟨t, rfl⟩ := π.surjective t
    simp only [ChainWitness.map, fvMap_val, psMap_fst, π.injective.eq_iff]
    exact h.exh t

theorem fvMap_eq_of {t : Wick.FermionVertex κ} {t' : Wick.FermionVertex κ'} (h : π t.1 = t'.1) :
    fvMap π hκ t = t' := fv_ext h

theorem psMap_eq_of {s : Wick.PhotonSlot κ} {s' : Wick.PhotonSlot κ'} (h1 : π s.1 = s'.1)
    (h2 : s.2.val = s'.2.val) : psMap π hκ s = s' := ps_ext h1 h2

/-- **The body of (C₁) is transported by relabelling** to any witness whose vertices are the
images and whose photon fields have the same slot indices. -/
theorem ChainBody.relabelK {n : ℕ} {C : Contraction 1 1 κ} {W : ChainWitness n κ}
    (h : ChainBody n C W) (W' : ChainWitness n κ') (ha : π W.a.1 = W'.a.1)
    (hb : π W.b.1 = W'.b.1) (hc : π W.c.1 = W'.c.1) (hsb1 : π W.sb.1 = W'.sb.1)
    (hsb2 : W.sb.2.val = W'.sb.2.val) (hs1 : ∀ i, π (W.src i).1 = (W'.src i).1)
    (hs2 : ∀ i, (W.src i).2.val = (W'.src i).2.val) (hd1 : ∀ i, π (W.dst i).1 = (W'.dst i).1)
    (hd2 : ∀ i, (W.dst i).2.val = (W'.dst i).2.val) : ChainBody n (relabelK π hκ C) W' := by
  have hW : W.map π hκ = W' := by
    rcases W' with ⟨a', b', c', sb', src', dst'⟩
    simp only [ChainWitness.map, ChainWitness.mk.injEq]
    exact ⟨fvMap_eq_of π hκ ha, fvMap_eq_of π hκ hb, fvMap_eq_of π hκ hc,
      psMap_eq_of π hκ hsb1 hsb2, funext fun i => psMap_eq_of π hκ (hs1 i) (hs2 i),
      funext fun i => psMap_eq_of π hκ (hd1 i) (hd2 i)⟩
  exact hW ▸ h.relabelK_map π hκ

/-- (C₁) is invariant under relabelling the vertices across kind sequences. -/
theorem isVPChain_relabelK {n : ℕ} {C : Contraction 1 1 κ} (h : QED.VPChain.IsVPChain n C) :
    QED.VPChain.IsVPChain n (relabelK π hκ C) := by
  obtain ⟨W, hW⟩ := (isVPChain_iff n C).mp h
  exact (isVPChain_iff n _).mpr ⟨_, hW.relabelK_map π hκ⟩

end Relabel

/-! ### The witness determines the contraction -/

/-- **The witness determines the contraction**: two contractions of the same kind sequence that
satisfy the body of (C₁) with the same witness are equal. -/
theorem ChainBody.eq {n : ℕ} {C C' : Contraction 1 1 κ} {W : ChainWitness n κ}
    (h : ChainBody n C W) (h' : ChainBody n C' W) : C = C' := by
  have hσ : C.1.1 = C'.1.1 := by
    ext x
    rcases x with j | t
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [h.s0a, h'.s0a]
    · rcases h.exh t.1 with ht | ht | ht | ⟨i, ht | ht⟩
      · obtain rfl : t = W.a := fv_ext ht
        rw [h.sab, h'.sab]
      · obtain rfl : t = W.b := fv_ext ht
        rw [h.sbc, h'.sbc]
      · obtain rfl : t = W.c := fv_ext ht
        rw [h.sc0, h'.sc0]
      · rcases h.ins i with ⟨-, -, -, u, w, hu, hw, huw, -⟩ | ⟨hk, -, -⟩
        · rcases h'.ins i with ⟨-, -, -, u', w', hu', hw', huw', -⟩ | ⟨hk', -, -⟩
          · obtain rfl : t = u := fv_ext (ht.trans hu.symm)
            obtain rfl : u' = t := fv_ext (hu'.trans ht.symm)
            rw [huw, huw', fv_ext (hw.trans hw'.symm)]
          · exact absurd (ht ▸ hk') t.2
        · exact absurd (ht ▸ hk) t.2
      · rcases h.ins i with ⟨-, -, -, u, w, hu, hw, -, hwu⟩ | ⟨hk, hs, -⟩
        · rcases h'.ins i with ⟨-, -, -, u', w', hu', hw', -, hwu'⟩ | ⟨hk', hs', -⟩
          · obtain rfl : t = w := fv_ext (ht.trans hw.symm)
            obtain rfl : w' = t := fv_ext (hw'.trans ht.symm)
            rw [hwu, hwu', fv_ext (hu.trans hu'.symm)]
          · exact absurd ((ht.trans hs') ▸ hk') t.2
        · exact absurd ((ht.trans hs) ▸ hk) t.2
  have hτ : C.1.2 = C'.1.2 := by
    ext x
    rcases x with j | s
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [h.tsb, h'.tsb]
    · rcases h.exh s.1 with hs | hs | hs | ⟨i, hs | hs⟩
      · obtain rfl : s = W.src 0 := ps_eq_of_gauge (hs.trans h.src0.symm) (hs ▸ h.ka)
        rw [h.line, h'.line]
      · obtain rfl : s = W.sb := ps_eq_of_gauge (hs.trans h.sbv.symm) (hs ▸ h.kb)
        rw [tau_symm C h.tsb, tau_symm C' h'.tsb]
      · obtain rfl : s = W.dst (Fin.last n) := ps_eq_of_gauge (hs.trans h.dstn.symm) (hs ▸ h.kc)
        rw [tau_symm C (h.line _), tau_symm C' (h'.line _)]
      · rcases h.ins i with ⟨k1, -, -, -⟩ | ⟨k1, hsd, hne⟩
        · obtain rfl : s = W.dst i.castSucc := ps_eq_of_gauge hs (hs ▸ k1)
          rw [tau_symm C (h.line _), tau_symm C' (h'.line _)]
        · rcases ps_eq_or_of_photonCt hs.symm (hsd.trans hs.symm) hne.symm (hs ▸ k1) with
            rfl | rfl
          · rw [tau_symm C (h.line _), tau_symm C' (h'.line _)]
          · rw [h.line, h'.line]
      · rcases h.ins i with ⟨-, k2, -, -⟩ | ⟨k1, hsd, hne⟩
        · obtain rfl : s = W.src i.succ := ps_eq_of_gauge hs (hs ▸ k2)
          rw [h.line, h'.line]
        · rcases ps_eq_or_of_photonCt (hs.trans hsd).symm hs.symm hne.symm
            ((hs.trans hsd) ▸ k1) with rfl | rfl
          · rw [tau_symm C (h.line _), tau_symm C' (h'.line _)]
          · rw [h.line, h'.line]
  exact Subtype.ext (Prod.ext hσ hτ)

end QED.ChainProof.Enum

end
