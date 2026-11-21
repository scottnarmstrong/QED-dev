/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkClassLoop

/-!
# The set (a) family summed with coefficient one per class

Helper for the Phase 5 Stage 3a enumeration (decision D-58). The relabellings
`relabelK π hκ R.rep` of the representatives `R ∈ repsA N`, at the transported gradings, are
exactly the graded contractions of `N` vertices of graded order `7` satisfying (A₁)
`QED.ThreeLoop.IsSetA` (`QED.ChainProof.SetALink.exists_rep_setA`), and they are pairwise
distinct (`relabelK_repA_inj`): no class has a nontrivial automorphism and distinct
representatives give distinct classes.

Distinctness uses an intrinsic vertex list `vlistA C`, read off the contraction by following the
fermion pairing from the external field and the photon pairing from the open line (the open line
`c, b, a`, the insertion ends `u`, `w`, and the walk around the loop from `u`, each vertex at its
first occurrence). It is carried along by relabelling (`vlistA_relabelK`), and it is
`0, 1, …, N - 1` for every representative, so it determines the permutation. The raw list (with
repetitions), the slot index of the field `x`, and the kinds then separate the representatives.

## Main statements

* `QED.ChainProof.SetALink.isSetA_relabelK`: (A₁) is invariant under relabelling.
* `QED.ChainProof.SetALink.relabelK_repA_inj`: the relabelled representatives are pairwise
  distinct.
* `QED.ChainProof.SetALink.sum_setA`: for every `G` invariant under relabelling 1PI graded
  contractions, the sum over the kind sequences of `N` vertices, their gradings of graded order
  `7` (levels in `0, …, 7`) and their 1PI set (a) contractions of `fermionSign C * G C g` is `N!`
  times the signed sum of `G` over the representatives with `N` vertices.
-/

@[expose] public section

namespace QED.ChainProof.SetALink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum QED.GradedProof.VP2

variable {N : ℕ} {κ κ' : Fin N → Wick.VertexKind}

/-! ### Invariance of (A₁) -/

section Relabel

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t)

theorem sameCycle_relabelK (C : Contraction 1 1 κ) (x y : Fin 1 ⊕ Wick.FermionVertex κ) :
    (relabelK π hκ C).1.1.SameCycle (extFK π hκ x) (extFK π hκ y) ↔ C.1.1.SameCycle x y := by
  have key : ∀ i : ℤ, ((relabelK π hκ C).1.1 ^ i) (extFK π hκ x) =
      extFK π hκ ((C.1.1 ^ i) x) := by
    intro i
    have e : (relabelK π hκ C).1.1 = (extFK π hκ).permCongrHom C.1.1 := rfl
    rw [e, ← map_zpow, Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (extFK π hκ).injective (by rw [← key, hi])⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [key, hi]⟩

/-- **(A₁) is invariant under relabelling.** -/
theorem isSetA_relabelK {C : Contraction 1 1 κ} (hC : QED.ThreeLoop.IsSetA C) :
    QED.ThreeLoop.IsSetA (relabelK π hκ C) := by
  obtain ⟨a, b, c, sa, sb, sc, x, y, ka, kb, kc, s0a, sab, sbc, sc0, hsb, tsb, hsa, hsc, hx, hy,
    hins⟩ := hC
  refine ⟨fvMap π hκ a, fvMap π hκ b, fvMap π hκ c, psMap π hκ sa, psMap π hκ sb,
    psMap π hκ sc, psMap π hκ x, psMap π hκ y, by rw [fvMap_val, hκ, ka],
    by rw [fvMap_val, hκ, kb], by rw [fvMap_val, hκ, kc],
    by simpa [s0a] using relabelK_fst_apply π hκ C (.inl 0),
    by rw [relabelK_fst_inr', sab, extFK_inr], by rw [relabelK_fst_inr', sbc, extFK_inr],
    by rw [relabelK_fst_inr', sc0, extFK_inl], by simp [hsb],
    by simpa [tsb] using relabelK_snd_apply π hκ C (.inl 0), by simp [hsa], by simp [hsc],
    by rw [relabelK_snd_inr', hx, extPK_inr], by rw [relabelK_snd_inr', hy, extPK_inr], ?_⟩
  rcases hins with ⟨kx, hyx, hne, hexh⟩ | ⟨u, w, hu, hw, hsep, huw, hexh⟩
  · refine Or.inl ⟨by rw [psMap_fst, hκ, kx], by simp [hyx], (psMap π hκ).injective.ne hne,
      fun t => ?_⟩
    obtain ⟨t, rfl⟩ := π.surjective t
    simp only [fvMap_val, psMap_fst, π.injective.eq_iff]
    exact hexh t
  · refine Or.inr ⟨fvMap π hκ u, fvMap π hκ w, by simp [hu], by simp [hw],
      fun i h => hsep i ((sameCycle_relabelK π hκ C (.inl i) (.inr u)).1 h),
      (sameCycle_relabelK π hκ C (.inr u) (.inr w)).2 huw, fun t => ?_⟩
    obtain ⟨t, rfl⟩ := π.surjective t
    simp only [fvMap_val, π.injective.eq_iff]
    rcases hexh t with h | h | h | ⟨v, hv, hcv⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨fvMap π hκ v, by simp [hv],
        (sameCycle_relabelK π hκ C (.inr u) (.inr v)).2 hcv⟩))

/-- Relabelling preserves the graded order. -/
theorem gradedOrder_gradMap (g : Graded.Grading κ) :
    Graded.gradedOrder κ' (gradMap π hκ g) = Graded.gradedOrder κ g := by
  rw [gradedOrder_eq, gradedOrder_eq]
  congr 1
  · rw [← Equiv.sum_comp π (fun t => (κ' t).order)]
    simp only [hκ]
  · exact Equiv.sum_comp (ctMap π hκ).symm (fun t => 2 * g t)

end Relabel

/-! ### The intrinsic vertex list -/

/-- The vertex of a fermion field (none for the external field). -/
def fvt : Fin 1 ⊕ Wick.FermionVertex κ → List (Fin N) :=
  Sum.elim (fun _ => []) (fun v => [v.1])

/-- The vertex following `t` on the fermion pairing. -/
def fstep (C : Contraction 1 1 κ) (t : Fin N) : List (Fin N) :=
  if h : κ t = .photonCt then [] else fvt (C.1.1 (.inr ⟨t, h⟩))

/-- The vertex of the photon partner of the field `0` of `t`. -/
def pstep (C : Contraction 1 1 κ) (t : Fin N) : List (Fin N) :=
  if h : 0 < (κ t).photonSlots then
    Sum.elim (fun _ => []) (fun s => [s.1]) (C.1.2 (.inr ⟨t, ⟨0, h⟩⟩))
  else []

/-- The slot index of the photon partner of the field `0` of `t`. -/
def pidx (C : Contraction 1 1 κ) (t : Fin N) : List ℕ :=
  if h : 0 < (κ t).photonSlots then
    Sum.elim (fun _ => []) (fun s => [s.2.val]) (C.1.2 (.inr ⟨t, ⟨0, h⟩⟩))
  else []

/-- The raw vertex list: `c, b, a`, the insertion ends `u` (partner of `a`) and `w` (partner of
`c`), and three steps of the fermion pairing from `u`. -/
def rawA (C : Contraction 1 1 κ) : List (Fin N) :=
  let a := fvt (C.1.1 (.inl 0))
  let b := a.flatMap (fstep C)
  let c := b.flatMap (fstep C)
  let u := a.flatMap (pstep C)
  let w := c.flatMap (pstep C)
  let u₁ := u.flatMap (fstep C)
  let u₂ := u₁.flatMap (fstep C)
  let u₃ := u₂.flatMap (fstep C)
  c ++ b ++ a ++ u ++ w ++ u₁ ++ u₂ ++ u₃

/-- The vertex list: the raw list, each vertex at its first occurrence. -/
def vlistA (C : Contraction 1 1 κ) : List (Fin N) := (rawA C).reverse.dedup.reverse

/-- The slot index of the field `x` (the partner of `a`). -/
def slotIdxA (C : Contraction 1 1 κ) : List ℕ := (fvt (C.1.1 (.inl 0))).flatMap (pidx C)

section Equivariance

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 1 κ)

theorem fvt_extFK (z : Fin 1 ⊕ Wick.FermionVertex κ) :
    fvt (extFK π hκ z) = (fvt z).map π := by
  cases z <;> rfl

theorem fstep_relabelK (t : Fin N) :
    fstep (relabelK π hκ C) (π t) = (fstep C t).map π := by
  unfold fstep
  by_cases h : κ t = .photonCt
  · rw [dite_eq_left h, dite_eq_left ((hκ t).trans h)]
    rfl
  · rw [dite_eq_right h, dite_eq_right (by rw [hκ]; exact h)]
    have e := relabelK_fst_inr' π hκ C ⟨t, h⟩
    rw [← fvt_extFK π hκ, ← e]
    rfl

theorem pstep_relabelK (t : Fin N) :
    pstep (relabelK π hκ C) (π t) = (pstep C t).map π := by
  unfold pstep
  by_cases h : 0 < (κ t).photonSlots
  · have h' : 0 < (κ' (π t)).photonSlots := by rw [hκ]; exact h
    rw [dite_eq_left h, dite_eq_left h']
    have e := relabelK_snd_inr' π hκ C ⟨t, ⟨0, h⟩⟩
    have hs : psMap π hκ ⟨t, ⟨0, h⟩⟩ = ⟨π t, ⟨0, h'⟩⟩ := ps_ext rfl rfl
    rw [hs] at e
    rw [e]
    rcases C.1.2 (.inr ⟨t, ⟨0, h⟩⟩) with j | s <;> rfl
  · rw [dite_eq_right h, dite_eq_right (by rw [hκ]; exact h)]
    rfl

theorem pidx_relabelK (t : Fin N) : pidx (relabelK π hκ C) (π t) = pidx C t := by
  unfold pidx
  by_cases h : 0 < (κ t).photonSlots
  · have h' : 0 < (κ' (π t)).photonSlots := by rw [hκ]; exact h
    rw [dite_eq_left h, dite_eq_left h']
    have e := relabelK_snd_inr' π hκ C ⟨t, ⟨0, h⟩⟩
    have hs : psMap π hκ ⟨t, ⟨0, h⟩⟩ = ⟨π t, ⟨0, h'⟩⟩ := ps_ext rfl rfl
    rw [hs] at e
    rw [e]
    rcases C.1.2 (.inr ⟨t, ⟨0, h⟩⟩) with j | s <;> rfl
  · rw [dite_eq_right h, dite_eq_right (by rw [hκ]; exact h)]

theorem flatMap_map_of {α : Type*} {f : Fin N → List α} {f' : Fin N → List α}
    (h : ∀ t, f' (π t) = f t) (l : List (Fin N)) : (l.map π).flatMap f' = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [List.map_cons, List.flatMap_cons, h, ih]

theorem flatMap_map_map {f f' : Fin N → List (Fin N)} (h : ∀ t, f' (π t) = (f t).map π)
    (l : List (Fin N)) : (l.map π).flatMap f' = (l.flatMap f).map π := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [List.map_cons, List.flatMap_cons, h, ih, List.map_append]

theorem fvt_relabelK_inl :
    fvt ((relabelK π hκ C).1.1 (.inl 0)) = (fvt (C.1.1 (.inl 0))).map π := by
  rw [← fvt_extFK π hκ, ← relabelK_fst_apply π hκ C (.inl 0)]
  rfl

theorem rawA_relabelK : rawA (relabelK π hκ C) = (rawA C).map π := by
  have hf := flatMap_map_map π (fstep_relabelK π hκ C)
  have hp := flatMap_map_map π (pstep_relabelK π hκ C)
  simp only [rawA, fvt_relabelK_inl, hf, hp, List.map_append]

theorem vlistA_relabelK : vlistA (relabelK π hκ C) = (vlistA C).map π := by
  rw [vlistA, vlistA, rawA_relabelK, ← List.map_reverse, List.dedup_map_of_injective π.injective,
    List.map_reverse]

theorem slotA_relabelK : slotIdxA (relabelK π hκ C) = slotIdxA C := by
  rw [slotIdxA, slotIdxA, fvt_relabelK_inl, flatMap_map_of π (pidx_relabelK π hκ C)]

end Equivariance

/-! ### Properties of the representatives -/

theorem repsA_eq_nil (h4 : N ≠ 4) (h5 : N ≠ 5) (h6 : N ≠ 6) (h7 : N ≠ 7) : repsA N = [] := by
  unfold repsA
  split <;> simp_all

theorem repsA_cases (P : ∀ N, RepA N → Prop) (h4 : ∀ R ∈ repsA4, P 4 R)
    (h5 : ∀ R ∈ repsA5, P 5 R) (h6 : ∀ R ∈ repsA6, P 6 R) (h7 : ∀ R ∈ repsA7, P 7 R) :
    ∀ R ∈ repsA N, P N R := by
  by_cases e4 : N = 4
  · subst e4; exact h4
  by_cases e5 : N = 5
  · subst e5; exact h5
  by_cases e6 : N = 6
  · subst e6; exact h6
  by_cases e7 : N = 7
  · subst e7; exact h7
  rw [repsA_eq_nil e4 e5 e6 e7]
  simp

/-- The properties of the representatives used by the count. -/
def RepAProps {N : ℕ} (R : RepA N) : Prop :=
  IsOnePI R.rep ∧ QED.ThreeLoop.IsSetA R.rep ∧ Graded.gradedOrder R.kinds R.grad = 7 ∧
    (∀ t, R.grad t ≤ 1) ∧ vlistA R.rep = List.finRange N

theorem vlistA_repV : vlistA repVA = List.finRange 7 ∧ vlistA repVB = List.finRange 7 ∧
    vlistA repVC = List.finRange 7 := by
  decide +kernel

theorem vlistA_repF : vlistA repFA = List.finRange 6 ∧ vlistA repFB = List.finRange 6 := by
  decide +kernel

theorem vlistA_repG : vlistA repGW = List.finRange 5 ∧ vlistA repGU = List.finRange 5 := by
  decide +kernel

theorem vlistA_repP : ∀ s, vlistA (repP s) = List.finRange 4 := by
  decide +kernel

theorem gradP_le : ∀ t, gradP t ≤ 1 := fun _ => le_rfl

theorem repsA_props : ∀ R ∈ repsA N, RepAProps R := by
  refine repsA_cases (fun _ R => RepAProps R) ?_ ?_ ?_ ?_
  · simp only [repsA4, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl) <;>
      exact ⟨isOnePI_repP _, isSetA_repP _, gradedOrder_kP, gradP_le, vlistA_repP _⟩
  · simp only [repsA5, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl)
    · exact ⟨isOnePI_repGW, isSetA_repGW, gradedOrder_kGW, fun _ => Nat.zero_le _,
        vlistA_repG.1⟩
    · exact ⟨isOnePI_repGU, isSetA_repGU, gradedOrder_kGU, fun _ => Nat.zero_le _,
        vlistA_repG.2⟩
  · simp only [repsA6, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl)
    · exact ⟨isOnePI_repFA, isSetA_repFA, gradedOrder_kF, fun _ => Nat.zero_le _,
        vlistA_repF.1⟩
    · exact ⟨isOnePI_repFB, isSetA_repFB, gradedOrder_kF, fun _ => Nat.zero_le _,
        vlistA_repF.2⟩
  · simp only [repsA7, List.mem_cons, List.not_mem_nil, or_false]
    rintro R (rfl | rfl | rfl)
    · exact ⟨isOnePI_repVA, isSetA_repVA, gradedOrder_kV, fun _ => Nat.zero_le _,
        vlistA_repV.1⟩
    · exact ⟨isOnePI_repVB, isSetA_repVB, gradedOrder_kV, fun _ => Nat.zero_le _,
        vlistA_repV.2.1⟩
    · exact ⟨isOnePI_repVC, isSetA_repVC, gradedOrder_kV, fun _ => Nat.zero_le _,
        vlistA_repV.2.2⟩

/-- The signature of a representative: its kinds, raw vertex list and slot index of `x`. -/
def sigA (R : RepA N) : (Fin N → Wick.VertexKind) × List (Fin N) × List ℕ :=
  (R.kinds, rawA R.rep, slotIdxA R.rep)

/-- The signatures of the representatives with `N` vertices are pairwise distinct. -/
theorem nodup_sigA : ((repsA N).map sigA).Nodup := by
  by_cases e4 : N = 4
  · subst e4; decide +kernel
  by_cases e5 : N = 5
  · subst e5; decide +kernel
  by_cases e6 : N = 6
  · subst e6; decide +kernel
  by_cases e7 : N = 7
  · subst e7; decide +kernel
  rw [repsA_eq_nil e4 e5 e6 e7]
  exact List.nodup_nil

/-! ### Distinct classes, no automorphism -/

/-- **The relabelled representatives are pairwise distinct**: if two relabellings of
representatives with `N` vertices are the same contraction, the representatives (as positions
in `repsA N`) and the permutations agree. -/
theorem relabelK_repA_inj {i j : Fin (repsA N).length} {π π' : Equiv.Perm (Fin N)}
    (hκ : ∀ t, κ (π t) = ((repsA N).get i).kinds t)
    (hκ' : ∀ t, κ (π' t) = ((repsA N).get j).kinds t)
    (h : relabelK π hκ ((repsA N).get i).rep = relabelK π' hκ' ((repsA N).get j).rep) :
    i = j ∧ π = π' := by
  set R := (repsA N).get i with hR
  set R' := (repsA N).get j with hR'
  have hv := (repsA_props R (List.get_mem _ _)).2.2.2.2
  have hv' := (repsA_props R' (List.get_mem _ _)).2.2.2.2
  have hππ : π = π' := by
    have e := congrArg vlistA h
    rw [vlistA_relabelK, vlistA_relabelK, hv, hv'] at e
    ext t
    rw [List.map_inj_left.mp e t (List.mem_finRange t)]
  subst hππ
  refine ⟨?_, rfl⟩
  have hsig : sigA R = sigA R' := by
    refine Prod.ext (funext fun t => (hκ t).symm.trans (hκ' t)) (Prod.ext ?_ ?_)
    · have e := congrArg rawA h
      rw [rawA_relabelK, rawA_relabelK] at e
      exact List.map_injective_iff.mpr π.injective e
    · have e := congrArg slotIdxA h
      rwa [slotA_relabelK, slotA_relabelK] at e
  have hn := nodup_sigA (N := N)
  have hi : ((repsA N).map sigA).get (i.cast (List.length_map _).symm) = sigA R := by
    simp [hR]
  have hj : ((repsA N).map sigA).get (j.cast (List.length_map _).symm) = sigA R' := by
    simp [hR']
  have := (List.Nodup.get_inj_iff hn).mp (hi.trans (hsig.trans hj.symm))
  exact Fin.ext (by simpa using congrArg Fin.val this)

/-! ### The count -/

/-- **Each class has `N!` members.** For every function `G` of the graded contractions with `N`
vertices invariant under relabelling 1PI contractions across kind sequences (at the transported
grading), the sum over the kind sequences, their gradings of graded order `7` with levels in
`0, …, 7`, and their 1PI set (a) contractions of `fermionSign C * G C g` is `N!` times the signed
sum of `G` over the representatives with `N` vertices, at their gradings. The instances are
arbitrary (in particular the classical ones of (G₆)). -/
theorem sum_setA {instF : ∀ κ : Fin N → Wick.VertexKind, Fintype (Contraction 1 1 κ)}
    {instCF : ∀ κ : Fin N → Wick.VertexKind, Fintype (Graded.CtVertex κ)}
    {instCE : ∀ κ : Fin N → Wick.VertexKind, DecidableEq (Graded.CtVertex κ)}
    {instG : ∀ κ : Fin N → Wick.VertexKind,
      DecidablePred fun g : Graded.Grading κ => Graded.gradedOrder κ g = 7}
    {instC : ∀ κ : Fin N → Wick.VertexKind,
      DecidablePred fun C : Contraction 1 1 κ => IsOnePI C ∧ QED.ThreeLoop.IsSetA C}
    (G : ∀ {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Graded.Grading κ → ℂ)
    (hG : ∀ {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
      (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 1 κ) (g : Graded.Grading κ), IsOnePI C →
        G (relabelK π hκ C) (gradMap π hκ g) = G C g) :
    ∑ κ : Fin N → Wick.VertexKind,
      ∑ g ∈ (Fintype.piFinset fun _ : Graded.CtVertex κ => Finset.range (7 + 1)).filter
          (fun g => Graded.gradedOrder κ g = 7),
        ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter
            (fun C => IsOnePI C ∧ QED.ThreeLoop.IsSetA C),
          ((fermionSign C : ℤ) : ℂ) * G C g =
      (N.factorial : ℂ) * ∑ i : Fin (repsA N).length,
        ((fermionSign ((repsA N).get i).rep : ℤ) : ℂ) *
          G ((repsA N).get i).rep ((repsA N).get i).grad := by
  set R : Fin (repsA N).length → RepA N := fun i => (repsA N).get i with hRdef
  have hR : ∀ i, R i ∈ repsA N := fun i => List.get_mem _ _
  set gk : Fin (repsA N).length × Equiv.Perm (Fin N) → (Fin N → Wick.VertexKind) :=
    fun p => (R p.1).kinds ∘ p.2.symm with hgk
  set F : Fin (repsA N).length × Equiv.Perm (Fin N) → ℂ :=
    fun p => ((fermionSign (R p.1).rep : ℤ) : ℂ) * G (R p.1).rep (R p.1).grad with hF
  have hκ_of : ∀ {κ : Fin N → Wick.VertexKind} {p}, gk p = κ →
      ∀ t, κ (p.2 t) = (R p.1).kinds t :=
    fun {κ} {p} hp t => by rw [← hp]; simp [hgk]
  have inner : ∀ κ : Fin N → Wick.VertexKind,
      ∑ g ∈ (Fintype.piFinset fun _ : Graded.CtVertex κ => Finset.range (7 + 1)).filter
          (fun g => Graded.gradedOrder κ g = 7),
        ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter
            (fun C => IsOnePI C ∧ QED.ThreeLoop.IsSetA C), ((fermionSign C : ℤ) : ℂ) * G C g =
        ∑ p ∈ (Finset.univ : Finset (Fin (repsA N).length × Equiv.Perm (Fin N))).filter
          (fun p => gk p = κ), F p := by
    intro κ
    rw [Finset.sum_sigma']
    symm
    refine Finset.sum_bij
      (fun p hp => (⟨gradMap p.2 (hκ_of (Finset.mem_filter.mp hp).2) (R p.1).grad,
        relabelK p.2 (hκ_of (Finset.mem_filter.mp hp).2) (R p.1).rep⟩ :
          (_ : Graded.Grading κ) × Contraction 1 1 κ)) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨h1, h2, h3, h4, -⟩ := repsA_props _ (hR p.1)
      refine Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr fun s => ?_, ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
      · have := h4 ((ctMap p.2 (hκ_of (Finset.mem_filter.mp hp).2)).symm s)
        exact Finset.mem_range.mpr (by simp only [gradMap]; omega)
      · rw [gradedOrder_gradMap, h3]
      · exact (isOnePI_relabelK_iff _ _ _).mpr h1
      · exact isSetA_relabelK _ _ h2
    · intro p _ q _ hpq
      obtain ⟨h1, h2⟩ := relabelK_repA_inj _ _ (eq_of_heq (Sigma.mk.inj_iff.mp hpq).2)
      exact Prod.ext h1 h2
    · rintro ⟨g, C⟩ hgC
      obtain ⟨hg, hC⟩ := Finset.mem_sigma.mp hgC
      have hg7 := (Finset.mem_filter.mp hg).2
      have hCA := (Finset.mem_filter.mp hC).2.2
      obtain ⟨R', hR', π, hκ, rfl, rfl⟩ := exists_rep_setA g hg7 hCA
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hR'
      refine ⟨(i, π), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      funext s
      simp only [hgk, hRdef, Function.comp_apply]
      rw [← hκ, Equiv.apply_symm_apply]
    · intro p _
      obtain ⟨h1, -⟩ := repsA_props _ (hR p.1)
      simp only [hF, fermionSign_relabelK, hG _ _ _ _ h1]
  rw [Finset.sum_congr rfl fun κ _ => inner κ, Finset.sum_fiberwise Finset.univ gk F,
    Fintype.sum_prod_type]
  simp only [hF, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]
  rfl

end QED.ChainProof.SetALink

end
