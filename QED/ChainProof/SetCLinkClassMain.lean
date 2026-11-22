/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkClassWalk
public import QED.ChainProof.SetCLinkClassDecB
public import QED.ChainProof.SetCLinkClassDecD

/-!
# The set (c) classification

Helper for the set (c) headline (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(decision D-58), the enumeration step. Every 1PI contraction of graded order `7` satisfying (Sc₃)
`QED.ThreeLoop.IsSetC` is a relabelling of one of the 56 representatives `repsC N` of
`QED/ChainProof/SetCLinkReps.lean`, with its grading.

The open line is followed from `Ψ(x)` (`exists_openLine`); its vertices in order, then the element
(the bubble `u, w` or the `photonCt` vertex), number all vertices (`bijective_ext`), and the
renumbered contraction has the standard fermion pairing. Its photon pairing is a perfect matching,
and the kernel search of `QED/ChainProof/SetCLinkClassDecB.lean` and
`QED/ChainProof/SetCLinkClassDecD.lean` finds it among the representatives.

## Main statements

* `QED.ChainProof.SetCLink.exists_rep_setC_B`, `exists_rep_setC_D`, `exists_rep_setC_S`: the
  bubble, `δ₃` and VP-share branches of (Sc₃).
* `QED.ChainProof.SetCLink.exists_rep_setC`: **the classification.**
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum QED.GradedProof.VP2

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Properties of the representatives used by the classification -/

theorem repsCZ_eq_nil (h4 : N ≠ 4) (h5 : N ≠ 5) (h6 : N ≠ 6) (h7 : N ≠ 7) : repsCZ N = [] := by
  unfold repsCZ
  split <;> simp_all

theorem repsCS_eq_nil (h3 : N ≠ 3) (h4 : N ≠ 4) : repsCS N = [] := by
  unfold repsCS
  split <;> simp_all

theorem repsCZ_props : ∀ R ∈ repsCZ N, ∑ t, (R.kinds t).order = 7 ∧ R.grad = 0 := by
  by_cases e4 : N = 4
  · subst e4; decide +kernel
  by_cases e5 : N = 5
  · subst e5; decide +kernel
  by_cases e6 : N = 6
  · subst e6; decide +kernel
  by_cases e7 : N = 7
  · subst e7; decide +kernel
  rw [repsCZ_eq_nil e4 e5 e6 e7]
  simp

theorem repsCS_props : ∀ R ∈ repsCS N, R.grad = gOne _ := by
  by_cases e3 : N = 3
  · subst e3; decide +kernel
  by_cases e4 : N = 4
  · subst e4; decide +kernel
  rw [repsCS_eq_nil e3 e4]
  simp

/-! ### Agreement along the open line -/

section Agree

variable {κ₀ : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
  (h' : ∀ t, κ₀ (π.symm t) = κ t)

theorem extFK_symm_toFN (i : ℕ) (hi : i < N) (w : Wick.FermionVertex κ)
    (hw : w.1 = π ⟨i, hi⟩) : (extFK (nf := 1) π.symm h').symm (toFN κ₀ i) = .inr w := by
  have hk : κ₀ ⟨i, hi⟩ ≠ .photonCt := by
    rw [show κ₀ ⟨i, hi⟩ = κ (π ⟨i, hi⟩) by rw [← h' (π _), π.symm_apply_apply], ← hw]
    exact w.2
  rw [toFN_eq i hi hk]
  exact extFK_symm_inr_eq π h' _ w hw

theorem extFK_symm_inl : (extFK (nf := 1) π.symm h').symm (.inl 0) = .inl 0 := rfl

variable {C : Contraction 1 1 κ} {L : ℕ} {ov : ℕ → Fin N}

theorem agree_inl (hol : OpenLine C L ov) (hπ : ∀ a : Fin N, a.val < L → π a = ov a.val)
    (b : Bool) :
    C.1.1 ((extFK π.symm h').symm (.inl 0)) =
      (extFK π.symm h').symm (stdNext κ₀ L b (.inl 0)) := by
  rw [extFK_symm_inl]
  by_cases hL : 0 < L
  · have h0 : 0 < N := (ov 0).pos
    simp only [stdNext, ite_eq_left hL]
    rw [extFK_symm_toFN π h' 0 h0 ⟨ov 0, hol.isFV 0 hL⟩ (hπ ⟨0, h0⟩ hL).symm]
    exact hol.start hL _ rfl
  · simp only [stdNext, ite_eq_right hL]
    exact hol.start0 (by omega)

theorem agree_open (hol : OpenLine C L ov) (hπ : ∀ a : Fin N, a.val < L → π a = ov a.val)
    (hLN : L ≤ N) (b : Bool) (j : Fin N) (hj : κ₀ j ≠ .photonCt) (hjL : j.val < L) :
    C.1.1 ((extFK π.symm h').symm (.inr ⟨j, hj⟩)) =
      (extFK π.symm h').symm (stdNext κ₀ L b (.inr ⟨j, hj⟩)) := by
  have hw : κ (ov j.val) ≠ .photonCt := hol.isFV _ hjL
  rw [extFK_symm_inr_eq π h' ⟨j, hj⟩ ⟨ov j.val, hw⟩ (hπ j hjL).symm]
  by_cases hj1 : j.val + 1 < L
  · simp only [stdNext, ite_eq_left hj1]
    have hN : j.val + 1 < N := by omega
    rw [extFK_symm_toFN π h' _ hN ⟨ov (j.val + 1), hol.isFV _ hj1⟩ (hπ ⟨_, hN⟩ hj1).symm]
    exact hol.step _ hj1 _ _ rfl rfl
  · have he : j.val + 1 = L := by omega
    simp only [stdNext, ite_eq_right hj1, ite_eq_left he]
    exact hol.stop _ he _ rfl

end Agree

/-! ### The bubble branch -/

theorem not_sameCycle_bubble {C : Contraction 1 1 κ} {u w : Wick.FermionVertex κ}
    (su : C.1.1 (.inr u) = .inr w) (sw : C.1.1 (.inr w) = .inr u) :
    ¬ (C.1.1).SameCycle (.inl 0) (.inr u) := fun h => by
  have := SetALink.mem_of_sameCycle_of_mapsTo (T := {Sum.inr u, Sum.inr w})
    (by simp [su, sw]) (by simp) h.symm
  simp at this

/-- **The bubble branch.** -/
theorem exists_rep_setC_B (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7)
    (hph : ∀ t : Graded.CtVertex κ, κ t.1 = .photonCt → g t = 0) {C : Contraction 1 1 κ}
    (h1 : IsOnePI C) {u w : Wick.FermionVertex κ} (ku : κ u.1 = .gauge) (kw : κ w.1 = .gauge)
    (huw : u ≠ w) (su : C.1.1 (.inr u) = .inr w) (sw : C.1.1 (.inr w) = .inr u)
    (hexh : ∀ t : Fin N, t = u.1 ∨ t = w.1 ∨
      ∃ v : Wick.FermionVertex κ, v.1 = t ∧ (C.1.1).SameCycle (.inl 0) (.inr v)) :
    ∃ R ∈ repsC N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨L, ov, hol⟩ := exists_openLine u.1.pos C
  have hu' := not_sameCycle_bubble su sw
  have hw' := not_sameCycle_bubble sw su
  have hne : ∀ i < L, ov i ≠ u.1 ∧ ov i ≠ w.1 := fun i hi =>
    ⟨fun e => hu' (hol.onCycle i hi u e.symm), fun e => hw' (hol.onCycle i hi w e.symm)⟩
  have huw1 : u.1 ≠ w.1 := fun e => huw (fv_ext e)
  set E : ℕ → Fin N := fun j => if j = 0 then u.1 else w.1 with hE
  have hb := bijective_ext (k := 2) ov E hol.inj
    (fun i j hi hj e => by
      interval_cases i <;> interval_cases j <;> simp_all)
    (fun i j hi hj => by
      interval_cases j
      · exact (hne i hi).1
      · exact (hne i hi).2)
    (fun t => by
      rcases hexh t with rfl | rfl | ⟨v, rfl, hv⟩
      · exact Or.inr ⟨0, by omega, by simp [hE]⟩
      · exact Or.inr ⟨1, by omega, by simp [hE]⟩
      · obtain ⟨i, hi, e⟩ := hol.cover v hv
        exact Or.inl ⟨i, hi, e⟩)
  have hN : L + 2 = N := by simpa using Fintype.card_of_bijective hb
  subst hN
  set π : Equiv.Perm (Fin (L + 2)) := Equiv.ofBijective _ hb with hπdef
  have hπv : ∀ a : Fin (L + 2), π a = if a.val < L then ov a.val else E (a.val - L) :=
    fun _ => rfl
  have hπ : ∀ a : Fin (L + 2), a.val < L → π a = ov a.val := fun a ha => by
    rw [hπv, ite_eq_left ha]
  have hπL : π ⟨L, by omega⟩ = u.1 := by rw [hπv]; simp [hE]
  have hπL1 : π ⟨L + 1, by omega⟩ = w.1 := by rw [hπv]; simp [hE]
  set ℓ : Fin L → Wick.VertexKind := fun i => κ (ov i.val) with hℓdef
  have hℓ : ∀ i, ℓ i ≠ .photonCt := fun i => hol.isFV i.val i.isLt
  have hk : ∀ a, kindsB ℓ a = κ (π a) := by
    intro a
    rw [hπv]
    unfold kindsB
    split_ifs with ha
    · rfl
    · simp only [hE]
      split_ifs
      · rw [ku]
      · rw [kw]
  have h' : ∀ t, kindsB ℓ (π.symm t) = κ t := fun t => by rw [hk, π.apply_symm_apply]
  have hstd : ∀ z, (relabelK π.symm h' C).1.1 z = stdNext (kindsB ℓ) L true z := by
    refine std_of_agree π h' C L true fun z => ?_
    rcases z with i | ⟨j, hj⟩
    · rw [Subsingleton.elim i 0]
      exact agree_inl π h' hol hπ true
    rcases (by omega : j.val < L ∨ j.val = L ∨ j.val = L + 1) with hjL | hjL | hjL
    · exact agree_open π h' hol hπ (by omega) true j hj hjL
    · have hj' : π j = u.1 := by rw [← hπL]; exact congrArg π (Fin.ext hjL)
      rw [extFK_symm_inr_eq π h' ⟨j, hj⟩ u hj'.symm, su]
      have e : stdNext (kindsB ℓ) L true (.inr ⟨j, hj⟩) = toFN (kindsB ℓ) (L + 1) := by
        simp only [stdNext, hjL]
        split_ifs <;> first | rfl | omega | simp_all
      rw [e]
      exact (extFK_symm_toFN π h' (L + 1) (by omega) w hπL1.symm).symm
    · have hj' : π j = w.1 := by rw [← hπL1]; exact congrArg π (Fin.ext hjL)
      rw [extFK_symm_inr_eq π h' ⟨j, hj⟩ w hj'.symm, sw]
      have e : stdNext (kindsB ℓ) L true (.inr ⟨j, hj⟩) = toFN (kindsB ℓ) L := by
        simp only [stdNext, hjL]
        split_ifs <;> first | rfl | omega | simp_all
      rw [e]
      exact (extFK_symm_toFN π h' L (by omega) u hπL.symm).symm
  have hK := kfilter_of π h' g hg hph
  have hL : L ≤ 5 := by
    have h1 := hK.1
    have h2 := card_le_sum_order (κ := kindsB ℓ)
    omega
  obtain ⟨R, hR, ρ, -, h, hC⟩ := decB_of_le hL ℓ hℓ hK _
    (mem_stdContractions _ L true hstd) ((isOnePI_relabelK_iff _ _ _).mpr h1)
  obtain ⟨hκ, hCeq⟩ := eq_relabelK_of_std π h' C R ρ h hC
  obtain ⟨h7, hg0⟩ := repsCZ_props R hR
  refine ⟨R, List.mem_append_left _ hR, π * ρ, hκ, hCeq, ?_⟩
  rw [hg0]
  exact SetALink.grad_eq_zero _ hκ g hg h7

/-! ### The `δ₃` branch -/

theorem sum_order_kindsD {L : ℕ} (ℓ : Fin L → Wick.VertexKind) :
    L + 2 ≤ ∑ t, (kindsD ℓ t).order := by
  rw [Fin.sum_univ_castSucc]
  have e1 : ∀ i : Fin L, kindsD ℓ (Fin.castSucc i) = ℓ i := fun i => by
    simp [kindsD]
  have e2 : kindsD ℓ (Fin.last L) = .photonCt := by simp [kindsD]
  simp only [e1, e2]
  have := card_le_sum_order (κ := ℓ)
  have h2 : Wick.VertexKind.photonCt.order = 2 := rfl
  omega

/-- **The `δ₃` branch.** -/
theorem exists_rep_setC_D (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7)
    (hph : ∀ t : Graded.CtVertex κ, κ t.1 = .photonCt → g t = 0) {C : Contraction 1 1 κ}
    (h1 : IsOnePI C) {t₀ : Fin N} (k0 : κ t₀ = .photonCt)
    (hexh : ∀ t : Fin N, t = t₀ ∨
      ∃ v : Wick.FermionVertex κ, v.1 = t ∧ (C.1.1).SameCycle (.inl 0) (.inr v)) :
    ∃ R ∈ repsC N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨L, ov, hol⟩ := exists_openLine t₀.pos C
  have hne : ∀ i < L, ov i ≠ t₀ := fun i hi e => hol.isFV i hi (e ▸ k0)
  have hb := bijective_ext (k := 1) ov (fun _ => t₀) hol.inj
    (fun i j hi hj _ => by omega)
    (fun i j hi hj => hne i hi)
    (fun t => by
      rcases hexh t with rfl | ⟨v, rfl, hv⟩
      · exact Or.inr ⟨0, by omega, rfl⟩
      · obtain ⟨i, hi, e⟩ := hol.cover v hv
        exact Or.inl ⟨i, hi, e⟩)
  have hN : L + 1 = N := by simpa using Fintype.card_of_bijective hb
  subst hN
  set π : Equiv.Perm (Fin (L + 1)) := Equiv.ofBijective _ hb with hπdef
  have hπv : ∀ a : Fin (L + 1), π a = if a.val < L then ov a.val else t₀ := fun _ => rfl
  have hπ : ∀ a : Fin (L + 1), a.val < L → π a = ov a.val := fun a ha => by
    rw [hπv, ite_eq_left ha]
  set ℓ : Fin L → Wick.VertexKind := fun i => κ (ov i.val) with hℓdef
  have hℓ : ∀ i, ℓ i ≠ .photonCt := fun i => hol.isFV i.val i.isLt
  have hk : ∀ a, kindsD ℓ a = κ (π a) := by
    intro a
    rw [hπv]
    unfold kindsD
    split_ifs with ha
    · rfl
    · rw [k0]
  have h' : ∀ t, kindsD ℓ (π.symm t) = κ t := fun t => by rw [hk, π.apply_symm_apply]
  have hstd : ∀ z, (relabelK π.symm h' C).1.1 z = stdNext (kindsD ℓ) L false z := by
    refine std_of_agree π h' C L false fun z => ?_
    rcases z with i | ⟨j, hj⟩
    · rw [Subsingleton.elim i 0]
      exact agree_inl π h' hol hπ false
    · have hjL : j.val < L := by
        by_contra hc
        apply hj
        simp [kindsD, hc]
      exact agree_open π h' hol hπ (by omega) false j hj hjL
  have hK := kfilter_of π h' g hg hph
  have hL : L ≤ 5 := by
    have h1 := hK.1
    have h2 := sum_order_kindsD ℓ
    omega
  obtain ⟨R, hR, h, hC⟩ := decD_of_le hL ℓ hℓ hK _
    (mem_stdContractions _ L false hstd) ((isOnePI_relabelK_iff _ _ _).mpr h1)
  obtain ⟨hκ, hCeq⟩ := eq_relabelK_of_std π h' C R 1 h hC
  obtain ⟨h7, hg0⟩ := repsCZ_props R hR
  refine ⟨R, List.mem_append_left _ hR, π * 1, hκ, hCeq, ?_⟩
  rw [hg0]
  exact SetALink.grad_eq_zero _ hκ g hg h7

/-! ### The VP-share branch -/

/-- **The VP-share branch.** -/
theorem exists_rep_setC_S (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7)
    {C : Contraction 1 1 κ} (h1 : IsOnePI C)
    (hall : ∀ t : Fin N, ∃ v : Wick.FermionVertex κ, v.1 = t ∧
      (C.1.1).SameCycle (.inl 0) (.inr v))
    {t₀ : Graded.CtVertex κ} (hg1 : g t₀ = 1) (hu : ∀ t : Graded.CtVertex κ, t = t₀) :
    ∃ R ∈ repsC N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨L, ov, hol⟩ := exists_openLine t₀.1.pos C
  have hb := bijective_ext (k := 0) ov (fun _ => t₀.1) hol.inj
    (fun i j hi hj _ => by omega) (fun i j hi hj => by omega)
    (fun t => by
      obtain ⟨v, rfl, hv⟩ := hall t
      obtain ⟨i, hi, e⟩ := hol.cover v hv
      exact Or.inl ⟨i, hi, e⟩)
  have hN : L = N := by simpa using Fintype.card_of_bijective hb
  subst hN
  set π : Equiv.Perm (Fin L) := Equiv.ofBijective _ hb with hπdef
  have hπ : ∀ a : Fin L, a.val < L → π a = ov a.val := fun a ha => by
    show (if a.val < L then ov a.val else t₀.1) = ov a.val
    rw [ite_eq_left ha]
  have hfv : ∀ t, κ t ≠ .photonCt := fun t => by
    obtain ⟨v, rfl, -⟩ := hall t
    exact v.2
  set ℓ : Fin L → Wick.VertexKind := fun i => κ (π i) with hℓdef
  have h' : ∀ t, ℓ (π.symm t) = κ t := fun t => by simp [hℓdef]
  have hstd : ∀ z, (relabelK π.symm h' C).1.1 z = stdNext ℓ L false z := by
    refine std_of_agree π h' C L false fun z => ?_
    rcases z with i | ⟨j, hj⟩
    · rw [Subsingleton.elim i 0]
      exact agree_inl π h' hol hπ false
    · exact agree_open π h' hol hπ le_rfl false j hj j.isLt
  have hS := sfilter_of π g hg hfv t₀ hg1 hu
  have hL : L ≤ 5 := by
    have h1 : ∑ t, (ℓ t).order = 5 := hS.2.1
    have h2 := card_le_sum_order (κ := ℓ)
    omega
  obtain ⟨R, hR, h, hC⟩ := decS_of_le hL ℓ hS _
    (mem_stdContractions _ L false hstd) ((isOnePI_relabelK_iff _ _ _).mpr h1)
  obtain ⟨hκ, hCeq⟩ := eq_relabelK_of_std π h' C R 1 h hC
  refine ⟨R, List.mem_append_right _ hR, π * 1, hκ, hCeq, ?_⟩
  rw [repsCS_props R hR]
  funext s
  rw [hu s, hg1]
  rfl

/-! ### The classification -/

/-- **The set (c) classification.** Every 1PI graded contraction `(κ, g, C)` of graded order `7`
satisfying (Sc₃) is a relabelling of one of the 56 representatives, with its grading. -/
theorem exists_rep_setC (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7)
    {C : Contraction 1 1 κ} (h1 : IsOnePI C) (hC : QED.ThreeLoop.IsSetC C g) :
    ∃ R ∈ repsC N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨hph, hD | hB | hS⟩ := hC
  · obtain ⟨t₀, k0, hexh⟩ := hD
    exact exists_rep_setC_D g hg hph h1 k0 hexh
  · obtain ⟨u, w, ku, kw, huw, su, sw, hexh⟩ := hB
    exact exists_rep_setC_B g hg hph h1 ku kw huw su sw hexh
  · obtain ⟨hall, t₀, hg1, hu⟩ := hS
    exact exists_rep_setC_S g hg h1 hall hg1 hu

end QED.ChainProof.SetCLink

end
