/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkClassify

/-!
# The set (a) classification: the open data and the loop classes by shape

Helper for the Phase 5 Stage 3a enumeration (decision D-58). `OpenA C W` collects the open-line
clauses of (A₁) `QED.ThreeLoop.IsSetA` for a witness `W`. Once the closed loop of a set (a)
contraction is identified as one of the shapes of the representatives of
`QED/ChainProof/SetALinkReps.lean`, the contraction is the relabelling of that representative;
this file does this for the seven loop shapes.

* `QED.ChainProof.SetALink.grad_eq_zero`: at graded order `7`, a kind sequence whose vertex
  orders already sum to `7` carries the zero grading.
* `QED.ChainProof.SetALink.exists_rep_V`: **the classes `VA`, `VB`, `VC`.** Seven gauge vertices
  `c, b, a, u, w, p, q`, the loop through `u, w, p, q` in one of the three cyclic orders of the
  representatives, and the internal photon `p ⇄ q`: the contraction is a relabelling of `repVA`,
  `repVB` or `repVC` with grading `0`.
* `QED.ChainProof.SetALink.exists_rep_F`: **the classes `FA`, `FB`** (a `fermionCt` vertex `r`
  on the loop `u → w → r` or `u → r → w`).
* `QED.ChainProof.SetALink.exists_rep_GW`, `exists_rep_GU`: **the classes `GW`, `GU`** (the loop
  `u ⇄ w`, the `gaugeCt` vertex at `w`, resp. `u`).
-/

@[expose] public section

namespace QED.ChainProof.SetALink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum QED.GradedProof.VP2

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The open-line clauses of (A₁) for a witness `W`. -/
structure OpenA (C : Contraction 1 1 κ) (W : SetAWitness κ) : Prop where
  ka : κ W.a.1 = .gauge
  kb : κ W.b.1 = .gauge
  kc : κ W.c.1 = .gauge
  s0a : C.1.1 (.inl 0) = .inr W.a
  sab : C.1.1 (.inr W.a) = .inr W.b
  sbc : C.1.1 (.inr W.b) = .inr W.c
  sc0 : C.1.1 (.inr W.c) = .inl 0
  hsb : W.sb.1 = W.b.1
  tsb : C.1.2 (.inl 0) = .inr W.sb
  hsa : W.sa.1 = W.a.1
  hsc : W.sc.1 = W.c.1
  hx : C.1.2 (.inr W.sa) = .inr W.x
  hy : C.1.2 (.inr W.sc) = .inr W.y

/-! ### Relabelling tools -/

/-- A vertex with one photon field has it at index `0`. -/
theorem slots_eq_one {t : Fin N} (h : κ t = .gauge ∨ κ t = .gaugeCt) :
    (κ t).photonSlots = 1 := by
  rcases h with h | h <;> rw [h] <;> rfl

theorem psMap_pg {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ (π t) = κ' t) {i : Fin N} (hi : 0 < (κ' i).photonSlots)
    {s : Wick.PhotonSlot κ} (h1 : π i = s.1) (h2 : (κ s.1).photonSlots = 1) :
    psMap π hκ (pg κ' i hi) = s := by
  refine ps_ext (by rw [psMap_fst]; exact h1) ?_
  rw [psMap_snd_val]
  have := s.2.isLt
  show 0 = s.2.val
  omega

/-- **The zero grading.** At graded order `7`, if the vertex orders of `κ'` sum to `7`, the
grading of `κ` is the transported zero grading. -/
theorem grad_eq_zero {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ (π t) = κ' t) (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7)
    (h7 : ∑ t, (κ' t).order = 7) : g = gradMap π hκ 0 := by
  have hs : ∑ t, (κ t).order = 7 := by
    rw [← Equiv.sum_comp π]
    simp only [hκ]
    exact h7
  rw [gradedOrder_eq, hs] at hg
  have h0 : ∑ t : Graded.CtVertex κ, 2 * g t = 0 := by omega
  funext t
  have := (Finset.sum_eq_zero_iff.1 h0) t (Finset.mem_univ _)
  rw [gradMap_zero, Pi.zero_apply]
  omega

/-! ### Tables of the seven-vertex representatives -/

theorem kV_fields : ∀ z : Fin 1 ⊕ Wick.FermionVertex kV, z = .inl 0 ∨ z = .inr (fv kV 0) ∨
    z = .inr (fv kV 1) ∨ z = .inr (fv kV 2) ∨ z = .inr (fv kV 3) ∨ z = .inr (fv kV 4) ∨
      z = .inr (fv kV 5) ∨ z = .inr (fv kV 6) := by
  decide +kernel

theorem kV_slots : ∀ z : Fin 1 ⊕ Wick.PhotonSlot kV, z = .inl 0 ∨ z = .inr (pg kV 0) ∨
    z = .inr (pg kV 1) ∨ z = .inr (pg kV 2) ∨ z = .inr (pg kV 3) ∨ z = .inr (pg kV 4) ∨
      z = .inr (pg kV 5) ∨ z = .inr (pg kV 6) := by
  decide +kernel

theorem tauV_tab : tauV (.inl 0) = .inr (pg kV 1) ∧ tauV (.inr (pg kV 1)) = .inl 0 ∧
    tauV (.inr (pg kV 2)) = .inr (pg kV 3) ∧ tauV (.inr (pg kV 3)) = .inr (pg kV 2) ∧
    tauV (.inr (pg kV 0)) = .inr (pg kV 4) ∧ tauV (.inr (pg kV 4)) = .inr (pg kV 0) ∧
    tauV (.inr (pg kV 5)) = .inr (pg kV 6) ∧ tauV (.inr (pg kV 6)) = .inr (pg kV 5) := by
  decide +kernel

theorem repVA_tab : repVA.1.1 (.inl 0) = .inr (fv kV 2) ∧
    repVA.1.1 (.inr (fv kV 2)) = .inr (fv kV 1) ∧ repVA.1.1 (.inr (fv kV 1)) = .inr (fv kV 0) ∧
    repVA.1.1 (.inr (fv kV 0)) = .inl 0 ∧ repVA.1.1 (.inr (fv kV 3)) = .inr (fv kV 4) ∧
    repVA.1.1 (.inr (fv kV 4)) = .inr (fv kV 5) ∧ repVA.1.1 (.inr (fv kV 5)) = .inr (fv kV 6) ∧
    repVA.1.1 (.inr (fv kV 6)) = .inr (fv kV 3) := by
  decide +kernel

theorem repVB_tab : repVB.1.1 (.inl 0) = .inr (fv kV 2) ∧
    repVB.1.1 (.inr (fv kV 2)) = .inr (fv kV 1) ∧ repVB.1.1 (.inr (fv kV 1)) = .inr (fv kV 0) ∧
    repVB.1.1 (.inr (fv kV 0)) = .inl 0 ∧ repVB.1.1 (.inr (fv kV 3)) = .inr (fv kV 5) ∧
    repVB.1.1 (.inr (fv kV 5)) = .inr (fv kV 4) ∧ repVB.1.1 (.inr (fv kV 4)) = .inr (fv kV 6) ∧
    repVB.1.1 (.inr (fv kV 6)) = .inr (fv kV 3) := by
  decide +kernel

theorem repVC_tab : repVC.1.1 (.inl 0) = .inr (fv kV 2) ∧
    repVC.1.1 (.inr (fv kV 2)) = .inr (fv kV 1) ∧ repVC.1.1 (.inr (fv kV 1)) = .inr (fv kV 0) ∧
    repVC.1.1 (.inr (fv kV 0)) = .inl 0 ∧ repVC.1.1 (.inr (fv kV 3)) = .inr (fv kV 5) ∧
    repVC.1.1 (.inr (fv kV 5)) = .inr (fv kV 6) ∧ repVC.1.1 (.inr (fv kV 6)) = .inr (fv kV 4) ∧
    repVC.1.1 (.inr (fv kV 4)) = .inr (fv kV 3) := by
  decide +kernel

theorem order_kV : ∑ t, (kV t).order = 7 := by decide +kernel

/-! ### The classes `VA`, `VB`, `VC` -/

/-- **The two-loop-bubble classes.** -/
theorem exists_rep_V {C : Contraction 1 1 κ} {W : SetAWitness κ} (h : OpenA C W)
    {u w p q : Wick.FermionVertex κ} {sp sq : Wick.PhotonSlot κ}
    (hu : u.1 = W.x.1) (hw : w.1 = W.y.1) (hsp : sp.1 = p.1) (hsq : sq.1 = q.1)
    (ku : κ u.1 = .gauge) (kw : κ w.1 = .gauge) (kp : κ p.1 = .gauge) (kq : κ q.1 = .gauge)
    (tpq : C.1.2 (.inr sp) = .inr sq)
    (hloop : (C.1.1 (.inr u) = .inr w ∧ C.1.1 (.inr w) = .inr p ∧ C.1.1 (.inr p) = .inr q ∧
        C.1.1 (.inr q) = .inr u) ∨
      (C.1.1 (.inr u) = .inr p ∧ C.1.1 (.inr p) = .inr w ∧ C.1.1 (.inr w) = .inr q ∧
        C.1.1 (.inr q) = .inr u) ∨
      (C.1.1 (.inr u) = .inr p ∧ C.1.1 (.inr p) = .inr q ∧ C.1.1 (.inr q) = .inr w ∧
        C.1.1 (.inr w) = .inr u))
    (hinj : Function.Injective ![W.c.1, W.b.1, W.a.1, u.1, w.1, p.1, q.1])
    (hsurj : Function.Surjective ![W.c.1, W.b.1, W.a.1, u.1, w.1, p.1, q.1])
    (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7) :
    ∃ R ∈ repsA N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨ka, kb, kc, s0a, sab, sbc, sc0, hsb, tsb, hsa, hsc, hx, hy⟩ := h
  have hbij : Function.Bijective ![W.c.1, W.b.1, W.a.1, u.1, w.1, p.1, q.1] := ⟨hinj, hsurj⟩
  have hN : 7 = N := by simpa using Fintype.card_of_bijective hbij
  subst hN
  set π : Equiv.Perm (Fin 7) := Equiv.ofBijective _ hbij with hπ
  have hκ : ∀ t, κ (π t) = kV t := by
    intro t
    fin_cases t
    exacts [kc, kb, ka, ku, kw, kp, kq]
  have m0 : fvMap π hκ (fv kV 0) = W.c := fv_ext rfl
  have m1 : fvMap π hκ (fv kV 1) = W.b := fv_ext rfl
  have m2 : fvMap π hκ (fv kV 2) = W.a := fv_ext rfl
  have m3 : fvMap π hκ (fv kV 3) = u := fv_ext rfl
  have m4 : fvMap π hκ (fv kV 4) = w := fv_ext rfl
  have m5 : fvMap π hκ (fv kV 5) = p := fv_ext rfl
  have m6 : fvMap π hκ (fv kV 6) = q := fv_ext rfl
  have n0 : psMap π hκ (pg kV 0) = W.sc :=
    psMap_pg π hκ _ hsc.symm (slots_eq_one (Or.inl (by rw [hsc]; exact kc)))
  have n1 : psMap π hκ (pg kV 1) = W.sb :=
    psMap_pg π hκ _ hsb.symm (slots_eq_one (Or.inl (by rw [hsb]; exact kb)))
  have n2 : psMap π hκ (pg kV 2) = W.sa :=
    psMap_pg π hκ _ hsa.symm (slots_eq_one (Or.inl (by rw [hsa]; exact ka)))
  have n3 : psMap π hκ (pg kV 3) = W.x :=
    psMap_pg π hκ _ hu (slots_eq_one (Or.inl (by rw [← hu]; exact ku)))
  have n4 : psMap π hκ (pg kV 4) = W.y :=
    psMap_pg π hκ _ hw (slots_eq_one (Or.inl (by rw [← hw]; exact kw)))
  have n5 : psMap π hκ (pg kV 5) = sp :=
    psMap_pg π hκ _ hsp.symm (slots_eq_one (Or.inl (by rw [hsp]; exact kp)))
  have n6 : psMap π hκ (pg kV 6) = sq :=
    psMap_pg π hκ _ hsq.symm (slots_eq_one (Or.inl (by rw [hsq]; exact kq)))
  have t1 := tau_symm C tsb
  have t2 := tau_symm C hx
  have t3 := tau_symm C hy
  have t4 := tau_symm C tpq
  have key : ∀ R : Contraction 1 1 kV, (⟨kV, R, 0⟩ : RepA 7) ∈ repsA 7 → R.1.2 = tauV →
      (∀ z, C.1.1 (extFK π hκ z) = extFK π hκ (R.1.1 z)) →
      ∃ R ∈ repsA 7, ∃ π : Equiv.Perm (Fin 7), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
        C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
    intro R hR hτ hσ
    refine ⟨_, hR, π, hκ, eq_relabelK_of_agree π hκ R C hσ fun z => ?_,
      grad_eq_zero π hκ g hg order_kV⟩
    rw [hτ]
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := tauV_tab
    rcases kV_slots z with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e0, e1, e2, e3, e4, e5, e6, e7, extPK_inl, extPK_inr, n0, n1, n2, n3, n4, n5,
        n6] <;> assumption
  rcases hloop with ⟨l0, l1, l2, l3⟩ | ⟨l0, l1, l2, l3⟩ | ⟨l0, l1, l2, l3⟩
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := repVA_tab
    refine key repVA (by simp [repsA, repsA7]) rfl fun z => ?_
    rcases kV_fields z with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [c0, c1, c2, c3, c4, c5, c6, c7, extFK_inl, extFK_inr, m0, m1, m2, m3, m4, m5,
        m6] <;> assumption
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := repVB_tab
    refine key repVB (by simp [repsA, repsA7]) rfl fun z => ?_
    rcases kV_fields z with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [c0, c1, c2, c3, c4, c5, c6, c7, extFK_inl, extFK_inr, m0, m1, m2, m3, m4, m5,
        m6] <;> assumption
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := repVC_tab
    refine key repVC (by simp [repsA, repsA7]) rfl fun z => ?_
    rcases kV_fields z with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [c0, c1, c2, c3, c4, c5, c6, c7, extFK_inl, extFK_inr, m0, m1, m2, m3, m4, m5,
        m6] <;> assumption

/-! ### Tables of the six- and five-vertex representatives -/

theorem kF_fields : ∀ z : Fin 1 ⊕ Wick.FermionVertex kF, z = .inl 0 ∨ z = .inr (fv kF 0) ∨
    z = .inr (fv kF 1) ∨ z = .inr (fv kF 2) ∨ z = .inr (fv kF 3) ∨ z = .inr (fv kF 4) ∨
      z = .inr (fv kF 5) := by
  decide +kernel

theorem kF_slots : ∀ z : Fin 1 ⊕ Wick.PhotonSlot kF, z = .inl 0 ∨ z = .inr (pg kF 0) ∨
    z = .inr (pg kF 1) ∨ z = .inr (pg kF 2) ∨ z = .inr (pg kF 3) ∨ z = .inr (pg kF 4) := by
  decide +kernel

theorem tauF_tab : openTau witF (.inl 0) = .inr (pg kF 1) ∧
    openTau witF (.inr (pg kF 1)) = .inl 0 ∧ openTau witF (.inr (pg kF 2)) = .inr (pg kF 3) ∧
    openTau witF (.inr (pg kF 3)) = .inr (pg kF 2) ∧
    openTau witF (.inr (pg kF 0)) = .inr (pg kF 4) ∧
    openTau witF (.inr (pg kF 4)) = .inr (pg kF 0) := by
  decide +kernel

theorem repFA_tab : repFA.1.1 (.inl 0) = .inr (fv kF 2) ∧
    repFA.1.1 (.inr (fv kF 2)) = .inr (fv kF 1) ∧ repFA.1.1 (.inr (fv kF 1)) = .inr (fv kF 0) ∧
    repFA.1.1 (.inr (fv kF 0)) = .inl 0 ∧ repFA.1.1 (.inr (fv kF 3)) = .inr (fv kF 4) ∧
    repFA.1.1 (.inr (fv kF 4)) = .inr (fv kF 5) ∧
    repFA.1.1 (.inr (fv kF 5)) = .inr (fv kF 3) := by
  decide +kernel

theorem repFB_tab : repFB.1.1 (.inl 0) = .inr (fv kF 2) ∧
    repFB.1.1 (.inr (fv kF 2)) = .inr (fv kF 1) ∧ repFB.1.1 (.inr (fv kF 1)) = .inr (fv kF 0) ∧
    repFB.1.1 (.inr (fv kF 0)) = .inl 0 ∧ repFB.1.1 (.inr (fv kF 3)) = .inr (fv kF 5) ∧
    repFB.1.1 (.inr (fv kF 5)) = .inr (fv kF 4) ∧
    repFB.1.1 (.inr (fv kF 4)) = .inr (fv kF 3) := by
  decide +kernel

theorem order_kF : ∑ t, (kF t).order = 7 := by decide +kernel

theorem kGW_fields : ∀ z : Fin 1 ⊕ Wick.FermionVertex kGW, z = .inl 0 ∨
    z = .inr (fv kGW 0) ∨ z = .inr (fv kGW 1) ∨ z = .inr (fv kGW 2) ∨ z = .inr (fv kGW 3) ∨
      z = .inr (fv kGW 4) := by
  decide +kernel

theorem kGW_slots : ∀ z : Fin 1 ⊕ Wick.PhotonSlot kGW, z = .inl 0 ∨ z = .inr (pg kGW 0) ∨
    z = .inr (pg kGW 1) ∨ z = .inr (pg kGW 2) ∨ z = .inr (pg kGW 3) ∨ z = .inr (pg kGW 4) := by
  decide +kernel

theorem tauGW_tab : openTau witGW (.inl 0) = .inr (pg kGW 1) ∧
    openTau witGW (.inr (pg kGW 1)) = .inl 0 ∧
    openTau witGW (.inr (pg kGW 2)) = .inr (pg kGW 3) ∧
    openTau witGW (.inr (pg kGW 3)) = .inr (pg kGW 2) ∧
    openTau witGW (.inr (pg kGW 0)) = .inr (pg kGW 4) ∧
    openTau witGW (.inr (pg kGW 4)) = .inr (pg kGW 0) := by
  decide +kernel

theorem repGW_tab : repGW.1.1 (.inl 0) = .inr (fv kGW 2) ∧
    repGW.1.1 (.inr (fv kGW 2)) = .inr (fv kGW 1) ∧
    repGW.1.1 (.inr (fv kGW 1)) = .inr (fv kGW 0) ∧ repGW.1.1 (.inr (fv kGW 0)) = .inl 0 ∧
    repGW.1.1 (.inr (fv kGW 3)) = .inr (fv kGW 4) ∧
    repGW.1.1 (.inr (fv kGW 4)) = .inr (fv kGW 3) := by
  decide +kernel

theorem order_kGW : ∑ t, (kGW t).order = 7 := by decide +kernel

theorem kGU_fields : ∀ z : Fin 1 ⊕ Wick.FermionVertex kGU, z = .inl 0 ∨
    z = .inr (fv kGU 0) ∨ z = .inr (fv kGU 1) ∨ z = .inr (fv kGU 2) ∨ z = .inr (fv kGU 3) ∨
      z = .inr (fv kGU 4) := by
  decide +kernel

theorem kGU_slots : ∀ z : Fin 1 ⊕ Wick.PhotonSlot kGU, z = .inl 0 ∨ z = .inr (pg kGU 0) ∨
    z = .inr (pg kGU 1) ∨ z = .inr (pg kGU 2) ∨ z = .inr (pg kGU 3) ∨ z = .inr (pg kGU 4) := by
  decide +kernel

theorem tauGU_tab : openTau witGU (.inl 0) = .inr (pg kGU 1) ∧
    openTau witGU (.inr (pg kGU 1)) = .inl 0 ∧
    openTau witGU (.inr (pg kGU 2)) = .inr (pg kGU 3) ∧
    openTau witGU (.inr (pg kGU 3)) = .inr (pg kGU 2) ∧
    openTau witGU (.inr (pg kGU 0)) = .inr (pg kGU 4) ∧
    openTau witGU (.inr (pg kGU 4)) = .inr (pg kGU 0) := by
  decide +kernel

theorem repGU_tab : repGU.1.1 (.inl 0) = .inr (fv kGU 2) ∧
    repGU.1.1 (.inr (fv kGU 2)) = .inr (fv kGU 1) ∧
    repGU.1.1 (.inr (fv kGU 1)) = .inr (fv kGU 0) ∧ repGU.1.1 (.inr (fv kGU 0)) = .inl 0 ∧
    repGU.1.1 (.inr (fv kGU 3)) = .inr (fv kGU 4) ∧
    repGU.1.1 (.inr (fv kGU 4)) = .inr (fv kGU 3) := by
  decide +kernel

theorem order_kGU : ∑ t, (kGU t).order = 7 := by decide +kernel

/-! ### The classes `FA`, `FB` -/

/-- **The `fermionCt` classes.** -/
theorem exists_rep_F {C : Contraction 1 1 κ} {W : SetAWitness κ} (h : OpenA C W)
    {u w r : Wick.FermionVertex κ} (hu : u.1 = W.x.1) (hw : w.1 = W.y.1)
    (ku : κ u.1 = .gauge) (kw : κ w.1 = .gauge) (kr : κ r.1 = .fermionCt)
    (hloop : (C.1.1 (.inr u) = .inr w ∧ C.1.1 (.inr w) = .inr r ∧ C.1.1 (.inr r) = .inr u) ∨
      (C.1.1 (.inr u) = .inr r ∧ C.1.1 (.inr r) = .inr w ∧ C.1.1 (.inr w) = .inr u))
    (hinj : Function.Injective ![W.c.1, W.b.1, W.a.1, u.1, w.1, r.1])
    (hsurj : Function.Surjective ![W.c.1, W.b.1, W.a.1, u.1, w.1, r.1])
    (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7) :
    ∃ R ∈ repsA N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨ka, kb, kc, s0a, sab, sbc, sc0, hsb, tsb, hsa, hsc, hx, hy⟩ := h
  have hbij : Function.Bijective ![W.c.1, W.b.1, W.a.1, u.1, w.1, r.1] := ⟨hinj, hsurj⟩
  have hN : 6 = N := by simpa using Fintype.card_of_bijective hbij
  subst hN
  set π : Equiv.Perm (Fin 6) := Equiv.ofBijective _ hbij with hπ
  have hκ : ∀ t, κ (π t) = kF t := by
    intro t
    fin_cases t
    exacts [kc, kb, ka, ku, kw, kr]
  have m0 : fvMap π hκ (fv kF 0) = W.c := fv_ext rfl
  have m1 : fvMap π hκ (fv kF 1) = W.b := fv_ext rfl
  have m2 : fvMap π hκ (fv kF 2) = W.a := fv_ext rfl
  have m3 : fvMap π hκ (fv kF 3) = u := fv_ext rfl
  have m4 : fvMap π hκ (fv kF 4) = w := fv_ext rfl
  have m5 : fvMap π hκ (fv kF 5) = r := fv_ext rfl
  have n0 : psMap π hκ (pg kF 0) = W.sc :=
    psMap_pg π hκ _ hsc.symm (slots_eq_one (Or.inl (by rw [hsc]; exact kc)))
  have n1 : psMap π hκ (pg kF 1) = W.sb :=
    psMap_pg π hκ _ hsb.symm (slots_eq_one (Or.inl (by rw [hsb]; exact kb)))
  have n2 : psMap π hκ (pg kF 2) = W.sa :=
    psMap_pg π hκ _ hsa.symm (slots_eq_one (Or.inl (by rw [hsa]; exact ka)))
  have n3 : psMap π hκ (pg kF 3) = W.x :=
    psMap_pg π hκ _ hu (slots_eq_one (Or.inl (by rw [← hu]; exact ku)))
  have n4 : psMap π hκ (pg kF 4) = W.y :=
    psMap_pg π hκ _ hw (slots_eq_one (Or.inl (by rw [← hw]; exact kw)))
  have t1 := tau_symm C tsb
  have t2 := tau_symm C hx
  have t3 := tau_symm C hy
  have key : ∀ R : Contraction 1 1 kF, (⟨kF, R, 0⟩ : RepA 6) ∈ repsA 6 →
      R.1.2 = openTau witF → (∀ z, C.1.1 (extFK π hκ z) = extFK π hκ (R.1.1 z)) →
      ∃ R ∈ repsA 6, ∃ π : Equiv.Perm (Fin 6), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
        C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
    intro R hR hτ hσ
    refine ⟨_, hR, π, hκ, eq_relabelK_of_agree π hκ R C hσ fun z => ?_,
      grad_eq_zero π hκ g hg order_kF⟩
    rw [hτ]
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := tauF_tab
    rcases kF_slots z with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e0, e1, e2, e3, e4, e5, extPK_inl, extPK_inr, n0, n1, n2, n3, n4] <;>
      assumption
  rcases hloop with ⟨l0, l1, l2⟩ | ⟨l0, l1, l2⟩
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := repFA_tab
    refine key repFA (by simp [repsA, repsA6]) rfl fun z => ?_
    rcases kF_fields z with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [c0, c1, c2, c3, c4, c5, c6, extFK_inl, extFK_inr, m0, m1, m2, m3, m4, m5] <;>
      assumption
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := repFB_tab
    refine key repFB (by simp [repsA, repsA6]) rfl fun z => ?_
    rcases kF_fields z with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [c0, c1, c2, c3, c4, c5, c6, extFK_inl, extFK_inr, m0, m1, m2, m3, m4, m5] <;>
      assumption

/-! ### The classes `GW`, `GU` -/

/-- **The `gaugeCt` class `GW`** (the counterterm at `w`). -/
theorem exists_rep_GW {C : Contraction 1 1 κ} {W : SetAWitness κ} (h : OpenA C W)
    {u w : Wick.FermionVertex κ} (hu : u.1 = W.x.1) (hw : w.1 = W.y.1)
    (ku : κ u.1 = .gauge) (kw : κ w.1 = .gaugeCt)
    (huw : C.1.1 (.inr u) = .inr w) (hwu : C.1.1 (.inr w) = .inr u)
    (hinj : Function.Injective ![W.c.1, W.b.1, W.a.1, u.1, w.1])
    (hsurj : Function.Surjective ![W.c.1, W.b.1, W.a.1, u.1, w.1])
    (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7) :
    ∃ R ∈ repsA N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨ka, kb, kc, s0a, sab, sbc, sc0, hsb, tsb, hsa, hsc, hx, hy⟩ := h
  have hbij : Function.Bijective ![W.c.1, W.b.1, W.a.1, u.1, w.1] := ⟨hinj, hsurj⟩
  have hN : 5 = N := by simpa using Fintype.card_of_bijective hbij
  subst hN
  set π : Equiv.Perm (Fin 5) := Equiv.ofBijective _ hbij with hπ
  have hκ : ∀ t, κ (π t) = kGW t := by
    intro t
    fin_cases t
    exacts [kc, kb, ka, ku, kw]
  have m0 : fvMap π hκ (fv kGW 0) = W.c := fv_ext rfl
  have m1 : fvMap π hκ (fv kGW 1) = W.b := fv_ext rfl
  have m2 : fvMap π hκ (fv kGW 2) = W.a := fv_ext rfl
  have m3 : fvMap π hκ (fv kGW 3) = u := fv_ext rfl
  have m4 : fvMap π hκ (fv kGW 4) = w := fv_ext rfl
  have n0 : psMap π hκ (pg kGW 0) = W.sc :=
    psMap_pg π hκ _ hsc.symm (slots_eq_one (Or.inl (by rw [hsc]; exact kc)))
  have n1 : psMap π hκ (pg kGW 1) = W.sb :=
    psMap_pg π hκ _ hsb.symm (slots_eq_one (Or.inl (by rw [hsb]; exact kb)))
  have n2 : psMap π hκ (pg kGW 2) = W.sa :=
    psMap_pg π hκ _ hsa.symm (slots_eq_one (Or.inl (by rw [hsa]; exact ka)))
  have n3 : psMap π hκ (pg kGW 3) = W.x :=
    psMap_pg π hκ _ hu (slots_eq_one (Or.inl (by rw [← hu]; exact ku)))
  have n4 : psMap π hκ (pg kGW 4) = W.y :=
    psMap_pg π hκ _ hw (slots_eq_one (Or.inr (by rw [← hw]; exact kw)))
  have t1 := tau_symm C tsb
  have t2 := tau_symm C hx
  have t3 := tau_symm C hy
  refine ⟨⟨kGW, repGW, 0⟩, by simp [repsA, repsA5], π, hκ, ?_,
    grad_eq_zero π hκ g hg order_kGW⟩
  refine eq_relabelK_of_agree π hκ repGW C (fun z => ?_) (fun z => ?_)
  · obtain ⟨c0, c1, c2, c3, c4, c5⟩ := repGW_tab
    rcases kGW_fields z with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [c0, c1, c2, c3, c4, c5, extFK_inl, extFK_inr, m0, m1, m2, m3, m4] <;>
      assumption
  · change C.1.2 _ = extPK π hκ (openTau witGW z)
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := tauGW_tab
    rcases kGW_slots z with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e0, e1, e2, e3, e4, e5, extPK_inl, extPK_inr, n0, n1, n2, n3, n4] <;>
      assumption

/-- **The `gaugeCt` class `GU`** (the counterterm at `u`). -/
theorem exists_rep_GU {C : Contraction 1 1 κ} {W : SetAWitness κ} (h : OpenA C W)
    {u w : Wick.FermionVertex κ} (hu : u.1 = W.x.1) (hw : w.1 = W.y.1)
    (ku : κ u.1 = .gaugeCt) (kw : κ w.1 = .gauge)
    (huw : C.1.1 (.inr u) = .inr w) (hwu : C.1.1 (.inr w) = .inr u)
    (hinj : Function.Injective ![W.c.1, W.b.1, W.a.1, u.1, w.1])
    (hsurj : Function.Surjective ![W.c.1, W.b.1, W.a.1, u.1, w.1])
    (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7) :
    ∃ R ∈ repsA N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨ka, kb, kc, s0a, sab, sbc, sc0, hsb, tsb, hsa, hsc, hx, hy⟩ := h
  have hbij : Function.Bijective ![W.c.1, W.b.1, W.a.1, u.1, w.1] := ⟨hinj, hsurj⟩
  have hN : 5 = N := by simpa using Fintype.card_of_bijective hbij
  subst hN
  set π : Equiv.Perm (Fin 5) := Equiv.ofBijective _ hbij with hπ
  have hκ : ∀ t, κ (π t) = kGU t := by
    intro t
    fin_cases t
    exacts [kc, kb, ka, ku, kw]
  have m0 : fvMap π hκ (fv kGU 0) = W.c := fv_ext rfl
  have m1 : fvMap π hκ (fv kGU 1) = W.b := fv_ext rfl
  have m2 : fvMap π hκ (fv kGU 2) = W.a := fv_ext rfl
  have m3 : fvMap π hκ (fv kGU 3) = u := fv_ext rfl
  have m4 : fvMap π hκ (fv kGU 4) = w := fv_ext rfl
  have n0 : psMap π hκ (pg kGU 0) = W.sc :=
    psMap_pg π hκ _ hsc.symm (slots_eq_one (Or.inl (by rw [hsc]; exact kc)))
  have n1 : psMap π hκ (pg kGU 1) = W.sb :=
    psMap_pg π hκ _ hsb.symm (slots_eq_one (Or.inl (by rw [hsb]; exact kb)))
  have n2 : psMap π hκ (pg kGU 2) = W.sa :=
    psMap_pg π hκ _ hsa.symm (slots_eq_one (Or.inl (by rw [hsa]; exact ka)))
  have n3 : psMap π hκ (pg kGU 3) = W.x :=
    psMap_pg π hκ _ hu (slots_eq_one (Or.inr (by rw [← hu]; exact ku)))
  have n4 : psMap π hκ (pg kGU 4) = W.y :=
    psMap_pg π hκ _ hw (slots_eq_one (Or.inl (by rw [← hw]; exact kw)))
  have t1 := tau_symm C tsb
  have t2 := tau_symm C hx
  have t3 := tau_symm C hy
  refine ⟨⟨kGU, repGU, 0⟩, by simp [repsA, repsA5], π, hκ, ?_,
    grad_eq_zero π hκ g hg order_kGU⟩
  refine eq_relabelK_of_agree π hκ repGU C (fun z => ?_) (fun z => ?_)
  · obtain ⟨c0, c1, c2, c3, c4, c5⟩ := repGU_tab
    rcases kGU_fields z with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [c0, c1, c2, c3, c4, c5, extFK_inl, extFK_inr, m0, m1, m2, m3, m4] <;>
      assumption
  · change C.1.2 _ = extPK π hκ (openTau witGU z)
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := tauGU_tab
    rcases kGU_slots z with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e0, e1, e2, e3, e4, e5, extPK_inl, extPK_inr, n0, n1, n2, n3, n4] <;>
      assumption

end QED.ChainProof.SetALink

end
