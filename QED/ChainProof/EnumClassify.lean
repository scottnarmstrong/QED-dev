/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumReps

/-!
# Every set (b) chain contraction is a relabelling of one of nine representatives

Helper for obligation O3-4 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53), by the path argument of
the Stage 1a design note (section 4.1), with no enumeration of permutations.

* `QED.ChainProof.Enum.ChainBody.witness_eq`: **the contraction determines the witness** (for
  every `n`). The open line follows the fermion pairing from `Ψ(x)`, `src 0` is the photon field of
  `a`, `dst i` is the photon partner of `src i`, and `src (i + 1)` is the insertion partner of
  `dst i` (the photon field of the bubble vertex paired with the vertex of `dst i`, or the other
  field of its `photonCt` vertex); induction along the chain.
* For `n = 2`, the vertices named by the witness are pairwise distinct
  (`vertexList_nodup_*`): the open line is a cycle of length four through `Ψ(x)` of the fermion
  pairing and a bubble a cycle of length two, so they are disjoint; a gauge vertex has one photon
  field and a `photonCt` vertex two, and the photon pairing is a fixed-point-free involution, so the
  walk does not return. They exhaust the vertices (the last clause of (C₁)).
* `QED.ChainProof.Enum.exists_rep_of_chainBody`: so the map from the vertices of the
  representative of the matching class (`QED.ChainProof.Enum.repsOf`) to the witness vertices is a
  bijection `π`, the kinds match, the relabelled representative satisfies (C₁) with the same
  witness, and since the witness determines the contraction (`ChainBody.eq`), `C` is the
  relabelled representative.
-/

@[expose] public section

namespace QED.ChainProof.Enum

open QED.WickModel QED.TwoLoop.Relabel

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### The contraction determines the witness -/

theorem ChainWitness.ext' {n : ℕ} {W W' : ChainWitness n κ} (ha : W.a = W'.a) (hb : W.b = W'.b)
    (hc : W.c = W'.c) (hsb : W.sb = W'.sb) (hsrc : W.src = W'.src) (hdst : W.dst = W'.dst) :
    W = W' := by
  rcases W with ⟨a, b, c, sb, src, dst⟩
  rcases W' with ⟨a', b', c', sb', src', dst'⟩
  simp only at ha hb hc hsb hsrc hdst
  subst ha hb hc hsb hsrc hdst
  rfl

/-- **The contraction determines the witness** of (C₁). -/
theorem ChainBody.witness_eq {n : ℕ} {C : Contraction 1 1 κ} {W W' : ChainWitness n κ}
    (h : ChainBody n C W) (h' : ChainBody n C W') : W = W' := by
  have ha : W.a = W'.a := Sum.inr_injective (h.s0a.symm.trans h'.s0a)
  have hb : W.b = W'.b := by
    have e := h.sab
    rw [ha, h'.sab] at e
    exact (Sum.inr_injective e).symm
  have hc : W.c = W'.c := by
    have e := h.sbc
    rw [hb, h'.sbc] at e
    exact (Sum.inr_injective e).symm
  have hsb : W.sb = W'.sb := Sum.inr_injective (h.tsb.symm.trans h'.tsb)
  have hdst_of : ∀ i, W.src i = W'.src i → W.dst i = W'.dst i := fun i hi => by
    have e := h.line i
    rw [hi, h'.line] at e
    exact (Sum.inr_injective e).symm
  have hsrc : ∀ i, W.src i = W'.src i := by
    intro i
    induction i using Fin.induction with
    | zero =>
      exact ps_eq_of_gauge (by rw [h.src0, h'.src0, ha]) (by rw [h.src0]; exact h.ka)
    | succ i ih =>
      have hd := hdst_of _ ih
      rcases h.ins i with ⟨k1, k2, -, u, w, hu, hw, huw, -⟩ | ⟨k1, hs, hne⟩
      · rcases h'.ins i with ⟨-, -, -, u', w', hu', hw', huw', -⟩ | ⟨k1', -, -⟩
        · have huu : u = u' := fv_ext (by rw [hu, hu', hd])
          subst huu
          have hww : w = w' := Sum.inr_injective (huw.symm.trans huw')
          subst hww
          exact ps_eq_of_gauge (hw.symm.trans hw') k2
        · rw [hd] at k1
          exact absurd (k1.symm.trans k1') (by decide)
      · rcases h'.ins i with ⟨k1', -, -, -⟩ | ⟨-, hs', hne'⟩
        · rw [hd] at k1
          exact absurd (k1.symm.trans k1') (by decide)
        · have hx : (W'.dst i.castSucc).1 = (W.src i.succ).1 := by rw [← hd, hs]
          have hy : (W'.src i.succ).1 = (W.src i.succ).1 := by rw [hs', ← hd, hs]
          rcases ps_eq_or_of_photonCt hx hy (Ne.symm hne') (by rw [hs]; exact k1) with e | e
          · exact absurd (e.trans hd.symm) hne
          · exact e
  exact ChainWitness.ext' ha hb hc hsb (funext hsrc) (funext fun i => hdst_of i (hsrc i))

/-! ### Distinctness -/

section Distinct

variable {n : ℕ} {C : Contraction 1 1 κ} {W : ChainWitness n κ}

theorem ne_of_kinds {x y : Fin N} (hx : κ x = .gauge) (hy : κ y = .photonCt) : x ≠ y := by
  rintro rfl
  rw [hx] at hy
  exact absurd hy (by decide)

theorem ChainBody.a_ne_b (h : ChainBody n C W) : W.a.1 ≠ W.b.1 := by
  intro e
  have e2 := h.sab
  rw [← fv_ext e] at e2
  exact Sum.inl_ne_inr (C.1.1.injective (h.s0a.trans e2.symm))

theorem ChainBody.b_ne_c (h : ChainBody n C W) : W.b.1 ≠ W.c.1 := by
  intro e
  have e2 := h.sbc
  rw [← fv_ext e] at e2
  exact h.a_ne_b (congrArg Subtype.val (Sum.inr_injective (C.1.1.injective (h.sab.trans e2.symm))))

theorem ChainBody.a_ne_c (h : ChainBody n C W) : W.a.1 ≠ W.c.1 := by
  intro e
  have e2 := h.sc0
  rw [← fv_ext e, h.sab] at e2
  exact Sum.inr_ne_inl e2

/-- A vertex of a bubble (a two-cycle of the fermion pairing) is not on the open line. -/
theorem ChainBody.bubble_ne (h : ChainBody n C W) {u w : Wick.FermionVertex κ}
    (huw : C.1.1 (.inr u) = .inr w) (hwu : C.1.1 (.inr w) = .inr u) :
    u.1 ≠ W.a.1 ∧ u.1 ≠ W.b.1 ∧ u.1 ≠ W.c.1 := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain rfl : u = W.a := fv_ext e
    have hw : w = W.b := Sum.inr_injective (huw.symm.trans h.sab)
    subst hw
    exact h.a_ne_c (congrArg Subtype.val (Sum.inr_injective (hwu.symm.trans h.sbc)))
  · obtain rfl : u = W.b := fv_ext e
    have hw : w = W.c := Sum.inr_injective (huw.symm.trans h.sbc)
    subst hw
    exact Sum.inr_ne_inl (hwu.symm.trans h.sc0)
  · obtain rfl : u = W.c := fv_ext e
    exact Sum.inr_ne_inl (huw.symm.trans h.sc0)

theorem ChainBody.tau_src (h : ChainBody n C W) {i j : Fin (n + 1)}
    (e : W.src i = W.src j) : W.dst i = W.dst j := by
  have e2 := h.line i
  rw [e, h.line j] at e2
  exact (Sum.inr_injective e2).symm

theorem ChainBody.src_ne_dst (h : ChainBody n C W) (i : Fin (n + 1)) : W.src i ≠ W.dst i := by
  intro e
  have e2 := h.line i
  rw [← e] at e2
  exact (C.2 _).2 e2

/-- The two photon fields of a `photonCt` insertion have complementary slot indices. -/
theorem ct_vals {d s : Wick.PhotonSlot κ} (hc : κ d.1 = .photonCt) (hs : s.1 = d.1) (hne : s ≠ d) :
    d.2.val < 2 ∧ s.2.val = 1 - d.2.val := by
  have h1 := ps_val_lt_two_of_photonCt d hc
  have h2 := ps_val_lt_two_of_photonCt s (by rw [hs]; exact hc)
  have h3 : s.2.val ≠ d.2.val := fun e => hne (ps_ext hs e)
  omega

end Distinct

/-! ### The representatives by vertex number -/

/-- A representative: its kind sequence, contraction and chain witness. -/
structure Rep (N : ℕ) where
  /-- the kind sequence -/
  kinds : Fin N → Wick.VertexKind
  /-- the contraction -/
  rep : Contraction 1 1 kinds
  /-- its chain witness -/
  wit : ChainWitness 2 kinds

/-- The representatives with seven vertices: bubble–bubble. -/
def reps7 : List (Rep 7) := [⟨kBB, repBB, wBB⟩]

/-- The representatives with six vertices: bubble–`δ₃` and `δ₃`–bubble, both slot pairings. -/
def reps6 : List (Rep 6) :=
  [⟨kBD, repBD 0, wBD 0⟩, ⟨kBD, repBD 1, wBD 1⟩, ⟨kDB, repDB 0, wDB 0⟩, ⟨kDB, repDB 1, wDB 1⟩]

/-- The representatives with five vertices: `δ₃`–`δ₃`, the four slot pairings. -/
def reps5 : List (Rep 5) :=
  [⟨kDD, repDD 0 0, wDD 0 0⟩, ⟨kDD, repDD 0 1, wDD 0 1⟩, ⟨kDD, repDD 1 0, wDD 1 0⟩,
    ⟨kDD, repDD 1 1, wDD 1 1⟩]

/-- The representatives with `N` vertices. -/
def repsOf : (N : ℕ) → List (Rep N)
  | 5 => reps5
  | 6 => reps6
  | 7 => reps7
  | _ => []

/-! ### Building the relabelling from the witness -/

/-- **From a bijection onto the witness vertices to a relabelling.** If `g` maps the vertices of
a representative `R` bijectively onto those of `κ`, preserving kinds, and sends the witness of
`R` to `W` (vertices by `g`, slot indices equal), then `C` is the relabelled representative. -/
theorem exists_rep_of_bij {M : ℕ} (R : Rep M) (hR : R ∈ repsOf M) (hrep : ChainBody 2 R.rep R.wit)
    {C : Contraction 1 1 κ} {W : ChainWitness 2 κ} (h : ChainBody 2 C W) (g : Fin M → Fin N)
    (hg : Function.Bijective g) (hκg : ∀ t, κ (g t) = R.kinds t)
    (ha : g R.wit.a.1 = W.a.1) (hb : g R.wit.b.1 = W.b.1) (hc : g R.wit.c.1 = W.c.1)
    (hsb1 : g R.wit.sb.1 = W.sb.1) (hsb2 : R.wit.sb.2.val = W.sb.2.val)
    (hs1 : ∀ i, g (R.wit.src i).1 = (W.src i).1) (hs2 : ∀ i, (R.wit.src i).2.val = (W.src i).2.val)
    (hd1 : ∀ i, g (R.wit.dst i).1 = (W.dst i).1)
    (hd2 : ∀ i, (R.wit.dst i).2.val = (W.dst i).2.val) :
    ∃ R ∈ repsOf N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep := by
  have hMN : M = N := by simpa using Fintype.card_of_bijective hg
  subst hMN
  refine ⟨R, hR, Equiv.ofBijective g hg, hκg, ?_⟩
  exact ((hrep.relabelK (Equiv.ofBijective g hg) hκg W ha hb hc hsb1 hsb2 hs1 hs2 hd1 hd2).eq
    h).symm

/-! ### The four shapes -/

section Shapes

variable {C : Contraction 1 1 κ} {W : ChainWitness 2 κ}

theorem surj_of_exh (h : ChainBody 2 C W) {M : ℕ} (g : Fin M → Fin N)
    (hA : ∃ t, g t = W.a.1) (hB : ∃ t, g t = W.b.1) (hC : ∃ t, g t = W.c.1)
    (hD0 : ∃ t, g t = (W.dst 0).1) (hS1 : ∃ t, g t = (W.src 1).1)
    (hD1 : ∃ t, g t = (W.dst 1).1) (hS2 : ∃ t, g t = (W.src 2).1) : Function.Surjective g := by
  intro x
  rcases h.exh x with rfl | rfl | rfl | ⟨i, e | e⟩
  · exact hA
  · exact hB
  · exact hC
  · fin_cases i
    · exact e ▸ hD0
    · exact e ▸ hD1
  · fin_cases i
    · exact e ▸ hS1
    · exact e ▸ hS2

theorem val_eq_zero_of_eq {s : Wick.PhotonSlot κ} {x : Fin N} (hs : s.1 = x) (hx : κ x = .gauge) :
    s.2.val = 0 := ps_val_eq_zero_of_gauge s (by rw [hs]; exact hx)

/-- **Bubble–bubble.** -/
theorem exists_rep_BB (h : ChainBody 2 C W) {u₀ w₀ u₁ w₁ : Wick.FermionVertex κ}
    (k₀ : κ (W.dst 0).1 = .gauge) (k₀' : κ (W.src 1).1 = .gauge) (ne₀ : (W.dst 0).1 ≠ (W.src 1).1)
    (hu₀ : u₀.1 = (W.dst 0).1) (hw₀ : w₀.1 = (W.src 1).1)
    (huw₀ : C.1.1 (.inr u₀) = .inr w₀) (hwu₀ : C.1.1 (.inr w₀) = .inr u₀)
    (k₁ : κ (W.dst 1).1 = .gauge) (k₁' : κ (W.src 2).1 = .gauge) (ne₁ : (W.dst 1).1 ≠ (W.src 2).1)
    (hu₁ : u₁.1 = (W.dst 1).1) (hw₁ : w₁.1 = (W.src 2).1)
    (huw₁ : C.1.1 (.inr u₁) = .inr w₁) (hwu₁ : C.1.1 (.inr w₁) = .inr u₁) :
    ∃ R ∈ repsOf N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep := by
  set g : Fin 7 → Fin N :=
    ![W.c.1, W.b.1, W.a.1, (W.dst 0).1, (W.src 1).1, (W.dst 1).1, (W.src 2).1] with hg
  obtain ⟨a0, b0, c0⟩ := h.bubble_ne huw₀ hwu₀
  obtain ⟨a0', b0', c0'⟩ := h.bubble_ne hwu₀ huw₀
  obtain ⟨a1, b1, c1⟩ := h.bubble_ne huw₁ hwu₁
  obtain ⟨a1', b1', c1'⟩ := h.bubble_ne hwu₁ huw₁
  rw [hu₀] at a0 b0 c0
  rw [hw₀] at a0' b0' c0'
  rw [hu₁] at a1 b1 c1
  rw [hw₁] at a1' b1' c1'
  have hab := h.a_ne_b
  have hbc := h.b_ne_c
  have hac := h.a_ne_c
  -- the photon walk does not return
  have p1 : (W.dst 0).1 ≠ (W.dst 1).1 := fun e => by
    have : W.dst 1 = W.dst 0 := ps_eq_of_gauge e.symm k₁
    have hs : W.src 1 = W.src 0 := by
      have l1 := h.line 1
      have l0 := h.line 0
      rw [this, ← l0] at l1
      exact Sum.inr_injective (C.1.2.injective l1)
    exact a0' (by rw [hs, h.src0])
  have p2 : (W.src 1).1 ≠ (W.dst 1).1 := fun e =>
    h.src_ne_dst 1 (ps_eq_of_gauge e k₀')
  have p3 : (W.dst 0).1 ≠ (W.src 2).1 := fun e => by
    have hs : W.src 2 = W.dst 0 := ps_eq_of_gauge e.symm k₁'
    have l2 := h.line 2
    rw [hs, tau_symm C (h.line 0)] at l2
    exact hac (by
      have e3 : W.src 0 = W.dst 2 := Sum.inr_injective l2
      rw [← h.src0, e3]
      exact h.dstn)
  have p4 : (W.src 1).1 ≠ (W.src 2).1 := fun e => by
    have hs : W.src 2 = W.src 1 := ps_eq_of_gauge e.symm k₁'
    have hd := h.tau_src hs
    exact c1 (by rw [← hd]; exact h.dstn)
  have hinj : Function.Injective g := by
    rw [← List.nodup_ofFn]
    simp only [hg, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
      not_or, not_false_eq_true]
    refine ⟨⟨hbc.symm, hac.symm, Ne.symm c0, Ne.symm c0', Ne.symm c1, Ne.symm c1'⟩,
      ⟨hab.symm, Ne.symm b0, Ne.symm b0', Ne.symm b1, Ne.symm b1'⟩,
      ⟨Ne.symm a0, Ne.symm a0', Ne.symm a1, Ne.symm a1'⟩, ⟨ne₀, p1, p3⟩, ⟨p2, p4⟩, ne₁⟩
  have hsurj : Function.Surjective g :=
    surj_of_exh h g ⟨2, rfl⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨3, rfl⟩ ⟨4, rfl⟩ ⟨5, rfl⟩ ⟨6, rfl⟩
  refine exists_rep_of_bij ⟨kBB, repBB, wBB⟩ (by simp [repsOf, reps7]) chainBody_repBB h g
    ⟨hinj, hsurj⟩ ?_ rfl rfl rfl (by rw [h.sbv]; rfl) ?_ ?_ ?_ ?_ ?_
  · intro t
    fin_cases t
    exacts [h.kc, h.kb, h.ka, k₀, k₀', k₁, k₁']
  · exact (val_eq_zero_of_eq h.sbv h.kb).symm
  · intro i
    fin_cases i
    exacts [h.src0.symm, rfl, rfl]
  · intro i
    fin_cases i
    exacts [(val_eq_zero_of_eq h.src0 h.ka).symm, (val_eq_zero_of_eq rfl k₀').symm,
      (val_eq_zero_of_eq rfl k₁').symm]
  · intro i
    fin_cases i
    exacts [rfl, rfl, h.dstn.symm]
  · intro i
    fin_cases i
    exacts [(val_eq_zero_of_eq rfl k₀).symm, (val_eq_zero_of_eq rfl k₁).symm,
      (val_eq_zero_of_eq h.dstn h.kc).symm]

theorem rev_val (s : Fin 2) : s.rev.val = 1 - s.val := by
  fin_cases s <;> rfl

theorem mem_BD (s : Fin 2) : (⟨kBD, repBD s, wBD s⟩ : Rep 6) ∈ repsOf 6 := by
  fin_cases s <;> simp [repsOf, reps6]

theorem mem_DB (s : Fin 2) : (⟨kDB, repDB s, wDB s⟩ : Rep 6) ∈ repsOf 6 := by
  fin_cases s <;> simp [repsOf, reps6]

theorem mem_DD (s₀ s₁ : Fin 2) : (⟨kDD, repDD s₀ s₁, wDD s₀ s₁⟩ : Rep 5) ∈ repsOf 5 := by
  fin_cases s₀ <;> fin_cases s₁ <;> simp [repsOf, reps5]

/-- **Bubble–`δ₃`.** -/
theorem exists_rep_BD (h : ChainBody 2 C W) {u₀ w₀ : Wick.FermionVertex κ}
    (k₀ : κ (W.dst 0).1 = .gauge) (k₀' : κ (W.src 1).1 = .gauge) (ne₀ : (W.dst 0).1 ≠ (W.src 1).1)
    (hu₀ : u₀.1 = (W.dst 0).1) (hw₀ : w₀.1 = (W.src 1).1)
    (huw₀ : C.1.1 (.inr u₀) = .inr w₀) (hwu₀ : C.1.1 (.inr w₀) = .inr u₀)
    (k₁ : κ (W.dst 1).1 = .photonCt) (hs₁ : (W.src 2).1 = (W.dst 1).1)
    (hne₁ : W.src 2 ≠ W.dst 1) :
    ∃ R ∈ repsOf N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep := by
  set g : Fin 6 → Fin N :=
    ![W.c.1, W.b.1, W.a.1, (W.dst 0).1, (W.src 1).1, (W.dst 1).1] with hg
  obtain ⟨a0, b0, c0⟩ := h.bubble_ne huw₀ hwu₀
  obtain ⟨a0', b0', c0'⟩ := h.bubble_ne hwu₀ huw₀
  rw [hu₀] at a0 b0 c0
  rw [hw₀] at a0' b0' c0'
  have hab := h.a_ne_b
  have hbc := h.b_ne_c
  have hac := h.a_ne_c
  have hinj : Function.Injective g := by
    rw [← List.nodup_ofFn]
    simp only [hg, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
      not_or, not_false_eq_true]
    refine ⟨⟨hbc.symm, hac.symm, Ne.symm c0, Ne.symm c0', ne_of_kinds h.kc k₁⟩,
      ⟨hab.symm, Ne.symm b0, Ne.symm b0', ne_of_kinds h.kb k₁⟩,
      ⟨Ne.symm a0, Ne.symm a0', ne_of_kinds h.ka k₁⟩, ⟨ne₀, ne_of_kinds k₀ k₁⟩,
      ne_of_kinds k₀' k₁⟩
  have hsurj : Function.Surjective g :=
    surj_of_exh h g ⟨2, rfl⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨3, rfl⟩ ⟨4, rfl⟩ ⟨5, rfl⟩ ⟨5, hs₁.symm⟩
  obtain ⟨hlt, hval⟩ := ct_vals k₁ hs₁ hne₁
  obtain ⟨s, hsv⟩ : ∃ s : Fin 2, s.val = (W.dst 1).2.val := ⟨⟨_, hlt⟩, rfl⟩
  refine exists_rep_of_bij ⟨kBD, repBD s, wBD s⟩ (mem_BD s) (chainBody_repBD s) h g
    ⟨hinj, hsurj⟩ ?_ rfl rfl rfl (by rw [h.sbv]; rfl) ?_ ?_ ?_ ?_ ?_
  · intro t
    fin_cases t
    exacts [h.kc, h.kb, h.ka, k₀, k₀', k₁]
  · exact (val_eq_zero_of_eq h.sbv h.kb).symm
  · intro i
    fin_cases i
    exacts [h.src0.symm, rfl, hs₁.symm]
  · intro i
    fin_cases i
    · exact (val_eq_zero_of_eq h.src0 h.ka).symm
    · exact (val_eq_zero_of_eq rfl k₀').symm
    · show s.rev.val = _
      rw [rev_val, hsv]
      exact hval.symm
  · intro i
    fin_cases i
    exacts [rfl, rfl, h.dstn.symm]
  · intro i
    fin_cases i
    · exact (val_eq_zero_of_eq rfl k₀).symm
    · exact hsv
    · exact (val_eq_zero_of_eq h.dstn h.kc).symm

/-- **`δ₃`–bubble.** -/
theorem exists_rep_DB (h : ChainBody 2 C W)
    (k₀ : κ (W.dst 0).1 = .photonCt) (hs₀ : (W.src 1).1 = (W.dst 0).1)
    (hne₀ : W.src 1 ≠ W.dst 0) {u₁ w₁ : Wick.FermionVertex κ}
    (k₁ : κ (W.dst 1).1 = .gauge) (k₁' : κ (W.src 2).1 = .gauge) (ne₁ : (W.dst 1).1 ≠ (W.src 2).1)
    (hu₁ : u₁.1 = (W.dst 1).1) (hw₁ : w₁.1 = (W.src 2).1)
    (huw₁ : C.1.1 (.inr u₁) = .inr w₁) (hwu₁ : C.1.1 (.inr w₁) = .inr u₁) :
    ∃ R ∈ repsOf N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep := by
  set g : Fin 6 → Fin N :=
    ![W.c.1, W.b.1, W.a.1, (W.dst 0).1, (W.dst 1).1, (W.src 2).1] with hg
  obtain ⟨a1, b1, c1⟩ := h.bubble_ne huw₁ hwu₁
  obtain ⟨a1', b1', c1'⟩ := h.bubble_ne hwu₁ huw₁
  rw [hu₁] at a1 b1 c1
  rw [hw₁] at a1' b1' c1'
  have hab := h.a_ne_b
  have hbc := h.b_ne_c
  have hac := h.a_ne_c
  have hinj : Function.Injective g := by
    rw [← List.nodup_ofFn]
    simp only [hg, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
      not_or, not_false_eq_true]
    refine ⟨⟨hbc.symm, hac.symm, ne_of_kinds h.kc k₀, Ne.symm c1, Ne.symm c1'⟩,
      ⟨hab.symm, ne_of_kinds h.kb k₀, Ne.symm b1, Ne.symm b1'⟩,
      ⟨ne_of_kinds h.ka k₀, Ne.symm a1, Ne.symm a1'⟩,
      ⟨(ne_of_kinds k₁ k₀).symm, (ne_of_kinds k₁' k₀).symm⟩, ne₁⟩
  have hsurj : Function.Surjective g :=
    surj_of_exh h g ⟨2, rfl⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨3, rfl⟩ ⟨3, hs₀.symm⟩ ⟨4, rfl⟩ ⟨5, rfl⟩
  obtain ⟨hlt, hval⟩ := ct_vals k₀ hs₀ hne₀
  obtain ⟨s, hsv⟩ : ∃ s : Fin 2, s.val = (W.dst 0).2.val := ⟨⟨_, hlt⟩, rfl⟩
  refine exists_rep_of_bij ⟨kDB, repDB s, wDB s⟩ (mem_DB s) (chainBody_repDB s) h g
    ⟨hinj, hsurj⟩ ?_ rfl rfl rfl (by rw [h.sbv]; rfl) ?_ ?_ ?_ ?_ ?_
  · intro t
    fin_cases t
    exacts [h.kc, h.kb, h.ka, k₀, k₁, k₁']
  · exact (val_eq_zero_of_eq h.sbv h.kb).symm
  · intro i
    fin_cases i
    exacts [h.src0.symm, hs₀.symm, rfl]
  · intro i
    fin_cases i
    · exact (val_eq_zero_of_eq h.src0 h.ka).symm
    · show s.rev.val = _
      rw [rev_val, hsv]
      exact hval.symm
    · exact (val_eq_zero_of_eq rfl k₁').symm
  · intro i
    fin_cases i
    exacts [rfl, rfl, h.dstn.symm]
  · intro i
    fin_cases i
    · exact hsv
    · exact (val_eq_zero_of_eq rfl k₁).symm
    · exact (val_eq_zero_of_eq h.dstn h.kc).symm

/-- **`δ₃`–`δ₃`.** -/
theorem exists_rep_DD (h : ChainBody 2 C W)
    (k₀ : κ (W.dst 0).1 = .photonCt) (hs₀ : (W.src 1).1 = (W.dst 0).1)
    (hne₀ : W.src 1 ≠ W.dst 0)
    (k₁ : κ (W.dst 1).1 = .photonCt) (hs₁ : (W.src 2).1 = (W.dst 1).1)
    (hne₁ : W.src 2 ≠ W.dst 1) :
    ∃ R ∈ repsOf N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep := by
  set g : Fin 5 → Fin N := ![W.c.1, W.b.1, W.a.1, (W.dst 0).1, (W.dst 1).1] with hg
  have hab := h.a_ne_b
  have hbc := h.b_ne_c
  have hac := h.a_ne_c
  have p : (W.dst 0).1 ≠ (W.dst 1).1 := fun e => by
    rcases ps_eq_or_of_photonCt e (hs₀.trans e) (Ne.symm hne₀) k₁ with e' | e'
    · have l1 := h.line 1
      rw [e', ← h.line 0] at l1
      have hs : W.src 1 = W.src 0 := Sum.inr_injective (C.1.2.injective l1)
      have k := h.ka
      rw [← h.src0, ← hs, hs₀] at k
      rw [k] at k₀
      exact absurd k₀ (by decide)
    · exact h.src_ne_dst 1 e'.symm
  have hinj : Function.Injective g := by
    rw [← List.nodup_ofFn]
    simp only [hg, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
      not_or, not_false_eq_true]
    exact ⟨⟨hbc.symm, hac.symm, ne_of_kinds h.kc k₀, ne_of_kinds h.kc k₁⟩,
      ⟨hab.symm, ne_of_kinds h.kb k₀, ne_of_kinds h.kb k₁⟩,
      ⟨ne_of_kinds h.ka k₀, ne_of_kinds h.ka k₁⟩, p⟩
  have hsurj : Function.Surjective g :=
    surj_of_exh h g ⟨2, rfl⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨3, rfl⟩ ⟨3, hs₀.symm⟩ ⟨4, rfl⟩ ⟨4, hs₁.symm⟩
  obtain ⟨hlt₀, hval₀⟩ := ct_vals k₀ hs₀ hne₀
  obtain ⟨hlt₁, hval₁⟩ := ct_vals k₁ hs₁ hne₁
  obtain ⟨s₀, hsv₀⟩ : ∃ s : Fin 2, s.val = (W.dst 0).2.val := ⟨⟨_, hlt₀⟩, rfl⟩
  obtain ⟨s₁, hsv₁⟩ : ∃ s : Fin 2, s.val = (W.dst 1).2.val := ⟨⟨_, hlt₁⟩, rfl⟩
  refine exists_rep_of_bij ⟨kDD, repDD s₀ s₁, wDD s₀ s₁⟩ (mem_DD s₀ s₁) (chainBody_repDD s₀ s₁)
    h g ⟨hinj, hsurj⟩ ?_ rfl rfl rfl (by rw [h.sbv]; rfl) ?_ ?_ ?_ ?_ ?_
  · intro t
    fin_cases t
    exacts [h.kc, h.kb, h.ka, k₀, k₁]
  · exact (val_eq_zero_of_eq h.sbv h.kb).symm
  · intro i
    fin_cases i
    exacts [h.src0.symm, hs₀.symm, hs₁.symm]
  · intro i
    fin_cases i
    · exact (val_eq_zero_of_eq h.src0 h.ka).symm
    · show s₀.rev.val = _
      rw [rev_val, hsv₀]
      exact hval₀.symm
    · show s₁.rev.val = _
      rw [rev_val, hsv₁]
      exact hval₁.symm
  · intro i
    fin_cases i
    exacts [rfl, rfl, h.dstn.symm]
  · intro i
    fin_cases i
    · exact hsv₀
    · exact hsv₁
    · exact (val_eq_zero_of_eq h.dstn h.kc).symm

end Shapes

/-! ### The classification -/

/-- **Every contraction satisfying the body of (C₁) with `n = 2` is a relabelling of one of the
nine representatives** (obligation O3-4), the relabelling built from the witness. -/
theorem exists_rep_of_chainBody {C : Contraction 1 1 κ} {W : ChainWitness 2 κ}
    (h : ChainBody 2 C W) :
    ∃ R ∈ repsOf N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep := by
  have i0 : InsClause C (W.dst 0) (W.src 1) := h.ins 0
  have i1 : InsClause C (W.dst 1) (W.src 2) := h.ins 1
  rcases i0 with ⟨k₀, k₀', ne₀, u₀, w₀, hu₀, hw₀, huw₀, hwu₀⟩ | ⟨k₀, hs₀, hne₀⟩ <;>
    rcases i1 with ⟨k₁, k₁', ne₁, u₁, w₁, hu₁, hw₁, huw₁, hwu₁⟩ | ⟨k₁, hs₁, hne₁⟩
  · exact exists_rep_BB h k₀ k₀' ne₀ hu₀ hw₀ huw₀ hwu₀ k₁ k₁' ne₁ hu₁ hw₁ huw₁ hwu₁
  · exact exists_rep_BD h k₀ k₀' ne₀ hu₀ hw₀ huw₀ hwu₀ k₁ hs₁ hne₁
  · exact exists_rep_DB h k₀ hs₀ hne₀ k₁ k₁' ne₁ hu₁ hw₁ huw₁ hwu₁
  · exact exists_rep_DD h k₀ hs₀ hne₀ k₁ hs₁ hne₁

/-- **The set (b) chain contractions are relabellings of the nine representatives**
(obligation O3-4): every contraction `C` with `IsVPChain 2 C` (one-particle irreducibility is
not assumed) is `relabelK π hκ R.rep` for a representative `R` with the same number of vertices
and a relabelling `π`. -/
theorem exists_rep {C : Contraction 1 1 κ} (hC : QED.VPChain.IsVPChain 2 C) :
    ∃ R ∈ repsOf N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep := by
  obtain ⟨W, hW⟩ := (isVPChain_iff 2 C).mp hC
  exact exists_rep_of_chainBody hW

end QED.ChainProof.Enum

end
