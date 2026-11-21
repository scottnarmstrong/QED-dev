/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkShape
public import QED.ChainProof.SetALinkLoop

/-!
# The set (a) classification: the loop classes, and the full classification

Helper for the Phase 5 Stage 3a enumeration (decision D-58). A contraction satisfying the loop
branch of (A₁) `QED.ThreeLoop.IsSetA` at graded order `7` is a relabelling of one of the seven
loop representatives `repVA`, …, `repGU` of `QED/ChainProof/SetALinkReps.lean`.

The argument walks around the loop from the vertex `u` of the field `x`: `u, σ u, σ² u, …`. The
fields `x`, `y` are distinct, so `u ≠ w`, and `u`, `w` are `gauge` or `gaugeCt` vertices. The open
line has order `3` and every vertex has order at least `1`, so the walk returns to `u` after `2`,
`3` or `4` steps. A `gauge` or `gaugeCt` vertex `p` of the loop other than `u`, `w` has its photon
field paired with the field of a fourth loop vertex (`exists_slot_partner`). Hence:
* a loop `u ⇄ w`: one of `u`, `w` is a level-`0` `gaugeCt` vertex (`GW`, `GU`);
* a loop of three vertices: the third is a `fermionCt` vertex, `u` and `w` are `gauge` (`FA`,
  `FB`);
* a loop of four vertices: all are `gauge` and the two other than `u`, `w` are joined by a photon
  (`VA`, `VB`, `VC` by the position of `w`).

## Main statements

* `QED.ChainProof.SetALink.exists_rep_setA_loop`: the loop branch.
* `QED.ChainProof.SetALink.exists_rep_setA`: **the classification.** Every graded contraction of
  graded order `7` satisfying (A₁) is a relabelling of one of the nine representatives `repsA N`,
  with its grading.
-/

@[expose] public section

namespace QED.ChainProof.SetALink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum QED.GradedProof.VP2

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Kinds and orders -/

theorem order_pos (k : Wick.VertexKind) : 1 ≤ k.order := by
  cases k <;> decide

theorem order_gauge : Wick.VertexKind.gauge.order = 1 := rfl

theorem order_gaugeCt : Wick.VertexKind.gaugeCt.order = 3 := rfl

theorem order_fermionCt : Wick.VertexKind.fermionCt.order = 2 := rfl

theorem eq_gauge_of_order {k : Wick.VertexKind} (h : k.order ≤ 1) : k = .gauge := by
  cases k <;> first | rfl | (simp [Wick.VertexKind.order] at h)

/-- A fermion vertex carrying a photon field is a `gauge` or `gaugeCt` vertex. -/
theorem kind_of_slot {v : Wick.FermionVertex κ} {s : Wick.PhotonSlot κ} (h : v.1 = s.1) :
    κ v.1 = .gauge ∨ κ v.1 = .gaugeCt := by
  have hs : 0 < (κ s.1).photonSlots := lt_of_le_of_lt (Nat.zero_le _) s.2.isLt
  rw [← h] at hs
  have hv := v.2
  generalize κ v.1 = k at hs hv ⊢
  cases k <;> simp_all [Wick.VertexKind.photonSlots]

theorem kind_fv (v : Wick.FermionVertex κ) :
    κ v.1 = .gauge ∨ κ v.1 = .gaugeCt ∨ κ v.1 = .fermionCt := by
  have hv := v.2
  generalize κ v.1 = k at hv ⊢
  cases k <;> simp_all

theorem ps_eq_of_one {s s' : Wick.PhotonSlot κ} (h : s.1 = s'.1)
    (h1 : (κ s.1).photonSlots = 1) : s = s' := by
  refine ps_ext h ?_
  have a := s.2.isLt
  have b := s'.2.isLt
  have h1' : (κ s'.1).photonSlots = 1 := by rw [← h]; exact h1
  omega

theorem exists_slot {t : Fin N} (h : κ t = .gauge ∨ κ t = .gaugeCt) :
    ∃ s : Wick.PhotonSlot κ, s.1 = t :=
  ⟨⟨t, ⟨0, by rw [slots_eq_one h]; exact Nat.one_pos⟩⟩, rfl⟩

theorem sum_order_le {M : ℕ} {f : Fin M → Fin N} (hbij : Function.Bijective f)
    {g : Graded.Grading κ} (hg : Graded.gradedOrder κ g = 7) : ∑ i, (κ (f i)).order ≤ 7 := by
  rw [hbij.sum_comp (fun t => (κ t).order)]
  rw [gradedOrder_eq] at hg
  omega

theorem gradedOrder_of_gauge {M : ℕ} {f : Fin M → Fin N} (hbij : Function.Bijective f)
    (hall : ∀ i, κ (f i) = .gauge) (g : Graded.Grading κ) : Graded.gradedOrder κ g = M := by
  have ht : ∀ t, κ t = .gauge := fun t => by
    obtain ⟨i, rfl⟩ := hbij.2 t
    exact hall i
  have hct : ∑ t : Graded.CtVertex κ, 2 * g t = 0 :=
    Finset.sum_eq_zero fun t _ => absurd (ht t.1) t.2
  rw [gradedOrder_eq, hct, ← hbij.sum_comp (fun t => (κ t).order)]
  simp [hall, Wick.VertexKind.order]

theorem card_le_seven {M : ℕ} {f : Fin M → Fin N} (hinj : Function.Injective f)
    {g : Graded.Grading κ} (hg : Graded.gradedOrder κ g = 7) : M ≤ 7 := by
  have h1 : M ≤ N := by simpa using Fintype.card_le_of_injective f hinj
  have h2 : ∑ _t : Fin N, 1 ≤ ∑ t, (κ t).order :=
    Finset.sum_le_sum fun t _ => order_pos (κ t)
  rw [gradedOrder_eq] at hg
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h2
  omega

theorem injective_of_lt {α : Type*} {M : ℕ} {f : Fin M → α}
    (h : ∀ i j : Fin M, i < j → f i ≠ f j) : Function.Injective f := by
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd hij (h i j hlt)
  · exact heq
  · exact absurd hij.symm (h j i hgt)

/-- Injectivity of an explicit vector of pairwise distinct entries, from hypotheses in context. -/
local macro "vec_inj" : tactic =>
  `(tactic| (refine injective_of_lt fun i j hij => ?_
             fin_cases i <;> fin_cases j <;>
               first | exact absurd hij (by decide) | assumption | exact Ne.symm (by assumption)))

/-! ### The loop -/

section Loop

variable {C : Contraction 1 1 κ} {W : SetAWitness κ} {u w : Wick.FermionVertex κ}

theorem sameCycle_of_eq {σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ)} {p q}
    (h : σ p = q) : σ.SameCycle p q :=
  ⟨1, by simpa using h⟩

/-- A loop vertex is not on the open line. -/
theorem ne_open (h : OpenA C W) (hsep : ¬ (C.1.1).SameCycle (.inl 0) (.inr u))
    {v : Wick.FermionVertex κ} (hv : (C.1.1).SameCycle (.inr u) (.inr v)) :
    v.1 ≠ W.a.1 ∧ v.1 ≠ W.b.1 ∧ v.1 ≠ W.c.1 := by
  have ha := sameCycle_of_eq h.s0a
  have hb := ha.trans (sameCycle_of_eq h.sab)
  have hc := hb.trans (sameCycle_of_eq h.sbc)
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [fv_ext e] at hv
    exact hsep (ha.trans hv.symm)
  · rw [fv_ext e] at hv
    exact hsep (hb.trans hv.symm)
  · rw [fv_ext e] at hv
    exact hsep (hc.trans hv.symm)

/-- **The photon slot argument.** The photon field of a loop vertex `p ≠ u, w` is paired with
the photon field of a loop vertex `q ≠ u, w, p`. -/
theorem exists_slot_partner (h : OpenA C W) (hsep : ¬ (C.1.1).SameCycle (.inl 0) (.inr u))
    (hu : u.1 = W.x.1) (hw : w.1 = W.y.1)
    (hexh : ∀ t : Fin N, t = W.a.1 ∨ t = W.b.1 ∨ t = W.c.1 ∨
      ∃ v : Wick.FermionVertex κ, v.1 = t ∧ (C.1.1).SameCycle (.inr u) (.inr v))
    {p : Wick.FermionVertex κ} (hp : (C.1.1).SameCycle (.inr u) (.inr p)) (hpu : p.1 ≠ u.1)
    (hpw : p.1 ≠ w.1) {sp : Wick.PhotonSlot κ} (hsp : sp.1 = p.1) :
    ∃ s' : Wick.PhotonSlot κ, C.1.2 (.inr sp) = .inr s' ∧ ∃ q : Wick.FermionVertex κ,
      q.1 = s'.1 ∧ (C.1.1).SameCycle (.inr u) (.inr q) ∧ q.1 ≠ u.1 ∧ q.1 ≠ w.1 ∧
        q.1 ≠ p.1 := by
  obtain ⟨hpa, hpb, hpc⟩ := ne_open h hsep hp
  have one : ∀ {s s' : Wick.PhotonSlot κ}, s.1 = s'.1 →
      (κ s.1 = .gauge ∨ κ s.1 = .gaugeCt) → s = s' := fun e k => ps_eq_of_one e (slots_eq_one k)
  rcases e : C.1.2 (.inr sp) with j | s'
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    have := (tau_symm C e).symm.trans h.tsb
    exact absurd (by rw [← h.hsb, ← Sum.inr_injective this, hsp]) hpb
  refine ⟨s', rfl, ?_⟩
  have e' := tau_symm C e
  rcases hexh s'.1 with hq | hq | hq | ⟨q, hq, hqc⟩
  · have : s' = W.sa := one (hq.trans h.hsa.symm) (Or.inl (hq ▸ h.ka))
    rw [this, h.hx] at e'
    exact absurd (by rw [hu, Sum.inr_injective e', hsp]) hpu
  · have : s' = W.sb := one (hq.trans h.hsb.symm) (Or.inl (hq ▸ h.kb))
    rw [this, tau_symm C h.tsb] at e'
    exact absurd e' (by simp)
  · have : s' = W.sc := one (hq.trans h.hsc.symm) (Or.inl (hq ▸ h.kc))
    rw [this, h.hy] at e'
    exact absurd (by rw [hw, Sum.inr_injective e', hsp]) hpw
  refine ⟨q, hq, hqc, fun equ => ?_, fun eqw => ?_, fun eqp => ?_⟩
  · have ku := kind_of_slot hu
    have : s' = W.x := one (hq.symm.trans (equ.trans hu)) (by rw [← hq, equ]; exact ku)
    rw [this, tau_symm C h.hx] at e'
    exact absurd (by rw [← h.hsa, Sum.inr_injective e', hsp]) hpa
  · have kw := kind_of_slot hw
    have : s' = W.y := one (hq.symm.trans (eqw.trans hw)) (by rw [← hq, eqw]; exact kw)
    rw [this, tau_symm C h.hy] at e'
    exact absurd (by rw [← h.hsc, Sum.inr_injective e', hsp]) hpc
  · have kp := kind_of_slot hsp.symm
    have : s' = sp := one (hq.symm.trans (eqp.trans hsp.symm)) (by rw [← hq, eqp]; exact kp)
    rw [this] at e
    exact (C.2 _).2 e

theorem fst_eq_of_step {C : Contraction 1 1 κ} {p q p' q' : Wick.FermionVertex κ}
    (e : C.1.1 (.inr p) = .inr q) (e' : C.1.1 (.inr p') = .inr q') (hq : q.1 = q'.1) :
    p.1 = p'.1 := by
  have := C.1.1.injective (by rw [e, e', fv_ext hq] : C.1.1 (.inr p) = C.1.1 (.inr p'))
  rw [Sum.inr_injective this]

/-- **The loop branch of the classification.** -/
theorem exists_rep_setA_loop (h : OpenA C W) (hu : u.1 = W.x.1) (hw : w.1 = W.y.1)
    (hsep' : ∀ i : Fin 1, ¬ (C.1.1).SameCycle (.inl i) (.inr u))
    (huw : (C.1.1).SameCycle (.inr u) (.inr w))
    (hexh : ∀ t : Fin N, t = W.a.1 ∨ t = W.b.1 ∨ t = W.c.1 ∨
      ∃ v : Wick.FermionVertex κ, v.1 = t ∧ (C.1.1).SameCycle (.inr u) (.inr v))
    (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7) :
    ∃ R ∈ repsA N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  have hsep := hsep' 0
  obtain ⟨hab, hbc, hac⟩ := open_ne h.s0a h.sab h.sbc h.sc0
  have ka := h.ka
  have kb := h.kb
  have kc := h.kc
  have ku := kind_of_slot hu
  have kw := kind_of_slot hw
  have hxy : W.x ≠ W.y := by
    intro e
    have h1 := tau_symm C h.hx
    have h2 := tau_symm C h.hy
    rw [e] at h1
    have : W.sa = W.sc := Sum.inr_injective (h1.symm.trans h2)
    exact hac (by rw [← h.hsa, ← h.hsc, this])
  have huw1 : u.1 ≠ w.1 := fun e =>
    hxy (ps_eq_of_one (by rw [← hu, ← hw, e]) (by rw [← hu]; exact slots_eq_one ku))
  have nop : ∀ {v : Wick.FermionVertex κ}, (C.1.1).SameCycle (.inr u) (.inr v) →
      v.1 ≠ W.a.1 ∧ v.1 ≠ W.b.1 ∧ v.1 ≠ W.c.1 := fun hv => ne_open h hsep hv
  obtain ⟨hua, hub, huc⟩ := nop (Equiv.Perm.SameCycle.refl _ _)
  obtain ⟨hwa, hwb, hwc⟩ := nop huw
  have part : ∀ {p : Wick.FermionVertex κ}, (C.1.1).SameCycle (.inr u) (.inr p) → p.1 ≠ u.1 →
      p.1 ≠ w.1 → ∀ {sp : Wick.PhotonSlot κ}, sp.1 = p.1 → ∃ s' : Wick.PhotonSlot κ,
        C.1.2 (.inr sp) = .inr s' ∧ ∃ q : Wick.FermionVertex κ, q.1 = s'.1 ∧
          (C.1.1).SameCycle (.inr u) (.inr q) ∧ q.1 ≠ u.1 ∧ q.1 ≠ w.1 ∧ q.1 ≠ p.1 :=
    fun hp hpu hpw _ hsp => exists_slot_partner h hsep hu hw hexh hp hpu hpw hsp
  -- the first step
  obtain ⟨u₁, l0, c1⟩ := loop_step C hsep (Equiv.Perm.SameCycle.refl _ _)
  obtain ⟨h1a, h1b, h1c⟩ := nop c1
  have hu1 : u₁.1 ≠ u.1 := by
    intro e
    rw [fv_ext e] at l0
    have := mem_of_sameCycle_of_mapsTo (T := {Sum.inr u}) (by simp [l0]) (by simp) huw
    simp only [Finset.mem_singleton, Sum.inr.injEq] at this
    exact huw1 (by rw [this])
  obtain ⟨u₂, l1, c2⟩ := loop_step C hsep c1
  obtain ⟨h2a, h2b, h2c⟩ := nop c2
  by_cases e2 : u₂.1 = u.1
  · -- the loop `u ⇄ w`
    rw [fv_ext e2] at l1
    have hmem : ∀ v, (C.1.1).SameCycle (.inr u) (.inr v) → v = u ∨ v = u₁ := fun v hv => by
      simpa using mem_of_sameCycle_of_mapsTo (T := {Sum.inr u, Sum.inr u₁}) (by simp [l0, l1])
        (by simp) hv
    have hw1 : w = u₁ := (hmem w huw).resolve_left fun e => huw1 (by rw [e])
    rw [← hw1] at l0 l1 hmem
    have hinj : Function.Injective ![W.c.1, W.b.1, W.a.1, u.1, w.1] := by vec_inj
    have hsurj : Function.Surjective ![W.c.1, W.b.1, W.a.1, u.1, w.1] := by
      intro t
      rcases hexh t with rfl | rfl | rfl | ⟨v, rfl, hv⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · rcases hmem v hv with rfl | rfl
        · exact ⟨3, rfl⟩
        · exact ⟨4, rfl⟩
    have hbij : Function.Bijective ![W.c.1, W.b.1, W.a.1, u.1, w.1] := ⟨hinj, hsurj⟩
    have ho := sum_order_le hbij hg
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, ka, kb, kc, order_gauge] at ho
    rcases ku with ku | ku <;> rcases kw with kw | kw
    · have := gradedOrder_of_gauge hbij (fun i => by fin_cases i <;> assumption) g
      omega
    · exact exists_rep_GW h hu hw ku kw l0 l1 hinj hsurj g hg
    · exact exists_rep_GU h hu hw ku kw l0 l1 hinj hsurj g hg
    · rw [ku, kw, order_gaugeCt] at ho
      omega
  have h21 : u₂.1 ≠ u₁.1 := fun e => hu1 (fst_eq_of_step l1 l0 e)
  obtain ⟨u₃, l2, c3⟩ := loop_step C hsep c2
  obtain ⟨h3a, h3b, h3c⟩ := nop c3
  by_cases e3 : u₃.1 = u.1
  · -- a loop of three vertices
    rw [fv_ext e3] at l2
    have hmem : ∀ v, (C.1.1).SameCycle (.inr u) (.inr v) → v = u ∨ v = u₁ ∨ v = u₂ :=
      fun v hv => by
        simpa using mem_of_sameCycle_of_mapsTo (T := {Sum.inr u, Sum.inr u₁, Sum.inr u₂})
          (by simp [l0, l1, l2]) (by simp) hv
    have kr : ∀ r : Wick.FermionVertex κ, (C.1.1).SameCycle (.inr u) (.inr r) → r.1 ≠ u.1 →
        r.1 ≠ w.1 → (∀ v, (C.1.1).SameCycle (.inr u) (.inr v) → v = u ∨ v = w ∨ v = r) →
        κ r.1 = .fermionCt := by
      intro r hr hru hrw hm
      have hk : ¬ (κ r.1 = .gauge ∨ κ r.1 = .gaugeCt) := by
        intro k
        obtain ⟨sr, hsr⟩ := exists_slot k
        obtain ⟨s', -, q, -, hq, hqu, hqw, hqr⟩ := part hr hru hrw hsr
        rcases hm q hq with rfl | rfl | rfl
        exacts [hqu rfl, hqw rfl, hqr rfl]
      rcases kind_fv r with k | k | k
      exacts [absurd (Or.inl k) hk, absurd (Or.inr k) hk, k]
    have fin : ∀ r : Wick.FermionVertex κ, κ r.1 = .fermionCt → r.1 ≠ W.a.1 →
        r.1 ≠ W.b.1 → r.1 ≠ W.c.1 → r.1 ≠ u.1 → r.1 ≠ w.1 →
        (∀ v, (C.1.1).SameCycle (.inr u) (.inr v) → v = u ∨ v = w ∨ v = r) →
        ((C.1.1 (.inr u) = .inr w ∧ C.1.1 (.inr w) = .inr r ∧ C.1.1 (.inr r) = .inr u) ∨
          (C.1.1 (.inr u) = .inr r ∧ C.1.1 (.inr r) = .inr w ∧
            C.1.1 (.inr w) = .inr u)) →
        ∃ R ∈ repsA N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
          C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
      intro r kr hra hrb hrc hru hrw hm hloop
      have hinj : Function.Injective ![W.c.1, W.b.1, W.a.1, u.1, w.1, r.1] := by vec_inj
      have hsurj : Function.Surjective ![W.c.1, W.b.1, W.a.1, u.1, w.1, r.1] := by
        intro t
        rcases hexh t with rfl | rfl | rfl | ⟨v, rfl, hv⟩
        · exact ⟨2, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨0, rfl⟩
        · rcases hm v hv with rfl | rfl | rfl
          · exact ⟨3, rfl⟩
          · exact ⟨4, rfl⟩
          · exact ⟨5, rfl⟩
      have ho := sum_order_le ⟨hinj, hsurj⟩ hg
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, ka, kb, kc, kr, order_gauge, order_fermionCt] at ho
      have ou := order_pos (κ u.1)
      have ow := order_pos (κ w.1)
      exact exists_rep_F h hu hw (eq_gauge_of_order (by omega)) (eq_gauge_of_order (by omega)) kr
        hloop hinj hsurj g hg
    rcases hmem w huw with e | e | e
    · exact absurd (by rw [e]) huw1
    · -- `w = u₁`: the loop `u → w → u₂`
      rw [← e] at l0 l1 hmem h21
      have hm : ∀ v, (C.1.1).SameCycle (.inr u) (.inr v) → v = u ∨ v = w ∨ v = u₂ := hmem
      exact fin u₂ (kr u₂ c2 e2 h21 hm) h2a h2b h2c e2 h21 hm (Or.inl ⟨l0, l1, l2⟩)
    · -- `w = u₂`: the loop `u → u₁ → w`
      rw [← e] at l1 l2 hmem h21
      have hm : ∀ v, (C.1.1).SameCycle (.inr u) (.inr v) → v = u ∨ v = w ∨ v = u₁ :=
        fun v hv => by rcases hmem v hv with h' | h' | h' <;> simp [h']
      exact fin u₁ (kr u₁ c1 hu1 (Ne.symm h21) hm) h1a h1b h1c hu1 (Ne.symm h21) hm
        (Or.inr ⟨l0, l1, l2⟩)
  have h31 : u₃.1 ≠ u₁.1 := fun e => e2 (fst_eq_of_step l2 l0 e)
  have h32 : u₃.1 ≠ u₂.1 := fun e => h21 (fst_eq_of_step l2 l1 e)
  obtain ⟨u₄, l3, c4⟩ := loop_step C hsep c3
  obtain ⟨h4a, h4b, h4c⟩ := nop c4
  by_cases e4 : u₄.1 = u.1
  · -- a loop of four vertices
    rw [fv_ext e4] at l3
    have hmem : ∀ v, (C.1.1).SameCycle (.inr u) (.inr v) →
        v = u ∨ v = u₁ ∨ v = u₂ ∨ v = u₃ := fun v hv => by
      simpa using mem_of_sameCycle_of_mapsTo
        (T := {Sum.inr u, Sum.inr u₁, Sum.inr u₂, Sum.inr u₃}) (by simp [l0, l1, l2, l3])
        (by simp) hv
    have hinj : Function.Injective ![W.c.1, W.b.1, W.a.1, u.1, u₁.1, u₂.1, u₃.1] := by vec_inj
    have hsurj : Function.Surjective ![W.c.1, W.b.1, W.a.1, u.1, u₁.1, u₂.1, u₃.1] := by
      intro t
      rcases hexh t with rfl | rfl | rfl | ⟨v, rfl, hv⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · rcases hmem v hv with rfl | rfl | rfl | rfl
        · exact ⟨3, rfl⟩
        · exact ⟨4, rfl⟩
        · exact ⟨5, rfl⟩
        · exact ⟨6, rfl⟩
    have ho := sum_order_le ⟨hinj, hsurj⟩ hg
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, ka, kb, kc, order_gauge] at ho
    have o0 := order_pos (κ u.1)
    have o1 := order_pos (κ u₁.1)
    have o2 := order_pos (κ u₂.1)
    have o3 := order_pos (κ u₃.1)
    have g0 : κ u.1 = .gauge := eq_gauge_of_order (by omega)
    have g1 : κ u₁.1 = .gauge := eq_gauge_of_order (by omega)
    have g2 : κ u₂.1 = .gauge := eq_gauge_of_order (by omega)
    have g3 : κ u₃.1 = .gauge := eq_gauge_of_order (by omega)
    have perm : ∀ ρ : Fin 7 → Fin 7, Function.Bijective ρ →
        Function.Bijective (![W.c.1, W.b.1, W.a.1, u.1, u₁.1, u₂.1, u₃.1] ∘ ρ) :=
      fun ρ hρ => (Function.Bijective.comp ⟨hinj, hsurj⟩ hρ)
    -- the partner of a loop vertex `p ≠ u, w` is the fourth loop vertex `q`
    have pq : ∀ p q : Wick.FermionVertex κ, (C.1.1).SameCycle (.inr u) (.inr p) →
        p.1 ≠ u.1 → p.1 ≠ w.1 → κ p.1 = .gauge →
        (∀ v, (C.1.1).SameCycle (.inr u) (.inr v) → v = u ∨ v = w ∨ v = p ∨ v = q) →
        ∃ sp sq : Wick.PhotonSlot κ, sp.1 = p.1 ∧ sq.1 = q.1 ∧ C.1.2 (.inr sp) = .inr sq := by
      intro p q hp hpu hpw kp hm
      obtain ⟨sp, hsp⟩ := exists_slot (Or.inl kp)
      obtain ⟨s', e, q', hq', hq'c, hq'u, hq'w, hq'p⟩ := part hp hpu hpw hsp
      rcases hm q' hq'c with rfl | rfl | rfl | rfl
      exacts [absurd rfl hq'u, absurd rfl hq'w, absurd rfl hq'p, ⟨sp, s', hsp, hq'.symm, e⟩]
    rcases hmem w huw with e | e | e | e
    · exact absurd (by rw [e]) huw1
    · -- `w = u₁`: `VA`
      rw [← e] at l0 l1 hmem h21 h31 g1 hinj hsurj
      obtain ⟨sp, sq, hsp, hsq, tpq⟩ := pq u₂ u₃ c2 e2 h21 g2
        fun v hv => by rcases hmem v hv with h' | h' | h' | h' <;> simp [h']
      exact exists_rep_V h hu hw hsp hsq g0 g1 g2 g3 tpq (Or.inl ⟨l0, l1, l2, l3⟩) hinj hsurj
        g hg
    · -- `w = u₂`: `VB`
      have hb := perm ![0, 1, 2, 3, 5, 4, 6] (by decide)
      rw [← e] at l1 l2 hmem h21 h32 g2
      have hv : ![W.c.1, W.b.1, W.a.1, u.1, u₁.1, w.1, u₃.1] ∘ ![0, 1, 2, 3, 5, 4, 6] =
          ![W.c.1, W.b.1, W.a.1, u.1, w.1, u₁.1, u₃.1] := by
        funext i
        fin_cases i <;> rfl
      rw [← e, hv] at hb
      obtain ⟨sp, sq, hsp, hsq, tpq⟩ := pq u₁ u₃ c1 hu1 (Ne.symm h21) g1
        fun v hv => by rcases hmem v hv with h' | h' | h' | h' <;> simp [h']
      exact exists_rep_V h hu hw hsp hsq g0 g2 g1 g3 tpq (Or.inr (Or.inl ⟨l0, l1, l2, l3⟩))
        hb.1 hb.2 g hg
    · -- `w = u₃`: `VC`
      have hb := perm ![0, 1, 2, 3, 6, 4, 5] (by decide)
      rw [← e] at l2 l3 hmem h31 h32 g3
      have hv : ![W.c.1, W.b.1, W.a.1, u.1, u₁.1, u₂.1, w.1] ∘ ![0, 1, 2, 3, 6, 4, 5] =
          ![W.c.1, W.b.1, W.a.1, u.1, w.1, u₁.1, u₂.1] := by
        funext i
        fin_cases i <;> rfl
      rw [← e, hv] at hb
      obtain ⟨sp, sq, hsp, hsq, tpq⟩ := pq u₁ u₂ c1 hu1 (Ne.symm h31) g1
        fun v hv => by rcases hmem v hv with h' | h' | h' | h' <;> simp [h']
      exact exists_rep_V h hu hw hsp hsq g0 g3 g1 g2 tpq
        (Or.inr (Or.inr ⟨l0, l1, l2, l3⟩)) hb.1 hb.2 g hg
  · -- five loop vertices: too many vertices
    have h41 : u₄.1 ≠ u₁.1 := fun e => e3 (fst_eq_of_step l3 l0 e)
    have h42 : u₄.1 ≠ u₂.1 := fun e => h31 (fst_eq_of_step l3 l1 e)
    have h43 : u₄.1 ≠ u₃.1 := fun e => h32 (fst_eq_of_step l3 l2 e)
    have hinj : Function.Injective
        ![W.c.1, W.b.1, W.a.1, u.1, u₁.1, u₂.1, u₃.1, u₄.1] := by vec_inj
    exact absurd (card_le_seven hinj hg) (by decide)

end Loop

/-! ### The classification -/

/-- **The set (a) classification.** Every graded contraction `(κ, g, C)` of graded order `7`
satisfying (A₁) is a relabelling of one of the nine representatives, with its grading. -/
theorem exists_rep_setA (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7)
    {C : Contraction 1 1 κ} (hC : QED.ThreeLoop.IsSetA C) :
    ∃ R ∈ repsA N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨a, b, c, sa, sb, sc, x, y, ka, kb, kc, s0a, sab, sbc, sc0, hsb, tsb, hsa, hsc, hx, hy,
    hins⟩ := hC
  rcases hins with ⟨kx, hyx, hne, hexh⟩ | ⟨u, w, hu, hw, hsep, huw, hexh⟩
  · exact exists_rep_setA_photonCt g hg ka kb kc s0a sab sbc sc0 hsb tsb hsa hsc hx hy kx hyx
      hne hexh
  · exact exists_rep_setA_loop (W := ⟨a, b, c, sa, sb, sc, x, y⟩)
      ⟨ka, kb, kc, s0a, sab, sbc, sc0, hsb, tsb, hsa, hsc, hx, hy⟩ hu hw hsep huw hexh g hg

end QED.ChainProof.SetALink

end
