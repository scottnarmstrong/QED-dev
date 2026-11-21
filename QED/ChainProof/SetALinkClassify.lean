/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkReps
public import QED.ChainProof.EnumClassify
public import QED.GradedProof.VP2Relabel

/-!
# The set (a) classification: generic tools and the `photonCt` class

Helper for the Phase 5 Stage 3a enumeration (decision D-58). The representatives of
`QED/ChainProof/SetALinkReps.lean` are collected by vertex number in `repsA N` (`RepA`: kinds,
contraction, grading). A contraction `C` of `κ` is the relabelling `relabelK π hκ R` of a
representative as soon as `C` agrees with `R` along `π` on every fermion and photon field
(`eq_relabelK_of_agree`); this replaces the set (b) witness transport.

* `QED.ChainProof.SetALink.exists_rep_setA_photonCt`: **the `photonCt` class.** If `(κ, g, C)` has
  graded order `7` and `C` satisfies the `photonCt` branch of (A₁), then `N = 4` and
  `(κ, g, C)` is a relabelling of `(kP, gradP, repP s)` for the field `s` of `x`.

The loop classes (`VA`, …, `GU`) are the remaining part of the classification
(see the session notes `setAlink/STATUS.md`).
-/

@[expose] public section

namespace QED.ChainProof.SetALink

open QED.WickModel QED.TwoLoop.Relabel QED.ChainProof.Enum QED.GradedProof.VP2

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Representatives by vertex number -/

/-- A set (a) representative: its kinds, its contraction and its grading. -/
structure RepA (N : ℕ) where
  /-- the kind sequence -/
  kinds : Fin N → Wick.VertexKind
  /-- the contraction -/
  rep : Contraction 1 1 kinds
  /-- the grading -/
  grad : Graded.Grading kinds

/-- The seven-vertex representatives. -/
def repsA7 : List (RepA 7) := [⟨kV, repVA, 0⟩, ⟨kV, repVB, 0⟩, ⟨kV, repVC, 0⟩]

/-- The six-vertex representatives. -/
def repsA6 : List (RepA 6) := [⟨kF, repFA, 0⟩, ⟨kF, repFB, 0⟩]

/-- The five-vertex representatives. -/
def repsA5 : List (RepA 5) := [⟨kGW, repGW, 0⟩, ⟨kGU, repGU, 0⟩]

/-- The four-vertex representatives. -/
def repsA4 : List (RepA 4) := [⟨kP, repP 0, gradP⟩, ⟨kP, repP 1, gradP⟩]

/-- The set (a) representatives with `N` vertices. -/
def repsA : (N : ℕ) → List (RepA N)
  | 4 => repsA4
  | 5 => repsA5
  | 6 => repsA6
  | 7 => repsA7
  | _ => []

/-! ### Agreement along a relabelling -/

/-- **A contraction agreeing with `R` along `π` on every field is the relabelling of `R`.** -/
theorem eq_relabelK_of_agree {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ (π t) = κ' t) (R : Contraction 1 1 κ') (C : Contraction 1 1 κ)
    (hσ : ∀ z, C.1.1 (extFK π hκ z) = extFK π hκ (R.1.1 z))
    (hτ : ∀ z, C.1.2 (extPK π hκ z) = extPK π hκ (R.1.2 z)) : C = relabelK π hκ R := by
  refine Subtype.ext (Prod.ext (Equiv.ext fun y => ?_) (Equiv.ext fun y => ?_))
  · obtain ⟨z, rfl⟩ := (extFK π hκ).surjective y
    rw [hσ]
    exact (relabelK_fst_apply π hκ R z).symm
  · obtain ⟨z, rfl⟩ := (extPK π hκ).surjective y
    rw [hτ]
    exact (relabelK_snd_apply π hκ R z).symm

/-- The graded order splits into the vertex orders and twice the levels. -/
theorem gradedOrder_eq (g : Graded.Grading κ) :
    Graded.gradedOrder κ g = ∑ t, (κ t).order + ∑ t : Graded.CtVertex κ, 2 * g t := rfl

/-! ### The `photonCt` class -/

section PhotonCt

variable {C : Contraction 1 1 κ} {a b c : Wick.FermionVertex κ} {sa sb sc x y : Wick.PhotonSlot κ}

theorem open_ne (s0a : C.1.1 (.inl 0) = .inr a) (sab : C.1.1 (.inr a) = .inr b)
    (sbc : C.1.1 (.inr b) = .inr c) (sc0 : C.1.1 (.inr c) = .inl 0) :
    a.1 ≠ b.1 ∧ b.1 ≠ c.1 ∧ a.1 ≠ c.1 := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [← fv_ext e] at sab
    exact Sum.inl_ne_inr (C.1.1.injective (s0a.trans sab.symm))
  · rw [← fv_ext e] at sc0
    exact Sum.inr_ne_inl (sbc.symm.trans sc0)
  · rw [← fv_ext e] at sc0
    exact Sum.inr_ne_inl (sab.symm.trans sc0)

theorem repP_fst (s : Fin 2) :
    (repP s).1.1 (.inl 0) = .inr (fv kP 2) ∧ (repP s).1.1 (.inr (fv kP 0)) = .inl 0 ∧
      (repP s).1.1 (.inr (fv kP 1)) = .inr (fv kP 0) ∧
      (repP s).1.1 (.inr (fv kP 2)) = .inr (fv kP 1) := by
  revert s; decide +kernel

theorem repP_snd (s : Fin 2) :
    (repP s).1.2 (.inl 0) = .inr (pg kP 1) ∧ (repP s).1.2 (.inr (pg kP 1)) = .inl 0 ∧
      (repP s).1.2 (.inr (pg kP 2)) = .inr (pc kP 3 s) ∧
      (repP s).1.2 (.inr (pc kP 3 s)) = .inr (pg kP 2) ∧
      (repP s).1.2 (.inr (pg kP 0)) = .inr (pc kP 3 s.rev) ∧
      (repP s).1.2 (.inr (pc kP 3 s.rev)) = .inr (pg kP 0) := by
  revert s; decide +kernel

theorem kP_fields : ∀ z : Fin 1 ⊕ Wick.FermionVertex kP,
    z = .inl 0 ∨ z = .inr (fv kP 0) ∨ z = .inr (fv kP 1) ∨ z = .inr (fv kP 2) := by
  decide +kernel

theorem kP_slots (s : Fin 2) : ∀ z : Fin 1 ⊕ Wick.PhotonSlot kP, z = .inl 0 ∨
    z = .inr (pg kP 0) ∨ z = .inr (pg kP 1) ∨ z = .inr (pg kP 2) ∨ z = .inr (pc kP 3 s) ∨
      z = .inr (pc kP 3 s.rev) := by
  revert s; decide +kernel

/-- **The `photonCt` class of (A₁).** -/
theorem exists_rep_setA_photonCt (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7)
    (ka : κ a.1 = .gauge) (kb : κ b.1 = .gauge) (kc : κ c.1 = .gauge)
    (s0a : C.1.1 (.inl 0) = .inr a) (sab : C.1.1 (.inr a) = .inr b)
    (sbc : C.1.1 (.inr b) = .inr c) (sc0 : C.1.1 (.inr c) = .inl 0)
    (hsb : sb.1 = b.1) (tsb : C.1.2 (.inl 0) = .inr sb) (hsa : sa.1 = a.1) (hsc : sc.1 = c.1)
    (hx : C.1.2 (.inr sa) = .inr x) (hy : C.1.2 (.inr sc) = .inr y)
    (kx : κ x.1 = .photonCt) (hyx : y.1 = x.1) (hne : y ≠ x)
    (hexh : ∀ t : Fin N, t = a.1 ∨ t = b.1 ∨ t = c.1 ∨ t = x.1) :
    ∃ R ∈ repsA N, ∃ π : Equiv.Perm (Fin N), ∃ hκ : ∀ t, κ (π t) = R.kinds t,
      C = relabelK π hκ R.rep ∧ g = gradMap π hκ R.grad := by
  obtain ⟨hab, hbc, hac⟩ := open_ne s0a sab sbc sc0
  have hxa : x.1 ≠ a.1 := fun e => by rw [e, ka] at kx; exact absurd kx (by decide)
  have hxb : x.1 ≠ b.1 := fun e => by rw [e, kb] at kx; exact absurd kx (by decide)
  have hxc : x.1 ≠ c.1 := fun e => by rw [e, kc] at kx; exact absurd kx (by decide)
  set f : Fin 4 → Fin N := ![c.1, b.1, a.1, x.1] with hf
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
      first
      | exact hab hij | exact hab hij.symm | exact hbc hij | exact hbc hij.symm
      | exact hac hij | exact hac hij.symm | exact hxa hij | exact hxa hij.symm
      | exact hxb hij | exact hxb hij.symm | exact hxc hij | exact hxc hij.symm
  have hsurj : Function.Surjective f := by
    intro t
    rcases hexh t with rfl | rfl | rfl | rfl
    exacts [⟨2, rfl⟩, ⟨1, rfl⟩, ⟨0, rfl⟩, ⟨3, rfl⟩]
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  have hN : 4 = N := by simpa using Fintype.card_of_bijective hbij
  subst hN
  have hκf : ∀ t, κ (f t) = kP t := by
    intro t
    fin_cases t
    exacts [kc, kb, ka, kx]
  have hxv := ps_val_lt_two_of_photonCt x kx
  obtain ⟨-, hyv⟩ := ct_vals kx hyx hne
  obtain ⟨s, hs⟩ : ∃ s : Fin 2, s.val = x.2.val := ⟨⟨x.2.val, hxv⟩, rfl⟩
  set π : Equiv.Perm (Fin 4) := Equiv.ofBijective f hbij with hπ
  have hπf : ∀ t, π t = f t := fun _ => rfl
  have hκ : ∀ t, κ (π t) = kP t := hκf
  have hmem : (⟨kP, repP s, gradP⟩ : RepA 4) ∈ repsA 4 := by
    simp only [repsA, repsA4, List.mem_cons, List.not_mem_nil, or_false]
    rcases (by omega : x.2.val = 0 ∨ x.2.val = 1) with h | h
    · exact Or.inl (by rw [show s = 0 from Fin.ext (hs.trans h)])
    · exact Or.inr (by rw [show s = 1 from Fin.ext (hs.trans h)])
  refine ⟨⟨kP, repP s, gradP⟩, hmem, π, hκ, ?_, ?_⟩
  · -- the contraction
    have fa : fvMap π hκ (fv kP 2) = a := fv_ext rfl
    have fb : fvMap π hκ (fv kP 1) = b := fv_ext rfl
    have fc : fvMap π hκ (fv kP 0) = c := fv_ext rfl
    have pa : psMap π hκ (pg kP 2) = sa :=
      ps_ext (by rw [psMap_fst, hsa]; rfl) (by rw [psMap_snd_val, val_eq_zero_of_eq hsa ka]; rfl)
    have pb : psMap π hκ (pg kP 1) = sb :=
      ps_ext (by rw [psMap_fst, hsb]; rfl) (by rw [psMap_snd_val, val_eq_zero_of_eq hsb kb]; rfl)
    have pc' : psMap π hκ (pg kP 0) = sc :=
      ps_ext (by rw [psMap_fst, hsc]; rfl) (by rw [psMap_snd_val, val_eq_zero_of_eq hsc kc]; rfl)
    have px : psMap π hκ (pc kP 3 s) = x := ps_ext (by rw [psMap_fst]; rfl) (by simp [pc, hs])
    have py : psMap π hκ (pc kP 3 s.rev) = y :=
      ps_ext (by rw [psMap_fst, hyx]; rfl) (by simp [pc, hs, hyv])
    obtain ⟨f0, f1, f2, f3⟩ := repP_fst s
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := repP_snd s
    refine eq_relabelK_of_agree π hκ (repP s) C ?_ ?_
    · intro z
      rcases kP_fields z with rfl | rfl | rfl | rfl
      · rw [f0, extFK_inl, extFK_inr, fa, s0a]
      · rw [f1, extFK_inl, extFK_inr, fc, sc0]
      · rw [f2, extFK_inr, extFK_inr, fb, fc, sbc]
      · rw [f3, extFK_inr, extFK_inr, fa, fb, sab]
    · intro z
      rcases kP_slots s z with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [e0, extPK_inl, extPK_inr, pb, tsb]
      · rw [e4, extPK_inr, extPK_inr, pc', py, hy]
      · rw [e1, extPK_inr, extPK_inl, pb, tau_symm C tsb]
      · rw [e2, extPK_inr, extPK_inr, pa, px, hx]
      · rw [e3, extPK_inr, extPK_inr, px, pa, tau_symm C hx]
      · rw [e5, extPK_inr, extPK_inr, py, pc', tau_symm C hy]
  · -- the grading: the only counterterm vertex is `x.1`, of level `1`
    have hct : ∀ t : Graded.CtVertex κ, t.1 = x.1 := by
      intro t
      rcases hexh t.1 with e | e | e | e
      · exact absurd (e ▸ ka) t.2
      · exact absurd (e ▸ kb) t.2
      · exact absurd (e ▸ kc) t.2
      · exact e
    have kx' : κ x.1 ≠ .gauge := by rw [kx]; decide
    have hsumo : ∑ t, (κ t).order = 5 := by
      rw [← Equiv.sum_comp π]
      simp only [hκ]
      decide +kernel
    have hlev : g ⟨x.1, kx'⟩ = 1 := by
      rw [gradedOrder_eq, hsumo,
        Finset.sum_eq_single_of_mem (⟨x.1, kx'⟩ : Graded.CtVertex κ) (Finset.mem_univ _)
          (fun t _ ht => absurd (Subtype.ext (hct t)) ht)] at hg
      omega
    funext t
    rw [show t = ⟨x.1, kx'⟩ from Subtype.ext (hct t), hlev]
    rfl

end PhotonCt

end QED.ChainProof.SetALink

end
