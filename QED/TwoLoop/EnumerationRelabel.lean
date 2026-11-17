/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.WickModel.FermionSign
public import QED.TwoLoop.ChordLoopLine
public import QED.TwoLoop.LoopBound

/-!
# Relabelling the vertices of a contraction of gauge vertices

The `1/N!` of the Wick expansion is cancelled because relabelling the `N` vertices permutes the
contractions (section 3.3 of `docs/TWO-LOOP-DERIVATION.md`). For `N` gauge vertices
(`gauges N`), a permutation `π` of the vertices acts on the contractions by conjugating both
pairings (`relabel π C`). This file proves:

* `QED.TwoLoop.Enumeration.relabel_one`, `relabel_mul`: it is an action of `Equiv.Perm (Fin N)`.
* `QED.TwoLoop.Enumeration.fermionSign_relabel`: it preserves the fermionic sign (X₅).
* `QED.TwoLoop.Enumeration.isOnePI_relabel_iff`: it preserves one-particle irreducibility (X₁₈).
  The internal lines of `C` and of `relabel π C` correspond (`lineEquiv`), with ends moved by
  `π` up to orientation: a photon line is indexed by its field of smaller key, which relabelling
  may change.
-/

@[expose] public section

namespace QED.TwoLoop.Enumeration

open QED.WickModel Relation

/-- `N` gauge vertices `e Ψ̄ A̸ Ψ`. -/
abbrev gauges (N : ℕ) : Fin N → Wick.VertexKind := fun _ => .gauge

variable {nf nA N : ℕ}

/-- Relabelling the fermion vertices. -/
def fvPerm (π : Equiv.Perm (Fin N)) : Equiv.Perm (Wick.FermionVertex (gauges N)) :=
  π.subtypePerm fun _ => Iff.rfl

/-- Relabelling the photon fields. -/
def psPerm (π : Equiv.Perm (Fin N)) : Equiv.Perm (Wick.PhotonSlot (gauges N)) where
  toFun a := ⟨π a.1, a.2⟩
  invFun a := ⟨π.symm a.1, a.2⟩
  left_inv _ := Sigma.ext (π.symm_apply_apply _) HEq.rfl
  right_inv _ := Sigma.ext (π.apply_symm_apply _) HEq.rfl

@[simp] theorem fvPerm_val (π : Equiv.Perm (Fin N)) (t : Wick.FermionVertex (gauges N)) :
    (fvPerm π t).1 = π t.1 := rfl

@[simp] theorem psPerm_fst (π : Equiv.Perm (Fin N)) (a : Wick.PhotonSlot (gauges N)) :
    (psPerm π a).1 = π a.1 := rfl

/-- The relabelling on the fermion fields, the externals fixed. -/
def extF (π : Equiv.Perm (Fin N)) : Fin nf ⊕ Wick.FermionVertex (gauges N) ≃
    Fin nf ⊕ Wick.FermionVertex (gauges N) :=
  Equiv.sumCongr (Equiv.refl _) (fvPerm π)

/-- The relabelling on the photon fields, the externals fixed. -/
def extP (π : Equiv.Perm (Fin N)) : Fin nA ⊕ Wick.PhotonSlot (gauges N) ≃
    Fin nA ⊕ Wick.PhotonSlot (gauges N) :=
  Equiv.sumCongr (Equiv.refl _) (psPerm π)

/-- **Relabelling a contraction** of `N` gauge vertices by `π`: vertex `t` becomes `π t`. -/
def relabel (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N)) :
    Contraction nf nA (gauges N) :=
  ⟨((extF π).permCongr C.1.1, (extP π).permCongr C.1.2), fun b => by
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, (C.2 _).1, Equiv.apply_symm_apply,
      true_and]
    intro h
    exact (C.2 _).2 ((extP π).injective (h.trans ((extP π).apply_symm_apply b).symm))⟩

theorem relabel_fst_apply (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N))
    (x : Fin nf ⊕ Wick.FermionVertex (gauges N)) :
    (relabel π C).1.1 (extF π x) = extF π (C.1.1 x) := by
  simp [relabel]

theorem relabel_snd_apply (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N))
    (x : Fin nA ⊕ Wick.PhotonSlot (gauges N)) :
    (relabel π C).1.2 (extP π x) = extP π (C.1.2 x) := by
  simp [relabel]

@[simp] theorem extF_inl (π : Equiv.Perm (Fin N)) (i : Fin nf) :
    extF (nf := nf) π (.inl i) = .inl i := rfl

@[simp] theorem extF_inr (π : Equiv.Perm (Fin N)) (t : Wick.FermionVertex (gauges N)) :
    extF (nf := nf) π (.inr t) = .inr (fvPerm π t) := rfl

@[simp] theorem extP_inl (π : Equiv.Perm (Fin N)) (i : Fin nA) :
    extP (nA := nA) π (.inl i) = .inl i := rfl

@[simp] theorem extP_inr (π : Equiv.Perm (Fin N)) (a : Wick.PhotonSlot (gauges N)) :
    extP (nA := nA) π (.inr a) = .inr (psPerm π a) := rfl

theorem fvPerm_mul (π ρ : Equiv.Perm (Fin N)) : fvPerm (π * ρ) = fvPerm π * fvPerm ρ := by
  ext t
  rfl

theorem psPerm_mul (π ρ : Equiv.Perm (Fin N)) : psPerm (π * ρ) = psPerm π * psPerm ρ := by
  ext a
  · rfl
  · rfl

theorem relabel_one (C : Contraction nf nA (gauges N)) : relabel 1 C = C := by
  have hF : extF (nf := nf) (1 : Equiv.Perm (Fin N)) = Equiv.refl _ := by
    ext (i | t) <;> rfl
  have hP : extP (nA := nA) (1 : Equiv.Perm (Fin N)) = Equiv.refl _ := by
    ext (i | ⟨t, k⟩) <;> rfl
  apply Subtype.ext
  simp only [relabel, hF, hP]
  rfl

theorem relabel_mul (π ρ : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N)) :
    relabel (π * ρ) C = relabel π (relabel ρ C) := by
  have hF : extF (nf := nf) (π * ρ) = (extF ρ).trans (extF π) := by
    ext (i | t) <;> rfl
  have hP : extP (nA := nA) (π * ρ) = (extP ρ).trans (extP π) := by
    ext (i | ⟨t, k⟩) <;> rfl
  apply Subtype.ext
  simp only [relabel, hF, hP]
  ext x <;> rfl

/-- Relabelling preserves the fermionic sign (X₅). -/
theorem fermionSign_relabel (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N)) :
    fermionSign (relabel π C) = fermionSign C := by
  simp only [fermionSign, relabel, Equiv.Perm.sign_permCongr]

/-! ### The internal lines correspond -/

section Lines

variable (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N))

/-- The fermion lines of `C` and of `relabel π C`. -/
def fermionLineEquiv : FermionLine C ≃ FermionLine (relabel π C) :=
  Equiv.subtypeEquiv (fvPerm π) fun t => by
    have := relabel_fst_apply π C (.inr t)
    simp only [extF_inr] at this
    rw [this]
    cases C.1.1 (.inr t) <;> rfl

theorem tail_eq {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ} (f : FermionLine C)
    {s : Wick.FermionVertex κ} (h : C.1.1 (.inr f.1) = .inr s) : f.tail = s :=
  (Sum.getRight_eq_iff _).mpr h

theorem head_eq {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ} (g : PhotonLine C)
    {b : Wick.PhotonSlot κ} (h : C.1.2 (.inr g.1) = .inr b) : g.head = b :=
  Sum.inr_injective ((LoopBound.apply_inr_photonLine g).symm.trans h)

theorem fermionLineEquiv_ends (f : FermionLine C) :
    Line.ends (Sum.inl (fermionLineEquiv π C f) : Line (relabel π C)) =
      (π (Line.ends (Sum.inl f : Line C)).1, π (Line.ends (Sum.inl f : Line C)).2) := by
  obtain ⟨s, hs⟩ : ∃ s, C.1.1 (.inr f.1) = .inr s := Sum.isRight_iff.mp f.2
  have h' : (relabel π C).1.1 (.inr (fermionLineEquiv π C f).1) = .inr (fvPerm π s) := by
    have := relabel_fst_apply π C (.inr f.1)
    simp only [extF_inr, hs] at this
    exact this
  simp only [Line.ends, tail_eq _ h', tail_eq _ hs]
  rfl

theorem relabel_snd_inr (a b : Wick.PhotonSlot (gauges N)) (h : C.1.2 (.inr a) = .inr b) :
    (relabel π C).1.2 (.inr (psPerm π a)) = .inr (psPerm π b) := by
  have := relabel_snd_apply π C (.inr a)
  simp only [extP_inr, h] at this
  exact this

theorem psPerm_ne {a b : Wick.PhotonSlot (gauges N)} (h : C.1.2 (.inr a) = .inr b) :
    Wick.photonKey (psPerm π a) ≠ Wick.photonKey (psPerm π b) := fun hk => by
  have hab := (psPerm π).injective (Chord.photonKey_injective hk)
  subst hab
  exact (C.2 _).2 h

/-- The image of a photon line: the line of the two relabelled fields. -/
def photonLineMap (g : PhotonLine C) : PhotonLine (relabel π C) :=
  if h : Wick.photonKey (psPerm π g.1) < Wick.photonKey (psPerm π g.head) then
    ⟨psPerm π g.1, psPerm π g.head,
      relabel_snd_inr π C _ _ (LoopBound.apply_inr_photonLine g), h⟩
  else
    ⟨psPerm π g.head, psPerm π g.1, relabel_snd_inr π C _ _ (LoopBound.apply_inr_head g),
      lt_of_le_of_ne (not_lt.mp h)
        (psPerm_ne π C (LoopBound.apply_inr_photonLine g)).symm⟩

theorem photonLineMap_cases (g : PhotonLine C) :
    ((photonLineMap π C g).1 = psPerm π g.1 ∧ (photonLineMap π C g).head = psPerm π g.head) ∨
      ((photonLineMap π C g).1 = psPerm π g.head ∧
        (photonLineMap π C g).head = psPerm π g.1) := by
  unfold photonLineMap
  split_ifs with h
  · exact Or.inl ⟨rfl, head_eq _ (relabel_snd_inr π C _ _ (LoopBound.apply_inr_photonLine g))⟩
  · exact Or.inr ⟨rfl, head_eq _ (relabel_snd_inr π C _ _ (LoopBound.apply_inr_head g))⟩

theorem photonLineMap_injective : Function.Injective (photonLineMap π C) := by
  intro g₁ g₂ h
  have k₁ := LoopBound.photonKey_lt_head g₁
  have k₂ := LoopBound.photonKey_lt_head g₂
  have e₁ := LoopBound.apply_inr_photonLine g₁
  have e₂ := LoopBound.apply_inr_photonLine g₂
  have h₁ := congrArg Subtype.val h
  have hh := congrArg PhotonLine.head h
  apply Subtype.ext
  rcases photonLineMap_cases π C g₁ with ⟨a₁, b₁⟩ | ⟨a₁, b₁⟩ <;>
    rcases photonLineMap_cases π C g₂ with ⟨a₂, b₂⟩ | ⟨a₂, b₂⟩
  · exact (psPerm π).injective (a₁.symm.trans (h₁.trans a₂))
  · have x : g₁.1 = g₂.head := (psPerm π).injective (a₁.symm.trans (h₁.trans a₂))
    have y : g₁.head = g₂.1 := (psPerm π).injective (b₁.symm.trans (hh.trans b₂))
    rw [x, y] at k₁
    exact absurd (k₁.trans k₂) (lt_irrefl _)
  · have x : g₁.head = g₂.1 := (psPerm π).injective (a₁.symm.trans (h₁.trans a₂))
    have y : g₁.1 = g₂.head := (psPerm π).injective (b₁.symm.trans (hh.trans b₂))
    rw [x, y] at k₁
    exact absurd (k₁.trans k₂) (lt_irrefl _)
  · have y : g₁.1 = g₂.1 := (psPerm π).injective (b₁.symm.trans (hh.trans b₂))
    exact y

theorem photonLineMap_surjective : Function.Surjective (photonLineMap π C) := by
  intro g'
  obtain ⟨b', hb', hk'⟩ := g'.2
  obtain ⟨a, ha⟩ := (psPerm π).surjective g'.1
  have h1 := relabel_snd_apply π C (.inr a)
  rw [extP_inr, ha, hb'] at h1
  obtain ⟨c, hc⟩ : ∃ c, C.1.2 (.inr a) = .inr c := by
    rcases hC : C.1.2 (.inr a) with i | c
    · rw [hC] at h1
      cases h1
    · exact ⟨c, rfl⟩
  rw [hc, extP_inr] at h1
  have hgb : psPerm π c = b' := (Sum.inr_injective h1).symm
  have hkac : Wick.photonKey a ≠ Wick.photonKey c := fun hk =>
    (C.2 _).2 (hc.trans (congrArg _ (Chord.photonKey_injective hk).symm))
  rcases lt_or_gt_of_ne hkac with hlt | hlt
  · have hhead : PhotonLine.head (C := C) ⟨a, c, hc, hlt⟩ = c := head_eq _ hc
    have hcond : Wick.photonKey (psPerm π (⟨a, c, hc, hlt⟩ : PhotonLine C).1) <
        Wick.photonKey (psPerm π (PhotonLine.head (C := C) ⟨a, c, hc, hlt⟩)) := by
      rw [hhead, hgb]
      exact ha ▸ hk'
    refine ⟨⟨a, c, hc, hlt⟩, Subtype.ext ?_⟩
    unfold photonLineMap
    rw [dite_eq_left hcond]
    exact ha
  · have hca : C.1.2 (.inr c) = .inr a := by rw [← hc, (C.2 _).1]
    have hhead : PhotonLine.head (C := C) ⟨c, a, hca, hlt⟩ = a := head_eq _ hca
    have hcond : ¬ Wick.photonKey (psPerm π (⟨c, a, hca, hlt⟩ : PhotonLine C).1) <
        Wick.photonKey (psPerm π (PhotonLine.head (C := C) ⟨c, a, hca, hlt⟩)) := by
      rw [hhead]
      show ¬ Wick.photonKey (psPerm π c) < _
      rw [hgb, ha]
      exact not_lt.mpr hk'.le
    refine ⟨⟨c, a, hca, hlt⟩, Subtype.ext ?_⟩
    unfold photonLineMap
    rw [dite_eq_right hcond]
    show psPerm π (PhotonLine.head (C := C) ⟨c, a, hca, hlt⟩) = _
    rw [hhead, ha]

/-- The internal lines of `C` and of `relabel π C`. -/
noncomputable def lineEquiv : Line C ≃ Line (relabel π C) :=
  Equiv.sumCongr (fermionLineEquiv π C)
    (Equiv.ofBijective (photonLineMap π C)
      ⟨photonLineMap_injective π C, photonLineMap_surjective π C⟩)

theorem lineEquiv_ends (f : Line C) :
    (lineEquiv π C f).ends = (π f.ends.1, π f.ends.2) ∨
      (lineEquiv π C f).ends = (π f.ends.2, π f.ends.1) := by
  rcases f with f | g
  · exact Or.inl (fermionLineEquiv_ends π C f)
  · rcases photonLineMap_cases π C g with ⟨a, b⟩ | ⟨a, b⟩
    · left
      change ((photonLineMap π C g).1.1, (photonLineMap π C g).head.1) = _
      rw [a, b]
      rfl
    · right
      change ((photonLineMap π C g).1.1, (photonLineMap π C g).head.1) = _
      rw [a, b]
      rfl

theorem joined_relabel_iff (S : Set (Line C)) (u w : Fin N) :
    Joined (relabel π C) (lineEquiv π C '' S) (π u) (π w) ↔ Joined C S u w := by
  constructor
  · rintro ⟨f', hf', h⟩
    obtain ⟨f, rfl⟩ := (lineEquiv π C).surjective f'
    refine ⟨f, fun hf => hf' ⟨f, hf, rfl⟩, ?_⟩
    rcases lineEquiv_ends π C f with he | he <;> rw [he] at h <;>
      rcases h with h | h <;> simp only [Prod.mk.injEq, π.injective.eq_iff] at h
    · exact Or.inl (Prod.ext h.1 h.2)
    · exact Or.inr (Prod.ext h.1 h.2)
    · exact Or.inr (Prod.ext h.2 h.1)
    · exact Or.inl (Prod.ext h.2 h.1)
  · rintro ⟨f, hf, h⟩
    refine ⟨lineEquiv π C f, fun ⟨g, hg, he⟩ => hf ((lineEquiv π C).injective he ▸ hg), ?_⟩
    rcases lineEquiv_ends π C f with he | he <;> rw [he] <;> rcases h with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem reflTransGen_relabel_iff (S : Set (Line C)) (u w : Fin N) :
    ReflTransGen (Joined (relabel π C) (lineEquiv π C '' S)) (π u) (π w) ↔
      ReflTransGen (Joined C S) u w := by
  constructor
  · intro h
    have := ReflTransGen.lift π.symm (by
      intro a b hab
      rw [← π.apply_symm_apply a, ← π.apply_symm_apply b] at hab
      exact (joined_relabel_iff π C S _ _).mp hab) (π u) (π w) h
    simpa [Function.onFun] using this
  · intro h
    exact ReflTransGen.lift π (by
      intro a b hab
      exact (joined_relabel_iff π C S a b).mpr hab) u w h

end Lines

theorem externalsAttached_relabel_iff (π : Equiv.Perm (Fin N))
    (C : Contraction nf nA (gauges N)) :
    ExternalsAttached (relabel π C) ↔ ExternalsAttached C := by
  have hF : ∀ i, (relabel π C).1.1 (.inl i) = extF π (C.1.1 (.inl i)) := fun i =>
    relabel_fst_apply π C (.inl i)
  have hP : ∀ i, (relabel π C).1.2 (.inl i) = extP π (C.1.2 (.inl i)) := fun i =>
    relabel_snd_apply π C (.inl i)
  have kF : ∀ x : Fin nf ⊕ Wick.FermionVertex (gauges N), ∀ j,
      extF π x ≠ .inl j ↔ x ≠ .inl j := by
    rintro (i | t) j <;> simp
  have kP : ∀ x : Fin nA ⊕ Wick.PhotonSlot (gauges N), ∀ j,
      extP π x ≠ .inl j ↔ x ≠ .inl j := by
    rintro (i | t) j <;> simp
  simp only [ExternalsAttached, hF, hP, kF, kP]

/-- **Relabelling preserves one-particle irreducibility** (X₁₈). -/
theorem isOnePI_relabel_iff (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N)) :
    IsOnePI (relabel π C) ↔ IsOnePI C := by
  have hV : VerticesConnected (relabel π C) ↔ VerticesConnected C := by
    have h := reflTransGen_relabel_iff π C ∅
    simp only [Set.image_empty] at h
    constructor
    · intro hC u w
      exact (h u w).mp (hC _ _)
    · intro hC u w
      rw [← π.apply_symm_apply u, ← π.apply_symm_apply w]
      exact (h _ _).mpr (hC _ _)
  have hB : (∀ f : Line (relabel π C), ¬ IsBridge f) ↔ ∀ f : Line C, ¬ IsBridge f := by
    have key : ∀ f : Line C, IsBridge (lineEquiv π C f) ↔ IsBridge f := fun f => by
      have h := reflTransGen_relabel_iff π C {f} f.ends.1 f.ends.2
      rw [Set.image_singleton] at h
      unfold IsBridge
      rw [not_iff_not, ← h]
      rcases lineEquiv_ends π C f with he | he <;> rw [he]
      exact ⟨LoopBound.reflTransGen_joined_symm, LoopBound.reflTransGen_joined_symm⟩
    constructor
    · intro h f
      exact (key f).not.mp (h _)
    · intro h f'
      obtain ⟨f, rfl⟩ := (lineEquiv π C).surjective f'
      exact (key f).not.mpr (h f)
  rw [IsOnePI, IsOnePI, externalsAttached_relabel_iff, hV, hB]

end QED.TwoLoop.Enumeration

end
