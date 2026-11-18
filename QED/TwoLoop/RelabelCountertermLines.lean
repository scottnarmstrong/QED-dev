/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RelabelInvariance

/-!
# Relabelling the vertices across kind sequences: the line correspondence

Section 3.3 of `docs/TWO-LOOP-DERIVATION.md`, item 2 of section 3 of
`docs/TWO-LOOP-ENUMERATION.md`. The relabelling of `QED/TwoLoop/EnumerationRelabel.lean` acts on
the contractions of `N` gauge vertices. A term of the Wick expansion with counterterm vertices
has a kind sequence `κ` that is not constant, and relabelling the vertices by `π` changes the
sequence: vertex `t` of kind `κ t` becomes vertex `π t` of `κ'` with `κ' (π t) = κ t`. This file
defines that relabelling and proves the combinatorial half of its invariance.

* `QED.TwoLoop.Relabel.relabelK π hκ C`: the contraction of `κ'` obtained from a contraction `C`
  of `κ`, for `hκ : ∀ t, κ' (π t) = κ t`; the photon field `k` of vertex `t` becomes the photon
  field `k` of vertex `π t`.
* `QED.TwoLoop.Relabel.relabelCorrK`: the internal lines correspond (`LineCorr`), with ends moved
  by `π`; the photon lines whose indexing field changes are reversed.
* `QED.TwoLoop.Relabel.externalMomentum_relabelK`, `verticesConnected_relabelK_iff`,
  `loopCount_relabelK`, `isOnePI_relabelK_iff`, `fermionSign_relabelK`: the external momenta
  match vertex by vertex, and connectivity, the number of loops, one-particle irreducibility and
  the fermionic sign are preserved.

The proofs follow those for gauge vertices; only the maps on the fields change.
-/

@[expose] public section

namespace QED.TwoLoop.Relabel

open QED.WickModel QED.TwoLoop.Enumeration Relation

variable {nf nA N : ℕ} {κ κ' : Fin N → Wick.VertexKind}

/-! ### Relabelling on fields -/

section Fields

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t)

include hκ in
theorem kind_symm_apply (s : Fin N) : κ (π.symm s) = κ' s := by
  rw [← hκ, π.apply_symm_apply]

/-- Relabelling the fermion vertices across kind sequences. -/
def fvMap : Wick.FermionVertex κ ≃ Wick.FermionVertex κ' where
  toFun t := ⟨π t.1, by rw [hκ]; exact t.2⟩
  invFun s := ⟨π.symm s.1, by rw [kind_symm_apply π hκ]; exact s.2⟩
  left_inv t := Subtype.ext (π.symm_apply_apply t.1)
  right_inv s := Subtype.ext (π.apply_symm_apply s.1)

/-- Relabelling the photon fields across kind sequences: the field `k` of vertex `t` becomes the
field `k` of vertex `π t`. -/
def psMap : Wick.PhotonSlot κ ≃ Wick.PhotonSlot κ' where
  toFun a := ⟨π a.1, Fin.cast (by rw [hκ]) a.2⟩
  invFun b := ⟨π.symm b.1, Fin.cast (by rw [kind_symm_apply π hκ]) b.2⟩
  left_inv a := Sigma.ext (π.symm_apply_apply a.1) ((Fin.heq_ext_iff (by simp)).mpr rfl)
  right_inv b := Sigma.ext (π.apply_symm_apply b.1) ((Fin.heq_ext_iff (by simp)).mpr rfl)

@[simp] theorem fvMap_val (t : Wick.FermionVertex κ) : (fvMap π hκ t).1 = π t.1 := rfl

@[simp] theorem psMap_fst (a : Wick.PhotonSlot κ) : (psMap π hκ a).1 = π a.1 := rfl

@[simp] theorem psMap_snd_val (a : Wick.PhotonSlot κ) : (psMap π hκ a).2.val = a.2.val := rfl

theorem fvMap_symm_mk (t : Fin N) (h : κ' (π t) ≠ .photonCt) :
    (fvMap π hκ).symm ⟨π t, h⟩ = ⟨t, by rw [← hκ]; exact h⟩ := by
  rw [Equiv.symm_apply_eq]
  rfl

theorem psMap_symm_mk (t : Fin N) (i : ℕ) (h : i < (κ' (π t)).photonSlots) :
    (psMap π hκ).symm ⟨π t, ⟨i, h⟩⟩ = ⟨t, ⟨i, by rw [← hκ]; exact h⟩⟩ := by
  rw [Equiv.symm_apply_eq]
  rfl

/-- The relabelling on the fermion fields, the externals fixed. -/
def extFK : Fin nf ⊕ Wick.FermionVertex κ ≃ Fin nf ⊕ Wick.FermionVertex κ' :=
  Equiv.sumCongr (Equiv.refl _) (fvMap π hκ)

/-- The relabelling on the photon fields, the externals fixed. -/
def extPK : Fin nA ⊕ Wick.PhotonSlot κ ≃ Fin nA ⊕ Wick.PhotonSlot κ' :=
  Equiv.sumCongr (Equiv.refl _) (psMap π hκ)

@[simp] theorem extFK_inl (i : Fin nf) : extFK π hκ (.inl i) = .inl i := rfl

@[simp] theorem extFK_inr (t : Wick.FermionVertex κ) :
    extFK (nf := nf) π hκ (.inr t) = .inr (fvMap π hκ t) := rfl

@[simp] theorem extPK_inl (i : Fin nA) : extPK π hκ (.inl i) = .inl i := rfl

@[simp] theorem extPK_inr (a : Wick.PhotonSlot κ) :
    extPK (nA := nA) π hκ (.inr a) = .inr (psMap π hκ a) := rfl

/-- **Relabelling a contraction across kind sequences**: vertex `t` of `κ` becomes vertex `π t`
of `κ'`, where `κ' (π t) = κ t`. -/
def relabelK (C : Contraction nf nA κ) : Contraction nf nA κ' :=
  ⟨((extFK π hκ).permCongr C.1.1, (extPK π hκ).permCongr C.1.2), fun b => by
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, (C.2 _).1, Equiv.apply_symm_apply,
      true_and]
    intro h
    exact (C.2 _).2 ((extPK π hκ).injective (h.trans ((extPK π hκ).apply_symm_apply b).symm))⟩

variable (C : Contraction nf nA κ)

theorem relabelK_fst_apply (x : Fin nf ⊕ Wick.FermionVertex κ) :
    (relabelK π hκ C).1.1 (extFK π hκ x) = extFK π hκ (C.1.1 x) := by
  simp [relabelK]

theorem relabelK_snd_apply (x : Fin nA ⊕ Wick.PhotonSlot κ) :
    (relabelK π hκ C).1.2 (extPK π hκ x) = extPK π hκ (C.1.2 x) := by
  simp [relabelK]

/-- Relabelling preserves the fermionic sign (X₅). -/
theorem fermionSign_relabelK : fermionSign (relabelK π hκ C) = fermionSign C := by
  simp only [fermionSign, relabelK, Equiv.Perm.sign_permCongr]
  rw [Fintype.card_congr (fvMap π hκ)]

theorem extFK_eq_inl_iff (y : Fin nf ⊕ Wick.FermionVertex κ) (i : Fin nf) :
    extFK π hκ y = .inl i ↔ y = .inl i := by
  cases y <;> simp

theorem extFK_eq_inr_iff (y : Fin nf ⊕ Wick.FermionVertex κ) (t : Wick.FermionVertex κ') :
    extFK π hκ y = .inr t ↔ y = .inr ((fvMap π hκ).symm t) := by
  cases y <;> simp [Equiv.eq_symm_apply]

theorem extPK_eq_inr_iff (y : Fin nA ⊕ Wick.PhotonSlot κ) (a : Wick.PhotonSlot κ') :
    extPK π hκ y = .inr a ↔ y = .inr ((psMap π hκ).symm a) := by
  cases y <;> simp [Equiv.eq_symm_apply]

theorem relabelK_fst_inl (i : Fin nf) :
    (relabelK π hκ C).1.1 (.inl i) = extFK π hκ (C.1.1 (.inl i)) :=
  relabelK_fst_apply π hκ C (.inl i)

theorem relabelK_fst_inr (t : Wick.FermionVertex κ') :
    (relabelK π hκ C).1.1 (.inr t) = extFK π hκ (C.1.1 (.inr ((fvMap π hκ).symm t))) := by
  have := relabelK_fst_apply π hκ C (.inr ((fvMap π hκ).symm t))
  simpa using this

theorem relabelK_snd_inl (j : Fin nA) :
    (relabelK π hκ C).1.2 (.inl j) = extPK π hκ (C.1.2 (.inl j)) :=
  relabelK_snd_apply π hκ C (.inl j)

/-- The external momentum flowing into `π v` in `relabelK π hκ C` is that flowing into `v` in
`C`. -/
theorem externalMomentum_relabelK (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (v : Fin N) :
    externalMomentum (relabelK π hκ C) pOut pIn kIn (π v) =
      externalMomentum C pOut pIn kIn v := by
  have hF : ∀ Q : Wick.FermionVertex κ' → Prop, (∃ t, Q t) ↔ ∃ s, Q (fvMap π hκ s) :=
    fun Q => (fvMap π hκ).exists_congr_right.symm
  have hP : ∀ Q : Wick.PhotonSlot κ' → Prop, (∃ a, Q a) ↔ ∃ b, Q (psMap π hκ b) :=
    fun Q => (psMap π hκ).exists_congr_right.symm
  unfold externalMomentum
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
  · refine (hF _).trans ?_
    simp only [fvMap_val, π.injective.eq_iff, relabelK_fst_inr, Equiv.symm_apply_apply,
      extFK_eq_inl_iff]
  · refine (hP _).trans ?_
    simp only [psMap_fst, π.injective.eq_iff, relabelK_snd_inl, extPK_eq_inr_iff,
      Equiv.symm_apply_apply]
  · refine (hF _).trans ?_
    simp only [fvMap_val, π.injective.eq_iff, relabelK_fst_inl, extFK_eq_inr_iff,
      Equiv.symm_apply_apply]

theorem externalsAttached_relabelK_iff :
    ExternalsAttached (relabelK π hκ C) ↔ ExternalsAttached C := by
  have kF : ∀ x : Fin nf ⊕ Wick.FermionVertex κ, ∀ j,
      extFK π hκ x ≠ .inl j ↔ x ≠ .inl j := by
    rintro (i | t) j <;> simp
  have kP : ∀ x : Fin nA ⊕ Wick.PhotonSlot κ, ∀ j,
      extPK π hκ x ≠ .inl j ↔ x ≠ .inl j := by
    rintro (i | t) j <;> simp
  simp only [ExternalsAttached, relabelK_fst_inl, relabelK_snd_inl, kF, kP]

end Fields

/-! ### The internal lines correspond -/

section Lines

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ)

/-- The fermion lines of `C` and of `relabelK π hκ C`. -/
def fermionLineEquivK : FermionLine C ≃ FermionLine (relabelK π hκ C) :=
  Equiv.subtypeEquiv (fvMap π hκ) fun t => by
    have := relabelK_fst_apply π hκ C (.inr t)
    simp only [extFK_inr] at this
    rw [this]
    cases C.1.1 (.inr t) <;> rfl

theorem fermionLineEquivK_val (f : FermionLine C) :
    (fermionLineEquivK π hκ C f).1 = fvMap π hκ f.1 :=
  rfl

theorem fermionLineEquivK_ends (f : FermionLine C) :
    Line.ends (Sum.inl (fermionLineEquivK π hκ C f) : Line (relabelK π hκ C)) =
      (π (Line.ends (Sum.inl f : Line C)).1, π (Line.ends (Sum.inl f : Line C)).2) := by
  obtain ⟨s, hs⟩ : ∃ s, C.1.1 (.inr f.1) = .inr s := Sum.isRight_iff.mp f.2
  have h' : (relabelK π hκ C).1.1 (.inr (fermionLineEquivK π hκ C f).1) =
      .inr (fvMap π hκ s) := by
    have := relabelK_fst_apply π hκ C (.inr f.1)
    simp only [extFK_inr, hs] at this
    exact this
  simp only [Line.ends, tail_eq _ h', tail_eq _ hs]
  rfl

theorem tail_fermionLineEquivK (f : FermionLine C) :
    (fermionLineEquivK π hκ C f).tail = fvMap π hκ f.tail :=
  Subtype.ext (congrArg Prod.fst (fermionLineEquivK_ends π hκ C f))

theorem relabelK_snd_inr (a b : Wick.PhotonSlot κ) (h : C.1.2 (.inr a) = .inr b) :
    (relabelK π hκ C).1.2 (.inr (psMap π hκ a)) = .inr (psMap π hκ b) := by
  have := relabelK_snd_apply π hκ C (.inr a)
  simp only [extPK_inr, h] at this
  exact this

theorem psMap_ne {a b : Wick.PhotonSlot κ} (h : C.1.2 (.inr a) = .inr b) :
    Wick.photonKey (psMap π hκ a) ≠ Wick.photonKey (psMap π hκ b) := fun hk => by
  have hab := (psMap π hκ).injective (Chord.photonKey_injective hk)
  subst hab
  exact (C.2 _).2 h

/-- The image of a photon line: the line of the two relabelled fields. -/
def photonLineMapK (g : PhotonLine C) : PhotonLine (relabelK π hκ C) :=
  if h : Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head) then
    ⟨psMap π hκ g.1, psMap π hκ g.head,
      relabelK_snd_inr π hκ C _ _ (LoopBound.apply_inr_photonLine g), h⟩
  else
    ⟨psMap π hκ g.head, psMap π hκ g.1,
      relabelK_snd_inr π hκ C _ _ (LoopBound.apply_inr_head g),
      lt_of_le_of_ne (not_lt.mp h)
        (psMap_ne π hκ C (LoopBound.apply_inr_photonLine g)).symm⟩

theorem photonLineMapK_of_lt (g : PhotonLine C)
    (h : Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head)) :
    (photonLineMapK π hκ C g).1 = psMap π hκ g.1 ∧
      (photonLineMapK π hκ C g).head = psMap π hκ g.head := by
  have e : photonLineMapK π hκ C g = ⟨psMap π hκ g.1, psMap π hκ g.head,
      relabelK_snd_inr π hκ C _ _ (LoopBound.apply_inr_photonLine g), h⟩ := by
    unfold photonLineMapK
    simp only [h, ↓reduceDIte]
  rw [e]
  exact ⟨rfl, head_eq _ (relabelK_snd_inr π hκ C _ _ (LoopBound.apply_inr_photonLine g))⟩

theorem photonLineMapK_of_not_lt (g : PhotonLine C)
    (h : ¬ Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head)) :
    (photonLineMapK π hκ C g).1 = psMap π hκ g.head ∧
      (photonLineMapK π hκ C g).head = psMap π hκ g.1 := by
  have e : photonLineMapK π hκ C g = ⟨psMap π hκ g.head, psMap π hκ g.1,
      relabelK_snd_inr π hκ C _ _ (LoopBound.apply_inr_head g),
      lt_of_le_of_ne (not_lt.mp h)
        (psMap_ne π hκ C (LoopBound.apply_inr_photonLine g)).symm⟩ := by
    unfold photonLineMapK
    simp only [h, ↓reduceDIte]
  rw [e]
  exact ⟨rfl, head_eq _ (relabelK_snd_inr π hκ C _ _ (LoopBound.apply_inr_head g))⟩

theorem photonLineMapK_cases (g : PhotonLine C) :
    ((photonLineMapK π hκ C g).1 = psMap π hκ g.1 ∧
        (photonLineMapK π hκ C g).head = psMap π hκ g.head) ∨
      ((photonLineMapK π hκ C g).1 = psMap π hκ g.head ∧
        (photonLineMapK π hκ C g).head = psMap π hκ g.1) := by
  by_cases h : Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head)
  · exact Or.inl (photonLineMapK_of_lt π hκ C g h)
  · exact Or.inr (photonLineMapK_of_not_lt π hκ C g h)

theorem photonLineMapK_injective : Function.Injective (photonLineMapK π hκ C) := by
  intro g₁ g₂ h
  have k₁ := LoopBound.photonKey_lt_head g₁
  have k₂ := LoopBound.photonKey_lt_head g₂
  have h₁ := congrArg Subtype.val h
  have hh := congrArg PhotonLine.head h
  apply Subtype.ext
  rcases photonLineMapK_cases π hκ C g₁ with ⟨a₁, b₁⟩ | ⟨a₁, b₁⟩ <;>
    rcases photonLineMapK_cases π hκ C g₂ with ⟨a₂, b₂⟩ | ⟨a₂, b₂⟩
  · exact (psMap π hκ).injective (a₁.symm.trans (h₁.trans a₂))
  · have x : g₁.1 = g₂.head := (psMap π hκ).injective (a₁.symm.trans (h₁.trans a₂))
    have y : g₁.head = g₂.1 := (psMap π hκ).injective (b₁.symm.trans (hh.trans b₂))
    rw [x, y] at k₁
    exact absurd (k₁.trans k₂) (lt_irrefl _)
  · have x : g₁.head = g₂.1 := (psMap π hκ).injective (a₁.symm.trans (h₁.trans a₂))
    have y : g₁.1 = g₂.head := (psMap π hκ).injective (b₁.symm.trans (hh.trans b₂))
    rw [x, y] at k₁
    exact absurd (k₁.trans k₂) (lt_irrefl _)
  · exact (psMap π hκ).injective (b₁.symm.trans (hh.trans b₂))

theorem photonLineMapK_surjective : Function.Surjective (photonLineMapK π hκ C) := by
  intro g'
  obtain ⟨b', hb', hk'⟩ := g'.2
  obtain ⟨a, ha⟩ := (psMap π hκ).surjective g'.1
  have h1 := relabelK_snd_apply π hκ C (.inr a)
  rw [extPK_inr, ha, hb'] at h1
  obtain ⟨c, hc⟩ : ∃ c, C.1.2 (.inr a) = .inr c := by
    rcases hC : C.1.2 (.inr a) with i | c
    · rw [hC] at h1
      cases h1
    · exact ⟨c, rfl⟩
  rw [hc, extPK_inr] at h1
  have hgb : psMap π hκ c = b' := (Sum.inr_injective h1).symm
  have hkac : Wick.photonKey a ≠ Wick.photonKey c := fun hk =>
    (C.2 _).2 (hc.trans (congrArg _ (Chord.photonKey_injective hk).symm))
  rcases lt_or_gt_of_ne hkac with hlt | hlt
  · have hhead : PhotonLine.head (C := C) ⟨a, c, hc, hlt⟩ = c := head_eq _ hc
    have hcond : Wick.photonKey (psMap π hκ (⟨a, c, hc, hlt⟩ : PhotonLine C).1) <
        Wick.photonKey (psMap π hκ (PhotonLine.head (C := C) ⟨a, c, hc, hlt⟩)) := by
      rw [hhead, hgb]
      exact ha ▸ hk'
    refine ⟨⟨a, c, hc, hlt⟩, Subtype.ext ?_⟩
    rw [(photonLineMapK_of_lt π hκ C _ hcond).1]
    exact ha
  · have hca : C.1.2 (.inr c) = .inr a := by rw [← hc, (C.2 _).1]
    have hhead : PhotonLine.head (C := C) ⟨c, a, hca, hlt⟩ = a := head_eq _ hca
    have hcond : ¬ Wick.photonKey (psMap π hκ (⟨c, a, hca, hlt⟩ : PhotonLine C).1) <
        Wick.photonKey (psMap π hκ (PhotonLine.head (C := C) ⟨c, a, hca, hlt⟩)) := by
      rw [hhead]
      change ¬ Wick.photonKey (psMap π hκ c) < _
      rw [hgb, ha]
      exact not_lt.mpr hk'.le
    refine ⟨⟨c, a, hca, hlt⟩, Subtype.ext ?_⟩
    rw [(photonLineMapK_of_not_lt π hκ C _ hcond).1, hhead, ha]

/-- The internal lines of `C` and of `relabelK π hκ C`. -/
noncomputable def lineEquivK : Line C ≃ Line (relabelK π hκ C) :=
  Equiv.sumCongr (fermionLineEquivK π hκ C)
    (Equiv.ofBijective (photonLineMapK π hκ C)
      ⟨photonLineMapK_injective π hκ C, photonLineMapK_surjective π hκ C⟩)

theorem lineEquivK_ends (f : Line C) :
    (lineEquivK π hκ C f).ends = (π f.ends.1, π f.ends.2) ∨
      (lineEquivK π hκ C f).ends = (π f.ends.2, π f.ends.1) := by
  rcases f with f | g
  · exact Or.inl (fermionLineEquivK_ends π hκ C f)
  · rcases photonLineMapK_cases π hκ C g with ⟨a, b⟩ | ⟨a, b⟩
    · left
      change ((photonLineMapK π hκ C g).1.1, (photonLineMapK π hκ C g).head.1) = _
      rw [a, b]
      rfl
    · right
      change ((photonLineMapK π hκ C g).1.1, (photonLineMapK π hκ C g).head.1) = _
      rw [a, b]
      rfl

theorem joined_relabelK_iff (S : Set (Line C)) (u w : Fin N) :
    Joined (relabelK π hκ C) (lineEquivK π hκ C '' S) (π u) (π w) ↔ Joined C S u w := by
  constructor
  · rintro ⟨f', hf', h⟩
    obtain ⟨f, rfl⟩ := (lineEquivK π hκ C).surjective f'
    refine ⟨f, fun hf => hf' ⟨f, hf, rfl⟩, ?_⟩
    rcases lineEquivK_ends π hκ C f with he | he <;> rw [he] at h <;>
      rcases h with h | h <;> simp only [Prod.mk.injEq, π.injective.eq_iff] at h
    · exact Or.inl (Prod.ext h.1 h.2)
    · exact Or.inr (Prod.ext h.1 h.2)
    · exact Or.inr (Prod.ext h.2 h.1)
    · exact Or.inl (Prod.ext h.2 h.1)
  · rintro ⟨f, hf, h⟩
    refine ⟨lineEquivK π hκ C f,
      fun ⟨g, hg, he⟩ => hf ((lineEquivK π hκ C).injective he ▸ hg), ?_⟩
    rcases lineEquivK_ends π hκ C f with he | he <;> rw [he] <;> rcases h with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem reflTransGen_relabelK_iff (S : Set (Line C)) (u w : Fin N) :
    ReflTransGen (Joined (relabelK π hκ C) (lineEquivK π hκ C '' S)) (π u) (π w) ↔
      ReflTransGen (Joined C S) u w := by
  constructor
  · intro h
    have := ReflTransGen.lift π.symm (by
      intro a b hab
      rw [← π.apply_symm_apply a, ← π.apply_symm_apply b] at hab
      exact (joined_relabelK_iff π hκ C S _ _).mp hab) (π u) (π w) h
    simpa [Function.onFun] using this
  · intro h
    exact ReflTransGen.lift π (by
      intro a b hab
      exact (joined_relabelK_iff π hκ C S a b).mpr hab) u w h

/-- The lines reversed by relabelling: the photon lines whose indexing field changes. -/
def relabelRevK : Line C → Bool
  | .inl _ => false
  | .inr g => !decide (Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head))

/-- **The line correspondence of a relabelling across kind sequences**: ends moved by `π`, the
photon lines whose indexing field changes reversed. -/
noncomputable def relabelCorrK : LineCorr C (relabelK π hκ C) where
  vtx := π
  line := lineEquivK π hκ C
  rev := relabelRevK π hκ C
  ends_line f := by
    rcases f with f | g
    · simp only [relabelRevK, Bool.false_eq_true, ↓reduceIte]
      exact fermionLineEquivK_ends π hκ C f
    · by_cases h : Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head)
      · obtain ⟨h1, h2⟩ := photonLineMapK_of_lt π hκ C g h
        simp only [relabelRevK, h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        change ((photonLineMapK π hκ C g).1.1, (photonLineMapK π hκ C g).head.1) = _
        rw [h1, h2]
        rfl
      · obtain ⟨h1, h2⟩ := photonLineMapK_of_not_lt π hκ C g h
        simp only [relabelRevK, h, decide_false, Bool.not_false, ↓reduceIte]
        change ((photonLineMapK π hκ C g).1.1, (photonLineMapK π hκ C g).head.1) = _
        rw [h1, h2]
        rfl

theorem verticesConnected_relabelK_iff :
    VerticesConnected (relabelK π hκ C) ↔ VerticesConnected C := by
  have h := reflTransGen_relabelK_iff π hκ C ∅
  simp only [Set.image_empty] at h
  constructor
  · intro hC u w
    exact (h u w).mp (hC _ _)
  · intro hC u w
    rw [← π.apply_symm_apply u, ← π.apply_symm_apply w]
    exact (h _ _).mpr (hC _ _)

theorem loopCount_eq_zero_of_fin_zero {κ₀ : Fin 0 → Wick.VertexKind}
    (C₀ : Contraction nf nA κ₀) : loopCount C₀ = 0 := by
  unfold loopCount
  exact Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun f _ => f.ends.1.elim0)

/-- **Relabelling preserves the number of loops** of a contraction with connected vertices. -/
theorem loopCount_relabelK (hV : VerticesConnected C) :
    loopCount (relabelK π hκ C) = loopCount C := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [loopCount_eq_zero_of_fin_zero, loopCount_eq_zero_of_fin_zero]
  · have h1 := LoopBoundTwo.loopCount_add_eq hV hN
    have h2 := LoopBoundTwo.loopCount_add_eq ((verticesConnected_relabelK_iff π hκ C).mpr hV) hN
    have h3 : Nat.card (Line (relabelK π hκ C)) = Nat.card (Line C) :=
      Nat.card_congr (lineEquivK π hκ C).symm
    omega

/-- **Relabelling preserves one-particle irreducibility** (X₁₈). -/
theorem isOnePI_relabelK_iff : IsOnePI (relabelK π hκ C) ↔ IsOnePI C := by
  have hB : (∀ f : Line (relabelK π hκ C), ¬ IsBridge f) ↔ ∀ f : Line C, ¬ IsBridge f := by
    have key : ∀ f : Line C, IsBridge (lineEquivK π hκ C f) ↔ IsBridge f := fun f => by
      have h := reflTransGen_relabelK_iff π hκ C {f} f.ends.1 f.ends.2
      rw [Set.image_singleton] at h
      unfold IsBridge
      rw [not_iff_not, ← h]
      rcases lineEquivK_ends π hκ C f with he | he <;> rw [he]
      exact ⟨LoopBound.reflTransGen_joined_symm, LoopBound.reflTransGen_joined_symm⟩
    constructor
    · intro h f
      exact (key f).not.mp (h _)
    · intro h f'
      obtain ⟨f, rfl⟩ := (lineEquivK π hκ C).surjective f'
      exact (key f).not.mpr (h f)
  rw [IsOnePI, IsOnePI, externalsAttached_relabelK_iff, verticesConnected_relabelK_iff, hB]

end Lines

end QED.TwoLoop.Relabel

end
