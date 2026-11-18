/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RelabelCountertermLines

/-!
# Relabelling invariance of the value across kind sequences

Section 3.3 of `docs/TWO-LOOP-DERIVATION.md`, item 2 of section 3 of
`docs/TWO-LOOP-ENUMERATION.md`. For a contraction `C` of any kind sequence `κ` with connected
vertices (X₁₇) whose external momenta (X₁₉) sum to zero, and a relabelling `π` of the vertices
onto a kind sequence `κ'` with `κ' (π t) = κ t`, the value (T₁₀) of `relabelK π hκ C` is that of
`C`. The vertex kinds are arbitrary, so the counterterm vertices are included.

* `QED.TwoLoop.Relabel.psiMomentum₂_relabelK`, `photonMomentum₂_relabelK`: the momentum entering
  a vertex through a field (T₅), (T₆) is carried along by the line correspondence. A reversed
  photon line has its momentum negated and its head and tail exchanged, so the momentum entering
  through each photon field is unchanged.
* `QED.TwoLoop.Relabel.vertexFactor_relabelK`: the vertex factor (V₁₉) at `π t`, with the
  indices and momenta carried along, is the factor at `t`. This covers the momentum-dependent
  factors of `fermionCt`, `-i (δ₂ k̸ + δ_m m)` with `k` the momentum entering through its `Ψ`, and
  of `photonCt`, whose two photon fields keep their slot numbers.
* `QED.TwoLoop.Relabel.regulatedAmplitude₂_relabelK`: the regulated amplitude (T₈) of
  `relabelK π hκ C` at line momenta `k'` is that of `C` at the pulled-back momenta.
* `QED.TwoLoop.Relabel.contractionValue₂_relabelK`: **relabelling invariance of the value**, by
  the routing change (`LineCorr.exists_routing_change`) and the invariance of the joint
  energy-first integral under integer unimodular affine maps.
* `QED.TwoLoop.Relabel.contractionValue₂_relabelK_of_isOnePI`: the same for 1PI contractions
  under momentum conservation `∑ pOut = ∑ pIn + ∑ kIn`.
-/

@[expose] public section

namespace QED.TwoLoop.Relabel

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Routing Complex

variable {nf nA N : ℕ} {κ κ' : Fin N → Wick.VertexKind}

/-! ### Vertex factors of a given kind -/

section VertexFactor

variable (e δ₁ δ₂ δm δ₃ m : ℝ) {κ₀ : Fin N → Wick.VertexKind} (α β : Wick.FermionVertex κ₀ → Fin 4)
  (lor : Wick.PhotonSlot κ₀ → Fin 4)
  (kψ : Wick.FermionVertex κ₀ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ₀ → Fin 4 → ℝ)

theorem vertexFactor_eq_of_gauge {t : Fin N} (h : κ₀ t = .gauge) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
        (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

theorem vertexFactor_eq_of_gaugeCt {t : Fin N} (h : κ₀ t = .gaugeCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * ((δ₁ * e : ℝ) : ℂ) * Dirac.gamma (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
        (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

theorem vertexFactor_eq_of_fermionCt {t : Fin N} (h : κ₀ t = .fermionCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      -I * (((δ₂ : ℂ) • Dirac.slash (kψ ⟨t, by simp [h]⟩)
        + ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
          (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩)) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

theorem vertexFactor_eq_of_photonCt {t : Fin N} (h : κ₀ t = .photonCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      -(I / 2) * ((δ₃ *
        (Minkowski.dot (kA ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
            (kA ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩) *
          Minkowski.metric (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
            (lor ⟨t, ⟨1, by simp [h, Wick.VertexKind.photonSlots]⟩⟩) -
        kA ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩
            (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩) *
          kA ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩
            (lor ⟨t, ⟨1, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)) : ℝ) : ℂ) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

end VertexFactor

/-- **Naturality of the vertex factor** (V₁₉): the factor of vertex `π t` of `κ'`, with the
spinor and Lorentz indices and the momenta carried along by the relabelling, is the factor of
vertex `t` of `κ`. -/
theorem vertexFactor_relabelK (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t)
    (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m (α ∘ (fvMap π hκ).symm) (β ∘ (fvMap π hκ).symm)
        (lor ∘ (psMap π hκ).symm) (kψ ∘ (fvMap π hκ).symm) (kA ∘ (psMap π hκ).symm) (π t) =
      Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t := by
  rcases hk : κ t
  · rw [vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ ((hκ t).trans hk),
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ hk]
    simp only [Function.comp_apply, fvMap_symm_mk, psMap_symm_mk]
  · rw [vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ ((hκ t).trans hk),
      vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ hk]
    simp only [Function.comp_apply, fvMap_symm_mk, psMap_symm_mk]
  · rw [vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ ((hκ t).trans hk),
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ hk]
    simp only [Function.comp_apply, fvMap_symm_mk]
  · rw [vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ ((hκ t).trans hk),
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ hk]
    simp only [Function.comp_apply, psMap_symm_mk]

/-! ### The momenta entering the vertices -/

section Momenta

theorem psiMomentum₂_of_inl {κ₀ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ₀}
    {pIn : Fin nf → Fin 4 → ℝ} {k : Line C → Fin 4 → ℝ} {t : Wick.FermionVertex κ₀} {i : Fin nf}
    (h : C.1.1 (.inr t) = .inl i) : psiMomentum₂ C pIn k t = pIn i := by
  unfold psiMomentum₂
  split <;> simp_all

theorem psiMomentum₂_of_isRight {κ₀ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ₀}
    {pIn : Fin nf → Fin 4 → ℝ} {k : Line C → Fin 4 → ℝ} {t : Wick.FermionVertex κ₀}
    (hf : (C.1.1 (.inr t)).isRight) : psiMomentum₂ C pIn k t = k (.inl ⟨t, hf⟩) := by
  unfold psiMomentum₂
  split
  · rename_i i h
    simp [h] at hf
  · rfl

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ)

theorem pullK_inl (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) (f : FermionLine C) :
    (relabelCorrK π hκ C).pull k' (.inl f) = k' (.inl (fermionLineEquivK π hκ C f)) :=
  rfl

theorem pullK_inr_of_lt (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) (g : PhotonLine C)
    (h : Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head)) :
    (relabelCorrK π hκ C).pull k' (.inr g) = k' (.inr (photonLineMapK π hκ C g)) := by
  simp only [LineCorr.pull, relabelCorrK, relabelRevK, h, decide_true, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  rfl

theorem pullK_inr_of_not_lt (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) (g : PhotonLine C)
    (h : ¬ Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head)) :
    (relabelCorrK π hκ C).pull k' (.inr g) = -k' (.inr (photonLineMapK π hκ C g)) := by
  simp only [LineCorr.pull, relabelCorrK, relabelRevK, h, decide_false, Bool.not_false,
    ↓reduceIte]
  rfl

/-- The momentum entering `π t` through its `Ψ` (T₅) is that entering `t`, at the pulled-back
line momenta. -/
theorem psiMomentum₂_relabelK (pIn : Fin nf → Fin 4 → ℝ) (k' : Line (relabelK π hκ C) → Fin 4 → ℝ)
    (t : Wick.FermionVertex κ) :
    psiMomentum₂ (relabelK π hκ C) pIn k' (fvMap π hκ t) =
      psiMomentum₂ C pIn ((relabelCorrK π hκ C).pull k') t := by
  by_cases hf : (C.1.1 (.inr t)).isRight
  · have hf' : ((relabelK π hκ C).1.1 (.inr (fvMap π hκ t))).isRight :=
      (fermionLineEquivK π hκ C ⟨t, hf⟩).2
    rw [psiMomentum₂_of_isRight hf', psiMomentum₂_of_isRight hf]
    rfl
  · obtain ⟨i, hi⟩ : ∃ i, C.1.1 (.inr t) = .inl i := by
      rcases h : C.1.1 (.inr t) with i | s
      · exact ⟨i, rfl⟩
      · rw [h] at hf
        exact absurd rfl hf
    have hi' : (relabelK π hκ C).1.1 (.inr (fvMap π hκ t)) = .inl i := by
      have := relabelK_fst_apply π hκ C (.inr t)
      rw [extFK_inr, hi, extFK_inl] at this
      exact this
    rw [psiMomentum₂_of_inl hi', psiMomentum₂_of_inl hi]

/-- The momentum entering a vertex through the photon field `psMap a` (T₆) is that entering
through `a`, at the pulled-back line momenta: a reversed line has its momentum negated and its
ends exchanged. -/
theorem photonMomentum₂_relabelK (kIn : Fin nA → Fin 4 → ℝ)
    (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) (a : Wick.PhotonSlot κ) :
    photonMomentum₂ (relabelK π hκ C) kIn k' (psMap π hκ a) =
      photonMomentum₂ C kIn ((relabelCorrK π hκ C).pull k') a := by
  unfold photonMomentum₂
  congr 1
  · refine Finset.sum_congr rfl fun j _ => if_congr ?_ rfl rfl
    rw [relabelK_snd_inl, extPK_eq_inr_iff, Equiv.symm_apply_apply]
  · symm
    refine Fintype.sum_bijective (photonLineMapK π hκ C)
      ⟨photonLineMapK_injective π hκ C, photonLineMapK_surjective π hκ C⟩ _ _ fun g => ?_
    by_cases h : Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head)
    · obtain ⟨h1, h2⟩ := photonLineMapK_of_lt π hκ C g h
      rw [h1, h2, pullK_inr_of_lt π hκ C k' g h]
      simp only [(psMap π hκ).injective.eq_iff]
    · obtain ⟨h1, h2⟩ := photonLineMapK_of_not_lt π hκ C g h
      rw [h1, h2, pullK_inr_of_not_lt π hκ C k' g h]
      simp only [(psMap π hκ).injective.eq_iff]
      split_ifs <;> abel

theorem psiMomentum₂_relabelK_eq (pIn : Fin nf → Fin 4 → ℝ)
    (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) :
    psiMomentum₂ (relabelK π hκ C) pIn k' =
      psiMomentum₂ C pIn ((relabelCorrK π hκ C).pull k') ∘ (fvMap π hκ).symm := by
  funext s
  obtain ⟨t, rfl⟩ := (fvMap π hκ).surjective s
  simp only [Function.comp_apply, Equiv.symm_apply_apply, psiMomentum₂_relabelK]

theorem photonMomentum₂_relabelK_eq (kIn : Fin nA → Fin 4 → ℝ)
    (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) :
    photonMomentum₂ (relabelK π hκ C) kIn k' =
      photonMomentum₂ C kIn ((relabelCorrK π hκ C).pull k') ∘ (psMap π hκ).symm := by
  funext b
  obtain ⟨a, rfl⟩ := (psMap π hκ).surjective b
  simp only [Function.comp_apply, Equiv.symm_apply_apply, photonMomentum₂_relabelK]

end Momenta

/-! ### Flavorings and closed loops -/

section Flavor

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ)

/-- Relabelling a flavoring across kind sequences. -/
def flavMapK : Flavoring κ ≃ Flavoring κ' where
  toFun φ := ⟨φ.1 ∘ (fvMap π hκ).symm, fun s hs => φ.2 _ (by
    change κ (π.symm s.1) ≠ _
    rw [kind_symm_apply π hκ]
    exact hs)⟩
  invFun φ := ⟨φ.1 ∘ fvMap π hκ, fun t ht => φ.2 _ (by
    change κ' (π t.1) ≠ _
    rw [hκ]
    exact ht)⟩
  left_inv φ := Subtype.ext (funext fun t => by simp)
  right_inv φ := Subtype.ext (funext fun t => by simp)

@[simp] theorem flavMapK_val (φ : Flavoring κ) (t : Wick.FermionVertex κ') :
    (flavMapK π hκ φ).1 t = φ.1 ((fvMap π hκ).symm t) :=
  rfl

theorem fermionFlavor_flavMapK (φ : Flavoring κ) (x : Fin nf ⊕ Wick.FermionVertex κ) :
    fermionFlavor (flavMapK π hκ φ) (extFK π hκ x) = fermionFlavor φ x := by
  cases x <;> simp [fermionFlavor]

theorem preserves_relabelK_iff (φ : Flavoring κ) :
    Preserves (relabelK π hκ C) (flavMapK π hκ φ) ↔ Preserves C φ := by
  constructor
  · intro h x
    have := h (extFK π hκ x)
    rwa [relabelK_fst_apply, fermionFlavor_flavMapK, fermionFlavor_flavMapK] at this
  · intro h a
    obtain ⟨x, rfl⟩ := (extFK π hκ).surjective a
    rw [relabelK_fst_apply, fermionFlavor_flavMapK, fermionFlavor_flavMapK]
    exact h x

theorem sameCycle_permCongr_iff {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) (x y : α) :
    Equiv.Perm.SameCycle (e.permCongr σ) (e x) (e y) ↔ Equiv.Perm.SameCycle σ x y := by
  have hz : ∀ i : ℤ, (e.permCongr σ) ^ i = e.permCongr (σ ^ i) := fun i =>
    (map_zpow e.permCongrHom σ i).symm
  simp only [Equiv.Perm.SameCycle, hz, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    e.injective.eq_iff]

theorem sameCycle_relabelK_iff (x y : Fin nf ⊕ Wick.FermionVertex κ) :
    Equiv.Perm.SameCycle C.1.1 x y ↔
      Equiv.Perm.SameCycle (relabelK π hκ C).1.1 (extFK π hκ x) (extFK π hκ y) :=
  (sameCycle_permCongr_iff (extFK π hκ) C.1.1 x y).symm

/-- The fermion cycles of `C` and of `relabelK π hκ C`. -/
def cycleEquivK : Quotient (Equiv.Perm.SameCycle.setoid C.1.1) ≃
    Quotient (Equiv.Perm.SameCycle.setoid (relabelK π hκ C).1.1) :=
  Quotient.congr (extFK π hκ) (sameCycle_relabelK_iff π hκ C)

theorem cycleEquivK_mk (x : Fin nf ⊕ Wick.FermionVertex κ) :
    cycleEquivK π hκ C (Quotient.mk _ x) = Quotient.mk _ (extFK π hκ x) :=
  rfl

/-- The closed fermion loops of `C` and of `relabelK π hκ C`. -/
def closedLoopEquivK : ClosedLoop C ≃ ClosedLoop (relabelK π hκ C) :=
  Equiv.subtypeEquiv (cycleEquivK π hκ C) fun q => by
    refine forall_congr' fun i => not_congr ?_
    rw [← (cycleEquivK π hκ C).injective.eq_iff, cycleEquivK_mk]
    rfl

open scoped Classical in
/-- Relabelling preserves the regulator weight (X₇) of a preserved flavoring. -/
theorem loopWeight_relabelK (P : Params) {φ : Flavoring κ} (hφ : Preserves C φ) :
    loopWeight P (relabelK π hκ C) (flavMapK π hκ φ) = loopWeight P C φ := by
  have hφ' := (preserves_relabelK_iff π hκ C φ).mpr hφ
  unfold loopWeight
  symm
  apply Fintype.prod_equiv (closedLoopEquivK π hκ C)
  intro q
  have hmk : (closedLoopEquivK π hκ C q).1 = Quotient.mk _ (extFK π hκ q.1.out) := by
    change cycleEquivK π hκ C q.1 = _
    conv_lhs => rw [← Quotient.out_eq q.1]
    rfl
  have hsc : Equiv.Perm.SameCycle (relabelK π hκ C).1.1 (closedLoopEquivK π hκ C q).1.out
      (extFK π hκ q.1.out) := by
    have h : (Quotient.mk _ (closedLoopEquivK π hκ C q).1.out :
        Quotient (Equiv.Perm.SameCycle.setoid (relabelK π hκ C).1.1)) =
          Quotient.mk _ (extFK π hκ q.1.out) := by
      rw [Quotient.out_eq, hmk]
    exact Quotient.exact h
  rw [fermionFlavor_eq_of_sameCycle hφ' hsc, fermionFlavor_flavMapK]

end Flavor

/-! ### The regulated amplitude -/

section Amplitude

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ)

open scoped Classical in
/-- Relabelling the amplitude (T₇): the amplitude of `relabelK π hκ C` with the relabelled
flavoring at line momenta `k'` is the amplitude of `C` at the pulled-back line momenta. -/
theorem contractionAmplitude₂_relabelK (P : Params) (φ : Flavoring κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude₂ P (relabelK π hκ C) (flavMapK π hκ φ) pIn kIn k' αOut βIn μ =
      contractionAmplitude₂ P C φ pIn kIn ((relabelCorrK π hκ C).pull k') αOut βIn μ := by
  unfold contractionAmplitude₂
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr (fvMap π hκ) (Equiv.refl (Fin 4))) _ _
    fun α => ?_
  refine Fintype.sum_equiv (Equiv.arrowCongr (fvMap π hκ) (Equiv.refl (Fin 4))) _ _
    fun β => ?_
  refine Fintype.sum_equiv (Equiv.arrowCongr (psMap π hκ) (Equiv.refl (Fin 4))) _ _
    fun lor => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.id_comp]
  have hα : (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ↔
      (∀ i t, (relabelK π hκ C).1.1 (.inl i) = .inr t →
        (α ∘ (fvMap π hκ).symm) t = αOut i) := by
    simp only [relabelK_fst_inl, extFK_eq_inr_iff, Function.comp_apply]
    exact forall_congr' fun i => ((fvMap π hκ).symm.forall_congr_right
      (q := fun t => C.1.1 (.inl i) = .inr t → α t = αOut i)).symm
  have hβ : (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ↔
      (∀ t i, (relabelK π hκ C).1.1 (.inr t) = .inl i →
        (β ∘ (fvMap π hκ).symm) t = βIn i) := by
    simp only [relabelK_fst_inr, extFK_eq_inl_iff, Function.comp_apply]
    exact ((fvMap π hκ).symm.forall_congr_right
      (q := fun t => ∀ i, C.1.1 (.inr t) = .inl i → β t = βIn i)).symm
  have hlor : (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) ↔
      (∀ j a, (relabelK π hκ C).1.2 (.inl j) = .inr a →
        (lor ∘ (psMap π hκ).symm) a = μ j) := by
    simp only [relabelK_snd_inl, extPK_eq_inr_iff, Function.comp_apply]
    exact forall_congr' fun j => ((psMap π hκ).symm.forall_congr_right
      (q := fun a => C.1.2 (.inl j) = .inr a → lor a = μ j)).symm
  congr 1
  · exact if_congr (and_congr hα (and_congr hβ hlor)) rfl rfl
  congr 1
  congr 1
  · rw [psiMomentum₂_relabelK_eq, photonMomentum₂_relabelK_eq]
    refine Fintype.prod_equiv π _ _ fun t => ?_
    exact (vertexFactor_relabelK π hκ _ _ _ _ _ _ α β lor _ _ t).symm
  · refine Fintype.prod_equiv (fermionLineEquivK π hκ C) _ _ fun f => ?_
    simp only [Function.comp_apply, flavMapK_val, tail_fermionLineEquivK,
      fermionLineEquivK_val, Equiv.symm_apply_apply, pullK_inl]
  · refine Fintype.prod_bijective (photonLineMapK π hκ C)
      ⟨photonLineMapK_injective π hκ C, photonLineMapK_surjective π hκ C⟩ _ _ fun g => ?_
    simp only [Function.comp_apply]
    by_cases h : Wick.photonKey (psMap π hκ g.1) < Wick.photonKey (psMap π hκ g.head)
    · obtain ⟨h1, h2⟩ := photonLineMapK_of_lt π hκ C g h
      rw [h1, h2, Equiv.symm_apply_apply, Equiv.symm_apply_apply, pullK_inr_of_lt π hκ C k' g h]
    · obtain ⟨h1, h2⟩ := photonLineMapK_of_not_lt π hκ C g h
      rw [h1, h2, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        pullK_inr_of_not_lt π hκ C k' g h, photonPropagator_neg_swap]

open scoped Classical in
/-- **Relabelling the regulated amplitude** (T₈) across kind sequences: the regulated amplitude
of `relabelK π hκ C` at line momenta `k'` is that of `C` at the pulled-back line momenta. -/
theorem regulatedAmplitude₂_relabelK (P : Params) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (relabelK π hκ C) → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P (relabelK π hκ C) pIn kIn k' αOut βIn μ =
      regulatedAmplitude₂ P C pIn kIn ((relabelCorrK π hκ C).pull k') αOut βIn μ := by
  unfold regulatedAmplitude₂
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  refine Fintype.sum_equiv (flavMapK π hκ) _ _ fun φ => ?_
  by_cases hφ : Preserves C φ
  · have hφ' := (preserves_relabelK_iff π hκ C φ).mpr hφ
    simp only [hφ, hφ', ↓reduceIte, loopWeight_relabelK π hκ C P hφ,
      contractionAmplitude₂_relabelK]
  · have hφ' : ¬ Preserves (relabelK π hκ C) (flavMapK π hκ φ) :=
      mt (preserves_relabelK_iff π hκ C φ).mp hφ
    simp only [hφ, hφ', ↓reduceIte]

end Amplitude

/-! ### The value -/

section Value

/-- **Relabelling invariance of the value** (T₁₀) across kind sequences: for a contraction `C`
of `κ` with connected vertices (X₁₇) whose external momenta (X₁₉) sum to zero, and `π` with
`κ' (π t) = κ t`, the value of `relabelK π hκ C` is that of `C`. -/
theorem contractionValue₂_relabelK (P : Params) (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ) (hV : VerticesConnected C)
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue₂ P (relabelK π hκ C) pOut pIn kIn αOut βIn μ =
      contractionValue₂ P C pOut pIn kIn αOut βIn μ := by
  have hV' := (verticesConnected_relabelK_iff π hκ C).mpr hV
  have hL' := loopCount_relabelK π hκ C hV
  obtain ⟨M, hM, a, h⟩ := (relabelCorrK π hκ C).exists_routing_change hV hV'
    (externalMomentum_relabelK π hκ C pOut pIn kIn) hsum rfl hL'
  rw [contractionValue₂_eq_of_loopCount P hL', contractionValue₂_eq_of_loopCount P rfl]
  simp only [regulatedAmplitude₂_relabelK, h]
  exact JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add _
    (fun ℓ => (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) M hM a

/-- **Relabelling invariance for 1PI contractions** across kind sequences, under momentum
conservation `∑ pOut = ∑ pIn + ∑ kIn`. -/
theorem contractionValue₂_relabelK_of_isOnePI (P : Params) (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction nf nA κ} (hC : IsOnePI C)
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue₂ P (relabelK π hκ C) pOut pIn kIn αOut βIn μ =
      contractionValue₂ P C pOut pIn kIn αOut βIn μ :=
  contractionValue₂_relabelK P π hκ C hC.2.1
    (by rw [sum_externalMomentum hC.1, hmom, sub_self]) αOut βIn μ

end Value

end QED.TwoLoop.Relabel

end
