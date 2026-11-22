/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RelabelCountertermValue
public import QED.TwoLoop.CountertermInsertionBasic

/-!
# Changing `gaugeCt` vertices into `gauge` vertices, all other kinds kept

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, classes
`CD2`–`CD4`. For any kind sequence `κ`, let `gKinds κ` replace each `gaugeCt` by `gauge` and keep
the other kinds (`fermionCt`, `photonCt` included). Both `gauge` and `gaugeCt` carry one `Ψ̄ Ψ`
pair and one photon field, so the fermion vertices and photon fields of `κ` and `gKinds κ` agree
(`fvGK`, `psGK`) and a contraction `C` of `κ` is a contraction `toGK C` of `gKinds κ` with the
same pairings and lines (`corrGK`, a line correspondence fixing the vertices and orientations).

* `contractionAmplitude₂_toGK`: the amplitude (T₇) of `C` at the all-electron flavouring is
  `δ₁^{#gaugeCt}` (`ctWK`) times that of `toGK C`;
* **`contractionValue₂_toGK`**: for an open-line contraction (no closed fermion loop) with
  connected vertices whose external momenta sum to zero, the value (T₁₀) of `C` is `ctWK` times
  that of `toGK C`, at every `ε`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCPauli

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Relabel
open QED.TwoLoop.Enumeration (tail_eq head_eq)

/-- `gaugeCt` becomes `gauge`; every other kind is kept. -/
def gKind : Wick.VertexKind → Wick.VertexKind
  | .gaugeCt => .gauge
  | k => k

/-- The kind sequence with every `gaugeCt` replaced by `gauge`. -/
def gKinds {N : ℕ} (κ : Fin N → Wick.VertexKind) : Fin N → Wick.VertexKind := fun t => gKind (κ t)

theorem gKind_ne_photonCt_iff (k : Wick.VertexKind) : k ≠ .photonCt ↔ gKind k ≠ .photonCt := by
  cases k <;> decide

theorem gKind_photonSlots (k : Wick.VertexKind) : k.photonSlots = (gKind k).photonSlots := by
  cases k <;> rfl

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Fields -/

section Fields

/-- The fermion vertices of `κ` are those of `gKinds κ`. -/
def fvGK : Wick.FermionVertex κ ≃ Wick.FermionVertex (gKinds κ) :=
  Equiv.subtypeEquivRight fun t => gKind_ne_photonCt_iff (κ t)

/-- The photon fields of `κ` are those of `gKinds κ`. -/
def psGK : Wick.PhotonSlot κ ≃ Wick.PhotonSlot (gKinds κ) :=
  Equiv.sigmaCongrRight fun t => finCongr (gKind_photonSlots (κ t))

@[simp] theorem fvGK_val (t : Wick.FermionVertex κ) : (fvGK t).1 = t.1 := rfl

@[simp] theorem fvGK_symm_val (t : Wick.FermionVertex (gKinds κ)) : (fvGK.symm t).1 = t.1 := rfl

@[simp] theorem psGK_fst (a : Wick.PhotonSlot κ) : (psGK a).1 = a.1 := rfl

@[simp] theorem psGK_symm_mk (t : Fin N) (i : ℕ) (h : i < (gKinds κ t).photonSlots) :
    psGK.symm (⟨t, ⟨i, h⟩⟩ : Wick.PhotonSlot (gKinds κ)) =
      ⟨t, ⟨i, (gKind_photonSlots (κ t)).symm ▸ h⟩⟩ := rfl

@[simp] theorem fvGK_symm_mk (t : Fin N) (h : gKinds κ t ≠ .photonCt) :
    fvGK.symm (⟨t, h⟩ : Wick.FermionVertex (gKinds κ)) =
      ⟨t, (gKind_ne_photonCt_iff (κ t)).mpr h⟩ := rfl

/-- The fermion fields, the externals fixed. -/
def extFGK : Fin nf ⊕ Wick.FermionVertex κ ≃ Fin nf ⊕ Wick.FermionVertex (gKinds κ) :=
  Equiv.sumCongr (Equiv.refl _) fvGK

/-- The photon fields, the externals fixed. -/
def extPGK : Fin nA ⊕ Wick.PhotonSlot κ ≃ Fin nA ⊕ Wick.PhotonSlot (gKinds κ) :=
  Equiv.sumCongr (Equiv.refl _) psGK

@[simp] theorem extFGK_inl (i : Fin nf) : extFGK (κ := κ) (.inl i) = .inl i := rfl

@[simp] theorem extFGK_inr (t : Wick.FermionVertex κ) :
    extFGK (nf := nf) (.inr t) = .inr (fvGK t) := rfl

@[simp] theorem extPGK_inl (i : Fin nA) : extPGK (κ := κ) (.inl i) = .inl i := rfl

@[simp] theorem extPGK_inr (a : Wick.PhotonSlot κ) :
    extPGK (nA := nA) (.inr a) = .inr (psGK a) := rfl

/-- **A contraction of `κ` as a contraction of `gKinds κ`.** -/
def toGK (C : Contraction nf nA κ) : Contraction nf nA (gKinds κ) :=
  ⟨(extFGK.permCongr C.1.1, extPGK.permCongr C.1.2), fun b => by
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, (C.2 _).1, Equiv.apply_symm_apply,
      true_and]
    intro h
    exact (C.2 _).2 (extPGK.injective (h.trans (extPGK.apply_symm_apply b).symm))⟩

variable (C : Contraction nf nA κ)

theorem toGK_fst_apply (x : Fin nf ⊕ Wick.FermionVertex κ) :
    (toGK C).1.1 (extFGK x) = extFGK (C.1.1 x) := by
  simp [toGK]

theorem toGK_snd_apply (x : Fin nA ⊕ Wick.PhotonSlot κ) :
    (toGK C).1.2 (extPGK x) = extPGK (C.1.2 x) := by
  simp [toGK]

theorem extFGK_eq_inl_iff (y : Fin nf ⊕ Wick.FermionVertex κ) (i : Fin nf) :
    extFGK y = .inl i ↔ y = .inl i := by
  cases y <;> simp

theorem extFGK_eq_inr_iff (y : Fin nf ⊕ Wick.FermionVertex κ)
    (t : Wick.FermionVertex (gKinds κ)) : extFGK y = .inr t ↔ y = .inr (fvGK.symm t) := by
  cases y <;> simp [Equiv.eq_symm_apply]

theorem extPGK_eq_inr_iff (y : Fin nA ⊕ Wick.PhotonSlot κ) (a : Wick.PhotonSlot (gKinds κ)) :
    extPGK y = .inr a ↔ y = .inr (psGK.symm a) := by
  cases y <;> simp [Equiv.eq_symm_apply]

theorem toGK_fst_inl (i : Fin nf) : (toGK C).1.1 (.inl i) = extFGK (C.1.1 (.inl i)) :=
  toGK_fst_apply C (.inl i)

theorem toGK_fst_inr (t : Wick.FermionVertex (gKinds κ)) :
    (toGK C).1.1 (.inr t) = extFGK (C.1.1 (.inr (fvGK.symm t))) := by
  simpa using toGK_fst_apply C (.inr (fvGK.symm t))

theorem toGK_snd_inl (j : Fin nA) : (toGK C).1.2 (.inl j) = extPGK (C.1.2 (.inl j)) :=
  toGK_snd_apply C (.inl j)

theorem toGK_snd_inr {a b : Wick.PhotonSlot κ} (h : C.1.2 (.inr a) = .inr b) :
    (toGK C).1.2 (.inr (psGK a)) = .inr (psGK b) := by
  have := toGK_snd_apply C (.inr a)
  simp only [extPGK_inr, h] at this
  exact this

/-- The external momentum flowing into `v` is the same in `toGK C` and in `C`. -/
theorem externalMomentum_toGK (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (v : Fin N) :
    externalMomentum (toGK C) pOut pIn kIn v = externalMomentum C pOut pIn kIn v := by
  have hF : ∀ Q : Wick.FermionVertex (gKinds κ) → Prop, (∃ t, Q t) ↔ ∃ s, Q (fvGK s) :=
    fun Q => fvGK.exists_congr_right.symm
  have hP : ∀ Q : Wick.PhotonSlot (gKinds κ) → Prop, (∃ a, Q a) ↔ ∃ b, Q (psGK b) :=
    fun Q => psGK.exists_congr_right.symm
  unfold externalMomentum
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
  · refine (hF _).trans ?_
    simp only [fvGK_val, toGK_fst_inr, Equiv.symm_apply_apply, extFGK_eq_inl_iff]
  · refine (hP _).trans ?_
    simp only [psGK_fst, toGK_snd_inl, extPGK_eq_inr_iff, Equiv.symm_apply_apply]
  · refine (hF _).trans ?_
    simp only [fvGK_val, toGK_fst_inl, extFGK_eq_inr_iff, Equiv.symm_apply_apply]

end Fields

/-! ### Lines -/

section Lines

variable (C : Contraction nf nA κ)

/-- The fermion lines of `C` and of `toGK C`. -/
def fermionLineGK : FermionLine C ≃ FermionLine (toGK C) :=
  Equiv.subtypeEquiv fvGK fun t => by
    have := toGK_fst_apply C (.inr t)
    simp only [extFGK_inr] at this
    rw [this]
    cases C.1.1 (.inr t) <;> rfl

theorem fermionLineGK_val (f : FermionLine C) : (fermionLineGK C f).1 = fvGK f.1 := rfl

theorem tail_fermionLineGK (f : FermionLine C) :
    (fermionLineGK C f).tail = fvGK f.tail := by
  obtain ⟨s, hs⟩ : ∃ s, C.1.1 (.inr f.1) = .inr s := Sum.isRight_iff.mp f.2
  have h' : (toGK C).1.1 (.inr (fermionLineGK C f).1) = .inr (fvGK s) := by
    have := toGK_fst_apply C (.inr f.1)
    simp only [extFGK_inr, hs] at this
    exact this
  rw [tail_eq _ h', tail_eq _ hs]

/-- The photon lines of `C` and of `toGK C`: the same indexing fields. -/
def photonLineGK : PhotonLine C ≃ PhotonLine (toGK C) :=
  Equiv.subtypeEquiv psGK fun a => by
    constructor
    · rintro ⟨b, hb, hk⟩
      exact ⟨psGK b, toGK_snd_inr C hb, hk⟩
    · rintro ⟨b', hb', hk⟩
      obtain ⟨b, rfl⟩ := psGK.surjective b'
      refine ⟨b, ?_, hk⟩
      have := toGK_snd_apply C (.inr a)
      rw [extPGK_inr, hb'] at this
      rcases h : C.1.2 (.inr a) with j | c
      · rw [h] at this
        simp at this
      · rw [h, extPGK_inr] at this
        rw [psGK.injective (Sum.inr_injective this)]

theorem photonLineGK_val (g : PhotonLine C) : (photonLineGK C g).1 = psGK g.1 := rfl

theorem head_photonLineGK (g : PhotonLine C) :
    (photonLineGK C g).head = psGK g.head :=
  head_eq _ (toGK_snd_inr C (QED.TwoLoop.LoopBound.apply_inr_photonLine g))

/-- The internal lines of `C` and of `toGK C`. -/
def lineGK : Line C ≃ Line (toGK C) :=
  Equiv.sumCongr (fermionLineGK C) (photonLineGK C)

theorem lineGK_ends (f : Line C) : (lineGK C f).ends = f.ends := by
  rcases f with f | g
  · change ((fermionLineGK C f).tail.1, (fermionLineGK C f).1.1) = (f.tail.1, f.1.1)
    rw [tail_fermionLineGK]
    rfl
  · change ((photonLineGK C g).1.1, (photonLineGK C g).head.1) = (g.1.1, g.head.1)
    rw [head_photonLineGK]
    rfl

/-- **The line correspondence of `C` and `toGK C`**: the vertices and orientations fixed. -/
def corrGK : LineCorr C (toGK C) where
  vtx := Equiv.refl _
  line := lineGK C
  rev := fun _ => false
  ends_line f := by
    rw [lineGK_ends]
    rfl

theorem corrGK_pull (k' : Line (toGK C) → Fin 4 → ℝ) (f : Line C) :
    (corrGK C).pull k' f = k' (lineGK C f) := by
  simp [LineCorr.pull, corrGK]

end Lines

/-! ### Momenta -/

section Momenta

variable (C : Contraction nf nA κ)

theorem psiMomentum₂_toGK (pIn : Fin nf → Fin 4 → ℝ) (k' : Line (toGK C) → Fin 4 → ℝ)
    (t : Wick.FermionVertex κ) :
    psiMomentum₂ (toGK C) pIn k' (fvGK t) = psiMomentum₂ C pIn ((corrGK C).pull k') t := by
  by_cases hf : (C.1.1 (.inr t)).isRight
  · have hf' : ((toGK C).1.1 (.inr (fvGK t))).isRight := (fermionLineGK C ⟨t, hf⟩).2
    rw [psiMomentum₂_of_isRight hf', psiMomentum₂_of_isRight hf, corrGK_pull]
    rfl
  · obtain ⟨i, hi⟩ : ∃ i, C.1.1 (.inr t) = .inl i := by
      rcases h : C.1.1 (.inr t) with i | s
      · exact ⟨i, rfl⟩
      · rw [h] at hf
        exact absurd rfl hf
    have hi' : (toGK C).1.1 (.inr (fvGK t)) = .inl i := by
      have := toGK_fst_apply C (.inr t)
      rw [extFGK_inr, hi, extFGK_inl] at this
      exact this
    rw [psiMomentum₂_of_inl hi', psiMomentum₂_of_inl hi]

theorem photonMomentum₂_toGK (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (toGK C) → Fin 4 → ℝ)
    (a : Wick.PhotonSlot κ) :
    photonMomentum₂ (toGK C) kIn k' (psGK a) =
      photonMomentum₂ C kIn ((corrGK C).pull k') a := by
  unfold photonMomentum₂
  congr 1
  · refine Finset.sum_congr rfl fun j _ => if_congr ?_ rfl rfl
    rw [toGK_snd_inl, extPGK_eq_inr_iff, Equiv.symm_apply_apply]
  · symm
    refine Fintype.sum_equiv (photonLineGK C) _ _ fun g => ?_
    rw [head_photonLineGK, photonLineGK_val, corrGK_pull]
    simp only [psGK.injective.eq_iff]
    rfl

theorem psiMomentum₂_toGK_eq (pIn : Fin nf → Fin 4 → ℝ) (k' : Line (toGK C) → Fin 4 → ℝ) :
    psiMomentum₂ (toGK C) pIn k' = psiMomentum₂ C pIn ((corrGK C).pull k') ∘ fvGK.symm := by
  funext s
  obtain ⟨t, rfl⟩ := fvGK.surjective s
  simp only [Function.comp_apply, Equiv.symm_apply_apply, psiMomentum₂_toGK]

theorem photonMomentum₂_toGK_eq (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (toGK C) → Fin 4 → ℝ) :
    photonMomentum₂ (toGK C) kIn k' =
      photonMomentum₂ C kIn ((corrGK C).pull k') ∘ psGK.symm := by
  funext b
  obtain ⟨a, rfl⟩ := psGK.surjective b
  simp only [Function.comp_apply, Equiv.symm_apply_apply, photonMomentum₂_toGK]

end Momenta

/-! ### Amplitudes -/

section Amplitude

/-- The product of the `gaugeCt` coefficients `δ₁`. -/
noncomputable def ctWK (δ₁ : ℝ) (κ : Fin N → Wick.VertexKind) : ℂ :=
  ∏ t, if κ t = .gaugeCt then (δ₁ : ℂ) else 1

/-- **Vertex factors under the kind change**: the factor of `t` in `gKinds κ`, with the indices
and momenta carried along, times `δ₁` if `t` is a `gaugeCt` vertex, is the factor of `t` in
`κ`. -/
theorem vertexFactor_gKinds (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      (if κ t = .gaugeCt then (δ₁ : ℂ) else 1) *
        Wick.vertexFactor (κ := gKinds κ) e δ₁ δ₂ δm δ₃ m (α ∘ fvGK.symm) (β ∘ fvGK.symm)
          (lor ∘ psGK.symm) (kψ ∘ fvGK.symm) (kA ∘ psGK.symm) t := by
  have hg : ∀ k, κ t = k → k ≠ .gaugeCt → gKinds κ t = k := fun k h hk => by
    simp only [gKinds, h]
    cases k <;> first | rfl | exact absurd rfl hk
  rcases hk : κ t
  · rw [vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ hk,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ (hg _ hk (by decide))]
    simp
  · have h' : gKinds κ t = .gauge := by simp only [gKinds, hk]; rfl
    rw [vertexFactor_eq_of_gaugeCt _ _ _ _ _ _ _ _ _ _ _ hk,
      vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ h']
    simp only [Function.comp_apply, fvGK_symm_mk, psGK_symm_mk, ite_true]
    push_cast
    ring
  · rw [vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ hk,
      vertexFactor_eq_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ (hg _ hk (by decide))]
    simp
  · rw [vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ hk,
      vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _ (hg _ hk (by decide))]
    simp

theorem amp_toGK_aux {a b c d w a' b' c' d' : ℂ} (h1 : a = a') (h2 : b = w * b') (h3 : c = c')
    (h4 : d = d') : a * (b * c * d) = w * (a' * (b' * c' * d')) := by
  subst h1 h2 h3 h4
  ring

variable (C : Contraction nf nA κ)

open scoped Classical in
/-- **The amplitude (T₇) at the all-electron flavouring** of `C` is `ctWK` times that of
`toGK C`. -/
theorem contractionAmplitude₂_toGK (P : Params) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (toGK C) → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionAmplitude₂ P C (QED.TwoLoop.Insertion.zeroFlavoring κ) pIn kIn
        ((corrGK C).pull k') αOut βIn μ =
      ctWK P.δ₁ κ * contractionAmplitude₂ P (toGK C)
        (QED.TwoLoop.Insertion.zeroFlavoring (gKinds κ)) pIn kIn k' αOut βIn μ := by
  unfold contractionAmplitude₂
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.arrowCongr fvGK (Equiv.refl (Fin 4))) _ _ fun α => ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.arrowCongr fvGK (Equiv.refl (Fin 4))) _ _ fun β => ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.arrowCongr psGK (Equiv.refl (Fin 4))) _ _ fun lor => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.id_comp]
  have hα : (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ↔
      (∀ i t, (toGK C).1.1 (.inl i) = .inr t → (α ∘ fvGK.symm) t = αOut i) := by
    simp only [toGK_fst_inl, extFGK_eq_inr_iff, Function.comp_apply]
    exact forall_congr' fun i => (fvGK.symm.forall_congr_right
      (q := fun t => C.1.1 (.inl i) = .inr t → α t = αOut i)).symm
  have hβ : (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ↔
      (∀ t i, (toGK C).1.1 (.inr t) = .inl i → (β ∘ fvGK.symm) t = βIn i) := by
    simp only [toGK_fst_inr, extFGK_eq_inl_iff, Function.comp_apply]
    exact (fvGK.symm.forall_congr_right
      (q := fun t => ∀ i, C.1.1 (.inr t) = .inl i → β t = βIn i)).symm
  have hlor : (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) ↔
      (∀ j a, (toGK C).1.2 (.inl j) = .inr a → (lor ∘ psGK.symm) a = μ j) := by
    simp only [toGK_snd_inl, extPGK_eq_inr_iff, Function.comp_apply]
    exact forall_congr' fun j => (psGK.symm.forall_congr_right
      (q := fun a => C.1.2 (.inl j) = .inr a → lor a = μ j)).symm
  refine QED.ChainProof.SetCPauli.amp_toGK_aux
    (if_congr (and_congr hα (and_congr hβ hlor)) rfl rfl) ?_ ?_ ?_
  · rw [psiMomentum₂_toGK_eq, photonMomentum₂_toGK_eq]
    unfold ctWK
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => vertexFactor_gKinds _ _ _ _ _ _ _ _ _ _ _ t
  · refine Fintype.prod_equiv (fermionLineGK C) _ _ fun f => ?_
    simp only [Function.comp_apply, tail_fermionLineGK, fermionLineGK_val,
      Equiv.symm_apply_apply, corrGK_pull]
    rfl
  · refine Fintype.prod_equiv (photonLineGK C) _ _ fun g => ?_
    simp only [Function.comp_apply, head_photonLineGK, photonLineGK_val, Equiv.symm_apply_apply,
      corrGK_pull]
    rfl

end Amplitude

/-! ### The value -/

section Value

/-- On an open-line contraction the cycle condition passes to `toGK C`. -/
theorem sameCycle_toGK {C : Contraction 1 nA κ}
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0))
    (x : Fin 1 ⊕ Wick.FermionVertex (gKinds κ)) :
    Equiv.Perm.SameCycle (toGK C).1.1 x (.inl 0) := by
  obtain ⟨y, rfl⟩ := extFGK.surjective x
  exact (sameCycle_permCongr_iff extFGK C.1.1 y (.inl 0)).mpr (hcyc y)

/-- **The value (T₁₀) under the kind change**: for an open-line contraction `C` with connected
vertices whose external momenta sum to zero, the value of `C` is `ctWK` times that of `toGK C`,
at every `ε`. -/
theorem contractionValue₂_toGK (P : Params) {C : Contraction 1 nA κ}
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hV : VerticesConnected C)
    (hV' : VerticesConnected (toGK C)) (hL : loopCount (toGK C) = loopCount C)
    {pOut pIn : Fin 1 → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue₂ P C pOut pIn kIn αOut βIn μ =
      ctWK P.δ₁ κ * contractionValue₂ P (toGK C) pOut pIn kIn αOut βIn μ := by
  obtain ⟨M, hM, a, h⟩ := (corrGK C).exists_routing_change hV hV'
    (fun v => externalMomentum_toGK C pOut pIn kIn v) hsum rfl hL
  rw [contractionValue₂_eq_of_loopCount P hL, contractionValue₂_eq_of_loopCount P rfl]
  have hint : ∀ ℓ, ctWK P.δ₁ κ * ((((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P (toGK C) pIn kIn (lineMomentum₂ (toGK C) pOut pIn kIn ℓ) αOut βIn
        μ) = (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn (matAct M ℓ + a)) αOut βIn
        μ := fun ℓ => by
    rw [← h ℓ, QED.TwoLoop.Insertion.regulatedAmplitude₂_eq_zeroFlavoring P hcyc,
      QED.TwoLoop.Insertion.regulatedAmplitude₂_eq_zeroFlavoring P (sameCycle_toGK hcyc),
      contractionAmplitude₂_toGK]
    ring
  have hmul : ∀ (c : ℂ) (G : (Fin (loopCount C) → Fin 4 → ℝ) → ℂ),
      QED.TwoLoop.jointEnergyFirstIntegral (loopCount C) (fun ℓ => c * G ℓ) =
        c * QED.TwoLoop.jointEnergyFirstIntegral (loopCount C) G := fun c G => by
    unfold QED.TwoLoop.jointEnergyFirstIntegral
    simp only [MeasureTheory.integral_const_mul]
  rw [← hmul]
  simp only [hint]
  exact (QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add _
    (fun ℓ => (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) M hM a).symm

end Value

end QED.ChainProof.SetCPauli

end
