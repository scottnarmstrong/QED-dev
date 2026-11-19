/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.IntegrableOrderFiveTransfer
public import QED.ChainProof.EnumLeptonRelabel
public import QED.Frozen.Graded.RegulatedAmplitude

/-!
# Relabelling invariance of the graded regulated amplitude

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57). This is
`QED.ChainProof.Enum.regulatedAmplitude₂_relabelK_lepton` for the graded model (G₄): relabelling
the vertices across kind sequences maps the flavourings (G₁) and the gradings (G₂′) of `C`
bijectively onto those of the relabelled contraction, preserving `Preserves` (G₁″), the loop
weight (G₁‴) and the amplitude (G₃), so the regulated amplitude is carried along by the line
correspondence. Every vertex factor of (G₃) reads its level and flavour from its own vertex, so
the per-vertex identity `QED.TwoLoop.Relabel.vertexFactor_relabelK` applies term by term.

## Main statements

* `QED.GradedProof.VP2.regulatedAmplitude_relabelK`: the graded regulated amplitude of a
  relabelled contraction, at the transported grading `gradMap π hκ g`, is that of `C` at the
  pulled-back line momenta.
* `QED.GradedProof.VP2.jointEnergyFirstIntegrable_relabelK_graded`: (T₉′) for the graded
  integrand of a 1PI contraction passes to its relabellings, under momentum conservation.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Relabel QED.TwoLoop.Routing
open QED.WickModel (Params Contraction IsOnePI VerticesConnected externalMomentum loopCount
  lineMomentum₂ Line)

variable {nf nA N : ℕ} {κ κ' : Fin N → Wick.VertexKind} {F : Type} (Φ : Lepton.Flavors F)

/-- A preserved flavouring is constant on the cycles of the fermion pairing. -/
theorem fermionFlavor_eq_of_sameCycle {C : Contraction nf nA κ} {φ : Flavoring F κ}
    (hφ : Preserves Φ C φ) {a b : Fin nf ⊕ Wick.FermionVertex κ}
    (hab : C.1.1.SameCycle a b) : fermionFlavor Φ φ a = fermionFlavor Φ φ b := by
  have key : ∀ (z : ℤ) (x : Fin nf ⊕ Wick.FermionVertex κ),
      fermionFlavor Φ φ ((C.1.1 ^ z) x) = fermionFlavor Φ φ x := by
    intro z
    induction z using Int.induction_on with
    | zero => intro x; rfl
    | succ z ih =>
      intro x
      rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hφ]
    | pred z ih =>
      intro x
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      have := hφ (C.1.1⁻¹ x)
      have hx : C.1.1 (C.1.1⁻¹ x) = x := by simp
      rwa [hx, eq_comm] at this
  obtain ⟨z, rfl⟩ := hab
  exact (key z a).symm

section Maps

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t)

/-- Relabelling a graded flavouring across kind sequences. -/
def flavMapG : Flavoring F κ ≃ Flavoring F κ' :=
  Equiv.arrowCongr (fvMap π hκ) (Equiv.refl F)

@[simp] theorem flavMapG_apply (φ : Flavoring F κ) (t : Wick.FermionVertex κ') :
    flavMapG π hκ φ t = φ ((fvMap π hκ).symm t) :=
  rfl

/-- Relabelling the counterterm vertices across kind sequences. -/
def ctMap : CtVertex κ ≃ CtVertex κ' where
  toFun t := ⟨π t.1, by rw [hκ]; exact t.2⟩
  invFun s := ⟨π.symm s.1, by rw [kind_symm_apply π hκ]; exact s.2⟩
  left_inv t := Subtype.ext (π.symm_apply_apply t.1)
  right_inv s := Subtype.ext (π.apply_symm_apply s.1)

/-- Relabelling a grading across kind sequences. -/
def gradMap (g : Grading κ) : Grading κ' :=
  fun s => g ((ctMap π hκ).symm s)

theorem gradMap_zero : gradMap π hκ (0 : Grading κ) = 0 := rfl

theorem fermionFlavor_flavMapG (φ : Flavoring F κ) (x : Fin nf ⊕ Wick.FermionVertex κ) :
    fermionFlavor Φ (flavMapG π hκ φ) (extFK π hκ x) = fermionFlavor Φ φ x := by
  cases x <;> simp [fermionFlavor]

/-- The level read at vertex `π t` of the relabelled sequence is that of `t`. -/
theorem level_relabel (g : Grading κ) (t : Fin N) :
    (if h : κ' (π t) = .gauge then 0 else gradMap π hκ g ⟨π t, h⟩) =
      (if h : κ t = .gauge then 0 else g ⟨t, h⟩) := by
  by_cases h : κ t = .gauge
  · simp only [h, (hκ t).trans h, ↓reduceDIte]
  · have h' : κ' (π t) ≠ .gauge := by rw [hκ]; exact h
    simp only [h, h', ↓reduceDIte, gradMap]
    congr 1
    exact Subtype.ext (π.symm_apply_apply t)

/-- The flavour read at vertex `π t` of the relabelled sequence is that of `t`. -/
theorem flavour_relabel (φ : Flavoring F κ) (t : Fin N) :
    (if h : κ' (π t) = .photonCt then Φ.openLine else flavMapG π hκ φ ⟨π t, h⟩) =
      (if h : κ t = .photonCt then Φ.openLine else φ ⟨t, h⟩) := by
  by_cases h : κ t = .photonCt
  · simp only [h, (hκ t).trans h, ↓reduceDIte]
  · have h' : κ' (π t) ≠ .photonCt := by rw [hκ]; exact h
    simp only [h, h', ↓reduceDIte, flavMapG_apply, fvMap_symm_mk]

end Maps

section Flavor

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ)

theorem preserves_relabelK_iff (φ : Flavoring F κ) :
    Preserves Φ (relabelK π hκ C) (flavMapG π hκ φ) ↔ Preserves Φ C φ := by
  constructor
  · intro h x
    have := h (extFK π hκ x)
    rwa [relabelK_fst_apply, fermionFlavor_flavMapG, fermionFlavor_flavMapG] at this
  · intro h a
    obtain ⟨x, rfl⟩ := (extFK π hκ).surjective a
    rw [relabelK_fst_apply, fermionFlavor_flavMapG, fermionFlavor_flavMapG]
    exact h x

open scoped Classical in
/-- Relabelling preserves the loop weight (G₁‴) of a preserved flavouring. -/
theorem loopWeight_relabelK {φ : Flavoring F κ} (hφ : Preserves Φ C φ) :
    loopWeight Φ (relabelK π hκ C) (flavMapG π hκ φ) = loopWeight Φ C φ := by
  have hφ' := (preserves_relabelK_iff Φ π hκ C φ).mpr hφ
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
  rw [fermionFlavor_eq_of_sameCycle Φ hφ' hsc, fermionFlavor_flavMapG]

end Flavor

section Amplitude

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ)

open scoped Classical in
/-- Relabelling the graded amplitude (G₃). -/
theorem contractionAmplitude_relabelK (P : Params) (D : Counterterms F) (φ : Flavoring F κ)
    (g : Grading κ) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D (relabelK π hκ C) (flavMapG π hκ φ) (gradMap π hκ g) pIn kIn k'
        αOut βIn μ =
      contractionAmplitude P Φ D C φ g pIn kIn ((relabelCorrK π hκ C).pull k') αOut βIn μ := by
  unfold contractionAmplitude
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
    rw [level_relabel π hκ g t, flavour_relabel Φ π hκ φ t]
    exact (vertexFactor_relabelK π hκ _ _ _ _ _ _ α β lor _ _ t).symm
  · refine Fintype.prod_equiv (fermionLineEquivK π hκ C) _ _ fun f => ?_
    simp only [Function.comp_apply, flavMapG_apply, tail_fermionLineEquivK,
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

/-- **Relabelling the graded regulated amplitude** (G₄) across kind sequences. -/
theorem regulatedAmplitude_relabelK (P : Params) [Fintype F] [DecidableEq F]
    (D : Counterterms F) (g : Grading κ) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D (relabelK π hκ C) (gradMap π hκ g) pIn kIn k' αOut βIn μ =
      regulatedAmplitude P Φ D C g pIn kIn ((relabelCorrK π hκ C).pull k') αOut βIn μ := by
  classical
  unfold regulatedAmplitude
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  refine Fintype.sum_equiv (flavMapG π hκ) _ _ fun φ => ?_
  by_cases hφ : Preserves Φ C φ
  · have hφ' := (preserves_relabelK_iff Φ π hκ C φ).mpr hφ
    simp only [hφ, hφ', ↓reduceIte, loopWeight_relabelK Φ π hκ C hφ,
      contractionAmplitude_relabelK]
  · have hφ' : ¬ Preserves Φ (relabelK π hκ C) (flavMapG π hκ φ) :=
      mt (preserves_relabelK_iff Φ π hκ C φ).mp hφ
    simp only [hφ, hφ', ↓reduceIte]

end Amplitude

/-- **(T₉′) for the graded integrand passes to relabellings** of a 1PI contraction across kind
sequences, under momentum conservation. -/
theorem jointEnergyFirstIntegrable_relabelK_graded (P : Params) [Fintype F] [DecidableEq F]
    (D : Counterterms F) (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t)
    {C : Contraction nf nA κ} (hC : IsOnePI C) (g : Grading κ) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4)
    (h : QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount (relabelK π hκ C)) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount (relabelK π hκ C)) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D (relabelK π hκ C) (gradMap π hκ g) pIn kIn
          (lineMomentum₂ (relabelK π hκ C) pOut pIn kIn ℓ) αOut βIn μ := by
  have hV := hC.2.1
  have hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hC.1, hmom, sub_self]
  have hV' := (verticesConnected_relabelK_iff π hκ C).mpr hV
  have hL' := loopCount_relabelK π hκ C hV
  obtain ⟨M, hM, a, hr⟩ := (relabelCorrK π hκ C).exists_routing_change hV hV'
    (externalMomentum_relabelK π hκ C pOut pIn kIn) hsum rfl hL'
  rw [hL']
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_matAct M hM a h fun ℓ => by
    rw [regulatedAmplitude_relabelK, hr]

end QED.GradedProof.VP2

end
