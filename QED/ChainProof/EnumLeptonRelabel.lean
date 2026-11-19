/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RelabelCountertermValue
public import QED.Frozen.Lepton.ContractionValue

/-!
# Relabelling invariance of the flavoured value (F₇)

Helper for obligation O3-4 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53), so that the
enumeration of the set (b) chain family applies to the chain vertex (C₃) at every flavour data
`Φ`, not only at T1's flavours. It is the proof of
`QED.TwoLoop.Relabel.contractionValue₂_relabelK` with the flavourings (F₂) of `Φ` in place of
those of T1: relabelling the vertices maps the flavourings of `C` bijectively onto those of the
relabelled contraction, preserving `Preserves` (F₃), the loop weight (F₄) and the amplitude (F₅),
so the regulated amplitude (F₆) is carried along by the line correspondence, and the value (F₇)
is invariant by the routing change.

* `QED.ChainProof.Enum.contractionValue₂_relabelK_lepton`: for a contraction with connected
  vertices whose external momenta sum to zero.
* `QED.ChainProof.Enum.contractionValue₂_relabelK_of_isOnePI_lepton`: for 1PI contractions under
  momentum conservation.
-/

@[expose] public section

namespace QED.ChainProof.Enum

open Complex QED.TwoLoop.Relabel QED.TwoLoop.Routing
open QED.WickModel (Params Contraction IsOnePI VerticesConnected externalMomentum loopCount
  lineMomentum₂ Line)
open QED.Lepton (Flavors Flavoring fermionFlavor Preserves loopWeight contractionAmplitude₂
  regulatedAmplitude₂ contractionValue₂)

variable {nf nA N : ℕ} {κ κ' : Fin N → Wick.VertexKind} {F : Type} (Φ : Flavors F)

/-- A preserved flavouring is constant on the cycles of the fermion pairing. -/
theorem fermionFlavor_eq_of_sameCycle_lepton {C : Contraction nf nA κ} {φ : Flavoring Φ κ}
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

section Flavor

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ)

/-- Relabelling a flavouring of `Φ` across kind sequences. -/
def flavMapL : Flavoring Φ κ ≃ Flavoring Φ κ' where
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

@[simp] theorem flavMapL_val (φ : Flavoring Φ κ) (t : Wick.FermionVertex κ') :
    (flavMapL Φ π hκ φ).1 t = φ.1 ((fvMap π hκ).symm t) :=
  rfl

theorem fermionFlavor_flavMapL (φ : Flavoring Φ κ) (x : Fin nf ⊕ Wick.FermionVertex κ) :
    fermionFlavor Φ (flavMapL Φ π hκ φ) (extFK π hκ x) = fermionFlavor Φ φ x := by
  cases x <;> simp [fermionFlavor]

theorem preserves_relabelK_iff_lepton (φ : Flavoring Φ κ) :
    Preserves Φ (relabelK π hκ C) (flavMapL Φ π hκ φ) ↔ Preserves Φ C φ := by
  constructor
  · intro h x
    have := h (extFK π hκ x)
    rwa [relabelK_fst_apply, fermionFlavor_flavMapL, fermionFlavor_flavMapL] at this
  · intro h a
    obtain ⟨x, rfl⟩ := (extFK π hκ).surjective a
    rw [relabelK_fst_apply, fermionFlavor_flavMapL, fermionFlavor_flavMapL]
    exact h x

open scoped Classical in
/-- Relabelling preserves the loop weight (F₄) of a preserved flavouring. -/
theorem loopWeight_relabelK_lepton {φ : Flavoring Φ κ} (hφ : Preserves Φ C φ) :
    loopWeight Φ (relabelK π hκ C) (flavMapL Φ π hκ φ) = loopWeight Φ C φ := by
  have hφ' := (preserves_relabelK_iff_lepton Φ π hκ C φ).mpr hφ
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
  rw [fermionFlavor_eq_of_sameCycle_lepton Φ hφ' hsc, fermionFlavor_flavMapL]

end Flavor

section Amplitude

variable (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ)

open scoped Classical in
/-- Relabelling the amplitude (F₅). -/
theorem contractionAmplitude₂_relabelK_lepton (P : Params) (φ : Flavoring Φ κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k' : Line (relabelK π hκ C) → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude₂ P Φ (relabelK π hκ C) (flavMapL Φ π hκ φ) pIn kIn k' αOut βIn μ =
      contractionAmplitude₂ P Φ C φ pIn kIn ((relabelCorrK π hκ C).pull k') αOut βIn μ := by
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
    simp only [Function.comp_apply, flavMapL_val, tail_fermionLineEquivK,
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

/-- **Relabelling the regulated amplitude** (F₆) across kind sequences. -/
theorem regulatedAmplitude₂_relabelK_lepton (P : Params) [Fintype F] [DecidableEq F]
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (relabelK π hκ C) → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P Φ (relabelK π hκ C) pIn kIn k' αOut βIn μ =
      regulatedAmplitude₂ P Φ C pIn kIn ((relabelCorrK π hκ C).pull k') αOut βIn μ := by
  classical
  unfold regulatedAmplitude₂
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  refine Fintype.sum_equiv (flavMapL Φ π hκ) _ _ fun φ => ?_
  by_cases hφ : Preserves Φ C φ
  · have hφ' := (preserves_relabelK_iff_lepton Φ π hκ C φ).mpr hφ
    simp only [hφ, hφ', ↓reduceIte, loopWeight_relabelK_lepton Φ π hκ C hφ,
      contractionAmplitude₂_relabelK_lepton]
  · have hφ' : ¬ Preserves Φ (relabelK π hκ C) (flavMapL Φ π hκ φ) :=
      mt (preserves_relabelK_iff_lepton Φ π hκ C φ).mp hφ
    simp only [hφ, hφ', ↓reduceIte]

end Amplitude

/-- **Relabelling invariance of the flavoured value** (F₇) across kind sequences, for a
contraction with connected vertices whose external momenta sum to zero. -/
theorem contractionValue₂_relabelK_lepton (P : Params) [Fintype F] [DecidableEq F]
    (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction nf nA κ)
    (hV : VerticesConnected C) {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue₂ P Φ (relabelK π hκ C) pOut pIn kIn αOut βIn μ =
      contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ := by
  have hV' := (verticesConnected_relabelK_iff π hκ C).mpr hV
  have hL' := loopCount_relabelK π hκ C hV
  obtain ⟨M, hM, a, h⟩ := (relabelCorrK π hκ C).exists_routing_change hV hV'
    (externalMomentum_relabelK π hκ C pOut pIn kIn) hsum rfl hL'
  unfold contractionValue₂
  rw [hL']
  simp only [regulatedAmplitude₂_relabelK_lepton, h]
  exact QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add _
    (fun ℓ => (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P Φ C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) M hM a

/-- **Relabelling invariance of the flavoured value for 1PI contractions**, under momentum
conservation `∑ pOut = ∑ pIn + ∑ kIn`. -/
theorem contractionValue₂_relabelK_of_isOnePI_lepton (P : Params) [Fintype F] [DecidableEq F]
    (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction nf nA κ}
    (hC : IsOnePI C) {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue₂ P Φ (relabelK π hκ C) pOut pIn kIn αOut βIn μ =
      contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ :=
  contractionValue₂_relabelK_lepton Φ P π hκ C hC.2.1
    (by rw [sum_externalMomentum hC.1, hmom, sub_self]) αOut βIn μ

end QED.ChainProof.Enum

end
