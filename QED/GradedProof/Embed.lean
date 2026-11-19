/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPart
public import QED.Frozen.Lepton.ContractionValue
public import QED.GradedProof.Homogeneity

/-!
# Embedding the graded model into the flavour model at level zero

Two reductions used by the embedding goals of the Phase 5 Stage 2 packet (decision D-57):

* `QED.GradedProof.selectedPart_eq_sum_order`: when the terms with a nonzero grading vanish (for
  example at order `K ≤ 3`, where no counterterm vertex can have level `≥ 1`), the graded order
  part (G₆) of a selection that does not read the grading is the sum, over the vertex sequences
  of total order (V₁) exactly `K`, of the values at the zero grading. The shape is that of
  `QED.ChainProof.Quick.sum_range_filter_order_sub`.
* `QED.GradedProof.contractionValue_zero_eq`: if every counterterm vertex with fermion fields lies
  on the fermion cycle of an external field (`CtReaches`), the graded value (G₅) at the zero
  grading is the value (F₇) of the flavour model, for parameters whose counterterms are the
  open-line level-`0` data times `e²` (only for the vertex kinds that occur). A preserved graded
  flavouring then puts every counterterm vertex on the open-line flavour, so it is a flavouring
  (F₁) of the flavour model.
-/

@[expose] public section

open Complex MeasureTheory Filter
open QED.WickModel (Params Contraction Line lineMomentum₂ loopCount fermionSign psiMomentum₂
  photonMomentum₂ ClosedLoop)
open QED.Graded

namespace QED.GradedProof

/-! ### The order sum at the zero grading -/

/-- The graded order of the zero grading is the order (V₁). -/
theorem gradedOrder_zero {N : ℕ} (κ : Fin N → Wick.VertexKind) :
    gradedOrder κ 0 = ∑ t, (κ t).order := by
  simp [gradedOrder]

/-- At order `K ≤ 3` every grading of graded order `K` is zero. -/
theorem eq_zero_of_gradedOrder_le_three {N : ℕ} {κ : Fin N → Wick.VertexKind} {g : Grading κ}
    (hg : gradedOrder κ g ≤ 3) : g = 0 := by
  funext t
  have := two_mul_add_two_le g t
  simp only [Pi.zero_apply]
  omega

open scoped Classical in
/-- **The graded order part at the zero grading.** If every term with a nonzero grading of
graded order `K` vanishes, the order-`K` part (G₆) of a selection that does not read the grading
is the sum over the vertex sequences of order exactly `K` of the values at the zero grading. -/
theorem selectedPart_eq_sum_order (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Prop) (K : ℕ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4)
    (hz : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Grading κ), gradedOrder κ g = K →
      g ≠ 0 → ∀ C : Contraction nf nA κ, Sel C →
        contractionValue P Φ D C g pOut pIn kIn αOut βIn μ = 0) :
    selectedPart P Φ D nf nA (fun C _ => Sel C) K pOut pIn kIn αOut βIn μ =
      ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order ≤ K),
          if ∑ t, (κ t).order = K then
            ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => Sel C),
              ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ
          else 0 := by
  unfold selectedPart
  refine Finset.sum_congr rfl fun N _ => congrArg _ ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun κ _ => ?_
  by_cases hK : ∑ t, (κ t).order = K
  · rw [ite_eq_left hK.le, ite_eq_left hK]
    have hmem : (0 : Grading κ) ∈ (Fintype.piFinset fun _ : CtVertex κ =>
        Finset.range (K + 1)).filter (fun g => gradedOrder κ g = K) := by
      refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun _ => ?_, ?_⟩
      · simp
      · rw [gradedOrder_zero, hK]
    rw [Finset.sum_eq_single_of_mem 0 hmem fun g hg hne => ?_]
    refine Finset.sum_eq_zero fun C hC => ?_
    rw [hz g (Finset.mem_filter.1 hg).2 hne C (Finset.mem_filter.1 hC).2, mul_zero]
  · rw [ite_eq_right_iff.2 fun _ => ite_eq_right hK]
    refine Finset.sum_eq_zero fun g hg => Finset.sum_eq_zero fun C hC => ?_
    have hg' := (Finset.mem_filter.1 hg).2
    by_cases h0 : g = 0
    · subst h0
      exact absurd (gradedOrder_zero κ ▸ hg') hK
    · rw [hz g hg' h0 C (Finset.mem_filter.1 hC).2, mul_zero]

open scoped Classical in
/-- `selectedPart_eq_sum_order` at order `K ≤ 3`, where every grading of order `K` is zero. -/
theorem selectedPart_eq_sum_order_of_le_three (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (nf nA : ℕ)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Prop) (K : ℕ)
    (hK : K ≤ 3) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    selectedPart P Φ D nf nA (fun C _ => Sel C) K pOut pIn kIn αOut βIn μ =
      ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order ≤ K),
          if ∑ t, (κ t).order = K then
            ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter (fun C => Sel C),
              ((fermionSign C : ℤ) : ℂ) * contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ
          else 0 :=
  selectedPart_eq_sum_order P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ
    fun _ hg hne _ _ => absurd (eq_zero_of_gradedOrder_le_three (hg.le.trans hK)) hne

/-! ### Flavourings when the counterterm vertices lie on the open line -/

section Reaches

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- Every counterterm vertex with fermion fields lies on the fermion cycle of an external
field. -/
def CtReaches (C : Contraction nf nA κ) : Prop :=
  ∀ t : Wick.FermionVertex κ, κ t.1 ≠ .gauge → ∃ i : Fin nf, C.1.1.SameCycle (.inl i) (.inr t)

/-- The graded flavour of a field under a flavouring of the flavour model is its flavour. -/
theorem fermionFlavor_val {F : Type} (Φ : Lepton.Flavors F) (ψ : Lepton.Flavoring Φ κ)
    (a : Fin nf ⊕ Wick.FermionVertex κ) :
    fermionFlavor Φ ψ.1 a = Lepton.fermionFlavor Φ ψ a := by
  rcases a with i | t <;> rfl

theorem preserves_val_iff {F : Type} (Φ : Lepton.Flavors F) (C : Contraction nf nA κ)
    (ψ : Lepton.Flavoring Φ κ) : Preserves Φ C ψ.1 ↔ Lepton.Preserves Φ C ψ := by
  simp only [Preserves, Lepton.Preserves, fermionFlavor_val]

theorem loopWeight_val {F : Type} (Φ : Lepton.Flavors F) (C : Contraction nf nA κ)
    (ψ : Lepton.Flavoring Φ κ) : loopWeight Φ C ψ.1 = Lepton.loopWeight Φ C ψ := by
  simp only [loopWeight, Lepton.loopWeight, fermionFlavor_val]

/-- A preserved graded flavouring is constant on the cycles of `σ`. -/
theorem fermionFlavor_eq_of_sameCycle {F : Type} {Φ : Lepton.Flavors F}
    {C : Contraction nf nA κ} {φ : Flavoring F κ} (hφ : Preserves Φ C φ)
    {a b : Fin nf ⊕ Wick.FermionVertex κ} (hab : C.1.1.SameCycle a b) :
    fermionFlavor Φ φ a = fermionFlavor Φ φ b := by
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

/-- Under `CtReaches`, a preserved graded flavouring puts every counterterm vertex on the
open-line flavour. -/
theorem eq_openLine_of_ctReaches {F : Type} {Φ : Lepton.Flavors F} {C : Contraction nf nA κ}
    (hC : CtReaches C) {φ : Flavoring F κ} (hφ : Preserves Φ C φ) (t : Wick.FermionVertex κ)
    (ht : κ t.1 ≠ .gauge) : φ t = Φ.openLine := by
  obtain ⟨i, hi⟩ := hC t ht
  exact (fermionFlavor_eq_of_sameCycle hφ hi).symm

/-- The factor (V₁₉) of a vertex reads only the data of its kind. -/
theorem vertexFactor_congr (e a b c d m a' b' c' d' m' : ℝ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N)
    (hG : κ t = .gaugeCt → a = a') (hF : κ t = .fermionCt → b = b' ∧ c = c' ∧ m = m')
    (hP : κ t = .photonCt → d = d') :
    Wick.vertexFactor e a b c d m α β lor kψ kA t =
      Wick.vertexFactor e a' b' c' d' m' α β lor kψ kA t := by
  unfold Wick.vertexFactor
  split <;> rename_i h
  · rfl
  · rw [hG h]
  · obtain ⟨rfl, rfl, rfl⟩ := hF h
    rfl
  · rw [hP h]

open scoped Classical in
/-- The graded amplitude (G₃) at the zero grading of a flavouring of the flavour model is the
amplitude (F₅), when the parameters carry the open-line level-`0` data of the kinds present. -/
theorem contractionAmplitude_zero_eq (P P' : Params) {F : Type} (Φ : Lepton.Flavors F)
    (D : Counterterms F) (C : Contraction nf nA κ) (ψ : Lepton.Flavoring Φ κ)
    (he : P'.e = P.e) (hmγ : P'.mγ = P.mγ) (hΛ : P'.Λ = P.Λ) (hε : P'.ε = P.ε)
    (hG : ∀ t, κ t = .gaugeCt → P'.δ₁ = P.e ^ 2 * D.d₁ Φ.openLine 0)
    (hF : ∀ t, κ t = .fermionCt → P'.δ₂ = P.e ^ 2 * D.d₂ Φ.openLine 0 ∧
      P'.δm = P.e ^ 2 * D.dm Φ.openLine 0 ∧ P'.m = Φ.mass Φ.openLine)
    (hP : ∀ t, κ t = .photonCt → P'.δ₃ = P.e ^ 2 * D.d₃ 0)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D C ψ.1 0 pIn kIn k αOut βIn μ =
      Lepton.contractionAmplitude₂ P' Φ C ψ pIn kIn k αOut βIn μ := by
  unfold contractionAmplitude Lepton.contractionAmplitude₂
  rw [he, hmγ, hΛ, hε]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun lor _ => ?_
  refine congrArg₂ _ rfl (congrArg₂ _ (congrArg₂ _ ?_ rfl) rfl)
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [Pi.zero_apply, dite_eq_ite, ite_self, zero_add, mul_one]
  by_cases hg : κ t = .gauge
  · exact vertexFactor_of_gauge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t hg
  by_cases hp : κ t = .photonCt
  · rw [dite_eq_left hp]
    exact vertexFactor_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t (fun h => by simp_all)
      (fun h => by simp_all) fun _ => (hP t hp).symm
  · have hψ : ψ.1 ⟨t, hp⟩ = Φ.openLine := ψ.2 ⟨t, hp⟩ hg
    rw [dite_eq_right hp, hψ]
    refine vertexFactor_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t (fun h => (hG t h).symm)
      (fun h => ?_) fun h => absurd h hp
    obtain ⟨h₂, hm, hM⟩ := hF t h
    exact ⟨h₂.symm, hm.symm, hM.symm⟩

open scoped Classical in
/-- **The graded value at the zero grading is the value of the flavour model** when every
counterterm vertex with fermion fields lies on the open line. -/
theorem regulatedAmplitude_zero_eq (P P' : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (C : Contraction nf nA κ) (hC : CtReaches C)
    (he : P'.e = P.e) (hmγ : P'.mγ = P.mγ) (hΛ : P'.Λ = P.Λ) (hε : P'.ε = P.ε)
    (hG : ∀ t, κ t = .gaugeCt → P'.δ₁ = P.e ^ 2 * D.d₁ Φ.openLine 0)
    (hF : ∀ t, κ t = .fermionCt → P'.δ₂ = P.e ^ 2 * D.d₂ Φ.openLine 0 ∧
      P'.δm = P.e ^ 2 * D.dm Φ.openLine 0 ∧ P'.m = Φ.mass Φ.openLine)
    (hP : ∀ t, κ t = .photonCt → P'.δ₃ = P.e ^ 2 * D.d₃ 0)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P Φ D C 0 pIn kIn k αOut βIn μ =
      Lepton.regulatedAmplitude₂ P' Φ C pIn kIn k αOut βIn μ := by
  unfold regulatedAmplitude Lepton.regulatedAmplitude₂
  symm
  refine Finset.sum_bij (fun ψ _ => ψ.1) (fun ψ hψ => ?_) (fun ψ _ ψ' _ h => Subtype.ext h)
    (fun φ hφ => ?_) (fun ψ _ => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (preserves_val_iff Φ C ψ).2 (Finset.mem_filter.1 hψ).2⟩
  · have hφ' := (Finset.mem_filter.1 hφ).2
    refine ⟨⟨φ, fun t ht => eq_openLine_of_ctReaches hC hφ' t ht⟩, ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (preserves_val_iff Φ C _).1 hφ'⟩
  · rw [loopWeight_val, contractionAmplitude_zero_eq P P' Φ D C ψ he hmγ hΛ hε hG hF hP]

open scoped Classical in
/-- The graded value (G₅) at the zero grading is the value (F₇) under the hypotheses of
`regulatedAmplitude_zero_eq`. -/
theorem contractionValue_zero_eq (P P' : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (C : Contraction nf nA κ) (hC : CtReaches C)
    (he : P'.e = P.e) (hmγ : P'.mγ = P.mγ) (hΛ : P'.Λ = P.Λ) (hε : P'.ε = P.ε)
    (hG : ∀ t, κ t = .gaugeCt → P'.δ₁ = P.e ^ 2 * D.d₁ Φ.openLine 0)
    (hF : ∀ t, κ t = .fermionCt → P'.δ₂ = P.e ^ 2 * D.d₂ Φ.openLine 0 ∧
      P'.δm = P.e ^ 2 * D.dm Φ.openLine 0 ∧ P'.m = Φ.mass Φ.openLine)
    (hP : ∀ t, κ t = .photonCt → P'.δ₃ = P.e ^ 2 * D.d₃ 0)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue P Φ D C 0 pOut pIn kIn αOut βIn μ =
      Lepton.contractionValue₂ P' Φ C pOut pIn kIn αOut βIn μ := by
  unfold contractionValue Lepton.contractionValue₂
  simp only [regulatedAmplitude_zero_eq P P' Φ D C hC he hmγ hΛ hε hG hF hP]

end Reaches

end QED.GradedProof

end
