/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RoutingChange
public import QED.TwoLoop.EnumerationRelabel
public import QED.TwoLoop.LoopBoundTwoExact
public import QED.TwoLoop.JointIntegralInvariance
public import QED.Frozen.TwoLoop.ContractionValue

/-!
# Relabelling invariance of the value of a contraction of gauge vertices

The analytic half of section 3.3 of `docs/TWO-LOOP-DERIVATION.md`: for a contraction `C` of `N`
gauge vertices (`gauges N`) with connected vertices (X₁₇) whose external momenta (X₁₉) sum to
zero, relabelling the vertices by any `π` leaves the value (T₁₀) unchanged.

* `QED.TwoLoop.Relabel.relabelCorr`: the internal lines of `C` and `relabel π C` correspond, with
  ends moved by `π`; the photon lines whose indexing field changes are reversed.
* `QED.TwoLoop.Relabel.loopCount_relabel`: the number of loops is preserved (the cyclomatic
  number, `LoopBoundTwo.loopCount_add_eq`).
* `QED.TwoLoop.Relabel.regulatedAmplitude₂_relabel`: the regulated amplitude (T₈) of
  `relabel π C` at line momenta `k'` is that of `C` at the pulled-back momenta. The spinor,
  Lorentz and flavor sums are reindexed by `π`; the gauge vertex factor does not depend on the
  momenta; fermion propagators correspond line by line; a reversed photon line has its momentum
  negated and its indices swapped, which leaves the Feynman-gauge propagator unchanged; the closed
  fermion loops correspond, and the flavor is constant on each loop, so the regulator weights (X₇)
  agree.
* `QED.TwoLoop.Relabel.contractionValue₂_relabel`: **relabelling invariance**. The routings are
  related by an integer unimodular affine change of loop momenta (`exists_routing_change`), under
  which the joint energy-first integral is invariant (`jointEnergyFirstIntegral_comp_matrix_add`),
  for every integrand.
* `QED.TwoLoop.Relabel.contractionValue₂_relabel_of_isOnePI`: the same for 1PI contractions under
  momentum conservation `∑ pOut = ∑ pIn + ∑ kIn`.
* `QED.TwoLoop.Relabel.onePIFunction₂_five_sub_four_eq`: the order-`e⁵` vertex with coefficient
  one per class, under momentum conservation only.

Momentum conservation is needed: without it the routing (T₄) is not conserved, and the defect
depends on the orientation of the lines, which relabelling changes.
-/

@[expose] public section

namespace QED.TwoLoop.Relabel

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Routing Complex

variable {nf nA N : ℕ}

/-! ### Relabelling on fields -/

section Fields

variable (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N))

@[simp] theorem fvPerm_symm_mk (t : Fin N) (h : gauges N t ≠ .photonCt) :
    (fvPerm π).symm ⟨π t, h⟩ = ⟨t, h⟩ :=
  (fvPerm π).symm_apply_apply ⟨t, h⟩

@[simp] theorem psPerm_symm_mk (t : Fin N) (i : Fin (gauges N t).photonSlots) :
    (psPerm π).symm ⟨π t, i⟩ = ⟨t, i⟩ :=
  (psPerm π).symm_apply_apply ⟨t, i⟩

theorem extF_eq_inl_iff (y : Fin nf ⊕ Wick.FermionVertex (gauges N)) (i : Fin nf) :
    extF π y = .inl i ↔ y = .inl i := by
  cases y <;> simp

theorem extF_eq_inr_iff (y : Fin nf ⊕ Wick.FermionVertex (gauges N))
    (t : Wick.FermionVertex (gauges N)) :
    extF π y = .inr t ↔ y = .inr ((fvPerm π).symm t) := by
  cases y <;> simp [Equiv.eq_symm_apply]

theorem extP_eq_inr_iff (y : Fin nA ⊕ Wick.PhotonSlot (gauges N))
    (a : Wick.PhotonSlot (gauges N)) :
    extP π y = .inr a ↔ y = .inr ((psPerm π).symm a) := by
  cases y <;> simp [Equiv.eq_symm_apply]

theorem relabel_fst_inl (i : Fin nf) :
    (relabel π C).1.1 (.inl i) = extF π (C.1.1 (.inl i)) :=
  relabel_fst_apply π C (.inl i)

theorem relabel_fst_inr (t : Wick.FermionVertex (gauges N)) :
    (relabel π C).1.1 (.inr t) = extF π (C.1.1 (.inr ((fvPerm π).symm t))) := by
  have := relabel_fst_apply π C (.inr ((fvPerm π).symm t))
  simpa using this

theorem relabel_snd_inl (j : Fin nA) :
    (relabel π C).1.2 (.inl j) = extP π (C.1.2 (.inl j)) :=
  relabel_snd_apply π C (.inl j)

/-- The external momentum flowing into `π v` in `relabel π C` is that flowing into `v` in `C`. -/
theorem externalMomentum_relabel (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (v : Fin N) :
    externalMomentum (relabel π C) pOut pIn kIn (π v) = externalMomentum C pOut pIn kIn v := by
  have hF : ∀ Q : Wick.FermionVertex (gauges N) → Prop, (∃ t, Q t) ↔ ∃ s, Q (fvPerm π s) :=
    fun Q => (fvPerm π).exists_congr_right.symm
  have hP : ∀ Q : Wick.PhotonSlot (gauges N) → Prop, (∃ a, Q a) ↔ ∃ b, Q (psPerm π b) :=
    fun Q => (psPerm π).exists_congr_right.symm
  unfold externalMomentum
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
  · refine (hF _).trans ?_
    simp only [fvPerm_val, π.injective.eq_iff, relabel_fst_inr, Equiv.symm_apply_apply,
      extF_eq_inl_iff]
  · refine (hP _).trans ?_
    simp only [psPerm_fst, π.injective.eq_iff, relabel_snd_inl, extP_eq_inr_iff,
      Equiv.symm_apply_apply]
  · refine (hF _).trans ?_
    simp only [fvPerm_val, π.injective.eq_iff, relabel_fst_inl, extF_eq_inr_iff,
      Equiv.symm_apply_apply]

end Fields

/-! ### The line correspondence -/

section Lines

variable (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N))

/-- The lines reversed by relabelling: the photon lines whose indexing field changes. -/
def relabelRev : Line C → Bool
  | .inl _ => false
  | .inr g => !decide (Wick.photonKey (psPerm π g.1) < Wick.photonKey (psPerm π g.head))

theorem photonLineMap_of_lt (g : PhotonLine C)
    (h : Wick.photonKey (psPerm π g.1) < Wick.photonKey (psPerm π g.head)) :
    (photonLineMap π C g).1 = psPerm π g.1 ∧ (photonLineMap π C g).head = psPerm π g.head := by
  have e : photonLineMap π C g = ⟨psPerm π g.1, psPerm π g.head,
      relabel_snd_inr π C _ _ (LoopBound.apply_inr_photonLine g), h⟩ := by
    unfold photonLineMap
    simp only [h, ↓reduceDIte]
  rw [e]
  exact ⟨rfl, head_eq _ (relabel_snd_inr π C _ _ (LoopBound.apply_inr_photonLine g))⟩

theorem photonLineMap_of_not_lt (g : PhotonLine C)
    (h : ¬ Wick.photonKey (psPerm π g.1) < Wick.photonKey (psPerm π g.head)) :
    (photonLineMap π C g).1 = psPerm π g.head ∧ (photonLineMap π C g).head = psPerm π g.1 := by
  have e : photonLineMap π C g = ⟨psPerm π g.head, psPerm π g.1,
      relabel_snd_inr π C _ _ (LoopBound.apply_inr_head g),
      lt_of_le_of_ne (not_lt.mp h) (psPerm_ne π C (LoopBound.apply_inr_photonLine g)).symm⟩ := by
    unfold photonLineMap
    simp only [h, ↓reduceDIte]
  rw [e]
  exact ⟨rfl, head_eq _ (relabel_snd_inr π C _ _ (LoopBound.apply_inr_head g))⟩

/-- **The line correspondence of a relabelling**: ends moved by `π`, the photon lines whose
indexing field changes reversed. -/
noncomputable def relabelCorr : LineCorr C (relabel π C) where
  vtx := π
  line := lineEquiv π C
  rev := relabelRev π C
  ends_line f := by
    rcases f with f | g
    · simp only [relabelRev, Bool.false_eq_true, ↓reduceIte]
      exact fermionLineEquiv_ends π C f
    · by_cases h : Wick.photonKey (psPerm π g.1) < Wick.photonKey (psPerm π g.head)
      · obtain ⟨h1, h2⟩ := photonLineMap_of_lt π C g h
        simp only [relabelRev, h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        change ((photonLineMap π C g).1.1, (photonLineMap π C g).head.1) = _
        rw [h1, h2]
        rfl
      · obtain ⟨h1, h2⟩ := photonLineMap_of_not_lt π C g h
        simp only [relabelRev, h, decide_false, Bool.not_false, ↓reduceIte]
        change ((photonLineMap π C g).1.1, (photonLineMap π C g).head.1) = _
        rw [h1, h2]
        rfl

theorem tail_fermionLineEquiv (f : FermionLine C) :
    (fermionLineEquiv π C f).tail = fvPerm π f.tail :=
  Subtype.ext (congrArg Prod.fst (fermionLineEquiv_ends π C f))

theorem fermionLineEquiv_val (f : FermionLine C) :
    (fermionLineEquiv π C f).1 = fvPerm π f.1 :=
  rfl

theorem pull_inl (k' : Line (relabel π C) → Fin 4 → ℝ) (f : FermionLine C) :
    (relabelCorr π C).pull k' (.inl f) = k' (.inl (fermionLineEquiv π C f)) :=
  rfl

theorem verticesConnected_relabel_iff :
    VerticesConnected (relabel π C) ↔ VerticesConnected C := by
  have h := reflTransGen_relabel_iff π C ∅
  simp only [Set.image_empty] at h
  constructor
  · intro hC u w
    exact (h u w).mp (hC _ _)
  · intro hC u w
    rw [← π.apply_symm_apply u, ← π.apply_symm_apply w]
    exact (h _ _).mpr (hC _ _)

theorem loopCount_gauges_zero (C : Contraction nf nA (gauges 0)) : loopCount C = 0 := by
  unfold loopCount
  exact Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun f _ => f.ends.1.elim0)

/-- **Relabelling preserves the number of loops** of a contraction with connected vertices. -/
theorem loopCount_relabel (hV : VerticesConnected C) :
    loopCount (relabel π C) = loopCount C := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [loopCount_gauges_zero, loopCount_gauges_zero]
  · have h1 := LoopBoundTwo.loopCount_add_eq hV hN
    have h2 := LoopBoundTwo.loopCount_add_eq ((verticesConnected_relabel_iff π C).mpr hV) hN
    have h3 : Nat.card (Line (relabel π C)) = Nat.card (Line C) :=
      Nat.card_congr (lineEquiv π C).symm
    omega

end Lines

/-! ### The regulated amplitude -/

section Amplitude

variable (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N))

/-- The gauge vertex factor does not depend on the momenta. -/
theorem vertexFactor_gauges (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex (gauges N) → Fin 4)
    (lor : Wick.PhotonSlot (gauges N) → Fin 4) (kψ : Wick.FermionVertex (gauges N) → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot (gauges N) → Fin 4 → ℝ) (t : Fin N) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor ⟨t, ⟨0, Nat.one_pos⟩⟩)
        (α ⟨t, fun h => Wick.VertexKind.noConfusion h⟩)
        (β ⟨t, fun h => Wick.VertexKind.noConfusion h⟩) :=
  rfl

/-- Relabelling a flavoring. -/
def flavMap : Flavoring (gauges N) ≃ Flavoring (gauges N) where
  toFun φ := ⟨φ.1 ∘ (fvPerm π).symm, fun _ h => absurd rfl h⟩
  invFun φ := ⟨φ.1 ∘ fvPerm π, fun _ h => absurd rfl h⟩
  left_inv φ := Subtype.ext (funext fun t => by simp)
  right_inv φ := Subtype.ext (funext fun t => by simp)

@[simp] theorem flavMap_val (φ : Flavoring (gauges N)) (t : Wick.FermionVertex (gauges N)) :
    (flavMap π φ).1 t = φ.1 ((fvPerm π).symm t) :=
  rfl

theorem fermionFlavor_flavMap (φ : Flavoring (gauges N))
    (x : Fin nf ⊕ Wick.FermionVertex (gauges N)) :
    fermionFlavor (flavMap π φ) (extF π x) = fermionFlavor φ x := by
  cases x <;> simp [fermionFlavor]

theorem preserves_relabel_iff (φ : Flavoring (gauges N)) :
    Preserves (relabel π C) (flavMap π φ) ↔ Preserves C φ := by
  constructor
  · intro h x
    have := h (extF π x)
    rwa [relabel_fst_apply, fermionFlavor_flavMap, fermionFlavor_flavMap] at this
  · intro h a
    obtain ⟨x, rfl⟩ := (extF π).surjective a
    rw [relabel_fst_apply, fermionFlavor_flavMap, fermionFlavor_flavMap]
    exact h x

/-- A flavoring preserved by `σ` is constant on its cycles. -/
theorem fermionFlavor_eq_of_sameCycle {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    {φ : Flavoring κ} (hφ : Preserves C φ) {x y : Fin nf ⊕ Wick.FermionVertex κ}
    (h : Equiv.Perm.SameCycle C.1.1 x y) : fermionFlavor φ x = fermionFlavor φ y := by
  obtain ⟨i, rfl⟩ := h
  have hinv : ∀ z, fermionFlavor φ (C.1.1⁻¹ z) = fermionFlavor φ z := fun z => by
    rw [← hφ (C.1.1⁻¹ z)]
    simp
  induction i using Int.induction_on generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ← ih]
    exact (hφ x).symm
  | pred n ih =>
    rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply, ← ih]
    exact (hinv x).symm

theorem sameCycle_relabel_iff (x y : Fin nf ⊕ Wick.FermionVertex (gauges N)) :
    Equiv.Perm.SameCycle C.1.1 x y ↔
      Equiv.Perm.SameCycle (relabel π C).1.1 (extF π x) (extF π y) := by
  have h : (relabel π C).1.1 = (extF π : Equiv.Perm _) * C.1.1 * (extF π : Equiv.Perm _)⁻¹ :=
    Equiv.ext fun _ => rfl
  rw [h, Equiv.Perm.sameCycle_conj]
  simp

/-- The fermion cycles of `C` and of `relabel π C`. -/
def cycleEquiv : Quotient (Equiv.Perm.SameCycle.setoid C.1.1) ≃
    Quotient (Equiv.Perm.SameCycle.setoid (relabel π C).1.1) :=
  Quotient.congr (extF π) (sameCycle_relabel_iff π C)

theorem cycleEquiv_mk (x : Fin nf ⊕ Wick.FermionVertex (gauges N)) :
    cycleEquiv π C (Quotient.mk _ x) = Quotient.mk _ (extF π x) :=
  rfl

/-- The closed fermion loops of `C` and of `relabel π C`. -/
def closedLoopEquiv : ClosedLoop C ≃ ClosedLoop (relabel π C) :=
  Equiv.subtypeEquiv (cycleEquiv π C) fun q => by
    refine forall_congr' fun i => not_congr ?_
    rw [← (cycleEquiv π C).injective.eq_iff, cycleEquiv_mk]
    rfl

open scoped Classical in
/-- Relabelling preserves the regulator weight (X₇) of a preserved flavoring. -/
theorem loopWeight_relabel (P : Params) {φ : Flavoring (gauges N)} (hφ : Preserves C φ) :
    loopWeight P (relabel π C) (flavMap π φ) = loopWeight P C φ := by
  have hφ' := (preserves_relabel_iff π C φ).mpr hφ
  unfold loopWeight
  symm
  apply Fintype.prod_equiv (closedLoopEquiv π C)
  intro q
  have hmk : (closedLoopEquiv π C q).1 = Quotient.mk _ (extF π q.1.out) := by
    change cycleEquiv π C q.1 = _
    conv_lhs => rw [← Quotient.out_eq q.1]
    rfl
  have hsc : Equiv.Perm.SameCycle (relabel π C).1.1 (closedLoopEquiv π C q).1.out
      (extF π q.1.out) := by
    have h : (Quotient.mk _ (closedLoopEquiv π C q).1.out :
        Quotient (Equiv.Perm.SameCycle.setoid (relabel π C).1.1)) =
          Quotient.mk _ (extF π q.1.out) := by
      rw [Quotient.out_eq, hmk]
    exact Quotient.exact h
  rw [fermionFlavor_eq_of_sameCycle hφ' hsc, fermionFlavor_flavMap]

/-- The Feynman-gauge photon propagator is unchanged by reversing the line. -/
theorem photonPropagator_neg_swap (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε (-k) ν μ = QED.OneLoop.photonPropagator mγ Λ ε k μ ν := by
  have hm : Minkowski.metric ν μ = Minkowski.metric μ ν := by
    unfold Minkowski.metric
    by_cases h : μ = ν
    · subst h; rfl
    · simp [h, Ne.symm h]
  have hd : Minkowski.dot (-k) (-k) = Minkowski.dot k k := by
    simp [Minkowski.dot]
  simp only [QED.OneLoop.photonPropagator, hm, hd]

open scoped Classical in
/-- Relabelling the amplitude (T₇): the amplitude of `relabel π C` with the relabelled flavoring
at line momenta `k'` is the amplitude of `C` at the pulled-back line momenta. -/
theorem contractionAmplitude₂_relabel (P : Params) (φ : Flavoring (gauges N))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (relabel π C) → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude₂ P (relabel π C) (flavMap π φ) pIn kIn k' αOut βIn μ =
      contractionAmplitude₂ P C φ pIn kIn ((relabelCorr π C).pull k') αOut βIn μ := by
  unfold contractionAmplitude₂
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr (fvPerm π) (Equiv.refl (Fin 4))) _ _ fun α => ?_
  refine Fintype.sum_equiv (Equiv.arrowCongr (fvPerm π) (Equiv.refl (Fin 4))) _ _ fun β => ?_
  refine Fintype.sum_equiv (Equiv.arrowCongr (psPerm π) (Equiv.refl (Fin 4))) _ _ fun lor => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, vertexFactor_gauges]
  have hα : (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ↔
      (∀ i t, (relabel π C).1.1 (.inl i) = .inr t → (α ∘ (fvPerm π).symm) t = αOut i) := by
    simp only [relabel_fst_inl, extF_eq_inr_iff, Function.comp_apply]
    exact forall_congr' fun i => ((fvPerm π).symm.forall_congr_right
      (q := fun t => C.1.1 (.inl i) = .inr t → α t = αOut i)).symm
  have hβ : (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ↔
      (∀ t i, (relabel π C).1.1 (.inr t) = .inl i → (β ∘ (fvPerm π).symm) t = βIn i) := by
    simp only [relabel_fst_inr, extF_eq_inl_iff, Function.comp_apply]
    exact ((fvPerm π).symm.forall_congr_right
      (q := fun t => ∀ i, C.1.1 (.inr t) = .inl i → β t = βIn i)).symm
  have hlor : (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) ↔
      (∀ j a, (relabel π C).1.2 (.inl j) = .inr a → (lor ∘ (psPerm π).symm) a = μ j) := by
    simp only [relabel_snd_inl, extP_eq_inr_iff, Function.comp_apply]
    exact forall_congr' fun j => ((psPerm π).symm.forall_congr_right
      (q := fun a => C.1.2 (.inl j) = .inr a → lor a = μ j)).symm
  congr 1
  · exact if_congr (and_congr hα (and_congr hβ hlor)) rfl rfl
  congr 1
  congr 1
  · refine Fintype.prod_equiv π _ _ fun t => ?_
    have e : ∀ y : Wick.FermionVertex (gauges N), y.1 = π t →
        (fvPerm π).symm y = ⟨t, fun h => Wick.VertexKind.noConfusion h⟩ := fun y hy =>
      Subtype.ext (show π.symm y.1 = t by rw [hy, π.symm_apply_apply])
    simp only [Function.comp_apply, id_eq, psPerm_symm_mk]
    rw [e _ rfl]
  · refine Fintype.prod_equiv (fermionLineEquiv π C) _ _ fun f => ?_
    simp only [Function.comp_apply, id_eq, flavMap_val, tail_fermionLineEquiv,
      fermionLineEquiv_val, Equiv.symm_apply_apply, pull_inl]
  · refine Fintype.prod_bijective (photonLineMap π C)
      ⟨photonLineMap_injective π C, photonLineMap_surjective π C⟩ _ _ fun g => ?_
    simp only [Function.comp_apply]
    have hk : k' (lineEquiv π C (.inr g)) = k' (.inr (photonLineMap π C g)) := rfl
    by_cases h : Wick.photonKey (psPerm π g.1) < Wick.photonKey (psPerm π g.head)
    · obtain ⟨h1, h2⟩ := photonLineMap_of_lt π C g h
      rw [h1, h2, Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← hk]
      simp [LineCorr.pull, relabelCorr, relabelRev, h]
    · obtain ⟨h1, h2⟩ := photonLineMap_of_not_lt π C g h
      rw [h1, h2, Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← hk,
        ← photonPropagator_neg_swap]
      simp [LineCorr.pull, relabelCorr, relabelRev, h]

open scoped Classical in
/-- **Relabelling the regulated amplitude** (T₈): the regulated amplitude of `relabel π C` at line
momenta `k'` is that of `C` at the pulled-back line momenta. -/
theorem regulatedAmplitude₂_relabel (P : Params) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (relabel π C) → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    regulatedAmplitude₂ P (relabel π C) pIn kIn k' αOut βIn μ =
      regulatedAmplitude₂ P C pIn kIn ((relabelCorr π C).pull k') αOut βIn μ := by
  unfold regulatedAmplitude₂
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  refine Fintype.sum_equiv (flavMap π) _ _ fun φ => ?_
  by_cases hφ : Preserves C φ
  · have hφ' := (preserves_relabel_iff π C φ).mpr hφ
    simp only [hφ, hφ', ↓reduceIte, loopWeight_relabel π C P hφ, contractionAmplitude₂_relabel]
  · have hφ' : ¬ Preserves (relabel π C) (flavMap π φ) := mt (preserves_relabel_iff π C φ).mp hφ
    simp only [hφ, hφ', ↓reduceIte]

end Amplitude

/-! ### The value -/

section Value

/-- The value (T₁₀) with the number of loops given as `L`. -/
theorem contractionValue₂_eq_of_loopCount (P : Params) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction nf nA κ} {L : ℕ} (hL : loopCount C = L) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue₂ P C pOut pIn kIn αOut βIn μ =
      jointEnergyFirstIntegral L fun ℓ => (((2 * Real.pi) ^ (4 * L) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  subst hL
  rfl

/-- **Relabelling invariance of the value** (T₁₀) of a contraction of `N` gauge vertices with
connected vertices (X₁₇) whose external momenta (X₁₉) sum to zero. -/
theorem contractionValue₂_relabel (P : Params) (π : Equiv.Perm (Fin N))
    (C : Contraction nf nA (gauges N)) (hV : VerticesConnected C)
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue₂ P (relabel π C) pOut pIn kIn αOut βIn μ =
      contractionValue₂ P C pOut pIn kIn αOut βIn μ := by
  have hV' := (verticesConnected_relabel_iff π C).mpr hV
  have hL' := loopCount_relabel π C hV
  obtain ⟨M, hM, a, h⟩ := (relabelCorr π C).exists_routing_change hV hV'
    (externalMomentum_relabel π C pOut pIn kIn) hsum rfl hL'
  rw [contractionValue₂_eq_of_loopCount P hL', contractionValue₂_eq_of_loopCount P rfl]
  simp only [regulatedAmplitude₂_relabel, h]
  exact JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add _
    (fun ℓ => (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) M hM a

/-- With attached externals (X₁₆), the external momenta flowing into the vertices sum to
`∑ pIn + ∑ kIn - ∑ pOut`. -/
theorem sum_externalMomentum {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (hA : ExternalsAttached C) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) :
    ∑ v, externalMomentum C pOut pIn kIn v = ∑ i, pIn i + ∑ j, kIn j - ∑ i, pOut i := by
  classical
  unfold externalMomentum
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;> rw [Finset.sum_comm] <;>
    refine Finset.sum_congr rfl fun i _ => ?_
  · have hc : ∀ v, (∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inr t) = .inl i) ↔
        (LoopBound.fermionExt hA i).1 = v := fun v => by
      constructor
      · rintro ⟨t, rfl, ht⟩
        have := C.1.1.injective (ht.trans (LoopBound.apply_inr_fermionExt hA i).symm)
        rw [Sum.inr_injective this]
      · rintro rfl
        exact ⟨_, rfl, LoopBound.apply_inr_fermionExt hA i⟩
    simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  · have hj : C.1.2 (.inl i) = .inr (LoopBound.photonExt hA i) := by
      rw [LoopBound.photonExt, Sum.inr_getRight]
    have hc : ∀ v, (∃ a : Wick.PhotonSlot κ, a.1 = v ∧ C.1.2 (.inl i) = .inr a) ↔
        (LoopBound.photonExt hA i).1 = v := fun v => by
      constructor
      · rintro ⟨a, rfl, ha⟩
        rw [Sum.inr_injective (hj.symm.trans ha)]
      · rintro rfl
        exact ⟨_, rfl, hj⟩
    simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  · obtain ⟨s, hs⟩ : ∃ s, C.1.1 (.inl i) = .inr s := by
      rcases h : C.1.1 (.inl i) with j | s
      · exact absurd h (hA.1 i j)
      · exact ⟨s, rfl⟩
    have hc : ∀ v, (∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inl i) = .inr t) ↔
        s.1 = v := fun v => by
      constructor
      · rintro ⟨t, rfl, ht⟩
        rw [Sum.inr_injective (hs.symm.trans ht)]
      · rintro rfl
        exact ⟨_, rfl, hs⟩
    simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- **Relabelling invariance for 1PI contractions** of `N` gauge vertices, under momentum
conservation `∑ pOut = ∑ pIn + ∑ kIn`. -/
theorem contractionValue₂_relabel_of_isOnePI (P : Params) (π : Equiv.Perm (Fin N))
    {C : Contraction nf nA (gauges N)} (hC : IsOnePI C) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue₂ P (relabel π C) pOut pIn kIn αOut βIn μ =
      contractionValue₂ P C pOut pIn kIn αOut βIn μ :=
  contractionValue₂_relabel P π C hC.2.1
    (by rw [sum_externalMomentum hC.1, hmom, sub_self]) αOut βIn μ

end Value

end QED.TwoLoop.Relabel

end
