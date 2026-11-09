/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPointClassificationBasic

/-!
# The two-point functions without loops

The terms of the two-point 1PI functions of the general Wick model (packet 6a, decision D-24) with
at most one vertex: the electron self-energy `onePIFunction P 1 0 2` and the vacuum polarization
`onePIFunction P 0 2 2` (decisions D-23, D-25).

* Without vertices there is no 1PI contraction.
* With one vertex, the self-energy has only the `fermionCt` tree `selfEnergyTree`, of sign `+1`
  and value `-i (δ₂ p̸ + δ_m m)`, the external `Ψ(x)` giving the row and `Ψ̄(y)` the column.
* With one vertex, the vacuum polarization has only the two `photonCt` trees
  `polarizationTree a b`, one for each pairing of the external photons with the two photon fields
  of the vertex. Each has sign `+1` and value half of `-i δ₃ (k² g^{μν} - k^μ k^ν)`.

## Main statements

* `sum_isOnePI_selfEnergyTree`: the 1PI part of a single `fermionCt` vertex.
* `sum_isOnePI_polarizationTree`: the 1PI part of a single `photonCt` vertex.
* `not_isOnePI_oneVertex_selfEnergy`, `not_isOnePI_oneVertex_polarization`: no other single
  vertex has a 1PI contraction.
-/

@[expose] public section

open Complex

namespace QED.WickModel

/-- The vertex sequence of a single vertex of kind `k`. -/
abbrev oneVertex (k : Wick.VertexKind) : Fin 1 → Wick.VertexKind := fun _ => k

/-- Every sequence of one vertex is `oneVertex` of its kind. -/
theorem eq_oneVertex (κ : Fin 1 → Wick.VertexKind) : κ = oneVertex (κ 0) :=
  funext fun t => by rw [Subsingleton.elim t 0]

/-! ### No vertices -/

/-- Without vertices, no contraction with an external fermion pair is 1PI. -/
theorem not_isOnePI_of_fin_zero_left {κ : Fin 0 → Wick.VertexKind} {n nA : ℕ}
    (C : Contraction (n + 1) nA κ) : ¬ IsOnePI C :=
  haveI : IsEmpty (Wick.FermionVertex κ) := ⟨fun t => t.1.elim0⟩
  not_isOnePI_of_isEmpty_fermionVertex C

/-- Without vertices, no contraction with an external photon is 1PI. -/
theorem not_isOnePI_of_fin_zero_right {κ : Fin 0 → Wick.VertexKind} {nf n : ℕ}
    (C : Contraction nf (n + 1) κ) : ¬ IsOnePI C :=
  haveI : IsEmpty (Wick.PhotonSlot κ) := ⟨fun a => a.1.elim0⟩
  not_isOnePI_of_isEmpty_photonSlot C

/-! ### Single vertices that do not contribute -/

/-- A single `photonCt` vertex carries no `Ψ̄ Ψ`. -/
instance : IsEmpty (Wick.FermionVertex (oneVertex .photonCt)) := ⟨fun t => t.2 rfl⟩

/-- A single `fermionCt` vertex carries no photon field. -/
instance : IsEmpty (Wick.PhotonSlot (oneVertex .fermionCt)) := ⟨fun a => by
  obtain ⟨_, j⟩ := a
  exact j.elim0⟩

/-- The only single vertex with a 1PI contraction of one external fermion pair is `fermionCt`:
`gauge` and `gaugeCt` have an odd number of photon fields, and `photonCt` has no `Ψ̄ Ψ`. -/
theorem not_isOnePI_oneVertex_selfEnergy {k : Wick.VertexKind} (hk : k ≠ .fermionCt)
    (C : Contraction 1 0 (oneVertex k)) : ¬ IsOnePI C := by
  cases k
  · exact (isEmpty_contraction_of_not_two_dvd (by decide)).elim C
  · exact (isEmpty_contraction_of_not_two_dvd (by decide)).elim C
  · exact absurd rfl hk
  · exact not_isOnePI_of_isEmpty_fermionVertex C

/-- The only single vertex with a 1PI contraction of two external photons is `photonCt`: `gauge`
and `gaugeCt` have an odd number of photon fields, and `fermionCt` has none. -/
theorem not_isOnePI_oneVertex_polarization {k : Wick.VertexKind} (hk : k ≠ .photonCt)
    (C : Contraction 0 2 (oneVertex k)) : ¬ IsOnePI C := by
  cases k
  · exact (isEmpty_contraction_of_not_two_dvd (by decide)).elim C
  · exact (isEmpty_contraction_of_not_two_dvd (by decide)).elim C
  · exact not_isOnePI_of_isEmpty_photonSlot C
  · exact absurd rfl hk

/-! ### The `fermionCt` tree -/

/-- The fermion vertex of a single `fermionCt` vertex. -/
def ctFv : Wick.FermionVertex (oneVertex .fermionCt) := ⟨0, by decide⟩

/-- A single `fermionCt` vertex has one fermion vertex. -/
theorem eq_ctFv (t : Wick.FermionVertex (oneVertex .fermionCt)) : t = ctFv :=
  Subtype.ext (Subsingleton.elim _ _)

/-- A single `fermionCt` vertex carries one `Ψ̄ Ψ`. -/
instance : Unique (Wick.FermionVertex (oneVertex .fermionCt)) := ⟨⟨ctFv⟩, eq_ctFv⟩

/-- The tree of a single `fermionCt` vertex: `Ψ(x)` is contracted with the vertex's `Ψ̄` and
`Ψ̄(y)` with its `Ψ`. -/
def selfEnergyTree : Contraction 1 0 (oneVertex .fermionCt) :=
  ⟨(Equiv.swap (.inl 0) (.inr ctFv), 1), fun b => by
    rcases b with i | a
    · exact i.elim0
    · exact isEmptyElim a⟩

/-- The tree has no internal fermion line. -/
instance : IsEmpty (FermionLine selfEnergyTree) :=
  ⟨fun f => by
    obtain ⟨t, ht⟩ := f
    rw [eq_ctFv t] at ht
    simp [selfEnergyTree] at ht⟩

/-- The tree has no internal photon line. -/
instance : IsEmpty (PhotonLine selfEnergyTree) := ⟨fun g => isEmptyElim g.1⟩

/-- The tree has no internal line. -/
instance : IsEmpty (Line selfEnergyTree) := inferInstanceAs (IsEmpty (_ ⊕ _))

/-- The only 1PI contraction of a single `fermionCt` vertex is the tree. -/
theorem isOnePI_iff_eq_selfEnergyTree (C : Contraction 1 0 (oneVertex .fermionCt)) :
    IsOnePI C ↔ C = selfEnergyTree := by
  constructor
  · intro hC
    have h0 : C.1.1 (.inl 0) = .inr ctFv := by
      rcases h : C.1.1 (.inl 0) with i | t
      · exact absurd h (hC.1.1 0 i)
      · rw [eq_ctFv t]
    have h1 : C.1.1 (.inr ctFv) = .inl 0 := by
      rcases h : C.1.1 (.inr ctFv) with i | t
      · rw [Subsingleton.elim i 0]
      · rw [eq_ctFv t] at h
        exact absurd (C.1.1.injective (h.trans h0.symm)) Sum.inr_ne_inl
    apply Subtype.ext
    apply Prod.ext
    · ext1 x
      rcases x with i | t
      · rw [Subsingleton.elim i 0, h0]
        simp [selfEnergyTree]
      · rw [eq_ctFv t, h1]
        simp [selfEnergyTree]
    · ext1 x
      rcases x with i | a
      · exact i.elim0
      · exact isEmptyElim a
  · rintro rfl
    refine ⟨⟨fun i j => ?_, fun i => i.elim0⟩, fun u w => ?_, fun f => isEmptyElim f⟩
    · rw [Subsingleton.elim i 0]
      simp [selfEnergyTree]
    · rw [Subsingleton.elim u w]

/-- The tree has fermionic sign `+1`: `(-1)¹` from the vertex times the sign `-1` of a
transposition. -/
theorem fermionSign_selfEnergyTree : fermionSign selfEnergyTree = 1 := by
  simp [fermionSign, selfEnergyTree]

/-- The factor of a single `fermionCt` vertex. -/
theorem vertexFactor_fermionCt (e δ₁ δ₂ δm δ₃ m : ℝ)
    (α β : Wick.FermionVertex (oneVertex .fermionCt) → Fin 4)
    (lor : Wick.PhotonSlot (oneVertex .fermionCt) → Fin 4)
    (kψ : Wick.FermionVertex (oneVertex .fermionCt) → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot (oneVertex .fermionCt) → Fin 4 → ℝ) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA 0 =
      -I * (((δ₂ : ℂ) • Dirac.slash (kψ ctFv) +
        ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) (α ctFv) (β ctFv)) := rfl

/-- The value of the `fermionCt` tree: `-i (δ₂ p̸ + δ_m m)` at the incoming momentum, the external
`Ψ(x)` giving the row and `Ψ̄(y)` the column. -/
theorem contractionValue_selfEnergyTree (P : Params) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4) :
    contractionValue P selfEnergyTree pOut pIn kIn αOut βIn μ =
      -I * (((P.δ₂ : ℂ) • Dirac.slash (pIn 0) +
        ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) (αOut 0) (βIn 0)) := by
  have hφ : ∀ φ : Flavoring (oneVertex .fermionCt), Preserves selfEnergyTree φ →
      φ = electronFlavoring _ := fun φ _ =>
    Subtype.ext (funext fun t => φ.2 t (by intro h; cases h))
  have hψ : psiMomentum selfEnergyTree pOut pIn kIn 0 ctFv = pIn 0 :=
    psiMomentum_of_eq_inl (by simp [selfEnergyTree]) _ _ _ _
  rw [contractionValue_of_isEmpty, regulatedAmplitude_eq_of_forall_preserves P hφ,
    contractionAmplitude]
  simp only [Fin.prod_univ_one, vertexFactor_fermionCt, hψ, Finset.univ_eq_empty,
    Finset.prod_empty, mul_one]
  simp only [sum_pi_eq_of_forall_eq eq_ctFv, Fintype.sum_unique]
  simp [selfEnergyTree, Fin.forall_fin_one, ctFv, ite_and]

/-- The 1PI part of a single `fermionCt` vertex: the tree `-i (δ₂ p̸ + δ_m m)`. -/
theorem sum_isOnePI_selfEnergyTree (P : Params)
    [Fintype (Contraction 1 0 (oneVertex .fermionCt))]
    [DecidablePred (IsOnePI (nf := 1) (nA := 0) (κ := oneVertex .fermionCt))]
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin 0 → Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 0 (oneVertex .fermionCt))).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * contractionValue P C pOut pIn kIn αOut βIn μ =
      -I * (((P.δ₂ : ℂ) • Dirac.slash (pIn 0) +
        ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) (αOut 0) (βIn 0)) := by
  rw [Finset.sum_eq_single_of_mem selfEnergyTree
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (isOnePI_iff_eq_selfEnergyTree _).mpr rfl⟩)
      fun C hC hne => absurd ((isOnePI_iff_eq_selfEnergyTree C).mp (Finset.mem_filter.mp hC).2)
        hne,
    fermionSign_selfEnergyTree, contractionValue_selfEnergyTree]
  simp

/-! ### The `photonCt` trees -/

/-- The photon field `j` of a single `photonCt` vertex. -/
def ctPs (j : Fin 2) : Wick.PhotonSlot (oneVertex .photonCt) := ⟨0, j⟩

/-- Every photon field of a single `photonCt` vertex is `ctPs j`. -/
theorem eq_ctPs (a : Wick.PhotonSlot (oneVertex .photonCt)) : a = ctPs a.2 := by
  obtain ⟨t, j⟩ := a
  obtain rfl := Subsingleton.elim t 0
  rfl

/-- The photon fields of a single `photonCt` vertex are the fields `a` and `b`, for `a ≠ b`. -/
theorem ctPs_eq_or : ∀ a b : Fin 2, a ≠ b →
    ∀ s : Wick.PhotonSlot (oneVertex .photonCt), s = ctPs a ∨ s = ctPs b := by
  decide

/-- The photon fields of a single `photonCt` vertex are distinct. -/
theorem ctPs_injective : Function.Injective ctPs := fun _ _ h =>
  eq_of_heq (Sigma.mk.inj_iff.mp h).2

/-- The photon fields of a single `photonCt` vertex are distinct. -/
@[simp]
theorem ctPs_inj {i j : Fin 2} : ctPs i = ctPs j ↔ i = j := ctPs_injective.eq_iff

/-- The photon pairing of the tree `polarizationTree a b`: `A(z₁)` with the photon field `a` and
`A(z₂)` with the photon field `b`. -/
def polarizationPairing (a b : Fin 2) :
    Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot (oneVertex .photonCt)) :=
  Equiv.swap (.inl 0) (.inr (ctPs a)) * Equiv.swap (.inl 1) (.inr (ctPs b))

/-- The pairing of the tree is a fixed-point-free involution. -/
theorem polarizationPairing_involutive : ∀ a b : Fin 2, a ≠ b →
    ∀ x, polarizationPairing a b (polarizationPairing a b x) = x ∧
      polarizationPairing a b x ≠ x := by
  decide

/-- The tree of a single `photonCt` vertex in which the external photon `A(z₁)` is contracted
with the photon field `a` and `A(z₂)` with the photon field `b`. -/
def polarizationTree (a b : Fin 2) (hab : a ≠ b) : Contraction 0 2 (oneVertex .photonCt) :=
  ⟨(1, polarizationPairing a b), polarizationPairing_involutive a b hab⟩

/-- The pairing of the tree sends `A(z₁)` to the photon field `a`. -/
theorem polarizationPairing_inl_zero : ∀ a b : Fin 2,
    polarizationPairing a b (.inl 0) = .inr (ctPs a) := by
  decide

/-- The pairing of the tree sends `A(z₂)` to the photon field `b`. -/
theorem polarizationPairing_inl_one : ∀ a b : Fin 2, a ≠ b →
    polarizationPairing a b (.inl 1) = .inr (ctPs b) := by
  decide

/-- The pairing of the tree sends the photon field `a` to `A(z₁)`. -/
theorem polarizationPairing_inr_left : ∀ a b : Fin 2, a ≠ b →
    polarizationPairing a b (.inr (ctPs a)) = .inl 0 := by
  decide

/-- The pairing of the tree sends the photon field `b` to `A(z₂)`. -/
theorem polarizationPairing_inr_right : ∀ a b : Fin 2, a ≠ b →
    polarizationPairing a b (.inr (ctPs b)) = .inl 1 := by
  decide

/-- The pairing of the tree contracts every photon field of the vertex with an external
photon. -/
theorem polarizationPairing_inr_isLeft : ∀ a b : Fin 2, a ≠ b →
    ∀ s, (polarizationPairing a b (.inr s)).isLeft := by
  decide

/-- The pairing of the tree contracts every external photon with a vertex field. -/
theorem polarizationPairing_inl_ne_inl : ∀ a b : Fin 2, a ≠ b →
    ∀ i j, polarizationPairing a b (.inl i) ≠ .inl j := by
  decide

section PolarizationTree

variable (a b : Fin 2) (hab : a ≠ b)

/-- Without external fermions, a single `photonCt` vertex has no fermion field. -/
instance : IsEmpty (Fin 0 ⊕ Wick.FermionVertex (oneVertex .photonCt)) :=
  inferInstanceAs (IsEmpty (_ ⊕ _))

/-- The tree has no internal fermion line. -/
instance : IsEmpty (FermionLine (polarizationTree a b hab)) := ⟨fun f => isEmptyElim f.1⟩

/-- The tree has no internal photon line. -/
instance : IsEmpty (PhotonLine (polarizationTree a b hab)) := ⟨fun g => by
  obtain ⟨s, s', hs, -⟩ := g
  have h := polarizationPairing_inr_isLeft a b hab s
  change polarizationPairing a b (.inr s) = .inr s' at hs
  rw [hs] at h
  exact Bool.false_ne_true h⟩

/-- The tree has no internal line. -/
instance : IsEmpty (Line (polarizationTree a b hab)) := inferInstanceAs (IsEmpty (_ ⊕ _))

/-- The tree is 1PI. -/
theorem isOnePI_polarizationTree : IsOnePI (polarizationTree a b hab) :=
  ⟨⟨fun i => i.elim0, polarizationPairing_inl_ne_inl a b hab⟩,
    fun u w => by rw [Subsingleton.elim u w], fun f => isEmptyElim f⟩

/-- The tree has fermionic sign `+1`: it has no fermion field. -/
theorem fermionSign_polarizationTree : fermionSign (polarizationTree a b hab) = 1 := by
  simp [fermionSign, polarizationTree]

end PolarizationTree

/-- **The 1PI contractions of a single `photonCt` vertex** are the two trees, one for each pairing
of the external photons with the photon fields of the vertex. -/
theorem isOnePI_iff_polarizationTree (C : Contraction 0 2 (oneVertex .photonCt)) :
    IsOnePI C ↔ C = polarizationTree 0 1 (by decide) ∨ C = polarizationTree 1 0 (by decide) := by
  constructor
  · intro hC
    have hext : ∀ j, ∃ a, C.1.2 (.inl j) = .inr (ctPs a) := fun j => by
      rcases h : C.1.2 (.inl j) with i | s
      · exact absurd h (hC.1.2 j i)
      · exact ⟨s.2, by rw [← eq_ctPs]⟩
    obtain ⟨a, ha⟩ := hext 0
    obtain ⟨b, hb⟩ := hext 1
    have hab : a ≠ b := by
      rintro rfl
      exact absurd (C.1.2.injective (ha.trans hb.symm)) (by decide)
    have ha' : C.1.2 (.inr (ctPs a)) = .inl 0 := by rw [← ha, (C.2 _).1]
    have hb' : C.1.2 (.inr (ctPs b)) = .inl 1 := by rw [← hb, (C.2 _).1]
    have key : C = polarizationTree a b hab := by
      apply Subtype.ext
      apply Prod.ext
      · ext1 x
        exact isEmptyElim x
      · ext1 x
        change C.1.2 x = polarizationPairing a b x
        rcases x with i | s
        · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
          · rw [ha, polarizationPairing_inl_zero]
          · rw [hb, polarizationPairing_inl_one a b hab]
        · rcases ctPs_eq_or a b hab s with rfl | rfl
          · rw [ha', polarizationPairing_inr_left a b hab]
          · rw [hb', polarizationPairing_inr_right a b hab]
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
    · exact Or.inl key
    · exact Or.inr key
  · rintro (rfl | rfl) <;> exact isOnePI_polarizationTree _ _ _

/-- The factor of a single `photonCt` vertex. -/
theorem vertexFactor_photonCt (e δ₁ δ₂ δm δ₃ m : ℝ)
    (α β : Wick.FermionVertex (oneVertex .photonCt) → Fin 4)
    (lor : Wick.PhotonSlot (oneVertex .photonCt) → Fin 4)
    (kψ : Wick.FermionVertex (oneVertex .photonCt) → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot (oneVertex .photonCt) → Fin 4 → ℝ) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA 0 =
      -(I / 2) * ((δ₃ * (Minkowski.dot (kA (ctPs 0)) (kA (ctPs 0)) *
          Minkowski.metric (lor (ctPs 0)) (lor (ctPs 1)) -
        kA (ctPs 0) (lor (ctPs 0)) * kA (ctPs 0) (lor (ctPs 1))) : ℝ) : ℂ) := rfl

/-- **The value of a `photonCt` tree**: half of `-i δ₃ (k² g^{μν} - k^μ k^ν)`, where `k` is the
momentum of the external photon `A(z_a)` contracted with the first photon field of the vertex. -/
theorem contractionValue_polarizationTree (P : Params) (a b : Fin 2) (hab : a ≠ b)
    (pOut pIn : Fin 0 → Fin 4 → ℝ) (kIn : Fin 2 → Fin 4 → ℝ) (αOut βIn : Fin 0 → Fin 4)
    (μ : Fin 2 → Fin 4) :
    contractionValue P (polarizationTree a b hab) pOut pIn kIn αOut βIn μ =
      -(I / 2) * ((P.δ₃ * (Minkowski.dot (kIn a) (kIn a) * Minkowski.metric (μ 0) (μ 1) -
        kIn a (μ 0) * kIn a (μ 1)) : ℝ) : ℂ) := by
  have hφ : ∀ φ : Flavoring (oneVertex .photonCt), Preserves (polarizationTree a b hab) φ →
      φ = electronFlavoring _ := fun φ _ => Subtype.ext (funext fun t => isEmptyElim t)
  have h0 : (polarizationTree a b hab).1.2 (.inl 0) = .inr (ctPs a) :=
    polarizationPairing_inl_zero a b
  have h1 : (polarizationTree a b hab).1.2 (.inl 1) = .inr (ctPs b) :=
    polarizationPairing_inl_one a b hab
  rw [contractionValue_of_isEmpty, regulatedAmplitude_eq_of_forall_preserves P hφ,
    contractionAmplitude]
  simp only [Fin.prod_univ_one, vertexFactor_photonCt, photonMomentum_of_isEmpty,
    Finset.univ_eq_empty, Finset.prod_empty, mul_one, Fintype.sum_unique,
    lorentz_constraint_iff_of_two h0 h1, IsEmpty.forall_iff, true_and,
    Fin.sum_univ_two, h0, h1, Sum.inr.injEq, ctPs_inj]
  rw [Fintype.sum_eq_single (fun s => if s = ctPs a then μ 0 else μ 1) fun lor hlor => ?_]
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
    · simp
    · simp [Minkowski.metric_symm (μ 1), mul_comm (kIn 1 (μ 1))]
  · have hne : ¬ (lor (ctPs a) = μ 0 ∧ lor (ctPs b) = μ 1) := fun h => hlor (funext fun s => by
      rcases ctPs_eq_or a b hab s with rfl | rfl
      · simp [h.1]
      · simp [h.2, (ctPs_injective.ne hab).symm])
    rw [ite_eq_right hne, zero_mul]

/-- The two `photonCt` trees are distinct. -/
theorem polarizationTree_ne :
    polarizationTree 0 1 (by decide) ≠ polarizationTree 1 0 (by decide) := fun h => by
  have h' := congrArg (fun C : Contraction 0 2 (oneVertex .photonCt) => C.1.2 (.inl 0)) h
  simp only [polarizationTree, polarizationPairing_inl_zero, Sum.inr.injEq, ctPs_inj] at h'
  exact absurd h' (by decide)

/-- The 1PI part of a single `photonCt` vertex, with the external photons carrying `k` and `-k`
and the Lorentz indices `μ`, `ν`: the two pairings each give half of
`-i δ₃ (k² g^{μν} - k^μ k^ν)`. -/
theorem sum_isOnePI_polarizationTree (P : Params)
    [Fintype (Contraction 0 2 (oneVertex .photonCt))]
    [DecidablePred (IsOnePI (nf := 0) (nA := 2) (κ := oneVertex .photonCt))]
    (pOut pIn : Fin 0 → Fin 4 → ℝ) (αOut βIn : Fin 0 → Fin 4) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 0 2 (oneVertex .photonCt))).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * contractionValue P C pOut pIn ![k, -k] αOut βIn ![μ, ν] =
      -I * ((P.δ₃ * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ) := by
  classical
  have hfilter : (Finset.univ : Finset (Contraction 0 2 (oneVertex .photonCt))).filter IsOnePI =
      {polarizationTree 0 1 (by decide), polarizationTree 1 0 (by decide)} := by
    ext C
    simp [isOnePI_iff_polarizationTree]
  have hdot : Minkowski.dot (-k) (-k) = Minkowski.dot k k := by simp [Minkowski.dot]
  rw [hfilter, Finset.sum_pair polarizationTree_ne, fermionSign_polarizationTree,
    fermionSign_polarizationTree, contractionValue_polarizationTree,
    contractionValue_polarizationTree]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hdot,
    Pi.neg_apply, neg_mul_neg, Int.cast_one, one_mul]
  ring

end QED.WickModel

end
