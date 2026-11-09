/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPoint
public import QED.WickModel.Compatibility
import QED.Wick.ClassificationBasic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Graph and routing lemmas for the two-point functions

General facts about the contractions of the general Wick model (packet 6a, decision D-24), used to
reduce the two-point 1PI functions at order `≤ 2` to their trees and one-loop integrals
(decisions D-23, D-25).

* `isEmpty_contraction_of_not_two_dvd`: an odd number of photon fields admits no contraction.
* `not_isOnePI_of_isEmpty_fermionVertex`, `not_isOnePI_of_isEmpty_photonSlot`: an external field
  with no vertex field to pair with leaves the contraction non-1PI.
* `IsOnePI.exists_crosses_ne`: in a 1PI contraction with at least two vertices, every vertex is an
  end of two distinct internal lines that are not self-loops.
* `isOnePI_of_fin_two`: with two vertices, two distinct lines joining them make a contraction with
  attached externals 1PI.
* `IsOnePI.isLoopLine_iff`: in a 1PI contraction the loop line is the lowest-labelled line.
* `lineMomentum_of_forall_eq_or`: the routing of a contraction with two internal lines.
* `sum_pi_eq_of_forall_eq_or_eq`: a sum over the functions on a two-element type.
* `QED.OneLoop.energyFirstIntegral_const_mul`: the energy-first integral is homogeneous.
-/

@[expose] public section

open Complex

namespace QED.OneLoop

/-- The energy-first integral commutes with multiplication by a constant, for every integrand. -/
theorem energyFirstIntegral_const_mul (c : ℂ) (F : (Fin 4 → ℝ) → ℂ) :
    energyFirstIntegral (fun ℓ => c * F ℓ) = c * energyFirstIntegral F := by
  unfold energyFirstIntegral
  simp only [MeasureTheory.integral_const_mul]

/-- The photon propagator is even in its momentum. -/
theorem photonPropagator_neg (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    photonPropagator mγ Λ ε (-k) μ ν = photonPropagator mγ Λ ε k μ ν := by
  simp [photonPropagator, Minkowski.dot]

/-- The photon propagator is symmetric in its Lorentz indices. -/
theorem photonPropagator_comm (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    photonPropagator mγ Λ ε k μ ν = photonPropagator mγ Λ ε k ν μ := by
  simp only [photonPropagator, Minkowski.metric_symm μ ν]

end QED.OneLoop

namespace QED.WickModel

/-! ### Finite sums -/

section Sums

/-- A sum over the functions on a type covered by two distinct elements `u, v` is a double sum
over their values at `u` and `v`. -/
theorem sum_pi_eq_of_forall_eq_or_eq {X R M : Type*} [Fintype X] [DecidableEq X] [Fintype R]
    [AddCommMonoid M] {u v : X} (huv : u ≠ v) (hX : ∀ x, x = u ∨ x = v) (g : (X → R) → M) :
    ∑ f, g f = ∑ x, ∑ y, g (fun t => if t = u then x else y) := by
  let e : (X → R) ≃ R × R :=
    { toFun := fun f => (f u, f v)
      invFun := fun q t => if t = u then q.1 else q.2
      left_inv := fun f => by
        funext t
        rcases hX t with rfl | rfl <;> simp [huv.symm]
      right_inv := fun q => by simp [huv.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- A sum over the functions on a type with a single element `u` is a sum over the value at
`u`. -/
theorem sum_pi_eq_of_forall_eq {X R M : Type*} [Fintype X] [DecidableEq X] [Fintype R]
    [AddCommMonoid M] {u : X} (hX : ∀ x, x = u) (g : (X → R) → M) :
    ∑ f, g f = ∑ x, g (fun _ => x) := by
  let e : (X → R) ≃ R :=
    { toFun := fun f => f u
      invFun := fun x _ => x
      left_inv := fun f => by
        funext t
        rw [hX t]
      right_inv := fun _ => rfl }
  exact (e.symm.sum_comp g).symm

/-- A product over `Fin 2` in either order. -/
theorem prod_fin_two_eq_mul {M : Type*} [CommMonoid M] {a b : Fin 2} (hab : a ≠ b)
    (F : Fin 2 → M) : ∏ t, F t = F a * F b := by
  rw [Fin.prod_univ_two]
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · rfl
  · exact mul_comm _ _
  · exact absurd rfl hab

end Sums

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Contractions that are empty or not 1PI -/

/-- There is no contraction when the number of photon fields, counting the externals, is odd: a
fixed-point-free involution needs a carrier of even cardinality. -/
theorem isEmpty_contraction_of_not_two_dvd
    (h : ¬ 2 ∣ Fintype.card (Fin nA ⊕ Wick.PhotonSlot κ)) : IsEmpty (Contraction nf nA κ) := by
  refine ⟨fun C => ?_⟩
  have hsq : C.1.2 ^ 2 ^ 1 = 1 := Equiv.ext fun a => by simp [pow_two, (C.2 a).1]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime h hsq
  exact (C.2 a).2 ha

/-- A sum over the 1PI contractions vanishes when no contraction is 1PI. -/
theorem sum_isOnePI_eq_zero {M : Type*} [AddCommMonoid M] [Fintype (Contraction nf nA κ)]
    [DecidablePred (IsOnePI (nf := nf) (nA := nA) (κ := κ))]
    (h : ∀ C : Contraction nf nA κ, ¬ IsOnePI C) (F : Contraction nf nA κ → M) :
    ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter IsOnePI, F C = 0 :=
  Finset.sum_eq_zero fun C hC => absurd (Finset.mem_filter.mp hC).2 (h C)

/-- If the vertices carry no `Ψ̄ Ψ` pair, an external `Ψ(x)` can only be contracted with an
external `Ψ̄(y)`, so no contraction is 1PI. -/
theorem not_isOnePI_of_isEmpty_fermionVertex [IsEmpty (Wick.FermionVertex κ)] {n : ℕ}
    (C : Contraction (n + 1) nA κ) : ¬ IsOnePI C := by
  intro hC
  rcases h : C.1.1 (.inl 0) with i | t
  · exact hC.1.1 0 i h
  · exact isEmptyElim t

/-- If the vertices carry no photon field, an external `A(z)` can only be contracted with another
external photon, so no contraction is 1PI. -/
theorem not_isOnePI_of_isEmpty_photonSlot [IsEmpty (Wick.PhotonSlot κ)] {n : ℕ}
    (C : Contraction nf (n + 1) κ) : ¬ IsOnePI C := by
  intro hC
  rcases h : C.1.2 (.inl 0) with i | a
  · exact hC.1.2 0 i h
  · exact isEmptyElim a

/-! ### Crossing lines -/

/-- The internal line `f` is not a self-loop and has an end at the vertex `v`, so it crosses the
cut between `{v}` and the other vertices. -/
def Line.Crosses {C : Contraction nf nA κ} (f : Line C) (v : Fin N) : Prop :=
  f.ends.1 ≠ f.ends.2 ∧ (f.ends.1 = v ∨ f.ends.2 = v)

/-- `Joined` is symmetric. -/
theorem Joined.symm {C : Contraction nf nA κ} {S : Set (Line C)} {u w : Fin N}
    (h : Joined C S u w) : Joined C S w u := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨f, hf, h.symm⟩

/-- If the vertex `v` is connected to a different vertex by the internal lines outside `S`, then
some line outside `S` crosses the cut around `v`. -/
theorem exists_crosses_of_reflTransGen {C : Contraction nf nA κ} {S : Set (Line C)} {v w : Fin N}
    (hvw : v ≠ w) (h : Relation.ReflTransGen (Joined C S) v w) : ∃ f ∉ S, f.Crosses v := by
  by_contra hne
  push Not at hne
  refine hvw (Wick.reflTransGen_mem_of_closed (A := {v}) ?_ h rfl).symm
  rintro x y ⟨f, hfS, hf⟩ rfl
  by_contra hy
  apply hne f hfS
  rcases hf with hf | hf <;> simp only [Line.Crosses, hf] <;> exact ⟨by simpa [eq_comm] using hy,
    by simp⟩

/-- In a 1PI contraction, a vertex `v` (in a graph with another vertex `w`) is an end of two
distinct internal lines that are not self-loops: no line is a bridge. -/
theorem IsOnePI.exists_crosses_ne {C : Contraction nf nA κ} (hC : IsOnePI C) {v w : Fin N}
    (hvw : v ≠ w) : ∃ f₁ f₂ : Line C, f₁ ≠ f₂ ∧ f₁.Crosses v ∧ f₂.Crosses v := by
  obtain ⟨f₁, -, h₁⟩ := exists_crosses_of_reflTransGen hvw (hC.2.1 v w)
  have hb : Relation.ReflTransGen (Joined C {f₁}) f₁.ends.1 f₁.ends.2 := not_not.mp (hC.2.2 f₁)
  have hsymm : ∀ {x y}, Relation.ReflTransGen (Joined C {f₁}) x y →
      Relation.ReflTransGen (Joined C {f₁}) y x := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact (Relation.ReflTransGen.single hab.symm).trans ih
  have key : ∀ {x y : Fin N}, x ≠ y → Relation.ReflTransGen (Joined C {f₁}) x y →
      ∃ f₂ : Line C, f₁ ≠ f₂ ∧ f₂.Crosses x := fun hxy h => by
    obtain ⟨f₂, h₂S, h₂⟩ := exists_crosses_of_reflTransGen hxy h
    exact ⟨f₂, fun h => h₂S (by simp [h]), h₂⟩
  rcases h₁.2 with h | h
  · obtain ⟨f₂, hne, h₂⟩ := key h₁.1 hb
    exact ⟨f₁, f₂, hne, h₁, h ▸ h₂⟩
  · obtain ⟨f₂, hne, h₂⟩ := key (Ne.symm h₁.1) (hsymm hb)
    exact ⟨f₁, f₂, hne, h₁, h ▸ h₂⟩

/-! ### Two vertices -/

/-- Two pairs of distinct elements of `Fin 2` agree up to order. -/
theorem fin_two_pair_eq_or {x y u w : Fin 2} (hxy : x ≠ y) (huw : u ≠ w) :
    (x, y) = (u, w) ∨ (x, y) = (w, u) := by
  revert x y u w
  decide

/-- **A criterion for one-particle irreducibility with two vertices.** If the externals are
attached and two distinct internal lines join the two vertices, the contraction is 1PI. -/
theorem isOnePI_of_fin_two {κ : Fin 2 → Wick.VertexKind} {C : Contraction nf nA κ}
    (hext : ExternalsAttached C) {f₁ f₂ : Line C} (h12 : f₁ ≠ f₂) (h₁ : f₁.ends.1 ≠ f₁.ends.2)
    (h₂ : f₂.ends.1 ≠ f₂.ends.2) : IsOnePI C := by
  have hjoin : ∀ {S : Set (Line C)} {g : Line C}, g ∉ S → g.ends.1 ≠ g.ends.2 →
      ∀ {u w : Fin 2}, u ≠ w → Joined C S u w := fun hgS hg _ _ huw =>
    ⟨_, hgS, fin_two_pair_eq_or hg huw⟩
  refine ⟨hext, fun u w => ?_, fun f hf => hf ?_⟩
  · by_cases huw : u = w
    · rw [huw]
    · exact .single (hjoin (Set.notMem_empty f₁) h₁ huw)
  · by_cases hf' : f.ends.1 = f.ends.2
    · rw [hf']
    · by_cases hf₁ : f = f₁
      · subst hf₁
        exact .single (hjoin (g := f₂) (fun h => h12 (Set.mem_singleton_iff.mp h).symm) h₂ hf')
      · exact .single (hjoin (g := f₁) (fun h => hf₁ (Set.mem_singleton_iff.mp h).symm) h₁ hf')

/-! ### Loop lines and routing -/

/-- In a 1PI contraction no line is a bridge, so the loop line is the lowest-labelled line. -/
theorem IsOnePI.isLoopLine_iff {C : Contraction nf nA κ} (hC : IsOnePI C) (f : Line C) :
    IsLoopLine f ↔ ∀ g : Line C, f.label ≤ g.label := by
  unfold IsLoopLine
  simp only [hC.2.2, not_false_eq_true, forall_const, true_and]

/-- The loop line carries the loop momentum. -/
theorem lineMomentum_of_isLoopLine {C : Contraction nf nA κ} {f : Line C} (hf : IsLoopLine f)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) :
    lineMomentum C pOut pIn kIn ℓ f = ℓ := by
  rw [lineMomentum, ite_eq_left hf]

open scoped Classical in
/-- **The routing of a contraction with two internal lines.** If the internal lines are the loop
line `l` and another line `f`, then `f` carries the momentum injected at its tail: the external
momentum there, plus the loop momentum entering or leaving through `l`. -/
theorem lineMomentum_of_forall_eq_or {C : Contraction nf nA κ} {f l : Line C}
    (hloop : ∀ g, IsLoopLine g ↔ g = l) (hfl : f ≠ l) (hall : ∀ g, g = f ∨ g = l)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) :
    lineMomentum C pOut pIn kIn ℓ f = externalMomentum C pOut pIn kIn f.ends.1 +
      ((if l.ends.2 = f.ends.1 then ℓ else 0) - (if l.ends.1 = f.ends.1 then ℓ else 0)) := by
  have hJ : ∀ v, ¬ Joined C {g | g = f ∨ IsLoopLine g} f.ends.1 v := by
    rintro v ⟨g, hg, -⟩
    refine hg ?_
    rcases hall g with h | h
    · exact Or.inl h
    · exact Or.inr ((hloop g).2 h)
  rw [lineMomentum, ite_eq_right fun h => hfl ((hloop f).1 h)]
  have hV : (Finset.univ.filter fun v => Relation.ReflTransGen
      (Joined C {g | g = f ∨ IsLoopLine g}) f.ends.1 v) = {f.ends.1} := by
    ext v
    simp [Relation.reflTransGen_iff_eq hJ]
  have hL : (Finset.univ.filter fun g : Line C => IsLoopLine g) = {l} := by
    ext g
    simp [hloop]
  rw [hV, hL, Finset.sum_singleton, Finset.sum_singleton]

/-- The momentum through a `Ψ` field contracted with an external `Ψ̄(yᵢ)` is `pIn i`. -/
theorem psiMomentum_of_eq_inl {C : Contraction nf nA κ} {t : Wick.FermionVertex κ} {i : Fin nf}
    (h : C.1.1 (.inr t) = .inl i) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) : psiMomentum C pOut pIn kIn ℓ t = pIn i := by
  rw [psiMomentum]
  split
  · next j hj => rw [h, Sum.inl.injEq] at hj; rw [hj]
  · next s hs => rw [h] at hs; exact absurd hs Sum.inl_ne_inr

open scoped Classical in
/-- Without internal photon lines, the momentum through a vertex photon field is the external
photon momentum contracted with it. -/
theorem photonMomentum_of_isEmpty {C : Contraction nf nA κ} [IsEmpty (PhotonLine C)]
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ)
    (a : Wick.PhotonSlot κ) :
    photonMomentum C pOut pIn kIn ℓ a = ∑ j, if C.1.2 (.inl j) = .inr a then kIn j else 0 := by
  rw [photonMomentum, Finset.univ_eq_empty (α := PhotonLine C), Finset.sum_empty, add_zero]

/-- The tail of an internal fermion line is the vertex whose `Ψ̄` is contracted with its `Ψ`. -/
theorem FermionLine.tail_eq {C : Contraction nf nA κ} {f : FermionLine C}
    {s : Wick.FermionVertex κ} (h : C.1.1 (.inr f.1) = .inr s) : f.tail = s := by
  apply Sum.inr_injective
  rw [FermionLine.tail, Sum.inr_getRight, h]

/-- The head of an internal photon line is the vertex field contracted with its indexing
field. -/
theorem PhotonLine.head_eq {C : Contraction nf nA κ} {g : PhotonLine C}
    {s : Wick.PhotonSlot κ} (h : C.1.2 (.inr g.1) = .inr s) : g.head = s := by
  apply Sum.inr_injective
  rw [PhotonLine.head, Sum.inr_getRight, h]

/-- With the external `Ψ(x)` contracted with the `Ψ̄` of `s`, the constraint on the spinor
indices of the `Ψ̄` fields fixes that of `s`. -/
theorem spinor_constraint_out_iff_of_one {C : Contraction 1 nA κ} {s : Wick.FermionVertex κ}
    (h : C.1.1 (.inl 0) = .inr s) (α : Wick.FermionVertex κ → Fin 4) (αOut : Fin 1 → Fin 4) :
    (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ↔ α s = αOut 0 := by
  simp only [Fin.forall_fin_one, h, Sum.inr.injEq, forall_eq']

/-- With the external `Ψ̄(y)` contracted with the `Ψ` of `t₀`, the constraint on the spinor
indices of the `Ψ` fields fixes that of `t₀`. -/
theorem spinor_constraint_in_iff_of_one {C : Contraction 1 nA κ} {t₀ : Wick.FermionVertex κ}
    (h : C.1.1 (.inr t₀) = .inl 0) (β : Wick.FermionVertex κ → Fin 4) (βIn : Fin 1 → Fin 4) :
    (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ↔ β t₀ = βIn 0 := by
  refine ⟨fun H => H t₀ 0 h, fun H t i ht => ?_⟩
  rw [Subsingleton.elim i 0] at ht ⊢
  rw [Sum.inr_injective (C.1.1.injective (ht.trans h.symm))]
  exact H

/-- With the external photons `A(z₁)`, `A(z₂)` contracted with the vertex fields `s₀`, `s₁`, the
constraint on the Lorentz indices of the vertex fields fixes those of `s₀` and `s₁`. -/
theorem lorentz_constraint_iff_of_two {C : Contraction nf 2 κ} {s₀ s₁ : Wick.PhotonSlot κ}
    (h₀ : C.1.2 (.inl 0) = .inr s₀) (h₁ : C.1.2 (.inl 1) = .inr s₁)
    (lor : Wick.PhotonSlot κ → Fin 4) (μ : Fin 2 → Fin 4) :
    (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) ↔ lor s₀ = μ 0 ∧ lor s₁ = μ 1 := by
  simp [Fin.forall_fin_two, h₀, h₁]

/-! ### Trees -/

/-- A contraction without internal lines has the value of its regulated amplitude at `ℓ = 0`. -/
theorem contractionValue_of_isEmpty (P : Params) {C : Contraction nf nA κ} [IsEmpty (Line C)]
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue P C pOut pIn kIn αOut βIn μ =
      regulatedAmplitude P C pOut pIn kIn 0 αOut βIn μ := by
  rw [contractionValue, ite_eq_right fun ⟨f, _⟩ => isEmptyElim f]

/-- A contraction with a loop line has the value of the energy-first integral of its regulated
amplitude. -/
theorem contractionValue_of_isLoopLine (P : Params) {C : Contraction nf nA κ} {f : Line C}
    (hf : IsLoopLine f) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue P C pOut pIn kIn αOut βIn μ =
      QED.OneLoop.energyFirstIntegral fun ℓ =>
        (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ := by
  rw [contractionValue, ite_eq_left ⟨f, hf⟩]

end QED.WickModel

end
