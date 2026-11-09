/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPointClassification
public import QED.Frozen.WickModel.ConnectedFunction
import QED.Wick.ClassificationBasic

/-!
# Graph, routing and splitting lemmas for the three-point function

General facts about the contractions of the general Wick model (packet 6a, decision D-24), used
to decompose the connected three-point function `connectedFunction P 1 1 3` into its 1PI part
and the corrections on its external legs.

* `connectedFunction_eq_onePIFunction_add`: the connected function is the 1PI function plus the
  sum over the connected contractions that are not 1PI.
* `vertexFactor_of_gauge`, `vertexFactor_of_fermionCt`, `vertexFactor_of_photonCt`: the vertex
  factor of a vertex of known kind.
* `Line.label_injective`, `IsLoopLine.isLoopLine_iff`: the loop line is unique.
* `not_isBridge_of_ends_eq`, `not_isBridge_of_parallel`, `isBridge_of_closed`: bridges.
* `not_verticesConnected_of_forall_not_crosses`, `forall_not_crosses_of_isolated`: an isolated
  vertex disconnects a contraction.
* `lineMomentum_of_forall_not_joined`, `lineMomentum_of_joined`: the canonical routing when at
  most one other line leaves the tail of a line.
* `sum_pi_eq_of_three`, `prod_fin_three_eq`: finite sums and products over three elements.
-/

@[expose] public section

open Complex

namespace QED.WickModel

/-! ### Finite sums and products over three elements -/

section Three

/-- A sum over the functions on a type covered by three distinct elements `u, v, w` is a triple
sum over their values. -/
theorem sum_pi_eq_of_three {X R M : Type*} [Fintype X] [DecidableEq X] [Fintype R]
    [AddCommMonoid M] {u v w : X} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hX : ∀ x, x = u ∨ x = v ∨ x = w) (g : (X → R) → M) :
    ∑ f, g f = ∑ x, ∑ y, ∑ z, g (fun t => if t = u then x else if t = v then y else z) := by
  let e : (X → R) ≃ R × R × R :=
    { toFun := fun f => (f u, f v, f w)
      invFun := fun q t => if t = u then q.1 else if t = v then q.2.1 else q.2.2
      left_inv := fun f => by
        funext t
        rcases hX t with rfl | rfl | rfl <;> simp [huv.symm, hvw.symm, huw.symm]
      right_inv := fun q => by simp [huv.symm, hvw.symm, huw.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Three distinct elements of `Fin 3` exhaust it. -/
theorem fin_three_eq_or {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (x : Fin 3) :
    x = a ∨ x = b ∨ x = c := by
  omega

/-- A product over `Fin 3` in the order of three distinct elements. -/
theorem prod_fin_three_eq {M : Type*} [CommMonoid M] {a b c : Fin 3} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) (F : Fin 3 → M) : ∏ t, F t = F a * F b * F c := by
  have hu : (Finset.univ : Finset (Fin 3)) = {a, b, c} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact fin_three_eq_or hab hbc hac x
  rw [hu, Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc, mul_assoc]


/-- Two disjoint swaps covering a four-element type form a fixed-point-free involution. -/
theorem swap_mul_swap_involutive {X : Type*} [DecidableEq X] {a b c d : X} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hX : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d) (x : X) :
    (Equiv.swap a b * Equiv.swap c d) ((Equiv.swap a b * Equiv.swap c d) x) = x ∧
      (Equiv.swap a b * Equiv.swap c d) x ≠ x := by
  rcases hX x with rfl | rfl | rfl | rfl <;>
    simp [Equiv.swap_apply_of_ne_of_ne, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
      had.symm, hbc.symm, hbd.symm, hcd.symm]

/-- A product over a type with exactly two elements. -/
theorem prod_eq_mul_of_two {X M : Type*} [Fintype X] [CommMonoid M] {x y : X} (hxy : x ≠ y)
    (h : ∀ z, z = x ∨ z = y) (F : X → M) : ∏ z, F z = F x * F y := by
  classical
  have hu : (Finset.univ : Finset X) = {x, y} := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact h z
  rw [hu, Finset.prod_pair hxy]

end Three

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Vertex factors of known kind -/

section VertexFactor

variable (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
  (lor : Wick.PhotonSlot κ → Fin 4)
  (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ)

/-- The factor of a gauge vertex: `i e γ^μ`. -/
theorem vertexFactor_of_gauge {t : Fin N} (h : κ t = .gauge) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor ⟨t, ⟨0, by simp [h, Wick.VertexKind.photonSlots]⟩⟩)
        (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

/-- The factor of a fermion counterterm vertex: `-i (δ₂ k̸ + δ_m m)`. -/
theorem vertexFactor_of_fermionCt {t : Fin N} (h : κ t = .fermionCt) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      -I * (((δ₂ : ℂ) • Dirac.slash (kψ ⟨t, by simp [h]⟩)
        + ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
          (α ⟨t, by simp [h]⟩) (β ⟨t, by simp [h]⟩)) := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> first | rfl | exact absurd (h.symm.trans h') (by decide)

/-- The factor of a photon counterterm vertex: half of `-i δ₃ (k² g^{μν} - k^μ k^ν)`. -/
theorem vertexFactor_of_photonCt {t : Fin N} (h : κ t = .photonCt) :
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

/-! ### Lines -/

/-- An internal fermion line runs to the `Ψ` that is contracted with the `Ψ̄` of its tail. -/
theorem FermionLine.apply_eq_inr_tail {C : Contraction nf nA κ} (f : FermionLine C) :
    C.1.1 (.inr f.1) = .inr f.tail := by
  rw [FermionLine.tail, Sum.inr_getRight]

/-- The indexing field of an internal photon line is contracted with its head. -/
theorem PhotonLine.apply_eq_inr_head {C : Contraction nf nA κ} (g : PhotonLine C) :
    C.1.2 (.inr g.1) = .inr g.head := by
  rw [PhotonLine.head, Sum.inr_getRight]

/-- A vertex has at most two photon fields. -/
theorem photonSlots_le_two (k : Wick.VertexKind) : k.photonSlots ≤ 2 := by
  cases k <;> decide

/-- The photon key is injective. -/
theorem photonKey_injective : Function.Injective (Wick.photonKey (κ := κ)) := by
  rintro ⟨t, i⟩ ⟨s, j⟩ h
  have hi := (photonSlots_le_two (κ t))
  have hj := (photonSlots_le_two (κ s))
  have hi' := i.2
  have hj' := j.2
  simp only [Wick.photonKey] at h
  have hts : t = s := Fin.ext (by omega)
  subst hts
  have hij : i = j := Fin.ext (by omega)
  subst hij
  rfl

/-- Distinct internal lines have distinct labels. -/
theorem Line.label_injective {C : Contraction nf nA κ} :
    Function.Injective (Line.label (C := C)) := by
  rintro (f | g) (f' | g') h <;> simp only [Line.label] at h
  · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (Fin.ext h)))
  · omega
  · omega
  · exact congrArg Sum.inr (Subtype.ext (photonKey_injective (by omega)))

/-- **The loop line is unique**: two loop lines have the same label. -/
theorem IsLoopLine.isLoopLine_iff {C : Contraction nf nA κ} {l : Line C} (hl : IsLoopLine l)
    (g : Line C) : IsLoopLine g ↔ g = l := by
  refine ⟨fun hg => Line.label_injective (le_antisymm (hg.2 l hl.1) (hl.2 g hg.1)), ?_⟩
  rintro rfl
  exact hl


/-- The indexing field of an internal photon line has the smaller key. -/
theorem PhotonLine.key_lt_head {C : Contraction nf nA κ} (g : PhotonLine C) :
    Wick.photonKey g.1 < Wick.photonKey g.head := by
  obtain ⟨b, hb, hk⟩ := g.2
  rwa [PhotonLine.head_eq hb]

/-- Two internal photon lines through a common photon field are equal. -/
theorem PhotonLine.eq_of_mem {C : Contraction nf nA κ} {g₁ g₂ : PhotonLine C}
    {z : Wick.PhotonSlot κ} (h₁ : g₁.1 = z ∨ g₁.head = z) (h₂ : g₂.1 = z ∨ g₂.head = z) :
    g₁ = g₂ := by
  have k₁ := g₁.key_lt_head
  have k₂ := g₂.key_lt_head
  have e₁ := g₁.apply_eq_inr_head
  have e₂ := g₂.apply_eq_inr_head
  have hinv : ∀ a, C.1.2 (C.1.2 a) = a := fun a => (C.2 a).1
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Subtype.ext (h₁.trans h₂.symm)
  · have : g₁.head = g₂.1 := by
      apply Sum.inr_injective
      rw [← e₁, h₁, ← h₂, ← e₂, hinv]
    rw [this] at k₁
    rw [h₂, ← h₁] at k₂
    omega
  · have : g₂.head = g₁.1 := by
      apply Sum.inr_injective
      rw [← e₂, h₂, ← h₁, ← e₁, hinv]
    rw [this] at k₂
    rw [h₁, ← h₂] at k₁
    omega
  · apply Subtype.ext
    apply Sum.inr_injective
    apply C.1.2.injective
    rw [e₁, e₂, h₁, h₂]

/-- The internal photon line joining two contracted vertex fields `s` and `s'`. -/
def photonLineOfPair {C : Contraction nf nA κ} {s s' : Wick.PhotonSlot κ}
    (h : C.1.2 (.inr s) = .inr s') (hne : s ≠ s') : PhotonLine C :=
  if hlt : Wick.photonKey s < Wick.photonKey s' then ⟨s, s', h, hlt⟩
  else ⟨s', s, by rw [← h, (C.2 _).1], by
    have := photonKey_injective.ne hne
    omega⟩

/-- The photon line joining `s` and `s'` is indexed by one of them, with the other as head. -/
theorem photonLineOfPair_spec {C : Contraction nf nA κ} {s s' : Wick.PhotonSlot κ}
    (h : C.1.2 (.inr s) = .inr s') (hne : s ≠ s') :
    ((photonLineOfPair h hne).1 = s ∧ (photonLineOfPair h hne).head = s') ∨
      ((photonLineOfPair h hne).1 = s' ∧ (photonLineOfPair h hne).head = s) := by
  unfold photonLineOfPair
  split
  · exact Or.inl ⟨rfl, PhotonLine.head_eq h⟩
  · exact Or.inr ⟨rfl, PhotonLine.head_eq (by rw [← h, (C.2 _).1])⟩

/-- The ends of the photon line joining `s` and `s'`. -/
theorem ends_photonLineOfPair {C : Contraction nf nA κ} {s s' : Wick.PhotonSlot κ}
    (h : C.1.2 (.inr s) = .inr s') (hne : s ≠ s') :
    Line.ends (.inr (photonLineOfPair h hne) : Line C) = (s.1, s'.1) ∨
      Line.ends (.inr (photonLineOfPair h hne) : Line C) = (s'.1, s.1) := by
  change ((photonLineOfPair h hne).1.1, (photonLineOfPair h hne).head.1) = _ ∨
    ((photonLineOfPair h hne).1.1, (photonLineOfPair h hne).head.1) = _
  rcases photonLineOfPair_spec h hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact Or.inl rfl
  · rw [h1, h2]; exact Or.inr rfl

/-- A photon propagator factor in either orientation, at a momentum `±k`. -/
theorem photonPropagator_of_pair {mγ Λ ε : ℝ} {k k' : Fin 4 → ℝ} (hk : k' = k ∨ k' = -k)
    (lor : Wick.PhotonSlot κ → Fin 4) {s s' a b : Wick.PhotonSlot κ}
    (h : (a = s ∧ b = s') ∨ (a = s' ∧ b = s)) :
    QED.OneLoop.photonPropagator mγ Λ ε k' (lor a) (lor b) =
      QED.OneLoop.photonPropagator mγ Λ ε k (lor s) (lor s') := by
  have hk' : QED.OneLoop.photonPropagator mγ Λ ε k' = QED.OneLoop.photonPropagator mγ Λ ε k := by
    rcases hk with rfl | rfl
    · rfl
    · funext μ ν
      exact QED.OneLoop.photonPropagator_neg _ _ _ _ _ _
  rw [hk']
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact QED.OneLoop.photonPropagator_comm _ _ _ _ _ _

/-! ### Bridges -/

/-- A self-loop is not a bridge. -/
theorem not_isBridge_of_ends_eq {C : Contraction nf nA κ} {f : Line C}
    (h : f.ends.1 = f.ends.2) : ¬ IsBridge f := fun hb => hb (by rw [h])

/-- A line with a parallel line is not a bridge. -/
theorem not_isBridge_of_parallel {C : Contraction nf nA κ} {f g : Line C} (hgf : g ≠ f)
    (h : g.ends = f.ends ∨ g.ends = (f.ends.2, f.ends.1)) : ¬ IsBridge f := fun hb =>
  hb (.single ⟨g, fun hg => hgf (Set.mem_singleton_iff.mp hg), h⟩)

/-- A line is a bridge if a set of vertices containing its tail but not its head is closed under
the other lines. -/
theorem isBridge_of_closed {C : Contraction nf nA κ} {f : Line C} (A : Set (Fin N))
    (h₁ : f.ends.1 ∈ A) (h₂ : f.ends.2 ∉ A)
    (hA : ∀ g : Line C, g ≠ f → (g.ends.1 ∈ A ↔ g.ends.2 ∈ A)) : IsBridge f := fun hb => by
  refine h₂ (Wick.reflTransGen_mem_of_closed ?_ hb h₁)
  rintro x y ⟨g, hg, hxy | hxy⟩ hx
  · have := hA g (fun h => hg (Set.mem_singleton_iff.mpr h))
    rw [hxy] at this
    exact this.mp hx
  · have := hA g (fun h => hg (Set.mem_singleton_iff.mpr h))
    rw [hxy] at this
    exact this.mpr hx


/-- A line is a bridge if a set of vertices containing exactly one of its ends is closed under the
other lines. -/
theorem isBridge_of_closed' {C : Contraction nf nA κ} {f : Line C} (A : Set (Fin N))
    (h : (f.ends.1 ∈ A ∧ f.ends.2 ∉ A) ∨ (f.ends.1 ∉ A ∧ f.ends.2 ∈ A))
    (hA : ∀ g : Line C, g ≠ f → (g.ends.1 ∈ A ↔ g.ends.2 ∈ A)) : IsBridge f := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact isBridge_of_closed A h₁ h₂ hA
  · exact isBridge_of_closed Aᶜ h₁ (fun h => h h₂) fun g hg => by
      simp only [Set.mem_compl_iff, not_iff_not]
      exact hA g hg

/-! ### Connectivity -/

/-- If no line crosses the cut around a vertex `v`, and there is another vertex, the vertices are
not connected. -/
theorem not_verticesConnected_of_forall_not_crosses {C : Contraction nf nA κ} {v w : Fin N}
    (hvw : v ≠ w) (h : ∀ f : Line C, ¬ f.Crosses v) : ¬ VerticesConnected C := fun hC => by
  obtain ⟨f, -, hf⟩ := exists_crosses_of_reflTransGen hvw (hC v w)
  exact h f hf

/-- **An isolated vertex.** If the fermion and photon fields of `v` are contracted only with
fields of `v` or with external fields, no line crosses the cut around `v`. -/
theorem forall_not_crosses_of_isolated {C : Contraction nf nA κ} {v : Fin N}
    (hσ : ∀ t s : Wick.FermionVertex κ, C.1.1 (.inr t) = .inr s → (t.1 = v ↔ s.1 = v))
    (hτ : ∀ a b : Wick.PhotonSlot κ, C.1.2 (.inr a) = .inr b → (a.1 = v ↔ b.1 = v)) :
    ∀ f : Line C, ¬ f.Crosses v := by
  rintro (f | g) ⟨hne, h⟩
  · have := hσ _ _ f.apply_eq_inr_tail
    change f.tail.1 ≠ f.1.1 at hne
    change f.tail.1 = v ∨ f.1.1 = v at h
    rcases h with h | h
    · exact hne (h.trans (this.mpr h).symm)
    · exact hne ((this.mp h).trans h.symm)
  · have := hτ _ _ g.apply_eq_inr_head
    change g.1.1 ≠ g.head.1 at hne
    change g.1.1 = v ∨ g.head.1 = v at h
    rcases h with h | h
    · exact hne (h.trans (this.mp h).symm)
    · exact hne ((this.mpr h).trans h.symm)

/-- A line outside `S` with ends `(u, w)` joins `u` and `w`. -/
theorem joined_of_ends {C : Contraction nf nA κ} {S : Set (Line C)} {g : Line C} (hg : g ∉ S)
    {u w : Fin N} (h : g.ends = (u, w)) : Joined C S u w :=
  ⟨g, hg, Or.inl h⟩

/-- **Connectivity of three vertices.** If a line joins `x` to `y` and a line joins `y` to `z`,
for distinct `x, y, z` in `Fin 3`, the vertices are connected. -/
theorem verticesConnected_of_three {κ : Fin 3 → Wick.VertexKind} {C : Contraction nf nA κ}
    {x y z : Fin 3} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (h₁ : Joined C ∅ x y)
    (h₂ : Joined C ∅ y z) : VerticesConnected C :=
  Wick.reflTransGen_of_forall_eq_or (fun _ _ h => h.symm) y (fun u => by
    rcases fin_three_eq_or hxy hyz hxz u with rfl | rfl | rfl
    · exact Or.inr h₁.symm
    · exact Or.inl rfl
    · exact Or.inr h₂)

/-- **Connectivity of two vertices** joined by a line. -/
theorem verticesConnected_of_two {κ : Fin 2 → Wick.VertexKind} {C : Contraction nf nA κ}
    {x y : Fin 2} (hxy : x ≠ y) (h : Joined C ∅ x y) : VerticesConnected C :=
  Wick.reflTransGen_of_forall_eq_or (fun _ _ h => h.symm) x (fun u => by
    rcases (by omega : u = x ∨ u = y) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr h)

/-! ### Routing -/

open scoped Classical in
/-- The loop-momentum term of the routing with a unique loop line `l`. -/
theorem sum_isLoopLine_eq {C : Contraction nf nA κ} {l : Line C} (hl : IsLoopLine l)
    (ℓ : Fin 4 → ℝ) (v : Fin N) :
    ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
        ((if g.ends.2 = v then ℓ else 0) - (if g.ends.1 = v then ℓ else 0)) =
      (if l.ends.2 = v then ℓ else 0) - (if l.ends.1 = v then ℓ else 0) := by
  have hL : (Finset.univ.filter fun g : Line C => IsLoopLine g) = {l} := by
    ext g
    simp [hl.isLoopLine_iff]
  rw [hL, Finset.sum_singleton]

open scoped Classical in
/-- **The routing when no line leaves the tail.** If no internal line outside `f` and the loop
lines joins the tail of `f` to another vertex, `f` carries the momentum injected at its tail. -/
theorem lineMomentum_of_forall_not_joined {C : Contraction nf nA κ} {f : Line C}
    (hf : ¬ IsLoopLine f)
    (h : ∀ w, Joined C {g | g = f ∨ IsLoopLine g} f.ends.1 w → w = f.ends.1)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) :
    lineMomentum C pOut pIn kIn ℓ f = externalMomentum C pOut pIn kIn f.ends.1 +
      ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
        ((if g.ends.2 = f.ends.1 then ℓ else 0) - (if g.ends.1 = f.ends.1 then ℓ else 0)) := by
  rw [lineMomentum, ite_eq_right hf]
  have hR : (Finset.univ.filter fun v => Relation.ReflTransGen
      (Joined C {g | g = f ∨ IsLoopLine g}) f.ends.1 v) = {f.ends.1} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hv
      exact (Wick.reflTransGen_mem_of_closed (A := {f.ends.1})
        (fun x y hxy hx => by rw [Set.mem_singleton_iff] at hx ⊢; subst hx; exact h y hxy)
        hv rfl : v ∈ ({f.ends.1} : Set (Fin N)))
    · rintro rfl
      exact .refl
  rw [hR, Finset.sum_singleton]

open scoped Classical in
/-- **The routing when one line leaves the tail.** If the line `g` outside `f` and the loop lines
joins the tail of `f` to another vertex `x`, and every other line outside `f` and the loop lines
is `g`, then `f` carries the momentum injected at its tail and at `x`. -/
theorem lineMomentum_of_joined {C : Contraction nf nA κ} {f g : Line C} (hf : ¬ IsLoopLine f)
    (hgS : g ∉ {g | g = f ∨ IsLoopLine g}) {x : Fin N} (hx : x ≠ f.ends.1)
    (hg : g.ends = (f.ends.1, x) ∨ g.ends = (x, f.ends.1))
    (hall : ∀ g' : Line C, g' ∉ {g | g = f ∨ IsLoopLine g} → g' = g)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) :
    lineMomentum C pOut pIn kIn ℓ f =
      (externalMomentum C pOut pIn kIn f.ends.1 +
        ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
          ((if g.ends.2 = f.ends.1 then ℓ else 0) - (if g.ends.1 = f.ends.1 then ℓ else 0))) +
      (externalMomentum C pOut pIn kIn x +
        ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
          ((if g.ends.2 = x then ℓ else 0) - (if g.ends.1 = x then ℓ else 0))) := by
  rw [lineMomentum, ite_eq_right hf]
  have hJ : Joined C {g | g = f ∨ IsLoopLine g} f.ends.1 x := ⟨g, hgS, hg⟩
  have hR : (Finset.univ.filter fun v => Relation.ReflTransGen
      (Joined C {g | g = f ∨ IsLoopLine g}) f.ends.1 v) = {f.ends.1, x} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hv
      refine (Wick.reflTransGen_mem_of_closed (A := {f.ends.1, x}) ?_ hv (by simp) :
        v ∈ ({f.ends.1, x} : Set (Fin N)))
      rintro u w ⟨g', hg'S, hg'⟩ hu
      obtain rfl := hall g' hg'S
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
      rcases hg with hg | hg <;> rcases hg' with hg' | hg' <;> rw [hg] at hg' <;>
        simp only [Prod.mk.injEq] at hg' <;> obtain ⟨h1, h2⟩ := hg' <;> subst h1 h2 <;> simp
    · rintro (rfl | rfl)
      · exact .refl
      · exact .single hJ
  rw [hR, Finset.sum_pair hx.symm]


/-! ### Momenta and constraints with one external fermion pair and one external photon -/

/-- The external momentum at a vertex, with `Ψ(x)` attached to `a`, `Ψ̄(y)` to `b` and `A(z)` to
the photon field `s₀`. -/
theorem externalMomentum_eq_of_one {C : Contraction 1 1 κ} {a b : Wick.FermionVertex κ}
    {s₀ : Wick.PhotonSlot κ} (ha : C.1.1 (.inl 0) = .inr a) (hb : C.1.1 (.inr b) = .inl 0)
    (hs : C.1.2 (.inl 0) = .inr s₀) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin N) :
    externalMomentum C pOut pIn kIn v =
      (if b.1 = v then pIn 0 else 0) + (if s₀.1 = v then kIn 0 else 0) -
        (if a.1 = v then pOut 0 else 0) := by
  have h1 : (∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inr t) = .inl 0) ↔ b.1 = v :=
    ⟨fun ⟨t, ht, h⟩ => by rwa [Sum.inr_injective (C.1.1.injective (h.trans hb.symm))] at ht,
      fun h => ⟨b, h, hb⟩⟩
  have h2 : (∃ s : Wick.PhotonSlot κ, s.1 = v ∧ C.1.2 (.inl 0) = .inr s) ↔ s₀.1 = v :=
    ⟨fun ⟨s, hsv, h⟩ => by rwa [Sum.inr_injective (h.symm.trans hs)] at hsv,
      fun h => ⟨s₀, h, hs⟩⟩
  have h3 : (∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inl 0) = .inr t) ↔ a.1 = v :=
    ⟨fun ⟨t, ht, h⟩ => by rwa [Sum.inr_injective (h.symm.trans ha)] at ht,
      fun h => ⟨a, h, ha⟩⟩
  unfold externalMomentum
  simp only [Fin.sum_univ_one, Fin.isValue, h1, h2, h3]

/-- The momentum through the `Ψ` of an internal fermion line is the momentum of the line. -/
theorem psiMomentum_eq_lineMomentum {C : Contraction nf nA κ} (f : FermionLine C)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) :
    psiMomentum C pOut pIn kIn ℓ f.1 = lineMomentum C pOut pIn kIn ℓ (.inl f) := by
  rw [psiMomentum]
  split
  · next i h => rw [f.apply_eq_inr_tail] at h; exact absurd h Sum.inr_ne_inl
  · rfl

/-- With the external photon contracted with the vertex field `s₀`, the constraint on the Lorentz
indices of the vertex fields fixes that of `s₀`. -/
theorem lorentz_constraint_iff_of_one {C : Contraction nf 1 κ} {s₀ : Wick.PhotonSlot κ}
    (h : C.1.2 (.inl 0) = .inr s₀) (lor : Wick.PhotonSlot κ → Fin 4) (μ : Fin 1 → Fin 4) :
    (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) ↔ lor s₀ = μ 0 := by
  simp only [Fin.forall_fin_one, h, Sum.inr.injEq, forall_eq']

/-- The electron flavoring gives every fermion the electron mass. -/
@[simp]
theorem mass_electronFlavoring (P : Params) (x : Wick.FermionVertex κ) :
    P.mass ((electronFlavoring κ).1 x) = P.m := rfl

/-- With one external photon, it is attached to a vertex field. -/
theorem photon_attached_of_one {C : Contraction nf 1 κ} (i j : Fin 1) :
    C.1.2 (.inl i) ≠ .inl j := by
  rw [Subsingleton.elim i j]
  exact (C.2 _).2

/-! ### Splitting off the 1PI part -/

open scoped Classical in
/-- **The connected function is the 1PI function plus the connected contractions that are not
1PI.** -/
theorem connectedFunction_eq_onePIFunction_add (P : Params) (nf nA K : ℕ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    connectedFunction P nf nA K pOut pIn kIn αOut βIn μ =
      onePIFunction P nf nA K pOut pIn kIn αOut βIn μ +
        ∑ N ∈ Finset.range (K + 1), (N.factorial : ℂ)⁻¹ *
          ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
              (fun κ => ∑ t, (κ t).order ≤ K),
            ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter
                (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C),
              ((fermionSign C : ℤ) : ℂ) * contractionValue P C pOut pIn kIn αOut βIn μ := by
  rw [connectedFunction, onePIFunction, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not _ IsOnePI, Finset.filter_filter,
    Finset.filter_filter]
  congr 2
  ext C
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

/-- With at most one vertex every internal line is a self-loop, so a connected contraction with
attached externals is 1PI. -/
theorem isOnePI_of_le_one (hN : N ≤ 1) {C : Contraction nf nA κ} (hext : ExternalsAttached C)
    (hconn : VerticesConnected C) : IsOnePI C :=
  ⟨hext, hconn, fun f => not_isBridge_of_ends_eq (by
    have h1 := f.ends.1.2
    have h2 := f.ends.2.2
    exact Fin.ext (by omega))⟩

/-- Without vertices an external `Ψ(x)` can only be contracted with an external `Ψ̄(y)`. -/
theorem not_externalsAttached_of_fin_zero {κ : Fin 0 → Wick.VertexKind} {n : ℕ}
    (C : Contraction (n + 1) nA κ) : ¬ ExternalsAttached C := fun h => by
  rcases hC : C.1.1 (.inl 0) with i | t
  · exact h.1 0 i hC
  · exact t.1.elim0

end QED.WickModel

end
