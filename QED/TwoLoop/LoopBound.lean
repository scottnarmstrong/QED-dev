/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.Wick.VertexKindOrder
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# At most one loop below the two-loop order

A contraction with attached externals and connected vertices whose total order is at most
`2 nf + nA + 1` has at most one chord (T₁), so `loopCount C ≤ 1` (T₂). This is the
graph-counting half of the theorem goal (T₁₄).

The proof bounds the number of chords by `E - V + 1`:

* The lines that are not chords connect the vertices (`reflTransGen_joined_chords`): the ends of
  a chord are joined by lines of larger label, and induction downward on the label replaces
  each of these by lines that are not chords.
* A connected graph on `V` vertices has at least `V - 1` edges
  (`SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`), so at least `V - 1` lines are not
  chords (`card_le_card_nonChord_add_one`).
* Field counting with attached externals gives `E + nf ≤ #(Ψ̄Ψ vertices)` and
  `2 E_γ + nA ≤ #(photon fields)`, hence `2 E ≤ 2 V + K - 2 nf - nA ≤ 2 V + 1`
  (`two_mul_card_line_le`), so `E ≤ V`.

Together, `#chords = E - #(non-chords) ≤ V - (V - 1) = 1`; the case `V = 0` needs no separate
treatment, since then there are no lines.
-/

@[expose] public section

namespace QED.TwoLoop.LoopBound

open QED.WickModel Relation

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Joining is symmetric -/

theorem joined_symm {C : Contraction nf nA κ} {S : Set (Line C)} {u w : Fin N}
    (h : Joined C S u w) : Joined C S w u := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨f, hf, h.symm⟩

theorem reflTransGen_joined_symm {C : Contraction nf nA κ} {S : Set (Line C)} {u w : Fin N}
    (h : ReflTransGen (Joined C S) u w) : ReflTransGen (Joined C S) w u := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ReflTransGen.head (joined_symm hbc) ih

/-- If the ends of every line outside `S` are connected outside `T`, then any two vertices
connected outside `S` are connected outside `T`. -/
theorem reflTransGen_joined_of_ends {C : Contraction nf nA κ} {S T : Set (Line C)}
    (hST : ∀ g : Line C, g ∉ S → ReflTransGen (Joined C T) g.ends.1 g.ends.2) {u w : Fin N}
    (h : ReflTransGen (Joined C S) u w) : ReflTransGen (Joined C T) u w := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih =>
    obtain ⟨g, hg, hends⟩ := hbc
    have hg' := hST g hg
    rcases hends with hends | hends
    · rw [hends] at hg'
      exact ih.trans hg'
    · rw [hends] at hg'
      exact ih.trans (reflTransGen_joined_symm hg')

/-! ### The lines that are not chords connect the vertices -/

/-- The ends of every line are connected by lines that are not chords. -/
theorem reflTransGen_joined_chords_ends (C : Contraction nf nA κ) (f : Line C) :
    ReflTransGen (Joined C {g | IsChord g}) f.ends.1 f.ends.2 := by
  let r : Line C → Line C → Prop := fun g f => f.label < g.label
  have : IsTrans (Line C) r := ⟨fun _ _ _ hab hbc => lt_trans hbc hab⟩
  have : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
  induction f using (Finite.wellFounded_of_trans_of_irrefl r).induction with
  | _ f ih =>
    by_cases hf : IsChord f
    · refine reflTransGen_joined_of_ends (fun g hg => ih g ?_) hf
      exact lt_of_not_ge hg
    · exact ReflTransGen.single ⟨f, hf, Or.inl rfl⟩

/-- With connected vertices (X₁₇), any two vertices are connected by lines that are not
chords. -/
theorem reflTransGen_joined_chords {C : Contraction nf nA κ} (hC : VerticesConnected C)
    (u w : Fin N) : ReflTransGen (Joined C {g | IsChord g}) u w :=
  reflTransGen_joined_of_ends (fun g _ => reflTransGen_joined_chords_ends C g) (hC u w)

/-! ### At least `V - 1` lines are not chords -/

/-- The simple graph on the vertices whose edges are the lines that are not chords, with
self-loops and multiple lines dropped. -/
private def nonChordGraph (C : Contraction nf nA κ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (Joined C {g | IsChord g})

private theorem nonChordGraph_reachable {C : Contraction nf nA κ} (hC : VerticesConnected C)
    (u w : Fin N) : (nonChordGraph C).Reachable u w := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction reflTransGen_joined_chords hC u w with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    by_cases hb : b = c
    · exact hb ▸ ih
    · exact ih.tail ⟨hb, Or.inl hbc⟩

private theorem exists_nonChord_of_mem_edgeSet {C : Contraction nf nA κ}
    (e : (nonChordGraph C).edgeSet) :
    ∃ g : {g : Line C // ¬ IsChord g}, s(g.1.ends.1, g.1.ends.2) = e.1 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u w =>
    obtain ⟨-, h | h⟩ := he
    · obtain ⟨g, hg, hends | hends⟩ := h
      · exact ⟨⟨g, hg⟩, by simp [hends]⟩
      · exact ⟨⟨g, hg⟩, by simp [hends, Sym2.eq_swap]⟩
    · obtain ⟨g, hg, hends | hends⟩ := h
      · exact ⟨⟨g, hg⟩, by simp [hends, Sym2.eq_swap]⟩
      · exact ⟨⟨g, hg⟩, by simp [hends]⟩

/-- The edges of `nonChordGraph C` are at most the lines that are not chords. -/
private theorem card_edgeSet_nonChordGraph_le (C : Contraction nf nA κ) :
    Nat.card (nonChordGraph C).edgeSet ≤ Nat.card {g : Line C // ¬ IsChord g} := by
  choose F hF using exists_nonChord_of_mem_edgeSet (C := C)
  refine Nat.card_le_card_of_injective F fun e e' h => Subtype.ext ?_
  rw [← hF e, ← hF e', h]

/-- With connected vertices (X₁₇), at least `V - 1` lines are not chords. -/
theorem card_le_card_nonChord_add_one {C : Contraction nf nA κ} (hC : VerticesConnected C) :
    N ≤ Nat.card {g : Line C // ¬ IsChord g} + 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · omega
  have hconn : (nonChordGraph C).Connected :=
    { preconnected := nonChordGraph_reachable hC
      nonempty := ⟨⟨0, hN⟩⟩ }
  have := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_fin] at this
  have := card_edgeSet_nonChordGraph_le C
  omega

/-! ### Field counting -/

theorem isRight_symm_inl {C : Contraction nf nA κ} (hC : ExternalsAttached C) (i : Fin nf) :
    (C.1.1.symm (.inl i)).isRight := by
  rcases h : C.1.1.symm (.inl i) with j | t
  · exact absurd (by rw [← h, Equiv.apply_symm_apply]) (hC.1 j i)
  · rfl

/-- The `Ψ̄Ψ` vertex whose `Ψ` is contracted with the external `Ψ̄(yᵢ)`. -/
def fermionExt {C : Contraction nf nA κ} (hC : ExternalsAttached C) (i : Fin nf) :
    Wick.FermionVertex κ :=
  (C.1.1.symm (.inl i)).getRight (isRight_symm_inl hC i)

theorem apply_inr_fermionExt {C : Contraction nf nA κ} (hC : ExternalsAttached C) (i : Fin nf) :
    C.1.1 (.inr (fermionExt hC i)) = .inl i := by
  rw [fermionExt, Sum.inr_getRight, Equiv.apply_symm_apply]

/-- Every internal fermion line and every external `Ψ̄` uses the `Ψ` of a distinct vertex. -/
theorem card_fermionLine_add_le {C : Contraction nf nA κ} (hC : ExternalsAttached C) :
    Nat.card (FermionLine C) + nf ≤ Nat.card (Wick.FermionVertex κ) := by
  let F : FermionLine C ⊕ Fin nf → Wick.FermionVertex κ
    | .inl f => f.1
    | .inr i => fermionExt hC i
  have hF : Function.Injective F := by
    rintro (f | i) (f' | i') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have := f.2
      simp only [F] at h
      rw [h, apply_inr_fermionExt] at this
      simp at this
    · have := f'.2
      simp only [F] at h
      rw [← h, apply_inr_fermionExt] at this
      simp at this
    · have := apply_inr_fermionExt hC i
      simp only [F] at h
      rw [h, apply_inr_fermionExt] at this
      exact congrArg Sum.inr (Sum.inl_injective this).symm
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_sum, Nat.card_fin] at this

theorem isRight_photon_inl {C : Contraction nf nA κ} (hC : ExternalsAttached C) (j : Fin nA) :
    (C.1.2 (.inl j)).isRight := by
  rcases h : C.1.2 (.inl j) with i | a
  · exact absurd h (hC.2 j i)
  · rfl

/-- The vertex photon field contracted with the external `A(zⱼ)`. -/
def photonExt {C : Contraction nf nA κ} (hC : ExternalsAttached C) (j : Fin nA) :
    Wick.PhotonSlot κ :=
  (C.1.2 (.inl j)).getRight (isRight_photon_inl hC j)

theorem apply_inr_photonExt {C : Contraction nf nA κ} (hC : ExternalsAttached C) (j : Fin nA) :
    C.1.2 (.inr (photonExt hC j)) = .inl j := by
  rw [photonExt, Sum.inr_getRight, (C.2 _).1]

theorem apply_inr_photonLine {C : Contraction nf nA κ} (g : PhotonLine C) :
    C.1.2 (.inr g.1) = .inr g.head := by
  rw [PhotonLine.head, Sum.inr_getRight]

theorem apply_inr_head {C : Contraction nf nA κ} (g : PhotonLine C) :
    C.1.2 (.inr g.head) = .inr g.1 := by
  rw [← apply_inr_photonLine, (C.2 _).1]

theorem photonKey_lt_head {C : Contraction nf nA κ} (g : PhotonLine C) :
    Wick.photonKey g.1 < Wick.photonKey g.head := by
  obtain ⟨b, hb, hk⟩ := g.2
  rw [apply_inr_photonLine] at hb
  rwa [Sum.inr_injective hb]

/-- Each internal photon line uses two vertex photon fields, and each external `A` one more,
all distinct. -/
theorem two_mul_card_photonLine_add_le {C : Contraction nf nA κ} (hC : ExternalsAttached C) :
    2 * Nat.card (PhotonLine C) + nA ≤ Nat.card (Wick.PhotonSlot κ) := by
  let F : PhotonLine C ⊕ PhotonLine C ⊕ Fin nA → Wick.PhotonSlot κ
    | .inl g => g.1
    | .inr (.inl g) => g.head
    | .inr (.inr j) => photonExt hC j
  have hF : Function.Injective F := by
    rintro (g | g | j) (g' | g' | j') h <;> simp only [F] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have h1 := apply_inr_photonLine g
      rw [h, apply_inr_head] at h1
      have h2 := photonKey_lt_head g
      have h3 := photonKey_lt_head g'
      rw [Sum.inr_injective h1, ← h] at h3
      omega
    · have h1 := apply_inr_photonLine g
      rw [h, apply_inr_photonExt] at h1
      simp at h1
    · have h1 := apply_inr_photonLine g'
      rw [← h, apply_inr_head] at h1
      have h2 := photonKey_lt_head g
      have h3 := photonKey_lt_head g'
      rw [Sum.inr_injective h1, h] at h2
      omega
    · have h1 := apply_inr_head g
      rw [h, apply_inr_head] at h1
      exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext (Sum.inr_injective h1).symm)
    · have h1 := apply_inr_head g
      rw [h, apply_inr_photonExt] at h1
      simp at h1
    · have h1 := apply_inr_photonLine g'
      rw [← h, apply_inr_photonExt] at h1
      simp at h1
    · have h1 := apply_inr_head g'
      rw [← h, apply_inr_photonExt] at h1
      simp at h1
    · have h1 := apply_inr_photonExt hC j
      rw [h, apply_inr_photonExt] at h1
      exact congrArg (Sum.inr ∘ Sum.inr) (Sum.inl_injective h1).symm
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_sum, Nat.card_sum, Nat.card_fin] at this
  omega

theorem card_fermionVertex (κ : Fin N → Wick.VertexKind) :
    Nat.card (Wick.FermionVertex κ) =
      ∑ t, if κ t ≠ .photonCt then 1 else 0 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

theorem card_photonSlot (κ : Fin N → Wick.VertexKind) :
    Nat.card (Wick.PhotonSlot κ) = ∑ t, (κ t).photonSlots := by
  simp

/-- Twice the `Ψ̄Ψ` vertices plus the photon fields exceed twice the vertices by at most the
total order. -/
theorem two_mul_card_fermionVertex_add_card_photonSlot_le (κ : Fin N → Wick.VertexKind) :
    2 * Nat.card (Wick.FermionVertex κ) + Nat.card (Wick.PhotonSlot κ) ≤
      2 * N + ∑ t, (κ t).order := by
  have h : ∑ t, (2 * (if κ t ≠ .photonCt then 1 else 0) + (κ t).photonSlots) ≤
      ∑ t, (2 + (κ t).order) :=
    Finset.sum_le_sum fun t _ => by
      cases κ t <;> simp [Wick.VertexKind.photonSlots, Wick.VertexKind.order]
  rw [card_fermionVertex, card_photonSlot, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine h.trans_eq ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_comm]

/-- With attached externals (X₁₆), field counting bounds the internal lines:
`2 E + 2 nf + nA ≤ 2 V + ∑ order`. -/
theorem two_mul_card_line_le {C : Contraction nf nA κ} (hC : ExternalsAttached C) :
    2 * Nat.card (Line C) + 2 * nf + nA ≤ 2 * N + ∑ t, (κ t).order := by
  have h1 := card_fermionLine_add_le hC
  have h2 := two_mul_card_photonLine_add_le hC
  have h3 := two_mul_card_fermionVertex_add_card_photonSlot_le κ
  rw [Nat.card_sum]
  omega

/-! ### The loop bound -/

theorem loopCount_add_card_nonChord (C : Contraction nf nA κ) :
    loopCount C + Nat.card {g : Line C // ¬ IsChord g} = Nat.card (Line C) := by
  classical
  rw [loopCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card,
    ← Finset.card_univ]
  convert Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun f : Line C => IsChord f)

/-- A contraction with attached externals (X₁₆) and connected vertices (X₁₇) of total order at
most `K ≤ 2 nf + nA + 1` has at most one loop. -/
theorem loopCount_le_one_of_connected {K : ℕ} (hκ : ∑ t, (κ t).order ≤ K)
    (hK : K ≤ 2 * nf + nA + 1) {C : Contraction nf nA κ} (hA : ExternalsAttached C)
    (hV : VerticesConnected C) : loopCount C ≤ 1 := by
  have h1 := two_mul_card_line_le hA
  have h2 := card_le_card_nonChord_add_one hV
  have h3 := loopCount_add_card_nonChord C
  omega

/-- **At most one loop below the two-loop order.** Every 1PI contraction (X₁₈) of total order at
most `K ≤ 2 nf + nA + 1` has at most one loop (T₂). -/
theorem loopCount_le_one_of_order {K : ℕ} (hκ : ∑ t, (κ t).order ≤ K)
    (hK : K ≤ 2 * nf + nA + 1) (C : Contraction nf nA κ) (hC : IsOnePI C) : loopCount C ≤ 1 :=
  loopCount_le_one_of_connected hκ hK hC.1 hC.2.1

/-- The form used for a `Finset.sum_congr` over the filters of `onePIFunction₂` and
`onePIFunction`: the ambient finsets and the decidability instances are arbitrary, so the lemma
applies to the frozen sums whatever instances they were elaborated with. -/
theorem loopCount_le_one_of_mem_filter {K : ℕ} (hK : K ≤ 2 * nf + nA + 1)
    {s : Finset (Fin N → Wick.VertexKind)}
    {dκ : DecidablePred fun κ : Fin N → Wick.VertexKind => ∑ t, (κ t).order ≤ K}
    (hκ : κ ∈ @Finset.filter _ (fun κ => ∑ t, (κ t).order ≤ K) dκ s)
    {u : Finset (Contraction nf nA κ)} {dC : DecidablePred (IsOnePI (nf := nf) (nA := nA) (κ := κ))}
    {C : Contraction nf nA κ} (hC : C ∈ @Finset.filter _ IsOnePI dC u) :
    loopCount C ≤ 1 :=
  loopCount_le_one_of_order (Finset.mem_filter.mp hκ).2 hK C (Finset.mem_filter.mp hC).2

end QED.TwoLoop.LoopBound

end
