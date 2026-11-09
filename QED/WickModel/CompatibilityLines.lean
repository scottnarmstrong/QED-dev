/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.Wick.WickVertex

/-!
# Packet 5's contractions in the general Wick model

Packet 5 (decision D-20) indexes the external fields of `⟨Ψ(x) Ψ̄(y) A(z)⟩` by `none` in
`Option (FermionVertex κ)` and `Option (PhotonSlot κ)`. The general model of packet 6a (decision
D-24) indexes them by `inl 0` in `Fin 1 ⊕ FermionVertex κ` and `Fin 1 ⊕ PhotonSlot κ`. This file
transports packet 5's contractions along `Option α ≃ Fin 1 ⊕ α` and shows that the transport
preserves the combinatorial structure.

## Main definitions

* `optionEquivFinOneSum α`: the equivalence `Option α ≃ Fin 1 ⊕ α` with `none ↦ inl 0`.
* `contractionEquiv κ`: packet 5's contractions of `κ` are the contractions of `κ` with one
  external fermion pair and one external photon.
* `lineEquiv C`: the internal lines of `C` and of `contractionEquiv κ C` correspond, with the
  same ends.

## Main statements

* `fermionSign_contractionEquiv`: the transport preserves the fermionic sign.
* `isOnePI_contractionEquiv_iff`: packet 5's one-particle irreducibility agrees with the general
  model's `ExternalsAttached ∧ VerticesConnected ∧ ∀ f, ¬ IsBridge f`.
* `isLoopLine_lineEquiv`: for a 1PI contraction the loop lines correspond.
-/

@[expose] public section

namespace QED.WickModel

/-- The equivalence `Option α ≃ Fin 1 ⊕ α` sending `none` to `inl 0` and `some a` to `inr a`. -/
def optionEquivFinOneSum (α : Type*) : Option α ≃ Fin 1 ⊕ α where
  toFun x := x.elim (.inl 0) .inr
  invFun y := y.elim (fun _ => none) some
  left_inv x := by cases x <;> rfl
  right_inv y := by
    rcases y with i | a
    · rw [Subsingleton.elim i 0]
      rfl
    · rfl

section OptionEquiv

variable {α : Type*}

/-- `optionEquivFinOneSum` sends `none` to `inl 0`. -/
@[simp]
theorem optionEquivFinOneSum_none : optionEquivFinOneSum α none = .inl 0 := rfl

/-- `optionEquivFinOneSum` sends `some a` to `inr a`. -/
@[simp]
theorem optionEquivFinOneSum_some (a : α) : optionEquivFinOneSum α (some a) = .inr a := rfl

/-- The inverse of `optionEquivFinOneSum` sends the left summand to `none`. -/
@[simp]
theorem optionEquivFinOneSum_symm_inl (i : Fin 1) :
    (optionEquivFinOneSum α).symm (.inl i) = none := rfl

/-- The inverse of `optionEquivFinOneSum` sends `inr a` to `some a`. -/
@[simp]
theorem optionEquivFinOneSum_symm_inr (a : α) :
    (optionEquivFinOneSum α).symm (.inr a) = some a := rfl

/-- `optionEquivFinOneSum` hits `inr a` exactly at `some a`. -/
@[simp]
theorem optionEquivFinOneSum_eq_inr_iff {x : Option α} {a : α} :
    optionEquivFinOneSum α x = .inr a ↔ x = some a := by
  cases x <;> simp

/-- `optionEquivFinOneSum` hits the left summand exactly at `none`. -/
@[simp]
theorem optionEquivFinOneSum_eq_inl_iff {x : Option α} {i : Fin 1} :
    optionEquivFinOneSum α x = .inl i ↔ x = none := by
  cases x <;> simp [Subsingleton.elim i 0]

/-- `optionEquivFinOneSum x` is in the right summand exactly when `x` is `some`. -/
@[simp]
theorem isRight_optionEquivFinOneSum (x : Option α) :
    (optionEquivFinOneSum α x).isRight = x.isSome := by
  cases x <;> rfl

end OptionEquiv

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **Packet 5's contractions in the general model.** A contraction of `⟨Ψ(x) Ψ̄(y) A(z)⟩` with
vertices `κ` in packet 5's indexing (external fields `none`) is a contraction of the general model
with one external fermion pair and one external photon (external fields `inl 0`). -/
def contractionEquiv (κ : Fin N → Wick.VertexKind) : Wick.Contraction κ ≃ Contraction 1 1 κ :=
  Equiv.subtypeEquiv ((optionEquivFinOneSum _).permCongr.prodCongr
      (optionEquivFinOneSum _).permCongr) fun c => by
    simp only [Equiv.prodCongr_apply, Prod.map, Equiv.permCongr_apply]
    refine (optionEquivFinOneSum _).forall_congr fun a => ?_
    simp

section Contraction

variable (C : Wick.Contraction κ)

/-- The external `Ψ(x)` is paired as in packet 5. -/
@[simp]
theorem contractionEquiv_fst_inl (i : Fin 1) :
    (contractionEquiv κ C).1.1 (.inl i) = optionEquivFinOneSum _ (C.1.1 none) := rfl

/-- The `Ψ` field of a vertex is paired as in packet 5. -/
@[simp]
theorem contractionEquiv_fst_inr (t : Wick.FermionVertex κ) :
    (contractionEquiv κ C).1.1 (.inr t) = optionEquivFinOneSum _ (C.1.1 (some t)) := rfl

/-- The external `A(z)` is paired as in packet 5. -/
@[simp]
theorem contractionEquiv_snd_inl (i : Fin 1) :
    (contractionEquiv κ C).1.2 (.inl i) = optionEquivFinOneSum _ (C.1.2 none) := rfl

/-- A vertex photon field is paired as in packet 5. -/
@[simp]
theorem contractionEquiv_snd_inr (a : Wick.PhotonSlot κ) :
    (contractionEquiv κ C).1.2 (.inr a) = optionEquivFinOneSum _ (C.1.2 (some a)) := rfl

/-- The fermion pairing of the transported contraction is the conjugate of packet 5's. -/
theorem contractionEquiv_fst :
    (contractionEquiv κ C).1.1 = (optionEquivFinOneSum _).permCongr C.1.1 := rfl

/-- The transport preserves the fermionic sign. -/
theorem fermionSign_contractionEquiv :
    fermionSign (contractionEquiv κ C) = Wick.fermionSign C := by
  rw [fermionSign, Wick.fermionSign, contractionEquiv_fst, Equiv.Perm.sign_permCongr]

/-- The internal fermion lines of `C` are those of the transported contraction. -/
def fermionLineEquiv : Wick.FermionLine C ≃ FermionLine (contractionEquiv κ C) :=
  Equiv.subtypeEquivRight fun t => by
    simp [Option.ne_none_iff_isSome]

/-- The internal photon lines of `C` are those of the transported contraction. -/
def photonLineEquiv : Wick.PhotonLine C ≃ PhotonLine (contractionEquiv κ C) :=
  Equiv.subtypeEquivRight fun a => by
    simp

/-- The internal lines of `C` are those of the transported contraction. -/
def lineEquiv : Wick.Line C ≃ Line (contractionEquiv κ C) :=
  (fermionLineEquiv C).sumCongr (photonLineEquiv C)

variable {C}

/-- A transported fermion line has the same indexing `Ψ` field. -/
@[simp]
theorem fermionLineEquiv_val (f : Wick.FermionLine C) : (fermionLineEquiv C f).1 = f.1 := rfl

/-- A transported photon line has the same indexing photon field. -/
@[simp]
theorem photonLineEquiv_val (g : Wick.PhotonLine C) : (photonLineEquiv C g).1 = g.1 := rfl

/-- `lineEquiv` on fermion lines. -/
@[simp]
theorem lineEquiv_inl (f : Wick.FermionLine C) :
    lineEquiv C (.inl f) = .inl (fermionLineEquiv C f) := rfl

/-- `lineEquiv` on photon lines. -/
@[simp]
theorem lineEquiv_inr (g : Wick.PhotonLine C) :
    lineEquiv C (.inr g) = .inr (photonLineEquiv C g) := rfl

/-- The tail of a transported fermion line is the `Ψ̄` contracted with its `Ψ` in `C`. -/
theorem some_tail_fermionLineEquiv (f : Wick.FermionLine C) :
    some (fermionLineEquiv C f).tail = C.1.1 (some f.1) := by
  apply (optionEquivFinOneSum _).injective
  rw [optionEquivFinOneSum_some, FermionLine.tail, Sum.inr_getRight]
  rfl

/-- The tail of a transported fermion line, as packet 5 writes it. -/
theorem tail_fermionLineEquiv (f : Wick.FermionLine C) :
    (fermionLineEquiv C f).tail = (C.1.1 (some f.1)).get (Option.ne_none_iff_isSome.mp f.2) :=
  (Option.get_of_eq_some _ (some_tail_fermionLineEquiv f).symm).symm

/-- The head of a transported photon line is the photon field contracted with it in `C`. -/
theorem some_head_photonLineEquiv (g : Wick.PhotonLine C) :
    some (photonLineEquiv C g).head = C.1.2 (some g.1) := by
  apply (optionEquivFinOneSum _).injective
  rw [optionEquivFinOneSum_some, PhotonLine.head, Sum.inr_getRight]
  rfl

/-- The head of a transported photon line, as packet 5 writes it. -/
theorem head_photonLineEquiv (g : Wick.PhotonLine C) :
    (photonLineEquiv C g).head = (C.1.2 (some g.1)).get
      (Option.isSome_iff_exists.mpr (g.2.imp fun _ h => h.1)) :=
  (Option.get_of_eq_some _ (some_head_photonLineEquiv g).symm).symm

/-- The transport preserves the ends of the internal lines. -/
@[simp]
theorem ends_lineEquiv (f : Wick.Line C) : (lineEquiv C f).ends = f.ends := by
  rcases f with f | g
  · simp only [lineEquiv_inl, Line.ends, Wick.Line.ends, tail_fermionLineEquiv,
      fermionLineEquiv_val]
  · simp only [lineEquiv_inr, Line.ends, Wick.Line.ends, head_photonLineEquiv,
      photonLineEquiv_val]

/-- The transport preserves the labels of the internal lines. -/
theorem label_lineEquiv_le_iff (f g : Wick.Line C) :
    (lineEquiv C f).label ≤ (lineEquiv C g).label ↔
      (match f with | .inl f => f.1.1.val | .inr f => N + Wick.photonKey f.1) ≤
        (match g with | .inl g => g.1.1.val | .inr g => N + Wick.photonKey g.1) := by
  rcases f with f | f <;> rcases g with g | g <;> rfl

/-- Joining by internal lines outside corresponding sets of lines is the same relation. -/
theorem joined_contractionEquiv {S : Set (Wick.Line C)} {S' : Set (Line (contractionEquiv κ C))}
    (hS : ∀ g, lineEquiv C g ∈ S' ↔ g ∈ S) :
    Joined (contractionEquiv κ C) S' = Wick.Joined C S := by
  funext u w
  apply propext
  constructor
  · rintro ⟨f, hf, h⟩
    obtain ⟨g, rfl⟩ := (lineEquiv C).surjective f
    exact ⟨g, fun hg => hf ((hS g).mpr hg), by rwa [ends_lineEquiv] at h⟩
  · rintro ⟨g, hg, h⟩
    exact ⟨lineEquiv C g, fun hg' => hg ((hS g).mp hg'), by rwa [ends_lineEquiv]⟩

/-- `Wick.Joined` is symmetric. -/
theorem wickJoined_symm {S : Set (Wick.Line C)} {u w : Fin N} (h : Wick.Joined C S u w) :
    Wick.Joined C S w u := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨f, hf, h.symm⟩

/-- If the ends of the internal line `f` stay connected without `f`, then any two connected
vertices stay connected without `f`: a path through `f` can be rerouted. -/
theorem reflTransGen_wickJoined_singleton {f : Wick.Line C}
    (hf : Relation.ReflTransGen (Wick.Joined C {f}) f.ends.1 f.ends.2) {u w : Fin N}
    (h : Relation.ReflTransGen (Wick.Joined C ∅) u w) :
    Relation.ReflTransGen (Wick.Joined C {f}) u w := by
  have hsymm : ∀ {x y}, Relation.ReflTransGen (Wick.Joined C {f}) x y →
      Relation.ReflTransGen (Wick.Joined C {f}) y x := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact (Relation.ReflTransGen.single (wickJoined_symm hab)).trans ih
  induction h with
  | refl => exact .refl
  | tail _ hxy ih =>
    obtain ⟨g, -, hg⟩ := hxy
    by_cases hgf : g = f
    · subst hgf
      rcases hg with hg | hg <;> simp only [hg] at hf
      · exact ih.trans hf
      · exact ih.trans (hsymm hf)
    · exact ih.tail ⟨g, hgf, hg⟩

/-- The set `{f}` as packet 5's set of lines deleted by `some f`. -/
theorem singleton_eq_setOf_some_eq (f : Wick.Line C) :
    ({f} : Set (Wick.Line C)) = {g | some f = some g} :=
  Set.ext fun g => by
    rw [Set.mem_singleton_iff]
    exact ⟨fun h => by rw [h]; rfl, fun h => (Option.some_injective _ h).symm⟩

/-- **One-particle irreducibility is preserved.** Packet 5's `IsOnePI` (the external `Ψ(x)` is
attached, and the vertices stay connected after deleting at most one internal line) agrees with
the general model's `IsOnePI` (the externals are attached, the vertices are connected, and no
internal line is a bridge). -/
theorem isOnePI_contractionEquiv_iff : IsOnePI (contractionEquiv κ C) ↔ Wick.IsOnePI C := by
  constructor
  · rintro ⟨⟨hext, -⟩, hconn, hbr⟩
    refine ⟨fun h => hext 0 0 (by simp [h]), fun g u w => ?_⟩
    have hconn' : Relation.ReflTransGen (Wick.Joined C ∅) u w := by
      rw [← joined_contractionEquiv (S' := ∅) fun g => by simp]
      exact hconn u w
    rcases g with _ | f
    · simpa using hconn'
    · have hf := not_not.mp (hbr (lineEquiv C f))
      rw [joined_contractionEquiv (S := {f}) fun g => by simp, ends_lineEquiv] at hf
      rw [← singleton_eq_setOf_some_eq]
      exact reflTransGen_wickJoined_singleton hf hconn'
  · rintro ⟨hext, hconn⟩
    refine ⟨⟨fun _ _ => by simpa using hext, fun _ _ => by simpa using (C.2 none).2⟩,
      fun u w => ?_, fun f hf => hf ?_⟩
    · rw [joined_contractionEquiv (S := ∅) fun g => by simp]
      simpa using hconn none u w
    · obtain ⟨g, rfl⟩ := (lineEquiv C).surjective f
      rw [joined_contractionEquiv (S := {g}) fun g => by simp, ends_lineEquiv,
        singleton_eq_setOf_some_eq]
      exact hconn (some g) g.ends.1 g.ends.2

/-- In a 1PI contraction no internal line of the transported contraction is a bridge. -/
theorem not_isBridge_of_isOnePI (hC : Wick.IsOnePI C) (f : Line (contractionEquiv κ C)) :
    ¬ IsBridge f :=
  (isOnePI_contractionEquiv_iff.mpr hC).2.2 f

/-- **The loop lines correspond** for a 1PI contraction: every internal line is a non-bridge, so
the general model's loop line is the lowest-labelled line, as in packet 5. -/
theorem isLoopLine_lineEquiv (hC : Wick.IsOnePI C) (f : Wick.Line C) :
    IsLoopLine (lineEquiv C f) ↔ Wick.IsLoopLine f := by
  unfold IsLoopLine Wick.IsLoopLine
  simp only [not_isBridge_of_isOnePI hC, not_false_eq_true, forall_const, true_and]
  exact ((lineEquiv C).forall_congr fun g => (label_lineEquiv_le_iff f g).symm).symm

/-- A 1PI contraction with an internal line has a loop line. -/
theorem exists_isLoopLine_iff (hC : Wick.IsOnePI C) :
    (∃ f : Line (contractionEquiv κ C), IsLoopLine f) ↔ ¬ IsEmpty (Wick.Line C) := by
  constructor
  · rintro ⟨f, -⟩ hE
    exact hE.elim ((lineEquiv C).symm f)
  · intro hE
    rw [not_isEmpty_iff] at hE
    obtain ⟨f, -, hf⟩ := Finset.exists_min_image Finset.univ
      (fun f : Line (contractionEquiv κ C) => f.label)
      (Finset.univ_nonempty_iff.mpr ((lineEquiv C).nonempty_congr.mp hE))
    exact ⟨f, not_isBridge_of_isOnePI hC f, fun g _ => hf g (Finset.mem_univ g)⟩

end Contraction

end QED.WickModel

end
