/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassificationBasic
public import QED.Wick.Gauge3

/-!
# Three gauge vertices: names and shapes

The contractions of the vertex sequence `gauge3` of three gauge vertices with one external fermion
pair and one external photon, `Contraction 1 1 Wick.gauge3` (packet 6a, decision D-24). With the
externals attached, the external photon is contracted with the photon field of one vertex `u`
(`PhotonAt C u`), and the photon fields of the other two vertices are contracted with each other.
The connected contractions that are not 1PI have one of four shapes:

* `IsSEin C a b c`: the fermion line runs `Ψ̄(y) → c → b → a → Ψ(x)`, the external photon is at
  `a`, and the photon line joins `b` and `c`: a self-energy loop on the incoming leg.
* `IsSEout C a b c`: the same fermion line, with the external photon at `c` and the photon line
  joining `a` and `b`: a self-energy loop on the outgoing leg.
* `IsVP C a v w`: the fermion line runs `Ψ̄(y) → a → Ψ(x)`, the vertices `v`, `w` form a closed
  fermion loop, the external photon is at `v`, and the photon line joins `w` and `a`: a vacuum
  polarization loop on the photon leg.
* `IsTP C a b c u`: the fermion line runs `Ψ̄(y) → b → a → Ψ(x)`, the `Ψ` of `c` is contracted with
  its own `Ψ̄` (a one-vertex closed loop), and the external photon is at `u ∈ {a, b}`: a tadpole.

This file names the fields and the lines of each shape.
-/

@[expose] public section

open Complex

namespace QED.WickModel

open Wick (gauge3)

/-! ### Fields -/

/-- `Wick.fv` is injective. -/
theorem fv3_injective : Function.Injective Wick.fv := fun _ _ h => congrArg Subtype.val h

/-- `Wick.ps` is injective. -/
theorem ps3_injective : Function.Injective Wick.ps := fun _ _ h => congrArg Sigma.fst h

/-- `Wick.fv` is injective. -/
@[simp]
theorem fv3_inj {s t : Fin 3} : Wick.fv s = Wick.fv t ↔ s = t := fv3_injective.eq_iff

/-- `Wick.ps` is injective. -/
@[simp]
theorem ps3_inj {s t : Fin 3} : Wick.ps s = Wick.ps t ↔ s = t := ps3_injective.eq_iff

/-- The vertex of `Wick.fv t` is `t`. -/
@[simp]
theorem fv3_val (t : Fin 3) : (Wick.fv t).1 = t := rfl

/-- The vertex of `Wick.ps t` is `t`. -/
@[simp]
theorem ps3_fst (t : Fin 3) : (Wick.ps t).1 = t := rfl

/-- Every fermion vertex of `gauge3` is `Wick.fv t`. -/
theorem fv3_eq (x : Wick.FermionVertex gauge3) : x = Wick.fv x.1 := rfl

/-- Every photon field of `gauge3` is `Wick.ps t`. -/
theorem ps3_eq (x : Wick.PhotonSlot gauge3) : x = Wick.ps x.1 := by
  obtain ⟨t, k, hk⟩ := x
  change k < 1 at hk
  obtain rfl : k = 0 := by omega
  rfl

/-- The key of the photon field of vertex `t`. -/
@[simp]
theorem photonKey_ps3 (t : Fin 3) : Wick.photonKey (Wick.ps t) = 2 * t.val := rfl

/-- `gauge3` has three fermion vertices. -/
theorem card_fermionVertex_gauge3 : Fintype.card (Wick.FermionVertex gauge3) = 3 := by
  decide

/-- The vertex factor of `gauge3`. -/
theorem vertexFactor_gauge3 (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : Wick.FermionVertex gauge3 → Fin 4)
    (lor : Wick.PhotonSlot gauge3 → Fin 4) (kψ : Wick.FermionVertex gauge3 → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot gauge3 → Fin 4 → ℝ) (t : Fin 3) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor (Wick.ps t)) (α (Wick.fv t)) (β (Wick.fv t)) := rfl

/-- The fermion fields of the contraction, for distinct `a, b, c`. -/
theorem fermion_field_cases {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (y : Fin 1 ⊕ Wick.FermionVertex gauge3) :
    y = .inl 0 ∨ y = .inr (Wick.fv a) ∨ y = .inr (Wick.fv b) ∨ y = .inr (Wick.fv c) := by
  rcases y with i | t
  · exact Or.inl (by rw [Subsingleton.elim i 0])
  · rcases fin_three_eq_or hab hbc hac t.1 with h | h | h <;> rw [fv3_eq t, h] <;> simp

/-- The fermion vertices of `gauge3`, for distinct `a, b, c`. -/
theorem fv3_cases {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (x : Wick.FermionVertex gauge3) : x = Wick.fv a ∨ x = Wick.fv b ∨ x = Wick.fv c := by
  rcases fin_three_eq_or hab hbc hac x.1 with h | h | h <;> rw [fv3_eq x, h] <;> simp

/-- The photon fields of `gauge3`, for distinct `a, b, c`. -/
theorem ps3_cases {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (x : Wick.PhotonSlot gauge3) : x = Wick.ps a ∨ x = Wick.ps b ∨ x = Wick.ps c := by
  rcases fin_three_eq_or hab hbc hac x.1 with h | h | h <;> rw [ps3_eq x, h] <;> simp

/-- A permutation of a four-element type is determined at the fourth point by its values at the
other three. -/
theorem perm_apply_eq_of_three {X : Type*} {σ : Equiv.Perm X} {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : X}
    (hX : ∀ y, y = y₁ ∨ y = y₂ ∨ y = y₃ ∨ y = y₄) (h₁ : σ x₁ = y₁) (h₂ : σ x₂ = y₂)
    (h₃ : σ x₃ = y₃) (h₁₄ : x₄ ≠ x₁) (h₂₄ : x₄ ≠ x₂) (h₃₄ : x₄ ≠ x₃) : σ x₄ = y₄ := by
  rcases hX (σ x₄) with h | h | h | h
  · exact absurd (σ.injective (h.trans h₁.symm)) h₁₄
  · exact absurd (σ.injective (h.trans h₂.symm)) h₂₄
  · exact absurd (σ.injective (h.trans h₃.symm)) h₃₄
  · exact h

/-- A permutation of a four-element type takes one of two values at a third point, given its
values at two others. -/
theorem perm_apply_cases_of_two {X : Type*} {σ : Equiv.Perm X} {x₁ x₂ x₃ y₁ y₂ y₃ y₄ : X}
    (hX : ∀ y, y = y₁ ∨ y = y₂ ∨ y = y₃ ∨ y = y₄) (h₁ : σ x₁ = y₁) (h₂ : σ x₂ = y₂)
    (h₁₃ : x₃ ≠ x₁) (h₂₃ : x₃ ≠ x₂) : σ x₃ = y₃ ∨ σ x₃ = y₄ := by
  rcases hX (σ x₃) with h | h | h | h
  · exact absurd (σ.injective (h.trans h₁.symm)) h₁₃
  · exact absurd (σ.injective (h.trans h₂.symm)) h₂₃
  · exact Or.inl h
  · exact Or.inr h

variable {C : Contraction 1 1 gauge3}

/-! ### The photon pairing -/

/-- The external photon is contracted with the photon field of `u`. -/
def PhotonAt (C : Contraction 1 1 gauge3) (u : Fin 3) : Prop :=
  C.1.2 (.inl 0) = .inr (Wick.ps u)

/-- With the externals attached, the external photon is contracted with a vertex field. -/
theorem exists_photonAt (C : Contraction 1 1 gauge3) : ∃ u, PhotonAt C u := by
  rcases h : C.1.2 (.inl 0) with i | s
  · rw [Subsingleton.elim i 0] at h
    exact absurd h (C.2 _).2
  · exact ⟨s.1, by unfold PhotonAt; rw [h, ← ps3_eq]⟩

/-- The photon field of `u` is contracted with the external photon. -/
theorem PhotonAt.snd_self {u : Fin 3} (hu : PhotonAt C u) : C.1.2 (.inr (Wick.ps u)) = .inl 0 := by
  rw [← hu, (C.2 _).1]

/-- **The photon line.** With the external photon at `u`, the photon fields of the other two
vertices `v`, `w` are contracted with each other. -/
theorem PhotonAt.snd_pair {u v w : Fin 3} (hu : PhotonAt C u) (huv : u ≠ v) (hvw : v ≠ w)
    (huw : u ≠ w) : C.1.2 (.inr (Wick.ps v)) = .inr (Wick.ps w) := by
  rcases h : C.1.2 (.inr (Wick.ps v)) with i | s
  · rw [Subsingleton.elim i 0, ← hu.snd_self] at h
    exact absurd (ps3_injective (Sum.inr_injective (C.1.2.injective h))) huv.symm
  · rcases ps3_cases huv hvw huw s with rfl | rfl | rfl
    · rw [← hu] at h
      exact absurd (C.1.2.injective h) Sum.inr_ne_inl
    · exact absurd h (C.2 _).2
    · rfl

/-- No photon field other than that of `u` is contracted with an external photon, and vertex
fields of `u` are not contracted with vertex fields. -/
theorem PhotonAt.fst_ne {u : Fin 3} (hu : PhotonAt C u) {s s' : Wick.PhotonSlot gauge3}
    (h : C.1.2 (.inr s) = .inr s') : s.1 ≠ u ∧ s'.1 ≠ u := by
  constructor
  · intro hs
    rw [ps3_eq s, hs, hu.snd_self] at h
    exact Sum.inl_ne_inr h
  · intro hs
    rw [ps3_eq s', hs, ← hu] at h
    exact Sum.inr_ne_inl (C.1.2.injective h)

/-- The photon line of the vertices `v` and `w`, the external photon being at `u`. -/
def PhotonAt.line {u v w : Fin 3} (hu : PhotonAt C u) (huv : u ≠ v) (hvw : v ≠ w)
    (huw : u ≠ w) : PhotonLine C :=
  photonLineOfPair (hu.snd_pair huv hvw huw) (ps3_injective.ne hvw)

/-- The photon line is indexed by one of its two fields, with the other as head. -/
theorem PhotonAt.line_spec {u v w : Fin 3} (hu : PhotonAt C u) (huv : u ≠ v) (hvw : v ≠ w)
    (huw : u ≠ w) :
    ((hu.line huv hvw huw).1 = Wick.ps v ∧ (hu.line huv hvw huw).head = Wick.ps w) ∨
      ((hu.line huv hvw huw).1 = Wick.ps w ∧ (hu.line huv hvw huw).head = Wick.ps v) :=
  photonLineOfPair_spec _ _

/-- The photon line joins `v` and `w`. -/
theorem PhotonAt.ends_line {u v w : Fin 3} (hu : PhotonAt C u) (huv : u ≠ v) (hvw : v ≠ w)
    (huw : u ≠ w) :
    Line.ends (.inr (hu.line huv hvw huw) : Line C) = (v, w) ∨
      Line.ends (.inr (hu.line huv hvw huw) : Line C) = (w, v) :=
  ends_photonLineOfPair _ _

/-- The photon line is the only internal photon line. -/
theorem PhotonAt.eq_line {u v w : Fin 3} (hu : PhotonAt C u) (huv : u ≠ v) (hvw : v ≠ w)
    (huw : u ≠ w) (l : PhotonLine C) : l = hu.line huv hvw huw := by
  refine PhotonLine.eq_of_mem (z := Wick.ps v) ?_ ?_
  · have hl := l.apply_eq_inr_head
    rcases ps3_cases huv hvw huw l.1 with h1 | h1 | h1
    · exact absurd (congrArg Sigma.fst h1) (hu.fst_ne hl).1
    · exact Or.inl h1
    · right
      rw [h1, hu.snd_pair huw hvw.symm huv] at hl
      exact (Sum.inr_injective hl).symm
  · rcases hu.line_spec huv hvw huw with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2

/-- The label of the photon line is at least `3`. -/
theorem label_inr_ge (l : PhotonLine C) : 3 ≤ Line.label (.inr l : Line C) := by
  change 3 ≤ 3 + Wick.photonKey l.1
  omega

/-! ### Fermion lines -/

/-- The internal fermion line indexed by the `Ψ` of `t`, contracted with the `Ψ̄` of `s`. -/
def fline {t s : Fin 3} (h : C.1.1 (.inr (Wick.fv t)) = .inr (Wick.fv s)) : FermionLine C :=
  ⟨Wick.fv t, by simp [h]⟩

/-- The fermion line is indexed by the `Ψ` of `t`. -/
@[simp]
theorem fline_val {t s : Fin 3} (h : C.1.1 (.inr (Wick.fv t)) = .inr (Wick.fv s)) :
    (fline h).1 = Wick.fv t := rfl

/-- The fermion line starts at `s`. -/
@[simp]
theorem tail_fline {t s : Fin 3} (h : C.1.1 (.inr (Wick.fv t)) = .inr (Wick.fv s)) :
    (fline h).tail = Wick.fv s := FermionLine.tail_eq h

/-- The fermion line runs from `s` to `t`. -/
theorem ends_fline {t s : Fin 3} (h : C.1.1 (.inr (Wick.fv t)) = .inr (Wick.fv s)) :
    Line.ends (.inl (fline h) : Line C) = (s, t) := by
  change ((fline h).tail.1, (fline h).1.1) = (s, t)
  rw [tail_fline]
  rfl

/-- The label of the fermion line is `t`. -/
theorem label_fline {t s : Fin 3} (h : C.1.1 (.inr (Wick.fv t)) = .inr (Wick.fv s)) :
    Line.label (.inl (fline h) : Line C) = t.val := rfl

/-- A fermion line whose `Ψ` is at `t` is the fermion line of `t`. -/
theorem eq_fline {t s : Fin 3} (h : C.1.1 (.inr (Wick.fv t)) = .inr (Wick.fv s))
    (f : FermionLine C) (hf : f.1 = Wick.fv t) : f = fline h :=
  Subtype.ext hf

/-- A vertex whose `Ψ` is contracted with the external `Ψ̄(y)` has no fermion line. -/
theorem val_ne_of_eq_inl {t : Fin 3} (h : C.1.1 (.inr (Wick.fv t)) = .inl 0) (f : FermionLine C) :
    f.1 ≠ Wick.fv t := by
  intro hf
  have := f.2
  rw [hf, h] at this
  exact Bool.false_ne_true this

end QED.WickModel

end
