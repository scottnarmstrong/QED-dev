/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CCountGlue

/-!
# (X₁) piece C: glued contractions as a bijection, and recovering the pieces of `glueIn`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (counting).

* `countIdxSet`: the data `(N₁ + N₂ = N, shuffle e, C₁, C₂)` of a glued contraction, as a finset
  of a sigma type.
* `count_sum_of_bij`: the hypothesis `hcount` of `countSum_glue` from a bijection: the glue map
  sends the data into the selected contractions (`hmem`), injectively (`hinj`), and onto
  (`hsurj`).
* `countGlueIn_pieces_eq`: for a fixed split `e`, `glueIn e C₁ C₂` determines `C₁` and `C₂`
  (read off from the pairings, no graph theory).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Contraction)
open QED.Graded

/-- The data of a glued contraction on `κ`: a split `N₁ + N₂`, a bijection `e` and the pieces. -/
abbrev CountIdx (nf nA nf₂ nA₂ : ℕ) {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  Σ p : ℕ × ℕ, Σ e : Fin p.1 ⊕ Fin p.2 ≃ Fin N,
    Contraction nf nA (leftKinds κ e) × Contraction nf₂ nA₂ (rightKinds κ e)

variable {nf nA nf₂ nA₂ N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The data of glued contractions with selected pieces over the shuffles. -/
noncomputable def countIdxSet (Sel₁ : CountSel nf nA) (Sel₂ : CountSel nf₂ nA₂)
    (g : Grading κ) : Finset (CountIdx nf nA nf₂ nA₂ κ) :=
  (antidiagonal N).sigma fun p => (countShuffles p.1 p.2 N).sigma fun e =>
    countSel Sel₁ (gradL κ e g) ×ˢ countSel Sel₂ (gradR κ e g)

theorem mem_countIdxSet {Sel₁ : CountSel nf nA} {Sel₂ : CountSel nf₂ nA₂} {g : Grading κ}
    {x : CountIdx nf nA nf₂ nA₂ κ} :
    x ∈ countIdxSet Sel₁ Sel₂ g ↔ x.1.1 + x.1.2 = N ∧ IsShuffle x.2.1 ∧
      Sel₁ x.2.2.1 (gradL κ x.2.1 g) ∧ Sel₂ x.2.2.2 (gradR κ x.2.1 g) := by
  simp only [countIdxSet, mem_sigma, mem_antidiagonal, mem_countShuffles, mem_product,
    mem_countSel]

/-- **The counting hypothesis from a bijection.** -/
theorem count_sum_of_bij (Sel Sel₁ : CountSel nf nA) (Sel₂ : CountSel nf₂ nA₂)
    (glue : ∀ {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N),
      Contraction nf nA (leftKinds κ e) → Contraction nf₂ nA₂ (rightKinds κ e) →
        Contraction nf nA κ) (g : Grading κ)
    (hmem : ∀ x ∈ countIdxSet Sel₁ Sel₂ g, Sel (glue x.2.1 x.2.2.1 x.2.2.2) g)
    (hinj : Set.InjOn (fun x : CountIdx nf nA nf₂ nA₂ κ => glue x.2.1 x.2.2.1 x.2.2.2)
      (countIdxSet Sel₁ Sel₂ g))
    (hsurj : ∀ C : Contraction nf nA κ, Sel C g →
      ∃ x ∈ countIdxSet Sel₁ Sel₂ g, glue x.2.1 x.2.2.1 x.2.2.2 = C)
    (f : Contraction nf nA κ → ℂ) :
    ∑ C ∈ countSel Sel g, f C =
      ∑ p ∈ antidiagonal N, ∑ e ∈ countShuffles p.1 p.2 N,
        ∑ C₁ ∈ countSel Sel₁ (gradL κ e g), ∑ C₂ ∈ countSel Sel₂ (gradR κ e g),
          f (glue e C₁ C₂) := by
  have hR : ∑ p ∈ antidiagonal N, ∑ e ∈ countShuffles p.1 p.2 N,
      ∑ C₁ ∈ countSel Sel₁ (gradL κ e g), ∑ C₂ ∈ countSel Sel₂ (gradR κ e g),
        f (glue e C₁ C₂) =
      ∑ x ∈ countIdxSet Sel₁ Sel₂ g, f (glue x.2.1 x.2.2.1 x.2.2.2) := by
    simp only [countIdxSet, sum_sigma, sum_product]
  rw [hR]
  symm
  refine sum_nbij (fun x => glue x.2.1 x.2.2.1 x.2.2.2) (fun x hx => ?_) hinj
    (fun C hC => ?_) fun _ _ => rfl
  · exact mem_countSel.2 (hmem x hx)
  · obtain ⟨x, hx, rfl⟩ := hsurj C (mem_countSel.1 hC)
    exact ⟨x, hx, rfl⟩

/-! ### The pieces of `glueIn` -/

section Pieces

variable {N₁ N₂ : ℕ} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}

theorem count_dsum_inj {α β γ : Type*} (E : α ⊕ β ≃ γ) {σ₁ σ₁' : Equiv.Perm α}
    {σ₂ σ₂' : Equiv.Perm β} (h : dsum E σ₁ σ₂ = dsum E σ₁' σ₂') : σ₁ = σ₁' ∧ σ₂ = σ₂' := by
  refine ⟨Equiv.ext fun x => ?_, Equiv.ext fun x => ?_⟩
  · have := congrArg (fun σ => σ (E (.inl x))) h
    simp only [dsum_apply_inl] at this
    exact Sum.inl_injective (E.injective this)
  · have := congrArg (fun σ => σ (E (.inr x))) h
    simp only [dsum_apply_inr] at this
    exact Sum.inr_injective (E.injective this)

theorem count_fvSplit_inl_ne_fR (t : Wick.FermionVertex (leftKinds κ e))
    (y : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    (Sum.inr (fvSplit κ e (.inl t)) : Fin 1 ⊕ Wick.FermionVertex κ) ≠ fR κ e 1 (.inr y) := by
  rcases y with i | s
  · exact Sum.inr_ne_inl
  · rw [fR_inr_inr]
    intro h
    exact Sum.inl_ne_inr ((fvSplit κ e).injective (Sum.inr_injective h))

/-- The value of the left pairing of `glueIn` on a left field, read off from the glue. -/
theorem count_glueIn_left_eq {nA : ℕ} {C₁ C₁' : Contraction 1 nA (leftKinds κ e)}
    {C₂ C₂' : Contraction 1 0 (rightKinds κ e)}
    (h : (glueIn e C₁ C₂).1.1 = (glueIn e C₁' C₂').1.1)
    (x : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) : C₁.1.1 x = C₁'.1.1 x := by
  have hx := congrArg (fun σ => σ (fL κ e 1 (.inl x))) h
  rcases h₁ : C₁.1.1 x with i | t <;> rcases h₂ : C₁'.1.1 x with i' | t'
  · rw [Subsingleton.elim i i']
  · rw [glueIn_left_ext C₁ C₂ h₁, glueIn_left C₁' C₂' h₂] at hx
    exact absurd hx.symm (count_fvSplit_inl_ne_fR t' _)
  · rw [glueIn_left C₁ C₂ h₁, glueIn_left_ext C₁' C₂' h₂] at hx
    exact absurd hx (count_fvSplit_inl_ne_fR t _)
  · rw [glueIn_left C₁ C₂ h₁, glueIn_left C₁' C₂' h₂] at hx
    exact congrArg Sum.inr (Sum.inl_injective ((fvSplit κ e).injective (Sum.inr_injective hx)))

/-- **For a fixed split, `glueIn` determines its pieces.** -/
theorem countGlueIn_pieces_eq {nA : ℕ} {C₁ C₁' : Contraction 1 nA (leftKinds κ e)}
    {C₂ C₂' : Contraction 1 0 (rightKinds κ e)} (h : glueIn e C₁ C₂ = glueIn e C₁' C₂') :
    C₁ = C₁' ∧ C₂ = C₂' := by
  have hf : (glueIn e C₁ C₂).1.1 = (glueIn e C₁' C₂').1.1 := by rw [h]
  have hp : gluePhotons e C₁.1.2 C₂.1.2 = gluePhotons e C₁'.1.2 C₂'.1.2 :=
    congrArg (fun C : Contraction 1 nA κ => C.1.2) h
  obtain ⟨hp₁, hp₂⟩ := count_dsum_inj _ hp
  have h₁ : C₁.1.1 = C₁'.1.1 := Equiv.ext (count_glueIn_left_eq hf)
  have h₂ : C₂.1.1 = C₂'.1.1 := by
    refine Equiv.ext ?_
    rintro (i | t)
    · obtain ⟨x, hx⟩ := C₁.1.1.surjective (.inl i)
      have hx' : C₁'.1.1 x = .inl i := by rw [← h₁]; exact hx
      have := congrArg (fun σ => σ (fL κ e 1 (.inl x))) hf
      rw [glueIn_left_ext C₁ C₂ hx, glueIn_left_ext C₁' C₂' hx'] at this
      exact Sum.inr_injective ((fR κ e 1).injective this)
    · have := congrArg (fun σ => σ (.inr (fvSplit κ e (.inr t)))) hf
      rw [glueIn_right, glueIn_right] at this
      exact Sum.inr_injective ((fR κ e 1).injective this)
  exact ⟨Subtype.ext (Prod.ext h₁ hp₁), Subtype.ext (Prod.ext h₂ hp₂)⟩

end Pieces

end QED.GradedProof.X1C

end
