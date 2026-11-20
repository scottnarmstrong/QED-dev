/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CLinesIn
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# (X₁) piece C: the number of shuffles

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (counting). A shuffle `e : Fin N₁ ⊕ Fin N₂ ≃ Fin N`
(`IsShuffle`: increasing on each summand) is determined by the image of `Fin N₁`, and every
subset of `Fin N` with `N₁` elements is such an image. Hence there are `C(N, N₁)` shuffles, and
the weight `1/N!` of a glued contraction summed over the shuffles is `1/(N₁! N₂!)`, the product
of the weights of the two pieces.

* `countShuffles`: the finset of shuffles.
* `card_countShuffles`: there are `C(N, N₁)` of them.
* `countShuffles_weight`: `(N!)⁻¹ · #shuffles = (N₁!)⁻¹ (N₂!)⁻¹`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset

open scoped Classical in
/-- The shuffles `Fin N₁ ⊕ Fin N₂ ≃ Fin N`. -/
noncomputable def countShuffles (N₁ N₂ N : ℕ) : Finset (Fin N₁ ⊕ Fin N₂ ≃ Fin N) :=
  univ.filter IsShuffle

theorem mem_countShuffles {N₁ N₂ N : ℕ} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N} :
    e ∈ countShuffles N₁ N₂ N ↔ IsShuffle e := by
  classical
  simp [countShuffles]

/-- The image of the first summand under `e`. -/
def countLeftImage {N₁ N₂ N : ℕ} (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) : Finset (Fin N) :=
  univ.map ⟨fun t => e (.inl t), e.injective.comp Sum.inl_injective⟩

theorem card_countLeftImage {N₁ N₂ N : ℕ} (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) :
    (countLeftImage e).card = N₁ := by
  simp [countLeftImage]

theorem mem_countLeftImage {N₁ N₂ N : ℕ} {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N} {x : Fin N} :
    x ∈ countLeftImage e ↔ ∃ t, e (.inl t) = x := by
  simp [countLeftImage]

theorem inr_mem_compl_countLeftImage {N₁ N₂ N : ℕ} (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (j : Fin N₂) :
    e (.inr j) ∈ (countLeftImage e)ᶜ := by
  rw [mem_compl, mem_countLeftImage]
  rintro ⟨t, ht⟩
  exact Sum.inl_ne_inr (e.injective ht)

theorem card_compl_countLeftImage {N₁ N₂ N : ℕ} (h : N₁ + N₂ = N)
    (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) : (countLeftImage e)ᶜ.card = N₂ := by
  rw [card_compl, card_countLeftImage, Fintype.card_fin]
  omega

/-- **A shuffle is determined by the image of the first summand.** -/
theorem countShuffle_ext {N₁ N₂ N : ℕ} (h : N₁ + N₂ = N) {e e' : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
    (he : IsShuffle e) (he' : IsShuffle e') (himg : countLeftImage e = countLeftImage e') :
    e = e' := by
  have hL : ∀ f : Fin N₁ ⊕ Fin N₂ ≃ Fin N, IsShuffle f → countLeftImage f = countLeftImage e →
      (fun t => f (.inl t)) = (countLeftImage e).orderEmbOfFin (card_countLeftImage e) :=
    fun f hf hfe => orderEmbOfFin_unique _ (fun t => hfe ▸ mem_countLeftImage.2 ⟨t, rfl⟩) hf.left
  have hR : ∀ f : Fin N₁ ⊕ Fin N₂ ≃ Fin N, IsShuffle f → countLeftImage f = countLeftImage e →
      (fun t => f (.inr t)) = (countLeftImage e)ᶜ.orderEmbOfFin
        (card_compl_countLeftImage h e) :=
    fun f hf hfe => orderEmbOfFin_unique _
      (fun t => hfe ▸ inr_mem_compl_countLeftImage f t) hf.right
  refine Equiv.ext ?_
  rintro (t | t)
  · exact (congrFun (hL e he rfl) t).trans (congrFun (hL e' he' himg.symm) t).symm
  · exact (congrFun (hR e he rfl) t).trans (congrFun (hR e' he' himg.symm) t).symm

/-- **The number of shuffles** is the binomial coefficient. -/
theorem card_countShuffles {N₁ N₂ N : ℕ} (h : N₁ + N₂ = N) :
    (countShuffles N₁ N₂ N).card = N.choose N₁ := by
  classical
  rw [show N.choose N₁ = (powersetCard N₁ (univ : Finset (Fin N))).card by simp]
  refine card_nbij countLeftImage (fun e _ => ?_) (fun e he e' he' himg => ?_) ?_
  · rw [mem_coe, mem_powersetCard]
    exact ⟨subset_univ _, card_countLeftImage e⟩
  · rw [mem_coe] at he he'
    exact countShuffle_ext h (mem_countShuffles.1 he) (mem_countShuffles.1 he') himg
  · intro s hs
    rw [mem_coe, mem_powersetCard] at hs
    have hc : sᶜ.card = N₂ := by
      rw [card_compl, hs.2, Fintype.card_fin]
      omega
    refine ⟨finSumEquivOfFinset hs.2 hc, mem_countShuffles.2 ⟨?_, ?_⟩, ?_⟩
    · exact (s.orderEmbOfFin hs.2).strictMono
    · exact (sᶜ.orderEmbOfFin hc).strictMono
    · ext x
      rw [mem_countLeftImage]
      simp only [finSumEquivOfFinset_inl]
      rw [← Set.mem_range, range_orderEmbOfFin, mem_coe]

/-- **The weight of the shuffles**: `(N!)⁻¹ · C(N, N₁) = (N₁!)⁻¹ (N₂!)⁻¹`. -/
theorem countShuffles_weight {N₁ N₂ N : ℕ} (h : N₁ + N₂ = N) :
    (N.factorial : ℂ)⁻¹ * ((countShuffles N₁ N₂ N).card : ℂ) =
      (N₁.factorial : ℂ)⁻¹ * (N₂.factorial : ℂ)⁻¹ := by
  rw [card_countShuffles h]
  subst h
  have key := Nat.add_choose_mul_factorial_mul_factorial N₂ N₁
  rw [Nat.add_comm N₂ N₁] at key
  have hN : ((N₁ + N₂).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h₁ : (N₁.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h₂ : (N₂.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have key' : ((N₁ + N₂).choose N₁ : ℂ) * N₂.factorial * N₁.factorial =
      (N₁ + N₂).factorial := by exact_mod_cast key
  field_simp
  rw [← key']
  ring

end QED.GradedProof.X1C

end
