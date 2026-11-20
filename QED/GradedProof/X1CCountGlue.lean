/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CCountSum

/-!
# (X₁) piece C: the graded sum of glued contractions factorizes

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (counting). **`countSum_glue`**: let `glue e C₁ C₂` be any way of
gluing a contraction `C₁` on the left piece and `C₂` on the right piece of a split `e` (as
`glueIn`, `glueOut`, `glueP`). Suppose that for every `κ` and grading `g` of order `K`

* (`hcount`) the `Sel`-selected contractions are, bijectively, the glued contractions
  `glue e C₁ C₂` over the splits `N₁ + N₂ = N`, the shuffles `e`, and the pieces with
  `Sel₁ C₁ (gradL g)`, `Sel₂ C₂ (gradR g)` (stated as an equality of sums for every summand), and
* (`hW`) the weight of a glued contraction is bilinear in weights of the pieces,
  `W (glue e C₁ C₂) g = ∑ z, W₁ z C₁ (gradL g) * W₂ z C₂ (gradR g)` (for the fermionic sign
  times the value: `fermionSign_glueIn` and `contractionValue_glueIn`, `z` the bridge indices).

Then `countSum Sel W K = ∑_{K₁+K₂=K} ∑ z, countSum Sel₁ (W₁ z) K₁ * countSum Sel₂ (W₂ z) K₂`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Contraction)
open QED.Graded

variable {nf nA nf₂ nA₂ : ℕ} {Z : Type} [Fintype Z]

/-- The summand of the factorized side: for fixed `(K₁, K₂)` and `z`, the product of the sums over
the kinds and gradings of the two pieces. -/
noncomputable def countPair (Sel₁ : CountSel nf nA) (Sel₂ : CountSel nf₂ nA₂)
    (W₁ : Z → CountWt nf nA) (W₂ : Z → CountWt nf₂ nA₂) (K N₁ N₂ : ℕ) : ℂ :=
  ∑ q ∈ antidiagonal K, ∑ z,
    (∑ κ₁ : Fin N₁ → Wick.VertexKind, ∑ g₁ ∈ countGr κ₁ q.1, ∑ C₁ ∈ countSel Sel₁ g₁,
      W₁ z C₁ g₁) *
    (∑ κ₂ : Fin N₂ → Wick.VertexKind, ∑ g₂ ∈ countGr κ₂ q.2, ∑ C₂ ∈ countSel Sel₂ g₂,
      W₂ z C₂ g₂)

theorem countPair_eq_zero (Sel₁ : CountSel nf nA) (Sel₂ : CountSel nf₂ nA₂)
    (W₁ : Z → CountWt nf nA) (W₂ : Z → CountWt nf₂ nA₂) {K N₁ N₂ : ℕ} (h : K < N₁ + N₂) :
    countPair Sel₁ Sel₂ W₁ W₂ K N₁ N₂ = 0 := by
  refine sum_eq_zero fun q hq => sum_eq_zero fun z _ => ?_
  rw [mem_antidiagonal] at hq
  rcases Nat.lt_or_ge q.1 N₁ with h₁ | h₁
  · rw [countSum_term_eq_zero Sel₁ (W₁ z) h₁, zero_mul]
  · rw [countSum_term_eq_zero Sel₂ (W₂ z) (by omega), mul_zero]

/-- For a fixed split `e`, the sum over the kinds and gradings of `κ` of a function of the
pieces is `countPair`. -/
theorem count_split_eq_countPair (Sel₁ : CountSel nf nA) (Sel₂ : CountSel nf₂ nA₂)
    (W₁ : Z → CountWt nf nA) (W₂ : Z → CountWt nf₂ nA₂) (K : ℕ) {N N₁ N₂ : ℕ}
    (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) :
    ∑ κ : Fin N → Wick.VertexKind, ∑ g ∈ countGr κ K, ∑ z,
      (∑ C₁ ∈ countSel Sel₁ (gradL κ e g), W₁ z C₁ (gradL κ e g)) *
      (∑ C₂ ∈ countSel Sel₂ (gradR κ e g), W₂ z C₂ (gradR κ e g)) =
    countPair Sel₁ Sel₂ W₁ W₂ K N₁ N₂ := by
  set a : ∀ z {N₁ : ℕ} (κ₁ : Fin N₁ → Wick.VertexKind), Grading κ₁ → ℂ :=
    fun z _ κ₁ g₁ => ∑ C₁ ∈ countSel Sel₁ (κ := κ₁) g₁, W₁ z C₁ g₁
  set b : ∀ z {N₂ : ℕ} (κ₂ : Fin N₂ → Wick.VertexKind), Grading κ₂ → ℂ :=
    fun z _ κ₂ g₂ => ∑ C₂ ∈ countSel Sel₂ (κ := κ₂) g₂, W₂ z C₂ g₂
  change ∑ κ : Fin N → Wick.VertexKind, ∑ g ∈ countGr κ K, ∑ z,
      a z (leftKinds κ e) (gradL κ e g) * b z (rightKinds κ e) (gradR κ e g) =
    ∑ q ∈ antidiagonal K, ∑ z, (∑ κ₁ : Fin N₁ → Wick.VertexKind, ∑ g₁ ∈ countGr κ₁ q.1,
      a z κ₁ g₁) * (∑ κ₂ : Fin N₂ → Wick.VertexKind, ∑ g₂ ∈ countGr κ₂ q.2, b z κ₂ g₂)
  refine (sum_congr rfl fun κ _ => countSum_grading_split κ e K
    (fun g₁ g₂ => ∑ z, a z _ g₁ * b z _ g₂)).trans ?_
  refine (countSum_kinds_split e (fun κ₁ κ₂ => ∑ q ∈ antidiagonal K, ∑ g₁ ∈ countGr κ₁ q.1,
    ∑ g₂ ∈ countGr κ₂ q.2, ∑ z, a z κ₁ g₁ * b z κ₂ g₂)).trans ?_
  -- reorder `κ₁ κ₂ q g₁ g₂ z` into `q z κ₁ κ₂ g₁ g₂`
  calc _ = ∑ κ₁ : Fin N₁ → Wick.VertexKind, ∑ κ₂ : Fin N₂ → Wick.VertexKind,
        ∑ q ∈ antidiagonal K, ∑ z, ∑ g₁ ∈ countGr κ₁ q.1, ∑ g₂ ∈ countGr κ₂ q.2,
          a z κ₁ g₁ * b z κ₂ g₂ := by
        refine sum_congr rfl fun κ₁ _ => sum_congr rfl fun κ₂ _ => sum_congr rfl fun q _ => ?_
        exact (sum_congr rfl fun _ _ => sum_comm).trans sum_comm
      _ = ∑ κ₁ : Fin N₁ → Wick.VertexKind, ∑ q ∈ antidiagonal K, ∑ z,
          ∑ κ₂ : Fin N₂ → Wick.VertexKind, ∑ g₁ ∈ countGr κ₁ q.1, ∑ g₂ ∈ countGr κ₂ q.2,
            a z κ₁ g₁ * b z κ₂ g₂ :=
        sum_congr rfl fun _ _ => sum_comm.trans (sum_congr rfl fun _ _ => sum_comm)
      _ = ∑ q ∈ antidiagonal K, ∑ z, ∑ κ₁ : Fin N₁ → Wick.VertexKind,
          ∑ κ₂ : Fin N₂ → Wick.VertexKind, ∑ g₁ ∈ countGr κ₁ q.1, ∑ g₂ ∈ countGr κ₂ q.2,
            a z κ₁ g₁ * b z κ₂ g₂ :=
        sum_comm.trans (sum_congr rfl fun _ _ => sum_comm)
      _ = _ := by simp only [sum_mul_sum]

/-- **The counting lemma**: the graded sum of glued contractions is the sum over `K₁ + K₂ = K`
of products of graded sums of the pieces. -/
theorem countSum_glue (Sel Sel₁ : CountSel nf nA) (Sel₂ : CountSel nf₂ nA₂) (W : CountWt nf nA)
    (W₁ : Z → CountWt nf nA) (W₂ : Z → CountWt nf₂ nA₂)
    (glue : ∀ {N N₁ N₂ : ℕ} {κ : Fin N → Wick.VertexKind} (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N),
      Contraction nf nA (leftKinds κ e) → Contraction nf₂ nA₂ (rightKinds κ e) →
        Contraction nf nA κ) (K : ℕ)
    (hcount : ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = K →
      ∀ f : Contraction nf nA κ → ℂ, ∑ C ∈ countSel Sel g, f C =
        ∑ p ∈ antidiagonal N, ∑ e ∈ countShuffles p.1 p.2 N,
          ∑ C₁ ∈ countSel Sel₁ (gradL κ e g), ∑ C₂ ∈ countSel Sel₂ (gradR κ e g),
            f (glue e C₁ C₂))
    (hW : ∀ {N N₁ N₂ : ℕ} (κ : Fin N → Wick.VertexKind) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N)
      (g : Grading κ) (C₁ : Contraction nf nA (leftKinds κ e))
      (C₂ : Contraction nf₂ nA₂ (rightKinds κ e)), IsShuffle e → gradedOrder κ g = K →
      Sel₁ C₁ (gradL κ e g) → Sel₂ C₂ (gradR κ e g) →
      W (glue e C₁ C₂) g = ∑ z, W₁ z C₁ (gradL κ e g) * W₂ z C₂ (gradR κ e g)) :
    countSum Sel W K =
      ∑ q ∈ antidiagonal K, ∑ z, countSum Sel₁ (W₁ z) q.1 * countSum Sel₂ (W₂ z) q.2 := by
  have h1 : ∀ N, ∑ κ : Fin N → Wick.VertexKind, ∑ g ∈ countGr κ K, ∑ C ∈ countSel Sel g, W C g =
      ∑ p ∈ antidiagonal N, ((countShuffles p.1 p.2 N).card : ℂ) *
        countPair Sel₁ Sel₂ W₁ W₂ K p.1 p.2 := by
    intro N
    calc _ = ∑ κ : Fin N → Wick.VertexKind, ∑ g ∈ countGr κ K, ∑ p ∈ antidiagonal N,
          ∑ e ∈ countShuffles p.1 p.2 N, ∑ z,
            (∑ C₁ ∈ countSel Sel₁ (gradL κ e g), W₁ z C₁ (gradL κ e g)) *
            (∑ C₂ ∈ countSel Sel₂ (gradR κ e g), W₂ z C₂ (gradR κ e g)) := by
          refine sum_congr rfl fun κ _ => sum_congr rfl fun g hg => ?_
          rw [hcount κ g (mem_countGr.1 hg)]
          refine sum_congr rfl fun p _ => sum_congr rfl fun e he => ?_
          calc _ = ∑ C₁ ∈ countSel Sel₁ (gradL κ e g), ∑ C₂ ∈ countSel Sel₂ (gradR κ e g),
                ∑ z, W₁ z C₁ (gradL κ e g) * W₂ z C₂ (gradR κ e g) :=
              sum_congr rfl fun C₁ h₁ => sum_congr rfl fun C₂ h₂ =>
                hW κ e g C₁ C₂ (mem_countShuffles.1 he) (mem_countGr.1 hg)
                  (mem_countSel.1 h₁) (mem_countSel.1 h₂)
            _ = ∑ z, ∑ C₁ ∈ countSel Sel₁ (gradL κ e g), ∑ C₂ ∈ countSel Sel₂ (gradR κ e g),
                W₁ z C₁ (gradL κ e g) * W₂ z C₂ (gradR κ e g) :=
              (sum_congr rfl fun _ _ => sum_comm).trans sum_comm
            _ = _ := by simp only [sum_mul_sum]
      _ = ∑ p ∈ antidiagonal N, ∑ e ∈ countShuffles p.1 p.2 N,
          ∑ κ : Fin N → Wick.VertexKind, ∑ g ∈ countGr κ K, ∑ z,
            (∑ C₁ ∈ countSel Sel₁ (gradL κ e g), W₁ z C₁ (gradL κ e g)) *
            (∑ C₂ ∈ countSel Sel₂ (gradR κ e g), W₂ z C₂ (gradR κ e g)) := by
          rw [(sum_congr rfl fun _ _ => sum_comm).trans sum_comm]
          refine sum_congr rfl fun p _ => ?_
          rw [(sum_congr rfl fun _ _ => sum_comm).trans sum_comm]
      _ = _ := by
          refine sum_congr rfl fun p _ => ?_
          rw [sum_congr rfl fun e _ => count_split_eq_countPair Sel₁ Sel₂ W₁ W₂ K e, sum_const,
            nsmul_eq_mul]
  have hL : countSum Sel W K = ∑ a ∈ range (K + 1), ∑ b ∈ range (K + 1),
      ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) * countPair Sel₁ Sel₂ W₁ W₂ K a b := by
    rw [countSum, ← count_sum_antidiagonal_range K
      (fun p => ((p.1.factorial : ℂ)⁻¹ * (p.2.factorial : ℂ)⁻¹) *
        countPair Sel₁ Sel₂ W₁ W₂ K p.1 p.2)
      (fun a b h => by rw [countPair_eq_zero Sel₁ Sel₂ W₁ W₂ h, mul_zero])]
    refine sum_congr rfl fun N _ => ?_
    rw [h1, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [← mul_assoc, countShuffles_weight (mem_antidiagonal.1 hp)]
  rw [hL]
  have hR : ∀ q ∈ antidiagonal K, ∀ z, countSum Sel₁ (W₁ z) q.1 * countSum Sel₂ (W₂ z) q.2 =
      ∑ a ∈ range (K + 1), ∑ b ∈ range (K + 1), ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) *
        ((∑ κ₁ : Fin a → Wick.VertexKind, ∑ g₁ ∈ countGr κ₁ q.1, ∑ C₁ ∈ countSel Sel₁ g₁,
          W₁ z C₁ g₁) *
        (∑ κ₂ : Fin b → Wick.VertexKind, ∑ g₂ ∈ countGr κ₂ q.2, ∑ C₂ ∈ countSel Sel₂ g₂,
          W₂ z C₂ g₂)) := by
    intro q hq z
    rw [mem_antidiagonal] at hq
    rw [countSum_eq_of_le Sel₁ (W₁ z) (show q.1 ≤ K by omega),
      countSum_eq_of_le Sel₂ (W₂ z) (show q.2 ≤ K by omega), sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [sum_congr rfl fun q hq => sum_congr rfl fun z _ => hR q hq z]
  calc _ = ∑ a ∈ range (K + 1), ∑ b ∈ range (K + 1), ∑ q ∈ antidiagonal K, ∑ z,
        ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) *
        ((∑ κ₁ : Fin a → Wick.VertexKind, ∑ g₁ ∈ countGr κ₁ q.1, ∑ C₁ ∈ countSel Sel₁ g₁,
          W₁ z C₁ g₁) *
        (∑ κ₂ : Fin b → Wick.VertexKind, ∑ g₂ ∈ countGr κ₂ q.2, ∑ C₂ ∈ countSel Sel₂ g₂,
          W₂ z C₂ g₂)) := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        rw [countPair, mul_sum]
        exact sum_congr rfl fun q _ => by rw [mul_sum]
    _ = _ := (sum_congr rfl fun _ _ => sum_comm).trans (sum_comm.trans
        (sum_congr rfl fun _ _ => (sum_congr rfl fun _ _ => sum_comm).trans sum_comm))

end QED.GradedProof.X1C

end
