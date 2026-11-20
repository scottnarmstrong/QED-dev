/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CCountShuffle
public import QED.Frozen.Graded.SelectedPart

/-!
# (X₁) piece C: the counting of glued contractions

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (counting). The graded sum (G₆) is written with a general
selection and a general weight (`countSum`; `selectedPart` is the case of the fermionic sign
times the value). If, for every vertex sequence `κ` and grading `g` of order `K`, the selected
contractions are exactly the glued contractions `glue e C₁ C₂` of selected pieces over the splits
`N₁ + N₂ = N` and the shuffles `e` (`hcount`, a bijection statement), and the weight of a glued
contraction is bilinear in the weights of its pieces (`hW`), then the graded sum is the sum over
`K₁ + K₂ = K` of products of the graded sums of the pieces (`countSum_glue`). The factors `1/N!`
become `1/(N₁! N₂!)` by the count of shuffles; the kinds and gradings of `κ` are those of the
pieces (`countSum_kinds_split`, `countSum_grading_split`); no cast is used.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Contraction)
open QED.Graded

/-- The selection predicates of (G₆) for contractions with `nf` fermion and `nA` photon
externals. -/
abbrev CountSel (nf nA : ℕ) : Type :=
  ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Grading κ → Prop

/-- A weight of graded contractions. -/
abbrev CountWt (nf nA : ℕ) : Type :=
  ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction nf nA κ → Grading κ → ℂ

open scoped Classical in
/-- The gradings of `κ` of order `K` (levels at most `K`, as in (G₆)). -/
noncomputable def countGr {N : ℕ} (κ : Fin N → Wick.VertexKind) (K : ℕ) : Finset (Grading κ) :=
  (Fintype.piFinset fun _ : CtVertex κ => range (K + 1)).filter fun g => gradedOrder κ g = K

open scoped Classical in
/-- The selected contractions at the grading `g`. -/
noncomputable def countSel {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (Sel : CountSel nf nA)
    (g : Grading κ) : Finset (Contraction nf nA κ) :=
  univ.filter fun C => Sel C g

theorem mem_countSel {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {Sel : CountSel nf nA}
    {g : Grading κ} {C : Contraction nf nA κ} : C ∈ countSel Sel g ↔ Sel C g := by
  classical
  simp [countSel]

/-- **The graded sum (G₆) with a general weight.** -/
noncomputable def countSum {nf nA : ℕ} (Sel : CountSel nf nA) (W : CountWt nf nA) (K : ℕ) : ℂ :=
  ∑ N ∈ range (K + 1), (N.factorial : ℂ)⁻¹ *
    ∑ κ : Fin N → Wick.VertexKind, ∑ g ∈ countGr κ K, ∑ C ∈ countSel Sel g, W C g

theorem selectedPart_eq_countSum (P : QED.WickModel.Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (nf nA : ℕ) (Sel : CountSel nf nA)
    (K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    selectedPart P Φ D nf nA Sel K pOut pIn kIn αOut βIn μ =
      countSum Sel (fun C g => ((QED.WickModel.fermionSign C : ℤ) : ℂ) *
        contractionValue P Φ D C g pOut pIn kIn αOut βIn μ) K := rfl

/-! ### Orders bound the number of vertices and the levels -/

theorem countOne_le_order (k : Wick.VertexKind) : 1 ≤ k.order := by
  cases k <;> decide

theorem count_card_le_gradedOrder {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ) :
    N ≤ gradedOrder κ g := by
  unfold gradedOrder
  calc N = ∑ _t : Fin N, 1 := by simp
    _ ≤ ∑ t, (κ t).order := sum_le_sum fun t _ => countOne_le_order (κ t)
    _ ≤ _ := Nat.le_add_right _ _

theorem count_level_le_gradedOrder {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ)
    (t : CtVertex κ) : g t ≤ gradedOrder κ g := by
  unfold gradedOrder
  calc g t ≤ 2 * g t := by omega
    _ ≤ ∑ t, 2 * g t := single_le_sum (f := fun t => 2 * g t) (fun _ _ => Nat.zero_le _)
        (mem_univ t)
    _ ≤ _ := Nat.le_add_left _ _

theorem mem_countGr {N : ℕ} {κ : Fin N → Wick.VertexKind} {K : ℕ} {g : Grading κ} :
    g ∈ countGr κ K ↔ gradedOrder κ g = K := by
  classical
  simp only [countGr, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h t
  have := count_level_le_gradedOrder κ g t
  omega

theorem countGr_eq_empty {N : ℕ} (κ : Fin N → Wick.VertexKind) {K : ℕ} (h : K < N) :
    countGr κ K = ∅ := by
  refine eq_empty_of_forall_notMem fun g hg => ?_
  have := count_card_le_gradedOrder κ g
  rw [mem_countGr.1 hg] at this
  omega

/-- The summand of `countSum` at `N` vertices vanishes beyond the order. -/
theorem countSum_term_eq_zero {nf nA : ℕ} (Sel : CountSel nf nA) (W : CountWt nf nA) {K N : ℕ}
    (h : K < N) :
    ∑ κ : Fin N → Wick.VertexKind, ∑ g ∈ countGr κ K, ∑ C ∈ countSel Sel g, W C g = 0 :=
  sum_eq_zero fun κ _ => by rw [countGr_eq_empty κ h, sum_empty]

/-- The range of `N` in `countSum` may be enlarged. -/
theorem countSum_eq_of_le {nf nA : ℕ} (Sel : CountSel nf nA) (W : CountWt nf nA) {K B : ℕ}
    (h : K ≤ B) :
    countSum Sel W K = ∑ N ∈ range (B + 1), (N.factorial : ℂ)⁻¹ *
      ∑ κ : Fin N → Wick.VertexKind, ∑ g ∈ countGr κ K, ∑ C ∈ countSel Sel g, W C g := by
  refine sum_subset (range_subset_range.2 (by omega)) fun N _ hN => ?_
  rw [mem_range, not_lt] at hN
  rw [countSum_term_eq_zero Sel W (by omega), mul_zero]

/-! ### Splitting the kinds and the gradings -/

/-- **The kinds of `κ` are those of the pieces**: for fixed `e`, `κ ↦ (κ ∘ e ∘ inl, κ ∘ e ∘ inr)`
is a bijection. -/
theorem countSum_kinds_split {N N₁ N₂ : ℕ} (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N)
    (Y : (Fin N₁ → Wick.VertexKind) → (Fin N₂ → Wick.VertexKind) → ℂ) :
    ∑ κ : Fin N → Wick.VertexKind, Y (leftKinds κ e) (rightKinds κ e) =
      ∑ κ₁ : Fin N₁ → Wick.VertexKind, ∑ κ₂ : Fin N₂ → Wick.VertexKind, Y κ₁ κ₂ := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.arrowCongr e.symm (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)) _ (fun x => Y x.1 x.2) fun κ => rfl

/-- The gradings of `κ` are pairs of gradings of the pieces. -/
def countGradEquiv {N N₁ N₂ : ℕ} (κ : Fin N → Wick.VertexKind) (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) :
    Grading κ ≃ Grading (leftKinds κ e) × Grading (rightKinds κ e) :=
  (Equiv.arrowCongr (ctSplit κ e).symm (Equiv.refl ℕ)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem countGradEquiv_apply {N N₁ N₂ : ℕ} (κ : Fin N → Wick.VertexKind)
    (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (g : Grading κ) :
    countGradEquiv κ e g = (gradL κ e g, gradR κ e g) := rfl

/-- **The gradings of order `K` are the pairs of gradings of orders `K₁ + K₂ = K`.** -/
theorem countSum_grading_split {N N₁ N₂ : ℕ} (κ : Fin N → Wick.VertexKind)
    (e : Fin N₁ ⊕ Fin N₂ ≃ Fin N) (K : ℕ)
    (X : Grading (leftKinds κ e) → Grading (rightKinds κ e) → ℂ) :
    ∑ g ∈ countGr κ K, X (gradL κ e g) (gradR κ e g) =
      ∑ q ∈ antidiagonal K, ∑ g₁ ∈ countGr (leftKinds κ e) q.1,
        ∑ g₂ ∈ countGr (rightKinds κ e) q.2, X g₁ g₂ := by
  classical
  rw [← sum_fiberwise_of_maps_to (s := countGr κ K) (t := antidiagonal K)
    (g := fun g => (gradedOrder _ (gradL κ e g), gradedOrder _ (gradR κ e g))) (fun g hg => by
      rw [mem_antidiagonal, ← gradedOrder_split, ← mem_countGr]; exact hg)]
  refine sum_congr rfl fun q hq => ?_
  rw [← sum_product']
  refine sum_equiv (countGradEquiv κ e) (fun g => ?_) fun g _ => rfl
  rw [mem_antidiagonal] at hq
  simp only [mem_filter, mem_product, countGradEquiv_apply, mem_countGr, Prod.ext_iff,
    gradedOrder_split κ e g]
  omega

/-! ### The counting lemma -/

/-- A bookkeeping lemma: summing over `N ≤ K` and `N₁ + N₂ = N` is summing over `N₁, N₂ ≤ K`
when the summand vanishes for `N₁ + N₂ > K`. -/
theorem count_sum_antidiagonal_range (K : ℕ) (f : ℕ × ℕ → ℂ)
    (hf : ∀ a b, K < a + b → f (a, b) = 0) :
    ∑ N ∈ range (K + 1), ∑ p ∈ antidiagonal N, f p =
      ∑ a ∈ range (K + 1), ∑ b ∈ range (K + 1), f (a, b) := by
  rw [← sum_product' (f := fun a b => f (a, b))]
  have hsub : (range (K + 1) ×ˢ range (K + 1)).filter (fun p => p.1 + p.2 ≤ K) ⊆
      range (K + 1) ×ˢ range (K + 1) := filter_subset _ _
  rw [← sum_subset hsub fun p _ hp => by
    simp only [mem_filter, not_and, not_le] at hp
    exact hf p.1 p.2 (hp (by assumption))]
  rw [← sum_fiberwise_of_maps_to (s := (range (K + 1) ×ˢ range (K + 1)).filter
    (fun p => p.1 + p.2 ≤ K)) (t := range (K + 1)) (g := fun p => p.1 + p.2) (fun p hp => by
    rw [mem_filter] at hp; rw [mem_range]; omega)]
  refine sum_congr rfl fun N hN => sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [mem_antidiagonal, mem_filter, mem_product, mem_range]
  rw [mem_range] at hN
  omega

end QED.GradedProof.X1C

end
