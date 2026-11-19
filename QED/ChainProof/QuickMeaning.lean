/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFamilyFunction
public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.TwoLoop.ContractionValue
public import QED.ChainProof.QuickOrder

/-!
# The meaning theorems (M₁)–(M₃) of the Stage 1a packet

Helper proofs of the Phase 5 Stage 1a theorem goals (decision D-53):

* `QED.ChainProof.onePIFamilyFunction₂_true'`: (M₁), the trivial family is (F₈).
* `QED.ChainProof.onePIFunction₂_sub_eq_family_add'`: (M₂), the order-`(2n+3)` part of (F₈) is
  the chain family plus the remaining contractions of total order `2n + 3`.
* `QED.ChainProof.contractionValue₂_params'`: (M₃), at T1's flavours the value is (T₁₀).

The order bookkeeping is `QED.ChainProof.Quick.sum_range_filter_order_sub`: since every vertex
has order at least one, the difference of the order-`K + 1` and order-`K` sums is the sum of the
terms of total order exactly `K + 1`.
-/

@[expose] public section

open QED.WickModel (Params Contraction IsOnePI fermionSign)
open QED.Lepton (Flavors onePIFunction₂ onePIFamilyFunction₂ contractionValue₂)

namespace QED.ChainProof

/-- (M₁) **The trivial family is the whole 1PI function.** -/
theorem onePIFamilyFunction₂_true' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) (nf nA : ℕ) :
    onePIFamilyFunction₂ P Φ nf nA (fun _ => True) = onePIFunction₂ P Φ nf nA := by
  funext K pOut pIn kIn αOut βIn μ
  unfold onePIFamilyFunction₂ onePIFunction₂
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun N _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun κ _ => ?_
  split_ifs
  · refine Finset.sum_congr rfl fun C _ => ?_
    by_cases h : IsOnePI C <;> simp [h]
  · rfl

/-- (M₃) **At T1's flavours the value is T1's** (definitional). -/
theorem contractionValue₂_params' (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) :
    contractionValue₂ P ⟨P.mass, P.loopCoeff, 0⟩ C = QED.WickModel.contractionValue₂ P C :=
  rfl

/-- The order-`(K + 1)` sum minus the order-`K` sum is the sum of the terms of total order
exactly `K + 1`. -/
theorem Quick.sum_range_filter_order_sub (c : ℕ → ℂ) (G : ∀ N : ℕ, (Fin N → Wick.VertexKind) → ℂ)
    (K : ℕ) :
    (∑ N ∈ Finset.range (K + 1 + 1), c N *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order ≤ K + 1), G N κ) -
      ∑ N ∈ Finset.range (K + 1), c N *
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order ≤ K), G N κ =
    ∑ N ∈ Finset.range (K + 1 + 1), c N *
      ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K + 1),
        if ∑ t, (κ t).order = K + 1 then G N κ else 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ _ (K + 1)]
  have hlast : ∑ κ ∈ (Finset.univ : Finset (Fin (K + 1) → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K + 1), G (K + 1) κ =
      ∑ κ ∈ (Finset.univ : Finset (Fin (K + 1) → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ K + 1),
        if ∑ t, (κ t).order = K + 1 then G (K + 1) κ else 0 := by
    refine Finset.sum_congr rfl fun κ hκ => ?_
    have h1 := Quick.le_sum_order κ
    have h2 := (Finset.mem_filter.1 hκ).2
    split_ifs with h3
    · rfl
    · omega
  rw [hlast, add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [← mul_sub]
  congr 1
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  split_ifs <;> first | omega | ring

open scoped Classical in
/-- (M₂) **The chains are a part of the order-`e^{2n+3}` vertex terms.** -/
theorem onePIFunction₂_sub_eq_family_add' (n : ℕ) (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Flavors F) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    onePIFunction₂ P Φ 1 1 (2 * n + 3) pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P Φ 1 1 (2 * n + 2) pOut pIn kIn αOut βIn μ =
      onePIFamilyFunction₂ P Φ 1 1 (QED.VPChain.IsVPChain n) (2 * n + 3) pOut pIn kIn αOut βIn μ +
        onePIFamilyFunction₂ P Φ 1 1
          (fun {_} {κ} C => ¬ QED.VPChain.IsVPChain n C ∧ ∑ t, (κ t).order = 2 * n + 3)
          (2 * n + 3) pOut pIn kIn αOut βIn μ := by
  have key := Quick.sum_range_filter_order_sub (fun N => (N.factorial : ℂ)⁻¹)
    (fun N κ => ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ) (2 * n + 2)
  beta_reduce at key
  unfold onePIFunction₂ onePIFamilyFunction₂
  refine key.trans ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun κ _ => ?_
  split_ifs with ho
  · simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    by_cases h1 : IsOnePI C <;> by_cases h2 : QED.VPChain.IsVPChain n C <;>
      simp [h1, h2, ho]
  · simp only [Finset.sum_filter]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    all_goals
      intro C _
      refine ite_eq_right_iff.mpr fun h' => absurd h' ?_
      first
        | (rintro ⟨-, -, h⟩; exact ho h)
        | (rintro ⟨-, h⟩; exact ho (Quick.order_sum_of_isVPChain h))

end QED.ChainProof

end
