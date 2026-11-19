/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0Num
public import QED.GradedProof.SE2TwoLoopGggg
public import QED.Integration.TwoLoopRefinedBoundFubini

/-!
# (X₀): (T₉′) for a two-loop contraction of `gauge` vertices from the edge criterion

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0d.5. Let `C`
be a contraction of `gauge` vertices, `ε > 0`, any masses, any flavoring. Number the parametric
lines on the loops by `ι : LoopLine C ≃ Fin (m + 1)`. If the line data pass the Boolean
criterion `EdgeCrit` and either `m ≥ 7` with at most four fermion lines on the loops, or `m ≥ 6`
with at most three, then the amplitude (T₇) in the frozen routing (T₄) with two loop momenta,
times any constant, satisfies (T₉′) (`jointEnergyFirstIntegrable_contractionAmplitude₂`).

## Proof

The amplitude is numerator times denominators (`contractionAmplitude₂_eq`); the denominators are
a constant times the parametric line denominators (`amplitudeDenominator_eq`); the numerator is a
polynomial of degree at most the number of fermion lines on the loops, bounded by their line
weights (`isLoopPoly_amplitudeNumerator_loop`, `refinedBound_amplitudeNumerator_loop`); the
criterion transports (`noSubdivergenceRefined_pMat_of_edgeCrit`); and the refined (`m ≥ 7`) or
cubic (`m ≥ 6`) two-loop Fubini theorem gives (T₉′).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.Enumeration (lineData)
open QED.Integration.TwoLoop (castLoopMatrix lineDenom RefinedBound LoopQuartic
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic)

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

/-- **(T₉′) for a two-loop contraction of `gauge` vertices passing the edge criterion.** -/
theorem jointEnergyFirstIntegrable_contractionAmplitude₂ (P : Params) (hε : 0 < P.ε)
    (hκ : ∀ t, κ t = .gauge) (φ : Flavoring κ) {m : ℕ} (ι : LoopLine C ≃ Fin (m + 1))
    (hcrit : EdgeCrit (lineData C))
    (hsize : (7 ≤ m ∧ Fintype.card (LoopFermion C) ≤ 4) ∨
      (6 ≤ m ∧ Fintype.card (LoopFermion C) ≤ 3))
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) (c : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      c * contractionAmplitude₂ P C φ pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  set c' := c * offLoopFactor C P φ pOut pIn kIn with hc'
  have hpoly := (isLoopPoly_amplitudeNumerator_loop P hκ φ ι pOut pIn kIn αOut βIn μ).const_mul c'
  have hB := (refinedBound_amplitudeNumerator_loop P hκ φ ι pOut pIn kIn αOut βIn μ).const_mul c'
  have hcr := noSubdivergenceRefined_pMat_of_edgeCrit ι hcrit
  have hfun : (fun ℓ => c * contractionAmplitude₂ P C φ pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ)
      αOut βIn μ) = fun ℓ =>
        (c' * amplitudeNumerator P C φ pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) *
          ∏ i, (lineDenom (castLoopMatrix (pMat ι)) (pVec ι pOut pIn kIn) (pMass P φ ι) P.ε i
            ℓ)⁻¹ := by
    funext ℓ
    rw [contractionAmplitude₂_eq P hε.ne', amplitudeDenominator_eq P φ ι, hc']
    ring
  rw [hfun]
  rcases hsize with ⟨hm, hd⟩ | ⟨hm, hd⟩
  · obtain ⟨Q, hQ⟩ := (hpoly.mono hd).exists_loopQuartic
    rw [← hQ] at hB
    have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      Q _ (pVec ι pOut pIn kIn) (pMass P φ ι) hm hε hcr (hB.mono le_rfl hd)
    rw [hQ] at h
    exact h
  · obtain ⟨Q, hq, hQ⟩ := QED.GradedProof.SE2.IsLoopPoly.exists_loopQuartic_cubic (hpoly.mono hd)
    rw [← hQ] at hB
    have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic
      Q _ (pVec ι pOut pIn kIn) (pMass P φ ι) hq hm hε hcr (hB.mono le_rfl (by omega))
    rw [hQ] at h
    exact h

/-! ### The size test on the line data -/

/-- The number of parametric lines on a loop, from the line data. -/
def edgeLoopWeight (E : Multiset (ℕ × Fin N × Fin N)) : ℕ :=
  (E.map fun y => if edgeLoop E y = true then edgeWeight N y else 0).sum

/-- The number of fermion lines on a loop, from the line data. -/
def edgeLoopFermions (E : Multiset (ℕ × Fin N × Fin N)) : ℕ :=
  (E.map fun y => if y.1 < N ∧ edgeLoop E y = true then 1 else 0).sum

/-- The size condition of the two Fubini theorems on the line data. -/
def EdgeSize (E : Multiset (ℕ × Fin N × Fin N)) : Prop :=
  (8 ≤ edgeLoopWeight E ∧ edgeLoopFermions E ≤ 4) ∨ (7 ≤ edgeLoopWeight E ∧ edgeLoopFermions E ≤ 3)

instance (E : Multiset (ℕ × Fin N × Fin N)) : Decidable (EdgeSize E) := by
  unfold EdgeSize; infer_instance

theorem card_loopLine (C : Contraction nf nA κ) :
    Fintype.card (LoopLine C) = edgeLoopWeight (lineData C) := by
  classical
  rw [edgeLoopWeight, sum_lineData, Fintype.card_subtype, Finset.card_filter]
  refine (sum_line_weight fun l => if edgeLoop (lineData C) (edgeOf l) = true then 1 else 0).trans
    (Finset.sum_congr rfl fun l _ => ?_)
  split_ifs <;> simp

theorem card_loopFermion (C : Contraction nf nA κ) :
    Fintype.card (LoopFermion C) = edgeLoopFermions (lineData C) := by
  classical
  rw [edgeLoopFermions, sum_lineData, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_sum_type]
  have h0 : ∀ g : PhotonLine C, ¬ (edgeOf (Sum.inr g : Line C)).1 < N := fun g => by
    simp [label_lt_iff]
  simp only [h0, false_and, ite_false, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [label_lt_iff, Sum.isLeft_inl, true_and]

/-- **(T₉′) for a two-loop contraction of `gauge` vertices from the Boolean tests** on its line
data. -/
theorem jointEnergyFirstIntegrable_of_edgeCrit (P : Params) (hε : 0 < P.ε)
    (hκ : ∀ t, κ t = .gauge) (φ : Flavoring κ) (hcrit : EdgeCrit (lineData C))
    (hsize : EdgeSize (lineData C))
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) (c : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      c * contractionAmplitude₂ P C φ pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  have hw := card_loopLine C
  have hf := card_loopFermion C
  have hpos : 1 ≤ Fintype.card (LoopLine C) := by
    rw [hw]; rcases hsize with h | h <;> omega
  refine jointEnergyFirstIntegrable_contractionAmplitude₂ P hε hκ φ
    (Fintype.equivFinOfCardEq (Nat.succ_pred_eq_of_pos hpos).symm) hcrit ?_ pOut pIn kIn αOut βIn
    μ c
  rw [hf]
  rcases hsize with h | h
  · exact Or.inl ⟨by rw [Nat.pred_eq_sub_one, hw]; omega, h.2⟩
  · exact Or.inr ⟨by rw [Nat.pred_eq_sub_one, hw]; omega, h.2⟩

end QED.GradedProof.X0

end
