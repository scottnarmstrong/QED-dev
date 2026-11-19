/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0Reduce
public import QED.GradedProof.X0Open
public import QED.GradedProof.LoopCycle
public import QED.TwoLoop.LoopBoundTwoExact

/-!
# (X₀): the reduction to three families of contractions

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0f. At a
nonzero grading the contraction is a tree (`jointEnergyFirstIntegrable_of_ne_zero`). At the zero
grading the vertex orders sum to `5`, and an attached connected `(1, 1)` contraction has
`2 L + 1 = V₃` loops, `V₃` the number of `gauge` and `gaugeCt` vertices
(`QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_eq`), so `L ≤ 2`:

* `L = 0`: nothing to prove;
* `L = 2`: then `V₃ = 5` and every vertex is a `gauge` vertex, so the kind sequence is
  `gauges 5`; the contractions with no closed fermion loop are done
  (`jointEnergyFirstIntegrable_open`), the others are `TwoLoopClosedGoal`;
* `L = 1`: `OneLoopGoal` (one counterterm vertex of level `0`).

`jointEnergyFirstIntegrable_five_of_goals` assembles (X₀) from the two remaining goals.
-/

@[expose] public section

open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount lineMomentum₂)

namespace QED.GradedProof.X0

open QED.Graded
open QED.TwoLoop.Enumeration (gauges)

/-- The graded integrand of (X₀). -/
noncomputable def integrand (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (g : Grading κ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin (loopCount C) → Fin 4 → ℝ) : ℂ :=
  (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
    regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ

/-- **Remaining goal: one loop.** Every attached connected `(1, 1)` contraction with one loop
whose vertex orders sum to `5` satisfies (T₉′) at the zero grading. -/
def OneLoopGoal (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) : Prop :=
  ∀ {N : ℕ} (κ : Fin N → Wick.VertexKind) (C : Contraction 1 1 κ), ∑ t, (κ t).order = 5 →
    ExternalsAttached C → VerticesConnected C → loopCount C = 1 →
    ∀ pOut pIn kIn : Fin 1 → Fin 4 → ℝ, pOut 0 = pIn 0 + kIn 0 → ∀ αOut βIn μ : Fin 1 → Fin 4,
      QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
        (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ)

/-- **Remaining goal: two loops with a closed fermion loop.** -/
def TwoLoopClosedGoal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) : Prop :=
  ∀ C : Contraction 1 1 (gauges 5), ExternalsAttached C → VerticesConnected C →
    ¬ (∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) →
    ∀ pOut pIn kIn : Fin 1 → Fin 4 → ℝ, pOut 0 = pIn 0 + kIn 0 → ∀ αOut βIn μ : Fin 1 → Fin 4,
      QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
        (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ)

theorem gradedOrder_zero {N : ℕ} (κ : Fin N → Wick.VertexKind) :
    gradedOrder κ 0 = ∑ t, (κ t).order := by
  simp [gradedOrder]

/-- With vertex orders summing to `5` and five `gauge` or `gaugeCt` vertices, the kind sequence
is five `gauge` vertices. -/
theorem eq_gauges_of_card {N : ℕ} (κ : Fin N → Wick.VertexKind) (h5 : ∑ t, (κ t).order = 5)
    (hV : (Finset.univ.filter fun t => κ t = .gauge ∨ κ t = .gaugeCt).card = 5) :
    N = 5 ∧ ∀ t, κ t = .gauge := by
  have h1 := sum_order_eq κ
  have h2 := QED.TwoLoop.Enumeration.le_sum_order κ
  have h3 : (Finset.univ.filter fun t => κ t = .gauge ∨ κ t = .gaugeCt).card ≤ N := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin N)) _
  refine ⟨by omega, fun t => ?_⟩
  by_contra ht
  have : 1 ≤ (Finset.univ.filter fun t => κ t ≠ .gauge).card :=
    Finset.card_pos.2 ⟨t, by simp [ht]⟩
  omega

/-- **(X₀) from the two remaining goals.** -/
theorem jointEnergyFirstIntegrable_five_of_goals (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (hε : 0 < P.ε)
    (h1 : OneLoopGoal P Φ D) (h2 : TwoLoopClosedGoal P Φ D)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (g : Grading κ) (hg : gradedOrder κ g = 5)
    (C : Contraction 1 1 κ) (hC : ExternalsAttached C ∧ VerticesConnected C)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  by_cases hg0 : g = 0
  swap
  · exact jointEnergyFirstIntegrable_of_ne_zero P Φ D g hg0 hg C hC pOut pIn kIn αOut βIn μ
  subst hg0
  rw [gradedOrder_zero] at hg
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hg
    · exact h
  have hL := QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_eq hC.1 hC.2 hN
  have hV3 : (Finset.univ.filter fun t => κ t = .gauge ∨ κ t = .gaugeCt).card ≤ 5 := by
    have h1 := sum_order_eq κ
    omega
  have hL2 : loopCount C ≤ 2 := by omega
  rcases (show loopCount C = 0 ∨ loopCount C = 1 ∨ loopCount C = 2 by omega) with
    hLC | hLC | hLC
  · exact jointEnergyFirstIntegrable_of_loopCount_eq_zero _ hLC
  · exact h1 κ C hg hC.1 hC.2 hLC pOut pIn kIn hmom αOut βIn μ
  · obtain ⟨rfl, hκ⟩ := eq_gauges_of_card κ hg (by omega)
    obtain rfl : κ = gauges 5 := funext hκ
    by_cases hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)
    · exact jointEnergyFirstIntegrable_open P Φ D hε C hC.1 hC.2 hcyc pOut pIn kIn hmom αOut
        βIn μ
    · exact h2 C hC.1 hC.2 hcyc pOut pIn kIn hmom αOut βIn μ

end QED.GradedProof.X0

end
