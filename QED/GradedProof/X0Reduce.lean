/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Reduce
public import QED.GradedProof.VertexTwo

/-!
# (X₀): the trees

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0a. (T₉′)
holds trivially for a contraction without loops (`jointEnergyFirstIntegrable_of_loopCount_eq_zero`).
At a nonzero grading of graded order `5` a counterterm vertex of level `≥ 1` has graded order
`≥ 4`, so the vertex orders sum to at most `3` (`QED.GradedProof.sum_order_le_three`), while a
counterterm vertex costs two orders (`QED.GradedProof.two_mul_loopCount_add_le_sum_order`:
`2 · loopCount + 3 ≤ ∑ order`); so an attached connected `(1, 1)` contraction has no loop
(`loopCount_eq_zero_of_ne_zero`) and its (T₉′) is trivial (`jointEnergyFirstIntegrable_of_ne_zero`).
What remains is the zero grading.
-/

@[expose] public section

open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount lineMomentum₂)

namespace QED.GradedProof.X0

open QED.Graded

/-- (T₉′) without loops. -/
theorem jointEnergyFirstIntegrable_of_loopCount_eq_zero {L : ℕ}
    (G : (Fin L → Fin 4 → ℝ) → ℂ) (hL : L = 0) : QED.TwoLoop.jointEnergyFirstIntegrable L G := by
  subst hL
  exact SE2.jointEnergyFirstIntegrable_zero G

/-- At a nonzero grading of graded order `5`, an attached connected `(1, 1)` contraction has no
loop. -/
theorem loopCount_eq_zero_of_ne_zero {N : ℕ} {κ : Fin N → Wick.VertexKind} {g : Grading κ}
    (hg0 : g ≠ 0) (hg : gradedOrder κ g = 5) (C : Contraction 1 1 κ)
    (hC : ExternalsAttached C ∧ VerticesConnected C) : loopCount C = 0 := by
  obtain ⟨t, -⟩ := exists_level_of_ne_zero hg0
  have h3 := sum_order_le_three hg0 hg
  have hL := two_mul_loopCount_add_le_sum_order hC.1 hC.2 t.1 t.2
  omega

/-- **(X₀) at a nonzero grading**: the contraction is a tree. -/
theorem jointEnergyFirstIntegrable_of_ne_zero (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (g : Grading κ) (hg0 : g ≠ 0) (hg : gradedOrder κ g = 5)
    (C : Contraction 1 1 κ) (hC : ExternalsAttached C ∧ VerticesConnected C)
    (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ :=
  jointEnergyFirstIntegrable_of_loopCount_eq_zero _ (loopCount_eq_zero_of_ne_zero hg0 hg C hC)

end QED.GradedProof.X0

end
