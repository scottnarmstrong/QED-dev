/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopParametricAlgebra

/-!
# (R-Π₄) step L6c′: the first Symanzik polynomial of a theta graph

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), steps L6c′ and L7. Every
line of the vacuum-polarization shapes has loop row `(1, 0)`, `(0, 1)` or `(1, -1)`: the lines
form three chains between the two photon vertices. With the chain sums
`Z₁ = ∑_{(1,0)} zᵢ`, `Z₂ = ∑_{(0,1)} zᵢ`, `Z₃ = ∑_{(1,-1)} zᵢ`:

* `chainZ`: the chain sum of a row;
* `symanzikU_chain`: `U = Z₁ Z₂ + Z₃ (Z₁ + Z₂)`, independent of the distribution inside the chains;
* `symanzikU_ge_chain`: `U ≥ Z₃ (Z₁ + Z₂)` for `z ≥ 0` (the photon-corner lower bound of L7).
-/

@[expose] public section

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

variable {m : ℕ}

/-- The sum of the parameters of the lines with loop row `r`. -/
noncomputable def chainZ (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) (r : Fin 2 → ℝ) :
    ℝ :=
  ∑ i, if α i = r then z i else 0

theorem symanzikMatrix_chain (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ)
    (hα : ∀ i, α i = ![1, 0] ∨ α i = ![0, 1] ∨ α i = ![1, -1]) :
    symanzikMatrix α z 0 0 = chainZ α z ![1, 0] + chainZ α z ![1, -1] ∧
      symanzikMatrix α z 1 1 = chainZ α z ![0, 1] + chainZ α z ![1, -1] ∧
      symanzikMatrix α z 0 1 = -chainZ α z ![1, -1] ∧
      symanzikMatrix α z 1 0 = -chainZ α z ![1, -1] := by
  have hne1 : (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := fun h => by
    simpa using congrFun h 0
  have hne2 : (![1, 0] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 1; norm_num at this
  have hne3 : (![0, 1] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    simpa using congrFun h 0
  simp only [symanzikMatrix, Matrix.of_apply, chainZ, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  refine ⟨Finset.sum_congr rfl fun i _ => ?_, Finset.sum_congr rfl fun i _ => ?_,
    Finset.sum_congr rfl fun i _ => ?_, Finset.sum_congr rfl fun i _ => ?_⟩ <;>
    rcases hα i with h | h | h <;>
    simp [h, hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm]

/-- **The first Symanzik polynomial of a theta graph** in its chain sums. -/
theorem symanzikU_chain (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ)
    (hα : ∀ i, α i = ![1, 0] ∨ α i = ![0, 1] ∨ α i = ![1, -1]) :
    symanzikU α z = chainZ α z ![1, 0] * chainZ α z ![0, 1] +
      chainZ α z ![1, -1] * (chainZ α z ![1, 0] + chainZ α z ![0, 1]) := by
  obtain ⟨h00, h11, h01, h10⟩ := symanzikMatrix_chain α z hα
  rw [symanzikU, Matrix.det_fin_two, h00, h11, h01, h10]
  ring

theorem chainZ_nonneg (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (r : Fin 2 → ℝ) : 0 ≤ chainZ α z r :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hz i]

/-- **The photon-corner lower bound** `U ≥ Z₃ (Z₁ + Z₂)`. -/
theorem symanzikU_ge_chain (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hα : ∀ i, α i = ![1, 0] ∨ α i = ![0, 1] ∨ α i = ![1, -1]) :
    chainZ α z ![1, -1] * (chainZ α z ![1, 0] + chainZ α z ![0, 1]) ≤ symanzikU α z := by
  rw [symanzikU_chain α z hα]
  have := mul_nonneg (chainZ_nonneg α hz ![1, 0]) (chainZ_nonneg α hz ![0, 1])
  linarith

end QED.GradedProof.RPi4

end
