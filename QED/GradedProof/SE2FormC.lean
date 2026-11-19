/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Decomp
public import QED.GradedProof.SE2LimC

/-!
# The class obligations of clause 2 for `C1`, `C2`

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2. The `δ₁` classes converge to `δ₁` times the one-loop self-energy
limit `i (A(p²) p̸ + B(p²) m)` (`QED/GradedProof/SE2LimC.lean`), which has the covariant form with
coefficients that are functions of `p²` (`classForm_repC1`, `classForm_repC2`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)

namespace QED.GradedProof.SE2

/-- A lower threshold implies a higher one. -/
theorem lt_of_threshold_le {m ν μ s : ℝ} (hm : 0 ≤ m) (hν : 0 ≤ ν) (hνμ : ν ≤ μ)
    (hs : -(m + ν) ^ 2 < s) : -(m + μ) ^ 2 < s :=
  lt_of_le_of_lt (neg_le_neg (pow_le_pow_left₀ (by linarith) (by linarith) 2)) hs

theorem seOneLoopLimit_eq (Q : Params) (c : ℂ) (p : Fin 4 → ℝ) (α β : Fin 4) :
    c * seOneLoopLimit Q p α β =
      seMat (c * I * QED.WickModel.selfEnergyLoopA Q (Minkowski.dot p p))
        (c * I * (QED.WickModel.selfEnergyLoopB Q (Minkowski.dot p p) * Q.m)) p α β := by
  simp only [seOneLoopLimit, seMat, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem classForm_repC1 : ClassForm repC1 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine ⟨fun s => (Q.δ₁ : ℂ) * I * QED.WickModel.selfEnergyLoopA Q s,
    fun s => (Q.δ₁ : ℂ) * I * (QED.WickModel.selfEnergyLoopB Q s * Q.m), fun p hp α β => ?_⟩
  rw [← seOneLoopLimit_eq]
  exact tendsto_contractionValue₂_repC1 hQ.hm hQ.hmγ hQ.hΛ
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β

theorem classForm_repC2 : ClassForm repC2 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine ⟨fun s => (Q.δ₁ : ℂ) * I * QED.WickModel.selfEnergyLoopA Q s,
    fun s => (Q.δ₁ : ℂ) * I * (QED.WickModel.selfEnergyLoopB Q s * Q.m), fun p hp α β => ?_⟩
  rw [← seOneLoopLimit_eq]
  exact tendsto_contractionValue₂_repC2 hQ.hm hQ.hmγ hQ.hΛ
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β

end QED.GradedProof.SE2

end
