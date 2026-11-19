/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormC
public import QED.GradedProof.SE2DecompD
public import QED.WickModel.ElectronOnShell

/-!
# Clause 3: the classes `C1`, `C2`

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 3: `ClassFormD` for the one-loop self-energy with a `δ₁` vertex, whose
limit is `δ₁ i (A(p²) p̸ + B(p²) m)` with `A`, `B` differentiable below both thresholds
(`QED.WickModel.differentiableAt_selfEnergyLoopA`, `…B`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)

namespace QED.GradedProof.SE2

/-- The one-loop coefficients are differentiable on the region below `-(m + ν)²`. -/
theorem differentiableAt_loopAB (Q : Params) (hm : 0 < Q.m) {ν : ℝ} (hν0 : 0 < ν)
    (hν : ν ≤ min Q.mγ Q.Λ) (c : ℂ) {s : ℝ} (hs : -(Q.m + ν) ^ 2 < s) :
    DifferentiableAt ℝ (fun s => c * QED.WickModel.selfEnergyLoopA Q s) s ∧
      DifferentiableAt ℝ (fun s => c * (QED.WickModel.selfEnergyLoopB Q s * Q.m)) s := by
  have hmγ : 0 < Q.mγ := hν0.trans_le (hν.trans (min_le_left _ _))
  have hΛ : 0 < Q.Λ := hν0.trans_le (hν.trans (min_le_right _ _))
  have hs' : s ∈ Set.Ioi (-(Q.m + Q.mγ) ^ 2) ∩ Set.Ioi (-(Q.m + Q.Λ) ^ 2) :=
    ⟨lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_left _ _)) hs,
      lt_of_threshold_le hm.le hν0.le (hν.trans (min_le_right _ _)) hs⟩
  exact ⟨(QED.WickModel.differentiableAt_selfEnergyLoopA hm hmγ hΛ hs').const_mul c,
    ((QED.WickModel.differentiableAt_selfEnergyLoopB hm hmγ hΛ hs').mul_const _).const_mul c⟩

theorem classFormD_repC1 : ClassFormD repC1 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine HasSEFormD.of_seMat (fun s => (Q.δ₁ : ℂ) * I * QED.WickModel.selfEnergyLoopA Q s)
    (fun s => (Q.δ₁ : ℂ) * I * (QED.WickModel.selfEnergyLoopB Q s * Q.m))
    (fun s hs => (differentiableAt_loopAB Q hQ.hm hν0 hν _ hs).1)
    (fun s hs => (differentiableAt_loopAB Q hQ.hm hν0 hν _ hs).2) fun p hp α β => ?_
  rw [← seOneLoopLimit_eq]
  exact tendsto_contractionValue₂_repC1 hQ.hm hQ.hmγ hQ.hΛ
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β

theorem classFormD_repC2 : ClassFormD repC2 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine HasSEFormD.of_seMat (fun s => (Q.δ₁ : ℂ) * I * QED.WickModel.selfEnergyLoopA Q s)
    (fun s => (Q.δ₁ : ℂ) * I * (QED.WickModel.selfEnergyLoopB Q s * Q.m))
    (fun s hs => (differentiableAt_loopAB Q hQ.hm hν0 hν _ hs).1)
    (fun s hs => (differentiableAt_loopAB Q hQ.hm hν0 hν _ hs).2) fun p hp α β => ?_
  rw [← seOneLoopLimit_eq]
  exact tendsto_contractionValue₂_repC2 hQ.hm hQ.hmγ hQ.hΛ
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β

end QED.GradedProof.SE2

end
