/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealDecomp
public import QED.GradedProof.SE2FormC

/-!
# The reality class obligations for `C1`, `C2`

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `SEReal`; the reality counterpart of `QED/GradedProof/SE2FormC.lean`.

The one-loop self-energy limit `i (A(p²) p̸ + B(p²) m)` has real form factors `A`, `B` (they are
casts of real Feynman-parameter integrals), so it satisfies `X♯ = -X`
(`sharp_seOneLoopLimit`). The `δ₁` classes converge to `δ₁` times it (`classSharp_repC1`,
`classSharp_repC2`).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)

namespace QED.GradedProof.SE2Real

open QED.GradedProof.SE2

theorem conj_selfEnergyLoopA (Q : Params) (s : ℝ) :
    starRingEnd ℂ (QED.WickModel.selfEnergyLoopA Q s) = QED.WickModel.selfEnergyLoopA Q s := by
  rw [QED.WickModel.selfEnergyLoopA, Complex.conj_ofReal]

theorem conj_selfEnergyLoopB (Q : Params) (s : ℝ) :
    starRingEnd ℂ (QED.WickModel.selfEnergyLoopB Q s) = QED.WickModel.selfEnergyLoopB Q s := by
  rw [QED.WickModel.selfEnergyLoopB, Complex.conj_ofReal]

/-- **The one-loop self-energy limit is `♯`-odd.** -/
theorem sharp_seOneLoopLimit (Q : Params) (p : Fin 4 → ℝ) :
    sharp (seOneLoopLimit Q p) = (-1 : ℂ) • seOneLoopLimit Q p := by
  rw [seOneLoopLimit, sharp_smul, sharp_seForm, map_mul, conj_selfEnergyLoopA,
    conj_selfEnergyLoopB, Complex.conj_ofReal, Complex.conj_I, smul_smul, neg_one_mul]

/-- `δ₁` times the one-loop self-energy limit as a `♯`-symmetric limit. -/
theorem hasSharpLim_delta_one {T : ℝ} (Q : Params)
    {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε => G ε p α β) (𝓝[>] 0) (𝓝 ((Q.δ₁ : ℂ) * seOneLoopLimit Q p α β))) :
    HasSharpLim T (-1) G := by
  refine ⟨fun p => (Q.δ₁ : ℂ) • seOneLoopLimit Q p, fun p hp => ⟨fun α β => ?_, ?_⟩⟩
  · simpa only [Matrix.smul_apply, smul_eq_mul] using h p hp α β
  · rw [sharp_smul, Complex.conj_ofReal, sharp_seOneLoopLimit, smul_comm]

theorem classSharp_repC1 : ClassSharp repC1 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine hasSharpLim_delta_one Q fun p hp α β => ?_
  exact tendsto_contractionValue₂_repC1 hQ.hm hQ.hmγ hQ.hΛ
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β

theorem classSharp_repC2 : ClassSharp repC2 := by
  intro Q hQ m₀ ν _ _ _ _ hν0 hν _
  refine hasSharpLim_delta_one Q fun p hp α β => ?_
  exact tendsto_contractionValue₂_repC2 hQ.hm hQ.hmγ hQ.hΛ
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_left _ _)) hp)
    (lt_of_threshold_le hQ.hm.le hν0.le (hν.trans (min_le_right _ _)) hp) α β

end QED.GradedProof.SE2Real

end
