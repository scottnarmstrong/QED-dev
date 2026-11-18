/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Admissible heavy-lepton regulators exist

Helper-level proof for the Phase 5 Stage 0 packet (decision D-50), goal
`exists_heavyLepton_regulators`.

For each lepton `ℓ` take `M₁ = |m_ℓ| + |R_M| + 1`, `M₂ = |m_ℓ| + |R_M| + 2` and the
Pauli–Villars coefficients `c₁ = (M₂² - m_ℓ²)/(M₁² - M₂²)`, `c₂ = (M₁² - m_ℓ²)/(M₂² - M₁²)`
(those of `QED.Chain.HeavyVP.pvC1L`, `pvC2L`), which solve both conditions since `M₁² ≠ M₂²`.

## Main statements

* `exists_heavyLepton_regulators'`: the frozen goal `QED.Lepton.exists_heavyLepton_regulators`.
-/

@[expose] public section

namespace QED.Lepton.Proof

/-- **Admissible heavy-lepton regulators exist above every threshold.** -/
theorem exists_heavyLepton_regulators' {n : ℕ} (mH : Fin n → ℝ) (RM : ℝ) :
    ∃ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) ∧ (∀ ℓ, mH ℓ < MH₂ ℓ) ∧
      (∀ ℓ, RM < MH₁ ℓ) ∧ (∀ ℓ, RM < MH₂ ℓ) ∧ (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) ∧
      ∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0 := by
  have hm : ∀ ℓ, mH ℓ ≤ |mH ℓ| := fun ℓ => le_abs_self _
  have hR : RM ≤ |RM| := le_abs_self _
  have hm0 : ∀ ℓ, 0 ≤ |mH ℓ| := fun ℓ => abs_nonneg _
  have hR0 : 0 ≤ |RM| := abs_nonneg _
  have hne : ∀ ℓ, (|mH ℓ| + |RM| + 1) ^ 2 - (|mH ℓ| + |RM| + 2) ^ 2 ≠ 0 := by
    intro ℓ
    have := hm0 ℓ
    nlinarith
  refine ⟨fun ℓ => |mH ℓ| + |RM| + 1, fun ℓ => |mH ℓ| + |RM| + 2,
    fun ℓ => ((|mH ℓ| + |RM| + 2) ^ 2 - mH ℓ ^ 2) /
      ((|mH ℓ| + |RM| + 1) ^ 2 - (|mH ℓ| + |RM| + 2) ^ 2),
    fun ℓ => ((|mH ℓ| + |RM| + 1) ^ 2 - mH ℓ ^ 2) /
      ((|mH ℓ| + |RM| + 2) ^ 2 - (|mH ℓ| + |RM| + 1) ^ 2),
    fun ℓ => ?_, fun ℓ => ?_, fun ℓ => ?_, fun ℓ => ?_, fun ℓ => ?_, fun ℓ => ?_⟩
  · linarith [hm ℓ]
  · linarith [hm ℓ]
  · linarith [hm0 ℓ]
  · linarith [hm0 ℓ]
  · have h1 := hne ℓ
    have h2 : (|mH ℓ| + |RM| + 2) ^ 2 - (|mH ℓ| + |RM| + 1) ^ 2 ≠ 0 := fun h =>
      h1 (by linarith)
    field_simp
    ring
  · have h1 := hne ℓ
    have h2 : (|mH ℓ| + |RM| + 2) ^ 2 - (|mH ℓ| + |RM| + 1) ^ 2 ≠ 0 := fun h =>
      h1 (by linarith)
    field_simp
    ring

end QED.Lepton.Proof

end
