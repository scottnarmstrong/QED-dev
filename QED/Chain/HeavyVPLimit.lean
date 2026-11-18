/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.HeavyVPOuter
public import QED.Chain.HeavyVPValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The heavy-flavour outer functional tends to `A₂⁽⁴⁾(y)` (analytic core of O3-M2)

Helper-level assembly of `QED/Chain/HeavyVPOuter.lean` (the outer functional of the heavy
lepton's subtracted `Π` is `e² heavyUnitReg`) and `QED/Chain/HeavyVPValue.lean` (the iterated
limit of `heavyUnitReg` is `a2Heavy`). It is **not** frozen and does not depend on any
multi-lepton model.

## Main statement

* `heavyOuter_iterated_limit`: for `y ∈ (0,1)`, loop mass `M_L = 1/y` and unit charge, in the
  order of D-37.4 (regulator masses last): for every `η > 0` there is `R` such that for all
  `M₁, M₂ > R` there are `δ > 0` and `Λ₀` such that for all `m_γ ∈ (0, δ)`, `Λ > Λ₀` and every
  pair `c₁, c₂` satisfying the Pauli–Villars conditions of the loop mass,
  `|16π⁴ outerF2 (s ↦ (Π_ℓ(s) - Π_ℓ(0)) s D(s)²) - a2Heavy y| < η`.

This is the analytic statement that a model-level heavy VP unit consumes once its nested form
(the analogue of `QED.TwoLoop.UnitVPLink.VPUnitNested` for a loop of mass `m_ℓ`) is proved.
-/

@[expose] public section

open Real Filter Topology

namespace QED.Chain.HeavyVP

open QED.TwoLoop.VPUnit QED.TwoLoop.UnitVPLink QED.Chain.HeavyLepton

/-- **The heavy-flavour outer functional tends to `A₂⁽⁴⁾(y)` in the order of D-37.4.** -/
theorem heavyOuter_iterated_limit {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ c₁ c₂ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ → 1 + c₁ + c₂ = 0 →
        (1 / y) ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
        |16 * π ^ 4 * outerF2 (fun s =>
            (heavyPi 1 (1 / y) M₁ M₂ c₁ c₂ s - heavyPi 1 (1 / y) M₁ M₂ c₁ c₂ 0) * s *
              photonD mγ Λ s ^ 2) - a2Heavy y| < η := by
  have hML : 1 < 1 / y := by rw [lt_div_iff₀ hy.1]; linarith [hy.2]
  intro η hη
  obtain ⟨R, hR⟩ := heavyUnitReg_iterated_limit_a2Heavy hy η hη
  refine ⟨max R (1 / y), fun M₁ M₂ h1 h2 => ?_⟩
  have hM₁ : 1 / y < M₁ := lt_of_le_of_lt (le_max_right _ _) h1
  have hM₂ : 1 / y < M₂ := lt_of_le_of_lt (le_max_right _ _) h2
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hR M₁ M₂ (lt_of_le_of_lt (le_max_left _ _) h1)
    (lt_of_le_of_lt (le_max_left _ _) h2)
  refine ⟨min δ 1, lt_min hδ one_pos, max Λ₀ 1, fun mγ Λ c₁ c₂ hm0 hm1 hΛ hPV₁ hPV₂ => ?_⟩
  have hmδ : mγ < δ := hm1.trans_le (min_le_left _ _)
  have hm1' : mγ < 1 := hm1.trans_le (min_le_right _ _)
  have hmΛ : mγ < Λ := by linarith [le_max_right Λ₀ 1]
  have key := heavyOuter_eq_heavyUnitReg (e := 1) (by linarith) hM₁ hM₂ hPV₁ hPV₂ hm0 hmΛ
    (by linarith)
  rw [one_pow, one_mul] at key
  rw [key]
  exact hΛ₀ mγ Λ hm0 hmδ (lt_of_le_of_lt (le_max_left _ _) hΛ)

end QED.Chain.HeavyVP
