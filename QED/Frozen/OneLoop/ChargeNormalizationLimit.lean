-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Provider.OneLoop.ChargeNormalizationLimit
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (M) **Charge normalization `F₁(0) = 1` (64.2) (packet 3 theorem goal).** For `e ≠ 0`,
`m > 0`, fixed regulators `m_γ, Λ > 0`, and a counterterm `Z₁` satisfying the charge condition
(K₀), the first form factor of the vertex function (J) tends to `1` as `q² → 0⁺` over on-shell
positive-energy pairs, uniformly over the pairs: near `q² = 0⁺` a form-factor pair exists, and
every such pair has its first component within `η` of `1`. The regulators are held fixed, as in
the order of limits of decision D-5 (`q² → 0⁺` before `m_γ → 0⁺`). A joint limit with
`m_γ → 0⁺` would be false: the slope of `F₁` at `q² = 0` grows like `ln(m/m_γ)`. -/
theorem isFormFactorPair_vertexFunction_dirac_limit (e Z₁ m mγ Λ : ℝ) (he : e ≠ 0) (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hZ : IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ) (η : ℝ)
    (hη : 0 < η) :
    ∃ δ > 0, ∀ (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2)
      (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
      0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < δ →
      (∃ F : ℂ × ℂ, IsFormFactorPair e m p' p
        (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F) ∧
      ∀ F : ℂ × ℂ, IsFormFactorPair e m p' p
          (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0) F →
        ‖F.1 - 1‖ < η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
