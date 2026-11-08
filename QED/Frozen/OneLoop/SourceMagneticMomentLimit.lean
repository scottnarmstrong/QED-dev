-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.SourceMagneticMoment
public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import QED.Provider.OneLoop.SourceMagneticMomentLimit
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section

open Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.OneLoop

/-- (W₄) **The two magnetic moments agree (packet 4b theorem goal; obligation O-24).** For
`m > 0`, regulators `m_γ, Λ > 0`, every counterterm `Z₁`, and every real smooth compactly
supported profile `φ` that is not identically zero on `[0, ∞)`: for every packet width `λ > 0`
the position integral of the source definition (W₃) converges absolutely, and as the packet
becomes sharply peaked at rest (`λ → 0⁺`, ruling D-17) the source magnetic moment tends to the
response magnetic moment (R₀). -/
theorem integrable_and_tendsto_sourceMagneticMoment (e Z₁ m mγ Λ : ℝ) (hm : 0 < m)
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∃ t, 0 ≤ t ∧ φ t ≠ 0) :
    (∀ lam > 0, Integrable fun x : Fin 3 → ℝ =>
      (x 0 : ℂ) * packetCurrentDensity e Z₁ m mγ Λ hm hmγ hΛ φ lam x) ∧
    ∀ μ : ℝ, IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ →
      Tendsto (fun lam => sourceMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ φ lam) (𝓝[>] 0)
        (𝓝 (μ : ℂ)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
