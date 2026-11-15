-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Frozen.OneLoop.VertexOneLoop
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import QED.Provider.OneLoop.OneLoopAnomalyCodata2022

@[expose] public section

namespace QED.OneLoop

/-- (Q₄) **The one-loop contribution to the electron anomaly for the CODATA 2022 value of `α`
(Phase 3 theorem goal; decision D-34).** If `α = e²/(4π)` (63.22) has `α⁻¹` in the CODATA 2022
one-standard-uncertainty interval `[137.035999156, 137.035999198]`, from
`α⁻¹ = 137.035999177(21)` (a sourced external input; a one-sigma interval does not guarantee that
the true value lies inside, so the conclusion is conditional on it), then the one-loop value
`e²/(8π²) = α/(2π)` of the anomaly, which is the limit of `F₂` in (I) and of `g/2 - 1` in the
headline theorem (H), lies in `[0.0011614097319, 0.0011614097323]`. -/
theorem oneLoopAnomaly_mem_codata2022 (e : ℝ)
    (hα : 4 * Real.pi / e ^ 2 ∈ Set.Icc (137.035999156 : ℝ) 137.035999198) :
    e ^ 2 / (8 * Real.pi ^ 2) ∈ Set.Icc (0.0011614097319 : ℝ) 0.0011614097323 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
