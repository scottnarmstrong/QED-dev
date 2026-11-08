/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.OneParticleMomentum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open MeasureTheory

namespace QED.OneLoop

/-- (W₂) The squared norm `⟨e|e⟩ = ∫ d̃k f(k⃗)²` of the wave packet (W₁), with the one-particle
normalization (41.5). -/
noncomputable def packetNormSq (m : ℝ) (φ : ℝ → ℝ) (lam : ℝ) : ℝ :=
  ∫ k : Fin 3 → ℝ, φ ((∑ j, k j ^ 2) / lam ^ 2) ^ 2
    / ((2 * Real.pi) ^ 3 * (2 * oneParticleMomentum m k 0))

end QED.OneLoop

end
