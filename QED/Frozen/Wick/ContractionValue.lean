/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.ContractionAmplitude
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

open scoped Classical in
/-- (V₂₁) The value of a contraction. A contraction without internal lines (a single vertex) has
the value of its amplitude. Otherwise the amplitude, times the loop measure `(2π)⁻⁴`, is integrated
over the loop momentum with the energy-first prescription M1 at the fixed `ε` (decision D-19).
Only 1PI contractions at order `≤ e³` and `ε > 0` are source-facing; each such contraction has
at most one loop. -/
noncomputable def contractionValue (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) {N : ℕ} {κ : Fin N → VertexKind}
    (C : Contraction κ) (p' p : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  if IsEmpty (Line C) then contractionAmplitude e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p 0 μ
  else Matrix.of fun i j => QED.OneLoop.energyFirstIntegral fun ℓ =>
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * contractionAmplitude e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p ℓ μ i j

end QED.Wick

end
