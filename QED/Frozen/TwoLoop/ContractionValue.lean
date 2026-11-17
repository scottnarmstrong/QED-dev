/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.RegulatedAmplitude
public import QED.Frozen.TwoLoop.LineMomentum
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Complex

namespace QED.WickModel

/-- (T₁₀) **The value of a contraction with any number of loops** (decisions D-19, D-37.5): with
`L = loopCount C` (T₂) loop momenta routed by (T₄), the regulated amplitude (T₈), times the loop
measure `(2π)^{-4L}`, integrated with the joint energy-first prescription (T₉) at the fixed `ε`.
For a tree (`L = 0`) this is the regulated amplitude itself; for one loop it is (X₂₇) (T₁₃); for
two loops it is `∫_{ℝ⁶} d³ℓ⃗₁ d³ℓ⃗₂ (∫_{ℝ²} dℓ₁⁰ dℓ₂⁰ (2π)⁻⁸ ⋯)`. As in (T₉), a stage that is
not integrable contributes `0`: the energy integral is `0` at each `ℓ⃗` where it does not converge
absolutely, and the value is `0` when the resulting spatial integrand is not integrable. Only
connected contractions with attached externals and at most two loops, and `ε > 0`, are
source-facing. -/
noncomputable def contractionValue₂ (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  QED.TwoLoop.jointEnergyFirstIntegral (loopCount C) fun ℓ =>
    (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ

end QED.WickModel

end
