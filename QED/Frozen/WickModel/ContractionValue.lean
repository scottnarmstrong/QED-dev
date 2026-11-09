/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.RegulatedAmplitude
public import QED.Frozen.WickModel.IsLoopLine
public import QED.Frozen.OneLoop.EnergyFirstIntegral
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

open scoped Classical in
/-- (X₂₇) The value of a contraction. A contraction without a loop line (when connected, a tree)
has the value of its regulated amplitude (X₂₆), which then does not depend on `ℓ`. Otherwise
the regulated amplitude, times the loop measure `(2π)⁻⁴`, is integrated over the loop momentum
with the energy-first prescription M1 at the fixed `ε` (decision D-19). Like the frozen
`energyFirstIntegral` (D), the value is `0` when the integrand is not integrable; a closed fermion
loop with at most four vertices needs the Pauli–Villars conditions `∑ c_f = 0` and
`∑ c_f M_f² = 0` to be integrable.
Only connected contractions with attached externals and at most one loop, and `ε > 0`, are
source-facing. -/
noncomputable def contractionValue (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  if ∃ f : Line C, IsLoopLine f then
    QED.OneLoop.energyFirstIntegral fun ℓ =>
      (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ
  else regulatedAmplitude P C pOut pIn kIn 0 αOut βIn μ

end QED.WickModel

end
