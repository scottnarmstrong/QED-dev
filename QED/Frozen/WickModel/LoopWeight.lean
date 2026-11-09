/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ClosedLoop
public import QED.Frozen.WickModel.FermionFlavor
public import QED.Frozen.WickModel.ParamsLoopCoeff
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
/-- (X₇) The regulator weight of the flavored contraction `(C, φ)` (decision D-22): the product
over the closed fermion loops (X₆) of the coefficient `c_f` of the loop's flavor. When `σ`
preserves `φ` (X₄), the flavor is constant on a loop and is read off its representative field
`q.out`; only such `φ` are meaningful, and only they enter (X₂₆). Electron loops have coefficient
`c₀ = 1`. -/
noncomputable def loopWeight (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (φ : Flavoring κ) : ℝ :=
  ∏ q : ClosedLoop C, P.loopCoeff (fermionFlavor φ q.1.out)

end QED.WickModel

end
