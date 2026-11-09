/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Contraction
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

/-- (X₁₆) No external field is contracted with an external field: every external `Ψ(xᵢ)`,
`Ψ̄(yⱼ)` and `A(zⱼ)` is contracted with a vertex field, so its propagator is an external leg. -/
def ExternalsAttached {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) :
    Prop :=
  (∀ i j : Fin nf, C.1.1 (.inl i) ≠ .inl j) ∧ ∀ i j : Fin nA, C.1.2 (.inl i) ≠ .inl j

end QED.WickModel

end
