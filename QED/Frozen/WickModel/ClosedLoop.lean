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

/-- (X₆) The closed fermion loops of a contraction: the cycles of `σ` (the classes of
`Equiv.Perm.SameCycle σ`, fixed points included) that contain no external slot. Following `σ`
from a vertex `Ψ_t` to the `Ψ̄_s` it is contracted with, then to `Ψ_s`, and so on, traverses a
fermion line against its arrow; the line is closed when it never reaches an external field. -/
abbrev ClosedLoop {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : Type :=
  {q : Quotient (Equiv.Perm.SameCycle.setoid C.1.1) //
    ∀ i : Fin nf, Quotient.mk _ (Sum.inl i) ≠ q}

end QED.WickModel

end
