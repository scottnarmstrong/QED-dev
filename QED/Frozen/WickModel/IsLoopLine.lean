/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsBridge
public import QED.Frozen.WickModel.LineLabel
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

/-- (X₂₁) The loop line: the internal line that is not a bridge and has the smallest label among
the lines that are not bridges (decision D-19). In a connected contraction with one loop the
lines that are not bridges form the unique cycle, and this is its lowest-labelled line; a tree
has no loop line. -/
def IsLoopLine {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (f : Line C) : Prop :=
  ¬ IsBridge f ∧ ∀ g : Line C, ¬ IsBridge g → f.label ≤ g.label

end QED.WickModel

end
