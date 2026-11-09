/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ExternalsAttached
public import QED.Frozen.WickModel.VerticesConnected
public import QED.Frozen.WickModel.IsBridge
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

/-- (X₁₈) **One-particle irreducibility** (section 14; (62.4), (62.27), (62.39)): every external
field is attached to a vertex (so the external propagators are amputated), the vertices are
connected by internal lines, and no internal line is a bridge. -/
def IsOnePI {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : Prop :=
  ExternalsAttached C ∧ VerticesConnected C ∧ ∀ f : Line C, ¬ IsBridge f

end QED.WickModel

end
