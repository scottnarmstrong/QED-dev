/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LineEnds
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

/-- (X₁₄) Vertices `u` and `w` are joined by an internal line of `C` outside the set `S`. -/
def Joined {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (S : Set (Line C)) (u w : Fin N) : Prop :=
  ∃ f : Line C, f ∉ S ∧ (f.ends = (u, w) ∨ f.ends = (w, u))

end QED.WickModel

end
