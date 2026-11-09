/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Line
public import QED.Frozen.Wick.PhotonKey
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

/-- (X₂₀) The label of an internal line, used to choose the loop line: fermion lines (by the vertex
of their `Ψ`) before photon lines (by key). Distinct lines have distinct labels. -/
def Line.label {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ} :
    Line C → ℕ
  | .inl f => f.1.1.val
  | .inr g => N + Wick.photonKey g.1

end QED.WickModel

end
