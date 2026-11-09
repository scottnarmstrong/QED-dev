/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Line
public import QED.Frozen.WickModel.FermionLineTail
public import QED.Frozen.WickModel.PhotonLineHead
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

/-- (X₁₃) The end vertices `(tail, head)` of an internal line; momentum flows from tail to head.
A fermion line runs from the vertex of its `Ψ̄` to the vertex of its `Ψ` (the propagator
`⟨Ψ(x) Ψ̄(y)⟩` carries momentum from `y` to `x`, (58.19)); a photon line runs from its
smaller-key field to the other. -/
def Line.ends {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ} :
    Line C → Fin N × Fin N
  | .inl f => (f.tail.1, f.1.1)
  | .inr g => (g.1.1, g.head.1)

end QED.WickModel

end
