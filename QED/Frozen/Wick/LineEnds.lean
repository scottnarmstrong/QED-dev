/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.Line
public import Mathlib.Data.Option.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₁₁) The end vertices `(tail, head)` of an internal line; momentum flows from tail to head.
A fermion line runs from the vertex of its `Ψ̄` to the vertex of its `Ψ` (the propagator
`⟨Ψ(x) Ψ̄(y)⟩` carries momentum from `y` to `x`, (58.19)); a photon line runs from its
smaller-key field to the other. -/
def Line.ends {N : ℕ} {κ : Fin N → VertexKind} {C : Contraction κ} : Line C → Fin N × Fin N
  | .inl f => (((C.1.1 (some f.1)).get (Option.ne_none_iff_isSome.mp f.2)).1, f.1.1)
  | .inr g => (g.1.1, ((C.1.2 (some g.1)).get
      (Option.isSome_iff_exists.mpr (g.2.imp fun _ h => h.1))).1)

end QED.Wick

end
