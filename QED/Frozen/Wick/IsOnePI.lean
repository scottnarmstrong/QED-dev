/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.Joined
public import Mathlib.Logic.Relation
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₁₃) **One-particle irreducibility** (section 14; the vertex function (62.39)). The external
`Ψ(x)` and `Ψ̄(y)` are contracted with vertex fields (so their propagators are external and
amputated; the external `A(z)` is always contracted with a vertex field), and the vertices stay
connected by internal lines after deleting any one internal line (`g = some f`) or none
(`g = none`). -/
def IsOnePI {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ) : Prop :=
  C.1.1 none ≠ none ∧
    ∀ g : Option (Line C), ∀ u w : Fin N, Relation.ReflTransGen (Joined C {f | g = some f}) u w

end QED.Wick

end
