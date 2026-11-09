/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.Line
public import QED.Frozen.Wick.PhotonKey
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₁₅) The loop line: the internal line with the smallest label, fermion lines (by the vertex of
their `Ψ`) before photon lines (by key) (decision D-19). In a 1PI contraction every internal line
lies on a cycle, so for a 1PI one-loop contraction this is the lowest-labelled line of the
unique cycle. -/
def IsLoopLine {N : ℕ} {κ : Fin N → VertexKind} {C : Contraction κ} (f : Line C) : Prop :=
  ∀ g : Line C, (match f with | .inl f => f.1.1.val | .inr f => N + photonKey f.1) ≤
    (match g with | .inl g => g.1.1.val | .inr g => N + photonKey g.1)

end QED.Wick

end
