/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.LineEnds
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₁₂) Vertices `u` and `w` are joined by an internal line of `C` outside the set `S`. -/
def Joined {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ) (S : Set (Line C))
    (u w : Fin N) : Prop :=
  ∃ f : Line C, f ∉ S ∧ (f.ends = (u, w) ∨ f.ends = (w, u))

end QED.Wick

end
