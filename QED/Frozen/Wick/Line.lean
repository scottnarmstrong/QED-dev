/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.FermionLine
public import QED.Frozen.Wick.PhotonLine
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₁₀) The internal lines of a contraction. -/
abbrev Line {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ) : Type :=
  FermionLine C ⊕ PhotonLine C

end QED.Wick

end
