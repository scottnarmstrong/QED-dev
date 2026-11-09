/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.Contraction
public import QED.Frozen.Wick.PhotonKey
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₉) The internal photon lines of a contraction, indexed by the photon field with the smaller
key among the two contracted vertex fields. -/
abbrev PhotonLine {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ) : Type :=
  {a : PhotonSlot κ // ∃ b, C.1.2 (some a) = some b ∧ photonKey a < photonKey b}

end QED.Wick

end
