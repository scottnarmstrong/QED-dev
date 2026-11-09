/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.PhotonSlot
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₈) A numbering of photon fields, used only to orient photon lines and to order lines. -/
def photonKey {N : ℕ} {κ : Fin N → VertexKind} (a : PhotonSlot κ) : ℕ :=
  2 * a.1.val + a.2.val

end QED.Wick

end
