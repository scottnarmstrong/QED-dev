/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.LineMomentum
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

open scoped Classical in
/-- (V₁₈) The momentum flowing into the vertex of the photon field `a` through `a`: `p' - p` if
`a` is contracted with `A(z)`, and otherwise the momentum of its photon line, counted positively
at the line's head and negatively at its tail. -/
noncomputable def photonMomentum {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ)
    (p' p ℓ : Fin 4 → ℝ) (a : PhotonSlot κ) : Fin 4 → ℝ :=
  (if C.1.2 none = some a then p' - p else 0) +
    ∑ g : PhotonLine C, ((if C.1.2 (some g.1) = some a then lineMomentum C p' p ℓ (.inr g) else 0)
      - (if g.1 = a then lineMomentum C p' p ℓ (.inr g) else 0))

end QED.Wick

end
