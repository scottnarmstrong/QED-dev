/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.Contraction
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

open scoped Classical in
/-- (V₁₄) The external momentum flowing into vertex `v`: the incoming electron momentum `p` at
the vertex whose `Ψ` is contracted with `Ψ̄(y)`, the incoming photon momentum `p' - p` at the
vertex whose photon field is contracted with `A(z)`, and minus the outgoing electron momentum
`p'` at the vertex whose `Ψ̄` is contracted with `Ψ(x)` (rules 1, 2, 5, p. 348; (62.39)). -/
noncomputable def externalMomentum {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ)
    (p' p : Fin 4 → ℝ) (v : Fin N) : Fin 4 → ℝ :=
  (if ∃ t : FermionVertex κ, t.1 = v ∧ C.1.1 (some t) = none then p else 0)
    + (if ∃ a : PhotonSlot κ, a.1 = v ∧ C.1.2 none = some a then p' - p else 0)
    - (if ∃ t : FermionVertex κ, t.1 = v ∧ C.1.1 none = some t then p' else 0)

end QED.Wick

end
