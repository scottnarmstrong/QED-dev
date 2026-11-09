/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.FermionVertex
public import QED.Frozen.Wick.PhotonSlot
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₅) The Wick contractions of the fields of the three-point function `⟨Ψ(x) Ψ̄(y) A(z)⟩` with
interaction vertices `κ` ((58.17)–(58.18)). The first component pairs each `Ψ` field with a
`Ψ̄` field: `none` is the external `Ψ(x)` on the `Ψ` side and the external `Ψ̄(y)` on the `Ψ̄`
side, and `some t` is the field of vertex `t`; the value `c.1 i = j` means that the `Ψ` at `i`
is contracted with the `Ψ̄` at `j`. The second component is a fixed-point-free involution
pairing the photon fields, `none` being the external `A(z)`. -/
abbrev Contraction {N : ℕ} (κ : Fin N → VertexKind) : Type :=
  {c : Equiv.Perm (Option (FermionVertex κ)) × Equiv.Perm (Option (PhotonSlot κ)) //
    ∀ a, c.2 (c.2 a) = a ∧ c.2 a ≠ a}

end QED.Wick

end
