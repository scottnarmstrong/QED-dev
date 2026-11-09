/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.FermionVertex
public import QED.Frozen.Wick.PhotonSlot
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Complex

namespace QED.WickModel

/-- (X₃) The Wick contractions of the fields of the correlator
`⟨Ψ(x₁) Ψ̄(y₁) ⋯ Ψ(x_nf) Ψ̄(y_nf) A(z₁) ⋯ A(z_nA)⟩` with interaction vertices `κ`
((58.17)–(58.18); decision D-23.2), with the fermion and photon fields (V₃), (V₄) of packet 5.
The first component `σ` pairs each `Ψ` field with a `Ψ̄` field: on the `Ψ` side `inl i` is the
external `Ψ(xᵢ)`, on the `Ψ̄` side `inl i` is the external `Ψ̄(yᵢ)`, and `inr t` is the field of
vertex `t`; the value `σ a = b` means that the `Ψ` at `a` is contracted with the `Ψ̄` at `b`.
The second component is a fixed-point-free involution pairing the photon fields, `inl j` being
the external `A(zⱼ)`. Flavors are not part of a contraction: they are summed in (X₂₆). -/
abbrev Contraction (nf nA : ℕ) {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  {c : Equiv.Perm (Fin nf ⊕ Wick.FermionVertex κ) × Equiv.Perm (Fin nA ⊕ Wick.PhotonSlot κ) //
    ∀ b, c.2 (c.2 b) = b ∧ c.2 b ≠ b}

end QED.WickModel

end
