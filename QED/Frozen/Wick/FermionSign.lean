/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.Contraction
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₆) The fermionic (Grassmann) sign of a contraction. The fields are ordered as
`Ψ(x) Ψ̄(y) ∏_t (Ψ̄_t Ψ_t)`, from the correlator and the bilinears `Ψ̄ ⋯ Ψ` of the
Lagrangian. Rewriting each `Ψ̄_t Ψ_t` as `-Ψ_t Ψ̄_t` gives `(-1)^{#vertices with Ψ̄Ψ}` times
`∏_i Ψ_i Ψ̄_i`, whose complete contraction with pairing `σ` carries `sign σ`. -/
def fermionSign {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ) : ℤ :=
  (-1) ^ Fintype.card (FermionVertex κ) * (Equiv.Perm.sign C.1.1 : ℤ)

end QED.Wick

end
