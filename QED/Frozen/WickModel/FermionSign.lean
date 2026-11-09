/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Contraction
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

/-- (X₅) The fermionic (Grassmann) sign of a contraction. The fields are ordered as
`Ψ(x₁) Ψ̄(y₁) ⋯ Ψ(x_nf) Ψ̄(y_nf) ∏_t (Ψ̄_t Ψ_t)`, from the correlator and the bilinears `Ψ̄ ⋯ Ψ` of
the Lagrangian. Rewriting each `Ψ̄_t Ψ_t` as `-Ψ_t Ψ̄_t` gives `(-1)^{#vertices with Ψ̄Ψ}` times
the product of the Grassmann-even pairs `Ψ_a Ψ̄_a` over all fermion slots `a` (external `xᵢ ↔ yᵢ`
and vertex `t ↔ t`). Its complete contraction with pairing `σ` carries `sign σ` relative to the
reference pairing `a ↔ a`. A closed loop of `k` vertices thus has sign `(-1)^k (-1)^{k-1} = -1`. -/
def fermionSign {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : ℤ :=
  (-1) ^ Fintype.card (Wick.FermionVertex κ) * (Equiv.Perm.sign C.1.1 : ℤ)

end QED.WickModel

end
