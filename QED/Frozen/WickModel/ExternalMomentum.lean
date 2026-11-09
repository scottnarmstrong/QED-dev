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

open scoped Classical in
/-- (X₁₉) The external momentum flowing into vertex `v`: the incoming momentum `pIn i` of each
external `Ψ̄(yᵢ)` contracted with the vertex's `Ψ`, the incoming photon momentum `kIn j` of each
external `A(zⱼ)` contracted with one of its photon fields, minus the outgoing momentum `pOut i`
of each external `Ψ(xᵢ)` contracted with its `Ψ̄` (rules 1, 2, 5, pp. 348–349). Momentum
conservation is a hypothesis of later theorems. -/
noncomputable def externalMomentum {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (v : Fin N) : Fin 4 → ℝ :=
  (∑ i, if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inr t) = .inl i then pIn i else 0)
    + (∑ j, if ∃ a : Wick.PhotonSlot κ, a.1 = v ∧ C.1.2 (.inl j) = .inr a then kIn j else 0)
    - (∑ i, if ∃ t : Wick.FermionVertex κ, t.1 = v ∧ C.1.1 (.inl i) = .inr t then pOut i else 0)

end QED.WickModel

end
