/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Flavoring
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

/-- (X₂) The flavor of a fermion field under the flavoring `φ`. On either side, `inl i` is an
external field (the `Ψ(xᵢ)` on the `Ψ` side, the `Ψ̄(yᵢ)` on the `Ψ̄` side), an electron of
flavor `0`, and `inr t` is the field of vertex `t`, of flavor `φ t`. -/
def fermionFlavor {nf N : ℕ} {κ : Fin N → Wick.VertexKind} (φ : Flavoring κ) :
    Fin nf ⊕ Wick.FermionVertex κ → Fin 3
  | .inl _ => 0
  | .inr t => φ.1 t

end QED.WickModel

end
