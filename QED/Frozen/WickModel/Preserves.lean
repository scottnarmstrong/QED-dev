/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Contraction
public import QED.Frozen.WickModel.FermionFlavor
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

/-- (X₄) The contraction `C` is a contraction of the flavored fields of `(κ, φ)`: `σ` preserves
flavor, since the free propagator `⟨Ψ_f Ψ̄_g⟩` vanishes unless `f = g` (decision D-22). -/
def Preserves {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (φ : Flavoring κ) : Prop :=
  ∀ a, fermionFlavor φ (C.1.1 a) = fermionFlavor φ a

end QED.WickModel

end
