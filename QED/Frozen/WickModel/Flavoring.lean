/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.FermionVertex
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

/-- (X₁) A flavoring of a vertex sequence `κ` of packet 5's kinds (V₀): the flavor of the fermion
fields `Ψ̄ Ψ` of each vertex that has them (decision D-22). The interaction contains a gauge
vertex `e Ψ̄_f A̸ Ψ_f` for each flavor `f`, so a gauge vertex may have any flavor; the
counterterms act on the electron, flavor `0`. A sequence of flavored vertex kinds is exactly a
pair `(κ, φ)`. -/
abbrev Flavoring {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  {φ : Wick.FermionVertex κ → Fin 3 // ∀ t, κ t.1 ≠ .gauge → φ t = 0}

end QED.WickModel

end
