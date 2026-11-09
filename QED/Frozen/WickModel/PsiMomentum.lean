/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LineMomentum
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

/-- (X₂₃) The momentum flowing into vertex `t` through its `Ψ` field: `pIn i` if it is contracted
with the external `Ψ̄(yᵢ)`, and otherwise the momentum of its internal fermion line. -/
noncomputable def psiMomentum {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (t : Wick.FermionVertex κ) : Fin 4 → ℝ :=
  match h : C.1.1 (.inr t) with
  | .inl i => pIn i
  | .inr _ => lineMomentum C pOut pIn kIn ℓ (.inl ⟨t, by simp [h]⟩)

end QED.WickModel

end
