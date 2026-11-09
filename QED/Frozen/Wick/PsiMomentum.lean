/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.LineMomentum
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₁₇) The momentum flowing into vertex `t` through its `Ψ` field. -/
noncomputable def psiMomentum {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ)
    (p' p ℓ : Fin 4 → ℝ) (t : FermionVertex κ) : Fin 4 → ℝ :=
  if h : C.1.1 (some t) = none then p else lineMomentum C p' p ℓ (.inl ⟨t, h⟩)

end QED.Wick

end
