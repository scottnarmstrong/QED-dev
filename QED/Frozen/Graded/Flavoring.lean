/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.FermionVertex
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace QED.Graded

/-- (G₁) **A flavouring of a vertex sequence `κ`** (ruling S2′, D-55 revised; successor of (F₁)
without its restriction): the flavour of the fermion fields `Ψ̄ Ψ` of each vertex that has them.
Every vertex with fermion fields, counterterm vertices included, may have any flavour, since the
counterterm Lagrangian has a term for every flavour (B4 check: (F₁) forces counterterm vertices onto
the open line, so closed loops of other flavours carried no counterterms). -/
abbrev Flavoring (F : Type) {N : ℕ} (κ : Fin N → Wick.VertexKind) : Type :=
  Wick.FermionVertex κ → F

end QED.Graded

end
