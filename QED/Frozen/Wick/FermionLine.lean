/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.Contraction
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

/-- (V₇) The internal fermion lines of a contraction, indexed by the vertex `t` whose `Ψ` is
contracted with the `Ψ̄` of a vertex (the propagator `⟨Ψ_t Ψ̄_s⟩`). -/
abbrev FermionLine {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ) : Type :=
  {t : FermionVertex κ // C.1.1 (some t) ≠ none}

end QED.Wick

end
