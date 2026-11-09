-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.WickVertex
public import QED.Frozen.OneLoop.VertexIntegrand
public import QED.Provider.Wick.WickVertexEq
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

open Complex

namespace QED.Wick

/-- (W₁) **The Wick derivation of the vertex (packet 5 theorem goal; obligations O-1, O-2).** For
all parameters, the order-`e³` 1PI part of the Wick expansion is the counterterm-corrected tree
vertex `i Z₁ e γ^μ` with `Z₁ = 1 + δ₁`, plus the regulated one-loop diagram (62.40) at the same
`ε`: the energy-first integral of the frozen integrand (C), with coefficient one, the
fermion-line ordering `γ^ρ S̃ γ^μ S̃ γ^ν` and no closed-loop sign. The two-point counterterms
`δ₂, δ_m, δ₃` do not contribute. -/
theorem wickVertex_eq (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    wickVertex e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p μ =
      (I * (((1 + δ₁) * e : ℝ) : ℂ)) • Dirac.gamma μ +
        Matrix.of fun i j => QED.OneLoop.energyFirstIntegral fun ℓ =>
          QED.OneLoop.vertexIntegrand e m mγ Λ ε p' p μ ℓ i j :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Wick.wickVertex_eq
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Wick

end
-- FROZEN_ANCHOR_SUFFIX_END
