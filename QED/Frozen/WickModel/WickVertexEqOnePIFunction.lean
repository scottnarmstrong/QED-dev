-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.Wick.WickVertex
public import QED.Provider.WickModel.WickVertexEqOnePIFunction
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

/-- (Y₁) **Packet 5 is the special case (packet 6a theorem goal; decision D-23.2).** For all
parameters, packet 5's Wick vertex (its (V₂₂)) is the 1PI function (X₂₈) with one external
fermion pair and one external photon, at order `≤ 3`: outgoing momentum `p'`, incoming momentum
`p`, incoming photon momentum `p' - p`, and the spinor indices `i`, `j` and Lorentz index `μ`.
In every 1PI contraction of this order each fermion vertex lies on the open fermion line from
`Ψ̄(y)` to `Ψ(x)`, so the only flavoring that `σ` preserves is `φ = 0`, with weight `1`: the
regulator fermions do not contribute, and the result holds for all `M₁, M₂, c₁, c₂`. -/
theorem wickVertex_eq_onePIFunction (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    QED.Wick.wickVertex P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m P.mγ P.Λ P.ε p' p μ i j =
      onePIFunction P 1 1 3 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.wickVertex_eq_onePIFunction
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
