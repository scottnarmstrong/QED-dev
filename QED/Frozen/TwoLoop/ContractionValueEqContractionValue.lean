-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.ContractionValue
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.ContractionValue
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
public import QED.Provider.TwoLoop.ContractionValueEqContractionValue

@[expose] public section

open Complex

namespace QED.WickModel

/-- (T₁₃) **One-loop contractions have their packet 6a value** (obligation O2-9). For all
parameters and every contraction with at most one loop (T₂), connected or not, the value (T₁₀) is
the frozen value (X₂₇): the chord is the loop line (X₂₁), the routing (T₄) is (X₂₂), and the joint
prescription is (D) (T₁₂), or the evaluation at the empty family for a forest. -/
theorem contractionValue₂_eq_contractionValue (P : Params) {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (hC : loopCount C ≤ 1)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue₂ P C pOut pIn kIn αOut βIn μ =
      contractionValue P C pOut pIn kIn αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
