/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.ContractionAmplitude
public import QED.Frozen.WickModel.Preserves
public import QED.Frozen.WickModel.LoopWeight
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

open scoped Classical in
/-- (T₈) The Pauli–Villars regulated amplitude of a contraction for the line momenta `k`
(decision D-22): the sum, over the flavorings `φ` that `σ` preserves (X₄), of the regulator weight
(X₇) times the amplitude (T₇). As in (X₂₆), the flavors of one contraction are summed inside one
loop integrand. With `k = lineMomentum C pOut pIn kIn ℓ` it is (X₂₆). -/
noncomputable def regulatedAmplitude₂ (P : Params) {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) : ℂ :=
  ∑ φ ∈ (Finset.univ : Finset (Flavoring κ)).filter (Preserves C),
    (loopWeight P C φ : ℂ) * contractionAmplitude₂ P C φ pIn kIn k αOut βIn μ

end QED.WickModel

end
