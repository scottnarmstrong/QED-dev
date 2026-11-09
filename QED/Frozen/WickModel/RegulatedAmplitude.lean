/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.ContractionAmplitude
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
/-- (X₂₆) **The Pauli–Villars regulated amplitude** of a contraction at loop momentum `ℓ`
(decision D-22): the sum, over the flavorings `φ` that `σ` preserves (X₄), of the regulator
weight (X₇) times the amplitude (X₂₅). This is the same Wick sum, regrouped. The interaction has
a gauge vertex for each flavor, so a term of `exp(i ∫ L₁)` is a sequence of flavored kinds, that
is a pair `(κ, φ)`, and its contractions are the `C` that preserve `φ`; each flavored kind
sequence with a flavor-preserving contraction corresponds to exactly one `(κ, C, φ)`. The sign,
the lines, the routing and the 1PI and connectivity predicates do not depend on `φ`. Grouping
the flavors of one contraction puts `∑_f c_f (loop of mass M_f)` inside one loop integrand, which
is how the regulator acts: a single flavor's closed loop with at most four vertices (for example
the vacuum polarization) is not integrable. -/
noncomputable def regulatedAmplitude (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ φ ∈ (Finset.univ : Finset (Flavoring κ)).filter (Preserves C),
    (loopWeight P C φ : ℂ) * contractionAmplitude P C φ pOut pIn kIn ℓ αOut βIn μ

end QED.WickModel

end
