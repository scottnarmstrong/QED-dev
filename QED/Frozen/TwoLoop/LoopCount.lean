/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.IsChord
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
/-- (T₂) The number of independent loops of a contraction: the number of chords (T₁). For a
contraction with at least one vertex, connected vertices (X₁₇) and attached externals (X₁₆) it is
given by `2 · loopCount C = V₃ - 2 nf - nA + 2`, with `V₃` the number of `gauge` and `gaugeCt`
vertices; since
`V₃ ≤ K` for a term of total order at most `K`, such a term has at most one loop when
`K ≤ 2 nf + nA + 1` and at most two when `K ≤ 2 nf + nA + 3`. -/
noncomputable def loopCount {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) : ℕ :=
  (Finset.univ.filter fun f : Line C => IsChord f).card

end QED.WickModel

end
