/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Joined
public import QED.Frozen.WickModel.LineLabel
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

/-- (T₁) **The loop lines (chords)** of a contraction (obligation O2-5, extending decision
D-19.3): the internal line `f` is a chord when its two ends are joined by a path of internal lines
whose labels (X₂₀) are all larger than `f`'s. Labels are distinct, so the lines that are not
chords form the spanning forest of maximal total label, and the number of chords is the number of
independent loops. A self-loop is a chord. The chords are those of O2-5's greedy rule: the
lowest-labelled chord is the lowest-labelled line that is not a bridge (the loop line (X₂₁)), and
the next is the lowest-labelled line that is not a bridge once the first is deleted. With at most
one loop, `IsChord` is (X₂₁). -/
def IsChord {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (f : Line C) : Prop :=
  Relation.ReflTransGen (Joined C {g | g.label ≤ f.label}) f.ends.1 f.ends.2

end QED.WickModel

end
