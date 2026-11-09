/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Joined
public import QED.Frozen.WickModel.ExternalMomentum
public import QED.Frozen.WickModel.IsLoopLine
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
/-- (X₂₂) **Canonical one-loop routing** (rule 8, p. 349; decision D-19). The loop line carries the
loop momentum `ℓ`. Any other line `f` carries the total momentum injected into the side of its
tail, the set of vertices reachable from its tail without using `f` or the loop line; the loop
line injects `ℓ` at its head and removes it at its tail. For a connected contraction with at most
one loop whose external momenta sum to zero, deleting the loop line leaves a spanning tree, and
this is the unique momentum assignment that is conserved at every vertex and gives the loop line
`ℓ`; in a tree it is the unique conserved assignment. On other contractions the value is not
meaningful. -/
noncomputable def lineMomentum {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (f : Line C) : Fin 4 → ℝ :=
  if IsLoopLine f then ℓ else
    ∑ v ∈ Finset.univ.filter (fun v => Relation.ReflTransGen
        (Joined C {g | g = f ∨ IsLoopLine g}) f.ends.1 v),
      (externalMomentum C pOut pIn kIn v
        + ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
          ((if g.ends.2 = v then ℓ else 0) - (if g.ends.1 = v then ℓ else 0)))

end QED.WickModel

end
