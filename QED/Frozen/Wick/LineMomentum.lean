/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.Joined
public import QED.Frozen.Wick.ExternalMomentum
public import QED.Frozen.Wick.IsLoopLine
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace QED.Wick

open scoped Classical in
/-- (V₁₆) **Canonical one-loop routing** (rule 8, p. 349; decision D-19). The loop line carries the
loop momentum `ℓ`. Any other line `f` carries the total momentum injected into the side of its
tail, the set of vertices reachable from its tail without using `f` or the loop line; the loop
line injects `ℓ` at its head and removes it at its tail. For a 1PI one-loop contraction this is
the unique momentum assignment that is conserved at every vertex and gives the loop line `ℓ`;
on other contractions the value is not meaningful. -/
noncomputable def lineMomentum {N : ℕ} {κ : Fin N → VertexKind} (C : Contraction κ)
    (p' p ℓ : Fin 4 → ℝ) (f : Line C) : Fin 4 → ℝ :=
  if IsLoopLine f then ℓ else
    ∑ v ∈ Finset.univ.filter (fun v => Relation.ReflTransGen
        (Joined C {g | g = f ∨ IsLoopLine g}) f.ends.1 v),
      (externalMomentum C p' p v + ∑ g ∈ Finset.univ.filter (fun g : Line C => IsLoopLine g),
        ((if g.ends.2 = v then ℓ else 0) - (if g.ends.1 = v then ℓ else 0)))

end QED.Wick

end
