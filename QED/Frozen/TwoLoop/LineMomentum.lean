/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.ChordMomentum
public import QED.Frozen.WickModel.Joined
public import QED.Frozen.WickModel.ExternalMomentum
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
/-- (T₄) **Canonical routing with several loop momenta** (rule 8, p. 349; obligation O2-5). Each
chord (T₁) carries its loop momentum (T₃). Any other line `f` carries the total momentum injected
into the side of its tail, the set of vertices reachable from its tail without using `f` or any
chord; each chord injects its momentum at its head and removes it at its tail. For a contraction
whose external momenta sum to zero on each connected component, deleting the chords leaves a
spanning forest, and this is the unique momentum assignment that is conserved at every vertex and
gives each chord its loop momentum (CK-R (11)–(16)). With at most one loop and `L ≥ 1` it is
(X₂₂) at `ℓ 0`. -/
noncomputable def lineMomentum₂ {nf nA N L : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin L → Fin 4 → ℝ) (f : Line C) : Fin 4 → ℝ :=
  if IsChord f then chordMomentum ℓ f else
    ∑ v ∈ Finset.univ.filter (fun v => Relation.ReflTransGen
        (Joined C {g | g = f ∨ IsChord g}) f.ends.1 v),
      (externalMomentum C pOut pIn kIn v
        + ∑ g ∈ Finset.univ.filter (fun g : Line C => IsChord g),
          ((if g.ends.2 = v then chordMomentum ℓ g else 0)
            - (if g.ends.1 = v then chordMomentum ℓ g else 0)))

end QED.WickModel

end
