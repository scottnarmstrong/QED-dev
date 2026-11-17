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
/-- (T₃) The loop momentum carried by a chord: the chords are numbered `0, 1, …` by increasing
label, and the chord numbered `r` carries `ℓ r` (so, for `L ≥ 1`, the loop line (X₂₁) carries
`ℓ 0`). A chord numbered `r ≥ L` carries `0`; in the value (T₁₀) `L` is the number of chords, so
this does not occur there. The value on a line that is not a chord is not used. -/
noncomputable def chordMomentum {nf nA N L : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction nf nA κ} (ℓ : Fin L → Fin 4 → ℝ) (f : Line C) : Fin 4 → ℝ :=
  if h : (Finset.univ.filter fun g : Line C => IsChord g ∧ g.label < f.label).card < L then
    ℓ ⟨_, h⟩
  else 0

end QED.WickModel

end
