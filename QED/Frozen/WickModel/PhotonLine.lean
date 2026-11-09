/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Contraction
public import QED.Frozen.Wick.PhotonKey
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

/-- (X₁₀) The internal photon lines of a contraction, indexed by the photon field with the smaller
key (packet 5's (V₈)) among the two contracted vertex fields. -/
abbrev PhotonLine {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) : Type :=
  {a : Wick.PhotonSlot κ // ∃ b, C.1.2 (.inr a) = .inr b ∧ Wick.photonKey a < Wick.photonKey b}

end QED.WickModel

end
