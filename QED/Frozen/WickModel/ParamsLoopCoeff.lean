/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.Params
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

/-- (X₀″) The coefficient `c_f` of a closed fermion loop of flavor `f` (decision D-22): `c₀ = 1`
for the electron. The Pauli–Villars conditions `∑ c_f = 0` and `∑ c_f M_f² = 0` are hypotheses
of later theorems. -/
def Params.loopCoeff (P : Params) : Fin 3 → ℝ :=
  ![1, P.c₁, P.c₂]

end QED.WickModel

end
