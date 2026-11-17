-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Basic.Complex.Basic
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
public import QED.Provider.TwoLoop.JointEnergyFirstIntegralOne

@[expose] public section

open Complex

namespace QED.TwoLoop

/-- (T₁₂) **The joint prescription restricts to (D) at one loop** (obligations O2-6, O2-9). For
every integrand, measurable or not, the joint energy-first integral (T₉) of one loop momentum is
the frozen `energyFirstIntegral` (D). -/
theorem jointEnergyFirstIntegral_one (F : (Fin 4 → ℝ) → ℂ) :
    jointEnergyFirstIntegral 1 (fun ℓ => F (ℓ 0)) = QED.OneLoop.energyFirstIntegral F :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.TwoLoop.jointEnergyFirstIntegral_one
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.TwoLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
