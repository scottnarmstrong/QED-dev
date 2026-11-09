/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

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

/-- (X₀) The parameters of the regulated model (decisions D-5, D-19, D-22). They are data only:
conditions such as `ε > 0`, the on-shell conditions on the counterterms, and the Pauli–Villars
conditions are hypotheses of later theorems. -/
structure Params where
  /-- The electron charge `e` (negative, D-7). The regulator fermions couple with the same charge,
  as is standard for Pauli–Villars regulator fields. -/
  e : ℝ
  /-- The vertex counterterm coefficient `δ₁ = Z₁ - 1` of (62.2), of order `e²` (D-19). -/
  δ₁ : ℝ
  /-- The counterterm coefficient `δ₂ = Z₂ - 1` of (62.3), of order `e²` (D-19). -/
  δ₂ : ℝ
  /-- The counterterm coefficient `δ_m = Z_m - 1` of (62.3), of order `e²` (D-19). -/
  δm : ℝ
  /-- The counterterm coefficient `δ₃ = Z₃ - 1` of (62.3), of order `e²` (D-19). -/
  δ₃ : ℝ
  /-- The electron mass `m`. -/
  m : ℝ
  /-- The photon mass `m_γ`, the infrared regulator (D-5). -/
  mγ : ℝ
  /-- The Pauli–Villars photon mass `Λ` (D-5). -/
  Λ : ℝ
  /-- The Feynman prescription `ε` of the propagators; only `ε > 0` is source-facing. -/
  ε : ℝ
  /-- The mass `M₁` of the regulator fermion of flavor `1` (D-22). -/
  M₁ : ℝ
  /-- The mass `M₂` of the regulator fermion of flavor `2` (D-22). -/
  M₂ : ℝ
  /-- The coefficient `c₁` of a closed loop of the regulator fermion of flavor `1` (D-22). -/
  c₁ : ℝ
  /-- The coefficient `c₂` of a closed loop of the regulator fermion of flavor `2` (D-22). -/
  c₂ : ℝ

end QED.WickModel

end
