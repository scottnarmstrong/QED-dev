/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace QED.Lepton

/-- (L₀) **A heavy lepton with its own Pauli–Villars pair** (decision D-49.4; plan Q5 (i)): the
physical mass `m` of a lepton other than the electron (the muon or the tau), and the masses `M₁`,
`M₂` and loop coefficients `c₁`, `c₂` of its two regulator fermions, the analogue for this lepton
of T1's (D-22) fields of `Params`. A closed loop of the lepton itself has coefficient `1`. The
Pauli–Villars conditions `1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0`, the bounds `m < M₁`,
`m < M₂` and `m_e < m` are hypotheses of later theorems. -/
structure HeavyLepton where
  /-- The physical mass `m_ℓ` of the lepton. -/
  m : ℝ
  /-- The mass of the first regulator fermion of this lepton. -/
  M₁ : ℝ
  /-- The mass of the second regulator fermion of this lepton. -/
  M₂ : ℝ
  /-- The loop coefficient of the first regulator fermion of this lepton. -/
  c₁ : ℝ
  /-- The loop coefficient of the second regulator fermion of this lepton. -/
  c₂ : ℝ

end QED.Lepton

end
