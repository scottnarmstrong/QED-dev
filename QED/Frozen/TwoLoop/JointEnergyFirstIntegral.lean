/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

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

@[expose] public section

open Complex

namespace QED.TwoLoop

/-- (T₉) **The joint energy-first integral** for `L` loop momenta (decision D-37.5; obligation
O2-6; `docs/TWO-LOOP-DERIVATION.md`, section 4.3): `∫ d³ℓ⃗₁ ⋯ d³ℓ⃗_L (∫ dℓ₁⁰ ⋯ dℓ_L⁰ F)`, all loop
energies innermost, then all spatial components. Index `0` of each `ℓ s` is its energy. The
measures are Lebesgue (`volume`) on `Fin L → ℝ` and `Fin L → Fin 3 → ℝ`; for `L = 2` these are
`ℝ²` and `ℝ⁶`. Like Mathlib's Bochner integral it returns `0` on non-integrable data: the inner
integral is `0` at every `ℓ⃗` where `F` is not integrable in the energies, and the outer integral
is `0` when the resulting function is not integrable; source-facing statements assert the
integrability of both stages explicitly. For `L = 1` it is the frozen `energyFirstIntegral` (D)
(T₁₂); for `L = 0` it is the value of `F` at the empty family. -/
noncomputable def jointEnergyFirstIntegral (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ) : ℂ :=
  ∫ v : Fin L → Fin 3 → ℝ, ∫ t : Fin L → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)

end QED.TwoLoop

end
