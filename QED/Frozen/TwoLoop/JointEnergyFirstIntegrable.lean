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

/-- (T₉′) **Integrability of both stages of the joint energy-first integral** (T₉): the integrand
is integrable in the energies at every spatial `ℓ⃗`, and the resulting energy integral is
integrable in the spatial components. Source-facing statements about (T₉) and (T₁₀) assert this,
so that the values are genuine integrals. -/
def jointEnergyFirstIntegrable (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ v : Fin L → Fin 3 → ℝ, MeasureTheory.Integrable fun t : Fin L → ℝ =>
      F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) ∧
    MeasureTheory.Integrable fun v : Fin L → Fin 3 → ℝ =>
      ∫ t : Fin L → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)

end QED.TwoLoop

end
