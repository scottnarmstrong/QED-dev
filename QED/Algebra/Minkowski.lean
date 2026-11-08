/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Metric
public import QED.Frozen.Algebra.Dot
public import QED.Frozen.Algebra.Lower
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Minkowski space with the mostly-plus metric

Four-vectors are functions `Fin 4 → ℝ` of their contravariant components `p^μ`.
Index `0` is time. The metric is `g = diag(-1, 1, 1, 1)`, following the
project's conventions (`docs/CONVENTIONS.md`, decision D-7) and the primary
source's eq. (2.4).

## Main definitions

These are author-approved frozen definitions (decision D-12), one per file under
`QED/Frozen/Algebra/`. This module re-exports them and proves their basic
properties.

* `QED.Minkowski.metric`: the components `g_{μν}`. Numerically these are also
  the inverse metric `g^{μν}`.
* `QED.Minkowski.dot`: the bilinear form `p·k = g_{μν} p^μ k^ν`.
* `QED.Minkowski.lower`: the covariant components `p_μ = g_{μν} p^ν`.

## Main statements

* `QED.Minkowski.dot_eq`: `p·k = -p⁰k⁰ + p¹k¹ + p²k² + p³k³`.
* `QED.Minkowski.metric_mul_metric`: the metric is its own inverse.
-/

@[expose] public section

namespace QED.Minkowski

theorem metric_symm (μ ν : Fin 4) : metric μ ν = metric ν μ := by
  unfold metric
  by_cases h : μ = ν
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem dot_eq (p k : Fin 4 → ℝ) :
    dot p k = -(p 0 * k 0) + p 1 * k 1 + p 2 * k 2 + p 3 * k 3 := by
  simp [dot, metric, Fin.sum_univ_four]

theorem dot_comm (p k : Fin 4 → ℝ) : dot p k = dot k p := by
  rw [dot_eq, dot_eq]
  ring

theorem lower_eq (p : Fin 4 → ℝ) :
    lower p = ![-p 0, p 1, p 2, p 3] := by
  funext μ
  fin_cases μ <;> simp [lower, metric]

theorem dot_eq_sum_lower (p k : Fin 4 → ℝ) : dot p k = ∑ μ, lower p μ * k μ := by
  rw [dot_eq, lower_eq]
  simp [Fin.sum_univ_four]

/-- The metric is its own inverse: `g_{μν} g^{νρ} = δ_μ^ρ`. -/
theorem metric_mul_metric (μ ρ : Fin 4) :
    ∑ ν, metric μ ν * metric ν ρ = if μ = ρ then 1 else 0 := by
  fin_cases μ <;> fin_cases ρ <;> simp [metric]

end QED.Minkowski

end
