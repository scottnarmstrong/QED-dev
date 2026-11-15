/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Frozen.OneLoop.VertexOneLoop
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Provider for `QED.OneLoop.oneLoopAnomaly_mem_codata2022`

Proves the frozen theorem goal `QED.OneLoop.oneLoopAnomaly_mem_codata2022` (packet Q, decision D-35)
as `QED.Provider.OneLoop.oneLoopAnomaly_mem_codata2022`, with the binder convention of decision
D-13. With `a = 4π/e²`, the hypothesis forces `e ≠ 0` (in Lean `4π/0 = 0`), and then `e²/(8π²) =
1/(2πa)`; the bounds follow from Mathlib's 20-digit bounds on `π` (`Real.pi_gt_d20`,
`Real.pi_lt_d20`). It must never import the frozen anchor.
-/

@[expose] public section

namespace QED.Provider.OneLoop

/-- Packet Q's (Q₄), with an implicit data binder and a `by assumption` hypothesis
(decision D-13). -/
theorem oneLoopAnomaly_mem_codata2022 {e : ℝ}
    (hα : 4 * Real.pi / e ^ 2 ∈ Set.Icc (137.035999156 : ℝ) 137.035999198 := by assumption) :
    e ^ 2 / (8 * Real.pi ^ 2) ∈ Set.Icc (0.0011614097319 : ℝ) 0.0011614097323 := by
  obtain ⟨h1, h2⟩ := hα
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have hpi : 0 < Real.pi := Real.pi_pos
  have he : e ^ 2 ≠ 0 := by
    intro h
    rw [h, div_zero] at h1
    norm_num at h1
  have key : e ^ 2 / (8 * Real.pi ^ 2) = 1 / (2 * Real.pi * (4 * Real.pi / e ^ 2)) := by
    field_simp
    ring
  rw [key]
  set a := 4 * Real.pi / e ^ 2 with ha
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) h1
  constructor
  · rw [le_div_iff₀ (by positivity)]
    calc (0.0011614097319 : ℝ) * (2 * Real.pi * a)
        ≤ 0.0011614097319 * (2 * 3.14159265358979323847 * 137.035999198) := by gcongr
      _ ≤ 1 := by norm_num
  · rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) ≤ 0.0011614097323 * (2 * 3.14159265358979323846 * 137.035999156) := by
          norm_num
      _ ≤ 0.0011614097323 * (2 * Real.pi * a) := by gcongr

end QED.Provider.OneLoop

end
