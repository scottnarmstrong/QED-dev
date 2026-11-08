/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Minkowski
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Kinematics on the mass shell

Inequalities for future-pointing four-vectors on a common mass shell `p·p = -m²`, in the
mostly-plus conventions of `docs/CONVENTIONS.md`.

## Main statements

* `QED.Minkowski.dot_le_neg_sq_of_onShell`: the reverse Cauchy–Schwarz inequality
  `p'·p ≤ -m²`.
* `QED.Minkowski.dot_sub_self_nonneg_of_onShell`: the momentum transfer `q = p' - p` is
  spacelike or null, `q² ≥ 0`.
-/

@[expose] public section

namespace QED.Minkowski

/-- Two future-pointing vectors on the same mass shell satisfy `p'·p ≤ -m²`
(reverse Cauchy–Schwarz). Equivalently `q² = (p' - p)² ≥ 0`. -/
theorem dot_le_neg_sq_of_onShell {m : ℝ} {p' p : Fin 4 → ℝ} (hp' : dot p' p' = -m ^ 2)
    (hp : dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) : dot p' p ≤ -m ^ 2 := by
  rw [dot_eq] at hp' hp ⊢
  -- `s` is the spatial dot product `p⃗'·p⃗`; the claim is `m² + s ≤ p'⁰ p⁰`.
  set s := p' 1 * p 1 + p' 2 * p 2 + p' 3 * p 3
  have hpos : 0 < p' 0 * p 0 := mul_pos hp0' hp0
  suffices h : m ^ 2 + s ≤ p' 0 * p 0 by linarith
  rcases le_or_gt (m ^ 2 + s) 0 with h0 | h0
  · linarith
  · -- Compare squares, using `|p⃗'|²|p⃗|² ≥ s²` (Lagrange) and `|p⃗'|² + |p⃗|² ≥ 2s`.
    have hsq : (m ^ 2 + s) ^ 2 ≤ (p' 0 * p 0) ^ 2 := by
      nlinarith [sq_nonneg (p' 1 * p 2 - p' 2 * p 1), sq_nonneg (p' 1 * p 3 - p' 3 * p 1),
        sq_nonneg (p' 2 * p 3 - p' 3 * p 2), sq_nonneg (p' 1 - p 1), sq_nonneg (p' 2 - p 2),
        sq_nonneg (p' 3 - p 3), sq_nonneg m]
    nlinarith

/-- The momentum transfer between two future-pointing vectors on the same mass shell is
spacelike or null: `(p' - p)² ≥ 0`. -/
theorem dot_sub_self_nonneg_of_onShell {m : ℝ} {p' p : Fin 4 → ℝ} (hp' : dot p' p' = -m ^ 2)
    (hp : dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) :
    0 ≤ dot (p' - p) (p' - p) := by
  have h := dot_le_neg_sq_of_onShell hp' hp hp0' hp0
  have e : dot (p' - p) (p' - p) = dot p' p' - 2 * dot p' p + dot p p := by
    simp only [dot_eq, Pi.sub_apply]
    ring
  rw [e]
  linarith

end QED.Minkowski

end
