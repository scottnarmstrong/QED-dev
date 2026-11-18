/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.A2Four
public import QED.Frozen.Lepton.A2FourPas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Passera's term structure agrees with `a2Four`

Helper-level proof for the Phase 5 Stage 0 packet (decision D-50), goal `a2FourPas_eq_a2Four`.

On `0 < y < 1`, with `x = 1/y`: `Real.log` is `log |·|`, so
`log ((1 - x)/(1 + x)) = log ((1 - y)/(1 + y))` and `log (1/x - x) = log (1 - y²) - log y`;
`log x = -log y` and `log (x²) = -2 log y`. The constants `π²` cancel in both brackets, and the
remaining identity is rational in `y`, `log y` and the three series.

## Main statements

* `a2FourPas_eq_a2Four'`: the frozen goal `QED.Lepton.a2FourPas_eq_a2Four`.
-/

@[expose] public section

namespace QED.Lepton.Proof

/-- `log ((1 - 1/y)/(1 + 1/y)) = log ((1 - y)/(1 + y))` for `0 < y` (`Real.log` is even). -/
theorem log_one_sub_inv_div_one_add_inv {y : ℝ} (hy0 : 0 < y) :
    Real.log ((1 - y⁻¹) / (1 + y⁻¹)) = Real.log ((1 - y) / (1 + y)) := by
  have h : (1 - y⁻¹) / (1 + y⁻¹) = -((1 - y) / (1 + y)) := by
    have h1 : 1 + y ≠ 0 := by linarith
    field_simp
    ring
  rw [h, Real.log_neg_eq_log]

/-- `log (y - 1/y) = log (1 - y²) - log y` for `0 < y < 1`. -/
theorem log_inv_inv_sub_inv {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    Real.log (y⁻¹⁻¹ - y⁻¹) = Real.log (1 - y ^ 2) - Real.log y := by
  have h : y⁻¹⁻¹ - y⁻¹ = -((1 - y ^ 2) / y) := by
    rw [inv_inv]
    field_simp
    ring
  have h2 : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  rw [h, Real.log_neg_eq_log, Real.log_div h2.ne' hy0.ne']

/-- **Passera's term structure agrees with `a2Four`** on `(0, 1)`. -/
theorem a2FourPas_eq_a2Four' {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : a2FourPas y = a2Four y := by
  have hC : Real.log (y⁻¹ ^ 2) = -2 * Real.log y := by
    rw [Real.log_pow, Real.log_inv]
    push_cast
    ring
  unfold a2FourPas a2Four
  rw [log_one_sub_inv_div_one_add_inv hy0, log_inv_inv_sub_inv hy0 hy1, hC, Real.log_inv]
  generalize (∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) ^ 2) = S₁
  generalize (∑' n : ℕ, (-y) ^ (n + 1) / ((n : ℝ) + 1) ^ 2) = S₂
  generalize (∑' n : ℕ, (y ^ 2) ^ (n + 1) / ((n : ℝ) + 1) ^ 2) = S₃
  generalize Real.log ((1 - y) / (1 + y)) = A
  generalize Real.log (1 - y ^ 2) = B
  generalize Real.log y = L
  have hy : y ≠ 0 := hy0.ne'
  field_simp
  ring

end QED.Lepton.Proof

end
