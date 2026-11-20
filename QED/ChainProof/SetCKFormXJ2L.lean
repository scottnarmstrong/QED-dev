/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXKh
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the branch-2 `s`-integrand of `I(X)` in log letters

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 26+). With the simplified coefficients `k = formXkh` and the endpoint values
`B = Xs, (1 - s)(1 - X)`, `C = X(2 - X - s), 1 - s`, `D = X(2 - X - s), (1 - s)K₂`
(`K₂ = X² + (1 - X)(2 - s)`, `formXK2`) of the partial-fraction letters at `u = X, 1 - s`:

**`formXJ2_eq_L`**: for `X ∈ (0, 1)`, `s ∈ (1 - X, 1)`, `formXJ2 X s = formXJ2L X s`,
`formXJ2L = r₂ + (a₂ + a₄ + a₆)(log X - log(1 - s)) + a₂ (log s - log(1 - X)) +
(a₄ + a₆) log(2 - X - s) - a₆ log K₂`, `a₂ = k₂`, `a₄ = k₄/(1 - X)`, `a₆ = k₆/((1 - X)(2 - s))`,
`r₂ = formXJ2r` rational.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

/-- `K₂ = X² + (1 - X)(2 - s)`, the value `D(1 - s)/(1 - s)`. -/
def formXK2 (X s : ℝ) : ℝ := X ^ 2 + (1 - X) * (2 - s)

/-- `a₄ = k₄/(1 - X)`. -/
noncomputable def formXa4 (X s : ℝ) : ℝ := formXkh4 X s / (1 - X)

/-- `a₆ = k₆/((1 - X)(2 - s))`. -/
noncomputable def formXa6 (X s : ℝ) : ℝ := formXkh6 X s / ((1 - X) * (2 - s))

/-- The rational part `r₂` of the branch-2 `s`-integrand. -/
noncomputable def formXJ2r (X s : ℝ) : ℝ :=
  formXkh0 X s * (X - (1 - s)) + formXkh1 X s * (X ^ 2 - (1 - s) ^ 2) / 2 -
    formXkh3 X s * (1 / (X * s) - 1 / ((1 - s) * (1 - X))) -
    formXkh5 X s * (1 / (X * (2 - X - s)) - 1 / (1 - s)) / (1 - X) -
    (formXkh7 X s * (1 / (X * (2 - X - s)) - 1 / ((1 - s) * formXK2 X s)) +
      (formXkh8 X s / (2 * (X * (2 - X - s)) ^ 2) -
        formXkh8 X s / (2 * ((1 - s) * formXK2 X s) ^ 2))) /
      ((1 - X) * (2 - s))

/-- **The branch-2 `s`-integrand in log letters.** -/
noncomputable def formXJ2L (X s : ℝ) : ℝ :=
  formXJ2r X s + (formXkh2 X s + formXa4 X s + formXa6 X s) * (log X - log (1 - s)) +
    formXkh2 X s * (log s - log (1 - X)) + (formXa4 X s + formXa6 X s) * log (2 - X - s) -
    formXa6 X s * log (formXK2 X s)

/-- **`formXJ2` in log letters.** -/
theorem formXJ2_eq_L {X s : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (1 - X) 1) :
    formXJ2 X s = formXJ2L X s := by
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨hs0, hs1⟩ := hs
  have hs0' : 0 < s := by linarith
  have h1s : 0 < 1 - s := by linarith
  have h1X : 0 < 1 - X := by linarith
  have h2 : 0 < 2 - X - s := by linarith
  have hK : 0 < formXK2 X s := by unfold formXK2; nlinarith
  have hyp : formXKhHyp X s :=
    ⟨hX0.ne', by linarith, by linarith, hs0'.ne', by linarith, by linarith⟩
  have eB1 : formXLb X X s = X * s := by unfold formXLb; ring
  have eB0 : formXLb X (1 - s) s = (1 - s) * (1 - X) := by unfold formXLb; ring
  have eC1 : formXLc X X s = X * (2 - X - s) := by unfold formXLc; ring
  have eC0 : formXLc X (1 - s) s = 1 - s := by unfold formXLc; ring
  have eD1 : coordD X X s = X * (2 - X - s) := by unfold coordD; ring
  have eD0 : coordD X (1 - s) s = (1 - s) * formXK2 X s := by unfold coordD formXK2; ring
  unfold formXJ2 formXPFA
  rw [formXk2_eq hyp, eB1, eB0, eC1, eC0, eD1, eD0, log_mul hX0.ne' hs0'.ne',
    log_mul h1s.ne' h1X.ne', log_mul hX0.ne' h2.ne', log_mul h1s.ne' hK.ne']
  simp only [formXkh, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  unfold formXJ2L formXJ2r formXa4 formXa6
  ring

end QED.ChainProof.SetCK

end
