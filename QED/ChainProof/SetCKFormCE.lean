/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCFTC
public import QED.ChainProof.SetCKFormCDil
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the endpoint value of the `u`-antiderivative of `J`

Helper level (no frozen statement). At `u = X` the letters are `P = X`, `Q = X(2 - X)`, `M = 1`,
`X + u - Xu = X(2 - X)`, at `u = 0` they are `P = Q = X²`, `M = T = X² - X + 1`,
`X + u - Xu = X`; the `Li₂` arguments of the seven blocks become the thirteen arguments of
`formCLi` and `Li₂ 1 = π²/6`. So (**`formCG_sub_eq`**)

`G(X) - G(0) = E(X) = X(X - 2)/12 + X(2X² - 3X + 2)/(12(X - 1)²) log X`
`  - (X - 1)(X² - 3X + 1)/(6(X - 2)) log(1 - X) - X(X - 2)K/(12(X - 1)²) log(2 - X)`
`  + π²/36 + log² T/12 - log(1 - X) log T/6 - log K log T/6 + formCLi/6`

(`formCE`), and by the dilogarithm identity `formCDel_eq_zero` (**`formCE_eq`**)

`E(X) = X(X - 2)/12 + X(2X² - 3X + 2)/(12(X - 1)²) log X`
`  - (X - 1)(X² - 3X + 1)/(6(X - 2)) log(1 - X) - X(X - 2)K/(12(X - 1)²) log(2 - X) - W/6`.
-/

@[expose] public section

open Real Set QED.Polylog

namespace QED.ChainProof.SetCK

/-- **The endpoint value** `E(X) = G(X) - G(0)`. -/
noncomputable def formCE (X : ℝ) : ℝ :=
  X * (X - 2) / 12 + X * (2 * X ^ 2 - 3 * X + 2) / (12 * (X - 1) ^ 2) * log X -
    (X - 1) * (X ^ 2 - 3 * X + 1) / (6 * (X - 2)) * log (1 - X) -
    X * (X - 2) * formCK X / (12 * (X - 1) ^ 2) * log (2 - X) + π ^ 2 / 36 +
    log (formCT X) ^ 2 / 12 - log (1 - X) * log (formCT X) / 6 -
    log (formCK X) * log (formCT X) / 6 + formCLi X / 6

/-- **The closed form of `σ_C`**, weight two through `W` only. -/
noncomputable def formCSigT (X : ℝ) : ℝ :=
  X * (X - 2) / 12 + X * (2 * X ^ 2 - 3 * X + 2) / (12 * (X - 1) ^ 2) * log X -
    (X - 1) * (X ^ 2 - 3 * X + 1) / (6 * (X - 2)) * log (1 - X) -
    X * (X - 2) * formCK X / (12 * (X - 1) ^ 2) * log (2 - X) - formCW X / 6

theorem formCE_eq {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) : formCE X = formCSigT X := by
  have h := formCDel_eq_zero hX
  unfold formCDel at h
  unfold formCE formCSigT
  linear_combination h / 6

/-- **`G(X) - G(0) = E(X)`**. -/
theorem formCG_sub_eq {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) : formCG X X - formCG X 0 = formCE X := by
  obtain ⟨h0, h1⟩ := hX
  have h1X : 0 < 1 - X := by linarith
  have h2X : 0 < 2 - X := by linarith
  have hX1 : X - 1 ≠ 0 := by linarith
  have hX2 : X - 2 ≠ 0 := by linarith
  have hK := formCK_pos X
  have hT := formCT_pos X
  have hPX : formCP X X = X := by unfold formCP; ring
  have hQX : formCQ X X = X * (2 - X) := by unfold formCQ; ring
  have hMX : coordM X X = 1 := by unfold coordM; ring
  have hAX : X + X - X * X = X * (2 - X) := by ring
  have hP0 : formCP X 0 = X ^ 2 := by unfold formCP; ring
  have hQ0 : formCQ X 0 = X ^ 2 := by unfold formCQ; ring
  have hM0 : coordM X 0 = formCT X := by unfold coordM formCT; ring
  have hA0 : X + 0 - X * 0 = X := by ring
  have e6X : -X / (1 - X) / (-X / (1 - X) - 1) = X := by
    have : -X / (1 - X) - 1 = -1 / (1 - X) := by field_simp; ring
    rw [this]
    field_simp
  have e60 : -X ^ 2 / (1 - X) / (-X ^ 2 / (1 - X) - 1) = X ^ 2 / formCT X := by
    have : -X ^ 2 / (1 - X) - 1 = -formCT X / (1 - X) := by field_simp; unfold formCT; ring
    rw [this]
    field_simp
  have g1 : log (X * (2 - X)) = log X + log (2 - X) := log_mul h0.ne' h2X.ne'
  have g2 : log (X ^ 2) = 2 * log X := by rw [log_pow]; norm_num
  have g3 : log (formCK X / (2 * (1 - X))) = log (formCK X) - log 2 - log (1 - X) := by
    rw [log_div hK.ne' (by positivity), log_mul (by norm_num) h1X.ne']; ring
  have g4 : log (formCK X / (1 - X)) = log (formCK X) - log (1 - X) := log_div hK.ne' h1X.ne'
  have g5 : log (1 / (1 - X) ^ 2) = -(2 * log (1 - X)) := by
    rw [one_div, log_inv, log_pow]; norm_num
  have g6 : log (formCT X / (1 - X) ^ 2) = log (formCT X) - 2 * log (1 - X) := by
    rw [log_div hT.ne' (by positivity), log_pow]; norm_num
  have g7 : log (1 / (1 - X)) = -log (1 - X) := by rw [one_div, log_inv]
  have g8 : log (formCT X / (1 - X)) = log (formCT X) - log (1 - X) := log_div hT.ne' h1X.ne'
  have g9 : log (1 - -X / (1 - X)) = -log (1 - X) := by
    rw [show 1 - -X / (1 - X) = 1 / (1 - X) by field_simp; ring, g7]
  have g10 : log (1 - -X ^ 2 / (1 - X)) = log (formCT X) - log (1 - X) := by
    rw [show 1 - -X ^ 2 / (1 - X) = formCT X / (1 - X) by field_simp; unfold formCT; ring, g8]
  have g11 : log (formCK X / 2) = log (formCK X) - log 2 := log_div hK.ne' (by norm_num)
  unfold formCG formCD1 formCD2 formCD3 formCD4 formCD5 formCD6 formCD7
  simp only [hPX, hQX, hMX, hAX, hP0, hQ0, hM0, hA0, sub_self, sub_zero, log_zero, log_one,
    one_div_div, e6X, e60, Li₂_one, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11]
  unfold formCFU formCFV formCFM formCFX formCHr formCE formCLi
  unfold formCGm formCGq formCGp formCc formChU formChM formChP formChA
  simp only [hPX, hQX, hMX, hP0, hQ0, hM0]
  field_simp
  unfold formCK formCT
  ring

end QED.ChainProof.SetCK

end
