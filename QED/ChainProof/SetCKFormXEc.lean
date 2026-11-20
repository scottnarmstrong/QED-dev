/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXDil
public import QED.ChainProof.SetCKFormXRho
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the rational coefficients of `I(X)` at the endpoints

Helper level (no frozen statement). Step 5 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 26+; identities checked in `stageK/fxg/fin.py`). The value
`G₁(X) - G₁(0) + G₂(1) - G₂(1 - X)` of the two branch integrals is a combination of the
letters `log X`, `log(1 - X)`, `log(2 - X)`, `log N` with rational coefficients, plus a rational
part and `κ` times dilogarithms. With `r = Q/Q′` (`setCKQ X / setCKdQ X`), the rational
coefficients match those of `formXIT = (ρ_X Q - e₁M/(1 - X))/Q′` term by term:

* **`formXEc_logX`**, **`formXEc_log1`**, **`formXEc_log2`**: the coefficients of `log X`,
  `log(1 - X)`, `log(2 - X)`;
* **`formXEc_logN`**: the coefficient of `log N` vanishes;
* **`formXEc_W`**: the coefficient of `formXW` in `ρ_X r` is `κ`;
* **`formXEc_rat`**: the rational parts.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

section

variable {X : ℝ}

theorem formXEc_coordM_X (X : ℝ) : coordM X X = 1 := by unfold coordM; ring

theorem formXEc_coordM_0 (X : ℝ) : coordM X 0 = formXN X := by unfold coordM formXN; ring

theorem formXEc_logX (hX : X ∈ Ioo (0 : ℝ) 1) :
    formXG1c X X + formXG1d X X - formXG1b X 0 * X - formXG1c X 0 - 2 * formXG1d X 0 =
      -((X - 2) * (4 * X ^ 4 - 9 * X ^ 3 + 6 * X ^ 2 + 7 * X - 4) / (12 * (X - 1) ^ 4)) *
        (setCKQ X / setCKdQ X) := by
  obtain ⟨hX0, hX1⟩ := hX
  have h1 : X - 1 ≠ 0 := by linarith
  have h1' : 1 - X ≠ 0 := by linarith
  have h2 : X - 2 ≠ 0 := by linarith
  have h2' : 2 - X ≠ 0 := by linarith
  have hN := (formXN_pos X).ne'
  unfold formXG1c formXG1d formXG1b formXG1cD formXG1dD formXG1bD setCKQ setCKdQ
  rw [formXG1c_pol, formXG1c_pol, formXG1d_pol, formXG1d_pol, formXG1b_pol, formXEc_coordM_X,
    formXEc_coordM_0]
  field_simp
  unfold formXN
  ring

theorem formXEc_log1 (hX : X ∈ Ioo (0 : ℝ) 1) :
    formXG1a X X - formXG2s X 1 + formXG2u X 1 =
      -((4 * X ^ 6 - 37 * X ^ 5 + 110 * X ^ 4 - 146 * X ^ 3 + 85 * X ^ 2 - 10 * X - 8) /
        (12 * X * (X - 2) * (X - 1) ^ 2)) * (setCKQ X / setCKdQ X) := by
  obtain ⟨hX0, hX1⟩ := hX
  have h0 : X ≠ 0 := hX0.ne'
  have h1 : X - 1 ≠ 0 := by linarith
  have h1' : 1 - X ≠ 0 := by linarith
  have h2 : X - 2 ≠ 0 := by linarith
  have h2' : 2 - X ≠ 0 := by linarith
  have hK := (formXK_pos X).ne'
  unfold formXG1a formXG2s formXG2u formXG1aD formXG2sD formXG2uD setCKQ setCKdQ
  rw [formXG1a_pol, formXG2s_pol, formXG2u_pol, formXEc_coordM_X]
  field_simp
  unfold formXK
  ring

theorem formXEc_log2 (hX : X ∈ Ioo (0 : ℝ) 1) :
    formXG1c X X = (X - 2) ^ 2 * (X ^ 4 - 2 * X ^ 3 + X ^ 2 + 2 * X - 1) / (3 * (X - 1) ^ 4) *
      (setCKQ X / setCKdQ X) := by
  obtain ⟨hX0, hX1⟩ := hX
  have h0 : X ≠ 0 := hX0.ne'
  have h1 : X - 1 ≠ 0 := by linarith
  have h1' : 1 - X ≠ 0 := by linarith
  have h2' : 2 - X ≠ 0 := by linarith
  unfold formXG1c formXG1cD setCKQ setCKdQ
  rw [formXG1c_pol, formXEc_coordM_X]
  field_simp
  ring

theorem formXEc_logN (hX : X ∈ Ioo (0 : ℝ) 1) : formXG2k X 1 = formXG1m X := by
  obtain ⟨hX0, hX1⟩ := hX
  have h1 : X - 1 ≠ 0 := by linarith
  have hK := (formXK_pos X).ne'
  unfold formXG2k formXG2kD formXG1m
  rw [formXG2k_pol]
  field_simp
  ring

theorem formXEc_W (hX : X ∈ Ioo (0 : ℝ) 1) :
    (X - 2) * (X ^ 4 - 4 * X ^ 3 + 9 * X ^ 2 - 10 * X + 5) / (6 * X * (X - 1) ^ 3) *
      (setCKQ X / setCKdQ X) = formXkap X := by
  obtain ⟨hX0, hX1⟩ := hX
  have h0 : X ≠ 0 := hX0.ne'
  have h1 : X - 1 ≠ 0 := by linarith
  have h1' : 1 - X ≠ 0 := by linarith
  have h2 : X - 2 ≠ 0 := by linarith
  have h2' : 2 - X ≠ 0 := by linarith
  unfold formXkap setCKQ setCKdQ
  field_simp
  ring

theorem formXEc_rat (hX : X ∈ Ioo (0 : ℝ) 1) :
    formXG1h X X - formXG1h X 0 + formXG2h X 1 - formXG2h X (1 - X) =
      -(X - 2) * (9 * X ^ 2 - 20 * X + 15) / (12 * (X - 1) ^ 2) * (setCKQ X / setCKdQ X) -
        formXe1M X / (1 - X) / setCKdQ X := by
  obtain ⟨hX0, hX1⟩ := hX
  have h0 : X ≠ 0 := hX0.ne'
  have h1 : X - 1 ≠ 0 := by linarith
  have h1' : 1 - X ≠ 0 := by linarith
  have h2 : X - 2 ≠ 0 := by linarith
  have h2' : 2 - X ≠ 0 := by linarith
  have h3 : X + 1 ≠ 0 := by linarith
  have h4 : 1 - X - 2 ≠ 0 := by linarith
  have hK := (formXK_pos X).ne'
  have hN := (formXN_pos X).ne'
  have e1 : X ^ 2 + (1 - X) * X = X := by ring
  have e2 : X ^ 2 + (1 - X) * 0 = X ^ 2 := by ring
  have e3 : formXK2 X 1 = formXN X := by unfold formXK2 formXN; ring
  have e4 : formXK2 X (1 - X) = 1 := by unfold formXK2; ring
  unfold formXG1h formXG1hR formXG1hRD formXG1e1 formXG1e2 formXG2h formXG2hR formXG2hRD
    formXG2e setCKQ setCKdQ formXe1M
  rw [formXG1hR_pol, formXG1hR_pol, formXG2hR_pol, formXG2hR_pol, formXEc_coordM_X,
    formXEc_coordM_0, e1, e2, e3, e4]
  field_simp
  unfold formXK formXN
  ring

end

end QED.ChainProof.SetCK

end
