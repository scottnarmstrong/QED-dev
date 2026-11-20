/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXEc
public import QED.ChainProof.SetCKFormXIJ
import Mathlib.Tactic.LinearCombination

/-!
# Set (c), Stage K, closed forms: `I(X)` in closed form and the density `ρ_X`

Helper level (no frozen statement). Step 5 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 26+). The endpoint values of the antiderivatives `G₁` (`SetCKFormXG1`) and `G₂`
(`SetCKFormXG2`) are expanded in the letters `log X`, `log(1 - X)`, `log(2 - X)`, `log N`
(`formXG1_at_X`, `formXG1_at_0`, `formXG2_at_1`, `formXG2_at_1sub`); with the coefficient
identities of `SetCKFormXEc` and the dilogarithm identity `formXDil_eq_zero`:

* **`formXE_eq`**: for `X ∈ (0, 1)`, `G₁(X) - G₁(0) + (G₂(1) - G₂(1 - X)) = formXIT X`;
* **`formXI_ae_eq_formXIT`**: `I(X) = formXIT X` for almost every `X ∈ (0, 1)`;
* **`crossTH_ae_eq_rhoCrossX`**: `H_X = ∫₀^X ρ_X Q` for almost every `X ∈ (0, 1)`.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

section

variable {X : ℝ}

theorem formXG1_at_X (hX : X ∈ Ioo (0 : ℝ) 1) :
    formXG1 X X = formXG1h X X + formXG1a X X * log (1 - X) +
      formXG1c X X * (log X + log (2 - X)) + formXG1d X X * log X +
      formXkap X * (Li₂ (1 / formXK X) - Li₂ 1 + Li₂ ((1 - X) ^ 2) - Li₂ (1 - X)) := by
  have a1 : X + X - X * X = X * (2 - X) := by ring
  have a2 : X ^ 2 + (1 - X) * X = X := by ring
  unfold formXG1
  rw [formXEc_coordM_X, a1, a2, log_mul hX.1.ne' (by linarith [hX.2]), sub_self, log_zero,
    log_one, div_one, div_one]
  ring

theorem formXG1_at_0 :
    formXG1 X 0 = formXG1h X 0 + formXG1b X 0 * (X * log X) + formXG1c X 0 * log X +
      formXG1d X 0 * (2 * log X) +
      (formXG1m X - formXkap X * log (formXK X)) * log (formXN X) +
      formXkap X * (Li₂ (formXN X / formXK X) - Li₂ (formXN X) +
        Li₂ ((1 - X) ^ 2 / formXN X) - Li₂ ((1 - X) / formXN X)) := by
  have a1 : X + 0 - X * 0 = X := by ring
  have a2 : X ^ 2 + (1 - X) * 0 = X ^ 2 := by ring
  unfold formXG1
  rw [formXEc_coordM_0, a1, a2, sub_zero, sub_zero, log_one, log_pow]
  push_cast
  ring

theorem formXG2_at_1 :
    formXG2 X 1 = formXG2h X 1 - formXG2s X 1 * log (1 - X) + formXG2u X 1 * log (1 - X) +
      formXG2k X 1 * log (formXN X) - formXkap X * Li₂ 1 + formXkap X * Li₂ (1 / (2 - X)) -
      formXkap X * Li₂ ((1 - X) / formXK X) := by
  have a1 : 2 - X - 1 = 1 - X := by ring
  have a2 : formXK2 X 1 = formXN X := by unfold formXK2 formXN; ring
  unfold formXG2
  rw [a1, a2, sub_self, log_one, mul_one]
  ring

theorem formXG2_at_1sub :
    formXG2 X (1 - X) = formXG2h X (1 - X) +
      formXkap X * log (1 - X) * (log (formXK X) - log X - log (2 - X)) -
      formXkap X * Li₂ (1 - X) + formXkap X * Li₂ ((1 - X) / (2 - X)) -
      formXkap X * Li₂ ((1 - X) ^ 2 / formXK X) := by
  have a1 : 2 - X - (1 - X) = 1 := by ring
  have a2 : formXK2 X (1 - X) = 1 := by unfold formXK2; ring
  have a3 : (1 - X) * (1 - X) = (1 - X) ^ 2 := by ring
  unfold formXG2
  rw [a1, a2, a3, sub_sub_cancel, sub_self, log_one]
  ring

/-- **`I(X)` in closed form** at every `X ∈ (0, 1)`. -/
theorem formXE_eq (hX : X ∈ Ioo (0 : ℝ) 1) :
    formXG1 X X - formXG1 X 0 + (formXG2 X 1 - formXG2 X (1 - X)) = formXIT X := by
  have hD := formXDil_eq_zero hX
  have iX := formXEc_logX hX
  have i1 := formXEc_log1 hX
  have i2 := formXEc_log2 hX
  have iN := formXEc_logN hX
  have iW := formXEc_W hX
  have i0 := formXEc_rat hX
  unfold formXDil at hD
  rw [formXG1_at_X hX, formXG1_at_0, formXG2_at_1, formXG2_at_1sub]
  unfold formXIT rhoCrossX formXW
  linear_combination formXkap X * hD + log X * iX + log (1 - X) * i1 + log (2 - X) * i2 +
    log (formXN X) * iN + i0 - (4 * Li₂ (X - 1) + 2 * Li₂ (1 - X) +
      2 * log (1 - X) * log (2 - X) + log X * log (1 - X)) * iW

end

/-- **`I(X) = formXIT X`** for almost every `X ∈ (0, 1)`. -/
theorem formXI_ae_eq_formXIT :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), formXI X = formXIT X := by
  filter_upwards [formXI_ae_eq_J, ae_restrict_mem measurableSet_Ioo] with X h hX
  obtain ⟨i1, i2, he⟩ := h
  rw [he, integral_formXJ1_eq hX i1, integral_formXJ2_eq hX i2, ← formXE_eq hX]

/-- **The density of the crossed group**: `H_X = ∫₀^X ρ_X Q` for almost every `X ∈ (0, 1)`. -/
theorem crossTH_ae_eq_rhoCrossX :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), crossTH X = setCKRhoH rhoCrossX X :=
  crossTH_ae_eq_of_formXI formXI_ae_eq_formXIT

end QED.ChainProof.SetCK

end
