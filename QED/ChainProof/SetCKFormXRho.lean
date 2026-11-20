/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXFub
public import QED.ChainProof.SetCKAsmRho
public import QED.Polylog.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the crossed density and the last reduction

Helper level (no frozen statement). Step 5 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
sessions 16+, 19+, 24+). With `lX = log X`, `l₁ = log(1 - X)`, `l₂ = log(2 - X)` and
`W = 4 Li₂(X - 1) + 2 Li₂(1 - X) + 2 l₁ l₂ + lX l₁` (`formXW`), the crossed density is
(`rhoCrossX`) `ρ_X = a + b lX + c l₁ + d l₂ + p W`,
`a = -(X - 2)(9X² - 20X + 15)/(12(X - 1)²)`,
`b = -(X - 2)(4X⁴ - 9X³ + 6X² + 7X - 4)/(12(X - 1)⁴)`,
`c = -(4X⁶ - 37X⁵ + 110X⁴ - 146X³ + 85X² - 10X - 8)/(12X(X - 2)(X - 1)²)`,
`d = (X - 2)²(X⁴ - 2X³ + X² + 2X - 1)/(3(X - 1)⁴)`,
`p = (X - 2)(X⁴ - 4X³ + 9X² - 10X + 5)/(6X(X - 1)³)`.
The value of `I(X)` it predicts is `formXIT = (ρ_X Q - e₁M/(1 - X))/Q′`, and

**`crossTH_ae_eq_of_formXI`**: if `I = formXIT` almost everywhere on `(0, 1)`, then
`crossTH = setCKRhoH rhoCrossX` almost everywhere on `(0, 1)`

(from `crossTH_ae_eq_formXI` and `intervalIntegral.integral_congr_ae`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The weight-two function `W` of the `λ⁽⁴⁾` alphabet. -/
noncomputable def formXW (X : ℝ) : ℝ :=
  4 * Li₂ (X - 1) + 2 * Li₂ (1 - X) + 2 * log (1 - X) * log (2 - X) + log X * log (1 - X)

/-- **The Stieltjes density of the crossed group** `ρ_X`. -/
noncomputable def rhoCrossX (X : ℝ) : ℝ :=
  -(X - 2) * (9 * X ^ 2 - 20 * X + 15) / (12 * (X - 1) ^ 2) -
    (X - 2) * (4 * X ^ 4 - 9 * X ^ 3 + 6 * X ^ 2 + 7 * X - 4) / (12 * (X - 1) ^ 4) * log X -
    (4 * X ^ 6 - 37 * X ^ 5 + 110 * X ^ 4 - 146 * X ^ 3 + 85 * X ^ 2 - 10 * X - 8) /
      (12 * X * (X - 2) * (X - 1) ^ 2) * log (1 - X) +
    (X - 2) ^ 2 * (X ^ 4 - 2 * X ^ 3 + X ^ 2 + 2 * X - 1) / (3 * (X - 1) ^ 4) * log (2 - X) +
    (X - 2) * (X ^ 4 - 4 * X ^ 3 + 9 * X ^ 2 - 10 * X + 5) / (6 * X * (X - 1) ^ 3) * formXW X

/-- **The predicted value of `I(X)`**: `(ρ_X Q - e₁M/(1 - X))/Q′`. -/
noncomputable def formXIT (X : ℝ) : ℝ :=
  (rhoCrossX X * setCKQ X - formXe1M X / (1 - X)) / setCKdQ X

theorem formXIT_eq {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    formXe1M X / (1 - X) + setCKdQ X * formXIT X = rhoCrossX X * setCKQ X := by
  have hQ := (setCKdQ_pos hX).ne'
  unfold formXIT
  field_simp
  ring

/-- **The last reduction**: the closed form of `I` almost everywhere gives
`H_X = ∫₀^X ρ_X Q` almost everywhere. -/
theorem crossTH_ae_eq_of_formXI
    (h : ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), formXI X = formXIT X) :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), crossTH X = setCKRhoH rhoCrossX X := by
  have h' : ∀ᵐ x ∂volume, x ∈ Ioo (0 : ℝ) 1 → formXI x = formXIT x :=
    (ae_restrict_iff' measurableSet_Ioo).1 h
  filter_upwards [crossTH_ae_eq_formXI, ae_restrict_mem measurableSet_Ioo] with X hI hX
  rw [hI.2, setCKRhoH]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h'] with x hx hxX
  rw [uIoc_of_le hX.1.le] at hxX
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hxX.1, hxX.2.trans_lt hX.2⟩
  rw [hx hx01, formXIT_eq hx01]

end QED.ChainProof.SetCK

end
