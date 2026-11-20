/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCE
public import QED.ChainProof.SetCKAsmRho
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the inner corner density `ρ_C`

Helper level (no frozen statement). With `W = formCW` the weight-two function of the `λ⁽⁴⁾`
alphabet, the Stieltjes density of the inner corner group (`cornIn`) is (`rhoCornC`)

`ρ_C = a + b log X + c log(1 - X) + d log(2 - X) + p W`,
`a = -(2X - 1)(X² + 4X - 6)/(6X(X - 1))`, `b = (X - 2)(2X² - 3X + 2)/(6(X - 1)³)`,
`c = -(X² - 3X + 1)/(3X)`, `d = -(X - 2)²(X² - 2X + 2)/(6(X - 1)³)`,
`p = -(X - 2)/(3X(X - 1))`

(scratch `stageK/STATUS.md`, session 16). Proof: for almost every `X`,
`σ_C(X) = ∫_{(0, X)} J` (`cornInSig_ae_eq_formCJ`) `= G(X) - G(0)` (`integral_formCJ_eq`)
`= E(X)` (`formCG_sub_eq`) `= formCSigT X` (`formCE_eq`, the dilogarithm identity), and
`2(e₁ + Q' formCSigT)/Q = ρ_C` is rational algebra (`rhoCornIn_eq_of_sig`).

* **`cornInSig_ae_eq_formCSigT`**: `σ_C = formCSigT` almost everywhere on `(0, 1)`;
* **`rhoCornIn_ae_eq`**: `rhoCornIn = rhoCornC` almost everywhere on `(0, 1)`;
* **`setCKRhoH_rhoCornIn_eq`**: `H_ρ` of `rhoCornIn` and of `rhoCornC` agree on `(0, 1)`.
-/

@[expose] public section

open Real Set Filter MeasureTheory

namespace QED.ChainProof.SetCK

/-- **The Stieltjes density of the inner corner group** `ρ_C`, in closed form. -/
noncomputable def rhoCornC (X : ℝ) : ℝ :=
  -(2 * X - 1) * (X ^ 2 + 4 * X - 6) / (6 * X * (X - 1)) +
    (X - 2) * (2 * X ^ 2 - 3 * X + 2) / (6 * (X - 1) ^ 3) * log X -
    (X ^ 2 - 3 * X + 1) / (3 * X) * log (1 - X) -
    (X - 2) ^ 2 * (X ^ 2 - 2 * X + 2) / (6 * (X - 1) ^ 3) * log (2 - X) -
    (X - 2) / (3 * X * (X - 1)) * formCW X

/-- **`σ_C` in closed form** almost everywhere on `(0, 1)`. -/
theorem cornInSig_ae_eq_formCSigT :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), cornInSig X = formCSigT X := by
  filter_upwards [cornInSig_ae_eq_formCJ, ae_restrict_mem measurableSet_Ioo] with X h hX
  rw [h.2, integral_formCJ_eq hX h.1, formCG_sub_eq hX, formCE_eq hX]

/-- The density from the closed form of `σ_C`: `2(e₁ + Q' σ_C)/Q = ρ_C`. -/
theorem rhoCornIn_eq_of_sig {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (h : cornInSig X = formCSigT X) :
    rhoCornIn X = rhoCornC X := by
  obtain ⟨h0, h1⟩ := hX
  have hX0 : X ≠ 0 := h0.ne'
  have h1X : 1 - X ≠ 0 := by linarith
  have hX1 : X - 1 ≠ 0 := by linarith
  have hX2 : X - 2 ≠ 0 := by linarith
  have h2X : 2 - X ≠ 0 := by linarith
  have hK := (formCK_pos X).ne'
  rw [rhoCornIn, h]
  unfold cornInE1 cornInE1M setCKdQ setCKQ formCSigT rhoCornC
  field_simp
  unfold formCK
  ring

/-- **The inner corner density in closed form**: `rhoCornIn = rhoCornC` a.e. on `(0, 1)`. -/
theorem rhoCornIn_ae_eq :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), rhoCornIn X = rhoCornC X := by
  filter_upwards [cornInSig_ae_eq_formCSigT, ae_restrict_mem measurableSet_Ioo] with X h hX
  exact rhoCornIn_eq_of_sig hX h

/-- **The weight of the inner corner group in closed form**: on `(0, 1)`,
`H_ρ(X) = ∫₀^X ρ_C Q` with `ρ_C = rhoCornC`. -/
theorem setCKRhoH_rhoCornIn_eq {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    setCKRhoH rhoCornIn X = setCKRhoH rhoCornC X := by
  have h' : ∀ᵐ x ∂volume, x ∈ Ioo (0 : ℝ) 1 → rhoCornIn x = rhoCornC x :=
    (ae_restrict_iff' measurableSet_Ioo).1 rhoCornIn_ae_eq
  unfold setCKRhoH
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h'] with x hx hxX
  rw [uIoc_of_le hX.1.le] at hxX
  rw [hx ⟨hxX.1, hxX.2.trans_lt hX.2⟩]

end QED.ChainProof.SetCK

end
