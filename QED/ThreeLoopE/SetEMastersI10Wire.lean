/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10Def
public import QED.ThreeLoopE.SetEMastersLaurent
public import QED.ThreeLoopD.SetDMastersGamma2
public import QED.DimReg.GammaTaylor
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (e), master `I₁₀`: the input from the expansion of the analytic remainder

`I₁₀ C⁻¹ = Γ(3ε - 1) / Γ(1 + ε)³ · T` (`QED.ThreeLoopE.lr96I10`), and
`T = Closed + Rest / ε` (`QED.ThreeLoopE.i10T_eq`) with the `Γ`-function part
`Closed = (S₀ + 2 C_a + C_ab) / (1 - ε)` (`QED.ThreeLoopE.i10Closed`) and the remainder

  `Rest = (2 K_a + ε K_ab) / (1 - ε) + 2 ε B(ε, 1 + ε) G₀ + ε K₂` (`QED.ThreeLoopE.i10Rest`),

analytic at `0` once `K_a, K_ab, G₀, K₂` are (`ε B(ε, 1 + ε) = Γ(1 + ε)² / Γ(1 + 2ε)`). With
`A, B, C, D = Γ(1 + ε), Γ(1 - ε), Γ(1 + 2ε), Γ(1 + 3ε)` the master is
(`QED.ThreeLoopE.setEMasterI10_eq`)

  `ε³ Den · I₁₀ C⁻¹ = P₁ E₁ + P₂ E₂ + P₃ E₃ + P₄ E₄ + P₅ E₅ Rest`,

`Den = 3(ε - 1)²(ε + 1)(3ε - 1)`, `E₁ = D/(A C)`, `E₂ = C/A²`, `E₃ = B D/C`, `E₄ = B C/A`,
`E₅ = D/A³`, and polynomials `Pᵢ`. In each `Eᵢ` the arguments balance, so by
`QED.DimReg.Gamma_one_add_eq_exp` it is `exp(ε² (x₀ + x₁ ε + x₂ ε² + ε³ Yᵢ))` with `Yᵢ` analytic
(`QED.ThreeLoopE.i10E1_eq`, …). Truncating `exp` (`QED.ThreeLoopE.i10_exp_trunc`), the expansion

  `Rest = -1 + (π² - 10) ε + (5π²/6 + 44ζ₃ - 55) ε² + (401π⁴/90 - 47π²/3 + 6ζ₃ - 285) ε³
    + O(ε⁴)` (`QED.ThreeLoopE.i10RestLaurent`)

gives `HasTruncLaurent setEMasterI10 setELaurentI10 2`
(`QED.ThreeLoopE.hasTruncLaurent_setEMasterI10_of_rest`): the orders `ε⁰` to `ε⁴` of
`ε³ Den · I₁₀ C⁻¹` match by the polynomial identity `QED.ThreeLoopE.i10Wire_key`, checked by
`ring`. The coefficients of `Rest` are the ones the LR96 table forces; they and the polynomial
data were computed by `scripts/numerics/three_loop_masters/i10gen.py`. The Taylor coefficients of
the integrals, computed directly from the integrands
(`scripts/numerics/three_loop_masters/i10taylor.py`), reproduce them to `5 · 10⁻¹³`. Their proof
is the hypothesis that remains.

## Main results

* `QED.ThreeLoopE.i10T_eq`, `QED.ThreeLoopE.setEMasterI10_eq`.
* `QED.ThreeLoopE.hasTruncLaurent_setEMasterI10_of_rest`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog QED.ThreeLoopD

namespace QED.ThreeLoopE

/-! ### The closed part and the remainder -/

/-- The `Γ`-function part of `T`: `(S₀ + 2 C_a + C_ab) / (1 - ε)`. -/
noncomputable def i10Closed (ε : ℂ) : ℂ := (i10S0 ε + 2 * i10Ca ε + i10Cab ε) / (1 - ε)

/-- **The analytic remainder** `Rest = ε (T - Closed)`:
`(2 K_a + ε K_ab) / (1 - ε) + 2 ε B(ε, 1 + ε) G₀ + ε K₂`. -/
noncomputable def i10Rest (ε : ℂ) : ℂ :=
  (2 * i10Ka ε + ε * i10Kab ε) / (1 - ε) + 2 * (ε * i9Beta ε (1 + ε)) * i10G0 ε + ε * i10K2 ε

/-- **The target expansion of `Rest`** through `ε³` (forced by the LR96 table). -/
noncomputable def i10RestLaurent (ε : ℂ) : ℂ :=
  -1 + ((π : ℂ) ^ 2 - 10) * ε + (5 / 6 * (π : ℂ) ^ 2 + 44 * (zeta3 : ℂ) - 55) * ε ^ 2 +
    (401 / 90 * (π : ℂ) ^ 4 - 47 / 3 * (π : ℂ) ^ 2 + 6 * (zeta3 : ℂ) - 285) * ε ^ 3

theorem i10T_eq {ε : ℂ} (h0 : ε ≠ 0) (h1 : 1 - ε ≠ 0) :
    i10T ε = i10Closed ε + i10Rest ε / ε := by
  simp only [i10T, i10S, i10Closed, i10Rest]
  field_simp
  ring

/-! ### The master as a combination of `Γ`-ratios -/

/-- `E₁ = Γ(1 + 3ε) / (Γ(1 + ε) Γ(1 + 2ε))`. -/
noncomputable def i10E1 (ε : ℂ) : ℂ :=
  Gamma (1 + 3 * ε) / (Gamma (1 + 1 * ε) * Gamma (1 + 2 * ε))

/-- `E₂ = Γ(1 + 2ε) / Γ(1 + ε)²`. -/
noncomputable def i10E2 (ε : ℂ) : ℂ :=
  Gamma (1 + 2 * ε) / (Gamma (1 + 1 * ε) * Gamma (1 + 1 * ε))

/-- `E₃ = Γ(1 - ε) Γ(1 + 3ε) / Γ(1 + 2ε)`. -/
noncomputable def i10E3 (ε : ℂ) : ℂ :=
  Gamma (1 + (-1) * ε) * Gamma (1 + 3 * ε) / Gamma (1 + 2 * ε)

/-- `E₄ = Γ(1 - ε) Γ(1 + 2ε) / Γ(1 + ε)`. -/
noncomputable def i10E4 (ε : ℂ) : ℂ :=
  Gamma (1 + (-1) * ε) * Gamma (1 + 2 * ε) / Gamma (1 + 1 * ε)

/-- `E₅ = Γ(1 + 3ε) / Γ(1 + ε)³`. -/
noncomputable def i10E5 (ε : ℂ) : ℂ :=
  Gamma (1 + 3 * ε) / (Gamma (1 + 1 * ε) * Gamma (1 + 1 * ε) * Gamma (1 + 1 * ε))

/-- The denominator `3(ε - 1)²(ε + 1)(3ε - 1)`. -/
noncomputable def i10Den (ε : ℂ) : ℂ := 3 * (ε - 1) ^ 2 * (ε + 1) * (3 * ε - 1)

/-- `P₁ = 2(ε² - 4ε + 1)`. -/
noncomputable def i10P1 (ε : ℂ) : ℂ := 2 * (ε ^ 2 - 4 * ε + 1)

/-- `P₂ = 2(4ε - 1)`. -/
noncomputable def i10P2 (ε : ℂ) : ℂ := 2 * (4 * ε - 1)

/-- `P₃ = 2(ε + 1)`. -/
noncomputable def i10P3 (ε : ℂ) : ℂ := 2 * (ε + 1)

/-- `P₄ = (ε - 1)(ε + 1)`. -/
noncomputable def i10P4 (ε : ℂ) : ℂ := (ε - 1) * (ε + 1)

/-- `P₅ / ε = (ε - 1)²(ε + 1)`. -/
noncomputable def i10P5 (ε : ℂ) : ℂ := (ε - 1) ^ 2 * (ε + 1)

theorem i10Den_ne_zero {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i10Den ε ≠ 0 := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl (-1) 1 (by norm_num) (by norm_num) (x := ε - 1) (by ring)
  have h2 := hl 1 1 (by norm_num) (by norm_num) (x := ε + 1) (by ring)
  have h3 := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
  simp only [i10Den]
  simp [h1, h2, h3]

/-- **`I₁₀ C⁻¹` as a combination of `Γ`-ratios and the remainder.** -/
theorem setEMasterI10_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setEMasterI10 ε = (i10P1 ε * i10E1 ε + i10P2 ε * i10E2 ε + i10P3 ε * i10E3 ε +
      i10P4 ε * i10E4 ε + ε * i10P5 ε * i10E5 ε * i10Rest ε) / (ε ^ 3 * i10Den ε) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have hm := fun a ha {x : ℂ} (hx : x = a * ε) => setDGamma_mul_ne_zero h0 a ha hx
  have hG := fun a ha => Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε a ha)
  have k1 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have k2 := hl (-1) 1 (by norm_num) (by norm_num) (x := ε - 1) (by ring)
  have k3 := hl 1 1 (by norm_num) (by norm_num) (x := 1 + ε) (by ring)
  have k4 := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
  have k5 := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
  have k6 := hl (-2) 2 (by norm_num) (by norm_num) (x := 2 * ε - 2) (by ring)
  have k7 := hl 1 1 (by norm_num) (by norm_num) (x := ε + 1) (by ring)
  have m2 := hm 2 two_ne_zero (x := 2 * ε) rfl
  have m3 := hm 3 three_ne_zero (x := 3 * ε) rfl
  have g1 : Gamma (ε - 1 + (ε - 1)) =
      Gamma (1 + 2 * ε) / ((2 * ε - 1) * (2 * ε - 2) * (2 * ε)) := by
    have s0 : ε - 1 + (ε - 1) ≠ 0 := hl (-2) 2 (by norm_num) (by norm_num) (by ring)
    have s1 : ε - 1 + (ε - 1) + 1 ≠ 0 := hl (-1) 2 (by norm_num) (by norm_num) (by ring)
    have s2 : ε - 1 + (ε - 1) + 1 + 1 ≠ 0 := hm 2 two_ne_zero (by ring)
    exact Gamma_eq_div_three s0 s1 s2 (by ring) (by ring)
  have g2 : Gamma (2 * ε + (ε - 1)) = Gamma (1 + 3 * ε) / (3 * ε * (3 * ε - 1)) :=
    Gamma_eq_div_two (hl (-1) 3 (by norm_num) (by norm_num) (by ring))
      (by rw [show 2 * ε + (ε - 1) + 1 = 3 * ε by ring]; exact m3) (by ring) (by ring)
  have g3 : Gamma (3 * ε - 1) = Gamma (1 + 3 * ε) / (3 * ε * (3 * ε - 1)) :=
    Gamma_eq_div_two k4 (by rw [show 3 * ε - 1 + 1 = 3 * ε by ring]; exact m3) (by ring)
      (by ring)
  have g4 : Gamma (ε + (1 + ε)) = Gamma (1 + 2 * ε) := by congr 1; ring
  have g5 : Gamma (2 * ε + (1 + ε)) = Gamma (1 + 3 * ε) := by congr 1; ring
  have g6 : Gamma (1 + ε + ε) = Gamma (1 + 2 * ε) := by congr 1; ring
  have g7 : Gamma (ε - 1) = Gamma (1 + 1 * ε) / (ε * (ε - 1)) :=
    Gamma_eq_div_two k2 (by rw [show ε - 1 + 1 = ε by ring]; exact h0) (by ring) (by ring)
  have g8 : Gamma (2 * ε) = Gamma (1 + 2 * ε) / (2 * ε) := Gamma_eq_div_one m2 (by ring) rfl
  have g9 : Gamma (1 - ε) = Gamma (1 + (-1) * ε) := by congr 1; ring
  have g10 : Gamma ε = Gamma (1 + 1 * ε) / ε := Gamma_eq_div_one h0 (by ring) rfl
  have g11 : Gamma (1 + ε) = Gamma (1 + 1 * ε) := by congr 1; ring
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  have hA := hG 1 (by norm_num)
  have hC := hG 2 (by norm_num)
  have hD := hG 3 (by norm_num)
  rw [setEMasterI10, lr96I10, lr96C, QED.DimReg.lr96LoopFactor_four_sub, i10T_eq h0 k1]
  simp only [i10Closed, i10S0, i10Ca, i10Cab, i9Beta, i10E1, i10E2, i10E3, i10E4, i10E5,
    i10P1, i10P2, i10P3, i10P4, i10P5, i10Den]
  rw [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11]
  generalize i10Rest ε = R
  generalize Gamma (1 + 1 * ε) = A at *
  generalize Gamma (1 + (-1) * ε) = B
  generalize Gamma (1 + 2 * ε) = C at *
  generalize Gamma (1 + 3 * ε) = D at *
  generalize (π : ℂ) ^ ε = P at *
  field_simp
  ring

/-! ### The `Γ`-ratios as exponentials -/

/-- The exponent tail of `Γ(1 + z)`: `log Γ(1 + z) = -γ z + π²/12 z² - ζ₃/3 z³ + π⁴/360 z⁴
+ z⁵ Lₜ(z)`. -/
noncomputable def i10Lt (z : ℂ) : ℂ := -(zeta5 : ℂ) / 5 + z * QED.DimReg.logGammaRem z

theorem i10_Gamma_eq_exp {z : ℂ} (hz : ‖z‖ < 1) :
    Gamma (1 + z) = cexp (-(eulerMascheroniConstant : ℂ) * z + (π : ℂ) ^ 2 / 12 * z ^ 2 -
      (zeta3 : ℂ) / 3 * z ^ 3 + (π : ℂ) ^ 4 / 360 * z ^ 4 + z ^ 5 * i10Lt z) := by
  rw [QED.DimReg.Gamma_one_add_eq_exp hz, i10Lt]
  congr 1
  ring

/-- `Y₁ = 3⁵ Lₜ(3ε) - Lₜ(ε) - 2⁵ Lₜ(2ε)`. -/
noncomputable def i10Y1 (ε : ℂ) : ℂ := 243 * i10Lt (3 * ε) - i10Lt (1 * ε) - 32 * i10Lt (2 * ε)

/-- `Y₂ = 2⁵ Lₜ(2ε) - 2 Lₜ(ε)`. -/
noncomputable def i10Y2 (ε : ℂ) : ℂ := 32 * i10Lt (2 * ε) - 2 * i10Lt (1 * ε)

/-- `Y₃ = -Lₜ(-ε) + 3⁵ Lₜ(3ε) - 2⁵ Lₜ(2ε)`. -/
noncomputable def i10Y3 (ε : ℂ) : ℂ :=
  -i10Lt ((-1) * ε) + 243 * i10Lt (3 * ε) - 32 * i10Lt (2 * ε)

/-- `Y₄ = -Lₜ(-ε) + 2⁵ Lₜ(2ε) - Lₜ(ε)`. -/
noncomputable def i10Y4 (ε : ℂ) : ℂ := -i10Lt ((-1) * ε) + 32 * i10Lt (2 * ε) - i10Lt (1 * ε)

/-- `Y₅ = 3⁵ Lₜ(3ε) - 3 Lₜ(ε)`. -/
noncomputable def i10Y5 (ε : ℂ) : ℂ := 243 * i10Lt (3 * ε) - 3 * i10Lt (1 * ε)

theorem i10E1_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i10E1 ε = cexp (ε ^ 2 * ((π : ℂ) ^ 2 / 3 + (-6 * (zeta3 : ℂ)) * ε +
      8 / 45 * (π : ℂ) ^ 4 * ε ^ 2 + ε ^ 3 * i10Y1 ε)) := by
  rw [i10E1, i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    ← Complex.exp_add, ← Complex.exp_sub, i10Y1]
  congr 1
  ring

theorem i10E2_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i10E2 ε = cexp (ε ^ 2 * ((π : ℂ) ^ 2 / 6 + (-2 * (zeta3 : ℂ)) * ε +
      7 / 180 * (π : ℂ) ^ 4 * ε ^ 2 + ε ^ 3 * i10Y2 ε)) := by
  rw [i10E2, i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    ← Complex.exp_add, ← Complex.exp_sub, i10Y2]
  congr 1
  ring

theorem i10E3_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i10E3 ε = cexp (ε ^ 2 * ((π : ℂ) ^ 2 / 2 + (-6 * (zeta3 : ℂ)) * ε +
      11 / 60 * (π : ℂ) ^ 4 * ε ^ 2 + ε ^ 3 * i10Y3 ε)) := by
  rw [i10E3, i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    ← Complex.exp_add, ← Complex.exp_sub, i10Y3]
  congr 1
  ring

theorem i10E4_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i10E4 ε = cexp (ε ^ 2 * ((π : ℂ) ^ 2 / 3 + (-2 * (zeta3 : ℂ)) * ε +
      2 / 45 * (π : ℂ) ^ 4 * ε ^ 2 + ε ^ 3 * i10Y4 ε)) := by
  rw [i10E4, i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    ← Complex.exp_add, ← Complex.exp_sub, i10Y4]
  congr 1
  ring

theorem i10E5_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i10E5 ε = cexp (ε ^ 2 * ((π : ℂ) ^ 2 / 2 + (-8 * (zeta3 : ℂ)) * ε +
      13 / 60 * (π : ℂ) ^ 4 * ε ^ 2 + ε ^ 3 * i10Y5 ε)) := by
  rw [i10E5, i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    i10_Gamma_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub, i10Y5]
  congr 1
  ring

/-! ### Truncations -/

/-- The truncation `1 + x₀ ε² + x₁ ε³ + (x₂ + x₀²/2) ε⁴` of `exp(ε² (x₀ + x₁ ε + x₂ ε² + …))`. -/
noncomputable def i10Ep (ε x₀ x₁ x₂ : ℂ) : ℂ :=
  1 + x₀ * ε ^ 2 + x₁ * ε ^ 3 + (x₂ + x₀ ^ 2 / 2) * ε ^ 4

/-- `(exp(ε² X) - E_p) / ε⁵` for `X = x₀ + x₁ ε + x₂ ε² + ε³ Y`, in terms of `E = expRem3(ε² X)`. -/
noncomputable def i10dE (ε x₀ x₁ x₂ Y E : ℂ) : ℂ :=
  Y + x₀ * x₁ + (x₁ ^ 2 / 2 + x₀ * x₂) * ε + x₁ * x₂ * ε ^ 2 + x₂ ^ 2 / 2 * ε ^ 3 +
    ε ^ 2 * (x₀ + x₁ * ε + x₂ * ε ^ 2) * Y + ε ^ 5 * Y ^ 2 / 2 +
    ε * (x₀ + x₁ * ε + x₂ * ε ^ 2 + ε ^ 3 * Y) ^ 3 * E

theorem i10_exp_trunc (ε x₀ x₁ x₂ Y : ℂ) :
    cexp (ε ^ 2 * (x₀ + x₁ * ε + x₂ * ε ^ 2 + ε ^ 3 * Y)) = i10Ep ε x₀ x₁ x₂ +
      ε ^ 5 * i10dE ε x₀ x₁ x₂ Y
        (QED.DimReg.expRem3 (ε ^ 2 * (x₀ + x₁ * ε + x₂ * ε ^ 2 + ε ^ 3 * Y))) := by
  rw [QED.DimReg.exp_eq_expRem3, i10Ep, i10dE]
  ring

theorem analyticAt_i10dE {x₀ x₁ x₂ : ℂ} {Y : ℂ → ℂ} (hY : AnalyticAt ℂ Y 0) :
    AnalyticAt ℂ (fun ε => i10dE ε x₀ x₁ x₂ (Y ε)
      (QED.DimReg.expRem3 (ε ^ 2 * (x₀ + x₁ * ε + x₂ * ε ^ 2 + ε ^ 3 * Y ε)))) 0 := by
  have hE : AnalyticAt ℂ
      (fun ε => QED.DimReg.expRem3 (ε ^ 2 * (x₀ + x₁ * ε + x₂ * ε ^ 2 + ε ^ 3 * Y ε))) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  unfold i10dE
  fun_prop

theorem analyticAt_i10Lt_mul (a : ℂ) : AnalyticAt ℂ (fun ε => i10Lt (a * ε)) 0 := by
  have h := analyticAt_logGammaRem_mul a
  unfold i10Lt
  fun_prop

/-! ### Truncations of the five ratios -/

/-- The truncation of `E₁` through `ε⁴`. -/
noncomputable def i10Ep1 (ε : ℂ) : ℂ :=
  i10Ep ε ((π : ℂ) ^ 2 / 3) (-6 * (zeta3 : ℂ)) (8 / 45 * (π : ℂ) ^ 4)

/-- `(E₁ - E_p) / ε⁵`. -/
noncomputable def i10d1 (ε : ℂ) : ℂ :=
  i10dE ε ((π : ℂ) ^ 2 / 3) (-6 * (zeta3 : ℂ)) (8 / 45 * (π : ℂ) ^ 4) (i10Y1 ε)
    (QED.DimReg.expRem3 (ε ^ 2 * (((π : ℂ) ^ 2 / 3) + (-6 * (zeta3 : ℂ)) * ε +
      (8 / 45 * (π : ℂ) ^ 4) * ε ^ 2 + ε ^ 3 * i10Y1 ε)))

theorem i10E1_trunc {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i10E1 ε = i10Ep1 ε + ε ^ 5 * i10d1 ε := by
  rw [i10E1_eq hε]
  exact i10_exp_trunc ..

theorem analyticAt_i10d1 : AnalyticAt ℂ i10d1 0 := by
  have h1 := analyticAt_i10Lt_mul 1
  have h2 := analyticAt_i10Lt_mul 2
  have h3 := analyticAt_i10Lt_mul 3
  have hm := analyticAt_i10Lt_mul (-1)
  exact analyticAt_i10dE (by unfold i10Y1; fun_prop)

/-- The truncation of `E₂` through `ε⁴`. -/
noncomputable def i10Ep2 (ε : ℂ) : ℂ :=
  i10Ep ε ((π : ℂ) ^ 2 / 6) (-2 * (zeta3 : ℂ)) (7 / 180 * (π : ℂ) ^ 4)

/-- `(E₂ - E_p) / ε⁵`. -/
noncomputable def i10d2 (ε : ℂ) : ℂ :=
  i10dE ε ((π : ℂ) ^ 2 / 6) (-2 * (zeta3 : ℂ)) (7 / 180 * (π : ℂ) ^ 4) (i10Y2 ε)
    (QED.DimReg.expRem3 (ε ^ 2 * (((π : ℂ) ^ 2 / 6) + (-2 * (zeta3 : ℂ)) * ε +
      (7 / 180 * (π : ℂ) ^ 4) * ε ^ 2 + ε ^ 3 * i10Y2 ε)))

theorem i10E2_trunc {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i10E2 ε = i10Ep2 ε + ε ^ 5 * i10d2 ε := by
  rw [i10E2_eq hε]
  exact i10_exp_trunc ..

theorem analyticAt_i10d2 : AnalyticAt ℂ i10d2 0 := by
  have h1 := analyticAt_i10Lt_mul 1
  have h2 := analyticAt_i10Lt_mul 2
  have h3 := analyticAt_i10Lt_mul 3
  have hm := analyticAt_i10Lt_mul (-1)
  exact analyticAt_i10dE (by unfold i10Y2; fun_prop)

/-- The truncation of `E₃` through `ε⁴`. -/
noncomputable def i10Ep3 (ε : ℂ) : ℂ :=
  i10Ep ε ((π : ℂ) ^ 2 / 2) (-6 * (zeta3 : ℂ)) (11 / 60 * (π : ℂ) ^ 4)

/-- `(E₃ - E_p) / ε⁵`. -/
noncomputable def i10d3 (ε : ℂ) : ℂ :=
  i10dE ε ((π : ℂ) ^ 2 / 2) (-6 * (zeta3 : ℂ)) (11 / 60 * (π : ℂ) ^ 4) (i10Y3 ε)
    (QED.DimReg.expRem3 (ε ^ 2 * (((π : ℂ) ^ 2 / 2) + (-6 * (zeta3 : ℂ)) * ε +
      (11 / 60 * (π : ℂ) ^ 4) * ε ^ 2 + ε ^ 3 * i10Y3 ε)))

theorem i10E3_trunc {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i10E3 ε = i10Ep3 ε + ε ^ 5 * i10d3 ε := by
  rw [i10E3_eq hε]
  exact i10_exp_trunc ..

theorem analyticAt_i10d3 : AnalyticAt ℂ i10d3 0 := by
  have h1 := analyticAt_i10Lt_mul 1
  have h2 := analyticAt_i10Lt_mul 2
  have h3 := analyticAt_i10Lt_mul 3
  have hm := analyticAt_i10Lt_mul (-1)
  exact analyticAt_i10dE (by unfold i10Y3; fun_prop)

/-- The truncation of `E₄` through `ε⁴`. -/
noncomputable def i10Ep4 (ε : ℂ) : ℂ :=
  i10Ep ε ((π : ℂ) ^ 2 / 3) (-2 * (zeta3 : ℂ)) (2 / 45 * (π : ℂ) ^ 4)

/-- `(E₄ - E_p) / ε⁵`. -/
noncomputable def i10d4 (ε : ℂ) : ℂ :=
  i10dE ε ((π : ℂ) ^ 2 / 3) (-2 * (zeta3 : ℂ)) (2 / 45 * (π : ℂ) ^ 4) (i10Y4 ε)
    (QED.DimReg.expRem3 (ε ^ 2 * (((π : ℂ) ^ 2 / 3) + (-2 * (zeta3 : ℂ)) * ε +
      (2 / 45 * (π : ℂ) ^ 4) * ε ^ 2 + ε ^ 3 * i10Y4 ε)))

theorem i10E4_trunc {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i10E4 ε = i10Ep4 ε + ε ^ 5 * i10d4 ε := by
  rw [i10E4_eq hε]
  exact i10_exp_trunc ..

theorem analyticAt_i10d4 : AnalyticAt ℂ i10d4 0 := by
  have h1 := analyticAt_i10Lt_mul 1
  have h2 := analyticAt_i10Lt_mul 2
  have h3 := analyticAt_i10Lt_mul 3
  have hm := analyticAt_i10Lt_mul (-1)
  exact analyticAt_i10dE (by unfold i10Y4; fun_prop)

/-- The truncation of `E₅` through `ε⁴`. -/
noncomputable def i10Ep5 (ε : ℂ) : ℂ :=
  i10Ep ε ((π : ℂ) ^ 2 / 2) (-8 * (zeta3 : ℂ)) (13 / 60 * (π : ℂ) ^ 4)

/-- `(E₅ - E_p) / ε⁵`. -/
noncomputable def i10d5 (ε : ℂ) : ℂ :=
  i10dE ε ((π : ℂ) ^ 2 / 2) (-8 * (zeta3 : ℂ)) (13 / 60 * (π : ℂ) ^ 4) (i10Y5 ε)
    (QED.DimReg.expRem3 (ε ^ 2 * (((π : ℂ) ^ 2 / 2) + (-8 * (zeta3 : ℂ)) * ε +
      (13 / 60 * (π : ℂ) ^ 4) * ε ^ 2 + ε ^ 3 * i10Y5 ε)))

theorem i10E5_trunc {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i10E5 ε = i10Ep5 ε + ε ^ 5 * i10d5 ε := by
  rw [i10E5_eq hε]
  exact i10_exp_trunc ..

theorem analyticAt_i10d5 : AnalyticAt ℂ i10d5 0 := by
  have h1 := analyticAt_i10Lt_mul 1
  have h2 := analyticAt_i10Lt_mul 2
  have h3 := analyticAt_i10Lt_mul 3
  have hm := analyticAt_i10Lt_mul (-1)
  exact analyticAt_i10dE (by unfold i10Y5; fun_prop)

/-! ### The polynomial identity -/

/-- `ε³` times the Laurent polynomial of `I₁₀ C⁻¹`. -/
noncomputable def i10L3e (ε : ℂ) : ℂ :=
  -1 / 3 - 5 / 3 * ε + (-2 / 3 * (π : ℂ) ^ 2 - 4) * ε ^ 2 +
    (-7 / 3 * (π : ℂ) ^ 2 - 26 / 3 * (zeta3 : ℂ) + 10 / 3) * ε ^ 3 +
    (-35 / 18 * (π : ℂ) ^ 4 - (π : ℂ) ^ 2 - 94 / 3 * (zeta3 : ℂ) + 302 / 3) * ε ^ 4

/-- The polynomial `(Σ Pᵢ E_{p,i} + P₅ E_{p,5} Rest_L - ε³ L Den) / ε⁵`
(generated by `scripts/numerics/three_loop_masters/i10gen.py`). -/
noncomputable def i10WireP (ε : ℂ) : ℂ :=
  (141 / 8 * (π : ℂ) ^ 4 + 14 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 97 / 6 * (π : ℂ) ^ 2
    + 332 * (zeta3 : ℂ) - 891)
  + (185 / 72 * (π : ℂ) ^ 6 - 9857 / 360 * (π : ℂ) ^ 4 - 53 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    - 122 * (π : ℂ) ^ 2 - 352 * (zeta3 : ℂ) ^ 2 + 98 * (zeta3 : ℂ) + 910) * ε
  + (-329 / 144 * (π : ℂ) ^ 6 - 371 / 18 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 4679 / 180 * (π : ℂ) ^ 4
    + 115 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 475 / 3 * (π : ℂ) ^ 2 + 304 * (zeta3 : ℂ) ^ 2
    + 1476 * (zeta3 : ℂ) + 893) * ε ^ 2
  + (16441 / 10800 * (π : ℂ) ^ 8 - 5909 / 720 * (π : ℂ) ^ 6
    + 4079 / 180 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 5971 / 120 * (π : ℂ) ^ 4
    - 323 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 124 * (π : ℂ) ^ 2 + 400 * (zeta3 : ℂ) ^ 2
    - 2358 * (zeta3 : ℂ) - 906) * ε ^ 3
  + (-16441 / 10800 * (π : ℂ) ^ 8 + 611 / 80 * (π : ℂ) ^ 6
    + 3341 / 180 * (π : ℂ) ^ 4 * (zeta3 : ℂ) + 1259 / 12 * (π : ℂ) ^ 4
    - 129 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 285 / 2 * (π : ℂ) ^ 2 - 304 * (zeta3 : ℂ) ^ 2
    - 1840 * (zeta3 : ℂ)) * ε ^ 4
  + (-16441 / 10800 * (π : ℂ) ^ 8 + 451 / 80 * (π : ℂ) ^ 6
    - 4079 / 180 * (π : ℂ) ^ 4 * (zeta3 : ℂ) + 943 / 12 * (π : ℂ) ^ 4
    + 376 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 48 * (zeta3 : ℂ) ^ 2 + 2280 * (zeta3 : ℂ)) * ε ^ 5
  + (16441 / 10800 * (π : ℂ) ^ 8 - 1927 / 360 * (π : ℂ) ^ 6
    + 41 / 20 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 779 / 8 * (π : ℂ) ^ 4) * ε ^ 6

/-- **The polynomial identity behind the expansion of `I₁₀`**: the orders `ε⁰` to `ε⁴` of
`Σ Pᵢ E_{p,i} + P₅ E_{p,5} Rest_L` are those of `ε³ L₁₀ Den`. -/
theorem i10Wire_key (ε : ℂ) :
    i10P1 ε * i10Ep1 ε + i10P2 ε * i10Ep2 ε + i10P3 ε * i10Ep3 ε + i10P4 ε * i10Ep4 ε +
      ε * i10P5 ε * i10Ep5 ε * i10RestLaurent ε - i10L3e ε * i10Den ε =
      ε ^ 5 * i10WireP ε := by
  simp only [i10P1, i10P2, i10P3, i10P4, i10P5, i10Ep1, i10Ep2, i10Ep3, i10Ep4, i10Ep5, i10Ep,
    i10RestLaurent, i10L3e, i10Den,
    i10WireP]
  ring

/-! ### The expansion -/

/-- **The set (e) input for `I₁₀` from the expansion of the remainder**: if
`Rest = Rest_L + ε⁴ R` with `R` analytic at `0`, then `I₁₀ C⁻¹ = L₁₀ + ε² R₁₀` with `R₁₀`
analytic at `0`, `L₁₀ = setELaurentI10` the LR96 table entry through `ε`. -/
theorem hasTruncLaurent_setEMasterI10_of_rest
    (hR : HasTruncLaurent i10Rest i10RestLaurent 4) :
    HasTruncLaurent setEMasterI10 setELaurentI10 2 := by
  obtain ⟨RR, hRR, hRe⟩ := hR
  refine ⟨fun ε => (i10WireP ε + i10P1 ε * i10d1 ε + i10P2 ε * i10d2 ε + i10P3 ε * i10d3 ε +
    i10P4 ε * i10d4 ε + ε * i10P5 ε * i10d5 ε * i10RestLaurent ε +
    i10P5 ε * (i10Ep5 ε + ε ^ 5 * i10d5 ε) * RR ε) / i10Den ε, ?_, ?_⟩
  · have hd1 := analyticAt_i10d1
    have hd2 := analyticAt_i10d2
    have hd3 := analyticAt_i10d3
    have hd4 := analyticAt_i10d4
    have hd5 := analyticAt_i10d5
    have hp5 : AnalyticAt ℂ i10Ep5 0 := by unfold i10Ep5 i10Ep; fun_prop
    have hW : AnalyticAt ℂ i10WireP 0 := by unfold i10WireP; fun_prop
    have hRL : AnalyticAt ℂ i10RestLaurent 0 := by unfold i10RestLaurent; fun_prop
    have hP1 : AnalyticAt ℂ i10P1 0 := by unfold i10P1; fun_prop
    have hP2 : AnalyticAt ℂ i10P2 0 := by unfold i10P2; fun_prop
    have hP3 : AnalyticAt ℂ i10P3 0 := by unfold i10P3; fun_prop
    have hP4 : AnalyticAt ℂ i10P4 0 := by unfold i10P4; fun_prop
    have hP5 : AnalyticAt ℂ i10P5 0 := by unfold i10P5; fun_prop
    have hD : AnalyticAt ℂ i10Den 0 := by unfold i10Den; fun_prop
    refine AnalyticAt.div (by fun_prop) hD ?_
    norm_num [i10Den]
  filter_upwards [setDGamma_eventually_small, hRe, self_mem_nhdsWithin] with ε hε hRε h0
  have h0 : ε ≠ 0 := h0
  have hD := i10Den_ne_zero hε
  have hL : setELaurentI10 ε = i10L3e ε / ε ^ 3 := by
    simp only [setELaurentI10, i10L3e]
    field_simp
    ring
  have key := i10Wire_key ε
  rw [setEMasterI10_eq h0 hε, i10E1_trunc hε, i10E2_trunc hε, i10E3_trunc hε, i10E4_trunc hε,
    i10E5_trunc hε, hRε, hL]
  generalize i10d1 ε = D1
  generalize i10d2 ε = D2
  generalize i10d3 ε = D3
  generalize i10d4 ε = D4
  generalize i10d5 ε = D5
  generalize i10Ep1 ε = Q1 at *
  generalize i10Ep2 ε = Q2 at *
  generalize i10Ep3 ε = Q3 at *
  generalize i10Ep4 ε = Q4 at *
  generalize i10Ep5 ε = Q5 at *
  generalize i10P1 ε = P1 at *
  generalize i10P2 ε = P2 at *
  generalize i10P3 ε = P3 at *
  generalize i10P4 ε = P4 at *
  generalize i10P5 ε = P5 at *
  generalize i10Den ε = Dn at *
  generalize i10RestLaurent ε = RL at *
  generalize i10L3e ε = L at *
  generalize i10WireP ε = W at *
  generalize RR ε = R at *
  field_simp
  linear_combination key

end QED.ThreeLoopE
