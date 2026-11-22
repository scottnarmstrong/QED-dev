/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12Def
public import QED.ThreeLoopD.SetDMastersI12Poly
public import QED.DimReg.GammaTaylor
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₁₂`: the input from the expansion of the remainder combination

`I₁₂ C⁻¹ = Γ(3ε - 2) / Γ(1 + ε)³ · (i12Closed + Rest / ε)` (`QED.ThreeLoopD.setDMasterI12`).
This file expands everything except `Rest = QED.ThreeLoopD.i12Rest`.

**The closed part.** Writing every `Γ` at `1 + aε` and `2 ^ z = exp(z ln 2)`, the four
powers of two in `i12Closed` combine to `4 ^ ε` and `4 ^ (-ε)`, and
(`QED.ThreeLoopD.setDMasterI12_eq`)

  `ε³ D(ε) I₁₂ C⁻¹ = K₁ N₁ + K₂ N₂ + (K₃ 4 ^ ε + K₄ 4 ^ (-ε)) N₃ + D_c ε Rest K₀`,

with the polynomials `N₁, N₂, N₃, D_c, D` of `QED.ThreeLoopD.SetDMastersI12Poly` and the
`Γ`-ratios `K₀ = Γ(1 + 3ε) / Γ(1 + ε)³`,
`K₁ = Γ(1 + 3ε) Γ(1 + 2ε)² Γ(1 - ε) / (Γ(1 + ε)² Γ(1 + 4ε))`,
`K₂ = Γ(1 + 3ε) Γ(1 - ε)² Γ(1 + 2ε) / Γ(1 + ε)³`, `K₃ = Γ(1 + 3ε) Γ(1 - 2ε) / (Γ(1 + ε)² Γ(1 - ε))`,
`K₄ = Γ(1 + 3ε) Γ(1 - 2ε) / Γ(1 + ε)`. In each the arguments sum to zero, so by
`QED.DimReg.Gamma_one_add_eq_exp` each is `exp(ε² (Xⱼ + ε⁴ Vⱼ))` with `Xⱼ` an explicit cubic and
`Vⱼ` analytic; `γ` cancels.

**The wiring.** Given the expansion of the remainder combination
(`QED.ThreeLoopD.i12RestLaurent`, coefficients identified numerically by PSLQ and confirmed
exactly by the identity `QED.ThreeLoopD.i12_key`)

  `Rest = (-71/6 - 11π²/3 - 8 ln²2) ε + … + O(ε⁵)`,

the truncations reproduce `setDLaurentI12` through `ε²`, giving the set (d) input for `I₁₂`
(`QED.ThreeLoopD.hasTruncLaurent_setDMasterI12_of_rest`). The expansion of `Rest` is the
hypothesis that remains.

## Main results

* `QED.ThreeLoopD.setDMasterI12_eq`, `QED.ThreeLoopD.hasTruncLaurent_setDMasterI12_of_rest`.
-/

@[expose] public section

open Complex Filter Topology QED.Polylog
open scoped Real

namespace QED.ThreeLoopD

/-! ### The target expansion of the remainder combination -/

/-- **The target expansion of `Rest`** through `ε⁴`. -/
noncomputable def i12RestLaurent (ε : ℂ) : ℂ :=
  (-11 / 3 * (π : ℂ) ^ 2 - 8 * (Real.log 2 : ℂ) ^ 2 - 71 / 6) * ε + (2 / 3 * (π : ℂ) ^ 2 *
    (Real.log 2 : ℂ) + 17 / 6 * (π : ℂ) ^ 2 + 8 * (zeta3 : ℂ) + 4 * (Real.log 2 : ℂ) ^ 2 + 179 / 36)
    * ε ^ 2 + (-7 / 60 * (π : ℂ) ^ 4 - 10 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 1 / 3 * (π : ℂ)
    ^ 2 * (Real.log 2 : ℂ) - 401 / 12 * (π : ℂ) ^ 2 + 2 * (zeta3 : ℂ) - 8 / 3 * (Real.log 2 : ℂ) ^ 4
    + 4 * (Real.log 2 : ℂ) ^ 2 + 47233 / 216) * ε ^ 3 + (3 / 10 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) -
    19 / 40 * (π : ℂ) ^ 4 - 34 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 4 / 9 * (π : ℂ) ^ 2 * (Real.log 2 :
    ℂ) ^ 3 + 5 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 1535 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
    - 7447 / 24 * (π : ℂ) ^ 2 - 16 * (zeta3 : ℂ) * (Real.log 2 : ℂ) ^ 2 - 3709 / 3 * (zeta3 : ℂ) -
    120 * (zeta5 : ℂ) + 4 / 3 * (Real.log 2 : ℂ) ^ 4 + 4 * (Real.log 2 : ℂ) ^ 2 + 1810835 / 1296) *
    ε ^ 4

theorem i12RestLaurent_eq (ε : ℂ) :
    i12RestLaurent ε = i12PolyRL (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) (Real.log 2 : ℂ) ε := by
  simp only [i12RestLaurent, i12PolyRL]

theorem setDLaurentI12_eq {ε : ℂ} (h0 : ε ≠ 0) :
    setDLaurentI12 ε = i12PolyLe (π : ℂ) (zeta3 : ℂ) (Real.log 2 : ℂ) ε / ε ^ 3 := by
  simp only [setDLaurentI12, i12PolyLe]
  field_simp
  ring

/-! ### The `Γ`-ratios -/

/-- `K₀ = Γ(1 + 3ε) / Γ(1 + ε)³`. -/
noncomputable def i12K0 (ε : ℂ) : ℂ := Gamma (1 + 3 * ε) / Gamma (1 + 1 * ε) ^ 3

/-- `K₁ = Γ(1 + 3ε) Γ(1 + 2ε)² Γ(1 - ε) / (Γ(1 + ε)² Γ(1 + 4ε))`. -/
noncomputable def i12K1 (ε : ℂ) : ℂ :=
  Gamma (1 + 3 * ε) * Gamma (1 + 2 * ε) ^ 2 * Gamma (1 + (-1) * ε) /
    (Gamma (1 + 1 * ε) ^ 2 * Gamma (1 + 4 * ε))

/-- `K₂ = Γ(1 + 3ε) Γ(1 - ε)² Γ(1 + 2ε) / Γ(1 + ε)³`. -/
noncomputable def i12K2 (ε : ℂ) : ℂ :=
  Gamma (1 + 3 * ε) * Gamma (1 + (-1) * ε) ^ 2 * Gamma (1 + 2 * ε) / Gamma (1 + 1 * ε) ^ 3

/-- `K₃ = Γ(1 + 3ε) Γ(1 - 2ε) / (Γ(1 + ε)² Γ(1 - ε))`. -/
noncomputable def i12K3 (ε : ℂ) : ℂ :=
  Gamma (1 + 3 * ε) * Gamma (1 + (-2) * ε) / (Gamma (1 + 1 * ε) ^ 2 * Gamma (1 + (-1) * ε))

/-- `K₄ = Γ(1 + 3ε) Γ(1 - 2ε) / Γ(1 + ε)`. -/
noncomputable def i12K4 (ε : ℂ) : ℂ := Gamma (1 + 3 * ε) * Gamma (1 + (-2) * ε) / Gamma (1 + 1 * ε)

/-! ### `I₁₂ C⁻¹` in terms of the `Γ`-ratios -/

theorem i12_log_two : Complex.log 2 = (Real.log 2 : ℂ) := by
  rw [ofReal_log zero_le_two, ofReal_ofNat]

theorem i12_two_cpow (z : ℂ) : (2 : ℂ) ^ z = exp ((Real.log 2 : ℂ) * z) := by
  rw [cpow_def_of_ne_zero two_ne_zero, i12_log_two]

theorem i12_four_cpow (z : ℂ) : (4 : ℂ) ^ z = exp (2 * (Real.log 2 : ℂ) * z) := by
  rw [cpow_def_of_ne_zero (by norm_num), show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
    ← ofReal_log (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring_nf

theorem i12_two_cpow_one_sub (ε : ℂ) :
    (2 : ℂ) ^ (1 - 2 * ε) = 2 * exp (-2 * (Real.log 2 : ℂ) * ε) := by
  rw [i12_two_cpow, show (Real.log 2 : ℂ) * (1 - 2 * ε) = Complex.log 2 + -2 * (Real.log 2 : ℂ) * ε
    by rw [i12_log_two]; ring, Complex.exp_add, Complex.exp_log two_ne_zero]

theorem i12_two_cpow_one_add (ε : ℂ) :
    (2 : ℂ) ^ (1 + ε) = 2 * exp ((Real.log 2 : ℂ) * ε) := by
  rw [i12_two_cpow, show (Real.log 2 : ℂ) * (1 + ε) = Complex.log 2 + (Real.log 2 : ℂ) * ε
    by rw [i12_log_two]; ring, Complex.exp_add, Complex.exp_log two_ne_zero]

/-- **`I₁₂ C⁻¹` from the `Γ`-ratios and the remainder combination.** -/
theorem setDMasterI12_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setDMasterI12 ε = (i12K1 ε * i12N1 ε + i12K2 ε * i12N2 ε +
      (i12K3 ε * exp (2 * (Real.log 2 : ℂ) * ε) + i12K4 ε * exp (-2 * (Real.log 2 : ℂ) * ε)) *
        i12N3 ε + i12Dc ε * ε * i12Rest ε * i12K0 ε) / (ε ^ 3 * i12D ε) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have hm := fun a ha {x : ℂ} (hx : x = a * ε) => setDGamma_mul_ne_zero h0 a ha hx
  have g1 : Gamma (2 * ε - 1) = Gamma (1 + 2 * ε) / ((2 * ε - 1 + 1) * (2 * ε - 1)) :=
    Gamma_eq_div_two (hl (-1) 2 (by norm_num) (by norm_num) (by ring))
      (hm 2 two_ne_zero (by ring)) (by ring) rfl
  have g2 : Gamma (2 * ε - 1 + (2 * ε - 1)) = Gamma (1 + 4 * ε) /
      ((4 * ε) * (4 * ε - 1) * (4 * ε - 2)) :=
    Gamma_eq_div_three (hl (-2) 4 (by norm_num) (by norm_num) (by ring))
      (hl (-1) 4 (by norm_num) (by norm_num) (by ring)) (hm 4 (by norm_num) (by ring)) (by ring)
      (by ring)
  have g3 : Gamma (1 - ε) = Gamma (1 + (-1) * ε) := congrArg Gamma (by ring)
  have g4 : Gamma (1 - ε + (1 - ε)) = (1 - 2 * ε) * Gamma (1 + (-2) * ε) := by
    rw [show 1 - ε + (1 - ε) = 1 + (-2) * ε + 1 by ring,
      Gamma_add_one _ (hl 1 (-2) (by norm_num) (by norm_num) rfl)]
    ring
  have g5 : Gamma (2 - 2 * ε) = (1 - 2 * ε) * Gamma (1 + (-2) * ε) := by
    rw [show 2 - 2 * ε = 1 + (-2) * ε + 1 by ring,
      Gamma_add_one _ (hl 1 (-2) (by norm_num) (by norm_num) rfl)]
    ring
  have g6 : Gamma ε = Gamma (1 + 1 * ε) / ε := Gamma_eq_div_one h0 (by ring) rfl
  have g7 : Gamma (2 - 2 * ε + ε) = (1 - ε) * Gamma (1 + (-1) * ε) := by
    rw [show 2 - 2 * ε + ε = 1 + (-1) * ε + 1 by ring,
      Gamma_add_one _ (hl 1 (-1) (by norm_num) (by norm_num) rfl)]
    ring
  have g8 : Gamma (2 * ε - 1 + (1 - ε)) = Gamma (1 + 1 * ε) / ε := by
    rw [show 2 * ε - 1 + (1 - ε) = ε by ring, g6]
  have g9 : Gamma (ε + (2 - 2 * ε)) = (1 - ε) * Gamma (1 + (-1) * ε) := by
    rw [show ε + (2 - 2 * ε) = 2 - 2 * ε + ε by ring, g7]
  have g10 : Gamma (2 * ε) = Gamma (1 + 2 * ε) / (2 * ε) :=
    Gamma_eq_div_one (hm 2 two_ne_zero rfl) (by ring) rfl
  have g11 : Gamma (2 * ε + 2 * ε) = Gamma (1 + 4 * ε) / (4 * ε) :=
    Gamma_eq_div_one (hm 4 (by norm_num) (by ring)) (by ring) (by ring)
  have g12 : Gamma (1 + ε) = Gamma (1 + 1 * ε) := congrArg Gamma (by ring)
  have g13 : Gamma (2 - 2 * ε + (1 + ε)) = (2 - ε) * ((1 - ε) * Gamma (1 + (-1) * ε)) := by
    rw [show 2 - 2 * ε + (1 + ε) = 2 - 2 * ε + ε + 1 by ring,
      Gamma_add_one _ (hl 2 (-1) (by norm_num) (by norm_num) (by ring)), g7]
    ring
  have g14 : Gamma (2 * ε + (1 - ε)) = Gamma (1 + 1 * ε) := congrArg Gamma (by ring)
  have g15 : Gamma (1 + ε + (2 - 2 * ε)) = (2 - ε) * ((1 - ε) * Gamma (1 + (-1) * ε)) := by
    rw [show 1 + ε + (2 - 2 * ε) = 2 - 2 * ε + (1 + ε) by ring, g13]
  have g16 : Gamma (1 - 2 * ε) = Gamma (1 + (-2) * ε) := congrArg Gamma (by ring)
  have g17 : Gamma (1 + ε + (1 - 2 * ε)) = (1 - ε) * Gamma (1 + (-1) * ε) := by
    rw [show 1 + ε + (1 - 2 * ε) = 2 - 2 * ε + ε by ring, g7]
  have g18 : Gamma (1 - 2 * ε + (1 + ε)) = (1 - ε) * Gamma (1 + (-1) * ε) := by
    rw [show 1 - 2 * ε + (1 + ε) = 2 - 2 * ε + ε by ring, g7]
  have g19 : Gamma (ε + (1 - ε)) = 1 := by rw [show ε + (1 - ε) = 1 by ring, Gamma_one]
  have g20 : Gamma (3 * ε - 2) = Gamma (1 + 3 * ε) / ((3 * ε) * (3 * ε - 1) * (3 * ε - 2)) :=
    Gamma_eq_div_three (hl (-2) 3 (by norm_num) (by norm_num) (by ring))
      (hl (-1) 3 (by norm_num) (by norm_num) (by ring)) (hm 3 (by norm_num) (by ring)) (by ring)
      (by ring)
  simp only [setDMasterI12, lr96I12, lr96C, i12Bracket, i12Closed, i9Beta,
    QED.DimReg.lr96LoopFactor_four_sub, i12K0, i12K1, i12K2, i12K3, i12K4, i12N1, i12N2, i12N3,
    i12D, i12Dc]
  rw [g2, g4, g7, g8, g9, g11, g13, g14, g15, g17, g18, g19, g1, g3, g5, g6, g10, g12, g16, g20,
    i12_four_cpow, i12_two_cpow_one_sub, i12_two_cpow_one_add, i12_two_cpow]
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hA := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hB := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-1) (by norm_num))
  have hC := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 2 (by norm_num))
  have hD := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-2) (by norm_num))
  have hE := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 4 (by norm_num))
  have n1 := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
  have n2 := hl (-1) 4 (by norm_num) (by norm_num) (x := 4 * ε - 1) (by ring)
  have n3 := hl (-2) 4 (by norm_num) (by norm_num) (x := 4 * ε - 2) (by ring)
  have n4 := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
  have n5 := hl (-2) 3 (by norm_num) (by norm_num) (x := 3 * ε - 2) (by ring)
  have n6 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have n7 := hl 2 (-1) (by norm_num) (by norm_num) (x := 2 - ε) (by ring)
  have n8 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have n9 : 2 * ε - 1 + 1 ≠ 0 := by
    rw [show 2 * ε - 1 + 1 = 2 * ε by ring]; exact hm 2 two_ne_zero rfl
  have n10 : 1 - ε * 4 + ε ^ 2 * 4 ≠ 0 := by
    rw [show 1 - ε * 4 + ε ^ 2 * 4 = (2 * ε - 1) ^ 2 by ring]; exact pow_ne_zero 2 n1
  have n11 : 1 - ε * 2 ≠ 0 := by rw [show 1 - ε * 2 = 1 - 2 * ε by ring]; exact n8
  have n12 : ε * 2 - 1 ≠ 0 := by rw [show ε * 2 - 1 = 2 * ε - 1 by ring]; exact n1
  generalize Gamma (1 + 1 * ε) = A at *
  generalize Gamma (1 + (-1) * ε) = B at *
  generalize Gamma (1 + 2 * ε) = C at *
  generalize Gamma (1 + (-2) * ε) = D at *
  generalize Gamma (1 + 4 * ε) = E at *
  generalize Gamma (1 + 3 * ε) = F at *
  generalize (π : ℂ) ^ ε = P at *
  generalize i12Rest ε = Rs
  generalize exp ((Real.log 2 : ℂ) * ε) = e1
  generalize exp (2 * (Real.log 2 : ℂ) * ε) = e2
  generalize exp (-2 * (Real.log 2 : ℂ) * ε) = e3
  field_simp
  ring

/-! ### The `Γ`-ratios as exponentials -/

/-- `Vⱼ = ∑ nᵢ aᵢ⁶ R(aᵢ ε)`, the analytic remainders of the exponents. -/
noncomputable def i12V0 (ε : ℂ) : ℂ :=
  3 ^ 6 * QED.DimReg.logGammaRem (3 * ε) - 3 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε)

@[inherit_doc i12V0]
noncomputable def i12V1 (ε : ℂ) : ℂ :=
  3 ^ 6 * QED.DimReg.logGammaRem (3 * ε) + 2 * 2 ^ 6 * QED.DimReg.logGammaRem (2 * ε) +
    (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε) - 2 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) -
    4 ^ 6 * QED.DimReg.logGammaRem (4 * ε)

@[inherit_doc i12V0]
noncomputable def i12V2 (ε : ℂ) : ℂ :=
  3 ^ 6 * QED.DimReg.logGammaRem (3 * ε) + 2 * (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε) +
    2 ^ 6 * QED.DimReg.logGammaRem (2 * ε) - 3 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε)

@[inherit_doc i12V0]
noncomputable def i12V3 (ε : ℂ) : ℂ :=
  3 ^ 6 * QED.DimReg.logGammaRem (3 * ε) + (-2) ^ 6 * QED.DimReg.logGammaRem ((-2) * ε) -
    2 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) - (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε)

@[inherit_doc i12V0]
noncomputable def i12V4 (ε : ℂ) : ℂ :=
  3 ^ 6 * QED.DimReg.logGammaRem (3 * ε) + (-2) ^ 6 * QED.DimReg.logGammaRem ((-2) * ε) -
    1 ^ 6 * QED.DimReg.logGammaRem (1 * ε)

theorem i12_exp_pow (x : ℂ) (n : ℕ) : exp x ^ n = exp (n * x) := (Complex.exp_nat_mul x n).symm

theorem i12K0_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i12K0 ε = exp (ε ^ 2 *
    (i12PolyX0 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε + ε ^ 4 * i12V0 ε)) := by
  rw [i12K0, QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num))]
  simp only [i12_exp_pow, ← Complex.exp_sub]
  congr 1
  simp only [i12PolyX0, i12V0]
  push_cast
  ring

theorem i12K1_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i12K1 ε = exp (ε ^ 2 *
    (i12PolyX1 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε + ε ^ 4 * i12V1 ε)) := by
  rw [i12K1, QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 4 (by norm_num))]
  simp only [i12_exp_pow, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  simp only [i12PolyX1, i12V1]
  push_cast
  ring

theorem i12K2_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i12K2 ε = exp (ε ^ 2 *
    (i12PolyX2 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε + ε ^ 4 * i12V2 ε)) := by
  rw [i12K2, QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num))]
  simp only [i12_exp_pow, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  simp only [i12PolyX2, i12V2]
  push_cast
  ring

theorem i12K3_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i12K3 ε = exp (ε ^ 2 *
    (i12PolyX3 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε + ε ^ 4 * i12V3 ε)) := by
  rw [i12K3, QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-2) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num))]
  simp only [i12_exp_pow, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  simp only [i12PolyX3, i12V3]
  push_cast
  ring

theorem i12K4_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i12K4 ε = exp (ε ^ 2 *
    (i12PolyX4 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε + ε ^ 4 * i12V4 ε)) := by
  rw [i12K4, QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-2) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num))]
  simp only [← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  simp only [i12PolyX4, i12V4]
  ring

/-! ### Truncated exponentials -/

/-- `(exp(ε² (X + ε⁴ V)) - 1 - ε² X - ε⁴ X² / 2) / ε⁶`. -/
noncomputable def i12ExpT (ε X V : ℂ) : ℂ :=
  V + ε ^ 2 * X * V + ε ^ 6 * V ^ 2 / 2 +
    (X + ε ^ 4 * V) ^ 3 * QED.DimReg.expRem3 (ε ^ 2 * (X + ε ^ 4 * V))

theorem exp_eq_i12ExpT (ε X V : ℂ) :
    exp (ε ^ 2 * (X + ε ^ 4 * V)) = i12PolyKH X ε + ε ^ 6 * i12ExpT ε X V := by
  rw [QED.DimReg.exp_eq_expRem3, i12ExpT, i12PolyKH]
  ring

/-- The remainder of `exp` after `w ^ 5`, divided by `w ^ 6`. -/
noncomputable def i12ExpRem6 (w : ℂ) : ℂ := ∑' m : ℕ, 1 / ((m + 6).factorial : ℂ) * w ^ m

theorem analyticAt_i12ExpRem6 : AnalyticAt ℂ i12ExpRem6 0 := by
  refine QED.DimReg.analyticAt_tsum_mul_pow (C := 1) fun m => ?_
  rw [norm_div, norm_one, Complex.norm_natCast]
  exact div_le_one_of_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    (by positivity)

theorem exp_eq_i12ExpRem6 (w : ℂ) : exp w = 1 + w + w ^ 2 / 2 + w ^ 3 / 6 + w ^ 4 / 24 +
    w ^ 5 / 120 + w ^ 6 * i12ExpRem6 w := by
  have h : HasSum (fun n => w ^ n / (n.factorial : ℂ)) (exp w) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp w
  rw [← h.tsum_eq, ← h.summable.sum_add_tsum_nat_add 6, i12ExpRem6, ← tsum_mul_left]
  congr 1
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
  · congr 1
    funext m
    rw [pow_add]
    ring

theorem exp_mul_eq_i12 (c ε : ℂ) :
    exp (c * ε) = i12PolyEH c ε + ε ^ 6 * (c ^ 6 * i12ExpRem6 (c * ε)) := by
  rw [exp_eq_i12ExpRem6, i12PolyEH]
  ring

/-! ### The wiring -/

/-- The tail `(Σ - Σ̂) / ε⁶` of the numerator, in variables. -/
noncomputable def i12Tail (p a b l e T0 T1 T2 T3 T4 Qp Qm R : ℂ) : ℂ :=
  T1 * i12N1 e + T2 * i12N2 e +
    (T3 * (i12PolyEH (2 * l) e + e ^ 6 * Qp) + i12PolyKH (i12PolyX3 p a b e) e * Qp +
      T4 * (i12PolyEH (-2 * l) e + e ^ 6 * Qm) + i12PolyKH (i12PolyX4 p a b e) e * Qm) *
      i12N3 e +
    i12Dc e * (e * i12PolyRL p a b l e * T0 + R * (i12PolyKH (i12PolyX0 p a b e) e + e ^ 6 * T0))

/-- The remainder `(P + Tail) / D`, in variables. -/
noncomputable def i12RemV (p a b l e T0 T1 T2 T3 T4 Qp Qm R : ℂ) : ℂ :=
  (i12PolyP p a b l e + i12Tail p a b l e T0 T1 T2 T3 T4 Qp Qm R) / i12D e

theorem i12_assemble (p a b l e T0 T1 T2 T3 T4 Qp Qm R : ℂ) (he : e ≠ 0) (hD : i12D e ≠ 0) :
    ((i12PolyKH (i12PolyX1 p a b e) e + e ^ 6 * T1) * i12N1 e +
      (i12PolyKH (i12PolyX2 p a b e) e + e ^ 6 * T2) * i12N2 e +
      ((i12PolyKH (i12PolyX3 p a b e) e + e ^ 6 * T3) * (i12PolyEH (2 * l) e + e ^ 6 * Qp) +
        (i12PolyKH (i12PolyX4 p a b e) e + e ^ 6 * T4) * (i12PolyEH (-2 * l) e + e ^ 6 * Qm)) *
        i12N3 e +
      i12Dc e * e * (i12PolyRL p a b l e + e ^ 5 * R) *
        (i12PolyKH (i12PolyX0 p a b e) e + e ^ 6 * T0)) / (e ^ 3 * i12D e) =
    i12PolyLe p a l e / e ^ 3 + e ^ 3 * i12RemV p a b l e T0 T1 T2 T3 T4 Qp Qm R := by
  have key := i12_key p a b l e
  have hnum : (i12PolyKH (i12PolyX1 p a b e) e + e ^ 6 * T1) * i12N1 e +
      (i12PolyKH (i12PolyX2 p a b e) e + e ^ 6 * T2) * i12N2 e +
      ((i12PolyKH (i12PolyX3 p a b e) e + e ^ 6 * T3) * (i12PolyEH (2 * l) e + e ^ 6 * Qp) +
        (i12PolyKH (i12PolyX4 p a b e) e + e ^ 6 * T4) * (i12PolyEH (-2 * l) e + e ^ 6 * Qm)) *
        i12N3 e +
      i12Dc e * e * (i12PolyRL p a b l e + e ^ 5 * R) *
        (i12PolyKH (i12PolyX0 p a b e) e + e ^ 6 * T0) =
      i12D e * i12PolyLe p a l e +
        e ^ 6 * (i12PolyP p a b l e + i12Tail p a b l e T0 T1 T2 T3 T4 Qp Qm R) := by
    rw [i12Tail]
    linear_combination key
  rw [hnum, i12RemV]
  field_simp

/-- The analytic remainder of `I₁₂ C⁻¹`, from that of `Rest`. -/
noncomputable def i12GammaR (R5 : ℂ → ℂ) (ε : ℂ) : ℂ :=
  i12RemV (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) (Real.log 2 : ℂ) ε
    (i12ExpT ε (i12PolyX0 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε) (i12V0 ε))
    (i12ExpT ε (i12PolyX1 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε) (i12V1 ε))
    (i12ExpT ε (i12PolyX2 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε) (i12V2 ε))
    (i12ExpT ε (i12PolyX3 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε) (i12V3 ε))
    (i12ExpT ε (i12PolyX4 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε) (i12V4 ε))
    ((2 * (Real.log 2 : ℂ)) ^ 6 * i12ExpRem6 (2 * (Real.log 2 : ℂ) * ε))
    ((-2 * (Real.log 2 : ℂ)) ^ 6 * i12ExpRem6 (-2 * (Real.log 2 : ℂ) * ε)) (R5 ε)

theorem analyticAt_i12ExpT {X V : ℂ → ℂ} (hX : AnalyticAt ℂ X 0) (hV : AnalyticAt ℂ V 0) :
    AnalyticAt ℂ (fun ε => i12ExpT ε (X ε) (V ε)) 0 := by
  have hE : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * (X ε + ε ^ 4 * V ε))) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  unfold i12ExpT
  fun_prop

theorem analyticAt_i12_logGammaRem (a : ℂ) :
    AnalyticAt ℂ (fun ε => QED.DimReg.logGammaRem (a * ε)) 0 :=
  QED.DimReg.analyticAt_logGammaRem.comp_of_eq (by fun_prop) (by simp)

theorem analyticAt_i12ExpRem6_mul (c : ℂ) : AnalyticAt ℂ (fun ε => i12ExpRem6 (c * ε)) 0 :=
  analyticAt_i12ExpRem6.comp_of_eq (by fun_prop) (by simp)

theorem analyticAt_i12GammaR {R5 : ℂ → ℂ} (hR : AnalyticAt ℂ R5 0) :
    AnalyticAt ℂ (i12GammaR R5) 0 := by
  have h1 := analyticAt_i12_logGammaRem 1
  have h2 := analyticAt_i12_logGammaRem 2
  have h3 := analyticAt_i12_logGammaRem 3
  have h4 := analyticAt_i12_logGammaRem 4
  have h5 := analyticAt_i12_logGammaRem (-1)
  have h6 := analyticAt_i12_logGammaRem (-2)
  have q1 := analyticAt_i12ExpRem6_mul (2 * (Real.log 2 : ℂ))
  have q2 := analyticAt_i12ExpRem6_mul (-2 * (Real.log 2 : ℂ))
  have hX0 : AnalyticAt ℂ (i12PolyX0 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ)) 0 := by
    unfold i12PolyX0; fun_prop
  have hX1 : AnalyticAt ℂ (i12PolyX1 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ)) 0 := by
    unfold i12PolyX1; fun_prop
  have hX2 : AnalyticAt ℂ (i12PolyX2 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ)) 0 := by
    unfold i12PolyX2; fun_prop
  have hX3 : AnalyticAt ℂ (i12PolyX3 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ)) 0 := by
    unfold i12PolyX3; fun_prop
  have hX4 : AnalyticAt ℂ (i12PolyX4 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ)) 0 := by
    unfold i12PolyX4; fun_prop
  have hT0 := analyticAt_i12ExpT (V := i12V0) hX0 (by unfold i12V0; fun_prop)
  have hT1 := analyticAt_i12ExpT (V := i12V1) hX1 (by unfold i12V1; fun_prop)
  have hT2 := analyticAt_i12ExpT (V := i12V2) hX2 (by unfold i12V2; fun_prop)
  have hT3 := analyticAt_i12ExpT (V := i12V3) hX3 (by unfold i12V3; fun_prop)
  have hT4 := analyticAt_i12ExpT (V := i12V4) hX4 (by unfold i12V4; fun_prop)
  unfold i12GammaR i12RemV
  refine AnalyticAt.div ?_ (by unfold i12D i12Dc; fun_prop) (by norm_num [i12D, i12Dc])
  unfold i12Tail i12PolyP
  simp only [i12PolyPC0, i12PolyPC1, i12PolyPC2, i12PolyPC3, i12PolyPC4, i12PolyPC5, i12PolyPC6,
    i12PolyPC7, i12PolyPC8, i12PolyPC9, i12PolyPC10, i12PolyPC11, i12PolyPC12, i12PolyPC13,
    i12PolyEH, i12PolyKH, i12PolyRL, i12N1, i12N2, i12N3, i12Dc]
  fun_prop

/-- **The set (d) input for `I₁₂`, from the expansion of the remainder combination.** -/
theorem hasTruncLaurent_setDMasterI12_of_rest (h : HasTruncLaurent i12Rest i12RestLaurent 5) :
    HasTruncLaurent setDMasterI12 setDLaurentI12 3 := by
  obtain ⟨R5, hR5, hev⟩ := h
  refine ⟨i12GammaR R5, analyticAt_i12GammaR hR5, ?_⟩
  filter_upwards [setDGamma_eventually_small, self_mem_nhdsWithin, hev] with ε hε h0 hR
  have h0 : ε ≠ 0 := h0
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have hD : i12D ε ≠ 0 := by
    simp only [i12D, i12Dc]
    have := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
    have := hl (-2) 3 (by norm_num) (by norm_num) (x := 3 * ε - 2) (by ring)
    have := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
    have := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
    have := hl 2 (-1) (by norm_num) (by norm_num) (x := 2 - ε) (by ring)
    simp_all
  rw [setDMasterI12_eq h0 hε, i12K0_eq hε, i12K1_eq hε, i12K2_eq hε, i12K3_eq hε, i12K4_eq hε,
    exp_eq_i12ExpT, exp_eq_i12ExpT, exp_eq_i12ExpT, exp_eq_i12ExpT, exp_eq_i12ExpT,
    exp_mul_eq_i12, exp_mul_eq_i12, hR, i12RestLaurent_eq, setDLaurentI12_eq h0]
  exact i12_assemble _ _ _ _ _ _ _ _ _ _ _ _ _ h0 hD

end QED.ThreeLoopD
