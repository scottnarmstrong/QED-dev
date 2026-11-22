/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13Def
public import QED.ThreeLoopD.SetDMastersGamma2
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₁₃`: the input from the expansion of the subtracted integral

`I₁₃ C⁻¹ = (i13Tail + i13Rem) / (ε² (1 - ε) Γ(1 + ε) Γ(1 - ε))`
(`QED.ThreeLoopD.setDMasterI13_eq`), and the tail is a rational function of `ε` and
`G = Γ(1 - ε)² / Γ(1 - 2ε)` (`QED.ThreeLoopD.i13Tail_eq`). With
`G = exp(-π²/6 ε² - 2ζ₃ ε³ - 7π⁴/180 ε⁴ - 6ζ₅ ε⁵ + O(ε⁶))` and
`Γ(1 + ε) Γ(1 - ε) = exp(π²/6 ε² + π⁴/180 ε⁴ + O(ε⁶))` (`QED.DimReg.Gamma_one_add_eq_exp`), the
expansion

  `Rem = 1/2 - 9/4 ε + (-4ζ₃ - 7π²/6 - 47/8) ε² + (12ζ₃ - 47π²/12 - π⁴/90 - 97/16) ε³
    + (256 a₄ + 32/3 ln⁴2 - 32/3 π² ln²2 + 2/3 π² ζ₃ + 176 ζ₃ - 12 ζ₅ - 133/45 π⁴ - 427/24 π²
      + 841/32) ε⁴ + O(ε⁵)` (`QED.ThreeLoopD.i13RemLaurent`)

gives `HasTruncLaurent setDMasterI13 setDLaurentI13 3`
(`QED.ThreeLoopD.hasTruncLaurent_setDMasterI13_of_Rem`). The orders `ε⁰` to `ε⁵` of
`ε³ I₁₃ C⁻¹` match by the polynomial identity `QED.ThreeLoopD.i13Wire_key`, checked by `ring`.
The expansion of `Rem` is the one implied by the LR96 table; numerically (contour integrals of
`setDI13/i13num.py`) its five coefficients are those of the integral to twelve digits. Its
proof is the hypothesis that remains.

## Main results

* `QED.ThreeLoopD.setDMasterI13_eq`, `QED.ThreeLoopD.i13Tail_eq`, `QED.ThreeLoopD.i13G_eq`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI13_of_Rem`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- **The target expansion of `Rem`** through `ε⁴`. -/
noncomputable def i13RemLaurent (ε : ℂ) : ℂ :=
  1 / 2 - 9 / 4 * ε + (-7 / 6 * (π : ℂ) ^ 2 - 4 * (zeta3 : ℂ) - 47 / 8) * ε ^ 2
    + (-1 / 90 * (π : ℂ) ^ 4 - 47 / 12 * (π : ℂ) ^ 2 + 12 * (zeta3 : ℂ) - 97 / 16) * ε ^ 3
    + (-133 / 45 * (π : ℂ) ^ 4 + 2 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    - 32 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 427 / 24 * (π : ℂ) ^ 2 + 176 * (zeta3 : ℂ)
    - 12 * (zeta5 : ℂ) + 32 / 3 * (Real.log 2 : ℂ) ^ 4 + 256 * (Li 4 (1 / 2) : ℂ)
    + 841 / 32) * ε ^ 4

/-! ### The master and the tail -/

/-- The numerator coefficient of `G²` in `ε · i13Tail`. -/
noncomputable def i13A2 (ε : ℂ) : ℂ :=
  ε * (ε - 2) * (ε - 1) ^ 2 * (288 * ε ^ 3 - 504 * ε ^ 2 + 301 * ε - 59)

/-- The numerator coefficient of `G` in `ε · i13Tail`. -/
noncomputable def i13A1 (ε : ℂ) : ℂ :=
  -12 * (ε - 1) * (3 * ε - 2) * (1 - 3 * ε) * (4 * ε ^ 3 - 13 * ε ^ 2 + 9 * ε - 1)

/-- The numerator term free of `G` in `ε · i13Tail`. -/
noncomputable def i13A0 (ε : ℂ) : ℂ :=
  -12 * (ε - 2) * (1 - 2 * ε) ^ 2 * (3 * ε - 2) * (1 - 3 * ε)

/-- The denominator of `ε · i13Tail`. -/
noncomputable def i13D (ε : ℂ) : ℂ :=
  -3 * (ε - 2) * (ε - 1) ^ 2 * (1 - 2 * ε) ^ 2 * (3 * ε - 2) * (1 - 3 * ε)

theorem i13D_ne_zero {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i13D ε ≠ 0 := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl (-2) 1 (by norm_num) (by norm_num) (x := ε - 2) (by ring)
  have h2 := hl (-1) 1 (by norm_num) (by norm_num) (x := ε - 1) (by ring)
  have h3 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have h4 := hl (-2) 3 (by norm_num) (by norm_num) (x := 3 * ε - 2) (by ring)
  have h5 := hl 1 (-3) (by norm_num) (by norm_num) (x := 1 - 3 * ε) (by ring)
  simp only [i13D]
  simp [h1, h2, h3, h4, h5]

/-- **The tail as a rational function of `ε` and `G`.** -/
theorem i13Tail_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    i13Tail ε = (i13G ε ^ 2 * i13A2 ε + i13G ε * i13A1 ε + i13A0 ε) / (ε * i13D ε) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl (-2) 1 (by norm_num) (by norm_num) (x := ε - 2) (by ring)
  have h2 := hl (-1) 1 (by norm_num) (by norm_num) (x := ε - 1) (by ring)
  have h3 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have h4 := hl (-2) 3 (by norm_num) (by norm_num) (x := 3 * ε - 2) (by ring)
  have h5 := hl 1 (-3) (by norm_num) (by norm_num) (x := 1 - 3 * ε) (by ring)
  have h3' : 1 - ε * 2 ≠ 0 := by rwa [mul_comm]
  have h4' : ε * 3 - 2 ≠ 0 := by rwa [mul_comm]
  have h5' : 1 - ε * 3 ≠ 0 := by rwa [mul_comm]
  simp only [i13Tail, i13Al0, i13Al1, i13Al2, i13Be0, i13Be1, i13A2, i13A1, i13A0, i13D]
  generalize i13G ε = G
  field_simp
  ring

/-- `I₁₃ C⁻¹ = T / (ε² (1 - ε) Γ(1 + ε) Γ(1 - ε))`. -/
theorem setDMasterI13_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setDMasterI13 ε =
      i13T ε / (ε ^ 2 * (1 - ε) * (Gamma (1 + 1 * ε) * Gamma (1 + (-1) * ε))) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 + (-1) * ε) (by ring)
  have h1' := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have hG1 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hGm := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-1) (by norm_num))
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  simp only [setDMasterI13, lr96I13, lr96C, QED.DimReg.lr96LoopFactor_four_sub]
  rw [show (1 : ℂ) + ε = 1 + 1 * ε by ring,
    Gamma_eq_div_one (s := ε) (t := 1 + 1 * ε) (p := ε) h0 (by ring) rfl,
    show (2 : ℂ) - ε = 1 + (-1) * ε + 1 by ring, Gamma_add_one _ h1]
  rw [show (1 : ℂ) * ε = ε by ring] at hG1 ⊢
  rw [show (1 : ℂ) + (-1) * ε = 1 - ε by ring] at hGm ⊢
  generalize Gamma (1 + ε) = A at *
  generalize Gamma (1 - ε) = B at *
  generalize (π : ℂ) ^ ε = P at *
  field_simp

/-! ### The `Γ`-functions as exponentials -/

/-- The analytic remainder of the exponent of `G`. -/
noncomputable def i13V (ε : ℂ) : ℂ :=
  2 * QED.DimReg.logGammaRem ((-1) * ε) - 64 * QED.DimReg.logGammaRem ((-2) * ε)

/-- The exponent of `G`, divided by `ε²`. -/
noncomputable def i13X (ε : ℂ) : ℂ :=
  -(π : ℂ) ^ 2 / 6 - 2 * (zeta3 : ℂ) * ε - 7 / 180 * (π : ℂ) ^ 4 * ε ^ 2 -
    6 * (zeta5 : ℂ) * ε ^ 3 + ε ^ 4 * i13V ε

/-- The analytic remainder of the exponent of `Γ(1 + ε) Γ(1 - ε)`. -/
noncomputable def i13W (ε : ℂ) : ℂ :=
  QED.DimReg.logGammaRem (1 * ε) + QED.DimReg.logGammaRem ((-1) * ε)

/-- The exponent of `Γ(1 + ε) Γ(1 - ε)`, divided by `ε²`. -/
noncomputable def i13Y (ε : ℂ) : ℂ :=
  (π : ℂ) ^ 2 / 6 + (π : ℂ) ^ 4 / 180 * ε ^ 2 + ε ^ 4 * i13W ε

theorem i13_exp_ratio (a b : ℂ) : exp a ^ 2 / exp b = exp (2 * a - b) := by
  rw [Complex.exp_sub, two_mul, Complex.exp_add, sq]

/-- `G = exp(ε² X)`. -/
theorem i13G_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i13G ε = exp (ε ^ 2 * i13X ε) := by
  rw [i13G, show (1 : ℂ) - ε = 1 + (-1) * ε by ring, show (1 : ℂ) - 2 * ε = 1 + (-2) * ε by ring,
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-2) (by norm_num)),
    i13_exp_ratio]
  congr 1
  simp only [i13X, i13V]
  ring

/-- `Γ(1 + ε) Γ(1 - ε) = exp(ε² Y)`. -/
theorem i13GammaProd_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    Gamma (1 + 1 * ε) * Gamma (1 + (-1) * ε) = exp (ε ^ 2 * i13Y ε) := by
  rw [QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    ← Complex.exp_add]
  congr 1
  simp only [i13Y, i13W]
  ring

/-! ### Truncations -/

/-- The truncation of `G` through `ε⁵`. -/
noncomputable def i13Gp (ε : ℂ) : ℂ :=
  1 - 1 / 6 * (π : ℂ) ^ 2 * ε ^ 2 - 2 * (zeta3 : ℂ) * ε ^ 3 - 1 / 40 * (π : ℂ) ^ 4 * ε ^ 4
    + (1 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 6 * (zeta5 : ℂ)) * ε ^ 5

/-- The polynomial part of `(G - G_p) / ε⁶`, in terms of `V`. -/
noncomputable def i13dGp (ε V : ℂ) : ℂ :=
  (7 / 1080 * (π : ℂ) ^ 6 + 2 * (zeta3 : ℂ) ^ 2 + V) + (7 / 90 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
    + (π : ℂ) ^ 2 * (zeta5 : ℂ)) * ε + (49 / 64800 * (π : ℂ) ^ 8 - 1 / 6 * (π : ℂ) ^ 2 * V
    + 12 * (zeta3 : ℂ) * (zeta5 : ℂ)) * ε ^ 2 + (7 / 30 * (π : ℂ) ^ 4 * (zeta5 : ℂ)
    - 2 * (zeta3 : ℂ) * V) * ε ^ 3 + (-7 / 180 * (π : ℂ) ^ 4 * V + 18 * (zeta5 : ℂ) ^ 2) * ε ^ 4
    - 6 * (zeta5 : ℂ) * V * ε ^ 5 + 1 / 2 * V ^ 2 * ε ^ 6

/-- The truncation of `(Γ(1 + ε) Γ(1 - ε))⁻¹` through `ε⁵`. -/
noncomputable def i13Sp (ε : ℂ) : ℂ :=
  1 - 1 / 6 * (π : ℂ) ^ 2 * ε ^ 2 + 1 / 120 * (π : ℂ) ^ 4 * ε ^ 4

/-- The polynomial part of `(S - S_p) / ε⁶`, in terms of `W`. -/
noncomputable def i13dSp (ε W : ℂ) : ℂ :=
  (1 / 1080 * (π : ℂ) ^ 6 - W) + (1 / 64800 * (π : ℂ) ^ 8 + 1 / 6 * (π : ℂ) ^ 2 * W) * ε ^ 2
    + 1 / 180 * (π : ℂ) ^ 4 * W * ε ^ 4 + 1 / 2 * W ^ 2 * ε ^ 6

/-- `(G - G_p) / ε⁶`. -/
noncomputable def i13dG (ε : ℂ) : ℂ :=
  i13dGp ε (i13V ε) + i13X ε ^ 3 * QED.DimReg.expRem3 (ε ^ 2 * i13X ε)

/-- `S = (Γ(1 + ε) Γ(1 - ε))⁻¹ = exp(-ε² Y)`. -/
noncomputable def i13S (ε : ℂ) : ℂ := exp (-(ε ^ 2 * i13Y ε))

/-- `(S - S_p) / ε⁶`. -/
noncomputable def i13dS (ε : ℂ) : ℂ :=
  i13dSp ε (i13W ε) - i13Y ε ^ 3 * QED.DimReg.expRem3 (-(ε ^ 2 * i13Y ε))

theorem i13G_trunc (ε : ℂ) : exp (ε ^ 2 * i13X ε) = i13Gp ε + ε ^ 6 * i13dG ε := by
  rw [QED.DimReg.exp_eq_expRem3, i13dG]
  generalize QED.DimReg.expRem3 (ε ^ 2 * i13X ε) = E
  simp only [i13X, i13Gp, i13dGp]
  ring

theorem i13S_trunc (ε : ℂ) : i13S ε = i13Sp ε + ε ^ 6 * i13dS ε := by
  rw [i13S, QED.DimReg.exp_eq_expRem3, i13dS]
  generalize QED.DimReg.expRem3 (-(ε ^ 2 * i13Y ε)) = E
  simp only [i13Y, i13Sp, i13dSp]
  ring

/-! ### The polynomial identity -/

/-- `ε³` times the Laurent polynomial of `I₁₃ C⁻¹`. -/
noncomputable def i13L13e (ε : ℂ) : ℂ :=
  2 + 23 / 3 * ε + 35 / 2 * ε ^ 2 + 275 / 12 * ε ^ 3 + (112 / 3 * (zeta3 : ℂ) - 189 / 8) * ε ^ 4
    + (-136 / 45 * (π : ℂ) ^ 4 - 32 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 280 * (zeta3 : ℂ)
    + 32 / 3 * (Real.log 2 : ℂ) ^ 4 + 256 * (Li 4 (1 / 2) : ℂ) - 14917 / 48) * ε ^ 5

/-- The coefficient of `ε ^ 0` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP0 : ℂ :=
  (2 / 45 * (π : ℂ) ^ 6 + 397 / 10 * (π : ℂ) ^ 4 + 204 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    + 128 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 3527 / 4 * (π : ℂ) ^ 2 - 6052 * (zeta3 : ℂ)
    - 912 * (zeta5 : ℂ) - 128 * (Real.log 2 : ℂ) ^ 4 - 3072 * (Li 4 (1 / 2) : ℂ) + 330675 / 16)

/-- The coefficient of `ε ^ 1` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP1 : ℂ :=
  (-2929 / 540 * (π : ℂ) ^ 6 - 64 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2 - 6499 / 15 * (π : ℂ) ^ 4
    - 1358 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 64 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4
    - 1408 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 512 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ)
    + 51343 / 8 * (π : ℂ) ^ 2 + 472 * (zeta3 : ℂ) ^ 2 + 57108 * (zeta3 : ℂ) + 7632 * (zeta5 : ℂ)
    + 1408 * (Real.log 2 : ℂ) ^ 4 + 33792 * (Li 4 (1 / 2) : ℂ) - 5217409 / 32)

/-- The coefficient of `ε ^ 2` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP2 : ℂ :=
  (-7 / 1800 * (π : ℂ) ^ 8 + 4283 / 72 * (π : ℂ) ^ 6 - 133 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
    + 704 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2 + 247967 / 120 * (π : ℂ) ^ 4
    + 2160 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 388 * (π : ℂ) ^ 2 * (zeta5 : ℂ)
    - 704 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4 + 6368 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2
    - 5632 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ) - 626803 / 32 * (π : ℂ) ^ 2 - 3588 * (zeta3 : ℂ) ^ 2
    - 229468 * (zeta3 : ℂ) - 27048 * (zeta5 : ℂ) - 6368 * (Real.log 2 : ℂ) ^ 4
    - 152832 * (Li 4 (1 / 2) : ℂ) + 17448891 / 32)

/-- The coefficient of `ε ^ 3` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP3 : ℂ :=
  (5267 / 21600 * (π : ℂ) ^ 8 + 16 / 15 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2
    - 59059 / 216 * (π : ℂ) ^ 6 + 1971 / 10 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
    - 16 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4 - 3184 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2
    - 128 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ) - 268351 / 48 * (π : ℂ) ^ 4
    - 236 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 + 6148 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    - 3066 * (π : ℂ) ^ 2 * (zeta5 : ℂ) + 3184 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4
    - 15328 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 25472 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ)
    + 2082337 / 64 * (π : ℂ) ^ 2 + 10996 * (zeta3 : ℂ) ^ 2 + 2832 * (zeta3 : ℂ) * (zeta5 : ℂ)
    + 503316 * (zeta3 : ℂ) + 50256 * (zeta5 : ℂ) + 15328 * (Real.log 2 : ℂ) ^ 4
    + 367872 * (Li 4 (1 / 2) : ℂ) - 31962325 / 32)

/-- The coefficient of `ε ^ 4` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP4 : ℂ :=
  (-38909 / 14400 * (π : ℂ) ^ 8 - 181 / 270 * (π : ℂ) ^ 6 * (zeta3 : ℂ)
    - 176 / 15 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 + 190579 / 288 * (π : ℂ) ^ 6
    - 1583 / 3 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 173 / 15 * (π : ℂ) ^ 4 * (zeta5 : ℂ)
    + 176 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4 + 7664 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2
    + 1408 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ) + 17939021 / 1920 * (π : ℂ) ^ 4
    + 1794 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 - 30100 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    + 10006 * (π : ℂ) ^ 2 * (zeta5 : ℂ) - 7664 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4
    + 21152 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 61312 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ)
    - 2074621 / 64 * (π : ℂ) ^ 2 - 17436 * (zeta3 : ℂ) ^ 2 - 21528 * (zeta3 : ℂ) * (zeta5 : ℂ)
    - 644608 * (zeta3 : ℂ) - 50232 * (zeta5 : ℂ) - 21152 * (Real.log 2 : ℂ) ^ 4
    - 507648 * (Li 4 (1 / 2) : ℂ) + 34518243 / 32)

/-- The coefficient of `ε ^ 5` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP5 : ℂ :=
  (-59 / 14400 * (π : ℂ) ^ 10 + 551527 / 43200 * (π : ℂ) ^ 8 + 859 / 180 * (π : ℂ) ^ 6 * (zeta3 : ℂ)
    + 796 / 15 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 - 7642417 / 8640 * (π : ℂ) ^ 6
    + 649 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2 + 2029 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
    + 187 / 2 * (π : ℂ) ^ 4 * (zeta5 : ℂ) - 796 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4
    - 10576 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2 - 6368 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ)
    - 12646729 / 1280 * (π : ℂ) ^ 4 - 5498 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2
    - 944 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) + 51154 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    - 17094 * (π : ℂ) ^ 2 * (zeta5 : ℂ) + 10576 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4
    - 16672 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 84608 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ)
    + 1329743 / 64 * (π : ℂ) ^ 2 + 15028 * (zeta3 : ℂ) ^ 2 + 65976 * (zeta3 : ℂ) * (zeta5 : ℂ)
    + 478104 * (zeta3 : ℂ) + 4248 * (zeta5 : ℂ) ^ 2 + 25056 * (zeta5 : ℂ)
    + 16672 * (Real.log 2 : ℂ) ^ 4 + 400128 * (Li 4 (1 / 2) : ℂ) - 10951421 / 16)

/-- The coefficient of `ε ^ 6` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP6 : ℂ :=
  (299 / 9600 * (π : ℂ) ^ 10 + 1711 / 5400 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
    - 460363 / 14400 * (π : ℂ) ^ 8 - 6983 / 540 * (π : ℂ) ^ 6 * (zeta3 : ℂ)
    - 59 / 15 * (π : ℂ) ^ 6 * (zeta5 : ℂ) - 1916 / 15 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2
    + 340451 / 576 * (π : ℂ) ^ 6 - 3289 / 10 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
    + 12682 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 9511 / 30 * (π : ℂ) ^ 4 * (zeta5 : ℂ)
    + 1916 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4 + 8336 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2
    + 15328 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ) + 25149343 / 3840 * (π : ℂ) ^ 4
    + 8718 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 + 7176 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ)
    - 43832 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 15886 * (π : ℂ) ^ 2 * (zeta5 : ℂ)
    - 8336 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4 + 6912 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2
    - 66688 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ) - 596273 / 64 * (π : ℂ) ^ 2 - 6624 * (zeta3 : ℂ) ^ 2
    - 104616 * (zeta3 : ℂ) * (zeta5 : ℂ) - 188640 * (zeta3 : ℂ) - 32292 * (zeta5 : ℂ) ^ 2
    - 4752 * (zeta5 : ℂ) - 6912 * (Real.log 2 : ℂ) ^ 4 - 165888 * (Li 4 (1 / 2) : ℂ) + 1881837 / 8)

/-- The coefficient of `ε ^ 7` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP7 : ℂ :=
  (59 / 96000 * (π : ℂ) ^ 12 - 2749 / 28800 * (π : ℂ) ^ 10 - 8671 / 3600 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
    + 394007 / 8640 * (π : ℂ) ^ 8 - 472 / 135 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2
    + 3077 / 180 * (π : ℂ) ^ 6 * (zeta3 : ℂ) + 299 / 10 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
    + 2644 / 15 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 - 21453 / 320 * (π : ℂ) ^ 6
    + 30239 / 30 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
    + 1534 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) - 22481 / 10 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
    + 5641 / 10 * (π : ℂ) ^ 4 * (zeta5 : ℂ) - 2644 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4
    - 1152 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2 - 21152 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ)
    - 3406031 / 1280 * (π : ℂ) ^ 4 - 7514 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2
    - 21992 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) + 18792 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    - 708 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2 - 7488 * (π : ℂ) ^ 2 * (zeta5 : ℂ)
    + 1152 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4 - 1152 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2
    + 27648 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ) + 5895 / 2 * (π : ℂ) ^ 2 + 1152 * (zeta3 : ℂ) ^ 2
    + 90168 * (zeta3 : ℂ) * (zeta5 : ℂ) + 30240 * (zeta3 : ℂ) + 98964 * (zeta5 : ℂ) ^ 2
    + 1152 * (Real.log 2 : ℂ) ^ 4 + 27648 * (Li 4 (1 / 2) : ℂ) - 134253 / 4)

/-- The coefficient of `ε ^ 8` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP8 : ℂ :=
  (-299 / 64000 * (π : ℂ) ^ 12 - 59 / 3600 * (π : ℂ) ^ 10 * (zeta3 : ℂ) + 1453 / 9600 * (π : ℂ) ^ 10
    + 79721 / 10800 * (π : ℂ) ^ 8 * (zeta3 : ℂ) + 59 / 200 * (π : ℂ) ^ 8 * (zeta5 : ℂ)
    - 33259 / 900 * (π : ℂ) ^ 8 + 1196 / 45 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2
    - 6227 / 540 * (π : ℂ) ^ 6 * (zeta3 : ℂ) - 2749 / 30 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
    - 2084 / 15 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 - 152099 / 960 * (π : ℂ) ^ 6
    - 15983 / 10 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
    - 3887 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) + 10676 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
    - 3263 / 6 * (π : ℂ) ^ 4 * (zeta5 : ℂ) + 2084 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4
    + 192 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2 + 16672 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ)
    + 883217 / 1280 * (π : ℂ) ^ 4 + 3312 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2
    + 34872 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) - 3168 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    + 5382 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2 + 1368 * (π : ℂ) ^ 2 * (zeta5 : ℂ)
    - 192 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4 - 4608 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ)
    - 7569 / 16 * (π : ℂ) ^ 2 - 39744 * (zeta3 : ℂ) * (zeta5 : ℂ) - 156924 * (zeta5 : ℂ) ^ 2)

/-- The coefficient of `ε ^ 9` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP9 : ℂ :=
  (2749 / 192000 * (π : ℂ) ^ 12 + 299 / 2400 * (π : ℂ) ^ 10 * (zeta3 : ℂ)
    - 3757 / 28800 * (π : ℂ) ^ 10 + 59 / 540 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2
    - 42137 / 3600 * (π : ℂ) ^ 8 * (zeta3 : ℂ) - 897 / 400 * (π : ℂ) ^ 8 * (zeta5 : ℂ)
    + 4703 / 300 * (π : ℂ) ^ 8 - 10996 / 135 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2
    - 59 / 15 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ) + 56 / 15 * (π : ℂ) ^ 6 * (zeta3 : ℂ)
    + 1453 / 10 * (π : ℂ) ^ 6 * (zeta5 : ℂ) + 288 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2
    + 1851 / 20 * (π : ℂ) ^ 6 + 41327 / 30 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
    + 35737 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) - 4698 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
    + 177 / 5 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2 + 264 * (π : ℂ) ^ 4 * (zeta5 : ℂ)
    - 288 / 5 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4 - 6912 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ)
    - 1179 / 8 * (π : ℂ) ^ 4 - 576 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2
    - 30056 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) - 16494 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2
    + 6912 * (zeta3 : ℂ) * (zeta5 : ℂ) + 135252 * (zeta5 : ℂ) ^ 2)

/-- The coefficient of `ε ^ 10` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP10 : ℂ :=
  (-1453 / 64000 * (π : ℂ) ^ 12 - 2749 / 7200 * (π : ℂ) ^ 10 * (zeta3 : ℂ) + 23 / 400 * (π : ℂ) ^ 10
    - 299 / 360 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 + 108953 / 10800 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
    + 2749 / 400 * (π : ℂ) ^ 8 * (zeta5 : ℂ) - 133 / 50 * (π : ℂ) ^ 8
    + 5812 / 45 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2 + 299 / 10 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
    - 7 / 15 * (π : ℂ) ^ 6 * (zeta3 : ℂ) - 3757 / 30 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
    - 48 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 - 1281 / 80 * (π : ℂ) ^ 6
    - 3036 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2 - 18889 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ)
    + 792 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 2691 / 10 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2
    - 246 / 5 * (π : ℂ) ^ 4 * (zeta5 : ℂ) + 48 / 5 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4
    + 1152 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ) + 7569 / 320 * (π : ℂ) ^ 4
    + 13248 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) + 26154 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2
    - 59616 * (zeta5 : ℂ) ^ 2)

/-- The coefficient of `ε ^ 11` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP11 : ℂ :=
  (3757 / 192000 * (π : ℂ) ^ 12 + 1453 / 2400 * (π : ℂ) ^ 10 * (zeta3 : ℂ) - 1 / 100 * (π : ℂ) ^ 10
    + 2749 / 1080 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 - 667 / 150 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
    - 4359 / 400 * (π : ℂ) ^ 8 * (zeta5 : ℂ) - 15028 / 135 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2
    - 2749 / 30 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ) + 276 / 5 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
    + 528 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2 + 48841 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ)
    + 8247 / 10 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2 - 2304 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ)
    - 22542 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2 + 10368 * (zeta5 : ℂ) ^ 2)

/-- The coefficient of `ε ^ 12` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP12 : ℂ :=
  (-69 / 8000 * (π : ℂ) ^ 12 - 3757 / 7200 * (π : ℂ) ^ 10 * (zeta3 : ℂ)
    - 1453 / 360 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 + 58 / 75 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
    + 3757 / 400 * (π : ℂ) ^ 8 * (zeta5 : ℂ) + 736 / 15 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2
    + 1453 / 10 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ) - 48 / 5 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
    - 7176 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ)
    - 13077 / 10 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2 + 9936 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2)

/-- The coefficient of `ε ^ 13` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP13 : ℂ :=
  (3 / 2000 * (π : ℂ) ^ 12 + 23 / 100 * (π : ℂ) ^ 10 * (zeta3 : ℂ)
    + 3757 / 1080 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 - 207 / 50 * (π : ℂ) ^ 8 * (zeta5 : ℂ)
    - 128 / 15 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2 - 3757 / 30 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
    + 1248 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ)
    + 11271 / 10 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2 - 1728 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2)

/-- The coefficient of `ε ^ 14` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP14 : ℂ :=
  (-1 / 25 * (π : ℂ) ^ 10 * (zeta3 : ℂ) - 23 / 15 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2
    + 18 / 25 * (π : ℂ) ^ 8 * (zeta5 : ℂ) + 276 / 5 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
    - 2484 / 5 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2)

/-- The coefficient of `ε ^ 15` in `QED.ThreeLoopD.i13WireP`. -/
noncomputable def i13WP15 : ℂ :=
  (4 / 15 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 - 48 / 5 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
    + 432 / 5 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2)

/-- The polynomial `(K S_p - ε³ L₁₃ D (1 - ε)) / ε⁶`. -/
noncomputable def i13WireP (ε : ℂ) : ℂ :=
  i13WP0 + i13WP1 * ε + i13WP2 * ε ^ 2 + i13WP3 * ε ^ 3 + i13WP4 * ε ^ 4 + i13WP5 * ε ^ 5
    + i13WP6 * ε ^ 6 + i13WP7 * ε ^ 7 + i13WP8 * ε ^ 8 + i13WP9 * ε ^ 9 + i13WP10 * ε ^ 10
    + i13WP11 * ε ^ 11 + i13WP12 * ε ^ 12 + i13WP13 * ε ^ 13 + i13WP14 * ε ^ 14 + i13WP15 * ε ^ 15

/-- The truncated numerator `G_p² A₂ + G_p A₁ + A₀ + ε D Rem_L`. -/
noncomputable def i13K (ε : ℂ) : ℂ :=
  i13Gp ε ^ 2 * i13A2 ε + i13Gp ε * i13A1 ε + i13A0 ε + ε * i13D ε * i13RemLaurent ε

/-- **The polynomial identity behind the expansion of `I₁₃`**: the orders `ε⁰` to `ε⁵` of
`K S_p` are those of `ε³ L₁₃ D (1 - ε)`. -/
theorem i13Wire_key (ε : ℂ) :
    i13K ε * i13Sp ε - i13L13e ε * i13D ε * (1 - ε) = ε ^ 6 * i13WireP ε := by
  simp only [i13K, i13Gp, i13A2, i13A1, i13A0, i13D, i13RemLaurent, i13Sp, i13L13e, i13WireP,
    i13WP0, i13WP1, i13WP2, i13WP3, i13WP4, i13WP5, i13WP6, i13WP7, i13WP8, i13WP9, i13WP10,
    i13WP11, i13WP12, i13WP13, i13WP14, i13WP15]
  ring

/-! ### The expansion -/

/-- `H = (2 G_p ΔG + ε⁶ ΔG²) A₂ + ΔG A₁ + D R`. -/
noncomputable def i13H (ε R : ℂ) : ℂ :=
  (2 * i13Gp ε * i13dG ε + ε ^ 6 * i13dG ε ^ 2) * i13A2 ε + i13dG ε * i13A1 ε + i13D ε * R

/-- The remainder `R₁₃` with `I₁₃ C⁻¹ = L₁₃ + ε³ R₁₃`, given `Rem = Rem_L + ε⁵ R`. -/
noncomputable def i13R (ε R : ℂ) : ℂ :=
  (i13WireP ε + i13K ε * i13dS ε + i13H ε R * i13S ε) / (i13D ε * (1 - ε))

theorem analyticAt_i13R {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0) :
    AnalyticAt ℂ (fun ε => i13R ε (R ε)) 0 := by
  have hV : AnalyticAt ℂ i13V 0 := by
    have h1 := analyticAt_logGammaRem_mul (-1)
    have h2 := analyticAt_logGammaRem_mul (-2)
    unfold i13V
    fun_prop
  have hW : AnalyticAt ℂ i13W 0 := by
    have h1 := analyticAt_logGammaRem_mul 1
    have h2 := analyticAt_logGammaRem_mul (-1)
    unfold i13W
    fun_prop
  have hX : AnalyticAt ℂ i13X 0 := by unfold i13X; fun_prop
  have hY : AnalyticAt ℂ i13Y 0 := by unfold i13Y; fun_prop
  have hEG : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * i13X ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hES : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (-(ε ^ 2 * i13Y ε))) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hdG : AnalyticAt ℂ i13dG 0 := by unfold i13dG i13dGp; fun_prop
  have hdS : AnalyticAt ℂ i13dS 0 := by unfold i13dS i13dSp; fun_prop
  have hS : AnalyticAt ℂ i13S 0 := by unfold i13S; fun_prop
  have hP : AnalyticAt ℂ i13WireP 0 := by unfold i13WireP; fun_prop
  have hGp : AnalyticAt ℂ i13Gp 0 := by unfold i13Gp; fun_prop
  have hA2 : AnalyticAt ℂ i13A2 0 := by unfold i13A2; fun_prop
  have hA1 : AnalyticAt ℂ i13A1 0 := by unfold i13A1; fun_prop
  have hA0 : AnalyticAt ℂ i13A0 0 := by unfold i13A0; fun_prop
  have hD : AnalyticAt ℂ i13D 0 := by unfold i13D; fun_prop
  have hRL : AnalyticAt ℂ i13RemLaurent 0 := by unfold i13RemLaurent; fun_prop
  have hK : AnalyticAt ℂ i13K 0 := by unfold i13K; fun_prop
  unfold i13R i13H
  refine AnalyticAt.div (by fun_prop) (by fun_prop) ?_
  norm_num [i13D]

/-- **The set (d) input for `I₁₃` from the expansion of `Rem`**: if
`Rem = Rem_L + ε⁵ R` with `R` analytic at `0`, then `I₁₃ C⁻¹ = L₁₃ + ε³ R₁₃` with `R₁₃`
analytic at `0`. -/
theorem hasTruncLaurent_setDMasterI13_of_Rem (hRem : HasTruncLaurent i13Rem i13RemLaurent 5) :
    HasTruncLaurent setDMasterI13 setDLaurentI13 3 := by
  obtain ⟨RR, hRR, hRe⟩ := hRem
  refine ⟨fun ε => i13R ε (RR ε), analyticAt_i13R hRR, ?_⟩
  filter_upwards [setDGamma_eventually_small, hRe, self_mem_nhdsWithin] with ε hε hRε h0
  have h0 : ε ≠ 0 := h0
  have hD := i13D_ne_zero hε
  have h1 : (1 : ℂ) - ε ≠ 0 :=
    setDGamma_lin_ne_zero hε 1 (-1) (by norm_num) (by norm_num) (by ring)
  have hL : setDLaurentI13 ε = i13L13e ε / ε ^ 3 := by
    simp only [setDLaurentI13, i13L13e]
    field_simp
    ring
  have hS0 : i13Sp ε + ε ^ 6 * i13dS ε ≠ 0 := by
    rw [← i13S_trunc]; exact Complex.exp_ne_zero _
  have hSG : Gamma (1 + 1 * ε) * Gamma (1 + (-1) * ε) = (i13Sp ε + ε ^ 6 * i13dS ε)⁻¹ := by
    rw [i13GammaProd_eq hε, ← i13S_trunc, i13S, Complex.exp_neg, inv_inv]
  have key := i13Wire_key ε
  rw [setDMasterI13_eq h0 hε, i13T, i13Tail_eq h0 hε, hRε, i13G_eq hε, i13G_trunc, hSG, hL,
    i13R, i13H, i13S_trunc]
  simp only [i13K] at key ⊢
  generalize i13Gp ε = Gp at *
  generalize i13dG ε = dG at *
  generalize i13A2 ε = A2 at *
  generalize i13A1 ε = A1 at *
  generalize i13A0 ε = A0 at *
  generalize i13D ε = D at *
  generalize i13RemLaurent ε = RL at *
  generalize RR ε = R at *
  generalize i13Sp ε = Sp at *
  generalize i13dS ε = dS at *
  generalize i13L13e ε = L at *
  generalize i13WireP ε = P at *
  field_simp
  linear_combination key

end QED.ThreeLoopD
