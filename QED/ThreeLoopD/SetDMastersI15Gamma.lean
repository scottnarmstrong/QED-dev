/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15Def
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₁₅`: the `Γ` prefactor, and the input from the expansion of `K`

By definition (`QED.ThreeLoopD.lr96I15`), `I₁₅ C⁻¹ = Γ(-1 + ε) Γ(2ε - 1) / Γ(1 + ε)³ · T` with
`T = B(ε, ε) / (1 - ε) + B(1 - ε, 1 - ε) / ε + K` (`QED.ThreeLoopD.i15T`). With
`Γ(-1 + ε) = Γ(1 + ε) / (ε (ε - 1))`, `Γ(2ε - 1) = Γ(1 + 2ε) / (2ε (2ε - 1))`,
`Γ(n ε) = Γ(1 + n ε) / (n ε)` and `Γ(2 - 2ε) = (1 - 2ε) Γ(1 - 2ε)` this is
(`QED.ThreeLoopD.setDMasterI15_eq`)

  `I₁₅ C⁻¹ = (2(1 - 2ε) + (1 - ε) G₂ + ε(1 - ε)(1 - 2ε) G K) / (2ε³ (1 - ε)² (1 - 2ε)²)`,

with the `Γ`-ratios `G = Γ(1 + 2ε) / Γ(1 + ε)²` and
`G₂ = Γ(1 + 2ε) Γ(1 - ε)² / (Γ(1 + ε)² Γ(1 - 2ε))` (the `Γ` factors of `B(ε, ε)` cancel
exactly against `G`). By `QED.DimReg.Gamma_one_add_eq_exp`,
`G = exp(ε² (π²/6 - 2ζ₃ ε + 7π⁴/180 ε² - 6ζ₅ ε³ + ε⁴ V))` and
`G₂ = exp(ε³ (-4ζ₃ - 12ζ₅ ε² + ε³ V₂))` with `V, V₂` analytic (`γ` cancels).

So the input `HasTruncLaurent setDMasterI15 setDLaurentI15 3` follows from the expansion of `K`
through `ε⁴`; the coefficients are fixed by the LR96/Laporta (2001) table:

  `K = -3/2 - 33/4 ε + (35π²/12 + 4ζ₃ - 251/8) ε² + (-16π² ln 2 + 107π²/8 + 61ζ₃ - 1665/16) ε³
     + (384 a₄ + 16 ln⁴2 + 32π² ln²2 - 72π² ln 2 - 253π⁴/80 - 2π²ζ₃/3 + 2267π²/48 + 503ζ₃/2
       + 12ζ₅ - 10403/32) ε⁴ + O(ε⁵)` (`QED.ThreeLoopD.i15KLaurent`).

Numerically (`setDI15/num.py`, double-exponential quadrature of the Taylor coefficients of the
integrand) these agree with `K` to 18 digits. `QED.ThreeLoopD.hasTruncLaurent_setDMasterI15_of_i15K`
proves the implication, with the explicit remainder `QED.ThreeLoopD.i15GammaR` checked by `ring`.

## Main results

* `QED.ThreeLoopD.setDMasterI15_eq`, `QED.ThreeLoopD.gammaRatio15_eq`,
  `QED.ThreeLoopD.gammaRatio15b_eq`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI15_of_i15K`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- **The target expansion of `K`** through `ε⁴` (forced by the LR96 table entry for `I₁₅`). -/
noncomputable def i15KLaurent (ε : ℂ) : ℂ :=
  -3 / 2 - 33 / 4 * ε + (35 / 12 * (π : ℂ) ^ 2 + 4 * (zeta3 : ℂ) - 251 / 8) * ε ^ 2 +
    (-16 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) + 107 / 8 * (π : ℂ) ^ 2 + 61 * (zeta3 : ℂ)
      - 1665 / 16) * ε ^ 3 +
    (384 * (Li 4 (1 / 2) : ℂ) + 16 * (Real.log 2 : ℂ) ^ 4
      + 32 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 72 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
      - 253 / 80 * (π : ℂ) ^ 4 - 2 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 2267 / 48 * (π : ℂ) ^ 2
      + 503 / 2 * (zeta3 : ℂ) + 12 * (zeta5 : ℂ) - 10403 / 32) * ε ^ 4

/-- `ε³ L₁₅(ε)`, a polynomial. -/
noncomputable def i15Le (ε : ℂ) : ℂ :=
  3 / 2 + 23 / 4 * ε + 105 / 8 * ε ^ 2 + (4 / 3 * (π : ℂ) ^ 2 + 275 / 16) * ε ^ 3 +
    (-8 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) + 28 * (zeta3 : ℂ) + 10 * (π : ℂ) ^ 2
      - 567 / 32) * ε ^ 4 +
    (8 * (Real.log 2 : ℂ) ^ 4 + 16 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2
      - 60 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 62 / 45 * (π : ℂ) ^ 4
      + 192 * (Li 4 (1 / 2) : ℂ) + 210 * (zeta3 : ℂ) + 145 / 3 * (π : ℂ) ^ 2
      - 14917 / 64) * ε ^ 5

/-! ### The `Γ` prefactor -/

/-- `I₁₅ C⁻¹` in terms of `K` and two ratios of `Γ(1 + a ε)`. -/
theorem setDMasterI15_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setDMasterI15 ε = (2 * (1 - 2 * ε) +
      (1 - ε) * (Gamma (1 + 2 * ε) * Gamma (1 + (-1) * ε) ^ 2 /
        (Gamma (1 + 1 * ε) ^ 2 * Gamma (1 + (-2) * ε))) +
      ε * (1 - ε) * (1 - 2 * ε) * (Gamma (1 + 2 * ε) / Gamma (1 + 1 * ε) ^ 2) * i15K ε) /
        (2 * ε ^ 3 * (1 - ε) ^ 2 * (1 - 2 * ε) ^ 2) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have hm := fun a ha {x : ℂ} (hx : x = a * ε) => setDGamma_mul_ne_zero h0 a ha hx
  simp only [setDMasterI15, lr96I15, lr96C, QED.DimReg.tadpole, i15T, i15Closed, i9Beta,
    QED.DimReg.lr96LoopFactor_four_sub]
  rw [Gamma_eq_div_two (s := 1 - (4 - 2 * ε) / 2) (t := 1 + 1 * ε) (p := ε * (ε - 1))
      (hl (-1) 1 (by norm_num) (by norm_num) (by ring)) (hm 1 one_ne_zero (by ring)) (by ring)
      (by ring),
    Gamma_eq_div_two (s := 2 * ε - 1) (t := 1 + 2 * ε) (p := 2 * ε * (2 * ε - 1))
      (hl (-1) 2 (by norm_num) (by norm_num) (by ring)) (hm 2 two_ne_zero (by ring)) (by ring)
      (by ring),
    Gamma_eq_div_one (s := ε + ε) (t := 1 + 2 * ε) (p := 2 * ε) (hm 2 two_ne_zero (by ring))
      (by ring) (by ring),
    Gamma_eq_div_one (s := ε) (t := 1 + 1 * ε) (p := ε) h0 (by ring) rfl,
    show (1 : ℂ) - ε + (1 - ε) = 1 + (-2) * ε + 1 by ring,
    Gamma_add_one _ (hl 1 (-2) (by norm_num) (by norm_num) (by ring)),
    show (1 : ℂ) - ε = 1 + (-1) * ε by ring, show (1 : ℂ) + ε = 1 + 1 * ε by ring,
    Complex.Gamma_one, ofReal_one, one_cpow]
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  have hG1 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hG2 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 2 (by norm_num))
  have hGm2 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-2) (by norm_num))
  have h1 := hl (-1) 1 (by norm_num) (by norm_num) (x := ε - 1) (by ring)
  have h2 := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
  have h3 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 + (-2) * ε) (by ring)
  have h4 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 + (-1) * ε) (by ring)
  have h5 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have h6 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  generalize Gamma (1 + 1 * ε) = A at *
  generalize Gamma (1 + (-1) * ε) = B at *
  generalize Gamma (1 + 2 * ε) = C at *
  generalize Gamma (1 + (-2) * ε) = D at *
  generalize (π : ℂ) ^ ε = P at *
  generalize i15K ε = K
  rw [show (1 : ℂ) + (-2) * ε = 1 - 2 * ε by ring, show (1 : ℂ) + (-1) * ε = 1 - ε by ring,
    show 2 * ε - 1 = -(1 - 2 * ε) by ring, show ε - 1 = -(1 - ε) by ring]
  have h7 : 1 - ε * 2 ≠ 0 := by rwa [mul_comm]
  field_simp

/-! ### The two `Γ`-ratios as exponentials -/

theorem exp_ratio15 (a c : ℂ) : exp a / exp c ^ 2 = exp (a - 2 * c) := by
  rw [Complex.exp_sub, two_mul, Complex.exp_add]
  ring

theorem exp_ratio15b (a b c d : ℂ) :
    exp a * exp b ^ 2 / (exp c ^ 2 * exp d) = exp (a + 2 * b - 2 * c - d) := by
  rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_add, two_mul, two_mul, Complex.exp_add,
    Complex.exp_add]
  ring

/-- The analytic remainder of the exponent of `G = Γ(1 + 2ε) / Γ(1 + ε)²`. -/
noncomputable def i15GammaV (ε : ℂ) : ℂ :=
  2 ^ 6 * QED.DimReg.logGammaRem (2 * ε) - 2 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε)

/-- The polynomial part `π²/6 - 2ζ₃ ε + 7π⁴/180 ε²` of the exponent of `G` over `ε²`. -/
noncomputable def i15GammaXp (ε : ℂ) : ℂ :=
  (π : ℂ) ^ 2 / 6 - 2 * (zeta3 : ℂ) * ε + 7 / 180 * (π : ℂ) ^ 4 * ε ^ 2

/-- The rest of the exponent of `G`, over `ε⁵`. -/
noncomputable def i15GammaY (ε : ℂ) : ℂ := -6 * (zeta5 : ℂ) + ε * i15GammaV ε

/-- The exponent of `G`, divided by `ε ^ 2`. -/
noncomputable def i15GammaX (ε : ℂ) : ℂ := i15GammaXp ε + ε ^ 3 * i15GammaY ε

theorem gammaRatio15_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    Gamma (1 + 2 * ε) / Gamma (1 + 1 * ε) ^ 2 = exp (ε ^ 2 * i15GammaX ε) := by
  rw [QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)), exp_ratio15]
  congr 1
  simp only [i15GammaX, i15GammaXp, i15GammaY, i15GammaV]
  ring

/-- The analytic remainder of the exponent of
`G₂ = Γ(1 + 2ε) Γ(1 - ε)² / (Γ(1 + ε)² Γ(1 - 2ε))`. -/
noncomputable def i15GammaV2 (ε : ℂ) : ℂ :=
  2 ^ 6 * QED.DimReg.logGammaRem (2 * ε) + 2 * (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε) -
    2 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) - (-2) ^ 6 * QED.DimReg.logGammaRem ((-2) * ε)

/-- The exponent of `G₂`, divided by `ε ^ 3`. -/
noncomputable def i15GammaX2 (ε : ℂ) : ℂ :=
  -4 * (zeta3 : ℂ) - 12 * (zeta5 : ℂ) * ε ^ 2 + ε ^ 3 * i15GammaV2 ε

theorem gammaRatio15b_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    Gamma (1 + 2 * ε) * Gamma (1 + (-1) * ε) ^ 2 /
        (Gamma (1 + 1 * ε) ^ 2 * Gamma (1 + (-2) * ε)) = exp (ε ^ 3 * i15GammaX2 ε) := by
  rw [QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-2) (by norm_num)),
    exp_ratio15b]
  congr 1
  simp only [i15GammaX2, i15GammaV2]
  ring

/-! ### The polynomial identity -/

/-! The `Y`-free polynomial part of the remainder for `I₁₅`, in the constants `p = π`, `z = ζ₃`,
`w = ζ₅`, `l = ln 2`, `a = a₄`: with `G₀ = 1 + ε² Xp + ε⁴ Xp²/2`, it is
`(2(1 - 2ε) + (1 - ε)(1 - 4ζ₃ε³ - 12ζ₅ε⁵) + ε(1 - ε)(1 - 2ε) G₀ K_L
  - 2(1 - ε)²(1 - 2ε)² ε³ L₁₅) / ε⁶` (`QED.ThreeLoopD.i15GammaP_spec`). -/

/-- The coefficient of `ε ^ 0` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc0 (p z w l a : ℂ) : ℂ :=
  -8 / 3 * p ^ 4 * l - 3107 / 480 * p ^ 4 + 29 / 6 * p ^ 2 * z + 96 * p ^ 2 * l ^ 2
    - 328 * p ^ 2 * l + 7445 / 32 * p ^ 2 - 8 * z ^ 2 + 4715 / 4 * z - 24 * w + 48 * l ^ 4
    + 1152 * a - 40371 / 32

/-- The coefficient of `ε ^ 1` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc1 (p z w l a : ℂ) : ℂ :=
  -827 / 2160 * p ^ 6 + 1 / 10 * p ^ 4 * z + 16 / 3 * p ^ 4 * l ^ 2 - 4 * p ^ 4 * l
    + 89699 / 2880 * p ^ 4 + 32 * p ^ 2 * z * l + 41 / 12 * p ^ 2 * z + 2 * p ^ 2 * w
    + 8 / 3 * p ^ 2 * l ^ 4 - 352 * p ^ 2 * l ^ 2 + 1224 * p ^ 2 * l + 64 * p ^ 2 * a
    - 60511 / 64 * p ^ 2 - 101 * z ^ 2 - 33857 / 8 * z + 24 * w - 176 * l ^ 4 - 4224 * a
    + 155107 / 32

/-- The coefficient of `ε ^ 2` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc2 (p z w l a : ℂ) : ℂ :=
  -38 / 45 * p ^ 6 * l + 1729 / 960 * p ^ 6 + 151 / 18 * p ^ 4 * z - 16 * p ^ 4 * l ^ 2
    + 92 / 3 * p ^ 4 * l - 102947 / 1920 * p ^ 4 - 64 * p ^ 2 * z * l ^ 2 + 48 * p ^ 2 * z * l
    - 1537 / 12 * p ^ 2 * z - 6 * p ^ 2 * w - 8 * p ^ 2 * l ^ 4 + 384 * p ^ 2 * l ^ 2
    - 1376 * p ^ 2 * l - 192 * p ^ 2 * a + 77303 / 64 * p ^ 2 - 321 / 2 * z ^ 2 - 24 * z * w
    - 32 * z * l ^ 4 - 768 * z * a + 79477 / 16 * z + 192 * l ^ 4 + 4608 * a - 43617 / 8

/-- The coefficient of `ε ^ 3` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc3 (p z w l a : ℂ) : ℂ :=
  -38657 / 259200 * p ^ 8 - 1 / 108 * p ^ 6 * z + 76 / 45 * p ^ 6 * l ^ 2
    - 19 / 15 * p ^ 6 * l - 1499 / 3456 * p ^ 6 + 16 / 3 * p ^ 4 * z * l
    - 2363 / 144 * p ^ 4 * z + 19 / 30 * p ^ 4 * w + 38 / 45 * p ^ 4 * l ^ 4
    + 32 / 3 * p ^ 4 * l ^ 2 - 24 * p ^ 4 * l + 304 / 15 * p ^ 4 * a + 262337 / 11520 * p ^ 4
    - 29 / 2 * p ^ 2 * z ^ 2 + 192 * p ^ 2 * z * l ^ 2 - 368 * p ^ 2 * z * l
    + 15481 / 48 * p ^ 2 * z + 4 * p ^ 2 * w + 16 / 3 * p ^ 2 * l ^ 4 - 128 * p ^ 2 * l ^ 2
    + 480 * p ^ 2 * l + 128 * p ^ 2 * a - 15841 / 32 * p ^ 2 + 8 * z ^ 3 + 4983 / 4 * z ^ 2
    + 72 * z * w + 96 * z * l ^ 4 + 2304 * z * a - 51429 / 16 * z - 64 * l ^ 4 - 1536 * a
    + 14917 / 8

/-- The coefficient of `ε ^ 4` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc4 (p z w l a : ℂ) : ℂ :=
  -14 / 135 * p ^ 8 * l + 5701 / 10800 * p ^ 8 + 2701 / 2160 * p ^ 6 * z
    - 76 / 15 * p ^ 6 * l ^ 2 + 437 / 45 * p ^ 6 * l - 499 / 80 * p ^ 6
    - 4 / 45 * p ^ 4 * z ^ 2 - 32 / 3 * p ^ 4 * z * l ^ 2 + 8 * p ^ 4 * z * l
    - 5831 / 240 * p ^ 4 * z - 19 / 10 * p ^ 4 * w - 38 / 15 * p ^ 4 * l ^ 4
    - 304 / 5 * p ^ 4 * a + 155477 / 3840 * p ^ 4 - 32 * p ^ 2 * z ^ 2 * l
    - 163 / 12 * p ^ 2 * z ^ 2 - 4 * p ^ 2 * z * w - 16 / 3 * p ^ 2 * z * l ^ 4
    - 128 * p ^ 2 * z * l ^ 2 + 288 * p ^ 2 * z * l - 128 * p ^ 2 * z * a
    - 15715 / 96 * p ^ 2 * z + 98 * z ^ 3 - 8471 / 8 * z ^ 2 - 48 * z * w - 64 * z * l ^ 4
    - 1536 * z * a + 10403 / 8 * z

/-- The coefficient of `ε ^ 5` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc5 (p z w l a : ℂ) : ℂ :=
  -889 / 48600 * p ^ 10 - 7 / 5400 * p ^ 8 * z + 28 / 135 * p ^ 8 * l ^ 2
    - 7 / 45 * p ^ 8 * l - 26671 / 103680 * p ^ 8 + 56 / 45 * p ^ 6 * z * l
    - 6689 / 2160 * p ^ 6 * z + 7 / 90 * p ^ 6 * w + 14 / 135 * p ^ 6 * l ^ 4
    + 152 / 45 * p ^ 6 * l ^ 2 - 38 / 5 * p ^ 6 * l + 112 / 45 * p ^ 6 * a
    + 31069 / 6912 * p ^ 6 - 3889 / 360 * p ^ 4 * z ^ 2 + 32 * p ^ 4 * z * l ^ 2
    - 184 / 3 * p ^ 4 * z * l + 96359 / 1440 * p ^ 4 * z + 19 / 15 * p ^ 4 * w
    + 76 / 45 * p ^ 4 * l ^ 4 + 608 / 15 * p ^ 4 * a - 197657 / 5760 * p ^ 4
    - 4 / 3 * p ^ 2 * z ^ 3 + 64 * p ^ 2 * z ^ 2 * l ^ 2 - 48 * p ^ 2 * z ^ 2 * l
    + 5681 / 24 * p ^ 2 * z ^ 2 + 12 * p ^ 2 * z * w + 16 * p ^ 2 * z * l ^ 4
    + 384 * p ^ 2 * z * a - 8183 / 32 * p ^ 2 * z + 153 * z ^ 3 + 24 * z ^ 2 * w
    + 32 * z ^ 2 * l ^ 4 + 768 * z ^ 2 * a - 2421 / 16 * z ^ 2

/-- The coefficient of `ε ^ 6` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc6 (p z w l a : ℂ) : ℂ :=
  -49 / 4050 * p ^ 10 * l + 33691 / 518400 * p ^ 10 + 959 / 3240 * p ^ 8 * z
    - 28 / 45 * p ^ 8 * l ^ 2 + 161 / 135 * p ^ 8 * l - 88123 / 115200 * p ^ 8
    + 7 / 135 * p ^ 6 * z ^ 2 - 112 / 45 * p ^ 6 * z * l ^ 2 + 28 / 15 * p ^ 6 * z * l
    - 12949 / 4320 * p ^ 6 * z - 7 / 30 * p ^ 6 * w - 14 / 45 * p ^ 6 * l ^ 4
    - 112 / 15 * p ^ 6 * a + 57281 / 11520 * p ^ 6 + 4849 / 360 * p ^ 4 * z ^ 2
    - 14 / 15 * p ^ 4 * z * w - 56 / 45 * p ^ 4 * z * l ^ 4 - 64 / 3 * p ^ 4 * z * l ^ 2
    + 48 * p ^ 4 * z * l - 448 / 15 * p ^ 4 * z * a - 73733 / 2880 * p ^ 4 * z
    + 4 * p ^ 2 * z ^ 3 - 192 * p ^ 2 * z ^ 2 * l ^ 2 + 368 * p ^ 2 * z ^ 2 * l
    - 9541 / 24 * p ^ 2 * z ^ 2 - 8 * p ^ 2 * z * w - 32 / 3 * p ^ 2 * z * l ^ 4
    - 256 * p ^ 2 * z * a + 10403 / 48 * p ^ 2 * z - 1265 * z ^ 3 - 72 * z ^ 2 * w
    - 96 * z ^ 2 * l ^ 4 - 2304 * z ^ 2 * a + 24549 / 16 * z ^ 2

/-- The coefficient of `ε ^ 7` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc7 (p z w l a : ℂ) : ℂ :=
  -12397 / 5184000 * p ^ 12 - 49 / 97200 * p ^ 10 * z + 49 / 2025 * p ^ 10 * l ^ 2
    - 49 / 2700 * p ^ 10 * l - 10787 / 345600 * p ^ 10 - 89257 / 129600 * p ^ 8 * z
    + 49 / 5400 * p ^ 8 * w + 49 / 4050 * p ^ 8 * l ^ 4 + 56 / 135 * p ^ 8 * l ^ 2
    - 14 / 15 * p ^ 8 * l + 196 / 675 * p ^ 8 * a + 1150891 / 2073600 * p ^ 8
    - 7 / 45 * p ^ 6 * z ^ 2 + 112 / 15 * p ^ 6 * z * l ^ 2 - 644 / 45 * p ^ 6 * z * l
    + 52703 / 4320 * p ^ 6 * z + 7 / 45 * p ^ 6 * w + 28 / 135 * p ^ 6 * l ^ 4
    + 224 / 45 * p ^ 6 * a - 72821 / 17280 * p ^ 6 + 3289 / 90 * p ^ 4 * z ^ 2
    + 14 / 5 * p ^ 4 * z * w + 56 / 15 * p ^ 4 * z * l ^ 4 + 448 / 5 * p ^ 4 * z * a
    - 57281 / 960 * p ^ 4 * z - 8 / 3 * p ^ 2 * z ^ 3 + 128 * p ^ 2 * z ^ 2 * l ^ 2
    - 288 * p ^ 2 * z ^ 2 * l + 2267 / 12 * p ^ 2 * z ^ 2 + 1006 * z ^ 3 + 48 * z ^ 2 * w
    + 64 * z ^ 2 * l ^ 4 + 1536 * z ^ 2 * a - 10403 / 8 * z ^ 2

/-- The coefficient of `ε ^ 8` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc8 (p z w l a : ℂ) : ℂ :=
  12397 / 1728000 * p ^ 12 + 49 / 32400 * p ^ 10 * z - 49 / 675 * p ^ 10 * l ^ 2
    + 1127 / 8100 * p ^ 10 * l - 30037 / 345600 * p ^ 10 + 1771 / 129600 * p ^ 8 * z
    - 49 / 1800 * p ^ 8 * w - 49 / 1350 * p ^ 8 * l ^ 4 - 196 / 225 * p ^ 8 * a
    + 400967 / 691200 * p ^ 8 + 14 / 135 * p ^ 6 * z ^ 2 - 224 / 45 * p ^ 6 * z * l ^ 2
    + 56 / 5 * p ^ 6 * z * l - 15869 / 2160 * p ^ 6 * z - 3521 / 90 * p ^ 4 * z ^ 2
    - 28 / 15 * p ^ 4 * z * w - 112 / 45 * p ^ 4 * z * l ^ 4 - 896 / 15 * p ^ 4 * z * a
    + 72821 / 1440 * p ^ 4 * z

/-- The coefficient of `ε ^ 9` in `QED.ThreeLoopD.i15GammaPoly`. -/
noncomputable def i15GammaPc9 (p z w l a : ℂ) : ℂ :=
  -12397 / 2592000 * p ^ 12 - 49 / 48600 * p ^ 10 * z + 98 / 2025 * p ^ 10 * l ^ 2
    - 49 / 450 * p ^ 10 * l + 111083 / 1555200 * p ^ 10 + 24647 / 64800 * p ^ 8 * z
    + 49 / 2700 * p ^ 8 * w + 49 / 2025 * p ^ 8 * l ^ 4 + 392 / 675 * p ^ 8 * a
    - 509747 / 1036800 * p ^ 8

/-- The `Y`-free polynomial part of the remainder for `I₁₅` (see `i15GammaP`). -/
noncomputable def i15GammaPoly (p z w l a ε : ℂ) : ℂ :=
  i15GammaPc0 p z w l a + i15GammaPc1 p z w l a * ε + i15GammaPc2 p z w l a * ε ^ 2 +
    i15GammaPc3 p z w l a * ε ^ 3 + i15GammaPc4 p z w l a * ε ^ 4 + i15GammaPc5 p z w l a * ε ^ 5 +
    i15GammaPc6 p z w l a * ε ^ 6 + i15GammaPc7 p z w l a * ε ^ 7 + i15GammaPc8 p z w l a * ε ^ 8 +
    i15GammaPc9 p z w l a * ε ^ 9

/-- The polynomial part of the remainder for `I₁₅`. -/
noncomputable def i15GammaP (ε : ℂ) : ℂ :=
  i15GammaPoly π zeta3 zeta5 (Real.log 2) (Li 4 (1 / 2)) ε

/-- `ε⁶ P = 2(1 - 2ε) + (1 - ε)(1 + ε³ X₂ₚ) + ε(1 - ε)(1 - 2ε) G₀ K_L
  - 2(1 - ε)²(1 - 2ε)² ε³ L₁₅`. -/
theorem i15GammaP_spec (ε : ℂ) :
    ε ^ 6 * i15GammaP ε = 2 * (1 - 2 * ε) +
      (1 - ε) * (1 + ε ^ 3 * (-4 * (zeta3 : ℂ) - 12 * (zeta5 : ℂ) * ε ^ 2)) +
      ε * (1 - ε) * (1 - 2 * ε) * (1 + ε ^ 2 * i15GammaXp ε + (ε ^ 2 * i15GammaXp ε) ^ 2 / 2) *
        i15KLaurent ε - 2 * (1 - ε) ^ 2 * (1 - 2 * ε) ^ 2 * i15Le ε := by
  unfold i15GammaP i15GammaPoly i15GammaPc0 i15GammaPc1 i15GammaPc2 i15GammaPc3 i15GammaPc4
    i15GammaPc5 i15GammaPc6 i15GammaPc7 i15GammaPc8 i15GammaPc9 i15GammaXp i15KLaurent i15Le
  ring

/-- The numerator of the remainder for `I₁₅`, with `Y`, `E = expRem3(ε² X)`, `V₂`,
`E₂ = expRem3(ε³ X₂)` and `R = R_K(ε)` as free variables (`X = Xp + ε³ Y`,
`X₂ = -4ζ₃ - 12ζ₅ε² + ε³ V₂`). -/
noncomputable def i15GammaN (ε Y E V₂ E₂ R : ℂ) : ℂ :=
  i15GammaP ε +
    (1 - ε) * (1 - 2 * ε) * (Y + ε ^ 2 * i15GammaXp ε * Y + ε ^ 5 * Y ^ 2 / 2 +
      ε * (i15GammaXp ε + ε ^ 3 * Y) ^ 3 * E) * i15KLaurent ε +
    (1 - ε) * (1 - 2 * ε) * (1 + ε ^ 2 * (i15GammaXp ε + ε ^ 3 * Y) +
      (ε ^ 2 * (i15GammaXp ε + ε ^ 3 * Y)) ^ 2 / 2 +
      (ε ^ 2 * (i15GammaXp ε + ε ^ 3 * Y)) ^ 3 * E) * R +
    (1 - ε) * (V₂ + (-4 * (zeta3 : ℂ) - 12 * (zeta5 : ℂ) * ε ^ 2 + ε ^ 3 * V₂) ^ 2 / 2 +
      ε ^ 3 * (-4 * (zeta3 : ℂ) - 12 * (zeta5 : ℂ) * ε ^ 2 + ε ^ 3 * V₂) ^ 3 * E₂)

/-- The polynomial identity behind the expansion of `I₁₅`. -/
theorem i15Gamma_key (ε Y E V₂ E₂ R : ℂ) :
    2 * (1 - 2 * ε) + (1 - ε) * (1 + ε ^ 3 * (-4 * (zeta3 : ℂ) - 12 * (zeta5 : ℂ) * ε ^ 2 +
        ε ^ 3 * V₂) + (ε ^ 3 * (-4 * (zeta3 : ℂ) - 12 * (zeta5 : ℂ) * ε ^ 2 +
        ε ^ 3 * V₂)) ^ 2 / 2 + (ε ^ 3 * (-4 * (zeta3 : ℂ) - 12 * (zeta5 : ℂ) * ε ^ 2 +
        ε ^ 3 * V₂)) ^ 3 * E₂) +
      ε * (1 - ε) * (1 - 2 * ε) * (1 + ε ^ 2 * (i15GammaXp ε + ε ^ 3 * Y) +
        (ε ^ 2 * (i15GammaXp ε + ε ^ 3 * Y)) ^ 2 / 2 +
        (ε ^ 2 * (i15GammaXp ε + ε ^ 3 * Y)) ^ 3 * E) * (i15KLaurent ε + ε ^ 5 * R) =
      2 * (1 - ε) ^ 2 * (1 - 2 * ε) ^ 2 * i15Le ε + ε ^ 6 * i15GammaN ε Y E V₂ E₂ R := by
  unfold i15GammaN
  linear_combination -i15GammaP_spec ε

/-! ### The input for `I₁₅` -/

/-- The remainder `R₁₅` with `I₁₅ C⁻¹ = L₁₅ + ε³ R₁₅`, given `K = K_L + ε⁵ R_K`. -/
noncomputable def i15GammaR (RK : ℂ → ℂ) (ε : ℂ) : ℂ :=
  i15GammaN ε (i15GammaY ε) (QED.DimReg.expRem3 (ε ^ 2 * i15GammaX ε)) (i15GammaV2 ε)
      (QED.DimReg.expRem3 (ε ^ 3 * i15GammaX2 ε)) (RK ε) /
    (2 * (1 - ε) ^ 2 * (1 - 2 * ε) ^ 2)

theorem analyticAt_i15GammaR {RK : ℂ → ℂ} (hRK : AnalyticAt ℂ RK 0) :
    AnalyticAt ℂ (i15GammaR RK) 0 := by
  have h1 := analyticAt_logGammaRem_mul (-1)
  have h2 := analyticAt_logGammaRem_mul 2
  have h3 := analyticAt_logGammaRem_mul 1
  have h4 := analyticAt_logGammaRem_mul (-2)
  have hV : AnalyticAt ℂ i15GammaV 0 := by unfold i15GammaV; fun_prop
  have hV2 : AnalyticAt ℂ i15GammaV2 0 := by unfold i15GammaV2; fun_prop
  have hY : AnalyticAt ℂ i15GammaY 0 := by unfold i15GammaY; fun_prop
  have hXp : AnalyticAt ℂ i15GammaXp 0 := by unfold i15GammaXp; fun_prop
  have hX : AnalyticAt ℂ i15GammaX 0 := by unfold i15GammaX; fun_prop
  have hX2 : AnalyticAt ℂ i15GammaX2 0 := by unfold i15GammaX2; fun_prop
  have hE : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * i15GammaX ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hE2 : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 3 * i15GammaX2 ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hP : AnalyticAt ℂ i15GammaP 0 := by
    unfold i15GammaP i15GammaPoly i15GammaPc0 i15GammaPc1 i15GammaPc2 i15GammaPc3 i15GammaPc4
      i15GammaPc5 i15GammaPc6 i15GammaPc7 i15GammaPc8 i15GammaPc9
    fun_prop
  have hK : AnalyticAt ℂ i15KLaurent 0 := by unfold i15KLaurent; fun_prop
  unfold i15GammaR i15GammaN
  refine AnalyticAt.div (by fun_prop) (by fun_prop) ?_
  norm_num

/-- **The input for `I₁₅` from the expansion of `K`**: if `K = K_L + ε⁵ R_K` with `R_K` analytic
at `0`, then `I₁₅ C⁻¹ = L₁₅ + ε³ R₁₅` with `R₁₅` analytic at `0`. -/
theorem hasTruncLaurent_setDMasterI15_of_i15K (hK : HasTruncLaurent i15K i15KLaurent 5) :
    HasTruncLaurent setDMasterI15 setDLaurentI15 3 := by
  obtain ⟨RK, hRK, hev⟩ := hK
  refine ⟨i15GammaR RK, analyticAt_i15GammaR hRK, ?_⟩
  filter_upwards [hev, setDGamma_eventually_small, self_mem_nhdsWithin] with ε hKε hε h0
  have h0 : ε ≠ 0 := h0
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have h2 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have hL : setDLaurentI15 ε = i15Le ε / ε ^ 3 := by
    simp only [setDLaurentI15, i15Le]; field_simp
  rw [setDMasterI15_eq h0 hε, gammaRatio15_eq hε, gammaRatio15b_eq hε,
    QED.DimReg.exp_eq_expRem3, QED.DimReg.exp_eq_expRem3, hKε, i15GammaR, hL]
  generalize QED.DimReg.expRem3 (ε ^ 2 * i15GammaX ε) = E
  generalize QED.DimReg.expRem3 (ε ^ 3 * i15GammaX2 ε) = E₂
  simp only [i15GammaX, i15GammaX2]
  generalize i15GammaY ε = Y
  generalize i15GammaV2 ε = V₂
  generalize RK ε = R
  have key := i15Gamma_key ε Y E V₂ E₂ R
  generalize i15GammaN ε Y E V₂ E₂ R = N at key ⊢
  generalize i15Le ε = A at key ⊢
  have hD : 2 * ε ^ 3 * (1 - ε) ^ 2 * (1 - 2 * ε) ^ 2 ≠ 0 := by simp [h0, h1, h2]
  rw [div_eq_iff hD]
  have e : (A / ε ^ 3 + ε ^ 3 * (N / (2 * (1 - ε) ^ 2 * (1 - 2 * ε) ^ 2))) *
      (2 * ε ^ 3 * (1 - ε) ^ 2 * (1 - 2 * ε) ^ 2) =
      2 * (1 - ε) ^ 2 * (1 - 2 * ε) ^ 2 * A + ε ^ 6 * N := by
    have h2' : 1 - ε * 2 ≠ 0 := by rwa [mul_comm]
    field_simp
  rw [e]
  linear_combination key

end QED.ThreeLoopD
