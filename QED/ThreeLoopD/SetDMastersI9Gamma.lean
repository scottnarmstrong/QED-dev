/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Def
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₉`: the `Γ` prefactor, and the input from the expansion of `T`

By definition (`QED.ThreeLoopD.lr96I9`), `I₉ C⁻¹ = Γ(1 - ε)² Γ(3ε - 1) / (Γ(2 - 2ε) Γ(1 + ε)³) T`
with `T = QED.ThreeLoopD.i9T`. With `Γ(3ε - 1) = Γ(1 + 3ε) / (3ε (3ε - 1))` and
`Γ(2 - 2ε) = (1 - 2ε) Γ(1 - 2ε)` this is (`QED.ThreeLoopD.setDMasterI9_eq`)

  `I₉ C⁻¹ = 1 / (3ε (3ε - 1)(1 - 2ε)) · Γ(1 - ε)² Γ(1 + 3ε) / (Γ(1 + ε)³ Γ(1 - 2ε)) · T`,

and the `Γ`-ratio is `exp(ε² X(ε))`, `X = π²/3 - 10ζ₃ ε + 8π⁴/45 ε² - 54ζ₅ ε³ + ε⁴ V(ε)` with `V`
analytic (`QED.DimReg.Gamma_one_add_eq_exp`; `γ` cancels).

So the input `HasTruncLaurent setDMasterI9 setDLaurentI9 2` is equivalent to the expansion of
`T` through `ε²`; the coefficients are fixed by the LR96/Laporta (2001) table:

  `T = 2/ε² + (π²/3 - 12) + (6π² + 36ζ₃ - 64) ε
     + (28π² - 48π² ln 2 + 13π⁴/45 + 168ζ₃ - 272) ε² + O(ε³)` (`QED.ThreeLoopD.i9TLaurent`).

`QED.ThreeLoopD.hasTruncLaurent_setDMasterI9_of_i9T` proves the implication, with the explicit
remainder `QED.ThreeLoopD.i9GammaR` checked by `ring`.

## Main results

* `QED.ThreeLoopD.setDMasterI9_eq`, `QED.ThreeLoopD.gammaRatio9_eq`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI9_of_i9T`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- **The target expansion of `T`** through `ε²` (from the LR96 table entry for `I₉`). -/
noncomputable def i9TLaurent (ε : ℂ) : ℂ :=
  2 * ε⁻¹ ^ 2 + ((π : ℂ) ^ 2 / 3 - 12) + (6 * (π : ℂ) ^ 2 + 36 * (zeta3 : ℂ) - 64) * ε +
    (28 * (π : ℂ) ^ 2 - 48 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) + 13 / 45 * (π : ℂ) ^ 4 +
      168 * (zeta3 : ℂ) - 272) * ε ^ 2

/-- `ε² T_L(ε)`, a polynomial. -/
noncomputable def i9TLe (ε : ℂ) : ℂ :=
  2 + ((π : ℂ) ^ 2 / 3 - 12) * ε ^ 2 + (6 * (π : ℂ) ^ 2 + 36 * (zeta3 : ℂ) - 64) * ε ^ 3 +
    (28 * (π : ℂ) ^ 2 - 48 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) + 13 / 45 * (π : ℂ) ^ 4 +
      168 * (zeta3 : ℂ) - 272) * ε ^ 4

/-- `I₉ C⁻¹` as a rational function times a ratio of `Γ(1 + a ε)` times `T`. -/
theorem setDMasterI9_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setDMasterI9 ε = 1 / (3 * ε * (3 * ε - 1) * (1 - 2 * ε)) *
      (Gamma (1 + (-1) * ε) ^ 2 * Gamma (1 + 3 * ε) /
        (Gamma (1 + 1 * ε) ^ 3 * Gamma (1 + (-2) * ε))) * i9T ε := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have hm := fun a ha {x : ℂ} (hx : x = a * ε) => setDGamma_mul_ne_zero h0 a ha hx
  simp only [setDMasterI9, lr96I9, lr96C, masslessBubble, QED.DimReg.lr96LoopFactor_four_sub]
  rw [Gamma_eq_div_one (s := 2 - (4 - 2 * ε) / 2) (t := 1 + 1 * ε) (p := ε)
      (hm 1 one_ne_zero (by ring)) (by ring) (by ring),
    Gamma_eq_div_one (s := ε) (t := 1 + 1 * ε) (p := ε) h0 (by ring) rfl,
    show (4 - 2 * ε) / 2 - 1 = 1 + (-1) * ε by ring,
    show (4 : ℂ) - 2 * ε - 2 = 1 + (-2) * ε + 1 by ring,
    Gamma_add_one _ (hl 1 (-2) (by norm_num) (by norm_num) (by ring)),
    Gamma_eq_div_two (s := 3 * ε - 1) (t := 1 + 3 * ε) (p := 3 * ε * (3 * ε - 1))
      (hl (-1) 3 (by norm_num) (by norm_num) (by ring)) (hm 3 (by norm_num) (by ring)) (by ring)
      (by ring),
    show (1 : ℂ) + ε = 1 + 1 * ε by ring]
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  have hG1 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hG2 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-2) (by norm_num))
  have hGm := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-1) (by norm_num))
  have h1 := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
  have h2 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have h3 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 + (-2) * ε) (by ring)
  generalize Gamma (1 + 1 * ε) = A at *
  generalize Gamma (1 + (-1) * ε) = B at *
  generalize Gamma (1 + 3 * ε) = C at *
  generalize Gamma (1 + (-2) * ε) = D at *
  generalize (π : ℂ) ^ ε = P at *
  generalize i9T ε = T
  rw [show (1 : ℂ) + (-2) * ε = 1 - 2 * ε by ring] at *
  field_simp

theorem exp_ratio9 (a b c d : ℂ) :
    exp a ^ 2 * exp b / (exp c ^ 3 * exp d) = exp (2 * a + b - 3 * c - d) := by
  rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_add, two_mul, Complex.exp_add,
    show 3 * c = c + c + c by ring, Complex.exp_add, Complex.exp_add]
  ring

/-- The analytic remainder of the exponent for `I₉`. -/
noncomputable def i9GammaV (ε : ℂ) : ℂ :=
  2 * (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε) + 3 ^ 6 * QED.DimReg.logGammaRem (3 * ε) -
    3 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) - (-2) ^ 6 * QED.DimReg.logGammaRem ((-2) * ε)

/-- The polynomial part `π²/3 - 10ζ₃ ε + 8π⁴/45 ε²` of the exponent for `I₉` over `ε²`. -/
noncomputable def i9GammaXp (ε : ℂ) : ℂ :=
  (π : ℂ) ^ 2 / 3 - 10 * (zeta3 : ℂ) * ε + 8 / 45 * (π : ℂ) ^ 4 * ε ^ 2

/-- The rest of the exponent for `I₉`, over `ε⁵`. -/
noncomputable def i9GammaY (ε : ℂ) : ℂ := -54 * (zeta5 : ℂ) + ε * i9GammaV ε

/-- The exponent for `I₉`, divided by `ε ^ 2`. -/
noncomputable def i9GammaX (ε : ℂ) : ℂ := i9GammaXp ε + ε ^ 3 * i9GammaY ε

theorem gammaRatio9_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    Gamma (1 + (-1) * ε) ^ 2 * Gamma (1 + 3 * ε) /
        (Gamma (1 + 1 * ε) ^ 3 * Gamma (1 + (-2) * ε)) = exp (ε ^ 2 * i9GammaX ε) := by
  rw [QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-2) (by norm_num)), exp_ratio9]
  congr 1
  simp only [i9GammaX, i9GammaXp, i9GammaY, i9GammaV]
  ring

/-- The `Y`-free polynomial part of the remainder for `I₉`:
`((1 + ε² Xp + ε⁴ Xp²/2) ε² T_L - 3 (3ε - 1)(1 - 2ε) ε³ L₉) / ε⁵`. -/
noncomputable def i9GammaP (ε : ℂ) : ℂ :=
  (19 / 3 * (π : ℂ) ^ 4 + 2 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 240 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
      + 833 / 3 * (π : ℂ) ^ 2 + 1264 * (zeta3 : ℂ) - 2026) +
    (79 / 270 * (π : ℂ) ^ 6 - 16 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) + 4 / 3 * (π : ℂ) ^ 4
      - 4 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 288 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
      - 1586 / 3 * (π : ℂ) ^ 2 - 260 * (zeta3 : ℂ) ^ 2 - 848 * (zeta3 : ℂ) + 2388) * ε +
    (7 / 5 * (π : ℂ) ^ 6 + 38 / 45 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 224 / 15 * (π : ℂ) ^ 4
      + 480 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (Real.log 2 : ℂ) - 240 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      - 1680 * (zeta3 : ℂ) ^ 2 + 2720 * (zeta3 : ℂ)) * ε ^ 2 +
    (481 / 4050 * (π : ℂ) ^ 8 - 56 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) + 262 / 45 * (π : ℂ) ^ 6
      + 96 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 952 / 15 * (π : ℂ) ^ 4
      - 310 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 + 640 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      - 600 * (zeta3 : ℂ) ^ 2) * ε ^ 3 +
    (16 / 45 * (π : ℂ) ^ 8 + 26 / 45 * (π : ℂ) ^ 6 * (zeta3 : ℂ) - 512 / 135 * (π : ℂ) ^ 6
      + 160 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (Real.log 2 : ℂ) - 72 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
      - 260 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 + 2720 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
      + 1800 * (zeta3 : ℂ) ^ 3 - 3200 * (zeta3 : ℂ) ^ 2) * ε ^ 4 +
    (136 / 6075 * (π : ℂ) ^ 10 - 128 / 45 * (π : ℂ) ^ 8 * (Real.log 2 : ℂ)
      + 992 / 675 * (π : ℂ) ^ 8 - 32 / 45 * (π : ℂ) ^ 6 * (zeta3 : ℂ) - 2176 / 135 * (π : ℂ) ^ 6
      - 446 / 9 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2 + 1024 / 9 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
      - 2400 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 * (Real.log 2 : ℂ)
      + 1400 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 + 8400 * (zeta3 : ℂ) ^ 3
      - 13600 * (zeta3 : ℂ) ^ 2) * ε ^ 5 +
    (64 / 675 * (π : ℂ) ^ 10 + 112 / 2025 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
      - 2048 / 2025 * (π : ℂ) ^ 8 + 256 / 3 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (Real.log 2 : ℂ)
      - 448 / 9 * (π : ℂ) ^ 6 * (zeta3 : ℂ) - 896 / 3 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
      + 4352 / 9 * (π : ℂ) ^ 4 * (zeta3 : ℂ)) * ε ^ 6 +
    (416 / 91125 * (π : ℂ) ^ 12 - 512 / 675 * (π : ℂ) ^ 10 * (Real.log 2 : ℂ)
      + 896 / 2025 * (π : ℂ) ^ 10 + 1792 / 675 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
      - 8704 / 2025 * (π : ℂ) ^ 8) * ε ^ 7

/-- `ε³ L₉(ε)`, a polynomial. -/
noncomputable def i9Le (ε : ℂ) : ℂ :=
  (-2 / 3) + (-10 / 3) * ε + (-1 / 3 * (π : ℂ) ^ 2 - 26 / 3) * ε ^ 2 +
    (-16 / 3 * (zeta3 : ℂ) - 11 / 3 * (π : ℂ) ^ 2 - 2) * ε ^ 3 +
    (16 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 13 / 45 * (π : ℂ) ^ 4 - 248 / 3 * (zeta3 : ℂ)
      - 73 / 3 * (π : ℂ) ^ 2 + 398 / 3) * ε ^ 4

/-- The numerator of the remainder for `I₉`, with `Y`, `E = expRem3(ε² X)` and `R = R_T(ε)` as
free variables (`X = Xp + ε³ Y`). -/
noncomputable def i9GammaN (ε Y E R : ℂ) : ℂ :=
  i9GammaP ε + Y * (1 + ε ^ 2 * i9GammaXp ε + ε ^ 5 * Y / 2) * i9TLe ε +
    ε * (i9GammaXp ε + ε ^ 3 * Y) ^ 3 * E * i9TLe ε +
    (1 + ε ^ 2 * (i9GammaXp ε + ε ^ 3 * Y) + ε ^ 4 * (i9GammaXp ε + ε ^ 3 * Y) ^ 2 / 2 +
      ε ^ 6 * (i9GammaXp ε + ε ^ 3 * Y) ^ 3 * E) * R

/-- The polynomial identity behind the expansion of `I₉`. -/
theorem i9Gamma_key (ε Y E R : ℂ) :
    (1 + ε ^ 2 * (i9GammaXp ε + ε ^ 3 * Y) + (ε ^ 2 * (i9GammaXp ε + ε ^ 3 * Y)) ^ 2 / 2 +
        (ε ^ 2 * (i9GammaXp ε + ε ^ 3 * Y)) ^ 3 * E) * (i9TLe ε + ε ^ 5 * R) =
      3 * (3 * ε - 1) * (1 - 2 * ε) * i9Le ε + ε ^ 5 * i9GammaN ε Y E R := by
  simp only [i9GammaN, i9GammaP, i9GammaXp, i9TLe, i9Le]
  ring

/-- The remainder `R₉` with `I₉ C⁻¹ = L₉ + ε² R₉`, given `T = T_L + ε³ R_T`. -/
noncomputable def i9GammaR (RT : ℂ → ℂ) (ε : ℂ) : ℂ :=
  i9GammaN ε (i9GammaY ε) (QED.DimReg.expRem3 (ε ^ 2 * i9GammaX ε)) (RT ε) /
    (3 * (3 * ε - 1) * (1 - 2 * ε))

theorem analyticAt_i9GammaR {RT : ℂ → ℂ} (hRT : AnalyticAt ℂ RT 0) :
    AnalyticAt ℂ (i9GammaR RT) 0 := by
  have h1 := analyticAt_logGammaRem_mul (-1)
  have h2 := analyticAt_logGammaRem_mul 3
  have h3 := analyticAt_logGammaRem_mul 1
  have h4 := analyticAt_logGammaRem_mul (-2)
  have hV : AnalyticAt ℂ i9GammaV 0 := by unfold i9GammaV; fun_prop
  have hY : AnalyticAt ℂ i9GammaY 0 := by unfold i9GammaY; fun_prop
  have hXp : AnalyticAt ℂ i9GammaXp 0 := by unfold i9GammaXp; fun_prop
  have hX : AnalyticAt ℂ i9GammaX 0 := by unfold i9GammaX; fun_prop
  have hE : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * i9GammaX ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hP : AnalyticAt ℂ i9GammaP 0 := by unfold i9GammaP; fun_prop
  have hT : AnalyticAt ℂ i9TLe 0 := by unfold i9TLe; fun_prop
  unfold i9GammaR i9GammaN
  refine AnalyticAt.div (by fun_prop) (by fun_prop) ?_
  norm_num

/-- **The input for `I₉` from the expansion of `T`**: if `T = T_L + ε³ R_T` with `R_T` analytic
at `0`, then `I₉ C⁻¹ = L₉ + ε² R₉` with `R₉` analytic at `0`. -/
theorem hasTruncLaurent_setDMasterI9_of_i9T (hT : HasTruncLaurent i9T i9TLaurent 3) :
    HasTruncLaurent setDMasterI9 setDLaurentI9 2 := by
  obtain ⟨RT, hRT, hev⟩ := hT
  refine ⟨i9GammaR RT, analyticAt_i9GammaR hRT, ?_⟩
  filter_upwards [hev, setDGamma_eventually_small, self_mem_nhdsWithin] with ε hTε hε h0
  have h0 : ε ≠ 0 := h0
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
  have h2 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have hTL : i9TLaurent ε = i9TLe ε / ε ^ 2 := by
    simp only [i9TLaurent, i9TLe]; field_simp
  have hL : setDLaurentI9 ε = i9Le ε / ε ^ 3 := by
    simp only [setDLaurentI9, i9Le]; field_simp
  have key := i9Gamma_key ε (i9GammaY ε) (QED.DimReg.expRem3 (ε ^ 2 * i9GammaX ε)) (RT ε)
  rw [setDMasterI9_eq h0 hε, gammaRatio9_eq hε, QED.DimReg.exp_eq_expRem3, hTε, i9GammaR, hTL,
    hL]
  generalize i9GammaN ε (i9GammaY ε) (QED.DimReg.expRem3 (ε ^ 2 * i9GammaX ε)) (RT ε) = N at *
  generalize QED.DimReg.expRem3 (ε ^ 2 * i9GammaX ε) = E at *
  rw [i9GammaX] at *
  generalize i9GammaXp ε + ε ^ 3 * i9GammaY ε = X at *
  generalize i9TLe ε = A at *
  generalize i9Le ε = B at *
  generalize RT ε = R at *
  have e : 1 / (3 * ε * (3 * ε - 1) * (1 - 2 * ε)) *
      (1 + ε ^ 2 * X + (ε ^ 2 * X) ^ 2 / 2 + (ε ^ 2 * X) ^ 3 * E) * (A / ε ^ 2 + ε ^ 3 * R) =
      (1 + ε ^ 2 * X + (ε ^ 2 * X) ^ 2 / 2 + (ε ^ 2 * X) ^ 3 * E) * (A + ε ^ 5 * R) /
        (3 * ε ^ 3 * (3 * ε - 1) * (1 - 2 * ε)) := by
    field_simp
  have hD : 3 * ε ^ 3 * (3 * ε - 1) * (1 - 2 * ε) ≠ 0 := by simp [h0, h1, h2]
  have hD' : 3 * (3 * ε - 1) * (1 - 2 * ε) ≠ 0 := by simp [h1, h2]
  have hB : B / ε ^ 3 = 3 * (3 * ε - 1) * (1 - 2 * ε) * B / (3 * ε ^ 3 * (3 * ε - 1) *
      (1 - 2 * ε)) := by
    rw [eq_div_iff hD]; field_simp
  have hN : ε ^ 2 * (N / (3 * (3 * ε - 1) * (1 - 2 * ε))) =
      ε ^ 5 * N / (3 * ε ^ 3 * (3 * ε - 1) * (1 - 2 * ε)) := by
    have h1' : ε * 3 - 1 ≠ 0 := by rwa [mul_comm]
    have h2' : 1 - ε * 2 ≠ 0 := by rwa [mul_comm]
    rw [eq_div_iff hD]; field_simp
  rw [e, key, hB, hN, add_div]

end QED.ThreeLoopD
