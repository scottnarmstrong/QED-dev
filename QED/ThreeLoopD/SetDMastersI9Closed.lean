/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Def
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₉`: the `Γ`-function part of `T` and the Beta factor `B(1 + ε, ε)`

`T = QED.ThreeLoopD.i9T` is `i9Closed + B(1 + ε, ε) K + Rem`. This file expands the two pieces
built from `Γ` functions alone.

**The Beta part.** With `Γ(n ε) = Γ(1 + n ε) / (n ε)`, `Γ(2 - 2ε) = (1 - 2ε) Γ(1 - 2ε)`,
`Γ(3 - 6ε) = (2 - 6ε)(1 - 6ε) Γ(1 - 6ε)` and `Γ(3 - 4ε) = (2 - 4ε)(1 - 4ε) Γ(1 - 4ε)`,
(`QED.ThreeLoopD.i9Closed_eq`)

  `ε² i9Closed = G₁ / (1 - ε) + G₂ / (2(1 - 2ε)) + (1 - 3ε)(1 - 6ε) / (2(1 - 2ε)²(1 - 4ε)) G₃`,

with the `Γ`-ratios
`G₁ = Γ(1 + 2ε)² Γ(1 - 2ε) Γ(1 + ε) / (Γ(1 + 4ε) Γ(1 - ε))`,
`G₂ = Γ(1 - ε)² Γ(1 + ε)² / (Γ(1 - 2ε) Γ(1 + 2ε))`,
`G₃ = Γ(1 - ε)² Γ(1 - 6ε) Γ(1 + ε)² / (Γ(1 - 2ε) Γ(1 - 4ε))`.
In each the arguments `aⱼ ε` sum to zero (with multiplicity), so by
`QED.DimReg.Gamma_one_add_eq_exp` each is `exp(ε² X(ε))` with `X = Xₚ + ε³ Y`, `Xₚ` an explicit
quadratic and `Y` analytic; `γ` cancels. With `exp w = 1 + w + w²/2 + w³ E(w)` this gives
(`QED.ThreeLoopD.hasTruncLaurent_i9Closed`)

  `i9Closed = 2/ε² + 3/(2ε) + (π²/3 - 2) + (-17 - 3π²/2 + 42ζ₃) ε
    + (-75 - 28π²/3 - 6ζ₃ + 143π⁴/90) ε² + O(ε³)`.

**The Beta factor.** `B(1 + ε, ε) = Γ(1 + ε)² / (ε Γ(1 + 2ε))`, so
(`QED.ThreeLoopD.hasTruncLaurent_i9BetaK`)

  `B(1 + ε, ε) = 1/ε - π²/6 ε + 2ζ₃ ε² - π⁴/40 ε³ + O(ε⁴)`.

The remainders are explicit and analytic at `0`; the polynomial identities behind them were
computed with sympy and are checked by `ring`.

## Main results

* `QED.ThreeLoopD.hasTruncLaurent_i9Closed`, `QED.ThreeLoopD.hasTruncLaurent_i9BetaK`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### Small-`ε` facts -/

theorem i9Cl_lin_ne_zero {ε : ℂ} (hε : ‖ε‖ < 1 / 8) (c a : ℂ) (hc : 1 ≤ ‖c‖) (ha : ‖a‖ ≤ 6)
    {x : ℂ} (hx : x = c + a * ε) : x ≠ 0 := by
  rintro rfl
  have h : c = -(a * ε) := by linear_combination -hx
  have h2 := congrArg norm h
  rw [norm_neg, norm_mul] at h2
  nlinarith [norm_nonneg a, norm_nonneg ε]

theorem i9Cl_norm_mul_lt_one {ε : ℂ} (hε : ‖ε‖ < 1 / 8) (a : ℂ) (ha : ‖a‖ ≤ 6) :
    ‖a * ε‖ < 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg ε]

theorem i9Cl_Gamma_ne_zero {ε : ℂ} (hε : ‖ε‖ < 1 / 8) (a : ℂ) (ha : ‖a‖ ≤ 6) :
    Gamma (1 + a * ε) ≠ 0 := by
  refine Gamma_ne_zero_of_re_pos ?_
  have h1 := i9Cl_norm_mul_lt_one hε a ha
  have := abs_re_le_norm (a * ε)
  rw [add_re, one_re]
  linarith [abs_le.mp this]

theorem i9Cl_eventually_small : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ‖ε‖ < 1 / 8 :=
  nhdsWithin_le_nhds (Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8))
    fun x hx => by simpa using hx)

theorem analyticAt_i9Cl_logGammaRem (a : ℂ) :
    AnalyticAt ℂ (fun ε => QED.DimReg.logGammaRem (a * ε)) 0 :=
  QED.DimReg.analyticAt_logGammaRem.comp_of_eq (by fun_prop) (by simp)

/-! ### The exponential with a quadratic polynomial part -/

/-- `(exp(ε² (Xₚ + ε³ Y)) - 1 - ε² Xₚ - ε⁴ Xₚ² / 2) / ε⁵`, written with `E = expRem3(ε² X)`. -/
noncomputable def i9ExpTail (ε Xp Y E : ℂ) : ℂ :=
  Y + ε ^ 2 * Xp * Y + ε ^ 5 * Y ^ 2 / 2 + ε * (Xp + ε ^ 3 * Y) ^ 3 * E

theorem exp_eq_i9ExpTail (ε Xp Y : ℂ) :
    exp (ε ^ 2 * (Xp + ε ^ 3 * Y)) = 1 + ε ^ 2 * Xp + ε ^ 4 * Xp ^ 2 / 2 +
      ε ^ 5 * i9ExpTail ε Xp Y (QED.DimReg.expRem3 (ε ^ 2 * (Xp + ε ^ 3 * Y))) := by
  rw [QED.DimReg.exp_eq_expRem3, i9ExpTail]
  ring

theorem analyticAt_i9ExpTail {Xp Y : ℂ → ℂ} (hX : AnalyticAt ℂ Xp 0) (hY : AnalyticAt ℂ Y 0) :
    AnalyticAt ℂ (fun ε => i9ExpTail ε (Xp ε) (Y ε)
      (QED.DimReg.expRem3 (ε ^ 2 * (Xp ε + ε ^ 3 * Y ε)))) 0 := by
  have hE : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * (Xp ε + ε ^ 3 * Y ε))) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  unfold i9ExpTail
  fun_prop

/-! ### The four `Γ`-ratios -/

/-- `G₁ = Γ(1 + 2ε)² Γ(1 - 2ε) Γ(1 + ε) / (Γ(1 + 4ε) Γ(1 - ε))`. -/
noncomputable def i9ClG1 (ε : ℂ) : ℂ :=
  Gamma (1 + 2 * ε) ^ 2 * Gamma (1 + (-2) * ε) * Gamma (1 + 1 * ε) /
    (Gamma (1 + 4 * ε) * Gamma (1 + (-1) * ε))

/-- `G₂ = Γ(1 - ε)² Γ(1 + ε)² / (Γ(1 - 2ε) Γ(1 + 2ε))`. -/
noncomputable def i9ClG2 (ε : ℂ) : ℂ :=
  Gamma (1 + (-1) * ε) ^ 2 * Gamma (1 + 1 * ε) ^ 2 /
    (Gamma (1 + (-2) * ε) * Gamma (1 + 2 * ε))

/-- `G₃ = Γ(1 - ε)² Γ(1 - 6ε) Γ(1 + ε)² / (Γ(1 - 2ε) Γ(1 - 4ε))`. -/
noncomputable def i9ClG3 (ε : ℂ) : ℂ :=
  Gamma (1 + (-1) * ε) ^ 2 * Gamma (1 + (-6) * ε) * Gamma (1 + 1 * ε) ^ 2 /
    (Gamma (1 + (-2) * ε) * Gamma (1 + (-4) * ε))

/-- `G_B = Γ(1 + ε)² / Γ(1 + 2ε) = ε B(1 + ε, ε)`. -/
noncomputable def i9ClGB (ε : ℂ) : ℂ := Gamma (1 + 1 * ε) ^ 2 / Gamma (1 + 2 * ε)

/-- The analytic remainders `∑ nⱼ aⱼ⁶ R(aⱼ ε)` of the four exponents. -/
noncomputable def i9ClV1 (ε : ℂ) : ℂ :=
  2 * 2 ^ 6 * QED.DimReg.logGammaRem (2 * ε) + (-2) ^ 6 * QED.DimReg.logGammaRem ((-2) * ε) +
    1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) - 4 ^ 6 * QED.DimReg.logGammaRem (4 * ε) -
    (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε)

@[inherit_doc i9ClV1]
noncomputable def i9ClV2 (ε : ℂ) : ℂ :=
  2 * (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε) + 2 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) -
    (-2) ^ 6 * QED.DimReg.logGammaRem ((-2) * ε) - 2 ^ 6 * QED.DimReg.logGammaRem (2 * ε)

@[inherit_doc i9ClV1]
noncomputable def i9ClV3 (ε : ℂ) : ℂ :=
  2 * (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε) +
    (-6) ^ 6 * QED.DimReg.logGammaRem ((-6) * ε) + 2 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) -
    (-2) ^ 6 * QED.DimReg.logGammaRem ((-2) * ε) - (-4) ^ 6 * QED.DimReg.logGammaRem ((-4) * ε)

@[inherit_doc i9ClV1]
noncomputable def i9ClVB (ε : ℂ) : ℂ :=
  2 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) - 2 ^ 6 * QED.DimReg.logGammaRem (2 * ε)

/-- The quadratic parts `Xₚ` of the four exponents divided by `ε²`. -/
noncomputable def i9ClXp1 (ε : ℂ) : ℂ :=
  -(π : ℂ) ^ 2 / 3 + 18 * (zeta3 : ℂ) * ε - 26 / 45 * (π : ℂ) ^ 4 * ε ^ 2

@[inherit_doc i9ClXp1]
noncomputable def i9ClXp2 (ε : ℂ) : ℂ := -(π : ℂ) ^ 2 / 3 - 7 / 90 * (π : ℂ) ^ 4 * ε ^ 2

@[inherit_doc i9ClXp1]
noncomputable def i9ClXp3 (ε : ℂ) : ℂ :=
  5 / 3 * (π : ℂ) ^ 2 + 48 * (zeta3 : ℂ) * ε + 257 / 90 * (π : ℂ) ^ 4 * ε ^ 2

@[inherit_doc i9ClXp1]
noncomputable def i9ClXpB (ε : ℂ) : ℂ :=
  -(π : ℂ) ^ 2 / 6 + 2 * (zeta3 : ℂ) * ε - 7 / 180 * (π : ℂ) ^ 4 * ε ^ 2

/-- The rests `Y` of the four exponents, over `ε⁵`. -/
noncomputable def i9ClY1 (ε : ℂ) : ℂ := 198 * (zeta5 : ℂ) + ε * i9ClV1 ε

@[inherit_doc i9ClY1]
noncomputable def i9ClY2 (ε : ℂ) : ℂ := ε * i9ClV2 ε

@[inherit_doc i9ClY1]
noncomputable def i9ClY3 (ε : ℂ) : ℂ := 1344 * (zeta5 : ℂ) + ε * i9ClV3 ε

@[inherit_doc i9ClY1]
noncomputable def i9ClYB (ε : ℂ) : ℂ := 6 * (zeta5 : ℂ) + ε * i9ClVB ε

theorem i9Cl_exp_ratio1 (a b c d e : ℂ) :
    exp a ^ 2 * exp b * exp c / (exp d * exp e) = exp (2 * a + b + c - d - e) := by
  simp only [Complex.exp_sub, Complex.exp_add, two_mul]
  ring

theorem i9Cl_exp_ratio2 (a b c d : ℂ) :
    exp a ^ 2 * exp b ^ 2 / (exp c * exp d) = exp (2 * a + 2 * b - c - d) := by
  simp only [Complex.exp_sub, Complex.exp_add, two_mul]
  ring

theorem i9Cl_exp_ratio3 (a b c d e : ℂ) :
    exp a ^ 2 * exp b * exp c ^ 2 / (exp d * exp e) = exp (2 * a + b + 2 * c - d - e) := by
  simp only [Complex.exp_sub, Complex.exp_add, two_mul]
  ring

theorem i9Cl_exp_ratioB (a b : ℂ) : exp a ^ 2 / exp b = exp (2 * a - b) := by
  simp only [Complex.exp_sub, Complex.exp_add, two_mul]
  ring

theorem i9ClG1_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i9ClG1 ε = exp (ε ^ 2 * (i9ClXp1 ε + ε ^ 3 * i9ClY1 ε)) := by
  rw [i9ClG1,
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε 2 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε (-2) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε 4 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε (-1) (by norm_num)),
    i9Cl_exp_ratio1]
  congr 1
  simp only [i9ClXp1, i9ClY1, i9ClV1]
  ring

theorem i9ClG2_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i9ClG2 ε = exp (ε ^ 2 * (i9ClXp2 ε + ε ^ 3 * i9ClY2 ε)) := by
  rw [i9ClG2,
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε (-1) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε (-2) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε 2 (by norm_num)),
    i9Cl_exp_ratio2]
  congr 1
  simp only [i9ClXp2, i9ClY2, i9ClV2]
  ring

theorem i9ClG3_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i9ClG3 ε = exp (ε ^ 2 * (i9ClXp3 ε + ε ^ 3 * i9ClY3 ε)) := by
  rw [i9ClG3,
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε (-1) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε (-6) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε (-2) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε (-4) (by norm_num)),
    i9Cl_exp_ratio3]
  congr 1
  simp only [i9ClXp3, i9ClY3, i9ClV3]
  ring

theorem i9ClGB_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    i9ClGB ε = exp (ε ^ 2 * (i9ClXpB ε + ε ^ 3 * i9ClYB ε)) := by
  rw [i9ClGB,
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (i9Cl_norm_mul_lt_one hε 2 (by norm_num)),
    i9Cl_exp_ratioB]
  congr 1
  simp only [i9ClXpB, i9ClYB, i9ClVB]
  ring

/-- The analytic tails `Wᵢ` with `Gᵢ = 1 + ε² Xₚ + ε⁴ Xₚ² / 2 + ε⁵ Wᵢ`. -/
noncomputable def i9ClW1 (ε : ℂ) : ℂ :=
  i9ExpTail ε (i9ClXp1 ε) (i9ClY1 ε) (QED.DimReg.expRem3 (ε ^ 2 * (i9ClXp1 ε + ε ^ 3 * i9ClY1 ε)))

@[inherit_doc i9ClW1]
noncomputable def i9ClW2 (ε : ℂ) : ℂ :=
  i9ExpTail ε (i9ClXp2 ε) (i9ClY2 ε) (QED.DimReg.expRem3 (ε ^ 2 * (i9ClXp2 ε + ε ^ 3 * i9ClY2 ε)))

@[inherit_doc i9ClW1]
noncomputable def i9ClW3 (ε : ℂ) : ℂ :=
  i9ExpTail ε (i9ClXp3 ε) (i9ClY3 ε) (QED.DimReg.expRem3 (ε ^ 2 * (i9ClXp3 ε + ε ^ 3 * i9ClY3 ε)))

@[inherit_doc i9ClW1]
noncomputable def i9ClWB (ε : ℂ) : ℂ :=
  i9ExpTail ε (i9ClXpB ε) (i9ClYB ε) (QED.DimReg.expRem3 (ε ^ 2 * (i9ClXpB ε + ε ^ 3 * i9ClYB ε)))

theorem analyticAt_i9ClW1 : AnalyticAt ℂ i9ClW1 0 := by
  have h1 := analyticAt_i9Cl_logGammaRem 2
  have h2 := analyticAt_i9Cl_logGammaRem (-2)
  have h3 := analyticAt_i9Cl_logGammaRem 1
  have h4 := analyticAt_i9Cl_logGammaRem 4
  have h5 := analyticAt_i9Cl_logGammaRem (-1)
  have hV : AnalyticAt ℂ i9ClV1 0 := by unfold i9ClV1; fun_prop
  exact analyticAt_i9ExpTail (by unfold i9ClXp1; fun_prop) (by unfold i9ClY1; fun_prop)

theorem analyticAt_i9ClW2 : AnalyticAt ℂ i9ClW2 0 := by
  have h1 := analyticAt_i9Cl_logGammaRem (-1)
  have h2 := analyticAt_i9Cl_logGammaRem 1
  have h3 := analyticAt_i9Cl_logGammaRem (-2)
  have h4 := analyticAt_i9Cl_logGammaRem 2
  have hV : AnalyticAt ℂ i9ClV2 0 := by unfold i9ClV2; fun_prop
  exact analyticAt_i9ExpTail (by unfold i9ClXp2; fun_prop) (by unfold i9ClY2; fun_prop)

theorem analyticAt_i9ClW3 : AnalyticAt ℂ i9ClW3 0 := by
  have h1 := analyticAt_i9Cl_logGammaRem (-1)
  have h2 := analyticAt_i9Cl_logGammaRem (-6)
  have h3 := analyticAt_i9Cl_logGammaRem 1
  have h4 := analyticAt_i9Cl_logGammaRem (-2)
  have h5 := analyticAt_i9Cl_logGammaRem (-4)
  have hV : AnalyticAt ℂ i9ClV3 0 := by unfold i9ClV3; fun_prop
  exact analyticAt_i9ExpTail (by unfold i9ClXp3; fun_prop) (by unfold i9ClY3; fun_prop)

theorem analyticAt_i9ClWB : AnalyticAt ℂ i9ClWB 0 := by
  have h1 := analyticAt_i9Cl_logGammaRem 1
  have h2 := analyticAt_i9Cl_logGammaRem 2
  have hV : AnalyticAt ℂ i9ClVB 0 := by unfold i9ClVB; fun_prop
  exact analyticAt_i9ExpTail (by unfold i9ClXpB; fun_prop) (by unfold i9ClYB; fun_prop)

/-! ### `i9Closed` as a combination of the `Γ`-ratios -/

/-- The common denominator `2(1 - ε)(1 - 2ε)²(1 - 4ε)`. -/
noncomputable def i9ClD (ε : ℂ) : ℂ := 2 * (1 - ε) * (1 - 2 * ε) ^ 2 * (1 - 4 * ε)

/-- `ε² D · i9Closed = 2(1 - 2ε)²(1 - 4ε) G₁ + (1 - ε)(1 - 2ε)(1 - 4ε) G₂
+ (1 - ε)(1 - 3ε)(1 - 6ε) G₃`. -/
theorem i9Closed_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    i9Closed ε = (2 * (1 - 2 * ε) ^ 2 * (1 - 4 * ε) * i9ClG1 ε +
      (1 - ε) * (1 - 2 * ε) * (1 - 4 * ε) * i9ClG2 ε +
      (1 - ε) * (1 - 3 * ε) * (1 - 6 * ε) * i9ClG3 ε) / (ε ^ 2 * i9ClD ε) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => i9Cl_lin_ne_zero hε c a hc ha hx
  have h2e : 2 * ε ≠ 0 := mul_ne_zero two_ne_zero h0
  have h4e : 4 * ε ≠ 0 := mul_ne_zero (by norm_num) h0
  have g4e : Gamma (2 * ε + 2 * ε) = Gamma (1 + 4 * ε) / (4 * ε) := by
    rw [eq_div_iff h4e, show (1 : ℂ) + 4 * ε = 2 * ε + 2 * ε + 1 by ring,
      Gamma_add_one _ (by rw [show 2 * ε + 2 * ε = 4 * ε by ring]; exact h4e)]
    ring
  have gee : Gamma (ε + ε) = Gamma (1 + 2 * ε) / (2 * ε) := by
    rw [eq_div_iff h2e, show (1 : ℂ) + 2 * ε = ε + ε + 1 by ring,
      Gamma_add_one _ (by rw [← two_mul]; exact h2e)]
    ring
  have g2e : Gamma (2 * ε) = Gamma (1 + 2 * ε) / (2 * ε) := by
    rw [eq_div_iff h2e, show (1 : ℂ) + 2 * ε = 2 * ε + 1 by ring, Gamma_add_one _ h2e]
    ring
  have ge : Gamma ε = Gamma (1 + 1 * ε) / ε := by
    rw [eq_div_iff h0, show (1 : ℂ) + 1 * ε = ε + 1 by ring, Gamma_add_one _ h0]
    ring
  have g1 : Gamma (1 - 2 * ε + ε) = Gamma (1 + (-1) * ε) := by congr 1; ring
  have gm1 : Gamma (1 - ε) = Gamma (1 + (-1) * ε) := by congr 1; ring
  have gm2 : Gamma (1 - 2 * ε) = Gamma (1 + (-2) * ε) := by congr 1; ring
  have gp1 : Gamma (1 + ε) = Gamma (1 + 1 * ε) := by congr 1; ring
  have g12 : Gamma (ε + (1 + ε)) = Gamma (1 + 2 * ε) := by congr 1; ring
  have g22 : Gamma (1 - ε + (1 - ε)) = (1 - 2 * ε) * Gamma (1 + (-2) * ε) := by
    rw [show 1 - ε + (1 - ε) = 1 + (-2) * ε + 1 by ring,
      Gamma_add_one _ (hl 1 (-2) (by norm_num) (by norm_num) rfl)]
    ring
  have g36 : Gamma (3 - 6 * ε) = (2 - 6 * ε) * (1 - 6 * ε) * Gamma (1 + (-6) * ε) := by
    rw [show 3 - 6 * ε = 1 + (-6) * ε + 1 + 1 by ring,
      Gamma_add_one _ (hl 2 (-6) (by norm_num) (by norm_num) (by ring)),
      Gamma_add_one _ (hl 1 (-6) (by norm_num) (by norm_num) rfl)]
    ring
  have g34 : Gamma (2 * ε + (3 - 6 * ε)) =
      (2 - 4 * ε) * (1 - 4 * ε) * Gamma (1 + (-4) * ε) := by
    rw [show 2 * ε + (3 - 6 * ε) = 1 + (-4) * ε + 1 + 1 by ring,
      Gamma_add_one _ (hl 2 (-4) (by norm_num) (by norm_num) (by ring)),
      Gamma_add_one _ (hl 1 (-4) (by norm_num) (by norm_num) rfl)]
    ring
  simp only [i9Closed, i9Beta, i9ClG1, i9ClG2, i9ClG3, i9ClD]
  rw [g4e, gee, g1, g22, g34, g12, g2e, ge, gm1, gm2, g36, gp1]
  have hB := i9Cl_Gamma_ne_zero hε (-1) (by norm_num)
  have hC := i9Cl_Gamma_ne_zero hε 2 (by norm_num)
  have hD := i9Cl_Gamma_ne_zero hε (-2) (by norm_num)
  have hE := i9Cl_Gamma_ne_zero hε 4 (by norm_num)
  have hF := i9Cl_Gamma_ne_zero hε (-4) (by norm_num)
  have h1 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have h2 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have h3 := hl 1 (-4) (by norm_num) (by norm_num) (x := 1 - 4 * ε) (by ring)
  have h4 := hl 2 (-4) (by norm_num) (by norm_num) (x := 2 - 4 * ε) (by ring)
  generalize Gamma (1 + 1 * ε) = A at *
  generalize Gamma (1 + (-1) * ε) = B at *
  generalize Gamma (1 + 2 * ε) = C at *
  generalize Gamma (1 + (-2) * ε) = D at *
  generalize Gamma (1 + 4 * ε) = E at *
  generalize Gamma (1 + (-4) * ε) = F at *
  generalize Gamma (1 + (-6) * ε) = G at *
  rw [show (2 : ℂ) - 4 * ε = 2 * (1 - 2 * ε) by ring]
  generalize hu : 1 - 4 * ε = u at *
  field_simp
  subst hu
  ring

/-! ### The expansion of `i9Closed` -/

/-- **The expansion of the `Γ` part of `T`** through `ε²`. -/
noncomputable def i9ClosedLaurent (ε : ℂ) : ℂ :=
  2 * ε⁻¹ ^ 2 + 3 / 2 * ε⁻¹ + ((π : ℂ) ^ 2 / 3 - 2) +
    (-17 - 3 / 2 * (π : ℂ) ^ 2 + 42 * (zeta3 : ℂ)) * ε +
    (-75 - 28 / 3 * (π : ℂ) ^ 2 - 6 * (zeta3 : ℂ) + 143 / 90 * (π : ℂ) ^ 4) * ε ^ 2

/-- `ε² i9ClosedLaurent`, a polynomial. -/
noncomputable def i9ClosedLe (ε : ℂ) : ℂ :=
  2 + 3 / 2 * ε + ((π : ℂ) ^ 2 / 3 - 2) * ε ^ 2 +
    (-17 - 3 / 2 * (π : ℂ) ^ 2 + 42 * (zeta3 : ℂ)) * ε ^ 3 +
    (-75 - 28 / 3 * (π : ℂ) ^ 2 - 6 * (zeta3 : ℂ) + 143 / 90 * (π : ℂ) ^ 4) * ε ^ 4

/-- The polynomial part of the remainder of `i9Closed`:
`(∑ pᵢ (1 + ε² Xₚᵢ + ε⁴ Xₚᵢ² / 2) - D ε² L) / ε⁵`. -/
noncomputable def i9ClP (ε : ℂ) : ℂ :=
  (-16 / 3 * (π : ℂ) ^ 4 + 68 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 230 / 3 * (π : ℂ) ^ 2
    - 444 * (zeta3 : ℂ) - 590) + (698 / 135 * (π : ℂ) ^ 6 + 199 / 45 * (π : ℂ) ^ 4
    - 704 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 404 * (π : ℂ) ^ 2 + 1476 * (zeta3 : ℂ) ^ 2
    + 1920 * (zeta3 : ℂ) + 3040) * ε + (-4577 / 90 * (π : ℂ) ^ 6
    + 1744 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) + 494 / 9 * (π : ℂ) ^ 4
    + 1920 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 624 * (π : ℂ) ^ 2 - 14112 * (zeta3 : ℂ) ^ 2
    - 1776 * (zeta3 : ℂ) - 4856) * ε ^ 2 + (35753 / 8100 * (π : ℂ) ^ 8
    + 4097 / 30 * (π : ℂ) ^ 6
    - 18064 / 15 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 2288 / 45 * (π : ℂ) ^ 4
    - 1248 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 896 / 3 * (π : ℂ) ^ 2 + 37584 * (zeta3 : ℂ) ^ 2
    + 192 * (zeta3 : ℂ) + 2400) * ε ^ 3 + (-78233 / 1800 * (π : ℂ) ^ 8
    - 2485 / 27 * (π : ℂ) ^ 6
    + 16424 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 25920 * (zeta3 : ℂ) ^ 2) * ε ^ 4
    + (210241 / 1800 * (π : ℂ) ^ 8 - 10672 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ)) * ε ^ 5
    + (-637901 / 8100 * (π : ℂ) ^ 8) * ε ^ 6

/-- The polynomial identity behind the expansion of `i9Closed`. -/
theorem i9Closed_key (ε : ℂ) :
    2 * (1 - 2 * ε) ^ 2 * (1 - 4 * ε) *
        (1 + ε ^ 2 * i9ClXp1 ε + ε ^ 4 * i9ClXp1 ε ^ 2 / 2) +
      (1 - ε) * (1 - 2 * ε) * (1 - 4 * ε) *
        (1 + ε ^ 2 * i9ClXp2 ε + ε ^ 4 * i9ClXp2 ε ^ 2 / 2) +
      (1 - ε) * (1 - 3 * ε) * (1 - 6 * ε) *
        (1 + ε ^ 2 * i9ClXp3 ε + ε ^ 4 * i9ClXp3 ε ^ 2 / 2) =
      i9ClD ε * i9ClosedLe ε + ε ^ 5 * i9ClP ε := by
  simp only [i9ClXp1, i9ClXp2, i9ClXp3, i9ClD, i9ClosedLe, i9ClP]
  ring

/-- The remainder `R` with `i9Closed = L + ε³ R`. -/
noncomputable def i9ClR (ε : ℂ) : ℂ :=
  (i9ClP ε + 2 * (1 - 2 * ε) ^ 2 * (1 - 4 * ε) * i9ClW1 ε +
    (1 - ε) * (1 - 2 * ε) * (1 - 4 * ε) * i9ClW2 ε +
    (1 - ε) * (1 - 3 * ε) * (1 - 6 * ε) * i9ClW3 ε) / i9ClD ε

theorem analyticAt_i9ClR : AnalyticAt ℂ i9ClR 0 := by
  have h1 := analyticAt_i9ClW1
  have h2 := analyticAt_i9ClW2
  have h3 := analyticAt_i9ClW3
  have hP : AnalyticAt ℂ i9ClP 0 := by unfold i9ClP; fun_prop
  have hD : AnalyticAt ℂ i9ClD 0 := by unfold i9ClD; fun_prop
  unfold i9ClR
  refine AnalyticAt.div (by fun_prop) hD ?_
  norm_num [i9ClD]

/-- **The expansion of `i9Closed`**: `i9Closed = i9ClosedLaurent + ε³ R` with `R` analytic. -/
theorem hasTruncLaurent_i9Closed : HasTruncLaurent i9Closed i9ClosedLaurent 3 := by
  refine ⟨i9ClR, analyticAt_i9ClR, ?_⟩
  filter_upwards [i9Cl_eventually_small, self_mem_nhdsWithin] with ε hε h0
  have h0 : ε ≠ 0 := h0
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => i9Cl_lin_ne_zero hε c a hc ha hx
  have h1 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have h2 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have h3 := hl 1 (-4) (by norm_num) (by norm_num) (x := 1 - 4 * ε) (by ring)
  have hD : i9ClD ε ≠ 0 := by simp [i9ClD, h1, h2, h3]
  have hL : i9ClosedLaurent ε = i9ClosedLe ε / ε ^ 2 := by
    simp only [i9ClosedLaurent, i9ClosedLe]; field_simp
  have key := i9Closed_key ε
  rw [i9Closed_eq h0 hε, i9ClG1_eq hε, i9ClG2_eq hε, i9ClG3_eq hε, exp_eq_i9ExpTail,
    exp_eq_i9ExpTail, exp_eq_i9ExpTail, hL, i9ClR]
  rw [← i9ClW1, ← i9ClW2, ← i9ClW3]
  generalize i9ClW1 ε = W1
  generalize i9ClW2 ε = W2
  generalize i9ClW3 ε = W3
  generalize i9ClD ε = D at *
  generalize i9ClP ε = P at *
  generalize i9ClosedLe ε = L at *
  field_simp
  linear_combination 2 * key

/-! ### The Beta factor `B(1 + ε, ε)` -/

/-- **The expansion of `B(1 + ε, ε)`** through `ε³`. -/
noncomputable def i9BetaKLaurent (ε : ℂ) : ℂ :=
  ε⁻¹ - (π : ℂ) ^ 2 / 6 * ε + 2 * (zeta3 : ℂ) * ε ^ 2 - (π : ℂ) ^ 4 / 40 * ε ^ 3

/-- The polynomial part of the remainder of `B(1 + ε, ε)`. -/
noncomputable def i9ClPB (ε : ℂ) : ℂ :=
  (-1 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)) + (7 / 1080 * (π : ℂ) ^ 6 + 2 * (zeta3 : ℂ) ^ 2) * ε
    + (-7 / 90 * (π : ℂ) ^ 4 * (zeta3 : ℂ)) * ε ^ 2 + (49 / 64800 * (π : ℂ) ^ 8) * ε ^ 3

theorem i9BetaK_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    i9Beta (1 + ε) ε = i9ClGB ε / ε := by
  have hC := i9Cl_Gamma_ne_zero hε 2 (by norm_num)
  have ge : Gamma ε = Gamma (1 + 1 * ε) / ε := by
    rw [eq_div_iff h0, show (1 : ℂ) + 1 * ε = ε + 1 by ring, Gamma_add_one _ h0]
    ring
  rw [i9Beta, i9ClGB, ge, show (1 : ℂ) + ε + ε = 1 + 2 * ε by ring,
    show (1 : ℂ) + ε = 1 + 1 * ε by ring]
  field_simp

/-- **The expansion of `B(1 + ε, ε)`**, with remainder `P_B + W_B` analytic at `0`. -/
theorem hasTruncLaurent_i9BetaK :
    HasTruncLaurent (fun ε => i9Beta (1 + ε) ε) i9BetaKLaurent 4 := by
  refine ⟨fun ε => i9ClPB ε + i9ClWB ε, ?_, ?_⟩
  · have h := analyticAt_i9ClWB
    have hP : AnalyticAt ℂ i9ClPB 0 := by unfold i9ClPB; fun_prop
    fun_prop
  filter_upwards [i9Cl_eventually_small, self_mem_nhdsWithin] with ε hε h0
  have h0 : ε ≠ 0 := h0
  rw [i9BetaK_eq h0 hε, i9ClGB_eq hε, exp_eq_i9ExpTail, ← i9ClWB]
  generalize i9ClWB ε = W
  simp only [i9BetaKLaurent, i9ClPB, i9ClXpB]
  field_simp
  ring

end QED.ThreeLoopD
