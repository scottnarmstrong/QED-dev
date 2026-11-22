/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSGoodId
public import QED.ThreeLoopD.SetDMastersI12RHighSPVal
public import QED.ThreeLoopD.SetDMastersI12RHighSJet

/-!
# Set (d), master `I₁₂`: the good part of the bulk remainder at orders `2` and `3`

`ε ∫ Good = R(ε) = A(ε) P(ε - 1, ε) - a B_w(ε) P(-ε - 1, ε)/2 - a B_w(ε) P(2ε - 1, ε)`
(`QED.ThreeLoopD.i12HS_mul_GoodI_eq`), with `a = 2 - 3ε`,
`A = (3/2) a (1 - 3ε)/((1 - ε)²(1 - 2ε)) Γ(1 + 2ε)Γ(1 + ε)/Γ(1 + 3ε)` and
`a B_w = a/(1 - ε) Γ(1 + ε)Γ(1 - 2ε)/Γ(1 - ε)`. We compute the jet of `R` at `0` through `ε⁴`:

* the `Γ`-ratios are `exp (ε² X(ε))` with `γ`-free exponents
  (`QED.DimReg.Gamma_one_add_eq_exp`), `X_A = -π²/3 + 6ζ₃ ε - 8π⁴/45 ε² + O(ε³)` and
  `X_B = π²/3 + 2ζ₃ ε + 2π⁴/45 ε² + O(ε³)`, so their jets are `(1, 0, X₀, X₁, X₂ + X₀²/2)`;
* the rational prefactors are expanded with explicit remainders;
* the jet of `ε ↦ P(cε - 1, ε)` consists of its Taylor coefficients `∫₀¹ G_{c,n} / n!`
  (`QED.ThreeLoopD.iteratedDeriv_i12HSP_real`), whose closed forms are those of
  `QED.ThreeLoopD.SetDMastersI12RHighSPVal`, e.g. `P(ε - 1, ε) = 2 log 2 - (log² 2 + π²/3) ε
  + (log³ 2/3 + 4ζ₃) ε² - (log⁴ 2/12 + π⁴/20) ε³ + (log⁵ 2/60 - 2π²ζ₃/3 + 12ζ₅) ε⁴ + O(ε⁵)`.

Multiplying the jets, `R⁽³⁾(0) = 6 R₃` and `R⁽⁴⁾(0) = 24 R₄`
(`QED.ThreeLoopD.iteratedDeriv_three_i12HSGoodR`, `QED.ThreeLoopD.iteratedDeriv_four_i12HSGoodR`)
with

  `R₃ = -36 Li₄(1/2) - log⁴ 2/2 + 3 log³ 2 + 4π² log² 2 + 6 log² 2 + 5π² log 2/2 + 6ζ₃ log 2
    - 30 log 2 + 13π⁴/12 + 2π² + 3ζ₃/4`,

and `R₄` of weight `≤ 5` (with `Li₅(1/2)`, `ζ₅`; `QED.ThreeLoopD.i12HSGood3`). Since
`R⁽ⁿ⁺¹⁾(0) = (n + 1) ∫ Good_n` (`QED.ThreeLoopD.iteratedDeriv_succ_i12HSGoodR`),

  `∫ Good₂ = 2 R₃`, `∫ Good₃ = 6 R₄`

(`QED.ThreeLoopD.integral_i12HSGoodDn_two`, `QED.ThreeLoopD.integral_i12HSGoodDn_three`), i.e.
`[ε²] Good = R₃` and `[ε³] Good = R₄`, the values found numerically (150-digit PSLQ) before.

## Main results

* `QED.ThreeLoopD.iteratedDeriv_i12HSP_real`, `QED.ThreeLoopD.i12HSJ_P`.
* `QED.ThreeLoopD.i12HSJ_gammaA`, `QED.ThreeLoopD.i12HSJ_gammaB`.
* `QED.ThreeLoopD.i12HSJ_goodR`.
* `QED.ThreeLoopD.integral_i12HSGoodDn_two`, `QED.ThreeLoopD.integral_i12HSGoodDn_three`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory Metric QED.Polylog

namespace QED.ThreeLoopD

/-! ### The jets of `P(cε - 1, ε)` -/

/-- The Taylor coefficients of `P(cε - 1, ε)` for real `c`, `|c| ≤ 2`, as real integrals after
the substitution `x = 2t/(1 + t)`. -/
theorem iteratedDeriv_i12HSP_real {c : ℝ} (hc : |c| ≤ 2) (n : ℕ) :
    iteratedDeriv n (fun ε => i12HSP ((c : ℂ) * ε - 1) ε) 0 =
      ((∫ t in Ioo (0 : ℝ) 1, i12HSKG c n t : ℝ) : ℂ) := by
  have hc' : ‖(c : ℂ)‖ ≤ 2 := by rwa [norm_real, Real.norm_eq_abs]
  rw [iteratedDeriv_i12HSP_lin hc' n, ← i12HSK_integral_F_eq, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  simp only [i12HSKF]
  push_cast
  rfl

/-- **The jet of `P(cε - 1, ε)`** at `0`, for real `c`, `|c| ≤ 2`. -/
theorem i12HSJ_P {c : ℝ} (hc : |c| ≤ 2) :
    i12HSJ (fun ε => i12HSP ((c : ℂ) * ε - 1) ε)
      ((∫ t in Ioo (0 : ℝ) 1, i12HSKG c 0 t : ℝ) : ℂ)
      ((∫ t in Ioo (0 : ℝ) 1, i12HSKG c 1 t : ℝ) : ℂ)
      (((∫ t in Ioo (0 : ℝ) 1, i12HSKG c 2 t : ℝ) : ℂ) / 2)
      (((∫ t in Ioo (0 : ℝ) 1, i12HSKG c 3 t : ℝ) : ℂ) / 6)
      (((∫ t in Ioo (0 : ℝ) 1, i12HSKG c 4 t : ℝ) : ℂ) / 24) := by
  have hc' : ‖(c : ℂ)‖ ≤ 2 := by rwa [norm_real, Real.norm_eq_abs]
  have ha : AnalyticAt ℂ (fun ε => i12HSP ((c : ℂ) * ε - 1) ε) 0 :=
    (differentiableOn_i12HSP_lin hc').analyticAt (ball_mem_nhds _ (by norm_num))
  simpa only [iteratedDeriv_i12HSP_real hc] using i12HSJ_of_analyticAt ha

/-! ### The jets of the `Γ`-ratios -/

/-- The analytic remainder of the exponent of `Γ(1 + 2ε)Γ(1 + ε)/Γ(1 + 3ε)` over `ε⁵`. -/
noncomputable def i12HSGamYA (ε : ℂ) : ℂ :=
  42 * (zeta5 : ℂ) + ε * (2 ^ 6 * QED.DimReg.logGammaRem (2 * ε) +
    QED.DimReg.logGammaRem ε - 3 ^ 6 * QED.DimReg.logGammaRem (3 * ε))

/-- The analytic remainder of the exponent of `Γ(1 + ε)Γ(1 - 2ε)/Γ(1 - ε)` over `ε⁵`. -/
noncomputable def i12HSGamYB (ε : ℂ) : ℂ :=
  6 * (zeta5 : ℂ) + ε * (QED.DimReg.logGammaRem ε +
    2 ^ 6 * QED.DimReg.logGammaRem (-2 * ε) - QED.DimReg.logGammaRem (-ε))

theorem analyticAt_i12HSGamYA : AnalyticAt ℂ i12HSGamYA 0 := by
  have h1 : AnalyticAt ℂ (fun ε : ℂ => QED.DimReg.logGammaRem (2 * ε)) 0 :=
    QED.DimReg.analyticAt_logGammaRem.comp_of_eq (by fun_prop) (by simp)
  have h2 : AnalyticAt ℂ (fun ε : ℂ => QED.DimReg.logGammaRem (3 * ε)) 0 :=
    QED.DimReg.analyticAt_logGammaRem.comp_of_eq (by fun_prop) (by simp)
  have h3 := QED.DimReg.analyticAt_logGammaRem
  unfold i12HSGamYA; fun_prop

theorem analyticAt_i12HSGamYB : AnalyticAt ℂ i12HSGamYB 0 := by
  have h1 : AnalyticAt ℂ (fun ε : ℂ => QED.DimReg.logGammaRem (-2 * ε)) 0 :=
    QED.DimReg.analyticAt_logGammaRem.comp_of_eq (by fun_prop) (by simp)
  have h2 : AnalyticAt ℂ (fun ε : ℂ => QED.DimReg.logGammaRem (-ε)) 0 :=
    QED.DimReg.analyticAt_logGammaRem.comp_of_eq (by fun_prop) (by simp)
  have h3 := QED.DimReg.analyticAt_logGammaRem
  unfold i12HSGamYB; fun_prop

theorem i12HS_norm_mul_lt {ε : ℂ} (hε : ‖ε‖ < 1 / 4) (a : ℂ) (ha : ‖a‖ ≤ 3) : ‖a * ε‖ < 1 := by
  rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg ε]

theorem i12HS_eventually_small : ∀ᶠ ε in 𝓝 (0 : ℂ), ‖ε‖ < 1 / 4 := by
  filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with ε h
  simpa using h

theorem i12HS_exp_ratio (a b c : ℂ) : exp a * exp b / exp c = exp (a + b - c) := by
  rw [Complex.exp_sub, Complex.exp_add]

/-- **The jet of `Γ(1 + 2ε)Γ(1 + ε)/Γ(1 + 3ε)`**: `(1, 0, -π²/3, 6ζ₃, -11π⁴/90)`. -/
theorem i12HSJ_gammaA :
    i12HSJ (fun ε => Gamma (1 + 2 * ε) * Gamma (1 + ε) / Gamma (1 + 3 * ε)) 1 0
      (-(Real.pi : ℂ) ^ 2 / 3) (6 * (zeta3 : ℂ)) (-11 / 90 * (Real.pi : ℂ) ^ 4) := by
  refine (i12HSJ_exp_sq (X := fun ε => -(Real.pi : ℂ) ^ 2 / 3 + 6 * (zeta3 : ℂ) * ε +
      (-8 / 45 * (Real.pi : ℂ) ^ 4) * ε ^ 2 + ε ^ 3 * i12HSGamYA ε) analyticAt_i12HSGamYA
      fun _ => rfl).congr rfl rfl rfl rfl (by ring) |>.congr_fun ?_
  filter_upwards [i12HS_eventually_small] with ε hε
  have e1 := QED.DimReg.Gamma_one_add_eq_exp (i12HS_norm_mul_lt hε 2 (by norm_num))
  have e2 := QED.DimReg.Gamma_one_add_eq_exp (i12HS_norm_mul_lt hε 1 (by norm_num))
  have e3 := QED.DimReg.Gamma_one_add_eq_exp (i12HS_norm_mul_lt hε 3 (by norm_num))
  rw [one_mul] at e2
  rw [e1, e2, e3, i12HS_exp_ratio]
  congr 1
  simp only [i12HSGamYA]
  ring

/-- **The jet of `Γ(1 + ε)Γ(1 - 2ε)/Γ(1 - ε)`**: `(1, 0, π²/3, 2ζ₃, π⁴/10)`. -/
theorem i12HSJ_gammaB :
    i12HSJ (fun ε => Gamma (1 + ε) * Gamma (1 - 2 * ε) / Gamma (1 - ε)) 1 0
      ((Real.pi : ℂ) ^ 2 / 3) (2 * (zeta3 : ℂ)) (1 / 10 * (Real.pi : ℂ) ^ 4) := by
  refine (i12HSJ_exp_sq (X := fun ε => (Real.pi : ℂ) ^ 2 / 3 + 2 * (zeta3 : ℂ) * ε +
      (2 / 45 * (Real.pi : ℂ) ^ 4) * ε ^ 2 + ε ^ 3 * i12HSGamYB ε) analyticAt_i12HSGamYB
      fun _ => rfl).congr rfl rfl rfl rfl (by ring) |>.congr_fun ?_
  filter_upwards [i12HS_eventually_small] with ε hε
  have e1 := QED.DimReg.Gamma_one_add_eq_exp (i12HS_norm_mul_lt hε 1 (by norm_num))
  have e2 := QED.DimReg.Gamma_one_add_eq_exp (i12HS_norm_mul_lt hε (-2) (by norm_num))
  have e3 := QED.DimReg.Gamma_one_add_eq_exp (i12HS_norm_mul_lt hε (-1) (by norm_num))
  rw [one_mul] at e1
  rw [show (1 : ℂ) + -2 * ε = 1 - 2 * ε by ring] at e2
  rw [show (1 : ℂ) + -1 * ε = 1 - ε by ring] at e3
  simp only [neg_one_mul] at e3
  rw [e1, e2, e3, i12HS_exp_ratio]
  congr 1
  simp only [i12HSGamYB]
  ring

/-! ### The rational prefactors -/

theorem i12HS_eventually_ne (c : ℂ) (hc : ‖c‖ ≤ 3) : ∀ᶠ ε in 𝓝 (0 : ℂ), 1 - c * ε ≠ 0 := by
  filter_upwards [i12HS_eventually_small] with ε hε h
  have := i12HS_norm_mul_lt hε c hc
  rw [show c * ε = 1 by linear_combination -h] at this
  simp at this

/-- The jet of `(3/2)(2 - 3ε)(1 - 3ε)/((1 - ε)(1 - 2ε)(1 - ε))`. -/
theorem i12HSJ_ratA :
    i12HSJ (fun ε => 3 / 2 * ((2 - 3 * ε) * (1 - 3 * ε) / ((1 - ε) * (1 - 2 * ε) * (1 - ε))))
      3 (-3 / 2) (-15 / 2) (-33 / 2) (-63 / 2) := by
  refine ⟨fun ε => (-117 / 2 + 249 / 2 * ε - 63 * ε ^ 2) / ((1 - ε) * (1 - 2 * ε) * (1 - ε)),
    AnalyticAt.div (by fun_prop) (by fun_prop) (by norm_num), ?_⟩
  filter_upwards [i12HS_eventually_ne 1 (by norm_num), i12HS_eventually_ne 2 (by norm_num)]
    with ε h1 h2
  rw [one_mul] at h1
  field_simp
  ring

/-- The jet of `(2 - 3ε)/(1 - ε)`. -/
theorem i12HSJ_ratB : i12HSJ (fun ε => (2 - 3 * ε) / (1 - ε)) 2 (-1) (-1) (-1) (-1) := by
  refine ⟨fun ε => -1 / (1 - ε), AnalyticAt.div (by fun_prop) (by fun_prop) (by norm_num), ?_⟩
  filter_upwards [i12HS_eventually_ne 1 (by norm_num)] with ε h1
  rw [one_mul] at h1
  field_simp
  ring

/-- The jet of `A(ε) = (3/2) a (1 - 3ε)/((1 - ε)²(1 - 2ε)) Γ(1 + 2ε)Γ(1 + ε)/Γ(1 + 3ε)`. -/
theorem i12HSJ_A :
    i12HSJ (fun ε => 3 / 2 * ((2 - 3 * ε) * (1 - 3 * ε) / ((1 - ε) * (1 - 2 * ε) * (1 - ε))) *
        (Gamma (1 + 2 * ε) * Gamma (1 + ε) / Gamma (1 + 3 * ε)))
      3 (-3 / 2) (-15 / 2 - (Real.pi : ℂ) ^ 2) (-33 / 2 + (Real.pi : ℂ) ^ 2 / 2 + 18 * zeta3)
      (-63 / 2 + 5 / 2 * (Real.pi : ℂ) ^ 2 - 9 * zeta3 - 11 / 30 * (Real.pi : ℂ) ^ 4) :=
  (i12HSJ_ratA.mul i12HSJ_gammaA).congr (by ring) (by ring) (by ring) (by ring) (by ring)

/-- The jet of `a B_w = (2 - 3ε) Γ(1 + ε)Γ(1 - 2ε)/Γ(2 - ε)`. -/
theorem i12HSJ_aBw :
    i12HSJ (fun ε => (2 - 3 * ε) * i12HSBw ε)
      2 (-1) (-1 + 2 / 3 * (Real.pi : ℂ) ^ 2) (-1 - (Real.pi : ℂ) ^ 2 / 3 + 4 * zeta3)
      (-1 - (Real.pi : ℂ) ^ 2 / 3 - 2 * zeta3 + 1 / 5 * (Real.pi : ℂ) ^ 4) := by
  refine ((i12HSJ_ratB.mul i12HSJ_gammaB).congr (by ring) (by ring) (by ring) (by ring)
    (by ring)).congr_fun ?_
  filter_upwards [i12HS_eventually_ne 1 (by norm_num)] with ε h1
  rw [one_mul] at h1
  rw [i12HSBw, show (2 : ℂ) - ε = 1 - ε + 1 by ring, Complex.Gamma_add_one _ h1]
  field_simp

/-! ### The jet of `R` and the good part at orders `2` and `3` -/

/-- `[ε²] Good = R₃` (`Li₄(1/2)` enters through `P(2ε - 1, ε)`). -/
noncomputable def i12HSGood2 : ℝ :=
  -1 / 2 * Real.log 2 ^ 4 + 3 * Real.log 2 ^ 3 + 4 * Real.log 2 ^ 2 * Real.pi ^ 2
    + 6 * Real.log 2 ^ 2 + 5 / 2 * Real.log 2 * Real.pi ^ 2 + 6 * Real.log 2 * zeta3
    - 30 * Real.log 2 + 13 / 12 * Real.pi ^ 4 + 2 * Real.pi ^ 2 + 3 / 4 * zeta3
    - 36 * Li 4 (1 / 2)

/-- `[ε³] Good = R₄`. -/
noncomputable def i12HSGood3 : ℝ :=
  18 / 5 * Real.log 2 ^ 5 + 1 / 4 * Real.log 2 ^ 4 - 22 / 3 * Real.log 2 ^ 3 * Real.pi ^ 2
    + Real.log 2 ^ 3 - 2 * Real.log 2 ^ 2 * Real.pi ^ 2 + 60 * Real.log 2 ^ 2 * zeta3
    + 15 * Real.log 2 ^ 2 - 67 / 30 * Real.log 2 * Real.pi ^ 4
    + 13 / 2 * Real.log 2 * Real.pi ^ 2 - 3 * Real.log 2 * zeta3
    + 144 * Real.log 2 * Li 4 (1 / 2) - 60 * Real.log 2 - 13 / 24 * Real.pi ^ 4
    - 17 / 2 * Real.pi ^ 2 * zeta3 + 5 * Real.pi ^ 2 - 93 / 4 * zeta3 - 621 / 4 * zeta5
    + 18 * Li 4 (1 / 2) + 108 * Li 5 (1 / 2)

theorem i12HS_P_one_eq : (fun ε => i12HSP (((1 : ℝ) : ℂ) * ε - 1) ε) =
    fun ε => i12HSP (ε - 1) ε := by
  funext ε; push_cast; rw [one_mul]

theorem i12HS_P_negOne_eq : (fun ε => i12HSP (((-1 : ℝ) : ℂ) * ε - 1) ε) =
    fun ε => i12HSP (-ε - 1) ε := by
  funext ε; push_cast; rw [neg_one_mul]

theorem i12HS_P_two_eq : (fun ε => i12HSP (((2 : ℝ) : ℂ) * ε - 1) ε) =
    fun ε => i12HSP (2 * ε - 1) ε := by
  funext ε; push_cast; rfl

/-- The jet of `P(ε - 1, ε)`. -/
theorem i12HSJ_P_one :
    i12HSJ (fun ε => i12HSP (ε - 1) ε)
      (2 * (Real.log 2 : ℂ))
      (-(Real.log 2 : ℂ) ^ 2 - 1 / 3 * (Real.pi : ℂ) ^ 2)
      (1 / 3 * (Real.log 2 : ℂ) ^ 3 + 4 * (zeta3 : ℂ))
      (-1 / 12 * (Real.log 2 : ℂ) ^ 4 - 1 / 20 * (Real.pi : ℂ) ^ 4)
      (1 / 60 * (Real.log 2 : ℂ) ^ 5 - 2 / 3 * (Real.pi : ℂ) ^ 2 * (zeta3 : ℂ)
        + 12 * (zeta5 : ℂ)) := by
  have h := i12HSJ_P (c := 1) (by norm_num [abs_of_pos])
  rw [i12HS_P_one_eq] at h
  refine h.congr ?_ ?_ ?_ ?_ ?_ <;>
    simp only [i12HSKG_zero_integral, i12HSKG_one_integral, i12HSKG_two_integral,
      i12HSKG_three_integral, i12HSKG_four_integral] <;> push_cast <;> ring

/-- The jet of `P(-ε - 1, ε)`. -/
theorem i12HSJ_P_negOne :
    i12HSJ (fun ε => i12HSP (-ε - 1) ε)
      (2 * (Real.log 2 : ℂ))
      (3 * (Real.log 2 : ℂ) ^ 2)
      (7 / 3 * (Real.log 2 : ℂ) ^ 3)
      (5 / 4 * (Real.log 2 : ℂ) ^ 4)
      (31 / 60 * (Real.log 2 : ℂ) ^ 5) := by
  have h := i12HSJ_P (c := -1) (by norm_num [abs_of_pos])
  rw [i12HS_P_negOne_eq] at h
  refine h.congr ?_ ?_ ?_ ?_ ?_ <;>
    simp only [i12HSKG_zero_integral, i12HSKG_one_integral, i12HSKG_two_integral,
      i12HSKG_three_integral, i12HSKG_four_integral] <;> push_cast <;> ring

/-- The jet of `P(2 * ε - 1, ε)`. -/
theorem i12HSJ_P_two :
    i12HSJ (fun ε => i12HSP (2 * ε - 1) ε)
      (2 * (Real.log 2 : ℂ))
      (-3 * (Real.log 2 : ℂ) ^ 2 - 1 / 2 * (Real.pi : ℂ) ^ 2)
      (7 / 3 * (Real.log 2 : ℂ) ^ 3 + 1 / 2 * (Real.log 2 : ℂ) * (Real.pi : ℂ) ^ 2
        + 27 / 4 * (zeta3 : ℂ))
      (-1 / 2 * (Real.log 2 : ℂ) ^ 4 - (Real.log 2 : ℂ) ^ 2 * (Real.pi : ℂ) ^ 2
        + 9 * (Real.log 2 : ℂ) * (zeta3 : ℂ) - 17 / 60 * (Real.pi : ℂ) ^ 4
        + 18 * (Li 4 (1 / 2) : ℂ))
      (-61 / 30 * (Real.log 2 : ℂ) ^ 5 + 7 / 3 * (Real.log 2 : ℂ) ^ 3 * (Real.pi : ℂ) ^ 2
        - 36 * (Real.log 2 : ℂ) ^ 2 * (zeta3 : ℂ)
        + 17 / 60 * (Real.log 2 : ℂ) * (Real.pi : ℂ) ^ 4
        - 72 * (Real.log 2 : ℂ) * (Li 4 (1 / 2) : ℂ) - 3 * (Real.pi : ℂ) ^ 2 * (zeta3 : ℂ)
        + 765 / 8 * (zeta5 : ℂ) - 54 * (Li 5 (1 / 2) : ℂ)) := by
  have h := i12HSJ_P (c := 2) (by norm_num [abs_of_pos])
  rw [i12HS_P_two_eq] at h
  refine h.congr ?_ ?_ ?_ ?_ ?_ <;>
    simp only [i12HSKG_zero_integral, i12HSKG_one_integral, i12HSKG_two_integral,
      i12HSKG_three_integral, i12HSKG_four_integral] <;> push_cast <;> ring

/-- **The jet of `R`** at `0`: `(0, 0, R₂, R₃, R₄)`, `R₂ = [ε] Good`. -/
theorem i12HSJ_goodR :
    i12HSJ i12HSGoodR 0 0
      (-6 * (Real.log 2 : ℂ) ^ 3 - 5 * (Real.log 2 : ℂ) * (Real.pi : ℂ) ^ 2
        - 12 * (Real.log 2 : ℂ) - 3 / 2 * (zeta3 : ℂ))
      (i12HSGood2 : ℂ) (i12HSGood3 : ℂ) := by
  refine ((((i12HSJ_A.mul i12HSJ_P_one).sub ((i12HSJ_aBw.const_mul (1 / 2)).mul
    i12HSJ_P_negOne)).sub (i12HSJ_aBw.mul i12HSJ_P_two)).congr ?_ ?_ ?_ ?_ ?_).congr_fun
    (Eventually.of_forall fun ε => ?_)
  · ring
  · ring
  · ring
  · simp only [i12HSGood2]; push_cast; ring
  · simp only [i12HSGood3]; push_cast; ring
  · simp only [i12HSGoodR]; ring

/-- **`R⁽³⁾(0) = 6 R₃`.** -/
theorem iteratedDeriv_three_i12HSGoodR :
    iteratedDeriv 3 i12HSGoodR 0 = 6 * (i12HSGood2 : ℂ) := by
  exact i12HSJ_goodR.iteratedDeriv_three

/-- **`R⁽⁴⁾(0) = 24 R₄`.** -/
theorem iteratedDeriv_four_i12HSGoodR :
    iteratedDeriv 4 i12HSGoodR 0 = 24 * (i12HSGood3 : ℂ) := by
  exact i12HSJ_goodR.iteratedDeriv_four

/-- **The good part at order `2`**: `∫ Good₂ = 2 R₃`. -/
theorem integral_i12HSGoodDn_two :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
      i12HSGoodDn 2 z.1 z.2.1 z.2.2 = 2 * i12HSGood2 := by
  have h : iteratedDeriv 3 i12HSGoodR 0 = (2 + 1) * ((∫ z in Ioo (0 : ℝ) 1 ×ˢ
      (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1), i12HSGoodDn 2 z.1 z.2.1 z.2.2 : ℝ) : ℂ) := by
    exact_mod_cast iteratedDeriv_succ_i12HSGoodR 2
  rw [iteratedDeriv_three_i12HSGoodR] at h
  have h' : ((∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
      i12HSGoodDn 2 z.1 z.2.1 z.2.2 : ℝ) : ℂ) = ((2 * i12HSGood2 : ℝ) : ℂ) := by
    push_cast; linear_combination -h / 3
  exact_mod_cast h'

/-- **The good part at order `3`**: `∫ Good₃ = 6 R₄`. -/
theorem integral_i12HSGoodDn_three :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
      i12HSGoodDn 3 z.1 z.2.1 z.2.2 = 6 * i12HSGood3 := by
  have h : iteratedDeriv 4 i12HSGoodR 0 = (3 + 1) * ((∫ z in Ioo (0 : ℝ) 1 ×ˢ
      (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1), i12HSGoodDn 3 z.1 z.2.1 z.2.2 : ℝ) : ℂ) := by
    exact_mod_cast iteratedDeriv_succ_i12HSGoodR 3
  rw [iteratedDeriv_four_i12HSGoodR] at h
  have h' : ((∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
      i12HSGoodDn 3 z.1 z.2.1 z.2.2 : ℝ) : ℂ) = ((6 * i12HSGood3 : ℝ) : ℂ) := by
    push_cast; linear_combination -h / 4
  exact_mod_cast h'

end QED.ThreeLoopD
