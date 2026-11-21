/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMasters
public import QED.ThreeLoopD.SetDMastersGamma
public import QED.DimReg.GammaTaylor
public import QED.DimReg.OneLoopClosedForm
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (d) of `A₁⁽⁶⁾`: the masters `I₁₄` and `I₁₆` are proved

The Laporta–Remiddi (1996) masters `I₁₄ = ∫ 1 / (D₃ D₅ D₆ D₇)` and `I₁₆ = ∫ 1 / (D₃ D₄ D₇ D₈)`
(normalization as in `QED.DimReg.LR96Family`) are products of one-loop `Γ`-function closed forms:

* `I₁₄`: a massless bubble (`QED.ThreeLoopD.masslessBubble`) inserted as the massless line of the
  two-loop vacuum graph with two unit masses (`QED.ThreeLoopD.vacuumTwoMass`, massless power
  `ω`), `QED.ThreeLoopD.lr96I14`;
* `I₁₆`: a unit tadpole (`QED.DimReg.tadpole`) times a massless bubble inserted as the massless
  line of the on-shell one-loop integral (`QED.DimReg.OneLoopSchwinger.phi`, massless power `ω`),
  `QED.ThreeLoopD.lr96I16`.

The tadpole and the on-shell closed form `phi` are proved from their parametric integrals in
`QED.DimReg`; the massless bubble and the two-mass vacuum closed forms are textbook formulas taken
as definitions, and the factorization of the two graphs into these pieces is recorded in the
docstrings, not formalized (as for the Wick rotation in `QED.DimReg.LR96Family`).

**Expansions.** Dividing by `C(ε) = (π ^ ε Γ(1 + ε))³`, each master is a rational function of `ε`
times a ratio of `Γ(1 + aᵢ ε)` with `∑ nᵢ aᵢ = 0` (`QED.ThreeLoopD.setDMasterI14_eq`,
`QED.ThreeLoopD.setDMasterI16_eq`):
`I₁₄ C⁻¹ = (4ε - 1)(4ε - 2) / (3ε³ (2ε - 1)² (3ε - 1)(3ε - 2)(1 - ε)) ·
  Γ(1 - ε) Γ(1 + 2ε)² Γ(1 + 3ε) / (Γ(1 + ε)² Γ(1 + 4ε))`,
`I₁₆ C⁻¹ = (2 - 4ε)(1 - 4ε) / (ε³ (ε - 1)(1 - 2ε) 2(2ε - 1)(2 - 3ε)(1 - 3ε)) ·
  Γ(1 - ε)² Γ(1 + 2ε) Γ(1 - 4ε) / (Γ(1 + ε) Γ(1 - 2ε) Γ(1 - 3ε))`.
By `QED.DimReg.Gamma_one_add_eq_exp` each `Γ`-ratio is `exp(W(ε))` with `W` the explicit polynomial
`8ζ₃ε³ - 2π⁴/5 ε⁴ + 144ζ₅ε⁵` (resp. `2π²/3 ε² + 8ζ₃ε³ + 22π⁴/45 ε⁴ + 144ζ₅ε⁵`) plus `ε⁶` times an
analytic function; `γ` cancels. Truncating `exp` (`QED.DimReg.exp_eq_expRem3`) gives the inputs
`HasTruncLaurent setDMasterI14 setDLaurentI14 3` and `HasTruncLaurent setDMasterI16
setDLaurentI16 2` with explicit analytic remainders (`QED.ThreeLoopD.setDGammaR14`,
`QED.ThreeLoopD.setDGammaR16`), checked by `ring`.

## Main results

* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI14`, `QED.ThreeLoopD.hasTruncLaurent_setDMasterI16`.
* `QED.ThreeLoopD.SetDMasters.Expansions.of_I14_I16_I18`: the eleven inputs from the remaining
  eight.
* `QED.ThreeLoopD.SetDMasters.tendsto_of_I14_I16_I18`: the set (d) value from the eight inputs.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### Closed forms -/

/-- The massless one-loop bubble coefficient `G(1, 1) = Γ(2 - d/2) Γ(d/2 - 1)² / Γ(d - 2)`:
`∫ dᵈk / π ^ (d/2) · 1 / (k² (k + q)²) = G(1, 1) (q²) ^ (d/2 - 2)` (Euclidean; the textbook closed
form, see e.g. Smirnov, *Evaluating Feynman Integrals* (2004)). Taken as a definition: the
integral itself is not formalized here. -/
noncomputable def masslessBubble (d : ℂ) : ℂ :=
  Gamma (2 - d / 2) * Gamma (d / 2 - 1) ^ 2 / Gamma (d - 2)

/-- The two-loop vacuum integral with two unit-mass lines (power `1`) and a massless line of power
`ν`: `∫∫ dᵈk dᵈl / π ^ d · 1 / ((k² + 1) (l² + 1) ((k - l)²) ^ ν)
= Γ(1 + ν - d/2)² Γ(2 + ν - d) Γ(d/2 - ν) / (Γ(d/2) Γ(2 + 2ν - d))` (the `m₁ = m₂`, `m₃ = 0`
case of the two-loop vacuum integral; see e.g. Davydychev–Tausk, Nucl. Phys. B 397 (1993) 123).
Taken as a definition: the integral itself is not formalized here. -/
noncomputable def vacuumTwoMass (ν d : ℂ) : ℂ :=
  Gamma (1 + ν - d / 2) ^ 2 * Gamma (2 + ν - d) * Gamma (d / 2 - ν) /
    (Gamma (d / 2) * Gamma (2 + 2 * ν - d))

/-- `I₁₄` in LR96's normalization, `1 / (D₃ D₅ D₆ D₇)`: the photons `k₁, k₂` form a massless bubble
with total momentum `q = k₁ + k₂`, giving `G(1, 1) (q²) ^ (-ω)`; what remains is the two-loop
vacuum graph with the massive lines `D₃, D₅` and the bubble as a massless line of power
`ν = 2 - d/2 = ω`. Each loop carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I14 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 *
    (masslessBubble (4 - 2 * ω) * vacuumTwoMass (2 - (4 - 2 * ω) / 2) (4 - 2 * ω))

/-- `I₁₆` in LR96's normalization, `1 / (D₃ D₄ D₇ D₈)`: `k₁` occurs only in `D₃`, a unit tadpole
(`QED.DimReg.tadpole`); the photons `k₂, k₃` form a massless bubble `G(1, 1) (q²) ^ (-ω)`
(`q = k₂ + k₃`); what remains is the on-shell one-loop integral with the massive line `D₄` and the
bubble as a massless line of power `2 - d/2 = ω`, whose closed form is
`QED.DimReg.OneLoopSchwinger.phi ω 1 d`. Each loop carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I16 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 *
    (QED.DimReg.tadpole 1 1 (4 - 2 * ω) * masslessBubble (4 - 2 * ω) *
      QED.DimReg.OneLoopSchwinger.phi (2 - (4 - 2 * ω) / 2) 1 (4 - 2 * ω))

/-- The master `I₁₄ C⁻¹`. -/
noncomputable def setDMasterI14 (ε : ℂ) : ℂ := lr96I14 ε / lr96C ε

/-- The master `I₁₆ C⁻¹`. -/
noncomputable def setDMasterI16 (ε : ℂ) : ℂ := lr96I16 ε / lr96C ε

/-! ### Small-`ε` facts and `Γ` recurrences -/

theorem setDGamma_lin_ne_zero {ε : ℂ} (hε : ‖ε‖ < 1 / 8) (c a : ℂ) (hc : 1 ≤ ‖c‖) (ha : ‖a‖ ≤ 4)
    {x : ℂ} (hx : x = c + a * ε) : x ≠ 0 := by
  rintro rfl
  have h : c = -(a * ε) := by linear_combination -hx
  have h2 := congrArg norm h
  rw [norm_neg, norm_mul] at h2
  nlinarith [norm_nonneg a, norm_nonneg ε]

theorem setDGamma_norm_mul_lt_one {ε : ℂ} (hε : ‖ε‖ < 1 / 8) (a : ℂ) (ha : ‖a‖ ≤ 4) :
    ‖a * ε‖ < 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg ε]

theorem setDGamma_Gamma_two_sub_ne_zero {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : Gamma (2 - 2 * ε) ≠ 0 := by
  refine Gamma_ne_zero_of_re_pos ?_
  have := abs_re_le_norm ε
  rw [sub_re, mul_re]
  norm_num
  linarith [abs_le.mp this]


theorem setDGamma_mul_ne_zero {ε : ℂ} (h0 : ε ≠ 0) (a : ℂ) (ha : a ≠ 0) {x : ℂ} (hx : x = a * ε) :
    x ≠ 0 := hx ▸ mul_ne_zero ha h0

theorem Gamma_one_add_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : Gamma (1 + z) ≠ 0 := by
  refine Gamma_ne_zero_of_re_pos ?_
  have := abs_re_le_norm z
  rw [add_re, one_re]
  linarith [abs_le.mp this]

theorem Gamma_eq_div_one {s t p : ℂ} (hs0 : s ≠ 0) (ht : t = s + 1) (hp : p = s) :
    Gamma s = Gamma t / p := by
  rw [eq_div_iff (hp ▸ hs0), ht, Gamma_add_one _ hs0, hp]
  ring

theorem Gamma_eq_div_two {s t p : ℂ} (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) (ht : t = s + 1 + 1)
    (hp : p = (s + 1) * s) : Gamma s = Gamma t / p := by
  rw [eq_div_iff (hp ▸ mul_ne_zero hs1 hs0), ht, Gamma_add_one _ hs1, Gamma_add_one _ hs0, hp]
  ring

theorem Gamma_eq_div_three {s t p : ℂ} (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) (hs2 : s + 1 + 1 ≠ 0)
    (ht : t = s + 1 + 1 + 1) (hp : p = (s + 1 + 1) * (s + 1) * s) : Gamma s = Gamma t / p := by
  rw [eq_div_iff (hp ▸ mul_ne_zero (mul_ne_zero hs2 hs1) hs0), ht, Gamma_add_one _ hs2,
    Gamma_add_one _ hs1, Gamma_add_one _ hs0, hp]
  ring

/-- `I₁₄ C⁻¹` as a rational function times a ratio of `Γ(1 + a ε)`. -/
theorem setDMasterI14_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setDMasterI14 ε = (4 * ε - 1) * (4 * ε - 2) /
        (3 * ε ^ 3 * ((2 * ε - 1) ^ 2 * (3 * ε - 1) * (3 * ε - 2) * (1 - ε))) *
      (Gamma (1 + (-1) * ε) * Gamma (1 + 2 * ε) ^ 2 * Gamma (1 + 3 * ε) /
        (Gamma (1 + 1 * ε) ^ 2 * Gamma (1 + 4 * ε))) := by
  have hb : ‖ε‖ < 1 := by linarith
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have hm := fun a ha {x : ℂ} (hx : x = a * ε) => setDGamma_mul_ne_zero h0 a ha hx
  simp only [setDMasterI14, lr96I14, lr96C, masslessBubble, vacuumTwoMass,
    QED.DimReg.lr96LoopFactor_four_sub]
  rw [Gamma_eq_div_one (s := 2 - (4 - 2 * ε) / 2) (t := 1 + 1 * ε) (p := ε)
      (hm 1 one_ne_zero (by ring)) (by ring) (by ring),
    show (4 - 2 * ε) / 2 - 1 = 1 + (-1) * ε by ring,
    show (4 : ℂ) - 2 * ε - 2 = 2 - 2 * ε by ring,
    Gamma_eq_div_two (s := 1 + (2 - (4 - 2 * ε) / 2) - (4 - 2 * ε) / 2) (t := 1 + 2 * ε)
      (p := 2 * ε * (2 * ε - 1)) (hl (-1) 2 (by norm_num) (by norm_num) (by ring))
      (hm 2 two_ne_zero (by ring)) (by ring) (by ring),
    Gamma_eq_div_three (s := 2 + (2 - (4 - 2 * ε) / 2) - (4 - 2 * ε)) (t := 1 + 3 * ε)
      (p := 3 * ε * (3 * ε - 1) * (3 * ε - 2)) (hl (-2) 3 (by norm_num) (by norm_num) (by ring))
      (hl (-1) 3 (by norm_num) (by norm_num) (by ring)) (hm 3 (by norm_num) (by ring)) (by ring)
      (by ring),
    show (4 - 2 * ε) / 2 - (2 - (4 - 2 * ε) / 2) = 2 - 2 * ε by ring,
    Gamma_eq_div_three (s := 2 + 2 * (2 - (4 - 2 * ε) / 2) - (4 - 2 * ε)) (t := 1 + 4 * ε)
      (p := 4 * ε * (4 * ε - 1) * (4 * ε - 2)) (hl (-2) 4 (by norm_num) (by norm_num) (by ring))
      (hl (-1) 4 (by norm_num) (by norm_num) (by ring)) (hm 4 (by norm_num) (by ring)) (by ring)
      (by ring),
    show (4 - 2 * ε) / 2 = 1 + (-1) * ε + 1 by ring, Gamma_add_one _ (hl 1 (-1) (by norm_num)
      (by norm_num) (by ring)), show (1 : ℂ) + ε = 1 + 1 * ε by ring]
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  have hG1 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hG4 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 4 (by norm_num))
  have hG22 := setDGamma_Gamma_two_sub_ne_zero hε
  have h1 := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
  have h2 := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
  have h3 := hl (-2) 3 (by norm_num) (by norm_num) (x := 3 * ε - 2) (by ring)
  have h4 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have h5 := hl (-1) 4 (by norm_num) (by norm_num) (x := 4 * ε - 1) (by ring)
  have h6 := hl (-2) 4 (by norm_num) (by norm_num) (x := 4 * ε - 2) (by ring)
  have h7 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 + (-1) * ε) (by ring)
  have hGm := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-1) (by norm_num))
  generalize Gamma (1 + 1 * ε) = A at *
  generalize Gamma (1 + (-1) * ε) = B at *
  generalize Gamma (1 + 2 * ε) = C at *
  generalize Gamma (1 + 3 * ε) = D at *
  generalize Gamma (1 + 4 * ε) = E at *
  generalize Gamma (2 - 2 * ε) = F at *
  generalize (π : ℂ) ^ ε = P at *
  rw [show (1 : ℂ) + -1 * ε = 1 - ε by ring]
  field_simp
  ring

/-! ### `I₁₄` -/

theorem exp_ratio14 (a b c d e : ℂ) :
    exp a * exp b ^ 2 * exp c / (exp d ^ 2 * exp e) = exp (a + 2 * b + c - 2 * d - e) := by
  rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_add, Complex.exp_add, two_mul, two_mul,
    Complex.exp_add, Complex.exp_add]
  ring

/-- The analytic remainder of the exponent for `I₁₄`. -/
noncomputable def setDGammaV14 (ε : ℂ) : ℂ :=
  (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε) + 2 * 2 ^ 6 * QED.DimReg.logGammaRem (2 * ε) +
    3 ^ 6 * QED.DimReg.logGammaRem (3 * ε) - 2 * 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) -
    4 ^ 6 * QED.DimReg.logGammaRem (4 * ε)

/-- The exponent for `I₁₄`, divided by `ε ^ 3`. -/
noncomputable def setDGammaX14 (ε : ℂ) : ℂ :=
  8 * (zeta3 : ℂ) - 2 / 5 * (π : ℂ) ^ 4 * ε + 144 * (zeta5 : ℂ) * ε ^ 2 + ε ^ 3 * setDGammaV14 ε

/-- The polynomial part of the remainder for `I₁₄`. -/
noncomputable def setDGammaP14 (ε : ℂ) : ℂ :=
  (-10 * (zeta3 : ℂ) + 1008 * (zeta5 : ℂ) - 5 * (π : ℂ) ^ 4 - 85175 / 32) +
    (-864 * (zeta3 : ℂ) - 7776 * (zeta5 : ℂ) + 48 * (π : ℂ) ^ 4 + 63015 / 4) * ε +
    (3514 * (zeta3 : ℂ) + 18000 * (zeta5 : ℂ) - 659 / 5 * (π : ℂ) ^ 4 - 1105201 / 32) * ε ^ 2 +
    (-4392 * (zeta3 : ℂ) - 15552 * (zeta5 : ℂ) + 684 / 5 * (π : ℂ) ^ 4 + 266049 / 8) * ε ^ 3 +
    (1800 * (zeta3 : ℂ) + 5184 * (zeta5 : ℂ) - 252 / 5 * (π : ℂ) ^ 4 - 94437 / 8) * ε ^ 4

/-- The denominator `(2ε - 1)² (3ε - 1) (3ε - 2) (1 - ε)` for `I₁₄`. -/
noncomputable def setDGammaD14 (ε : ℂ) : ℂ :=
  (2 * ε - 1) ^ 2 * (3 * ε - 1) * (3 * ε - 2) * (1 - ε)

/-- The remainder `R₁₄` with `I₁₄ C⁻¹ = L₁₄ + ε³ R₁₄`. -/
noncomputable def setDGammaR14 (ε : ℂ) : ℂ :=
  (setDGammaP14 ε + (4 * ε - 1) * (4 * ε - 2) * (setDGammaV14 ε + setDGammaX14 ε ^ 2 / 2 +
    ε ^ 3 * setDGammaX14 ε ^ 3 * QED.DimReg.expRem3 (ε ^ 3 * setDGammaX14 ε))) /
    (3 * setDGammaD14 ε)

theorem gammaRatio14_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    Gamma (1 + (-1) * ε) * Gamma (1 + 2 * ε) ^ 2 * Gamma (1 + 3 * ε) /
        (Gamma (1 + 1 * ε) ^ 2 * Gamma (1 + 4 * ε)) = exp (ε ^ 3 * setDGammaX14 ε) := by
  rw [QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 3 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 4 (by norm_num)), exp_ratio14]
  congr 1
  simp only [setDGammaX14, setDGammaV14]
  ring

theorem analyticAt_logGammaRem_mul (a : ℂ) :
    AnalyticAt ℂ (fun ε => QED.DimReg.logGammaRem (a * ε)) 0 :=
  QED.DimReg.analyticAt_logGammaRem.comp_of_eq (by fun_prop) (by simp)

theorem analyticAt_setDGammaV14 : AnalyticAt ℂ setDGammaV14 0 := by
  have h1 := analyticAt_logGammaRem_mul (-1)
  have h2 := analyticAt_logGammaRem_mul 2
  have h3 := analyticAt_logGammaRem_mul 3
  have h4 := analyticAt_logGammaRem_mul 1
  have h5 := analyticAt_logGammaRem_mul 4
  unfold setDGammaV14
  fun_prop

theorem analyticAt_setDGammaR14 : AnalyticAt ℂ setDGammaR14 0 := by
  have hV := analyticAt_setDGammaV14
  have hX : AnalyticAt ℂ setDGammaX14 0 := by unfold setDGammaX14; fun_prop
  have hE : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 3 * setDGammaX14 ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hP : AnalyticAt ℂ setDGammaP14 0 := by unfold setDGammaP14; fun_prop
  have hD : AnalyticAt ℂ setDGammaD14 0 := by unfold setDGammaD14; fun_prop
  unfold setDGammaR14
  refine AnalyticAt.div (by fun_prop) (by fun_prop) ?_
  simp [setDGammaD14]

theorem setDGamma_eventually_small : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ‖ε‖ < 1 / 8 :=
  nhdsWithin_le_nhds (Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8))
    fun x hx => by simpa using hx)

/-- **The input for `I₁₄`, proved**: `I₁₄ C⁻¹ = L₁₄(ε) + ε³ R₁₄(ε)` with `R₁₄` analytic at `0`. -/
theorem hasTruncLaurent_setDMasterI14 : HasTruncLaurent setDMasterI14 setDLaurentI14 3 := by
  refine ⟨setDGammaR14, analyticAt_setDGammaR14, ?_⟩
  filter_upwards [setDGamma_eventually_small, self_mem_nhdsWithin] with ε hε h0
  have h0 : ε ≠ 0 := h0
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
  have h2 := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
  have h3 := hl (-2) 3 (by norm_num) (by norm_num) (x := 3 * ε - 2) (by ring)
  have h4 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  rw [setDMasterI14_eq h0 hε, gammaRatio14_eq hε, QED.DimReg.exp_eq_expRem3, setDGammaR14]
  generalize QED.DimReg.expRem3 (ε ^ 3 * setDGammaX14 ε) = E
  simp only [setDLaurentI14, setDGammaX14, setDGammaP14, setDGammaD14]
  generalize setDGammaV14 ε = V
  have hD : (2 * ε - 1) ^ 2 * (3 * ε - 1) * (3 * ε - 2) * (1 - ε) ≠ 0 := by
    simp [h1, h2, h3, h4]
  generalize hDd : (2 * ε - 1) ^ 2 * (3 * ε - 1) * (3 * ε - 2) * (1 - ε) = D at *
  field_simp
  rw [← hDd]
  ring

/-! ### `I₁₆` -/

/-- The denominator `(ε - 1) (1 - 2ε) · 2 (2ε - 1) · (2 - 3ε) (1 - 3ε)` for `I₁₆`. -/
noncomputable def setDGammaD16 (ε : ℂ) : ℂ :=
  (ε - 1) * (1 - 2 * ε) * (2 * (2 * ε - 1)) * (2 - 3 * ε) * (1 - 3 * ε)

/-- `I₁₆ C⁻¹` as a rational function times a ratio of `Γ(1 + a ε)`. -/
theorem setDMasterI16_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setDMasterI16 ε = (2 - 4 * ε) * (1 - 4 * ε) / (ε ^ 3 * setDGammaD16 ε) *
      (Gamma (1 + (-1) * ε) ^ 2 * Gamma (1 + 2 * ε) * Gamma (1 + (-4) * ε) /
        (Gamma (1 + 1 * ε) * Gamma (1 + (-2) * ε) * Gamma (1 + (-3) * ε))) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have hm := fun a ha {x : ℂ} (hx : x = a * ε) => setDGamma_mul_ne_zero h0 a ha hx
  simp only [setDMasterI16, lr96I16, lr96C, masslessBubble, QED.DimReg.tadpole,
    QED.DimReg.OneLoopSchwinger.phi, QED.DimReg.lr96LoopFactor_four_sub, Complex.Gamma_one,
    ofReal_one, one_cpow, div_one, mul_one, inv_one]
  rw [Gamma_eq_div_two (s := 1 - (4 - 2 * ε) / 2) (t := 1 + 1 * ε) (p := ε * (ε - 1))
      (hl (-1) 1 (by norm_num) (by norm_num) (by ring)) (hm 1 one_ne_zero (by ring)) (by ring)
      (by ring),
    Gamma_eq_div_one (s := 2 - (4 - 2 * ε) / 2) (t := 1 + 1 * ε) (p := ε)
      (hm 1 one_ne_zero (by ring)) (by ring) (by ring),
    show (4 - 2 * ε) / 2 - 1 = 1 + (-1) * ε by ring,
    show (4 : ℂ) - 2 * ε - 2 = 1 + (-2) * ε + 1 by ring,
    Gamma_add_one _ (hl 1 (-2) (by norm_num) (by norm_num) (by ring)),
    Gamma_eq_div_two (s := 2 - (4 - 2 * ε) / 2 + 1 - (4 - 2 * ε) / 2) (t := 1 + 2 * ε)
      (p := 2 * ε * (2 * ε - 1)) (hl (-1) 2 (by norm_num) (by norm_num) (by ring))
      (hm 2 two_ne_zero (by ring)) (by ring) (by ring),
    show 4 - 2 * ε - 2 * (2 - (4 - 2 * ε) / 2) - 1 = 1 + (-4) * ε + 1 + 1 by ring,
    Gamma_add_one _ (hl 2 (-4) (by norm_num) (by norm_num) (by ring)),
    Gamma_add_one _ (hl 1 (-4) (by norm_num) (by norm_num) (by ring)),
    show 4 - 2 * ε - (2 - (4 - 2 * ε) / 2) - 1 = 1 + (-3) * ε + 1 + 1 by ring,
    Gamma_add_one _ (hl 2 (-3) (by norm_num) (by norm_num) (by ring)),
    Gamma_add_one _ (hl 1 (-3) (by norm_num) (by norm_num) (by ring)),
    show (1 : ℂ) + ε = 1 + 1 * ε by ring]
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  have hG1 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hG2 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-2) (by norm_num))
  have hG3 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-3) (by norm_num))
  have h1 := hl (-1) 1 (by norm_num) (by norm_num) (x := ε - 1) (by ring)
  have h2 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have h3 := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
  have h4 := hl 2 (-3) (by norm_num) (by norm_num) (x := 2 - 3 * ε) (by ring)
  have h5 := hl 1 (-3) (by norm_num) (by norm_num) (x := 1 - 3 * ε) (by ring)
  have h6 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 + (-2) * ε) (by ring)
  have h7 := hl 1 (-3) (by norm_num) (by norm_num) (x := 1 + (-3) * ε) (by ring)
  have h8 := hl 2 (-3) (by norm_num) (by norm_num) (x := 1 + (-3) * ε + 1) (by ring)
  generalize Gamma (1 + 1 * ε) = A at *
  generalize Gamma (1 + (-1) * ε) = B at *
  generalize Gamma (1 + 2 * ε) = C at *
  generalize Gamma (1 + (-4) * ε) = D at *
  generalize Gamma (1 + (-2) * ε) = E at *
  generalize Gamma (1 + (-3) * ε) = F at *
  generalize (π : ℂ) ^ ε = P at *
  rw [show (1 : ℂ) + (-3) * ε + 1 = 2 - 3 * ε by ring] at *
  rw [show (1 : ℂ) + (-2) * ε = 1 - 2 * ε by ring, show (1 : ℂ) + (-3) * ε = 1 - 3 * ε by ring] at *
  simp only [setDGammaD16]
  field_simp
  ring

theorem exp_ratio16 (a b c d e f : ℂ) :
    exp a ^ 2 * exp b * exp c / (exp d * exp e * exp f) = exp (2 * a + b + c - d - e - f) := by
  rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, Complex.exp_add, Complex.exp_add,
    two_mul, Complex.exp_add]
  ring

/-- The analytic remainder of the exponent for `I₁₆`. -/
noncomputable def setDGammaV16 (ε : ℂ) : ℂ :=
  2 * (-1) ^ 6 * QED.DimReg.logGammaRem ((-1) * ε) + 2 ^ 6 * QED.DimReg.logGammaRem (2 * ε) +
    (-4) ^ 6 * QED.DimReg.logGammaRem ((-4) * ε) - 1 ^ 6 * QED.DimReg.logGammaRem (1 * ε) -
    (-2) ^ 6 * QED.DimReg.logGammaRem ((-2) * ε) - (-3) ^ 6 * QED.DimReg.logGammaRem ((-3) * ε)

/-- The polynomial part `2π²/3 + 8ζ₃ ε + 22π⁴/45 ε²` of the exponent for `I₁₆` over `ε²`. -/
noncomputable def setDGammaXp16 (ε : ℂ) : ℂ :=
  2 / 3 * (π : ℂ) ^ 2 + 8 * (zeta3 : ℂ) * ε + 22 / 45 * (π : ℂ) ^ 4 * ε ^ 2

/-- The rest of the exponent for `I₁₆`, over `ε⁵`. -/
noncomputable def setDGammaY16 (ε : ℂ) : ℂ := 144 * (zeta5 : ℂ) + ε * setDGammaV16 ε

/-- The exponent for `I₁₆`, divided by `ε ^ 2`. -/
noncomputable def setDGammaX16 (ε : ℂ) : ℂ := setDGammaXp16 ε + ε ^ 3 * setDGammaY16 ε

/-- The polynomial part of the remainder for `I₁₆`. -/
noncomputable def setDGammaP16 (ε : ℂ) : ℂ :=
  (32 / 3 * (zeta3 : ℂ) * (π : ℂ) ^ 2 + 100 * (zeta3 : ℂ) + 224 / 45 * (π : ℂ) ^ 4
      - 5 / 6 * (π : ℂ) ^ 2 - 10493 / 16) +
    (64 * (zeta3 : ℂ) ^ 2 - 64 * (zeta3 : ℂ) * (π : ℂ) ^ 2 - 960 * (zeta3 : ℂ)
      + 88 / 135 * (π : ℂ) ^ 6 - 192 / 5 * (π : ℂ) ^ 4 - 72 * (π : ℂ) ^ 2 + 7137 / 2) * ε +
    (-384 * (zeta3 : ℂ) ^ 2 + 352 / 45 * (zeta3 : ℂ) * (π : ℂ) ^ 4
      + 256 / 3 * (zeta3 : ℂ) * (π : ℂ) ^ 2 + 2636 * (zeta3 : ℂ) - 176 / 45 * (π : ℂ) ^ 6
      + 800 / 9 * (π : ℂ) ^ 4 + 1757 / 6 * (π : ℂ) ^ 2 - 115195 / 16) * ε ^ 2 +
    (512 * (zeta3 : ℂ) ^ 2 - 704 / 15 * (zeta3 : ℂ) * (π : ℂ) ^ 4 - 2736 * (zeta3 : ℂ)
      + 484 / 2025 * (π : ℂ) ^ 8 + 704 / 135 * (π : ℂ) ^ 6 - 384 / 5 * (π : ℂ) ^ 4
      - 366 * (π : ℂ) ^ 2 + 25803 / 4) * ε ^ 3 +
    (2816 / 45 * (zeta3 : ℂ) * (π : ℂ) ^ 4 + 1008 * (zeta3 : ℂ) - 968 / 675 * (π : ℂ) ^ 8
      + 128 / 5 * (π : ℂ) ^ 4 + 150 * (π : ℂ) ^ 2 - 8631 / 4) * ε ^ 4 +
    3872 / 2025 * (π : ℂ) ^ 8 * ε ^ 5

/-- The remainder `R₁₆` with `I₁₆ C⁻¹ = L₁₆ + ε² R₁₆`. -/
noncomputable def setDGammaR16 (ε : ℂ) : ℂ :=
  (setDGammaP16 ε + (2 - 4 * ε) * (1 - 4 * ε) * (setDGammaY16 ε +
    ε ^ 2 * setDGammaY16 ε * (setDGammaX16 ε + setDGammaXp16 ε) / 2 +
    ε * setDGammaX16 ε ^ 3 * QED.DimReg.expRem3 (ε ^ 2 * setDGammaX16 ε))) / setDGammaD16 ε

theorem gammaRatio16_eq {ε : ℂ} (hε : ‖ε‖ < 1 / 8) :
    Gamma (1 + (-1) * ε) ^ 2 * Gamma (1 + 2 * ε) * Gamma (1 + (-4) * ε) /
        (Gamma (1 + 1 * ε) * Gamma (1 + (-2) * ε) * Gamma (1 + (-3) * ε)) =
      exp (ε ^ 2 * setDGammaX16 ε) := by
  rw [QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-1) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 2 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-4) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε 1 (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-2) (by norm_num)),
    QED.DimReg.Gamma_one_add_eq_exp (setDGamma_norm_mul_lt_one hε (-3) (by norm_num)), exp_ratio16]
  congr 1
  simp only [setDGammaX16, setDGammaXp16, setDGammaY16, setDGammaV16]
  ring

theorem analyticAt_setDGammaV16 : AnalyticAt ℂ setDGammaV16 0 := by
  have h1 := analyticAt_logGammaRem_mul (-1)
  have h2 := analyticAt_logGammaRem_mul 2
  have h3 := analyticAt_logGammaRem_mul (-4)
  have h4 := analyticAt_logGammaRem_mul 1
  have h5 := analyticAt_logGammaRem_mul (-2)
  have h6 := analyticAt_logGammaRem_mul (-3)
  unfold setDGammaV16
  fun_prop

theorem analyticAt_setDGammaR16 : AnalyticAt ℂ setDGammaR16 0 := by
  have hV := analyticAt_setDGammaV16
  have hY : AnalyticAt ℂ setDGammaY16 0 := by unfold setDGammaY16; fun_prop
  have hXp : AnalyticAt ℂ setDGammaXp16 0 := by unfold setDGammaXp16; fun_prop
  have hX : AnalyticAt ℂ setDGammaX16 0 := by unfold setDGammaX16; fun_prop
  have hE : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * setDGammaX16 ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hP : AnalyticAt ℂ setDGammaP16 0 := by unfold setDGammaP16; fun_prop
  have hD : AnalyticAt ℂ setDGammaD16 0 := by unfold setDGammaD16; fun_prop
  unfold setDGammaR16
  refine AnalyticAt.div (by fun_prop) (by fun_prop) ?_
  norm_num [setDGammaD16]

/-- **The input for `I₁₆`, proved**: `I₁₆ C⁻¹ = L₁₆(ε) + ε² R₁₆(ε)` with `R₁₆` analytic at `0`. -/
theorem hasTruncLaurent_setDMasterI16 : HasTruncLaurent setDMasterI16 setDLaurentI16 2 := by
  refine ⟨setDGammaR16, analyticAt_setDGammaR16, ?_⟩
  filter_upwards [setDGamma_eventually_small, self_mem_nhdsWithin] with ε hε h0
  have h0 : ε ≠ 0 := h0
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have hD : setDGammaD16 ε ≠ 0 := by
    have h1 := hl (-1) 1 (by norm_num) (by norm_num) (x := ε - 1) (by ring)
    have h2 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
    have h3 := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
    have h4 := hl 2 (-3) (by norm_num) (by norm_num) (x := 2 - 3 * ε) (by ring)
    have h5 := hl 1 (-3) (by norm_num) (by norm_num) (x := 1 - 3 * ε) (by ring)
    simp [setDGammaD16, h1, h2, h3, h4, h5]
  rw [setDMasterI16_eq h0 hε, gammaRatio16_eq hε, QED.DimReg.exp_eq_expRem3, setDGammaR16]
  generalize QED.DimReg.expRem3 (ε ^ 2 * setDGammaX16 ε) = E
  have hDd : setDGammaD16 ε =
      (ε - 1) * (1 - 2 * ε) * (2 * (2 * ε - 1)) * (2 - 3 * ε) * (1 - 3 * ε) := rfl
  generalize setDGammaD16 ε = D at *
  simp only [setDLaurentI16, setDGammaX16, setDGammaXp16, setDGammaY16, setDGammaP16]
  generalize setDGammaV16 ε = V
  field_simp
  rw [hDd]
  ring

/-! ### The set (d) inputs from eight master expansions -/

/-- The set (d) inputs with the three `Γ`-function masters `I₁₄, I₁₆, I₁₈` discharged: if they are
the proved masters and the other eight inputs hold, then all eleven hold. -/
theorem SetDMasters.Expansions.of_I14_I16_I18 {M : SetDMasters} (h14 : M.I14 = setDMasterI14)
    (h16 : M.I16 = setDMasterI16) (h18 : M.I18 = setDMasterI18)
    (h2 : HasTruncLaurent M.I2 setDLaurentI2 2) (h3 : HasTruncLaurent M.I3 setDLaurentI3 1)
    (h5 : HasTruncLaurent M.I5 setDLaurentI5 2) (h8 : HasTruncLaurent M.I8 setDLaurentI8 3)
    (h9 : HasTruncLaurent M.I9 setDLaurentI9 2) (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h15 : HasTruncLaurent M.I15 setDLaurentI15 3) : M.Expansions :=
  SetDMasters.Expansions.of_I18 h18 h2 h3 h5 h8 h9 h12 h13 (h14 ▸ hasTruncLaurent_setDMasterI14)
    h15 (h16 ▸ hasTruncLaurent_setDMasterI16)

/-- **Set (d) from eight master inputs**: with `I₁₄, I₁₆, I₁₈` the proved `Γ`-function masters and
the eight remaining expansions as inputs, the set (d) combination tends to the
Jegerlehner–Nyffeler value as `ε → 0`. -/
theorem SetDMasters.tendsto_of_I14_I16_I18 {M : SetDMasters} (h14 : M.I14 = setDMasterI14)
    (h16 : M.I16 = setDMasterI16) (h18 : M.I18 = setDMasterI18)
    (h2 : HasTruncLaurent M.I2 setDLaurentI2 2) (h3 : HasTruncLaurent M.I3 setDLaurentI3 1)
    (h5 : HasTruncLaurent M.I5 setDLaurentI5 2) (h8 : HasTruncLaurent M.I8 setDLaurentI8 3)
    (h9 : HasTruncLaurent M.I9 setDLaurentI9 2) (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h15 : HasTruncLaurent M.I15 setDLaurentI15 3) :
    Tendsto (setDCombination M) (𝓝[≠] (0 : ℂ)) (𝓝 (a1SixSetDJN : ℂ)) :=
  (SetDMasters.Expansions.of_I14_I16_I18 h14 h16 h18 h2 h3 h5 h8 h9 h12 h13 h15).tendsto

end QED.ThreeLoopD
