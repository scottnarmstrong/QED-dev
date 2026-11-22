/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (e) of `A₁⁽⁶⁾`: the master coefficients, part A

The no-closed-loop set (e) of the three-loop electron anomaly (50 vertex diagrams), after the
trace, the `g - 2` projection with the Ward-identity charge renormalization, the on-shell mass
counterterms and the IBP reduction (offline survey PE1: FORM and Kira 3.1, generated file
`sete_coeffs.json`), is a combination `∑ⱼ cⱼ(d) Mⱼ(d)` of the seventeen Laporta–Remiddi (1996)
masters `I₁, …, I₁₀, I₁₂, …, I₁₈`. The survey has already eliminated `I₁₁`, by
`I₁₁ = (4/3) I₁₂ - (2d - 5)/(3(d - 2)) I₁₄ + I₁₈/6`, and replaced Kira's scalar triple cross
`J₀` by `I₁`, through `J₀ = 2(d - 4)/(3d - 13) I₁ + (lower masters)`.

This file treats the masters `I₁`, `I₂`, `I₃`, `I₄`, `I₅`, `I₆`, `I₇`, `I₈`
(the others are in `QED.ThreeLoopE.SetEMastersCoeffsB`).
For the master `I_j`, with `pⱼ` the pole order of its coefficient at `ε = 0` (`d = 4 - 2ε`) and
`mⱼ` the leading pole order of the master itself:
* `setENumIj d`, `setEDenIj d`: numerator and denominator in `d`, transcribed (by a script)
  from `sete_coeffs.json`; `setECoeffIj ε = setENumIj (4 - 2ε) / setEDenIj (4 - 2ε)`;
* `setEUIj ε`: the factors of the denominator not vanishing at `ε = 0`, each normalized to
  `1 + bε`, so `setEUIj 0 = 1`;
* `setETIj`: the Taylor polynomial of `ε ^ pⱼ · cⱼ` to degree `pⱼ + mⱼ`; `setERIj` the
  polynomial with `setENumIj (4 - 2ε) = k (setEUIj · setETIj + ε ^ (mⱼ + pⱼ + 1) setERIj)`;
* `setECoeffIj_eq`: `cⱼ(ε) = ε⁻¹ ^ pⱼ setETIj ε + ε ^ (mⱼ + 1) setEQIj ε` for `ε ≠ 0`,
  `setEUIj ε ≠ 0`, with `setEQIj = setERIj / setEUIj` analytic at `0`.

Each identity is univariate with rational coefficients, checked by `ring`.
-/

@[expose] public section

namespace QED.ThreeLoopE

/-- Numerator of the set (e) coefficient of `I₁`, in `d`. -/
noncomputable def setENumI1 (d : ℂ) : ℂ :=
  -(81 * d ^ (8 : ℕ) - 3285 * d ^ (7 : ℕ) + 55599 * d ^ (6 : ℕ) - 518271 * d ^ (5 : ℕ)
    + 2932288 * d ^ (4 : ℕ) - 10370444 * d ^ (3 : ℕ) + 22488032 * d ^ (2 : ℕ) - 27431616 * d
    + 14449536)

/-- Denominator of the set (e) coefficient of `I₁`, in `d`. -/
noncomputable def setEDenI1 (d : ℂ) : ℂ :=
  64 * (d - 2) * (d - 1) * (2 * d - 7) * (3 * d - 13)

/-- The set (e) coefficient of `I₁` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI1 (ε : ℂ) : ℂ :=
  setENumI1 (4 - 2 * ε) / setEDenI1 (4 - 2 * ε)

/-- The factors of `setEDenI1 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI1 (ε : ℂ) : ℂ :=
  (1 - ε) * (1 - 2 / 3 * ε) * (1 - 4 * ε) * (1 + 6 * ε)

/-- The Taylor polynomial of `ε ^ 0 · setECoeffI1 ε` to degree 0. -/
noncomputable def setETI1 (_ε : ℂ) : ℂ :=
  -1 / 3

/-- The Taylor remainder numerator of the coefficient of `I₁`. -/
noncomputable def setERI1 (ε : ℂ) : ℂ :=
  54 * ε ^ (7 : ℕ) + 231 * ε ^ (6 : ℕ) - 31 / 2 * ε ^ (5 : ℕ) - 883 / 4 * ε ^ (4 : ℕ)
    + 905 / 6 * ε ^ (3 : ℕ) - 95 / 36 * ε ^ (2 : ℕ) - 505 / 18 * ε + 13 / 9

/-- The Taylor remainder of the coefficient of `I₁`, analytic at `0`. -/
noncomputable def setEQI1 (ε : ℂ) : ℂ :=
  setERI1 ε / setEUI1 ε

/-- The coefficient of `I₁` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI1_eq {ε : ℂ} (_hε : ε ≠ 0) (hU : setEUI1 ε ≠ 0) :
    setECoeffI1 ε = setETI1 ε + ε ^ (1 : ℕ) * setEQI1 ε := by
  have hden : setEDenI1 (4 - 2 * ε) = (-384) * (ε ^ (0 : ℕ) * setEUI1 ε) := by
    simp only [setEDenI1, setEUI1]; ring
  have hnum : setENumI1 (4 - 2 * ε) =
      (-384) * (setEUI1 ε * setETI1 ε + ε ^ (1 : ℕ) * setERI1 ε) := by
    simp only [setENumI1, setEUI1, setETI1, setERI1]; ring
  rw [setECoeffI1, hden, hnum, setEQI1]
  field_simp

theorem setEUI1_zero : setEUI1 0 = 1 := by
  norm_num [setEUI1]

theorem analyticAt_setEUI1 (z : ℂ) : AnalyticAt ℂ setEUI1 z := by
  unfold setEUI1; fun_prop

theorem analyticAt_setEQI1 : AnalyticAt ℂ setEQI1 0 := by
  have hR : AnalyticAt ℂ setERI1 0 := by unfold setERI1; fun_prop
  exact hR.div (analyticAt_setEUI1 0) (by rw [setEUI1_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₂`, in `d`. -/
noncomputable def setENumI2 (d : ℂ) : ℂ :=
  (135 * d ^ (12 : ℕ) - 7050 * d ^ (11 : ℕ) + 172099 * d ^ (10 : ℕ) - 2571877 * d ^ (9 : ℕ)
    + 26005390 * d ^ (8 : ℕ) - 186431173 * d ^ (7 : ℕ) + 968334224 * d ^ (6 : ℕ)
    - 3664487436 * d ^ (5 : ℕ) + 10017903800 * d ^ (4 : ℕ) - 19287111680 * d ^ (3 : ℕ)
    + 24822575712 * d ^ (2 : ℕ) - 19178176384 * d + 6728688640)

/-- Denominator of the set (e) coefficient of `I₂`, in `d`. -/
noncomputable def setEDenI2 (d : ℂ) : ℂ :=
  128 * (d - 5) * (d - 4) * (d - 3) * (d - 2) * (d - 1) * (2 * d - 7) * (3 * d - 13) * (3 * d - 8)

/-- The set (e) coefficient of `I₂` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI2 (ε : ℂ) : ℂ :=
  setENumI2 (4 - 2 * ε) / setEDenI2 (4 - 2 * ε)

/-- The factors of `setEDenI2 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI2 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - 2 * ε) * (1 - ε) * (1 - 2 / 3 * ε) * (1 - 4 * ε) * (1 + 6 * ε) *
    (1 - 3 / 2 * ε)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI2 ε` to degree 2. -/
noncomputable def setETI2 (ε : ℂ) : ℂ :=
  -3083 / 216 * ε ^ (2 : ℕ) + 119 / 72 * ε - 5 / 6

/-- The Taylor remainder numerator of the coefficient of `I₂`. -/
noncomputable def setERI2 (ε : ℂ) : ℂ :=
  -90 * ε ^ (9 : ℕ) - 190 * ε ^ (8 : ℕ) - 4459 / 6 * ε ^ (7 : ℕ) - 22679 / 36 * ε ^ (6 : ℕ)
    + 183581 / 36 * ε ^ (5 : ℕ) - 7357063 / 1296 * ε ^ (4 : ℕ) + 962305 / 648 * ε ^ (3 : ℕ)
    + 141919 / 144 * ε ^ (2 : ℕ) - 97327 / 162 * ε + 51101 / 648

/-- The Taylor remainder of the coefficient of `I₂`, analytic at `0`. -/
noncomputable def setEQI2 (ε : ℂ) : ℂ :=
  setERI2 ε / setEUI2 ε

/-- The coefficient of `I₂` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI2_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI2 ε ≠ 0) :
    setECoeffI2 ε = ε⁻¹ ^ (1 : ℕ) * setETI2 ε + ε ^ (2 : ℕ) * setEQI2 ε := by
  have hden : setEDenI2 (4 - 2 * ε) = (-6144) * (ε ^ (1 : ℕ) * setEUI2 ε) := by
    simp only [setEDenI2, setEUI2]; ring
  have hnum : setENumI2 (4 - 2 * ε) =
      (-6144) * (setEUI2 ε * setETI2 ε + ε ^ (3 : ℕ) * setERI2 ε) := by
    simp only [setENumI2, setEUI2, setETI2, setERI2]; ring
  rw [setECoeffI2, hden, hnum, setEQI2]
  field_simp

theorem setEUI2_zero : setEUI2 0 = 1 := by
  norm_num [setEUI2]

theorem analyticAt_setEUI2 (z : ℂ) : AnalyticAt ℂ setEUI2 z := by
  unfold setEUI2; fun_prop

theorem analyticAt_setEQI2 : AnalyticAt ℂ setEQI2 0 := by
  have hR : AnalyticAt ℂ setERI2 0 := by unfold setERI2; fun_prop
  exact hR.div (analyticAt_setEUI2 0) (by rw [setEUI2_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₃`, in `d`. -/
noncomputable def setENumI3 (d : ℂ) : ℂ :=
  -(153 * d ^ (11 : ℕ) - 7125 * d ^ (10 : ℕ) + 151746 * d ^ (9 : ℕ) - 1949428 * d ^ (8 : ℕ)
    + 16760555 * d ^ (7 : ℕ) - 101095123 * d ^ (6 : ℕ) + 435804706 * d ^ (5 : ℕ)
    - 1340645220 * d ^ (4 : ℕ) + 2880292696 * d ^ (3 : ℕ) - 4111167616 * d ^ (2 : ℕ)
    + 3505246016 * d - 1351403520)

/-- Denominator of the set (e) coefficient of `I₃`, in `d`. -/
noncomputable def setEDenI3 (d : ℂ) : ℂ :=
  512 * (d - 5) * (d - 4) * (d - 3) * (d - 2) * (d - 1) * (2 * d - 7) * (3 * d - 13)

/-- The set (e) coefficient of `I₃` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI3 (ε : ℂ) : ℂ :=
  setENumI3 (4 - 2 * ε) / setEDenI3 (4 - 2 * ε)

/-- The factors of `setEDenI3 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI3 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - 2 * ε) * (1 - ε) * (1 - 2 / 3 * ε) * (1 - 4 * ε) * (1 + 6 * ε)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI3 ε` to degree 4. -/
noncomputable def setETI3 (ε : ℂ) : ℂ :=
  -184135 / 1296 * ε ^ (4 : ℕ) + 19229 / 864 * ε ^ (3 : ℕ) - 97 / 36 * ε ^ (2 : ℕ) + 31 / 48 * ε
    - 3 / 8

/-- The Taylor remainder numerator of the coefficient of `I₃`. -/
noncomputable def setERI3 (ε : ℂ) : ℂ :=
  -51 * ε ^ (6 : ℕ) + 1462469 / 162 * ε ^ (5 : ℕ) - 12164747 / 486 * ε ^ (4 : ℕ)
    + 4057316 / 243 * ε ^ (3 : ℕ) + 4389479 / 1296 * ε ^ (2 : ℕ) - 39050431 / 7776 * ε
    + 6583997 / 7776

/-- The Taylor remainder of the coefficient of `I₃`, analytic at `0`. -/
noncomputable def setEQI3 (ε : ℂ) : ℂ :=
  setERI3 ε / setEUI3 ε

/-- The coefficient of `I₃` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI3_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI3 ε ≠ 0) :
    setECoeffI3 ε = ε⁻¹ ^ (1 : ℕ) * setETI3 ε + ε ^ (4 : ℕ) * setEQI3 ε := by
  have hden : setEDenI3 (4 - 2 * ε) = (-6144) * (ε ^ (1 : ℕ) * setEUI3 ε) := by
    simp only [setEDenI3, setEUI3]; ring
  have hnum : setENumI3 (4 - 2 * ε) =
      (-6144) * (setEUI3 ε * setETI3 ε + ε ^ (5 : ℕ) * setERI3 ε) := by
    simp only [setENumI3, setEUI3, setETI3, setERI3]; ring
  rw [setECoeffI3, hden, hnum, setEQI3]
  field_simp

theorem setEUI3_zero : setEUI3 0 = 1 := by
  norm_num [setEUI3]

theorem analyticAt_setEUI3 (z : ℂ) : AnalyticAt ℂ setEUI3 z := by
  unfold setEUI3; fun_prop

theorem analyticAt_setEQI3 : AnalyticAt ℂ setEQI3 0 := by
  have hR : AnalyticAt ℂ setERI3 0 := by unfold setERI3; fun_prop
  exact hR.div (analyticAt_setEUI3 0) (by rw [setEUI3_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₄`, in `d`. -/
noncomputable def setENumI4 (d : ℂ) : ℂ :=
  -(999 * d ^ (13 : ℕ) - 50529 * d ^ (12 : ℕ) + 1173397 * d ^ (11 : ℕ) - 16546404 * d ^ (10 : ℕ)
    + 157907907 * d ^ (9 : ℕ) - 1075859347 * d ^ (8 : ℕ) + 5378019565 * d ^ (7 : ℕ)
    - 19947446104 * d ^ (6 : ℕ) + 54822989236 * d ^ (5 : ℕ) - 110089801872 * d ^ (4 : ℕ)
    + 156681839456 * d ^ (3 : ℕ) - 149261314560 * d ^ (2 : ℕ) + 84992382976 * d - 21730846720)

/-- Denominator of the set (e) coefficient of `I₄`, in `d`. -/
noncomputable def setEDenI4 (d : ℂ) : ℂ :=
  256 * (d - 5) * (d - 4) * (d - 2) * (3 * d - 13) * (3 * d - 8) * (d - 1) ^ (2 : ℕ) *
    (2 * d - 7) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₄` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI4 (ε : ℂ) : ℂ :=
  setENumI4 (4 - 2 * ε) / setEDenI4 (4 - 2 * ε)

/-- The factors of `setEDenI4 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI4 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - ε) * (1 + 6 * ε) * (1 - 3 / 2 * ε) * (1 - 2 / 3 * ε) ^ (2 : ℕ) *
    (1 - 4 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI4 ε` to degree 2. -/
noncomputable def setETI4 (ε : ℂ) : ℂ :=
  467 / 54 * ε ^ (2 : ℕ) - 25 / 36 * ε + 1 / 3

/-- The Taylor remainder numerator of the coefficient of `I₄`. -/
noncomputable def setERI4 (ε : ℂ) : ℂ :=
  -222 * ε ^ (10 : ℕ) + 473 / 3 * ε ^ (9 : ℕ) + 5243 / 18 * ε ^ (8 : ℕ) - 22286 / 27 * ε ^ (7 : ℕ)
    + 105103 / 24 * ε ^ (6 : ℕ) - 31045597 / 3888 * ε ^ (5 : ℕ) + 38124449 / 7776 * ε ^ (4 : ℕ)
    + 334589 / 1296 * ε ^ (3 : ℕ) - 9482587 / 7776 * ε ^ (2 : ℕ) + 162487 / 486 * ε - 28693 / 1296

/-- The Taylor remainder of the coefficient of `I₄`, analytic at `0`. -/
noncomputable def setEQI4 (ε : ℂ) : ℂ :=
  setERI4 ε / setEUI4 ε

/-- The coefficient of `I₄` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI4_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI4 ε ≠ 0) :
    setECoeffI4 ε = ε⁻¹ ^ (1 : ℕ) * setETI4 ε + ε ^ (2 : ℕ) * setEQI4 ε := by
  have hden : setEDenI4 (4 - 2 * ε) = (-36864) * (ε ^ (1 : ℕ) * setEUI4 ε) := by
    simp only [setEDenI4, setEUI4]; ring
  have hnum : setENumI4 (4 - 2 * ε) =
      (-36864) * (setEUI4 ε * setETI4 ε + ε ^ (3 : ℕ) * setERI4 ε) := by
    simp only [setENumI4, setEUI4, setETI4, setERI4]; ring
  rw [setECoeffI4, hden, hnum, setEQI4]
  field_simp

theorem setEUI4_zero : setEUI4 0 = 1 := by
  norm_num [setEUI4]

theorem analyticAt_setEUI4 (z : ℂ) : AnalyticAt ℂ setEUI4 z := by
  unfold setEUI4; fun_prop

theorem analyticAt_setEQI4 : AnalyticAt ℂ setEQI4 0 := by
  have hR : AnalyticAt ℂ setERI4 0 := by unfold setERI4; fun_prop
  exact hR.div (analyticAt_setEUI4 0) (by rw [setEUI4_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₅`, in `d`. -/
noncomputable def setENumI5 (d : ℂ) : ℂ :=
  -(99 * d ^ (10 : ℕ) - 4299 * d ^ (9 : ℕ) + 82419 * d ^ (8 : ℕ) - 922831 * d ^ (7 : ℕ)
    + 6711426 * d ^ (6 : ℕ) - 33257110 * d ^ (5 : ℕ) + 114106792 * d ^ (4 : ℕ)
    - 268390448 * d ^ (3 : ℕ) + 414887488 * d ^ (2 : ℕ) - 380877088 * d + 157637120)

/-- Denominator of the set (e) coefficient of `I₅`, in `d`. -/
noncomputable def setEDenI5 (d : ℂ) : ℂ :=
  128 * (d - 5) * (d - 4) * (d - 3) * (d - 2) * (d - 1) * (3 * d - 13)

/-- The set (e) coefficient of `I₅` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI5 (ε : ℂ) : ℂ :=
  setENumI5 (4 - 2 * ε) / setEDenI5 (4 - 2 * ε)

/-- The factors of `setEDenI5 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI5 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - 2 * ε) * (1 - ε) * (1 - 2 / 3 * ε) * (1 + 6 * ε)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI5 ε` to degree 4. -/
noncomputable def setETI5 (ε : ℂ) : ℂ :=
  -191503 / 1944 * ε ^ (4 : ℕ) + 16879 / 648 * ε ^ (3 : ℕ) + 1055 / 216 * ε ^ (2 : ℕ) - 107 / 72 * ε
    - 5 / 12

/-- The Taylor remainder numerator of the coefficient of `I₅`. -/
noncomputable def setERI5 (ε : ℂ) : ℂ :=
  66 * ε ^ (5 : ℕ) - 355547 / 243 * ε ^ (4 : ℕ) + 5710933 / 1458 * ε ^ (3 : ℕ)
    - 6115391 / 2916 * ε ^ (2 : ℕ) - 2606027 / 2916 * ε + 875641 / 1458

/-- The Taylor remainder of the coefficient of `I₅`, analytic at `0`. -/
noncomputable def setEQI5 (ε : ℂ) : ℂ :=
  setERI5 ε / setEUI5 ε

/-- The coefficient of `I₅` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI5_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI5 ε ≠ 0) :
    setECoeffI5 ε = ε⁻¹ ^ (1 : ℕ) * setETI5 ε + ε ^ (4 : ℕ) * setEQI5 ε := by
  have hden : setEDenI5 (4 - 2 * ε) = (-1536) * (ε ^ (1 : ℕ) * setEUI5 ε) := by
    simp only [setEDenI5, setEUI5]; ring
  have hnum : setENumI5 (4 - 2 * ε) =
      (-1536) * (setEUI5 ε * setETI5 ε + ε ^ (5 : ℕ) * setERI5 ε) := by
    simp only [setENumI5, setEUI5, setETI5, setERI5]; ring
  rw [setECoeffI5, hden, hnum, setEQI5]
  field_simp

theorem setEUI5_zero : setEUI5 0 = 1 := by
  norm_num [setEUI5]

theorem analyticAt_setEUI5 (z : ℂ) : AnalyticAt ℂ setEUI5 z := by
  unfold setEUI5; fun_prop

theorem analyticAt_setEQI5 : AnalyticAt ℂ setEQI5 0 := by
  have hR : AnalyticAt ℂ setERI5 0 := by unfold setERI5; fun_prop
  exact hR.div (analyticAt_setEUI5 0) (by rw [setEUI5_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₆`, in `d`. -/
noncomputable def setENumI6 (d : ℂ) : ℂ :=
  (153 * d ^ (11 : ℕ) - 6396 * d ^ (10 : ℕ) + 121935 * d ^ (9 : ℕ) - 1394841 * d ^ (8 : ℕ)
    + 10624456 * d ^ (7 : ℕ) - 56607071 * d ^ (6 : ℕ) + 215671248 * d ^ (5 : ℕ)
    - 589194092 * d ^ (4 : ℕ) + 1134519296 * d ^ (3 : ℕ) - 1470376032 * d ^ (2 : ℕ) + 1156404224 * d
    - 418295040)

/-- Denominator of the set (e) coefficient of `I₆`, in `d`. -/
noncomputable def setEDenI6 (d : ℂ) : ℂ :=
  256 * (d - 5) * (d - 4) * (d - 2) * (d - 1) * (3 * d - 13) * (2 * d - 7) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₆` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI6 (ε : ℂ) : ℂ :=
  setENumI6 (4 - 2 * ε) / setEDenI6 (4 - 2 * ε)

/-- The factors of `setEDenI6 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI6 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - ε) * (1 - 2 / 3 * ε) * (1 + 6 * ε) * (1 - 4 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI6 ε` to degree 4. -/
noncomputable def setETI6 (ε : ℂ) : ℂ :=
  -567787 / 3888 * ε ^ (4 : ℕ) + 7721 / 648 * ε ^ (3 : ℕ) - 1499 / 216 * ε ^ (2 : ℕ) + 73 / 36 * ε
    - 1 / 12

/-- The Taylor remainder numerator of the coefficient of `I₆`. -/
noncomputable def setERI6 (ε : ℂ) : ℂ :=
  102 * ε ^ (6 : ℕ) + 4515080 / 243 * ε ^ (5 : ℕ) - 65637187 / 1458 * ε ^ (4 : ℕ)
    + 60489881 / 2916 * ε ^ (3 : ℕ) + 3536279 / 324 * ε ^ (2 : ℕ) - 67434409 / 11664 * ε
    + 6373369 / 11664

/-- The Taylor remainder of the coefficient of `I₆`, analytic at `0`. -/
noncomputable def setEQI6 (ε : ℂ) : ℂ :=
  setERI6 ε / setEUI6 ε

/-- The coefficient of `I₆` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI6_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI6 ε ≠ 0) :
    setECoeffI6 ε = ε⁻¹ ^ (1 : ℕ) * setETI6 ε + ε ^ (4 : ℕ) * setEQI6 ε := by
  have hden : setEDenI6 (4 - 2 * ε) = (-3072) * (ε ^ (1 : ℕ) * setEUI6 ε) := by
    simp only [setEDenI6, setEUI6]; ring
  have hnum : setENumI6 (4 - 2 * ε) =
      (-3072) * (setEUI6 ε * setETI6 ε + ε ^ (5 : ℕ) * setERI6 ε) := by
    simp only [setENumI6, setEUI6, setETI6, setERI6]; ring
  rw [setECoeffI6, hden, hnum, setEQI6]
  field_simp

theorem setEUI6_zero : setEUI6 0 = 1 := by
  norm_num [setEUI6]

theorem analyticAt_setEUI6 (z : ℂ) : AnalyticAt ℂ setEUI6 z := by
  unfold setEUI6; fun_prop

theorem analyticAt_setEQI6 : AnalyticAt ℂ setEQI6 0 := by
  have hR : AnalyticAt ℂ setERI6 0 := by unfold setERI6; fun_prop
  exact hR.div (analyticAt_setEUI6 0) (by rw [setEUI6_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₇`, in `d`. -/
noncomputable def setENumI7 (d : ℂ) : ℂ :=
  -(333 * d ^ (11 : ℕ) - 16518 * d ^ (10 : ℕ) + 364473 * d ^ (9 : ℕ) - 4740491 * d ^ (8 : ℕ)
    + 40499142 * d ^ (7 : ℕ) - 239160019 * d ^ (6 : ℕ) + 997892148 * d ^ (5 : ℕ)
    - 2946002428 * d ^ (4 : ℕ) + 6037313408 * d ^ (3 : ℕ) - 8186675232 * d ^ (2 : ℕ)
    + 6615514944 * d - 2414672640)

/-- Denominator of the set (e) coefficient of `I₇`, in `d`. -/
noncomputable def setEDenI7 (d : ℂ) : ℂ :=
  128 * (d - 5) * (d - 4) * (d - 2) * (d - 1) * (3 * d - 13) * (2 * d - 7) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₇` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI7 (ε : ℂ) : ℂ :=
  setENumI7 (4 - 2 * ε) / setEDenI7 (4 - 2 * ε)

/-- The factors of `setEDenI7 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI7 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - ε) * (1 - 2 / 3 * ε) * (1 + 6 * ε) * (1 - 4 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI7 ε` to degree 4. -/
noncomputable def setETI7 (ε : ℂ) : ℂ :=
  943333 / 1944 * ε ^ (4 : ℕ) - 6469 / 162 * ε ^ (3 : ℕ) + 455 / 27 * ε ^ (2 : ℕ) - 35 / 36 * ε
    + 2 / 3

/-- The Taylor remainder numerator of the coefficient of `I₇`. -/
noncomputable def setERI7 (ε : ℂ) : ℂ :=
  -444 * ε ^ (6 : ℕ) - 15395620 / 243 * ε ^ (5 : ℕ) + 110158741 / 729 * ε ^ (4 : ℕ)
    - 100674419 / 1458 * ε ^ (3 : ℕ) - 2918437 / 81 * ε ^ (2 : ℕ) + 111229105 / 5832 * ε
    - 10875937 / 5832

/-- The Taylor remainder of the coefficient of `I₇`, analytic at `0`. -/
noncomputable def setEQI7 (ε : ℂ) : ℂ :=
  setERI7 ε / setEUI7 ε

/-- The coefficient of `I₇` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI7_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI7 ε ≠ 0) :
    setECoeffI7 ε = ε⁻¹ ^ (1 : ℕ) * setETI7 ε + ε ^ (4 : ℕ) * setEQI7 ε := by
  have hden : setEDenI7 (4 - 2 * ε) = (-1536) * (ε ^ (1 : ℕ) * setEUI7 ε) := by
    simp only [setEDenI7, setEUI7]; ring
  have hnum : setENumI7 (4 - 2 * ε) =
      (-1536) * (setEUI7 ε * setETI7 ε + ε ^ (5 : ℕ) * setERI7 ε) := by
    simp only [setENumI7, setEUI7, setETI7, setERI7]; ring
  rw [setECoeffI7, hden, hnum, setEQI7]
  field_simp

theorem setEUI7_zero : setEUI7 0 = 1 := by
  norm_num [setEUI7]

theorem analyticAt_setEUI7 (z : ℂ) : AnalyticAt ℂ setEUI7 z := by
  unfold setEUI7; fun_prop

theorem analyticAt_setEQI7 : AnalyticAt ℂ setEQI7 0 := by
  have hR : AnalyticAt ℂ setERI7 0 := by unfold setERI7; fun_prop
  exact hR.div (analyticAt_setEUI7 0) (by rw [setEUI7_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₈`, in `d`. -/
noncomputable def setENumI8 (d : ℂ) : ℂ :=
  (243 * d ^ (12 : ℕ) - 13599 * d ^ (11 : ℕ) + 336105 * d ^ (10 : ℕ) - 4869577 * d ^ (9 : ℕ)
    + 46192977 * d ^ (8 : ℕ) - 302832765 * d ^ (7 : ℕ) + 1408435631 * d ^ (6 : ℕ)
    - 4683571303 * d ^ (5 : ℕ) + 11045297796 * d ^ (4 : ℕ) - 17984897652 * d ^ (3 : ℕ)
    + 19130346656 * d ^ (2 : ℕ) - 11866876096 * d + 3213142784)

/-- Denominator of the set (e) coefficient of `I₈`, in `d`. -/
noncomputable def setEDenI8 (d : ℂ) : ℂ :=
  384 * (d - 5) * (d - 2) * (3 * d - 13) * (3 * d - 11) * (d - 4) ^ (2 : ℕ) * (d - 1) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₈` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI8 (ε : ℂ) : ℂ :=
  setENumI8 (4 - 2 * ε) / setEDenI8 (4 - 2 * ε)

/-- The factors of `setEDenI8 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI8 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - ε) * (1 + 6 * ε) * (1 - 6 * ε) * (1 - 2 / 3 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 2 · setECoeffI8 ε` to degree 5. -/
noncomputable def setETI8 (ε : ℂ) : ℂ :=
  1012001 / 8748 * ε ^ (5 : ℕ) - 5365321 / 23328 * ε ^ (4 : ℕ) + 15535 / 7776 * ε ^ (3 : ℕ)
    - 8687 / 1296 * ε ^ (2 : ℕ) - 4 / 27 * ε - 17 / 36

/-- The Taylor remainder numerator of the coefficient of `I₈`. -/
noncomputable def setERI8 (ε : ℂ) : ℂ :=
  36 * ε ^ (6 : ℕ) - 7782538 / 2187 * ε ^ (5 : ℕ) + 43974908 / 2187 * ε ^ (4 : ℕ)
    - 753615125 / 19683 * ε ^ (3 : ℕ) + 1815999715 / 78732 * ε ^ (2 : ℕ) + 1117445303 / 157464 * ε
    - 446178031 / 52488

/-- The Taylor remainder of the coefficient of `I₈`, analytic at `0`. -/
noncomputable def setEQI8 (ε : ℂ) : ℂ :=
  setERI8 ε / setEUI8 ε

/-- The coefficient of `I₈` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI8_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI8 ε ≠ 0) :
    setECoeffI8 ε = ε⁻¹ ^ (2 : ℕ) * setETI8 ε + ε ^ (4 : ℕ) * setEQI8 ε := by
  have hden : setEDenI8 (4 - 2 * ε) = 27648 * (ε ^ (2 : ℕ) * setEUI8 ε) := by
    simp only [setEDenI8, setEUI8]; ring
  have hnum : setENumI8 (4 - 2 * ε) =
      27648 * (setEUI8 ε * setETI8 ε + ε ^ (6 : ℕ) * setERI8 ε) := by
    simp only [setENumI8, setEUI8, setETI8, setERI8]; ring
  rw [setECoeffI8, hden, hnum, setEQI8]
  field_simp

theorem setEUI8_zero : setEUI8 0 = 1 := by
  norm_num [setEUI8]

theorem analyticAt_setEUI8 (z : ℂ) : AnalyticAt ℂ setEUI8 z := by
  unfold setEUI8; fun_prop

theorem analyticAt_setEQI8 : AnalyticAt ℂ setEQI8 0 := by
  have hR : AnalyticAt ℂ setERI8 0 := by unfold setERI8; fun_prop
  exact hR.div (analyticAt_setEUI8 0) (by rw [setEUI8_zero]; exact one_ne_zero)

end QED.ThreeLoopE
