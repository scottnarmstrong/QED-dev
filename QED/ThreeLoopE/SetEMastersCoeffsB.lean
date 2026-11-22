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
# Set (e) of `A₁⁽⁶⁾`: the master coefficients, part B

The no-closed-loop set (e) of the three-loop electron anomaly (50 vertex diagrams), after the
trace, the `g - 2` projection with the Ward-identity charge renormalization, the on-shell mass
counterterms and the IBP reduction (offline survey PE1: FORM and Kira 3.1, generated file
`sete_coeffs.json`), is a combination `∑ⱼ cⱼ(d) Mⱼ(d)` of the seventeen Laporta–Remiddi (1996)
masters `I₁, …, I₁₀, I₁₂, …, I₁₈`. The survey has already eliminated `I₁₁`, by
`I₁₁ = (4/3) I₁₂ - (2d - 5)/(3(d - 2)) I₁₄ + I₁₈/6`, and replaced Kira's scalar triple cross
`J₀` by `I₁`, through `J₀ = 2(d - 4)/(3d - 13) I₁ + (lower masters)`.

This file treats the masters `I₉`, `I₁₀`, `I₁₂`, `I₁₃`, `I₁₄`, `I₁₅`, `I₁₆`, `I₁₇`, `I₁₈`
(the others are in `QED.ThreeLoopE.SetEMastersCoeffsA`).
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

/-- Numerator of the set (e) coefficient of `I₉`, in `d`. -/
noncomputable def setENumI9 (d : ℂ) : ℂ :=
  -(189 * d ^ (11 : ℕ) - 8493 * d ^ (10 : ℕ) + 168200 * d ^ (9 : ℕ) - 1952316 * d ^ (8 : ℕ)
    + 14854515 * d ^ (7 : ℕ) - 78283379 * d ^ (6 : ℕ) + 293339512 * d ^ (5 : ℕ)
    - 785820036 * d ^ (4 : ℕ) + 1481231248 * d ^ (3 : ℕ) - 1875908896 * d ^ (2 : ℕ) + 1437446080 * d
    - 504231424)

/-- Denominator of the set (e) coefficient of `I₉`, in `d`. -/
noncomputable def setEDenI9 (d : ℂ) : ℂ :=
  128 * (d - 5) * (d - 4) * (d - 2) * (d - 1) * (2 * d - 7) * (3 * d - 13) * (3 * d - 8)

/-- The set (e) coefficient of `I₉` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI9 (ε : ℂ) : ℂ :=
  setENumI9 (4 - 2 * ε) / setEDenI9 (4 - 2 * ε)

/-- The factors of `setEDenI9 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI9 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - ε) * (1 - 2 / 3 * ε) * (1 - 4 * ε) * (1 + 6 * ε) * (1 - 3 / 2 * ε)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI9 ε` to degree 4. -/
noncomputable def setETI9 (ε : ℂ) : ℂ :=
  11173027 / 7776 * ε ^ (4 : ℕ) - 155929 / 648 * ε ^ (3 : ℕ) + 8557 / 216 * ε ^ (2 : ℕ)
    - 169 / 18 * ε + 7 / 24

/-- The Taylor remainder numerator of the coefficient of `I₉`. -/
noncomputable def setERI9 (ε : ℂ) : ℂ :=
  -63 * ε ^ (6 : ℕ) - 5588903 / 81 * ε ^ (5 : ℕ) + 130668689 / 648 * ε ^ (4 : ℕ)
    - 1819532173 / 11664 * ε ^ (3 : ℕ) - 99742063 / 7776 * ε ^ (2 : ℕ) + 701332523 / 15552 * ε
    - 414353603 / 46656

/-- The Taylor remainder of the coefficient of `I₉`, analytic at `0`. -/
noncomputable def setEQI9 (ε : ℂ) : ℂ :=
  setERI9 ε / setEUI9 ε

/-- The coefficient of `I₉` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI9_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI9 ε ≠ 0) :
    setECoeffI9 ε = ε⁻¹ ^ (1 : ℕ) * setETI9 ε + ε ^ (4 : ℕ) * setEQI9 ε := by
  have hden : setEDenI9 (4 - 2 * ε) = (-6144) * (ε ^ (1 : ℕ) * setEUI9 ε) := by
    simp only [setEDenI9, setEUI9]; ring
  have hnum : setENumI9 (4 - 2 * ε) =
      (-6144) * (setEUI9 ε * setETI9 ε + ε ^ (5 : ℕ) * setERI9 ε) := by
    simp only [setENumI9, setEUI9, setETI9, setERI9]; ring
  rw [setECoeffI9, hden, hnum, setEQI9]
  field_simp

theorem setEUI9_zero : setEUI9 0 = 1 := by
  norm_num [setEUI9]

theorem analyticAt_setEUI9 (z : ℂ) : AnalyticAt ℂ setEUI9 z := by
  unfold setEUI9; fun_prop

theorem analyticAt_setEQI9 : AnalyticAt ℂ setEQI9 0 := by
  have hR : AnalyticAt ℂ setERI9 0 := by unfold setERI9; fun_prop
  exact hR.div (analyticAt_setEUI9 0) (by rw [setEUI9_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₁₀`, in `d`. -/
noncomputable def setENumI10 (d : ℂ) : ℂ :=
  -(2916 * d ^ (14 : ℕ) - 156996 * d ^ (13 : ℕ) + 3793683 * d ^ (12 : ℕ) - 54306626 * d ^ (11 : ℕ)
    + 511917636 * d ^ (10 : ℕ) - 3334414626 * d ^ (9 : ℕ) + 15250349369 * d ^ (8 : ℕ)
    - 48272527248 * d ^ (7 : ℕ) + 98490808748 * d ^ (6 : ℕ) - 94531533480 * d ^ (5 : ℕ)
    - 96583880288 * d ^ (4 : ℕ) + 472360222240 * d ^ (3 : ℕ) - 716098013056 * d ^ (2 : ℕ)
    + 536641558528 * d - 166085324800)

/-- Denominator of the set (e) coefficient of `I₁₀`, in `d`. -/
noncomputable def setEDenI10 (d : ℂ) : ℂ :=
  1536 * (d - 5) * (d - 4) * (d - 2) * (3 * d - 13) * (3 * d - 10) * (3 * d - 8) *
    (d - 1) ^ (2 : ℕ) * (2 * d - 7) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₁₀` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI10 (ε : ℂ) : ℂ :=
  setENumI10 (4 - 2 * ε) / setEDenI10 (4 - 2 * ε)

/-- The factors of `setEDenI10 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI10 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - ε) * (1 + 6 * ε) * (1 - 3 * ε) * (1 - 3 / 2 * ε) * (1 - 2 / 3 * ε) ^ (2 : ℕ) *
    (1 - 4 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI10 ε` to degree 4. -/
noncomputable def setETI10 (ε : ℂ) : ℂ :=
  96377 / 5184 * ε ^ (4 : ℕ) + 109055 / 2592 * ε ^ (3 : ℕ) + 3149 / 864 * ε ^ (2 : ℕ) + 35 / 48 * ε
    + 1 / 3

/-- The Taylor remainder numerator of the coefficient of `I₁₀`. -/
noncomputable def setERI10 (ε : ℂ) : ℂ :=
  108 * ε ^ (9 : ℕ) + 189604 / 27 * ε ^ (8 : ℕ) - 6318331 / 324 * ε ^ (7 : ℕ)
    - 29905589 / 1944 * ε ^ (6 : ℕ) + 542924651 / 5832 * ε ^ (5 : ℕ)
    - 1082661239 / 11664 * ε ^ (4 : ℕ) + 805326637 / 46656 * ε ^ (3 : ℕ)
    + 1705626985 / 93312 * ε ^ (2 : ℕ) - 429770719 / 46656 * ε + 111365395 / 93312

/-- The Taylor remainder of the coefficient of `I₁₀`, analytic at `0`. -/
noncomputable def setEQI10 (ε : ℂ) : ℂ :=
  setERI10 ε / setEUI10 ε

/-- The coefficient of `I₁₀` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI10_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI10 ε ≠ 0) :
    setECoeffI10 ε = ε⁻¹ ^ (1 : ℕ) * setETI10 ε + ε ^ (4 : ℕ) * setEQI10 ε := by
  have hden : setEDenI10 (4 - 2 * ε) = (-442368) * (ε ^ (1 : ℕ) * setEUI10 ε) := by
    simp only [setEDenI10, setEUI10]; ring
  have hnum : setENumI10 (4 - 2 * ε) =
      (-442368) * (setEUI10 ε * setETI10 ε + ε ^ (5 : ℕ) * setERI10 ε) := by
    simp only [setENumI10, setEUI10, setETI10, setERI10]; ring
  rw [setECoeffI10, hden, hnum, setEQI10]
  field_simp

theorem setEUI10_zero : setEUI10 0 = 1 := by
  norm_num [setEUI10]

theorem analyticAt_setEUI10 (z : ℂ) : AnalyticAt ℂ setEUI10 z := by
  unfold setEUI10; fun_prop

theorem analyticAt_setEQI10 : AnalyticAt ℂ setEQI10 0 := by
  have hR : AnalyticAt ℂ setERI10 0 := by unfold setERI10; fun_prop
  exact hR.div (analyticAt_setEUI10 0) (by rw [setEUI10_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₁₂`, in `d`. -/
noncomputable def setENumI12 (d : ℂ) : ℂ :=
  (2 * d - 5) * (5184 * d ^ (13 : ℕ) + 71541 * d ^ (12 : ℕ) - 5737917 * d ^ (11 : ℕ)
    + 101376302 * d ^ (10 : ℕ) - 923246450 * d ^ (9 : ℕ) + 4957652381 * d ^ (8 : ℕ)
    - 15212493469 * d ^ (7 : ℕ) + 16186933984 * d ^ (6 : ℕ) + 67421487564 * d ^ (5 : ℕ)
    - 346568496288 * d ^ (4 : ℕ) + 758684353728 * d ^ (3 : ℕ) - 931212937088 * d ^ (2 : ℕ)
    + 618202073088 * d - 170988994560)

/-- Denominator of the set (e) coefficient of `I₁₂`, in `d`. -/
noncomputable def setEDenI12 (d : ℂ) : ℂ :=
  24576 * (d - 4) * (d - 2) * (3 * d - 13) * (3 * d - 8) * (d - 3) ^ (2 : ℕ) * (d - 1) ^ (2 : ℕ) *
    (2 * d - 7) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₁₂` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI12 (ε : ℂ) : ℂ :=
  setENumI12 (4 - 2 * ε) / setEDenI12 (4 - 2 * ε)

/-- The factors of `setEDenI12 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI12 (ε : ℂ) : ℂ :=
  (1 - ε) * (1 + 6 * ε) * (1 - 3 / 2 * ε) * (1 - 2 * ε) ^ (2 : ℕ) * (1 - 2 / 3 * ε) ^ (2 : ℕ) *
    (1 - 4 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI12 ε` to degree 4. -/
noncomputable def setETI12 (ε : ℂ) : ℂ :=
  -327713275 / 124416 * ε ^ (4 : ℕ) + 4544627 / 10368 * ε ^ (3 : ℕ) - 13847 / 192 * ε ^ (2 : ℕ)
    + 10087 / 1152 * ε - 163 / 64

/-- The Taylor remainder numerator of the coefficient of `I₁₂`. -/
noncomputable def setERI12 (ε : ℂ) : ℂ :=
  48 * ε ^ (9 : ℕ) + 1307713135 / 1944 * ε ^ (8 : ℕ) - 10749616849 / 2592 * ε ^ (7 : ℕ)
    + 1480213717249 / 139968 * ε ^ (6 : ℕ) - 254106585881 / 17496 * ε ^ (5 : ℕ)
    + 1641999877027 / 139968 * ε ^ (4 : ℕ) - 6387295144343 / 1119744 * ε ^ (3 : ℕ)
    + 3651419186293 / 2239488 * ε ^ (2 : ℕ) - 561143391463 / 2239488 * ε + 988541347 / 62208

/-- The Taylor remainder of the coefficient of `I₁₂`, analytic at `0`. -/
noncomputable def setEQI12 (ε : ℂ) : ℂ :=
  setERI12 ε / setEUI12 ε

/-- The coefficient of `I₁₂` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI12_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI12 ε ≠ 0) :
    setECoeffI12 ε = ε⁻¹ ^ (1 : ℕ) * setETI12 ε + ε ^ (4 : ℕ) * setEQI12 ε := by
  have hden : setEDenI12 (4 - 2 * ε) = 3538944 * (ε ^ (1 : ℕ) * setEUI12 ε) := by
    simp only [setEDenI12, setEUI12]; ring
  have hnum : setENumI12 (4 - 2 * ε) =
      3538944 * (setEUI12 ε * setETI12 ε + ε ^ (5 : ℕ) * setERI12 ε) := by
    simp only [setENumI12, setEUI12, setETI12, setERI12]; ring
  rw [setECoeffI12, hden, hnum, setEQI12]
  field_simp

theorem setEUI12_zero : setEUI12 0 = 1 := by
  norm_num [setEUI12]

theorem analyticAt_setEUI12 (z : ℂ) : AnalyticAt ℂ setEUI12 z := by
  unfold setEUI12; fun_prop

theorem analyticAt_setEQI12 : AnalyticAt ℂ setEQI12 0 := by
  have hR : AnalyticAt ℂ setERI12 0 := by unfold setERI12; fun_prop
  exact hR.div (analyticAt_setEUI12 0) (by rw [setEUI12_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₁₃`, in `d`. -/
noncomputable def setENumI13 (d : ℂ) : ℂ :=
  (972 * d ^ (15 : ℕ) - 58077 * d ^ (14 : ℕ) + 1604529 * d ^ (13 : ℕ) - 27233973 * d ^ (12 : ℕ)
    + 317824701 * d ^ (11 : ℕ) - 2701736107 * d ^ (10 : ℕ) + 17278336181 * d ^ (9 : ℕ)
    - 84614292981 * d ^ (8 : ℕ) + 319745389535 * d ^ (7 : ℕ) - 931911321296 * d ^ (6 : ℕ)
    + 2077034099210 * d ^ (5 : ℕ) - 3476085228534 * d ^ (4 : ℕ) + 4229452078184 * d ^ (3 : ℕ)
    - 3534383915528 * d ^ (2 : ℕ) + 1816162088896 * d - 433479411712)

/-- Denominator of the set (e) coefficient of `I₁₃`, in `d`. -/
noncomputable def setEDenI13 (d : ℂ) : ℂ :=
  6144 * (d - 5) * (2 * d - 7) * (3 * d - 13) * (3 * d - 11) * (d - 4) ^ (2 : ℕ) *
    (d - 3) ^ (2 : ℕ) * (d - 1) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₁₃` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI13 (ε : ℂ) : ℂ :=
  setENumI13 (4 - 2 * ε) / setEDenI13 (4 - 2 * ε)

/-- The factors of `setEDenI13 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI13 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - 4 * ε) * (1 + 6 * ε) * (1 - 6 * ε) * (1 - 2 * ε) ^ (2 : ℕ) *
    (1 - 2 / 3 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 2 · setECoeffI13 ε` to degree 5. -/
noncomputable def setETI13 (ε : ℂ) : ℂ :=
  42599347 / 69984 * ε ^ (5 : ℕ) + 32960767 / 186624 * ε ^ (4 : ℕ) + 296993 / 15552 * ε ^ (3 : ℕ)
    + 126169 / 20736 * ε ^ (2 : ℕ) + 751 / 864 * ε + 151 / 576

/-- The Taylor remainder numerator of the coefficient of `I₁₃`. -/
noncomputable def setERI13 (ε : ℂ) : ℂ :=
  -144 * ε ^ (9 : ℕ) + 18 * ε ^ (8 : ℕ) - 680388889 / 2187 * ε ^ (7 : ℕ)
    + 523558171 / 486 * ε ^ (6 : ℕ) - 80550865607 / 78732 * ε ^ (5 : ℕ)
    - 792187537 / 17496 * ε ^ (4 : ℕ) + 117684113641 / 314928 * ε ^ (3 : ℕ)
    - 17227330769 / 209952 * ε ^ (2 : ℕ) - 30151548821 / 1259712 * ε + 2594621473 / 419904

/-- The Taylor remainder of the coefficient of `I₁₃`, analytic at `0`. -/
noncomputable def setEQI13 (ε : ℂ) : ℂ :=
  setERI13 ε / setEUI13 ε

/-- The coefficient of `I₁₃` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI13_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI13 ε ≠ 0) :
    setECoeffI13 ε = ε⁻¹ ^ (2 : ℕ) * setETI13 ε + ε ^ (4 : ℕ) * setEQI13 ε := by
  have hden : setEDenI13 (4 - 2 * ε) = 221184 * (ε ^ (2 : ℕ) * setEUI13 ε) := by
    simp only [setEDenI13, setEUI13]; ring
  have hnum : setENumI13 (4 - 2 * ε) =
      221184 * (setEUI13 ε * setETI13 ε + ε ^ (6 : ℕ) * setERI13 ε) := by
    simp only [setENumI13, setEUI13, setETI13, setERI13]; ring
  rw [setECoeffI13, hden, hnum, setEQI13]
  field_simp

theorem setEUI13_zero : setEUI13 0 = 1 := by
  norm_num [setEUI13]

theorem analyticAt_setEUI13 (z : ℂ) : AnalyticAt ℂ setEUI13 z := by
  unfold setEUI13; fun_prop

theorem analyticAt_setEQI13 : AnalyticAt ℂ setEQI13 0 := by
  have hR : AnalyticAt ℂ setERI13 0 := by unfold setERI13; fun_prop
  exact hR.div (analyticAt_setEUI13 0) (by rw [setEUI13_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₁₄`, in `d`. -/
noncomputable def setENumI14 (d : ℂ) : ℂ :=
  -(93312 * d ^ (19 : ℕ) - 6207678 * d ^ (18 : ℕ) + 194421195 * d ^ (17 : ℕ)
    - 3805323282 * d ^ (16 : ℕ) + 52118057715 * d ^ (15 : ℕ) - 530104737276 * d ^ (14 : ℕ)
    + 4147764715267 * d ^ (13 : ℕ) - 25518391239874 * d ^ (12 : ℕ) + 125117202860277 * d ^ (11 : ℕ)
    - 492519673118842 * d ^ (10 : ℕ) + 1560610892739226 * d ^ (9 : ℕ)
    - 3973475657333752 * d ^ (8 : ℕ) + 8079872803433552 * d ^ (7 : ℕ)
    - 12979298626883328 * d ^ (6 : ℕ) + 16196002620962784 * d ^ (5 : ℕ)
    - 15317147731477760 * d ^ (4 : ℕ) + 10590400821693440 * d ^ (3 : ℕ)
    - 5065386964868096 * d ^ (2 : ℕ) + 1520293065646080 * d - 223712300072960)

/-- Denominator of the set (e) coefficient of `I₁₄`, in `d`. -/
noncomputable def setEDenI14 (d : ℂ) : ℂ :=
  12288 * (d - 5) * (d - 2) * (3 * d - 13) * (3 * d - 10) * (3 * d - 8) * (d - 4) ^ (2 : ℕ) *
    (d - 3) ^ (2 : ℕ) * (d - 1) ^ (2 : ℕ) * (2 * d - 7) ^ (3 : ℕ)

/-- The set (e) coefficient of `I₁₄` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI14 (ε : ℂ) : ℂ :=
  setENumI14 (4 - 2 * ε) / setEDenI14 (4 - 2 * ε)

/-- The factors of `setEDenI14 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI14 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - ε) * (1 + 6 * ε) * (1 - 3 * ε) * (1 - 3 / 2 * ε) * (1 - 2 * ε) ^ (2 : ℕ) *
    (1 - 2 / 3 * ε) ^ (2 : ℕ) * (1 - 4 * ε) ^ (3 : ℕ)

/-- The Taylor polynomial of `ε ^ 2 · setECoeffI14 ε` to degree 5. -/
noncomputable def setETI14 (ε : ℂ) : ℂ :=
  -147877165 / 186624 * ε ^ (5 : ℕ) + 2483923 / 15552 * ε ^ (4 : ℕ) - 84727 / 5184 * ε ^ (3 : ℕ)
    + 4121 / 864 * ε ^ (2 : ℕ) - 185 / 288 * ε + 1 / 48

/-- The Taylor remainder numerator of the coefficient of `I₁₄`. -/
noncomputable def setERI14 (ε : ℂ) : ℂ :=
  6912 * ε ^ (13 : ℕ) - 32742 * ε ^ (12 : ℕ) + 2390964739 / 486 * ε ^ (11 : ℕ)
    - 44688621379 / 1458 * ε ^ (10 : ℕ) + 1386305913263 / 17496 * ε ^ (9 : ℕ)
    - 5663135319047 / 52488 * ε ^ (8 : ℕ) + 1862623024613 / 23328 * ε ^ (7 : ℕ)
    - 2646934205743 / 104976 * ε ^ (6 : ℕ) - 5556302844637 / 839808 * ε ^ (5 : ℕ)
    + 1023046583429 / 104976 * ε ^ (4 : ℕ) - 7007624286947 / 1679616 * ε ^ (3 : ℕ)
    + 1042761092381 / 1119744 * ε ^ (2 : ℕ) - 182961529673 / 1679616 * ε + 5894082935 / 1119744

/-- The Taylor remainder of the coefficient of `I₁₄`, analytic at `0`. -/
noncomputable def setEQI14 (ε : ℂ) : ℂ :=
  setERI14 ε / setEUI14 ε

/-- The coefficient of `I₁₄` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI14_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI14 ε ≠ 0) :
    setECoeffI14 ε = ε⁻¹ ^ (2 : ℕ) * setETI14 ε + ε ^ (4 : ℕ) * setEQI14 ε := by
  have hden : setEDenI14 (4 - 2 * ε) = 7077888 * (ε ^ (2 : ℕ) * setEUI14 ε) := by
    simp only [setEDenI14, setEUI14]; ring
  have hnum : setENumI14 (4 - 2 * ε) =
      7077888 * (setEUI14 ε * setETI14 ε + ε ^ (6 : ℕ) * setERI14 ε) := by
    simp only [setENumI14, setEUI14, setETI14, setERI14]; ring
  rw [setECoeffI14, hden, hnum, setEQI14]
  field_simp

theorem setEUI14_zero : setEUI14 0 = 1 := by
  norm_num [setEUI14]

theorem analyticAt_setEUI14 (z : ℂ) : AnalyticAt ℂ setEUI14 z := by
  unfold setEUI14; fun_prop

theorem analyticAt_setEQI14 : AnalyticAt ℂ setEQI14 0 := by
  have hR : AnalyticAt ℂ setERI14 0 := by unfold setERI14; fun_prop
  exact hR.div (analyticAt_setEUI14 0) (by rw [setEUI14_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₁₅`, in `d`. -/
noncomputable def setENumI15 (d : ℂ) : ℂ :=
  (324 * d ^ (16 : ℕ) - 25407 * d ^ (15 : ℕ) + 898443 * d ^ (14 : ℕ) - 19229169 * d ^ (13 : ℕ)
    + 280133559 * d ^ (12 : ℕ) - 2951393429 * d ^ (11 : ℕ) + 23281042367 * d ^ (10 : ℕ)
    - 140301258959 * d ^ (9 : ℕ) + 652897566125 * d ^ (8 : ℕ) - 2353934615916 * d ^ (7 : ℕ)
    + 6552426128742 * d ^ (6 : ℕ) - 13929126696928 * d ^ (5 : ℕ) + 22153043815592 * d ^ (4 : ℕ)
    - 25451662520096 * d ^ (3 : ℕ) + 19882785423616 * d ^ (2 : ℕ) - 9406332698624 * d
    + 2019820789760)

/-- Denominator of the set (e) coefficient of `I₁₅`, in `d`. -/
noncomputable def setEDenI15 (d : ℂ) : ℂ :=
  1536 * (d - 5) * (2 * d - 7) * (3 * d - 13) * (3 * d - 11) * (3 * d - 8) * (d - 4) ^ (2 : ℕ) *
    (d - 3) ^ (2 : ℕ) * (d - 1) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₁₅` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI15 (ε : ℂ) : ℂ :=
  setENumI15 (4 - 2 * ε) / setEDenI15 (4 - 2 * ε)

/-- The factors of `setEDenI15 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI15 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - 4 * ε) * (1 + 6 * ε) * (1 - 6 * ε) * (1 - 3 / 2 * ε) * (1 - 2 * ε) ^ (2 : ℕ) *
    (1 - 2 / 3 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 2 · setECoeffI15 ε` to degree 5. -/
noncomputable def setETI15 (ε : ℂ) : ℂ :=
  21524993 / 8748 * ε ^ (5 : ℕ) + 8149381 / 11664 * ε ^ (4 : ℕ) + 614221 / 7776 * ε ^ (3 : ℕ)
    + 8083 / 324 * ε ^ (2 : ℕ) + 613 / 216 * ε + 17 / 18

/-- The Taylor remainder numerator of the coefficient of `I₁₅`. -/
noncomputable def setERI15 (ε : ℂ) : ℂ :=
  96 * ε ^ (10 : ℕ) + 692 * ε ^ (9 : ℕ) + 1377389114 / 729 * ε ^ (8 : ℕ)
    - 17080658359 / 2187 * ε ^ (7 : ℕ) + 139354949921 / 13122 * ε ^ (6 : ℕ)
    - 312013006643 / 78732 * ε ^ (5 : ℕ) - 124103319511 / 52488 * ε ^ (4 : ℕ)
    + 622696390111 / 314928 * ε ^ (3 : ℕ) - 4320425125 / 23328 * ε ^ (2 : ℕ)
    - 41706370361 / 314928 * ε + 10364877337 / 419904

/-- The Taylor remainder of the coefficient of `I₁₅`, analytic at `0`. -/
noncomputable def setEQI15 (ε : ℂ) : ℂ :=
  setERI15 ε / setEUI15 ε

/-- The coefficient of `I₁₅` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI15_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI15 ε ≠ 0) :
    setECoeffI15 ε = ε⁻¹ ^ (2 : ℕ) * setETI15 ε + ε ^ (4 : ℕ) * setEQI15 ε := by
  have hden : setEDenI15 (4 - 2 * ε) = 221184 * (ε ^ (2 : ℕ) * setEUI15 ε) := by
    simp only [setEDenI15, setEUI15]; ring
  have hnum : setENumI15 (4 - 2 * ε) =
      221184 * (setEUI15 ε * setETI15 ε + ε ^ (6 : ℕ) * setERI15 ε) := by
    simp only [setENumI15, setEUI15, setETI15, setERI15]; ring
  rw [setECoeffI15, hden, hnum, setEQI15]
  field_simp

theorem setEUI15_zero : setEUI15 0 = 1 := by
  norm_num [setEUI15]

theorem analyticAt_setEUI15 (z : ℂ) : AnalyticAt ℂ setEUI15 z := by
  unfold setEUI15; fun_prop

theorem analyticAt_setEQI15 : AnalyticAt ℂ setEQI15 0 := by
  have hR : AnalyticAt ℂ setERI15 0 := by unfold setERI15; fun_prop
  exact hR.div (analyticAt_setEUI15 0) (by rw [setEUI15_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₁₆`, in `d`. -/
noncomputable def setENumI16 (d : ℂ) : ℂ :=
  -(2592 * d ^ (17 : ℕ) - 148527 * d ^ (16 : ℕ) + 3941199 * d ^ (15 : ℕ) - 64004115 * d ^ (14 : ℕ)
    + 707363901 * d ^ (13 : ℕ) - 5586025291 * d ^ (12 : ℕ) + 32078483441 * d ^ (11 : ℕ)
    - 132437228677 * d ^ (10 : ℕ) + 367975821291 * d ^ (9 : ℕ) - 505409797710 * d ^ (8 : ℕ)
    - 807051515512 * d ^ (7 : ℕ) + 6582721763008 * d ^ (6 : ℕ) - 19150955022480 * d ^ (5 : ℕ)
    + 34411184738592 * d ^ (4 : ℕ) - 40769170492672 * d ^ (3 : ℕ) + 30992067470336 * d ^ (2 : ℕ)
    - 13609902683136 * d + 2579711221760)

/-- Denominator of the set (e) coefficient of `I₁₆`, in `d`. -/
noncomputable def setEDenI16 (d : ℂ) : ℂ :=
  3072 * (d - 5) * (d - 4) * (d - 2) * (3 * d - 13) * (3 * d - 10) * (3 * d - 8) *
    (d - 3) ^ (2 : ℕ) * (d - 1) ^ (2 : ℕ) * (2 * d - 7) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₁₆` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI16 (ε : ℂ) : ℂ :=
  setENumI16 (4 - 2 * ε) / setEDenI16 (4 - 2 * ε)

/-- The factors of `setEDenI16 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI16 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - ε) * (1 + 6 * ε) * (1 - 3 * ε) * (1 - 3 / 2 * ε) * (1 - 2 * ε) ^ (2 : ℕ) *
    (1 - 2 / 3 * ε) ^ (2 : ℕ) * (1 - 4 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI16 ε` to degree 4. -/
noncomputable def setETI16 (ε : ℂ) : ℂ :=
  -9056791 / 7776 * ε ^ (4 : ℕ) + 206401 / 864 * ε ^ (3 : ℕ) - 13297 / 432 * ε ^ (2 : ℕ)
    + 607 / 72 * ε - 17 / 24

/-- The Taylor remainder numerator of the coefficient of `I₁₆`. -/
noncomputable def setERI16 (ε : ℂ) : ℂ :=
  -384 * ε ^ (12 : ℕ) + 2054 * ε ^ (11 : ℕ) - 145135645 / 81 * ε ^ (10 : ℕ)
    + 5251031849 / 486 * ε ^ (9 : ℕ) - 76996806419 / 2916 * ε ^ (8 : ℕ)
    + 577881817825 / 17496 * ε ^ (7 : ℕ) - 737457303205 / 34992 * ε ^ (6 : ℕ)
    + 279833676335 / 69984 * ε ^ (5 : ℕ) + 481668215873 / 139968 * ε ^ (4 : ℕ)
    - 384153809549 / 139968 * ε ^ (3 : ℕ) + 121204272755 / 139968 * ε ^ (2 : ℕ)
    - 18652648561 / 139968 * ε + 47998355 / 5832

/-- The Taylor remainder of the coefficient of `I₁₆`, analytic at `0`. -/
noncomputable def setEQI16 (ε : ℂ) : ℂ :=
  setERI16 ε / setEUI16 ε

/-- The coefficient of `I₁₆` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI16_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI16 ε ≠ 0) :
    setECoeffI16 ε = ε⁻¹ ^ (1 : ℕ) * setETI16 ε + ε ^ (4 : ℕ) * setEQI16 ε := by
  have hden : setEDenI16 (4 - 2 * ε) = (-884736) * (ε ^ (1 : ℕ) * setEUI16 ε) := by
    simp only [setEDenI16, setEUI16]; ring
  have hnum : setENumI16 (4 - 2 * ε) =
      (-884736) * (setEUI16 ε * setETI16 ε + ε ^ (5 : ℕ) * setERI16 ε) := by
    simp only [setENumI16, setEUI16, setETI16, setERI16]; ring
  rw [setECoeffI16, hden, hnum, setEQI16]
  field_simp

theorem setEUI16_zero : setEUI16 0 = 1 := by
  norm_num [setEUI16]

theorem analyticAt_setEUI16 (z : ℂ) : AnalyticAt ℂ setEUI16 z := by
  unfold setEUI16; fun_prop

theorem analyticAt_setEQI16 : AnalyticAt ℂ setEQI16 0 := by
  have hR : AnalyticAt ℂ setERI16 0 := by unfold setERI16; fun_prop
  exact hR.div (analyticAt_setEUI16 0) (by rw [setEUI16_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₁₇`, in `d`. -/
noncomputable def setENumI17 (d : ℂ) : ℂ :=
  (2 * d - 5) * (1377 * d ^ (13 : ℕ) - 75231 * d ^ (12 : ℕ) + 1844502 * d ^ (11 : ℕ)
    - 26944963 * d ^ (10 : ℕ) + 262203123 * d ^ (9 : ℕ) - 1797572315 * d ^ (8 : ℕ)
    + 8941683094 * d ^ (7 : ℕ) - 32697207783 * d ^ (6 : ℕ) + 87913433616 * d ^ (5 : ℕ)
    - 171612136700 * d ^ (4 : ℕ) + 236208721200 * d ^ (3 : ℕ) - 216743250464 * d ^ (2 : ℕ)
    + 118518411200 * d - 29040736256)

/-- Denominator of the set (e) coefficient of `I₁₇`, in `d`. -/
noncomputable def setEDenI17 (d : ℂ) : ℂ :=
  768 * (d - 5) * (d - 4) * (d - 2) * (2 * d - 7) * (3 * d - 13) * (3 * d - 8) * (d - 3) ^ (2 : ℕ) *
    (d - 1) ^ (2 : ℕ)

/-- The set (e) coefficient of `I₁₇` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI17 (ε : ℂ) : ℂ :=
  setENumI17 (4 - 2 * ε) / setEDenI17 (4 - 2 * ε)

/-- The factors of `setEDenI17 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI17 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 - ε) * (1 - 4 * ε) * (1 + 6 * ε) * (1 - 3 / 2 * ε) * (1 - 2 * ε) ^ (2 : ℕ) *
    (1 - 2 / 3 * ε) ^ (2 : ℕ)

/-- The Taylor polynomial of `ε ^ 1 · setECoeffI17 ε` to degree 3. -/
noncomputable def setETI17 (ε : ℂ) : ℂ :=
  -5706823 / 5184 * ε ^ (3 : ℕ) + 158795 / 864 * ε ^ (2 : ℕ) - 4453 / 144 * ε + 233 / 48

/-- The Taylor remainder numerator of the coefficient of `I₁₇`. -/
noncomputable def setERI17 (ε : ℂ) : ℂ :=
  -408 * ε ^ (10 : ℕ) - 694 / 3 * ε ^ (9 : ℕ) - 11092463 / 81 * ε ^ (8 : ℕ)
    + 13673815 / 18 * ε ^ (7 : ℕ) - 4657708399 / 2916 * ε ^ (6 : ℕ)
    + 2261332469 / 1458 * ε ^ (5 : ℕ) - 6517082509 / 11664 * ε ^ (4 : ℕ)
    - 4055718211 / 23328 * ε ^ (3 : ℕ) + 10091096639 / 46656 * ε ^ (2 : ℕ) - 6180879367 / 93312 * ε
    + 211246391 / 31104

/-- The Taylor remainder of the coefficient of `I₁₇`, analytic at `0`. -/
noncomputable def setEQI17 (ε : ℂ) : ℂ :=
  setERI17 ε / setEUI17 ε

/-- The coefficient of `I₁₇` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI17_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI17 ε ≠ 0) :
    setECoeffI17 ε = ε⁻¹ ^ (1 : ℕ) * setETI17 ε + ε ^ (3 : ℕ) * setEQI17 ε := by
  have hden : setEDenI17 (4 - 2 * ε) = (-110592) * (ε ^ (1 : ℕ) * setEUI17 ε) := by
    simp only [setEDenI17, setEUI17]; ring
  have hnum : setENumI17 (4 - 2 * ε) =
      (-110592) * (setEUI17 ε * setETI17 ε + ε ^ (4 : ℕ) * setERI17 ε) := by
    simp only [setENumI17, setEUI17, setETI17, setERI17]; ring
  rw [setECoeffI17, hden, hnum, setEQI17]
  field_simp

theorem setEUI17_zero : setEUI17 0 = 1 := by
  norm_num [setEUI17]

theorem analyticAt_setEUI17 (z : ℂ) : AnalyticAt ℂ setEUI17 z := by
  unfold setEUI17; fun_prop

theorem analyticAt_setEQI17 : AnalyticAt ℂ setEQI17 0 := by
  have hR : AnalyticAt ℂ setERI17 0 := by unfold setERI17; fun_prop
  exact hR.div (analyticAt_setEUI17 0) (by rw [setEUI17_zero]; exact one_ne_zero)

/-- Numerator of the set (e) coefficient of `I₁₈`, in `d`. -/
noncomputable def setENumI18 (d : ℂ) : ℂ :=
  (10368 * d ^ (19 : ℕ) - 743040 * d ^ (18 : ℕ) + 25637616 * d ^ (17 : ℕ) - 566031147 * d ^ (16 : ℕ)
    + 8941562709 * d ^ (15 : ℕ) - 106928063871 * d ^ (14 : ℕ) + 999024599741 * d ^ (13 : ℕ)
    - 7428103187957 * d ^ (12 : ℕ) + 44428755325135 * d ^ (11 : ℕ) - 214979297553021 * d ^ (10 : ℕ)
    + 843056436361591 * d ^ (9 : ℕ) - 2674969064239604 * d ^ (8 : ℕ)
    + 6830988430366920 * d ^ (7 : ℕ) - 13905410349981360 * d ^ (6 : ℕ)
    + 22222339074353264 * d ^ (5 : ℕ) - 27233033103700928 * d ^ (4 : ℕ)
    + 24668487178385152 * d ^ (3 : ℕ) - 15539396117825536 * d ^ (2 : ℕ) + 6069228287657984 * d
    - 1105114261078016)

/-- Denominator of the set (e) coefficient of `I₁₈`, in `d`. -/
noncomputable def setEDenI18 (d : ℂ) : ℂ :=
  49152 * (d - 5) * (3 * d - 13) * (3 * d - 11) * (3 * d - 8) * (d - 4) ^ (2 : ℕ) *
    (d - 1) ^ (2 : ℕ) * (2 * d - 7) ^ (2 : ℕ) * (d - 3) ^ (3 : ℕ)

/-- The set (e) coefficient of `I₁₈` at `d = 4 - 2ε`. -/
noncomputable def setECoeffI18 (ε : ℂ) : ℂ :=
  setENumI18 (4 - 2 * ε) / setEDenI18 (4 - 2 * ε)

/-- The factors of `setEDenI18 (4 - 2ε)` not vanishing at `ε = 0`, normalized to `1` there. -/
noncomputable def setEUI18 (ε : ℂ) : ℂ :=
  (1 + 2 * ε) * (1 + 6 * ε) * (1 - 6 * ε) * (1 - 3 / 2 * ε) * (1 - 2 / 3 * ε) ^ (2 : ℕ) *
    (1 - 4 * ε) ^ (2 : ℕ) * (1 - 2 * ε) ^ (3 : ℕ)

/-- The Taylor polynomial of `ε ^ 2 · setECoeffI18 ε` to degree 5. -/
noncomputable def setETI18 (ε : ℂ) : ℂ :=
  -477311927 / 139968 * ε ^ (5 : ℕ) - 326411449 / 186624 * ε ^ (4 : ℕ)
    - 3697129 / 31104 * ε ^ (3 : ℕ) - 34673 / 648 * ε ^ (2 : ℕ) - 2977 / 864 * ε - 425 / 288

/-- The Taylor remainder numerator of the coefficient of `I₁₈`. -/
noncomputable def setERI18 (ε : ℂ) : ℂ :=
  -768 * ε ^ (13 : ℕ) + 1664 * ε ^ (12 : ℕ) - 28088 / 3 * ε ^ (11 : ℕ)
    - 61059565513 / 2916 * ε ^ (10 : ℕ) + 1707077643547 / 17496 * ε ^ (9 : ℕ)
    - 16888552036649 / 104976 * ε ^ (8 : ℕ) + 59424499150835 / 629856 * ε ^ (7 : ℕ)
    + 10299283324589 / 419904 * ε ^ (6 : ℕ) - 5018550402917 / 93312 * ε ^ (5 : ℕ)
    + 31131873547573 / 1679616 * ε ^ (4 : ℕ) + 10174103897683 / 3359232 * ε ^ (3 : ℕ)
    - 952223869985 / 279936 * ε ^ (2 : ℕ) + 3956740233047 / 5038848 * ε - 101698360801 / 1679616

/-- The Taylor remainder of the coefficient of `I₁₈`, analytic at `0`. -/
noncomputable def setEQI18 (ε : ℂ) : ℂ :=
  setERI18 ε / setEUI18 ε

/-- The coefficient of `I₁₈` as its truncated Laurent expansion plus remainder. -/
theorem setECoeffI18_eq {ε : ℂ} (hε : ε ≠ 0) (hU : setEUI18 ε ≠ 0) :
    setECoeffI18 ε = ε⁻¹ ^ (2 : ℕ) * setETI18 ε + ε ^ (4 : ℕ) * setEQI18 ε := by
  have hden : setEDenI18 (4 - 2 * ε) = 7077888 * (ε ^ (2 : ℕ) * setEUI18 ε) := by
    simp only [setEDenI18, setEUI18]; ring
  have hnum : setENumI18 (4 - 2 * ε) =
      7077888 * (setEUI18 ε * setETI18 ε + ε ^ (6 : ℕ) * setERI18 ε) := by
    simp only [setENumI18, setEUI18, setETI18, setERI18]; ring
  rw [setECoeffI18, hden, hnum, setEQI18]
  field_simp

theorem setEUI18_zero : setEUI18 0 = 1 := by
  norm_num [setEUI18]

theorem analyticAt_setEUI18 (z : ℂ) : AnalyticAt ℂ setEUI18 z := by
  unfold setEUI18; fun_prop

theorem analyticAt_setEQI18 : AnalyticAt ℂ setEQI18 0 := by
  have hR : AnalyticAt ℂ setERI18 0 := by unfold setERI18; fun_prop
  exact hR.div (analyticAt_setEUI18 0) (by rw [setEUI18_zero]; exact one_ne_zero)

end QED.ThreeLoopE
