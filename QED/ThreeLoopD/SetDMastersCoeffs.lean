/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d) of `A₁⁽⁶⁾`: the coefficients of the eleven master integrals

The light-by-light set (d) of the three-loop electron anomaly, after the trace, the
`g - 2` projection and the IBP reduction (offline survey PD1: FORM and Kira 3.1, generated file
`coeffs.json`), is a combination `∑ᵢ cᵢ(d) Mᵢ(d)` of eleven master integrals. Each master is one
of the Laporta–Remiddi (1996) masters `I₂, I₃, I₅, I₈, I₉, I₁₂, I₁₃, I₁₄, I₁₅, I₁₆, I₁₈`.
This file defines the eleven coefficients exactly, as rational functions of `d`, and evaluates
them at `d = 4 - 2ε`.

For the master `I_j`:
* `setDNumIj d`, `setDDenIj d`: the numerator and denominator in `d`, transcribed (by a script)
  from `coeffs.json`;
* `setDCoeffIj ε = setDNumIj (4 - 2ε) / setDDenIj (4 - 2ε)`: the coefficient;
* `setDAIj ε`: the numerator after bringing the coefficient to the common denominator
  `ε ^ pⱼ · setDDen ε`, where `pⱼ ≤ 2` is the pole order of the coefficient at `ε = 0` and
  `setDDen ε` is a product of factors `1 + bε` with `|b| ≤ 6`, equal to `1` at `ε = 0`;
* `setDCoeffIj_eq`: `setDCoeffIj ε = setDAIj ε / (ε ^ pⱼ · setDDen ε)` for `ε ≠ 0` and
  `setDDen ε ≠ 0`.

The coefficients carry the overall normalization of the survey: the combination with the
masters in the normalization `Iⱼ C(ε)⁻¹` of Laporta–Remiddi, with the sign `(-1) ^ (lines)` of
`QED.ThreeLoopD.setDCombination`, is the coefficient of `(α/π)³` itself.
-/

@[expose] public section

namespace QED.ThreeLoopD

/-- Numerator of the set (d) coefficient of `I₂` (Kira master `lbl[0,1,1,1,0,1,1,1,0]`),
in `d`. -/
noncomputable def setDNumI2 (d : ℂ) : ℂ :=
  -(8 * d ^ (5 : ℕ) - 162 * d ^ (4 : ℕ) + 1307 * d ^ (3 : ℕ) - 5231 * d ^ (2 : ℕ) + 10358 * d
    - 8100)

/-- Denominator of the set (d) coefficient of `I₂`, in `d`. -/
noncomputable def setDDenI2 (d : ℂ) : ℂ :=
  4 * (d - 5) * (d - 4) * (d - 3) * (d - 1) * (2 * d - 9)

/-- The set (d) coefficient of `I₂` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI2 (ε : ℂ) : ℂ :=
  setDNumI2 (4 - 2 * ε) / setDDenI2 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₃` (Kira master `lbl[1,0,1,1,1,0,1,1,0]`),
in `d`. -/
noncomputable def setDNumI3 (d : ℂ) : ℂ :=
  (-3) * (d - 3) * (3 * d - 10) * (d ^ (2 : ℕ) - 9 * d + 21)

/-- Denominator of the set (d) coefficient of `I₃`, in `d`. -/
noncomputable def setDDenI3 (d : ℂ) : ℂ :=
  4 * (d - 5) * (d - 2) * (d - 1) * (2 * d - 9)

/-- The set (d) coefficient of `I₃` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI3 (ε : ℂ) : ℂ :=
  setDNumI3 (4 - 2 * ε) / setDDenI3 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₅` (Kira master `lbl[0,1,1,1,1,1,1,0,0]`),
in `d`. -/
noncomputable def setDNumI5 (d : ℂ) : ℂ :=
  -(16 * d ^ (7 : ℕ) - 338 * d ^ (6 : ℕ) + 2875 * d ^ (5 : ℕ) - 12254 * d ^ (4 : ℕ)
    + 25271 * d ^ (3 : ℕ) - 12978 * d ^ (2 : ℕ) - 34208 * d + 42480)

/-- Denominator of the set (d) coefficient of `I₅`, in `d`. -/
noncomputable def setDDenI5 (d : ℂ) : ℂ :=
  8 * (d - 5) * (d - 4) * (d - 3) * (d - 2) * (d - 1) * (2 * d - 9)

/-- The set (d) coefficient of `I₅` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI5 (ε : ℂ) : ℂ :=
  setDNumI5 (4 - 2 * ε) / setDDenI5 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₈` (Kira master `lbl[0,0,0,1,1,1,1,1,0]`),
in `d`. -/
noncomputable def setDNumI8 (d : ℂ) : ℂ :=
  -(36 * d ^ (8 : ℕ) - 933 * d ^ (7 : ℕ) + 10102 * d ^ (6 : ℕ) - 58442 * d ^ (5 : ℕ)
    + 188388 * d ^ (4 : ℕ) - 299761 * d ^ (3 : ℕ) + 56674 * d ^ (2 : ℕ) + 479008 * d - 471712)

/-- Denominator of the set (d) coefficient of `I₈`, in `d`. -/
noncomputable def setDDenI8 (d : ℂ) : ℂ :=
  24 * (d - 5) * (d - 2) * (d - 1) * (3 * d - 13) * (3 * d - 11) * (d - 4) ^ (2 : ℕ)

/-- The set (d) coefficient of `I₈` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI8 (ε : ℂ) : ℂ :=
  setDNumI8 (4 - 2 * ε) / setDDenI8 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₉` (Kira master `lbl[0,1,1,1,0,1,1,0,0]`),
in `d`. -/
noncomputable def setDNumI9 (d : ℂ) : ℂ :=
  -(4 * d ^ (6 : ℕ) - 44 * d ^ (5 : ℕ) - 37 * d ^ (4 : ℕ) + 2444 * d ^ (3 : ℕ) - 13007 * d ^ (2 : ℕ)
    + 27940 * d - 21996)

/-- Denominator of the set (d) coefficient of `I₉`, in `d`. -/
noncomputable def setDDenI9 (d : ℂ) : ℂ :=
  8 * (d - 5) * (d - 4) * (d - 2) * (d - 1) * (2 * d - 9)

/-- The set (d) coefficient of `I₉` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI9 (ε : ℂ) : ℂ :=
  setDNumI9 (4 - 2 * ε) / setDDenI9 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₁₂` (Kira master `lbl[0,1,0,0,1,1,1,0,0]`),
in `d`. -/
noncomputable def setDNumI12 (d : ℂ) : ℂ :=
  -((2 * d - 5) * (112 * d ^ (8 : ℕ) - 3078 * d ^ (7 : ℕ) + 36819 * d ^ (6 : ℕ)
    - 250690 * d ^ (5 : ℕ) + 1064495 * d ^ (4 : ℕ) - 2893310 * d ^ (3 : ℕ) + 4929804 * d ^ (2 : ℕ)
    - 4829544 * d + 2089152))

/-- Denominator of the set (d) coefficient of `I₁₂`, in `d`. -/
noncomputable def setDDenI12 (d : ℂ) : ℂ :=
  384 * (d - 5) * (d - 1) * (2 * d - 9) * (d - 4) ^ (2 : ℕ) * (d - 3) ^ (2 : ℕ)

/-- The set (d) coefficient of `I₁₂` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI12 (ε : ℂ) : ℂ :=
  setDNumI12 (4 - 2 * ε) / setDDenI12 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₁₃` (Kira master `lbl[0,0,0,1,1,0,1,1,0]`),
in `d`. -/
noncomputable def setDNumI13 (d : ℂ) : ℂ :=
  (3 * d - 8) * (1008 * d ^ (9 : ℕ) - 29562 * d ^ (8 : ℕ) + 373003 * d ^ (7 : ℕ)
    - 2626085 * d ^ (6 : ℕ) + 11118408 * d ^ (5 : ℕ) - 27944248 * d ^ (4 : ℕ)
    + 35834983 * d ^ (3 : ℕ) - 4177361 * d ^ (2 : ℕ) - 44363626 * d + 37628136)

/-- Denominator of the set (d) coefficient of `I₁₃`, in `d`. -/
noncomputable def setDDenI13 (d : ℂ) : ℂ :=
  768 * (d - 5) * (d - 1) * (2 * d - 9) * (3 * d - 13) * (3 * d - 11) * (d - 4) ^ (2 : ℕ) *
    (d - 3) ^ (2 : ℕ)

/-- The set (d) coefficient of `I₁₃` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI13 (ε : ℂ) : ℂ :=
  setDNumI13 (4 - 2 * ε) / setDDenI13 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₁₄` (Kira master `lbl[0,1,1,0,0,1,1,0,0]`),
in `d`. -/
noncomputable def setDNumI14 (d : ℂ) : ℂ :=
  (212 * d ^ (10 : ℕ) - 6718 * d ^ (9 : ℕ) + 93938 * d ^ (8 : ℕ) - 760601 * d ^ (7 : ℕ)
    + 3927527 * d ^ (6 : ℕ) - 13392752 * d ^ (5 : ℕ) + 30049287 * d ^ (4 : ℕ)
    - 42365815 * d ^ (3 : ℕ) + 32942970 * d ^ (2 : ℕ) - 8602896 * d - 2702592)

/-- Denominator of the set (d) coefficient of `I₁₄`, in `d`. -/
noncomputable def setDDenI14 (d : ℂ) : ℂ :=
  192 * (d - 5) * (d - 1) * (2 * d - 9) * (2 * d - 7) * (d - 4) ^ (2 : ℕ) * (d - 3) ^ (2 : ℕ)

/-- The set (d) coefficient of `I₁₄` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI14 (ε : ℂ) : ℂ :=
  setDNumI14 (4 - 2 * ε) / setDDenI14 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₁₅` (Kira master `lbl[0,0,0,1,1,1,1,0,0]`),
in `d`. -/
noncomputable def setDNumI15 (d : ℂ) : ℂ :=
  (540 * d ^ (10 : ℕ) - 18108 * d ^ (9 : ℕ) + 267285 * d ^ (8 : ℕ) - 2275786 * d ^ (7 : ℕ)
    + 12285152 * d ^ (6 : ℕ) - 43387794 * d ^ (5 : ℕ) + 99209203 * d ^ (4 : ℕ)
    - 137819608 * d ^ (3 : ℕ) + 95084252 * d ^ (2 : ℕ) - 3774512 * d - 23871744)

/-- Denominator of the set (d) coefficient of `I₁₅`, in `d`. -/
noncomputable def setDDenI15 (d : ℂ) : ℂ :=
  96 * (d - 5) * (d - 1) * (2 * d - 9) * (3 * d - 13) * (3 * d - 11) * (d - 4) ^ (2 : ℕ) *
    (d - 3) ^ (2 : ℕ)

/-- The set (d) coefficient of `I₁₅` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI15 (ε : ℂ) : ℂ :=
  setDNumI15 (4 - 2 * ε) / setDDenI15 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₁₆` (Kira master `lbl[0,1,1,1,0,1,0,0,0]`),
in `d`. -/
noncomputable def setDNumI16 (d : ℂ) : ℂ :=
  -(8 * d ^ (8 : ℕ) - 94 * d ^ (7 : ℕ) - 425 * d ^ (6 : ℕ) + 13590 * d ^ (5 : ℕ)
    - 102705 * d ^ (4 : ℕ) + 396466 * d ^ (3 : ℕ) - 858132 * d ^ (2 : ℕ) + 992028 * d - 477792)

/-- Denominator of the set (d) coefficient of `I₁₆`, in `d`. -/
noncomputable def setDDenI16 (d : ℂ) : ℂ :=
  192 * (d - 5) * (d - 4) * (d - 1) * (2 * d - 9) * (d - 3) ^ (2 : ℕ)

/-- The set (d) coefficient of `I₁₆` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI16 (ε : ℂ) : ℂ :=
  setDNumI16 (4 - 2 * ε) / setDDenI16 (4 - 2 * ε)

/-- Numerator of the set (d) coefficient of `I₁₈` (Kira master `lbl[0,0,0,1,1,1,0,0,0]`),
in `d`. -/
noncomputable def setDNumI18 (d : ℂ) : ℂ :=
  (d - 2) * (1008 * d ^ (11 : ℕ) - 41382 * d ^ (10 : ℕ) + 758351 * d ^ (9 : ℕ)
    - 8182166 * d ^ (8 : ℕ) + 57696074 * d ^ (7 : ℕ) - 278831968 * d ^ (6 : ℕ)
    + 940769413 * d ^ (5 : ℕ) - 2210753348 * d ^ (4 : ℕ) + 3534312922 * d ^ (3 : ℕ)
    - 3643602144 * d ^ (2 : ℕ) + 2164643800 * d - 555148800)

/-- Denominator of the set (d) coefficient of `I₁₈`, in `d`. -/
noncomputable def setDDenI18 (d : ℂ) : ℂ :=
  768 * (d - 5) * (d - 1) * (2 * d - 9) * (3 * d - 13) * (3 * d - 11) * (d - 4) ^ (2 : ℕ) *
    (d - 3) ^ (3 : ℕ)

/-- The set (d) coefficient of `I₁₈` at `d = 4 - 2ε`. -/
noncomputable def setDCoeffI18 (ε : ℂ) : ℂ :=
  setDNumI18 (4 - 2 * ε) / setDDenI18 (4 - 2 * ε)

/-- The common denominator of the coefficients at `d = 4 - 2ε`, without the powers of `ε`
(its factors are `d - 1`, `d - 5`, `d - 2`, `d - 3`, `2d - 9`, `2d - 7`, `3d - 13`, `3d - 11`,
normalized to `1` at `ε = 0`). -/
noncomputable def setDDen (ε : ℂ) : ℂ :=
  (1 - 2 / 3 * ε) * (1 - ε) * (1 - 2 * ε) ^ (3 : ℕ) * (1 + 2 * ε) * (1 - 4 * ε) * (1 + 4 * ε) *
    (1 - 6 * ε) * (1 + 6 * ε)

/-- The numerator of the coefficient of `I₂` over `ε ^ 1 · setDDen ε`. -/
noncomputable def setDAI2 (ε : ℂ) : ℂ :=
  setDNumI2 (4 - 2 * ε) * ((1 - ε) * (1 - 2 * ε) ^ (2 : ℕ) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 *
    ε)) / (-24)

/-- The numerator of the coefficient of `I₃` over `ε ^ 0 · setDDen ε`. -/
noncomputable def setDAI3 (ε : ℂ) : ℂ :=
  setDNumI3 (4 - 2 * ε) * ((1 - 2 * ε) ^ (3 : ℕ) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) / 24

/-- The numerator of the coefficient of `I₅` over `ε ^ 1 · setDDen ε`. -/
noncomputable def setDAI5 (ε : ℂ) : ℂ :=
  setDNumI5 (4 - 2 * ε) * ((1 - 2 * ε) ^ (2 : ℕ) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) / (-96)

/-- The numerator of the coefficient of `I₈` over `ε ^ 2 · setDDen ε`. -/
noncomputable def setDAI8 (ε : ℂ) : ℂ :=
  setDNumI8 (4 - 2 * ε) * ((1 - 2 * ε) ^ (3 : ℕ) * (1 - 4 * ε) * (1 + 4 * ε)) / 576

/-- The numerator of the coefficient of `I₉` over `ε ^ 1 · setDDen ε`. -/
noncomputable def setDAI9 (ε : ℂ) : ℂ :=
  setDNumI9 (4 - 2 * ε) * ((1 - 2 * ε) ^ (3 : ℕ) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) / (-96)

/-- The numerator of the coefficient of `I₁₂` over `ε ^ 2 · setDDen ε`. -/
noncomputable def setDAI12 (ε : ℂ) : ℂ :=
  setDNumI12 (4 - 2 * ε) * ((1 - ε) * (1 - 2 * ε) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) / 4608

/-- The numerator of the coefficient of `I₁₃` over `ε ^ 2 · setDDen ε`. -/
noncomputable def setDAI13 (ε : ℂ) : ℂ :=
  setDNumI13 (4 - 2 * ε) * ((1 - ε) * (1 - 2 * ε) * (1 - 4 * ε)) / (-9216)

/-- The numerator of the coefficient of `I₁₄` over `ε ^ 2 · setDDen ε`. -/
noncomputable def setDAI14 (ε : ℂ) : ℂ :=
  setDNumI14 (4 - 2 * ε) * ((1 - ε) * (1 - 2 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) / 2304

/-- The numerator of the coefficient of `I₁₅` over `ε ^ 2 · setDDen ε`. -/
noncomputable def setDAI15 (ε : ℂ) : ℂ :=
  setDNumI15 (4 - 2 * ε) * ((1 - ε) * (1 - 2 * ε) * (1 - 4 * ε)) / (-1152)

/-- The numerator of the coefficient of `I₁₆` over `ε ^ 1 · setDDen ε`. -/
noncomputable def setDAI16 (ε : ℂ) : ℂ :=
  setDNumI16 (4 - 2 * ε) * ((1 - ε) * (1 - 2 * ε) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 *
    ε)) / (-1152)

/-- The numerator of the coefficient of `I₁₈` over `ε ^ 2 · setDDen ε`. -/
noncomputable def setDAI18 (ε : ℂ) : ℂ :=
  setDNumI18 (4 - 2 * ε) * ((1 - ε) * (1 - 4 * ε)) / (-9216)

theorem setDCoeffI2_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI2 ε = setDAI2 ε / (ε ^ (1 : ℕ) * setDDen ε) := by
  have key : setDDenI2 (4 - 2 * ε) *
      ((1 - ε) * (1 - 2 * ε) ^ (2 : ℕ) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) =
      (-24) * (ε ^ (1 : ℕ) * setDDen ε) := by
    simp only [setDDenI2, setDDen]; ring
  have hr : ε ^ (1 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI2 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI2, setDAI2, div_eq_div_iff hden hr]
  linear_combination (-setDNumI2 (4 - 2 * ε) / (-24)) * key

theorem setDCoeffI3_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI3 ε = setDAI3 ε / (ε ^ (0 : ℕ) * setDDen ε) := by
  have key : setDDenI3 (4 - 2 * ε) *
      ((1 - 2 * ε) ^ (3 : ℕ) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) =
      24 * (ε ^ (0 : ℕ) * setDDen ε) := by
    simp only [setDDenI3, setDDen]; ring
  have hr : ε ^ (0 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI3 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI3, setDAI3, div_eq_div_iff hden hr]
  linear_combination (-setDNumI3 (4 - 2 * ε) / 24) * key

theorem setDCoeffI5_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI5 ε = setDAI5 ε / (ε ^ (1 : ℕ) * setDDen ε) := by
  have key : setDDenI5 (4 - 2 * ε) *
      ((1 - 2 * ε) ^ (2 : ℕ) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) =
      (-96) * (ε ^ (1 : ℕ) * setDDen ε) := by
    simp only [setDDenI5, setDDen]; ring
  have hr : ε ^ (1 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI5 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI5, setDAI5, div_eq_div_iff hden hr]
  linear_combination (-setDNumI5 (4 - 2 * ε) / (-96)) * key

theorem setDCoeffI8_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI8 ε = setDAI8 ε / (ε ^ (2 : ℕ) * setDDen ε) := by
  have key : setDDenI8 (4 - 2 * ε) *
      ((1 - 2 * ε) ^ (3 : ℕ) * (1 - 4 * ε) * (1 + 4 * ε)) =
      576 * (ε ^ (2 : ℕ) * setDDen ε) := by
    simp only [setDDenI8, setDDen]; ring
  have hr : ε ^ (2 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI8 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI8, setDAI8, div_eq_div_iff hden hr]
  linear_combination (-setDNumI8 (4 - 2 * ε) / 576) * key

theorem setDCoeffI9_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI9 ε = setDAI9 ε / (ε ^ (1 : ℕ) * setDDen ε) := by
  have key : setDDenI9 (4 - 2 * ε) *
      ((1 - 2 * ε) ^ (3 : ℕ) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) =
      (-96) * (ε ^ (1 : ℕ) * setDDen ε) := by
    simp only [setDDenI9, setDDen]; ring
  have hr : ε ^ (1 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI9 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI9, setDAI9, div_eq_div_iff hden hr]
  linear_combination (-setDNumI9 (4 - 2 * ε) / (-96)) * key

theorem setDCoeffI12_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI12 ε = setDAI12 ε / (ε ^ (2 : ℕ) * setDDen ε) := by
  have key : setDDenI12 (4 - 2 * ε) *
      ((1 - ε) * (1 - 2 * ε) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) =
      4608 * (ε ^ (2 : ℕ) * setDDen ε) := by
    simp only [setDDenI12, setDDen]; ring
  have hr : ε ^ (2 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI12 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI12, setDAI12, div_eq_div_iff hden hr]
  linear_combination (-setDNumI12 (4 - 2 * ε) / 4608) * key

theorem setDCoeffI13_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI13 ε = setDAI13 ε / (ε ^ (2 : ℕ) * setDDen ε) := by
  have key : setDDenI13 (4 - 2 * ε) *
      ((1 - ε) * (1 - 2 * ε) * (1 - 4 * ε)) =
      (-9216) * (ε ^ (2 : ℕ) * setDDen ε) := by
    simp only [setDDenI13, setDDen]; ring
  have hr : ε ^ (2 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI13 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI13, setDAI13, div_eq_div_iff hden hr]
  linear_combination (-setDNumI13 (4 - 2 * ε) / (-9216)) * key

theorem setDCoeffI14_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI14 ε = setDAI14 ε / (ε ^ (2 : ℕ) * setDDen ε) := by
  have key : setDDenI14 (4 - 2 * ε) *
      ((1 - ε) * (1 - 2 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) =
      2304 * (ε ^ (2 : ℕ) * setDDen ε) := by
    simp only [setDDenI14, setDDen]; ring
  have hr : ε ^ (2 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI14 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI14, setDAI14, div_eq_div_iff hden hr]
  linear_combination (-setDNumI14 (4 - 2 * ε) / 2304) * key

theorem setDCoeffI15_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI15 ε = setDAI15 ε / (ε ^ (2 : ℕ) * setDDen ε) := by
  have key : setDDenI15 (4 - 2 * ε) *
      ((1 - ε) * (1 - 2 * ε) * (1 - 4 * ε)) =
      (-1152) * (ε ^ (2 : ℕ) * setDDen ε) := by
    simp only [setDDenI15, setDDen]; ring
  have hr : ε ^ (2 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI15 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI15, setDAI15, div_eq_div_iff hden hr]
  linear_combination (-setDNumI15 (4 - 2 * ε) / (-1152)) * key

theorem setDCoeffI16_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI16 ε = setDAI16 ε / (ε ^ (1 : ℕ) * setDDen ε) := by
  have key : setDDenI16 (4 - 2 * ε) *
      ((1 - ε) * (1 - 2 * ε) * (1 - 4 * ε) * (1 - 6 * ε) * (1 + 6 * ε)) =
      (-1152) * (ε ^ (1 : ℕ) * setDDen ε) := by
    simp only [setDDenI16, setDDen]; ring
  have hr : ε ^ (1 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI16 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI16, setDAI16, div_eq_div_iff hden hr]
  linear_combination (-setDNumI16 (4 - 2 * ε) / (-1152)) * key

theorem setDCoeffI18_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDCoeffI18 ε = setDAI18 ε / (ε ^ (2 : ℕ) * setDDen ε) := by
  have key : setDDenI18 (4 - 2 * ε) *
      ((1 - ε) * (1 - 4 * ε)) =
      (-9216) * (ε ^ (2 : ℕ) * setDDen ε) := by
    simp only [setDDenI18, setDDen]; ring
  have hr : ε ^ (2 : ℕ) * setDDen ε ≠ 0 := mul_ne_zero (pow_ne_zero _ hε) hq
  have hden : setDDenI18 (4 - 2 * ε) ≠ 0 :=
    left_ne_zero_of_mul (by rw [key]; exact mul_ne_zero (by norm_num) hr)
  rw [setDCoeffI18, setDAI18, div_eq_div_iff hden hr]
  linear_combination (-setDNumI18 (4 - 2 * ε) / (-9216)) * key

end QED.ThreeLoopD
