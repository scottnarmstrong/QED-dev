/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDCertFullTarget1
public import QED.Algebra.IBPCertPoly
public import QED.ThreeLoopD.SetDMastersCoeffs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The set (d) reduction: the coefficients against `SetDMastersCoeffs`

For each master `Mⱼ` with index vector `ν`, the certified Euclidean coefficient `nⱼ / q` of the
full reduction equals `(-1) ^ (Σ ν) · (-512 (d - 1)(d - 2)) · setDNumIⱼ d / setDDenIⱼ d`: the
sign `(-1) ^ (Σ ν)` converts the Euclidean masters to the Minkowski ones of the survey, and
`-512 (d - 1)(d - 2) = 64 · N(d)` removes its normalization `1 / (64 N(d))`,
`N(d) = -8 (d - 1)(d - 2)`. `coeff_match_Iⱼ` states the cross-multiplied identity for every
`d`, `coeff_eq_Iⱼ` the quotient form at `d = 4 - 2ε`.
-/

@[expose] public section

namespace QED.ThreeLoopD.SetDCertFull

open QED.Algebra.IBPCert QED.ThreeLoopD

/-- The certified coefficient of `I₂` against `setDNumI2` and `setDDenI2`. -/
theorem coeff_match_I2 (d : ℂ) :
    Poly.eval d sdM2.2 * setDDenI2 d =
      -512 * (d - 1) * (d - 2) * setDNumI2 d * Poly.eval d sdDen := by
  simp only [sdM2, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI2, setDNumI2,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₂` is the survey coefficient `setDCoeffI2`, up to sign and
normalization. -/
theorem coeff_eq_I2 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI2 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM2.2 / Poly.eval (4 - 2 * ε) sdDen =
      (-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI2 ε := by
  have h := coeff_match_I2 (4 - 2 * ε)
  rw [setDCoeffI2, div_eq_iff hq]
  field_simp
  linear_combination h

/-- The certified coefficient of `I₃` against `setDNumI3` and `setDDenI3`. -/
theorem coeff_match_I3 (d : ℂ) :
    Poly.eval d sdM3.2 * setDDenI3 d =
      -512 * (d - 1) * (d - 2) * setDNumI3 d * Poly.eval d sdDen := by
  simp only [sdM3, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI3, setDNumI3,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₃` is the survey coefficient `setDCoeffI3`, up to sign and
normalization. -/
theorem coeff_eq_I3 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI3 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM3.2 / Poly.eval (4 - 2 * ε) sdDen =
      (-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI3 ε := by
  have h := coeff_match_I3 (4 - 2 * ε)
  rw [setDCoeffI3, div_eq_iff hq]
  field_simp
  linear_combination h

/-- The certified coefficient of `I₅` against `setDNumI5` and `setDDenI5`. -/
theorem coeff_match_I5 (d : ℂ) :
    Poly.eval d sdM5.2 * setDDenI5 d =
      -512 * (d - 1) * (d - 2) * setDNumI5 d * Poly.eval d sdDen := by
  simp only [sdM5, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI5, setDNumI5,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₅` is the survey coefficient `setDCoeffI5`, up to sign and
normalization. -/
theorem coeff_eq_I5 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI5 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM5.2 / Poly.eval (4 - 2 * ε) sdDen =
      (-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI5 ε := by
  have h := coeff_match_I5 (4 - 2 * ε)
  rw [setDCoeffI5, div_eq_iff hq]
  field_simp
  linear_combination h

/-- The certified coefficient of `I₈` against `setDNumI8` and `setDDenI8`. -/
theorem coeff_match_I8 (d : ℂ) :
    -Poly.eval d sdM8.2 * setDDenI8 d =
      -512 * (d - 1) * (d - 2) * setDNumI8 d * Poly.eval d sdDen := by
  simp only [sdM8, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI8, setDNumI8,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₈` is the survey coefficient `setDCoeffI8`, up to sign and
normalization. -/
theorem coeff_eq_I8 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI8 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM8.2 / Poly.eval (4 - 2 * ε) sdDen =
      -(-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI8 ε := by
  have h := coeff_match_I8 (4 - 2 * ε)
  rw [setDCoeffI8, div_eq_iff hq]
  field_simp
  linear_combination -h

/-- The certified coefficient of `I₉` against `setDNumI9` and `setDDenI9`. -/
theorem coeff_match_I9 (d : ℂ) :
    -Poly.eval d sdM9.2 * setDDenI9 d =
      -512 * (d - 1) * (d - 2) * setDNumI9 d * Poly.eval d sdDen := by
  simp only [sdM9, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI9, setDNumI9,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₉` is the survey coefficient `setDCoeffI9`, up to sign and
normalization. -/
theorem coeff_eq_I9 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI9 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM9.2 / Poly.eval (4 - 2 * ε) sdDen =
      -(-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI9 ε := by
  have h := coeff_match_I9 (4 - 2 * ε)
  rw [setDCoeffI9, div_eq_iff hq]
  field_simp
  linear_combination -h

/-- The certified coefficient of `I₁₂` against `setDNumI12` and `setDDenI12`. -/
theorem coeff_match_I12 (d : ℂ) :
    Poly.eval d sdM12.2 * setDDenI12 d =
      -512 * (d - 1) * (d - 2) * setDNumI12 d * Poly.eval d sdDen := by
  simp only [sdM12, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI12, setDNumI12,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₁₂` is the survey coefficient `setDCoeffI12`, up to sign and
normalization. -/
theorem coeff_eq_I12 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI12 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM12.2 / Poly.eval (4 - 2 * ε) sdDen =
      (-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI12 ε := by
  have h := coeff_match_I12 (4 - 2 * ε)
  rw [setDCoeffI12, div_eq_iff hq]
  field_simp
  linear_combination h

/-- The certified coefficient of `I₁₃` against `setDNumI13` and `setDDenI13`. -/
theorem coeff_match_I13 (d : ℂ) :
    Poly.eval d sdM13.2 * setDDenI13 d =
      -512 * (d - 1) * (d - 2) * setDNumI13 d * Poly.eval d sdDen := by
  simp only [sdM13, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI13, setDNumI13,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₁₃` is the survey coefficient `setDCoeffI13`, up to sign and
normalization. -/
theorem coeff_eq_I13 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI13 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM13.2 / Poly.eval (4 - 2 * ε) sdDen =
      (-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI13 ε := by
  have h := coeff_match_I13 (4 - 2 * ε)
  rw [setDCoeffI13, div_eq_iff hq]
  field_simp
  linear_combination h

/-- The certified coefficient of `I₁₄` against `setDNumI14` and `setDDenI14`. -/
theorem coeff_match_I14 (d : ℂ) :
    Poly.eval d sdM14.2 * setDDenI14 d =
      -512 * (d - 1) * (d - 2) * setDNumI14 d * Poly.eval d sdDen := by
  simp only [sdM14, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI14, setDNumI14,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₁₄` is the survey coefficient `setDCoeffI14`, up to sign and
normalization. -/
theorem coeff_eq_I14 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI14 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM14.2 / Poly.eval (4 - 2 * ε) sdDen =
      (-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI14 ε := by
  have h := coeff_match_I14 (4 - 2 * ε)
  rw [setDCoeffI14, div_eq_iff hq]
  field_simp
  linear_combination h

/-- The certified coefficient of `I₁₅` against `setDNumI15` and `setDDenI15`. -/
theorem coeff_match_I15 (d : ℂ) :
    Poly.eval d sdM15.2 * setDDenI15 d =
      -512 * (d - 1) * (d - 2) * setDNumI15 d * Poly.eval d sdDen := by
  simp only [sdM15, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI15, setDNumI15,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₁₅` is the survey coefficient `setDCoeffI15`, up to sign and
normalization. -/
theorem coeff_eq_I15 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI15 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM15.2 / Poly.eval (4 - 2 * ε) sdDen =
      (-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI15 ε := by
  have h := coeff_match_I15 (4 - 2 * ε)
  rw [setDCoeffI15, div_eq_iff hq]
  field_simp
  linear_combination h

/-- The certified coefficient of `I₁₆` against `setDNumI16` and `setDDenI16`. -/
theorem coeff_match_I16 (d : ℂ) :
    Poly.eval d sdM16.2 * setDDenI16 d =
      -512 * (d - 1) * (d - 2) * setDNumI16 d * Poly.eval d sdDen := by
  simp only [sdM16, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI16, setDNumI16,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₁₆` is the survey coefficient `setDCoeffI16`, up to sign and
normalization. -/
theorem coeff_eq_I16 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI16 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM16.2 / Poly.eval (4 - 2 * ε) sdDen =
      (-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI16 ε := by
  have h := coeff_match_I16 (4 - 2 * ε)
  rw [setDCoeffI16, div_eq_iff hq]
  field_simp
  linear_combination h

/-- The certified coefficient of `I₁₈` against `setDNumI18` and `setDDenI18`. -/
theorem coeff_match_I18 (d : ℂ) :
    -Poly.eval d sdM18.2 * setDDenI18 d =
      -512 * (d - 1) * (d - 2) * setDNumI18 d * Poly.eval d sdDen := by
  simp only [sdM18, sdDen, Poly.eval_cons, Poly.eval_nil, setDDenI18, setDNumI18,
    Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_negSucc]
  push_cast
  ring

/-- The certified coefficient of `I₁₈` is the survey coefficient `setDCoeffI18`, up to sign and
normalization. -/
theorem coeff_eq_I18 (ε : ℂ) (hq : Poly.eval (4 - 2 * ε) sdDen ≠ 0)
    (hD : setDDenI18 (4 - 2 * ε) ≠ 0) :
    Poly.eval (4 - 2 * ε) sdM18.2 / Poly.eval (4 - 2 * ε) sdDen =
      -(-512 * (3 - 2 * ε) * (2 - 2 * ε)) * setDCoeffI18 ε := by
  have h := coeff_match_I18 (4 - 2 * ε)
  rw [setDCoeffI18, div_eq_iff hq]
  field_simp
  linear_combination -h

end QED.ThreeLoopD.SetDCertFull
