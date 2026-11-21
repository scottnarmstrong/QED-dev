/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLDuality
public import QED.Polylog.HPLLi
public import QED.Polylog.MZVHPL
import QED.Polylog.LiCalculus
import QED.Polylog.HPLValues

/-!
# Harmonic polylogarithms at `1`: the words of weight four over `{0, 1}`

The classical multiple zeta values of weight four, obtained algebraically from the double
shuffle relations (`QED.Polylog.HPL.hpl_one_mul_hpl_one`,
`QED.Polylog.MZV.hpl_one_mul_hpl_one_stuffle`), duality
(`QED.Polylog.HPL.hpl_one_eq_hpl_one_dualWord`) and `ζ(4) = π⁴/90`:

| word | MZV | `H(w; 1)` | word | `H(w; 1)` |
|---|---|---|---|---|
| `0001` | `ζ(4)` | `π⁴/90` | `0010` | `-π⁴/30` |
| `0011` | `ζ(3, 1)` | `π⁴/360` | `0100` | `π⁴/30` |
| `0101` | `ζ(2, 2)` | `π⁴/120` | `0110` | `-π⁴/72` |
| `0111` | `ζ(2, 1, 1)` | `π⁴/90` | `0000` | `0` |

The words with a trailing zero follow from the shuffle with `H(0; 1) = 0`.
-/

@[expose] public section

open Real

namespace QED.Polylog.HPL

open Letter QED.Polylog.MZV

/-- `H(0001; 1) = ζ(4) = π⁴/90`. -/
theorem hpl_zero_zero_zero_one_at_one : hpl [zero, zero, zero, one] 1 = π ^ 4 / 90 := by
  rw [← Li_four_one]
  exact hpl_replicate_zero_one_at_one (k := 3) (by norm_num)

/-- `H(0111; 1) = ζ(2, 1, 1) = ζ(4)`, by duality. -/
theorem hpl_zero_one_one_one_at_one : hpl [zero, one, one, one] 1 = π ^ 4 / 90 := by
  rw [hpl_one_eq_hpl_one_dualWord (by rfl) (by rfl) (by decide),
    ← hpl_zero_zero_zero_one_at_one]
  rfl

/-- The stuffle `ζ(2)² = 2 ζ(2, 2) + ζ(4)`. -/
theorem stuffle_zero_one_zero_one : hpl [zero, one] 1 * hpl [zero, one] 1 =
    2 * hpl [zero, one, zero, one] 1 + hpl [zero, zero, zero, one] 1 := by
  have h := hpl_one_mul_hpl_one_stuffle (a := zero) (b := zero) (u := [one]) (v := [one])
    (by decide) (by decide) (by decide) (by decide)
  simp [encode, stuffle_cons_cons, decode, letterOfSign, mzvOp, wordSign] at h
  rw [h]
  ring

/-- `H(0101; 1) = ζ(2, 2) = π⁴/120`. -/
theorem hpl_zero_one_zero_one_at_one : hpl [zero, one, zero, one] 1 = π ^ 4 / 120 := by
  have h := stuffle_zero_one_zero_one
  rw [hpl_zero_one_at_one, hpl_zero_zero_zero_one_at_one] at h
  linarith

/-- `H(0011; 1) = ζ(3, 1) = π⁴/360`, from the shuffle `ζ(2)² = 2 ζ(2, 2) + 4 ζ(3, 1)`. -/
theorem hpl_zero_zero_one_one_at_one : hpl [zero, zero, one, one] 1 = π ^ 4 / 360 := by
  have h := hpl_one_mul_hpl_one (u := [zero, one]) (v := [zero, one]) (by decide) (by decide)
  simp [shuffle_cons_cons] at h
  rw [hpl_zero_one_at_one, hpl_zero_one_zero_one_at_one] at h
  linarith

/-- `H(0000; 1) = 0`. -/
theorem hpl_zero_zero_zero_zero_at_one : hpl [zero, zero, zero, zero] 1 = 0 := by
  rw [hpl_of_allZero (by decide)]
  simp

/-- `H(0010; 1) = -π⁴/30`, from `H(0) H(001) = 0` at `1`. -/
theorem hpl_zero_zero_one_zero_at_one : hpl [zero, zero, one, zero] 1 = -π ^ 4 / 30 := by
  have h := hpl_one_mul_hpl_one (u := [zero]) (v := [zero, zero, one]) (by decide) (by decide)
  simp [shuffle_cons_cons, hpl_zero_at_one] at h
  rw [hpl_zero_zero_zero_one_at_one] at h
  linarith

/-- `H(0110; 1) = -π⁴/72`, from `H(0) H(011) = 0` at `1`. -/
theorem hpl_zero_one_one_zero_at_one : hpl [zero, one, one, zero] 1 = -π ^ 4 / 72 := by
  have h := hpl_one_mul_hpl_one (u := [zero]) (v := [zero, one, one]) (by decide) (by decide)
  simp [shuffle_cons_cons, hpl_zero_at_one] at h
  rw [hpl_zero_zero_one_one_at_one, hpl_zero_one_zero_one_at_one] at h
  linarith

/-- `H(0100; 1) = π⁴/30`, from `H(0) H(010) = 0` at `1`. -/
theorem hpl_zero_one_zero_zero_at_one : hpl [zero, one, zero, zero] 1 = π ^ 4 / 30 := by
  have h := hpl_one_mul_hpl_one (u := [zero]) (v := [zero, one, zero]) (by decide) (by decide)
  simp [shuffle_cons_cons, hpl_zero_at_one] at h
  rw [hpl_zero_zero_one_zero_at_one] at h
  linarith

end QED.Polylog.HPL
