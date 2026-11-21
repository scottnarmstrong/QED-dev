/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLValues4
public import QED.Polylog.Zeta5
import QED.Polylog.HPLValues

/-!
# Harmonic polylogarithms at `1`: the convergent words of weight five over `{0, 1}`

The classical multiple zeta values of weight five, in the basis `ζ(5) = zeta5`, `π² ζ(3)`,
obtained algebraically: the double shuffle relations of `ζ(2) ζ(3)` and `ζ(2) ζ(2, 1)`
(`QED.Polylog.HPL.hpl_one_mul_hpl_one`, `QED.Polylog.MZV.hpl_one_mul_hpl_one_stuffle`) and
duality (`QED.Polylog.HPL.hpl_one_eq_hpl_one_dualWord`). In particular Euler's
`ζ(4, 1) = 2 ζ(5) - ζ(2) ζ(3)`.

| word | MZV | `H(w; 1)` |
|---|---|---|
| `00001`, `01111` | `ζ(5)`, `ζ(2, 1, 1, 1)` | `ζ(5)` |
| `00011`, `00111` | `ζ(4, 1)`, `ζ(3, 1, 1)` | `2 ζ(5) - π² ζ(3)/6` |
| `00101`, `01011` | `ζ(3, 2)`, `ζ(2, 2, 1)` | `π² ζ(3)/2 - 11 ζ(5)/2` |
| `01001`, `01101` | `ζ(2, 3)`, `ζ(2, 1, 2)` | `9 ζ(5)/2 - π² ζ(3)/3` |
-/

@[expose] public section

open Real

namespace QED.Polylog.HPL

open Letter QED.Polylog.MZV

/-- `H(00001; 1) = ζ(5)`. -/
theorem hpl_zero_zero_zero_zero_one_at_one : hpl [zero, zero, zero, zero, one] 1 = zeta5 := by
  rw [← Li_five_one]
  exact hpl_replicate_zero_one_at_one (k := 4) (by norm_num)

/-- `H(01111; 1) = ζ(2, 1, 1, 1) = ζ(5)`, by duality. -/
theorem hpl_zero_one_one_one_one_at_one : hpl [zero, one, one, one, one] 1 = zeta5 := by
  rw [← hpl_zero_zero_zero_zero_one_at_one]
  exact hpl_one_eq_hpl_one_dualWord (by rfl) (by rfl) (by decide)

/-- The double shuffle relations of weight five over `{0, 1}`, reduced by duality: the values
`ζ(4, 1)`, `ζ(3, 2)`, `ζ(2, 3)`. -/
theorem weight_five_values :
    hpl [zero, zero, zero, one, one] 1 = 2 * zeta5 - π ^ 2 * zeta3 / 6 ∧
      hpl [zero, zero, one, zero, one] 1 = π ^ 2 * zeta3 / 2 - 11 / 2 * zeta5 ∧
      hpl [zero, one, zero, zero, one] 1 = 9 / 2 * zeta5 - π ^ 2 * zeta3 / 3 := by
  have s1 := hpl_one_mul_hpl_one (u := [zero, one]) (v := [zero, zero, one]) (by decide)
    (by decide)
  have s2 := hpl_one_mul_hpl_one_stuffle (a := zero) (b := zero) (u := [one])
    (v := [zero, one]) (by decide) (by decide) (by decide) (by decide)
  have s3 := hpl_one_mul_hpl_one (u := [zero, one]) (v := [zero, one, one]) (by decide)
    (by decide)
  have s4 := hpl_one_mul_hpl_one_stuffle (a := zero) (b := zero) (u := [one])
    (v := [one, one]) (by decide) (by decide) (by decide) (by decide)
  simp [shuffle_cons_cons] at s1 s3
  simp [encode, stuffle_cons_cons, decode, letterOfSign, mzvOp, wordSign] at s2 s4
  have d1 : hpl [zero, zero, one, one, one] 1 = hpl [zero, zero, zero, one, one] 1 :=
    hpl_one_eq_hpl_one_dualWord (by rfl) (by rfl) (by decide)
  have d2 : hpl [zero, one, zero, one, one] 1 = hpl [zero, zero, one, zero, one] 1 :=
    hpl_one_eq_hpl_one_dualWord (by rfl) (by rfl) (by decide)
  have d3 : hpl [zero, one, one, zero, one] 1 = hpl [zero, one, zero, zero, one] 1 :=
    hpl_one_eq_hpl_one_dualWord (by rfl) (by rfl) (by decide)
  rw [hpl_zero_one_at_one, hpl_zero_zero_one_at_one] at s1 s2
  rw [hpl_zero_one_at_one, hpl_zero_one_one_at_one] at s3 s4
  simp only [d1, d2, d3, hpl_zero_zero_zero_zero_one_at_one] at s1 s2 s3 s4
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Euler: `H(00011; 1) = ζ(4, 1) = 2 ζ(5) - ζ(2) ζ(3)`. -/
theorem hpl_zero_zero_zero_one_one_at_one :
    hpl [zero, zero, zero, one, one] 1 = 2 * zeta5 - π ^ 2 * zeta3 / 6 :=
  weight_five_values.1

/-- `H(00101; 1) = ζ(3, 2) = 3 ζ(2) ζ(3) - 11 ζ(5)/2`. -/
theorem hpl_zero_zero_one_zero_one_at_one :
    hpl [zero, zero, one, zero, one] 1 = π ^ 2 * zeta3 / 2 - 11 / 2 * zeta5 :=
  weight_five_values.2.1

/-- `H(01001; 1) = ζ(2, 3) = 9 ζ(5)/2 - 2 ζ(2) ζ(3)`. -/
theorem hpl_zero_one_zero_zero_one_at_one :
    hpl [zero, one, zero, zero, one] 1 = 9 / 2 * zeta5 - π ^ 2 * zeta3 / 3 :=
  weight_five_values.2.2

/-- `H(00111; 1) = ζ(3, 1, 1) = ζ(4, 1)`. -/
theorem hpl_zero_zero_one_one_one_at_one :
    hpl [zero, zero, one, one, one] 1 = 2 * zeta5 - π ^ 2 * zeta3 / 6 := by
  rw [← hpl_zero_zero_zero_one_one_at_one]
  exact hpl_one_eq_hpl_one_dualWord (by rfl) (by rfl) (by decide)

/-- `H(01011; 1) = ζ(2, 2, 1) = ζ(3, 2)`. -/
theorem hpl_zero_one_zero_one_one_at_one :
    hpl [zero, one, zero, one, one] 1 = π ^ 2 * zeta3 / 2 - 11 / 2 * zeta5 := by
  rw [← hpl_zero_zero_one_zero_one_at_one]
  exact hpl_one_eq_hpl_one_dualWord (by rfl) (by rfl) (by decide)

/-- `H(01101; 1) = ζ(2, 1, 2) = ζ(2, 3)`. -/
theorem hpl_zero_one_one_zero_one_at_one :
    hpl [zero, one, one, zero, one] 1 = 9 / 2 * zeta5 - π ^ 2 * zeta3 / 3 := by
  rw [← hpl_zero_one_zero_zero_one_at_one]
  exact hpl_one_eq_hpl_one_dualWord (by rfl) (by rfl) (by decide)

end QED.Polylog.HPL
