/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCPF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the branch-2 integrand as partial fractions in `s`

Helper level (no frozen statement). The coefficients of the partial-fraction decomposition in `s`
of the branch-2 integrand `formCF2` (generated in exact arithmetic, scratch `stageK/fcc/g3.py`,
`g9.py`), all over the common denominator `formC2L = 12 X³ (X - 2)(X - 1) P³ Q⁴`
(`P = X² + (1 - X)u`, `Q = X² + 2(1 - X)u`), and

**`formCF2_eq_formCPF`**: `formCF2 X u s = formCPF (formC2k X u) X u s`.

Proof: `formCF2 · 12 s² B C D³` is the polynomial `formC2N` of degree 8 in `s`
(`formCF2_mul_den`); the same holds for the partial-fraction sum with numerator linear in the
coefficients (`formCPF_mul_den`); the two numerators agree power by power in `s` (`formC2_cfj`,
each from a pure polynomial identity `formC2_pcj` in `(X, u)`).
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

/-- `Q = X² + 2(1 - X)u`, the value of `D` at `s = 0`. -/
def formCQ (X u : ℝ) : ℝ := X ^ 2 + 2 * (1 - X) * u

/-- The common denominator `12 X³ (X - 2)(X - 1) P³ Q⁴` of the coefficients. -/
def formC2L (X u : ℝ) : ℝ := 12 * (X - 2) * (X - 1) * X ^ 3 * formCP X u ^ 3 * formCQ X u ^ 4

/-- Numerator of the branch-2 coefficient `q0` over `formC2L`. -/
def formC2Nq0 (X u : ℝ) : ℝ :=
  (-(X - 1) * (3 * X ^ 6 * u - 9 * X ^ 6 + 3 * X ^ 5 * u ^ 2 + 2 * X ^ 5 * u - 12 * X ^ 4 * u ^
      3 + 8 * X ^ 4 * u ^ 2 - 2 * X ^ 4 * u + 6 * X ^ 3 * u ^ 4 + 18 * X ^ 3 * u ^ 3 - 22 * X ^ 3 *
      u ^ 2 - 18 * X ^ 2 * u ^ 4 + 6 * X ^ 2 * u ^ 3 + 11 * X ^ 2 * u ^ 2 + 18 * X * u ^ 4 - 18 * X
      * u ^ 3 - 6 * u ^ 4 + 6 * u ^ 3)) *
    ((X - 2) * (X - 1) * X * formCQ X u ^ 4)

/-- Numerator of the branch-2 coefficient `q1` over `formC2L`. -/
def formC2Nq1 (X u : ℝ) : ℝ :=
  (u * (X - 1) ^ 2 * (-4 * X ^ 2 + 3 * X * u - 3 * u)) *
    (2 * (X - 2) * (X - 1) * X * formCP X u * formCQ X u ^ 4)

/-- Numerator of the branch-2 coefficient `r1` over `formC2L`. -/
def formC2Nr1 (X u : ℝ) : ℝ :=
  (-(X - 1) * (3 * X ^ 6 * u ^ 2 + 3 * X ^ 6 - 30 * X ^ 5 * u ^ 2 - 12 * X ^ 5 * u - 5 * X ^ 4 *
      u ^ 4 + 32 * X ^ 4 * u ^ 3 + 94 * X ^ 4 * u ^ 2 + 12 * X ^ 4 * u + 4 * X ^ 3 * u ^ 5 - 6 * X ^
      3 * u ^ 4 - 96 * X ^ 3 * u ^ 3 - 128 * X ^ 3 * u ^ 2 - 12 * X ^ 2 * u ^ 5 + 43 * X ^ 2 * u ^ 4
      + 128 * X ^ 2 * u ^ 3 + 64 * X ^ 2 * u ^ 2 + 12 * X * u ^ 5 - 48 * X * u ^ 4 - 96 * X * u ^ 3
      - 4 * u ^ 5 + 16 * u ^ 4 + 32 * u ^ 3)) *
    ((X - 2) * (X - 1) * X ^ 3 * formCP X u ^ 3)

/-- Numerator of the branch-2 coefficient `r2` over `formC2L`. -/
def formC2Nr2 (X u : ℝ) : ℝ :=
  (-(-X + u) ^ 2 * (X - 1) * (X * u - X - u) ^ 2) *
    (6 * (X - 2) * (X - 1) * X ^ 3 * formCQ X u * formCP X u ^ 3)

/-- Numerator of the branch-2 coefficient `b` over `formC2L`. -/
def formC2Nb (X u : ℝ) : ℝ :=
  (-(X - 1) ^ 2 * (-X ^ 4 - 4 * X ^ 3 * u + 2 * X ^ 3 + 8 * X ^ 2 * u + 6 * X * u ^ 2 - 6 * u ^
      2)) *
    ((X - 1) * formCP X u ^ 3 * formCQ X u ^ 4)

/-- Numerator of the branch-2 coefficient `c` over `formC2L`. -/
def formC2Nc (X u : ℝ) : ℝ :=
  (-4 * X ^ 4 * u - X ^ 4 - 6 * X ^ 3 * u ^ 2 + 12 * X ^ 3 * u + 2 * X ^ 3 + 18 * X ^ 2 * u ^ 2
      - 8 * X ^ 2 * u - 18 * X * u ^ 2 + 6 * u ^ 2) *
    (formCP X u ^ 3 * formCQ X u ^ 4)

/-- Numerator of the branch-2 coefficient `d1` over `formC2L`. -/
def formC2Nd1 (X u : ℝ) : ℝ :=
  (X ^ 16 - 7 * X ^ 15 * u - 3 * X ^ 15 + 7 * X ^ 14 * u ^ 2 + 32 * X ^ 14 * u + 3 * X ^ 14 + 55
      * X ^ 13 * u ^ 3 - 64 * X ^ 13 * u ^ 2 - 58 * X ^ 13 * u - 214 * X ^ 12 * u ^ 4 - 167 * X ^ 12
      * u ^ 3 + 162 * X ^ 12 * u ^ 2 + 49 * X ^ 12 * u + 352 * X ^ 11 * u ^ 5 + 978 * X ^ 11 * u ^ 4
      + 204 * X ^ 11 * u ^ 3 - 170 * X ^ 11 * u ^ 2 - 24 * X ^ 11 * u - 309 * X ^ 10 * u ^ 6 - 1918
      * X ^ 10 * u ^ 5 - 1938 * X ^ 10 * u ^ 4 - 222 * X ^ 10 * u ^ 3 + 80 * X ^ 10 * u ^ 2 + 8 * X
      ^ 10 * u + 143 * X ^ 9 * u ^ 7 + 1934 * X ^ 9 * u ^ 6 + 4484 * X ^ 9 * u ^ 5 + 2340 * X ^ 9 *
      u ^ 4 + 318 * X ^ 9 * u ^ 3 - 20 * X ^ 9 * u ^ 2 - 28 * X ^ 8 * u ^ 8 - 1017 * X ^ 8 * u ^ 7 -
      5195 * X ^ 8 * u ^ 6 - 6002 * X ^ 8 * u ^ 5 - 2094 * X ^ 8 * u ^ 4 - 312 * X ^ 8 * u ^ 3 + 5 *
      X ^ 8 * u ^ 2 + 224 * X ^ 7 * u ^ 8 + 3131 * X ^ 7 * u ^ 7 + 7860 * X ^ 7 * u ^ 6 + 5256 * X ^
      7 * u ^ 5 + 1490 * X ^ 7 * u ^ 4 + 155 * X ^ 7 * u ^ 3 - 784 * X ^ 6 * u ^ 8 - 5453 * X ^ 6 *
      u ^ 7 - 7435 * X ^ 6 * u ^ 6 - 3282 * X ^ 6 * u ^ 5 - 782 * X ^ 6 * u ^ 4 - 31 * X ^ 6 * u ^ 3
      + 1568 * X ^ 5 * u ^ 8 + 5901 * X ^ 5 * u ^ 7 + 4654 * X ^ 5 * u ^ 6 + 1508 * X ^ 5 * u ^ 5 +
      264 * X ^ 5 * u ^ 4 - 1960 * X ^ 4 * u ^ 8 - 4123 * X ^ 4 * u ^ 7 - 1989 * X ^ 4 * u ^ 6 - 494
      * X ^ 4 * u ^ 5 - 44 * X ^ 4 * u ^ 4 + 1568 * X ^ 3 * u ^ 8 + 1897 * X ^ 3 * u ^ 7 + 560 * X ^
      3 * u ^ 6 + 112 * X ^ 3 * u ^ 5 - 784 * X ^ 2 * u ^ 8 - 591 * X ^ 2 * u ^ 7 - 80 * X ^ 2 * u ^
      6 - 16 * X ^ 2 * u ^ 5 + 224 * X * u ^ 8 + 128 * X * u ^ 7 - 28 * u ^ 8 - 16 * u ^ 7) *
    ((X - 2) * X ^ 3 * formCP X u)

/-- Numerator of the branch-2 coefficient `d2` over `formC2L`. -/
def formC2Nd2 (X u : ℝ) : ℝ :=
  (u * (-X + u) * (X - 1) * (X * u - X - u) * (X ^ 12 - 6 * X ^ 11 * u - 2 * X ^ 11 + 23 * X ^
      10 * u ^ 2 + 11 * X ^ 10 * u + 2 * X ^ 10 - 48 * X ^ 9 * u ^ 3 - 58 * X ^ 9 * u ^ 2 - 10 * X ^
      9 * u + 51 * X ^ 8 * u ^ 4 + 159 * X ^ 8 * u ^ 3 + 59 * X ^ 8 * u ^ 2 + 5 * X ^ 8 * u - 27 * X
      ^ 7 * u ^ 5 - 206 * X ^ 7 * u ^ 4 - 204 * X ^ 7 * u ^ 3 - 36 * X ^ 7 * u ^ 2 + 6 * X ^ 6 * u ^
      6 + 135 * X ^ 6 * u ^ 5 + 316 * X ^ 6 * u ^ 4 + 138 * X ^ 6 * u ^ 3 + 12 * X ^ 6 * u ^ 2 - 36
      * X ^ 5 * u ^ 6 - 270 * X ^ 5 * u ^ 5 - 224 * X ^ 5 * u ^ 4 - 60 * X ^ 5 * u ^ 3 + 90 * X ^ 4
      * u ^ 6 + 270 * X ^ 4 * u ^ 5 + 71 * X ^ 4 * u ^ 4 + 15 * X ^ 4 * u ^ 3 - 120 * X ^ 3 * u ^ 6
      - 135 * X ^ 3 * u ^ 5 - 10 * X ^ 3 * u ^ 4 + 90 * X ^ 2 * u ^ 6 + 27 * X ^ 2 * u ^ 5 + 2 * X ^
      2 * u ^ 4 - 36 * X * u ^ 6 + 6 * u ^ 6)) *
    ((X - 2) * (X - 1) * X ^ 3 * formCQ X u)

/-- Numerator of the branch-2 coefficient `d3` over `formC2L`. -/
def formC2Nd3 (X u : ℝ) : ℝ :=
  (-X ^ 2 * u ^ 2 * (-X + u) ^ 2 * (X - 1) ^ 3 * (X * u - X - u) ^ 2 * (X ^ 4 - 2 * X ^ 3 * u +
      3 * X ^ 2 * u ^ 2 + 2 * X ^ 2 * u - 6 * X * u ^ 2 + 3 * u ^ 2)) *
    ((X - 2) * (X - 1) * X ^ 3 * formCQ X u ^ 2)

/-- The branch-2 partial-fraction coefficient `q0`. -/
noncomputable def formC2q0 (X u : ℝ) : ℝ := formC2Nq0 X u / formC2L X u

/-- The branch-2 partial-fraction coefficient `q1`. -/
noncomputable def formC2q1 (X u : ℝ) : ℝ := formC2Nq1 X u / formC2L X u

/-- The branch-2 partial-fraction coefficient `r1`. -/
noncomputable def formC2r1 (X u : ℝ) : ℝ := formC2Nr1 X u / formC2L X u

/-- The branch-2 partial-fraction coefficient `r2`. -/
noncomputable def formC2r2 (X u : ℝ) : ℝ := formC2Nr2 X u / formC2L X u

/-- The branch-2 partial-fraction coefficient `b`. -/
noncomputable def formC2b (X u : ℝ) : ℝ := formC2Nb X u / formC2L X u

/-- The branch-2 partial-fraction coefficient `c`. -/
noncomputable def formC2c (X u : ℝ) : ℝ := formC2Nc X u / formC2L X u

/-- The branch-2 partial-fraction coefficient `d1`. -/
noncomputable def formC2d1 (X u : ℝ) : ℝ := formC2Nd1 X u / formC2L X u

/-- The branch-2 partial-fraction coefficient `d2`. -/
noncomputable def formC2d2 (X u : ℝ) : ℝ := formC2Nd2 X u / formC2L X u

/-- The branch-2 partial-fraction coefficient `d3`. -/
noncomputable def formC2d3 (X u : ℝ) : ℝ := formC2Nd3 X u / formC2L X u

/-- **The branch-2 coefficient vector.** -/
noncomputable def formC2k (X u : ℝ) : FormCPFc :=
  ⟨formC2q0 X u, formC2q1 X u, formC2r1 X u, formC2r2 X u, formC2b X u, formC2c X u,
    formC2d1 X u, formC2d2 X u, formC2d3 X u⟩

/-- Coefficient of `s ^ 0` in the cleared numerator `formC2N`. -/
def formC2n0 (X u : ℝ) : ℝ :=
  6 * (-X + u) ^ 3 * (X - 1) * (X * u - X - u) ^ 3

/-- Coefficient of `s ^ 1` in the cleared numerator `formC2N`. -/
def formC2n1 (X u : ℝ) : ℝ :=
  -(-X + u) * (X - 1) * (X * u - X - u) * (21 * X ^ 4 * u ^ 2 - 54 * X ^ 4 * u + 27 * X ^ 4 - 30
      * X ^ 3 * u ^ 3 + 42 * X ^ 3 * u ^ 2 + 24 * X ^ 3 * u + 11 * X ^ 2 * u ^ 4 + 22 * X ^ 2 * u ^
      3 - 58 * X ^ 2 * u ^ 2 - 24 * X ^ 2 * u - 22 * X * u ^ 4 + 16 * X * u ^ 3 + 32 * X * u ^ 2 +
      11 * u ^ 4 - 8 * u ^ 3 - 16 * u ^ 2)

/-- Coefficient of `s ^ 2` in the cleared numerator `formC2N`. -/
def formC2n2 (X u : ℝ) : ℝ :=
  (X - 1) * (-24 * X ^ 6 * u ^ 3 + 114 * X ^ 6 * u ^ 2 - 132 * X ^ 6 * u + 36 * X ^ 6 + 41 * X ^
      5 * u ^ 4 - 158 * X ^ 5 * u ^ 3 - 4 * X ^ 5 * u ^ 2 + 132 * X ^ 5 * u - 30 * X ^ 4 * u ^ 5 +
      101 * X ^ 4 * u ^ 4 + 158 * X ^ 4 * u ^ 3 - 36 * X ^ 4 * u ^ 2 - 132 * X ^ 4 * u + 16 * X ^ 3
      * u ^ 6 - 44 * X ^ 3 * u ^ 5 - 188 * X ^ 3 * u ^ 4 - 48 * X ^ 3 * u ^ 3 + 80 * X ^ 3 * u ^ 2 -
      48 * X ^ 2 * u ^ 6 + 282 * X ^ 2 * u ^ 5 - 146 * X ^ 2 * u ^ 4 + 144 * X ^ 2 * u ^ 3 - 40 * X
      ^ 2 * u ^ 2 + 48 * X * u ^ 6 - 312 * X * u ^ 5 + 288 * X * u ^ 4 - 144 * X * u ^ 3 - 16 * u ^
      6 + 104 * u ^ 5 - 96 * u ^ 4 + 48 * u ^ 3)

/-- Coefficient of `s ^ 3` in the cleared numerator `formC2N`. -/
def formC2n3 (X u : ℝ) : ℝ :=
  -(X - 1) * (-6 * X ^ 6 * u ^ 3 + 66 * X ^ 6 * u ^ 2 - 75 * X ^ 6 * u - 15 * X ^ 6 - 4 * X ^ 5
      * u ^ 4 - 76 * X ^ 5 * u ^ 3 - 89 * X ^ 5 * u ^ 2 + 280 * X ^ 5 * u - 3 * X ^ 4 * u ^ 5 + 222
      * X ^ 4 * u ^ 4 - 212 * X ^ 4 * u ^ 3 + 145 * X ^ 4 * u ^ 2 - 280 * X ^ 4 * u + 10 * X ^ 3 * u
      ^ 6 - 188 * X ^ 3 * u ^ 5 - 44 * X ^ 3 * u ^ 4 + 360 * X ^ 3 * u ^ 3 - 112 * X ^ 3 * u ^ 2 -
      30 * X ^ 2 * u ^ 6 + 579 * X ^ 2 * u ^ 5 - 958 * X ^ 2 * u ^ 4 + 360 * X ^ 2 * u ^ 3 + 56 * X
      ^ 2 * u ^ 2 + 30 * X * u ^ 6 - 582 * X * u ^ 5 + 1176 * X * u ^ 4 - 648 * X * u ^ 3 - 10 * u ^
      6 + 194 * u ^ 5 - 392 * u ^ 4 + 216 * u ^ 3)

/-- Coefficient of `s ^ 4` in the cleared numerator `formC2N`. -/
def formC2n4 (X u : ℝ) : ℝ :=
  (X - 1) * (6 * X ^ 6 * u ^ 3 - 6 * X ^ 6 * u ^ 2 + 30 * X ^ 6 * u - 90 * X ^ 6 - 17 * X ^ 5 *
      u ^ 4 - 53 * X ^ 5 * u ^ 2 + 274 * X ^ 5 * u + 6 * X ^ 4 * u ^ 5 + 195 * X ^ 4 * u ^ 4 - 576 *
      X ^ 4 * u ^ 3 + 363 * X ^ 4 * u ^ 2 - 274 * X ^ 4 * u + 2 * X ^ 3 * u ^ 6 - 156 * X ^ 3 * u ^
      5 + 164 * X ^ 3 * u ^ 4 + 756 * X ^ 3 * u ^ 3 - 620 * X ^ 3 * u ^ 2 - 6 * X ^ 2 * u ^ 6 + 438
      * X ^ 2 * u ^ 5 - 1382 * X ^ 2 * u ^ 4 + 612 * X ^ 2 * u ^ 3 + 310 * X ^ 2 * u ^ 2 + 6 * X * u
      ^ 6 - 432 * X * u ^ 5 + 1560 * X * u ^ 4 - 1188 * X * u ^ 3 - 2 * u ^ 6 + 144 * u ^ 5 - 520 *
      u ^ 4 + 396 * u ^ 3)

/-- Coefficient of `s ^ 5` in the cleared numerator `formC2N`. -/
def formC2n5 (X u : ℝ) : ℝ :=
  -(X - 1) * (3 * X ^ 6 * u ^ 3 - 21 * X ^ 6 * u ^ 2 + 57 * X ^ 6 * u - 99 * X ^ 6 - 5 * X ^ 5 *
      u ^ 4 + 10 * X ^ 5 * u ^ 3 + 39 * X ^ 5 * u ^ 2 + 94 * X ^ 5 * u + 2 * X ^ 4 * u ^ 5 + 74 * X
      ^ 4 * u ^ 4 - 484 * X ^ 4 * u ^ 3 + 410 * X ^ 4 * u ^ 2 - 94 * X ^ 4 * u - 52 * X ^ 3 * u ^ 5
      + 189 * X ^ 3 * u ^ 4 + 570 * X ^ 3 * u ^ 3 - 898 * X ^ 3 * u ^ 2 + 146 * X ^ 2 * u ^ 5 - 912
      * X ^ 2 * u ^ 4 + 660 * X ^ 2 * u ^ 3 + 449 * X ^ 2 * u ^ 2 - 144 * X * u ^ 5 + 981 * X * u ^
      4 - 1134 * X * u ^ 3 + 48 * u ^ 5 - 327 * u ^ 4 + 378 * u ^ 3)

/-- Coefficient of `s ^ 6` in the cleared numerator `formC2N`. -/
def formC2n6 (X u : ℝ) : ℝ :=
  -(X - 1) * (6 * X ^ 6 * u ^ 2 - 24 * X ^ 6 * u + 48 * X ^ 6 - 2 * X ^ 5 * u ^ 3 - 45 * X ^ 5 *
      u ^ 2 + 38 * X ^ 5 * u - 10 * X ^ 4 * u ^ 4 + 182 * X ^ 4 * u ^ 3 - 265 * X ^ 4 * u ^ 2 - 38 *
      X ^ 4 * u + 6 * X ^ 3 * u ^ 5 - 80 * X ^ 3 * u ^ 4 - 162 * X ^ 3 * u ^ 3 + 620 * X ^ 3 * u ^ 2
      - 18 * X ^ 2 * u ^ 5 + 290 * X ^ 2 * u ^ 4 - 414 * X ^ 2 * u ^ 3 - 310 * X ^ 2 * u ^ 2 + 18 *
      X * u ^ 5 - 300 * X * u ^ 4 + 594 * X * u ^ 3 - 6 * u ^ 5 + 100 * u ^ 4 - 198 * u ^ 3)

/-- Coefficient of `s ^ 7` in the cleared numerator `formC2N`. -/
def formC2n7 (X u : ℝ) : ℝ :=
  -(X - 1) * (3 * X ^ 6 * u - 9 * X ^ 6 + 11 * X ^ 5 * u ^ 2 - 38 * X ^ 5 * u - 26 * X ^ 4 * u ^
      3 + 94 * X ^ 4 * u ^ 2 + 38 * X ^ 4 * u + 12 * X ^ 3 * u ^ 4 - 2 * X ^ 3 * u ^ 3 - 210 * X ^ 3
      * u ^ 2 - 36 * X ^ 2 * u ^ 4 + 136 * X ^ 2 * u ^ 3 + 105 * X ^ 2 * u ^ 2 + 36 * X * u ^ 4 -
      162 * X * u ^ 3 - 12 * u ^ 4 + 54 * u ^ 3)

/-- Coefficient of `s ^ 8` in the cleared numerator `formC2N`. -/
def formC2n8 (X u : ℝ) : ℝ :=
  -2 * u * (X - 1) ^ 2 * (-4 * X ^ 2 + 3 * X * u - 3 * u) * (-X ^ 2 + X * u - u)

/-- The cleared numerator `formCF2 · 12 s² B C D³`, a polynomial of degree 8 in `s`. -/
def formC2N (X u s : ℝ) : ℝ :=
  formC2n0 X u * s ^ 0 + formC2n1 X u * s ^ 1 + formC2n2 X u * s ^ 2 + formC2n3 X u * s ^ 3 +
      formC2n4 X u * s ^ 4 + formC2n5 X u * s ^ 5 + formC2n6 X u * s ^ 6 + formC2n7 X u * s ^ 7 +
      formC2n8 X u * s ^ 8

theorem formC2_pc0 (X u : ℝ) :
    formC2Nr2 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) =
      formC2L X u * formC2n0 X u := by
  simp only [formC2Nr2, formC2L, formC2n0, formCP, formCQ]
  ring

theorem formC2_cf0 {X u : ℝ} (hL : formC2L X u ≠ 0) :
    formC2r2 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) =
      formC2n0 X u := by
  simp only [formC2r2]
  field_simp
  linear_combination formC2_pc0 X u

theorem formC2_pc1 (X u : ℝ) :
    formC2Nr1 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) +
      formC2Nr2 X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 *
          X ^ 3 * u ^ 2 + 7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6
          * X * u ^ 3 + 3 * u ^ 3)) =
      formC2L X u * formC2n1 X u := by
  simp only [formC2Nr1, formC2Nr2, formC2L, formC2n1, formCP, formCQ]
  ring

theorem formC2_cf1 {X u : ℝ} (hL : formC2L X u ≠ 0) :
    formC2r1 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) +
      formC2r2 X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 *
          X ^ 3 * u ^ 2 + 7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6
          * X * u ^ 3 + 3 * u ^ 3)) =
      formC2n1 X u := by
  simp only [formC2r1, formC2r2]
  field_simp
  linear_combination formC2_pc1 X u

theorem formC2_pc2 (X u : ℝ) :
    formC2Nq0 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) +
      formC2Nr1 X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 *
          X ^ 3 * u ^ 2 + 7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6
          * X * u ^ 3 + 3 * u ^ 3)) +
      formC2Nr2 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X
          ^ 5 * u ^ 2 - 28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X
          ^ 3 * u ^ 4 + 30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u
          ^ 3 + 19 * X ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) +
      formC2Nb X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) +
      formC2Nc X u * (-12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3) +
      formC2Nd1 X u * (-12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (X * u - X - u)) +
      formC2Nd2 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) * (X * u - X - u)) +
      formC2Nd3 X u * (-12 * (-X + u) * (X * u - X - u)) =
      formC2L X u * formC2n2 X u := by
  simp only [formC2Nq0, formC2Nr1, formC2Nr2, formC2Nb, formC2Nc, formC2Nd1, formC2Nd2,
      formC2Nd3, formC2L, formC2n2, formCP, formCQ]
  ring

theorem formC2_cf2 {X u : ℝ} (hL : formC2L X u ≠ 0) :
    formC2q0 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) +
      formC2r1 X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 *
          X ^ 3 * u ^ 2 + 7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6
          * X * u ^ 3 + 3 * u ^ 3)) +
      formC2r2 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X
          ^ 5 * u ^ 2 - 28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X
          ^ 3 * u ^ 4 + 30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u
          ^ 3 + 19 * X ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) +
      formC2b X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) +
      formC2c X u * (-12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3) +
      formC2d1 X u * (-12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (X * u - X - u)) +
      formC2d2 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) * (X * u - X - u)) +
      formC2d3 X u * (-12 * (-X + u) * (X * u - X - u)) =
      formC2n2 X u := by
  simp only [formC2q0, formC2r1, formC2r2, formC2b, formC2c, formC2d1, formC2d2, formC2d3]
  field_simp
  linear_combination formC2_pc2 X u

theorem formC2_pc3 (X u : ℝ) :
    formC2Nq0 X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 * X
        ^ 3 * u ^ 2 + 7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6 * X
        * u ^ 3 + 3 * u ^ 3)) +
      formC2Nq1 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) +
      formC2Nr1 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X
          ^ 5 * u ^ 2 - 28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X
          ^ 3 * u ^ 4 + 30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u
          ^ 3 + 19 * X ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) +
      formC2Nr2 X u * (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 *
          u ^ 2 - 32 * X ^ 5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 *
          u ^ 4 + 18 * X ^ 3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 +
          25 * X ^ 2 * u ^ 2 + 3 * X * u ^ 4 - u ^ 4)) +
      formC2Nb X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (-3 * X ^ 3 * u + 4 * X ^ 3 + 3 *
          X ^ 2 * u ^ 2 - 2 * X ^ 2 * u - 6 * X * u ^ 2 + 5 * X * u + 3 * u ^ 2)) +
      formC2Nc X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 3 - 8 * X ^ 2 * u + 3 * X
          * u ^ 2 + 5 * X * u - 3 * u ^ 2)) +
      formC2Nd1 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (3 * X ^ 4 * u - 4 * X ^ 4 - 6 * X ^
          3 * u ^ 2 + 6 * X ^ 3 * u + 2 * X ^ 2 * u ^ 3 + 6 * X ^ 2 * u ^ 2 - 6 * X ^ 2 * u - 4 * X
          * u ^ 3 + 2 * u ^ 3)) +
      formC2Nd2 X u * (-12 * (2 * X ^ 4 * u - 3 * X ^ 4 - 4 * X ^ 3 * u ^ 2 + 5 * X ^ 3 * u + X
          ^ 2 * u ^ 3 + 4 * X ^ 2 * u ^ 2 - 5 * X ^ 2 * u - 2 * X * u ^ 3 + u ^ 3)) +
      formC2Nd3 X u * (-12 * X ^ 2 * (u - 2)) =
      formC2L X u * formC2n3 X u := by
  simp only [formC2Nq0, formC2Nq1, formC2Nr1, formC2Nr2, formC2Nb, formC2Nc, formC2Nd1,
      formC2Nd2, formC2Nd3, formC2L, formC2n3, formCP, formCQ]
  ring

theorem formC2_cf3 {X u : ℝ} (hL : formC2L X u ≠ 0) :
    formC2q0 X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 * X
        ^ 3 * u ^ 2 + 7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6 * X
        * u ^ 3 + 3 * u ^ 3)) +
      formC2q1 X u * (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) +
      formC2r1 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X
          ^ 5 * u ^ 2 - 28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X
          ^ 3 * u ^ 4 + 30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u
          ^ 3 + 19 * X ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) +
      formC2r2 X u * (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 * u
          ^ 2 - 32 * X ^ 5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 * u
          ^ 4 + 18 * X ^ 3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 + 25
          * X ^ 2 * u ^ 2 + 3 * X * u ^ 4 - u ^ 4)) +
      formC2b X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (-3 * X ^ 3 * u + 4 * X ^ 3 + 3 *
          X ^ 2 * u ^ 2 - 2 * X ^ 2 * u - 6 * X * u ^ 2 + 5 * X * u + 3 * u ^ 2)) +
      formC2c X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 3 - 8 * X ^ 2 * u + 3 * X
          * u ^ 2 + 5 * X * u - 3 * u ^ 2)) +
      formC2d1 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (3 * X ^ 4 * u - 4 * X ^ 4 - 6 * X ^ 3
          * u ^ 2 + 6 * X ^ 3 * u + 2 * X ^ 2 * u ^ 3 + 6 * X ^ 2 * u ^ 2 - 6 * X ^ 2 * u - 4 * X *
          u ^ 3 + 2 * u ^ 3)) +
      formC2d2 X u * (-12 * (2 * X ^ 4 * u - 3 * X ^ 4 - 4 * X ^ 3 * u ^ 2 + 5 * X ^ 3 * u + X ^
          2 * u ^ 3 + 4 * X ^ 2 * u ^ 2 - 5 * X ^ 2 * u - 2 * X * u ^ 3 + u ^ 3)) +
      formC2d3 X u * (-12 * X ^ 2 * (u - 2)) =
      formC2n3 X u := by
  simp only [formC2q0, formC2q1, formC2r1, formC2r2, formC2b, formC2c, formC2d1, formC2d2, formC2d3]
  field_simp
  linear_combination formC2_pc3 X u

theorem formC2_pc4 (X u : ℝ) :
    formC2Nq0 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X ^
        5 * u ^ 2 - 28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X ^ 3
        * u ^ 4 + 30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u ^ 3 +
        19 * X ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) +
      formC2Nq1 X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 *
          X ^ 3 * u ^ 2 + 7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6
          * X * u ^ 3 + 3 * u ^ 3)) +
      formC2Nr1 X u * (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 *
          u ^ 2 - 32 * X ^ 5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 *
          u ^ 4 + 18 * X ^ 3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 +
          25 * X ^ 2 * u ^ 2 + 3 * X * u ^ 4 - u ^ 4)) +
      formC2Nr2 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u
          ^ 2 - 8 * X * u - u ^ 2 + 8 * u)) +
      formC2Nb X u * (36 * (-X ^ 2 + X * u - u) * (-X ^ 2 + 2 * X * u - 2 * u) * (-X ^ 3 * u + 2
          * X ^ 3 + X ^ 2 * u ^ 2 - 2 * X ^ 2 * u - 2 * X * u ^ 2 + 3 * X * u + u ^ 2)) +
      formC2Nc X u * (-36 * (-X ^ 2 + X * u - u) * (-X ^ 2 + 2 * X * u - 2 * u) * (2 * X ^ 3 - 4
          * X ^ 2 * u + X * u ^ 2 + 3 * X * u - u ^ 2)) +
      formC2Nd1 X u * (-12 * (-3 * X ^ 6 * u + 6 * X ^ 6 + 9 * X ^ 5 * u ^ 2 - 18 * X ^ 5 * u -
          7 * X ^ 4 * u ^ 3 + 4 * X ^ 4 * u ^ 2 + 18 * X ^ 4 * u + X ^ 3 * u ^ 4 + 14 * X ^ 3 * u ^
          3 - 26 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 7 * X ^ 2 * u ^ 3 + 13 * X ^ 2 * u ^ 2 + 3 *
          X * u ^ 4 - u ^ 4)) +
      formC2Nd2 X u * (-12 * X ^ 2 * (-X ^ 2 * u + 3 * X ^ 2 + X * u ^ 2 - 4 * X * u - u ^ 2 + 4
          * u)) +
      formC2Nd3 X u * (-12 * X ^ 2) =
      formC2L X u * formC2n4 X u := by
  simp only [formC2Nq0, formC2Nq1, formC2Nr1, formC2Nr2, formC2Nb, formC2Nc, formC2Nd1,
      formC2Nd2, formC2Nd3, formC2L, formC2n4, formCP, formCQ]
  ring

theorem formC2_cf4 {X u : ℝ} (hL : formC2L X u ≠ 0) :
    formC2q0 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X ^
        5 * u ^ 2 - 28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X ^ 3
        * u ^ 4 + 30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u ^ 3 +
        19 * X ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) +
      formC2q1 X u * (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 *
          X ^ 3 * u ^ 2 + 7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6
          * X * u ^ 3 + 3 * u ^ 3)) +
      formC2r1 X u * (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 * u
          ^ 2 - 32 * X ^ 5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 * u
          ^ 4 + 18 * X ^ 3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 + 25
          * X ^ 2 * u ^ 2 + 3 * X * u ^ 4 - u ^ 4)) +
      formC2r2 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u ^
          2 - 8 * X * u - u ^ 2 + 8 * u)) +
      formC2b X u * (36 * (-X ^ 2 + X * u - u) * (-X ^ 2 + 2 * X * u - 2 * u) * (-X ^ 3 * u + 2
          * X ^ 3 + X ^ 2 * u ^ 2 - 2 * X ^ 2 * u - 2 * X * u ^ 2 + 3 * X * u + u ^ 2)) +
      formC2c X u * (-36 * (-X ^ 2 + X * u - u) * (-X ^ 2 + 2 * X * u - 2 * u) * (2 * X ^ 3 - 4
          * X ^ 2 * u + X * u ^ 2 + 3 * X * u - u ^ 2)) +
      formC2d1 X u * (-12 * (-3 * X ^ 6 * u + 6 * X ^ 6 + 9 * X ^ 5 * u ^ 2 - 18 * X ^ 5 * u - 7
          * X ^ 4 * u ^ 3 + 4 * X ^ 4 * u ^ 2 + 18 * X ^ 4 * u + X ^ 3 * u ^ 4 + 14 * X ^ 3 * u ^ 3
          - 26 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 7 * X ^ 2 * u ^ 3 + 13 * X ^ 2 * u ^ 2 + 3 * X
          * u ^ 4 - u ^ 4)) +
      formC2d2 X u * (-12 * X ^ 2 * (-X ^ 2 * u + 3 * X ^ 2 + X * u ^ 2 - 4 * X * u - u ^ 2 + 4
          * u)) +
      formC2d3 X u * (-12 * X ^ 2) =
      formC2n4 X u := by
  simp only [formC2q0, formC2q1, formC2r1, formC2r2, formC2b, formC2c, formC2d1, formC2d2, formC2d3]
  field_simp
  linear_combination formC2_pc4 X u

theorem formC2_pc5 (X u : ℝ) :
    formC2Nq0 X u * (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 * u
        ^ 2 - 32 * X ^ 5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 * u ^
        4 + 18 * X ^ 3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 + 25 * X
        ^ 2 * u ^ 2 + 3 * X * u ^ 4 - u ^ 4)) +
      formC2Nq1 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X
          ^ 5 * u ^ 2 - 28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X
          ^ 3 * u ^ 4 + 30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u
          ^ 3 + 19 * X ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) +
      formC2Nr1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u
          ^ 2 - 8 * X * u - u ^ 2 + 8 * u)) +
      formC2Nr2 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) +
      formC2Nb X u * (-12 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 3 * u + 4 * X ^ 3 + X ^ 2 * u ^ 2 -
          6 * X ^ 2 * u - 2 * X * u ^ 2 + 7 * X * u + u ^ 2)) +
      formC2Nc X u * (12 * (-X ^ 2 + X * u - u) ^ 2 * (4 * X ^ 3 - 8 * X ^ 2 * u + X * u ^ 2 + 7
          * X * u - u ^ 2)) +
      formC2Nd1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) * (-X ^ 2 * u + 4 * X ^ 2 + X * u ^ 2
          - 6 * X * u - u ^ 2 + 6 * u)) +
      formC2Nd2 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u)) =
      formC2L X u * formC2n5 X u := by
  simp only [formC2Nq0, formC2Nq1, formC2Nr1, formC2Nr2, formC2Nb, formC2Nc, formC2Nd1,
      formC2Nd2, formC2L, formC2n5, formCP, formCQ]
  ring

theorem formC2_cf5 {X u : ℝ} (hL : formC2L X u ≠ 0) :
    formC2q0 X u * (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 * u ^
        2 - 32 * X ^ 5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 * u ^ 4
        + 18 * X ^ 3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 + 25 * X ^
        2 * u ^ 2 + 3 * X * u ^ 4 - u ^ 4)) +
      formC2q1 X u * (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X
          ^ 5 * u ^ 2 - 28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X
          ^ 3 * u ^ 4 + 30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u
          ^ 3 + 19 * X ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) +
      formC2r1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u ^
          2 - 8 * X * u - u ^ 2 + 8 * u)) +
      formC2r2 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) +
      formC2b X u * (-12 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 3 * u + 4 * X ^ 3 + X ^ 2 * u ^ 2 -
          6 * X ^ 2 * u - 2 * X * u ^ 2 + 7 * X * u + u ^ 2)) +
      formC2c X u * (12 * (-X ^ 2 + X * u - u) ^ 2 * (4 * X ^ 3 - 8 * X ^ 2 * u + X * u ^ 2 + 7
          * X * u - u ^ 2)) +
      formC2d1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) * (-X ^ 2 * u + 4 * X ^ 2 + X * u ^ 2 -
          6 * X * u - u ^ 2 + 6 * u)) +
      formC2d2 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u)) =
      formC2n5 X u := by
  simp only [formC2q0, formC2q1, formC2r1, formC2r2, formC2b, formC2c, formC2d1, formC2d2]
  field_simp
  linear_combination formC2_pc5 X u

theorem formC2_pc6 (X u : ℝ) :
    formC2Nq0 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u ^
        2 - 8 * X * u - u ^ 2 + 8 * u)) +
      formC2Nq1 X u * (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 *
          u ^ 2 - 32 * X ^ 5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 *
          u ^ 4 + 18 * X ^ 3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 +
          25 * X ^ 2 * u ^ 2 + 3 * X * u ^ 4 - u ^ 4)) +
      formC2Nr1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) +
      formC2Nb X u * (-12 * X * (-X ^ 2 + X * u - u) ^ 3) +
      formC2Nc X u * (12 * X * (-X ^ 2 + X * u - u) ^ 3) +
      formC2Nd1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2) =
      formC2L X u * formC2n6 X u := by
  simp only [formC2Nq0, formC2Nq1, formC2Nr1, formC2Nb, formC2Nc, formC2Nd1, formC2L, formC2n6,
      formCP, formCQ]
  ring

theorem formC2_cf6 {X u : ℝ} (hL : formC2L X u ≠ 0) :
    formC2q0 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u ^ 2
        - 8 * X * u - u ^ 2 + 8 * u)) +
      formC2q1 X u * (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 * u
          ^ 2 - 32 * X ^ 5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 * u
          ^ 4 + 18 * X ^ 3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 + 25
          * X ^ 2 * u ^ 2 + 3 * X * u ^ 4 - u ^ 4)) +
      formC2r1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) +
      formC2b X u * (-12 * X * (-X ^ 2 + X * u - u) ^ 3) +
      formC2c X u * (12 * X * (-X ^ 2 + X * u - u) ^ 3) +
      formC2d1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2) =
      formC2n6 X u := by
  simp only [formC2q0, formC2q1, formC2r1, formC2b, formC2c, formC2d1]
  field_simp
  linear_combination formC2_pc6 X u

theorem formC2_pc7 (X u : ℝ) :
    formC2Nq0 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) +
      formC2Nq1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u
          ^ 2 - 8 * X * u - u ^ 2 + 8 * u)) =
      formC2L X u * formC2n7 X u := by
  simp only [formC2Nq0, formC2Nq1, formC2L, formC2n7, formCP, formCQ]
  ring

theorem formC2_cf7 {X u : ℝ} (hL : formC2L X u ≠ 0) :
    formC2q0 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) +
      formC2q1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u ^
          2 - 8 * X * u - u ^ 2 + 8 * u)) =
      formC2n7 X u := by
  simp only [formC2q0, formC2q1]
  field_simp
  linear_combination formC2_pc7 X u

theorem formC2_pc8 (X u : ℝ) :
    formC2Nq1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) =
      formC2L X u * formC2n8 X u := by
  simp only [formC2Nq1, formC2L, formC2n8, formCP, formCQ]
  ring

theorem formC2_cf8 {X u : ℝ} (hL : formC2L X u ≠ 0) :
    formC2q1 X u * (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) =
      formC2n8 X u := by
  simp only [formC2q1]
  field_simp
  linear_combination formC2_pc8 X u

theorem formC2_Mq0 (X u s : ℝ) :
    12 * s ^ 2 * formCB X u s * formCC X u s * coordD X u s ^ 3 =
      (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) * s ^ 2 +
      (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 * X ^ 3 * u ^ 2 +
          7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6 * X * u ^ 3 + 3
          * u ^ 3)) * s ^ 3 +
      (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X ^ 5 * u ^ 2 -
          28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X ^ 3 * u ^ 4 +
          30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u ^ 3 + 19 * X
          ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) * s ^ 4 +
      (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 * u ^ 2 - 32 * X ^
          5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 * u ^ 4 + 18 * X ^
          3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 + 25 * X ^ 2 * u ^
          2 + 3 * X * u ^ 4 - u ^ 4)) * s ^ 5 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u ^ 2 - 8 * X * u
          - u ^ 2 + 8 * u)) * s ^ 6 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) * s ^ 7 := by
  simp only [formCB, formCC, coordD]
  ring

theorem formC2_Mq1 (X u s : ℝ) :
    12 * s ^ 3 * formCB X u s * formCC X u s * coordD X u s ^ 3 =
      (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) * s ^ 3 +
      (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 * X ^ 3 * u ^ 2 +
          7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6 * X * u ^ 3 + 3
          * u ^ 3)) * s ^ 4 +
      (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X ^ 5 * u ^ 2 -
          28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X ^ 3 * u ^ 4 +
          30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u ^ 3 + 19 * X
          ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) * s ^ 5 +
      (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 * u ^ 2 - 32 * X ^
          5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 * u ^ 4 + 18 * X ^
          3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 + 25 * X ^ 2 * u ^
          2 + 3 * X * u ^ 4 - u ^ 4)) * s ^ 6 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u ^ 2 - 8 * X * u
          - u ^ 2 + 8 * u)) * s ^ 7 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) * s ^ 8 := by
  simp only [formCB, formCC, coordD]
  ring

theorem formC2_Mr1 (X u s : ℝ) :
    12 * s * formCB X u s * formCC X u s * coordD X u s ^ 3 =
      (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) * s ^ 1 +
      (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 * X ^ 3 * u ^ 2 +
          7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6 * X * u ^ 3 + 3
          * u ^ 3)) * s ^ 2 +
      (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X ^ 5 * u ^ 2 -
          28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X ^ 3 * u ^ 4 +
          30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u ^ 3 + 19 * X
          ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) * s ^ 3 +
      (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 * u ^ 2 - 32 * X ^
          5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 * u ^ 4 + 18 * X ^
          3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 + 25 * X ^ 2 * u ^
          2 + 3 * X * u ^ 4 - u ^ 4)) * s ^ 4 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u ^ 2 - 8 * X * u
          - u ^ 2 + 8 * u)) * s ^ 5 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) * s ^ 6 := by
  simp only [formCB, formCC, coordD]
  ring

theorem formC2_Mr2 (X u s : ℝ) :
    12 * formCB X u s * formCC X u s * coordD X u s ^ 3 =
      (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) * s ^ 0 +
      (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 4 * u - 5 * X ^ 4 - 8 * X ^ 3 * u ^ 2 +
          7 * X ^ 3 * u + 3 * X ^ 2 * u ^ 3 + 8 * X ^ 2 * u ^ 2 - 7 * X ^ 2 * u - 6 * X * u ^ 3 + 3
          * u ^ 3)) * s ^ 1 +
      (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (-6 * X ^ 6 * u + 10 * X ^ 6 + 18 * X ^ 5 * u ^ 2 -
          28 * X ^ 5 * u - 15 * X ^ 4 * u ^ 3 + X ^ 4 * u ^ 2 + 28 * X ^ 4 * u + 3 * X ^ 3 * u ^ 4 +
          30 * X ^ 3 * u ^ 3 - 38 * X ^ 3 * u ^ 2 - 9 * X ^ 2 * u ^ 4 - 15 * X ^ 2 * u ^ 3 + 19 * X
          ^ 2 * u ^ 2 + 9 * X * u ^ 4 - 3 * u ^ 4)) * s ^ 2 +
      (-12 * (-X ^ 2 + X * u - u) * (-4 * X ^ 6 * u + 10 * X ^ 6 + 12 * X ^ 5 * u ^ 2 - 32 * X ^
          5 * u - 9 * X ^ 4 * u ^ 3 + 13 * X ^ 4 * u ^ 2 + 32 * X ^ 4 * u + X ^ 3 * u ^ 4 + 18 * X ^
          3 * u ^ 3 - 50 * X ^ 3 * u ^ 2 - 3 * X ^ 2 * u ^ 4 - 9 * X ^ 2 * u ^ 3 + 25 * X ^ 2 * u ^
          2 + 3 * X * u ^ 4 - u ^ 4)) * s ^ 3 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 2 * u + 5 * X ^ 2 + X * u ^ 2 - 8 * X * u
          - u ^ 2 + 8 * u)) * s ^ 4 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 3) * s ^ 5 := by
  simp only [formCB, formCC, coordD]
  ring

theorem formC2_Mb (X u s : ℝ) :
    12 * s ^ 2 * formCC X u s * coordD X u s ^ 3 =
      (12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3 * (X * u - X - u)) * s ^ 2 +
      (-12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (-3 * X ^ 3 * u + 4 * X ^ 3 + 3 * X ^ 2 * u ^ 2
          - 2 * X ^ 2 * u - 6 * X * u ^ 2 + 5 * X * u + 3 * u ^ 2)) * s ^ 3 +
      (36 * (-X ^ 2 + X * u - u) * (-X ^ 2 + 2 * X * u - 2 * u) * (-X ^ 3 * u + 2 * X ^ 3 + X ^
          2 * u ^ 2 - 2 * X ^ 2 * u - 2 * X * u ^ 2 + 3 * X * u + u ^ 2)) * s ^ 4 +
      (-12 * (-X ^ 2 + X * u - u) ^ 2 * (-X ^ 3 * u + 4 * X ^ 3 + X ^ 2 * u ^ 2 - 6 * X ^ 2 * u
          - 2 * X * u ^ 2 + 7 * X * u + u ^ 2)) * s ^ 5 +
      (-12 * X * (-X ^ 2 + X * u - u) ^ 3) * s ^ 6 := by
  simp only [formCC, coordD]
  ring

theorem formC2_Mc (X u s : ℝ) :
    12 * s ^ 2 * formCB X u s * coordD X u s ^ 3 =
      (-12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 3) * s ^ 2 +
      (12 * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (4 * X ^ 3 - 8 * X ^ 2 * u + 3 * X * u ^ 2 + 5 *
          X * u - 3 * u ^ 2)) * s ^ 3 +
      (-36 * (-X ^ 2 + X * u - u) * (-X ^ 2 + 2 * X * u - 2 * u) * (2 * X ^ 3 - 4 * X ^ 2 * u +
          X * u ^ 2 + 3 * X * u - u ^ 2)) * s ^ 4 +
      (12 * (-X ^ 2 + X * u - u) ^ 2 * (4 * X ^ 3 - 8 * X ^ 2 * u + X * u ^ 2 + 7 * X * u - u ^
          2)) * s ^ 5 +
      (12 * X * (-X ^ 2 + X * u - u) ^ 3) * s ^ 6 := by
  simp only [formCB, coordD]
  ring

theorem formC2_Md1 (X u s : ℝ) :
    12 * s ^ 2 * formCB X u s * formCC X u s * coordD X u s ^ 2 =
      (-12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) ^ 2 * (X * u - X - u)) * s ^ 2 +
      (12 * (-X ^ 2 + 2 * X * u - 2 * u) * (3 * X ^ 4 * u - 4 * X ^ 4 - 6 * X ^ 3 * u ^ 2 + 6 *
          X ^ 3 * u + 2 * X ^ 2 * u ^ 3 + 6 * X ^ 2 * u ^ 2 - 6 * X ^ 2 * u - 4 * X * u ^ 3 + 2 * u
          ^ 3)) * s ^ 3 +
      (-12 * (-3 * X ^ 6 * u + 6 * X ^ 6 + 9 * X ^ 5 * u ^ 2 - 18 * X ^ 5 * u - 7 * X ^ 4 * u ^
          3 + 4 * X ^ 4 * u ^ 2 + 18 * X ^ 4 * u + X ^ 3 * u ^ 4 + 14 * X ^ 3 * u ^ 3 - 26 * X ^ 3 *
          u ^ 2 - 3 * X ^ 2 * u ^ 4 - 7 * X ^ 2 * u ^ 3 + 13 * X ^ 2 * u ^ 2 + 3 * X * u ^ 4 - u ^
          4)) * s ^ 4 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) * (-X ^ 2 * u + 4 * X ^ 2 + X * u ^ 2 - 6 * X * u - u
          ^ 2 + 6 * u)) * s ^ 5 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u) ^ 2) * s ^ 6 := by
  simp only [formCB, formCC, coordD]
  ring

theorem formC2_Md2 (X u s : ℝ) :
    12 * s ^ 2 * formCB X u s * formCC X u s * coordD X u s =
      (12 * (-X + u) * (-X ^ 2 + 2 * X * u - 2 * u) * (X * u - X - u)) * s ^ 2 +
      (-12 * (2 * X ^ 4 * u - 3 * X ^ 4 - 4 * X ^ 3 * u ^ 2 + 5 * X ^ 3 * u + X ^ 2 * u ^ 3 + 4
          * X ^ 2 * u ^ 2 - 5 * X ^ 2 * u - 2 * X * u ^ 3 + u ^ 3)) * s ^ 3 +
      (-12 * X ^ 2 * (-X ^ 2 * u + 3 * X ^ 2 + X * u ^ 2 - 4 * X * u - u ^ 2 + 4 * u)) * s ^ 4 +
      (-12 * X ^ 2 * (-X ^ 2 + X * u - u)) * s ^ 5 := by
  simp only [formCB, formCC, coordD]
  ring

theorem formC2_Md3 (X u s : ℝ) :
    12 * s ^ 2 * formCB X u s * formCC X u s =
      (-12 * (-X + u) * (X * u - X - u)) * s ^ 2 +
      (-12 * X ^ 2 * (u - 2)) * s ^ 3 +
      (-12 * X ^ 2) * s ^ 4 := by
  simp only [formCB, formCC]
  ring

theorem formCF2_mul_den {X u s : ℝ} (hs : s ≠ 0) (hB : formCB X u s ≠ 0)
    (hC : formCC X u s ≠ 0) (hD : coordD X u s ≠ 0) :
    formCF2 X u s * (12 * s ^ 2 * formCB X u s * formCC X u s * coordD X u s ^ 3) =
      formC2N X u s := by
  unfold formCB at hB
  unfold formCC at hC
  unfold formCF2 formCP2 coordY2 coordZ2 formCB formCC
  simp only [formC2N, formC2n0, formC2n1, formC2n2, formC2n3, formC2n4, formC2n5, formC2n6,
    formC2n7, formC2n8]
  field_simp
  unfold coordD
  ring

theorem formCPF_mul_den (k : FormCPFc) {X u s : ℝ} (hs : s ≠ 0) (hB : formCB X u s ≠ 0)
    (hC : formCC X u s ≠ 0) (hD : coordD X u s ≠ 0) :
    formCPF k X u s * (12 * s ^ 2 * formCB X u s * formCC X u s * coordD X u s ^ 3) =
      k.q0 * (12 * s ^ 2 * formCB X u s * formCC X u s * coordD X u s ^ 3) +
      k.q1 * (12 * s ^ 3 * formCB X u s * formCC X u s * coordD X u s ^ 3) +
      k.r1 * (12 * s * formCB X u s * formCC X u s * coordD X u s ^ 3) +
      k.r2 * (12 * formCB X u s * formCC X u s * coordD X u s ^ 3) +
      k.b * (12 * s ^ 2 * formCC X u s * coordD X u s ^ 3) +
      k.c * (12 * s ^ 2 * formCB X u s * coordD X u s ^ 3) +
      k.d1 * (12 * s ^ 2 * formCB X u s * formCC X u s * coordD X u s ^ 2) +
      k.d2 * (12 * s ^ 2 * formCB X u s * formCC X u s * coordD X u s) +
      k.d3 * (12 * s ^ 2 * formCB X u s * formCC X u s) := by
  unfold formCPF
  generalize formCB X u s = B at *
  generalize formCC X u s = C at *
  generalize coordD X u s = D at *
  field_simp

theorem formC2L_ne_zero {X u : ℝ} (hX : X ≠ 0) (hX1 : X - 1 ≠ 0) (hX2 : X - 2 ≠ 0)
    (hP : formCP X u ≠ 0) (hQ : formCQ X u ≠ 0) : formC2L X u ≠ 0 := by
  unfold formC2L
  positivity

/-- **The branch-2 integrand in partial fractions.** -/
theorem formCF2_eq_formCPF {X u s : ℝ} (hX : X ≠ 0) (hX1 : X - 1 ≠ 0) (hX2 : X - 2 ≠ 0)
    (hP : formCP X u ≠ 0) (hQ : formCQ X u ≠ 0) (hs : s ≠ 0)
    (hB : formCB X u s ≠ 0) (hC : formCC X u s ≠ 0) (hD : coordD X u s ≠ 0) :
    formCF2 X u s = formCPF (formC2k X u) X u s := by
  have hden : 12 * s ^ 2 * formCB X u s * formCC X u s * coordD X u s ^ 3 ≠ 0 := by
    have := pow_ne_zero 2 hs
    have := pow_ne_zero 3 hD
    positivity
  have hL := formC2L_ne_zero hX hX1 hX2 hP hQ
  refine mul_right_cancel₀ hden ?_
  rw [formCF2_mul_den hs hB hC hD, formCPF_mul_den _ hs hB hC hD]
  rw [formC2_Mq0, formC2_Mq1, formC2_Mr1, formC2_Mr2, formC2_Mb, formC2_Mc, formC2_Md1,
    formC2_Md2, formC2_Md3]
  simp only [formC2k]
  rw [formC2N, ← formC2_cf0 hL, ← formC2_cf1 hL, ← formC2_cf2 hL, ← formC2_cf3 hL,
    ← formC2_cf4 hL, ← formC2_cf5 hL, ← formC2_cf6 hL, ← formC2_cf7 hL, ← formC2_cf8 hL]
  ring

end QED.ChainProof.SetCK

end
