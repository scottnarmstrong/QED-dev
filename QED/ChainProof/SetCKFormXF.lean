/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossT
public import QED.ChainProof.SetCKFormCS
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the crossed weight integrated over `x`

Helper level (no frozen statement). First step of the closed form of the crossed density `ρ_X`
(group G3, `crossTH`). At a node `(Y, y₃)` with `0 < y₃ < Y < 1` the `(M + v)⁻²`-weight
`T(Y, y₃, x, m)` (`crossTT`) is integrated over `x ∈ (0, 1)` at a fixed value `m > 0` of `v`.
The threshold `w₀(x) = β(x) x` is strictly increasing (`cornInW0_lt_of_lt`), so if
`w₀(s) = m` the weight is `T = (a₁ - c₂ x)/m + (a₂ x - c₃ x²/2)/m² + c₁ log(m/(β x)) +
c₂/β + c₃/(2β²)` for `x < s` and `0` for `x > s`. Below `x* = (1 - Y)/(1 - y₃)` (`cornInXs`)
`β = g = y₃(1 - Y)` (weight `formXE1`), above `β = e x/(1 - x)`, `e = y₃(Y - y₃)` (weight
`formXE2`). Both are polynomials in `x` plus `c₁` times logarithms of `x` and `1 - x`, with the
antiderivatives (**`hasDerivAt_formXP1`**, **`hasDerivAt_formXP2`**)

`P₁ = U₁ + K₁ (x log(m/g) - x log x)`,
`P₂ = U₂ + K₁ (x log(m/e) - 2 x log x) + K_b (1 - x) log(1 - x)`,

`U₁, U₂` polynomials of degree five, `K₁ = (1/x) ∫₀^x c₁` and `((1 - x) K_b)′ = c₁`. With
`a = min(s, x*)`:

**`integral_crossTT_x`**: `∫₀¹ T(Y, y₃, x, m) dx = P₁(a) + P₂(s) - P₂(a)` (`formXF`).

Checks (scratch `stageK/fx`): `x5.py` (exact derivative identities), `c5.py` (the closed form
against direct `x`-quadrature at four points in both branches, `10⁻³⁰`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The polynomial `K₁ = (1/x) ∫₀^x c₁` (coefficient of `x log`). -/
noncomputable def formXK1 (Y y3 x : ℝ) : ℝ := formOSP6
    (-y3 * (2 - 4 * Y + 3 * y3) / 4)
    (y3 * (2 + y3 - 2 * Y) / 4)
    (y3 * (-1 + y3) / 3)
    (0)
    (0)
    (0)
    (0) x

/-- The polynomial `K_b` with `(K_b (1 - x))′ = c₁`. -/
noncomputable def formXKb (Y y3 x : ℝ) : ℝ := formOSP6
    (y3 * (2 + y3 - 3 * Y) / 6)
    (-y3 * (2 - 6 * Y + 7 * y3) / 12)
    (-y3 * (-1 + y3) / 3)
    (0)
    (0)
    (0)
    (0) x

/-- The coefficient of `x^1` in `formXU1`. -/
noncomputable def formXU11 (Y y3 m : ℝ) : ℝ :=
  -y3 * (-8 * Y ^ 2 + 2 * m + 4 * Y + 4 * Y ^ 3 - y3 * Y ^ 2 - 4 * Y * m + 2 * Y * y3 + 3 * y3
      * m) / (4 * m)

/-- The coefficient of `x^2` in `formXU1`. -/
noncomputable def formXU12 (Y y3 m : ℝ) : ℝ :=
  (-2 * y3 ^ 2 - 2 * y3 ^ 3 + 2 * m + 4 * y3 + m * y3 ^ 2 - 28 * Y * y3 - 26 * y3 * Y ^ 3 - 22 * y3
      * m - 20 * Y ^ 2 * y3 ^ 2 - 4 * Y * m - 2 * Y ^ 2 * y3 ^ 3 + 4 * Y * y3 ^ 3 + 4 * y3 * Y ^ 4
      + 4 * m * Y ^ 2 + 6 * m * y3 ^ 3 + 10 * Y ^ 3 * y3 ^ 2 + 12 * Y * y3 ^ 2 + 46 * y3 * Y ^ 2
      - 14 * y3 * m * Y ^ 2 - 9 * Y * m * y3 ^ 2 + 36 * Y * y3 * m) / (8 * m * (-1 + Y))

/-- The coefficient of `x^3` in `formXU1`. -/
noncomputable def formXU13 (Y y3 m : ℝ) : ℝ :=
  -(-15 * m ^ 2 - 206 * y3 ^ 2 * m ^ 2 - 84 * Y ^ 2 * y3 ^ 3 - 60 * y3 * m - 60 * Y ^ 4 * y3 ^ 3
      - 54 * Y ^ 2 * y3 ^ 2 - 54 * Y ^ 4 * y3 ^ 2 - 42 * m * y3 ^ 4 - 30 * Y ^ 2 * y3 ^ 4 - 24 * m
      * y3 ^ 3 - 24 * Y ^ 2 * m ^ 2 - 12 * y3 ^ 3 * m ^ 2 - 6 * Y ^ 4 * y3 ^ 4 + 9 * y3 ^ 4 * m ^ 2
      + 12 * Y * y3 ^ 2 + 12 * Y * y3 ^ 4 + 12 * Y ^ 5 * y3 ^ 2 + 12 * Y ^ 5 * y3 ^ 3 + 24 * Y
      * y3 ^ 3 + 24 * Y ^ 3 * y3 ^ 4 + 30 * Y * m ^ 2 + 84 * Y ^ 3 * y3 ^ 2 + 108 * Y ^ 3 * y3 ^ 3
      + 224 * y3 * m ^ 2 + 234 * m * y3 ^ 2 - 900 * Y * m * y3 ^ 2 - 720 * m * Y ^ 3 * y3 ^ 2 - 444
      * y3 * m * Y ^ 2 - 406 * Y * y3 * m ^ 2 - 240 * m * Y ^ 2 * y3 ^ 3 - 176 * Y ^ 2 * y3 ^ 2
      * m ^ 2 - 72 * y3 * m * Y ^ 4 - 42 * m * Y ^ 2 * y3 ^ 4 - 6 * Y * y3 ^ 3 * m ^ 2 + 84 * Y * m
      * y3 ^ 4 + 108 * m * Y ^ 3 * y3 ^ 3 + 144 * m * Y ^ 4 * y3 ^ 2 + 156 * Y * m * y3 ^ 3 + 200
      * y3 * Y ^ 2 * m ^ 2 + 276 * Y * y3 * m + 300 * y3 * m * Y ^ 3 + 382 * Y * y3 ^ 2 * m ^ 2
      + 1242 * m * Y ^ 2 * y3 ^ 2) / (72 * m ^ 2 * (-1 + Y) ^ 2)

/-- The coefficient of `x^4` in `formXU1`. -/
noncomputable def formXU14 (Y y3 m : ℝ) : ℝ :=
  -y3 * (-1 + y3) * (y3 + y3 ^ 3 - 8 * m ^ 2 + 2 * y3 ^ 2 + 4 * m + Y ^ 2 * y3 ^ 3 - 24 * y3 * m - 8
      * Y * m - 6 * Y * y3 ^ 2 - 4 * Y * y3 - 2 * Y * y3 ^ 3 - 2 * y3 * Y ^ 3 - 2 * Y ^ 3 * y3 ^ 2
      + 4 * m * Y ^ 2 + 5 * y3 * Y ^ 2 + 6 * Y ^ 2 * y3 ^ 2 + 8 * y3 * m ^ 2 - 20 * y3 * m * Y ^ 2
      + 44 * Y * y3 * m) / (8 * m ^ 2 * (-1 + Y))

/-- The coefficient of `x^5` in `formXU1`. -/
noncomputable def formXU15 (Y y3 m : ℝ) : ℝ :=
  y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3 ^ 2 - 8 * m - 2 * Y + 2 * y3 - 2 * Y * y3) / (8 * m ^ 2)

/-- The polynomial part `U₁` of the antiderivative below `x*`. -/
noncomputable def formXU1 (Y y3 m x : ℝ) : ℝ :=
  formOSP6 0 (formXU11 Y y3 m) (formXU12 Y y3 m) (formXU13 Y y3 m) (formXU14 Y y3 m) (formXU15 Y y3
      m) 0 x

/-- The coefficient of `x^1` in `formXU2`. -/
noncomputable def formXU21 (Y y3 m : ℝ) : ℝ :=
  -(9 * m - 72 * Y ^ 2 * y3 ^ 3 - 54 * Y ^ 4 * y3 ^ 2 - 48 * y3 * Y ^ 4 - 48 * Y ^ 2 * y3 ^ 2 - 24
      * m * Y ^ 2 - 12 * y3 * m - 6 * Y * m - 6 * Y ^ 2 * y3 ^ 4 + 4 * m * y3 ^ 3 + 5 * m * y3 ^ 4
      + 12 * Y * y3 ^ 4 + 24 * Y * y3 ^ 3 + 24 * y3 * Y ^ 3 + 24 * y3 * Y ^ 5 + 24 * m * Y ^ 3 + 36
      * Y ^ 3 * y3 ^ 3 + 102 * m * y3 ^ 2 + 108 * Y ^ 3 * y3 ^ 2 - 194 * Y * m * y3 ^ 2 - 108 * y3
      * m * Y ^ 3 - 78 * Y * y3 * m - 22 * Y * m * y3 ^ 3 + 116 * m * Y ^ 2 * y3 ^ 2 + 184 * y3 * m
      * Y ^ 2) / (24 * m * (y3 - Y) ^ 2)

/-- The coefficient of `x^2` in `formXU2`. -/
noncomputable def formXU22 (Y y3 m : ℝ) : ℝ :=
  -(-9 * m - 6 * y3 ^ 4 - 6 * y3 ^ 5 + 12 * y3 ^ 3 - 150 * m * y3 ^ 2 - 102 * Y ^ 3 * y3 ^ 2 - 72
      * y3 * Y ^ 3 - 60 * Y * y3 ^ 3 - 42 * Y ^ 2 * y3 ^ 4 - 24 * Y * y3 ^ 2 - 12 * y3 * Y ^ 5 - 12
      * m * Y ^ 3 - 6 * Y ^ 4 * y3 ^ 2 + 6 * Y * y3 ^ 5 + 12 * y3 * Y ^ 2 + 16 * m * y3 ^ 4 + 18
      * y3 * m + 24 * m * Y ^ 2 + 42 * Y * y3 ^ 4 + 54 * Y ^ 3 * y3 ^ 3 + 66 * y3 * Y ^ 4 + 86 * m
      * y3 ^ 3 + 138 * Y ^ 2 * y3 ^ 2 - 190 * y3 * m * Y ^ 2 - 116 * Y * m * y3 ^ 3 + 42 * y3 * m
      * Y ^ 3 + 67 * m * Y ^ 2 * y3 ^ 2 + 98 * Y * m * y3 ^ 2 + 126 * Y * y3 * m) / (24 * m * (y3
      - Y) ^ 2)

/-- The coefficient of `x^3` in `formXU2`. -/
noncomputable def formXU23 (Y y3 m : ℝ) : ℝ :=
  (-9 * m ^ 2 - 294 * y3 ^ 2 * m ^ 2 - 234 * m * y3 ^ 4 - 96 * Y ^ 3 * y3 ^ 4 - 85 * y3 ^ 4 * m ^ 2
      - 84 * Y ^ 3 * y3 ^ 3 - 24 * Y * y3 ^ 5 - 24 * Y ^ 3 * y3 ^ 5 - 12 * Y * y3 ^ 4 - 12 * Y
      * y3 ^ 6 - 12 * Y ^ 3 * y3 ^ 2 - 12 * Y ^ 5 * y3 ^ 2 - 12 * Y ^ 5 * y3 ^ 3 - 6 * Y * m ^ 2 + 6
      * Y ^ 2 * y3 ^ 6 + 24 * y3 * m ^ 2 + 24 * m * y3 ^ 5 + 24 * Y ^ 2 * y3 ^ 3 + 24 * Y ^ 2
      * m ^ 2 + 30 * Y ^ 4 * y3 ^ 2 + 30 * Y ^ 4 * y3 ^ 4 + 42 * m * y3 ^ 6 + 60 * m * y3 ^ 3 + 60
      * Y ^ 2 * y3 ^ 5 + 60 * Y ^ 4 * y3 ^ 3 + 78 * Y ^ 2 * y3 ^ 4 + 364 * y3 ^ 3 * m ^ 2 - 768 * m
      * Y ^ 2 * y3 ^ 3 - 200 * y3 * Y ^ 2 * m ^ 2 - 192 * Y * m * y3 ^ 5 - 182 * Y * y3 ^ 2 * m ^ 2
      - 156 * y3 * m * Y ^ 3 - 144 * m * Y ^ 4 * y3 ^ 2 - 120 * Y * m * y3 ^ 2 - 82 * Y * y3 ^ 3
      * m ^ 2 + 60 * y3 * m * Y ^ 2 + 72 * y3 * m * Y ^ 4 + 78 * m * Y ^ 2 * y3 ^ 2 + 114 * m
      * Y ^ 2 * y3 ^ 4 + 176 * Y ^ 2 * y3 ^ 2 * m ^ 2 + 180 * m * Y ^ 3 * y3 ^ 3 + 270 * Y * y3
      * m ^ 2 + 288 * m * Y ^ 3 * y3 ^ 2 + 312 * Y * m * y3 ^ 3 + 384 * Y * m * y3 ^ 4) / (72
      * m ^ 2 * (y3 - Y) ^ 2)

/-- The coefficient of `x^4` in `formXU2`. -/
noncomputable def formXU24 (Y y3 m : ℝ) : ℝ :=
  -y3 * (-1 + y3) * (-y3 ^ 2 - y3 ^ 4 - 2 * y3 ^ 3 + 8 * m ^ 2 + Y * y3 + Y * y3 ^ 4 - 8 * y3
      * m ^ 2 - 6 * Y ^ 2 * y3 ^ 2 - 4 * y3 * m - 4 * m * Y ^ 2 - 3 * y3 * Y ^ 2 - 3 * Y ^ 2
      * y3 ^ 3 + 2 * y3 * Y ^ 3 + 2 * Y ^ 3 * y3 ^ 2 + 4 * Y * m + 5 * Y * y3 ^ 2 + 5 * Y * y3 ^ 3
      + 24 * m * y3 ^ 2 - 20 * Y * y3 * m - 20 * Y * m * y3 ^ 2 + 20 * y3 * m * Y ^ 2) / (8 * m ^ 2
      * (y3 - Y))

/-- The coefficient of `x^5` in `formXU2`. -/
noncomputable def formXU25 (Y y3 m : ℝ) : ℝ :=
  y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3 ^ 2 - 8 * m - 2 * Y + 2 * y3 - 2 * Y * y3) / (8 * m ^ 2)

/-- The polynomial part `U₂` of the antiderivative above `x*`. -/
noncomputable def formXU2 (Y y3 m x : ℝ) : ℝ :=
  formOSP6 0 (formXU21 Y y3 m) (formXU22 Y y3 m) (formXU23 Y y3 m) (formXU24 Y y3 m) (formXU25 Y y3
      m) 0 x
theorem formX_c1_0 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (hY : 1 - Y ≠ 0) :
    (1 : ℝ) * formXU11 Y y3 m - (-y3 * (2 - 4 * Y + 3 * y3) / 4) =
      (Y * y3 * (-4 - 4 * Y ^ 2 - 2 * y3 + 8 * Y + Y * y3) / 4) / m + (0) / m ^ 2
          + (0) / cornerG y3 (Y - y3) + (0) / (2 * cornerG y3 (Y - y3) ^ 2) := by
  have hgE : cornerG y3 (Y - y3) = y3 * (1 - Y) := by unfold cornerG; ring
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  rw [hgE]
  unfold formXU11
  field_simp
  ring

theorem formX_c1_1 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (hY : 1 - Y ≠ 0) :
    (2 : ℝ) * formXU12 Y y3 m - (y3 * (2 + y3 - 2 * Y) / 4) =
      (-y3 * (2 - y3 - y3 ^ 2 - 12 * Y - 2 * Y ^ 3 + 11 * Y ^ 2 + Y * y3 ^ 2 - 5 * y3 * Y ^ 2 + 5
          * Y * y3) / 2) / m + (0) / m ^ 2 + (-y3 * (1 + y3 ^ 2 - 10 * y3 - 2 * Y + 2 * Y ^ 2 + 3
          * y3 ^ 3 - 6 * y3 * Y ^ 2 - 5 * Y * y3 ^ 2 + 16 * Y * y3) / 2) / cornerG y3 (Y - y3)
          + (0) / (2 * cornerG y3 (Y - y3) ^ 2) := by
  have hgE : cornerG y3 (Y - y3) = y3 * (1 - Y) := by unfold cornerG; ring
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  rw [hgE]
  unfold formXU12
  field_simp
  ring

theorem formX_c1_2 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (hY : 1 - Y ≠ 0) :
    (3 : ℝ) * formXU13 Y y3 m - (y3 * (-1 + y3) / 3) =
      (y3 * (10 - 39 * y3 - 26 * Y + 4 * y3 ^ 2 + 7 * y3 ^ 3 + 12 * Y ^ 2 - 24 * y3 * Y ^ 2 - 18 * Y
          * y3 ^ 2 + 72 * Y * y3) / 4) / m + (Y * y3 ^ 2 * (1 + y3) * (-2 + Y) * (1 + y3 - 2
          * Y) / 4) / m ^ 2 + (y3 * (-1 + y3) * (-2 + y3 ^ 2 + 2 * Y + 16 * y3 - 14 * Y
          * y3) / 2) / cornerG y3 (Y - y3) + (-3 * y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3 - 2
          * Y) / 4) / (2 * cornerG y3 (Y - y3) ^ 2) := by
  have hgE : cornerG y3 (Y - y3) = y3 * (1 - Y) := by unfold cornerG; ring
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  rw [hgE]
  unfold formXU13
  field_simp
  ring

theorem formX_c1_3 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (hY : 1 - Y ≠ 0) :
    (4 : ℝ) * formXU14 Y y3 m - (0) =
      (2 * y3 * (-1 + y3) * (1 - Y - 6 * y3 + 5 * Y * y3)) / m + (-y3 ^ 2 * (1 + y3) * (-1 + Y)
          * (-1 + y3) * (1 + y3 - 2 * Y) / 2) / m ^ 2 + (4 * y3 ^ 2 * (-1 + y3) ^ 2) / cornerG y3 (Y
          - y3) + (0) / (2 * cornerG y3 (Y - y3) ^ 2) := by
  have hgE : cornerG y3 (Y - y3) = y3 * (1 - Y) := by unfold cornerG; ring
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  rw [hgE]
  unfold formXU14
  field_simp
  ring

theorem formX_c1_4 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (hY : 1 - Y ≠ 0) :
    (5 : ℝ) * formXU15 Y y3 m - (0) =
      (-5 * y3 ^ 2 * (-1 + y3) ^ 2) / m + (5 * y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3 - 2
          * Y) / 8) / m ^ 2 + (0) / cornerG y3 (Y - y3) + (0) / (2 * cornerG y3 (Y - y3) ^ 2) := by
  have hgE : cornerG y3 (Y - y3) = y3 * (1 - Y) := by unfold cornerG; ring
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  rw [hgE]
  unfold formXU15
  field_simp
  ring


theorem formX_c2_0 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) :
    (1 : ℝ) * formXU21 Y y3 m - (-y3 * (4 - 9 * Y + 8 * y3) / 6) =
      (Y * y3 * (-4 - 4 * Y ^ 2 - 2 * y3 + 8 * Y + Y * y3) / 4) / m + (0) / m ^ 2 + (-y3 * (1
          + y3 ^ 2 - 10 * y3 - 2 * Y + 2 * Y ^ 2 + 3 * y3 ^ 3 - 6 * y3 * Y ^ 2 - 5 * Y * y3 ^ 2 + 16
          * Y * y3) / 2) / (y3 * (Y - y3)) + (-3 * y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3 - 2
          * Y) / 4) / (2 * (y3 * (Y - y3)) ^ 2) := by
  have h34 : y3 - Y ≠ 0 := by contrapose! h4; linarith
  unfold formXU21
  field_simp
  ring

theorem formX_c2_1 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) :
    (2 : ℝ) * formXU22 Y y3 m - (-y3 * (-10 + y3 + 6 * Y) / 12) =
      (-y3 * (2 - y3 - y3 ^ 2 - 12 * Y - 2 * Y ^ 3 + 11 * Y ^ 2 + Y * y3 ^ 2 - 5 * y3 * Y ^ 2 + 5
          * Y * y3) / 2) / m + (0) / m ^ 2 + (y3 * (3 - 28 * y3 - 4 * Y + 2 * Y ^ 2 + 4 * y3 ^ 3
          + 16 * y3 ^ 2 - 19 * Y * y3 ^ 2 - 6 * y3 * Y ^ 2 + 32 * Y * y3) / 2) / (y3 * (Y - y3))
          + (3 * y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3 - 2 * Y) / 2) / (2 * (y3 * (Y
          - y3)) ^ 2) := by
  have h34 : y3 - Y ≠ 0 := by contrapose! h4; linarith
  unfold formXU22
  field_simp
  ring

theorem formX_c2_2 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) :
    (3 : ℝ) * formXU23 Y y3 m - (y3 * (-1 + y3) / 3) =
      (y3 * (10 - 39 * y3 - 26 * Y + 4 * y3 ^ 2 + 7 * y3 ^ 3 + 12 * Y ^ 2 - 24 * y3 * Y ^ 2 - 18 * Y
          * y3 ^ 2 + 72 * Y * y3) / 4) / m + (Y * y3 ^ 2 * (1 + y3) * (-2 + Y) * (1 + y3 - 2
          * Y) / 4) / m ^ 2 + (y3 * (-1 + y3) * (2 - 24 * y3 - 2 * Y + 7 * y3 ^ 2 + 14 * Y
          * y3) / 2) / (y3 * (Y - y3)) + (-3 * y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3 - 2
          * Y) / 4) / (2 * (y3 * (Y - y3)) ^ 2) := by
  have h34 : y3 - Y ≠ 0 := by contrapose! h4; linarith
  unfold formXU23
  field_simp
  ring

theorem formX_c2_3 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) :
    (4 : ℝ) * formXU24 Y y3 m - (0) =
      (2 * y3 * (-1 + y3) * (1 - Y - 6 * y3 + 5 * Y * y3)) / m + (-y3 ^ 2 * (1 + y3) * (-1 + Y)
          * (-1 + y3) * (1 + y3 - 2 * Y) / 2) / m ^ 2 + (-4 * y3 ^ 2 * (-1 + y3) ^ 2) / (y3 * (Y
          - y3)) + (0) / (2 * (y3 * (Y - y3)) ^ 2) := by
  have h34 : y3 - Y ≠ 0 := by contrapose! h4; linarith
  unfold formXU24
  field_simp
  ring

theorem formX_c2_4 {Y y3 m : ℝ} (hm : m ≠ 0) (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) :
    (5 : ℝ) * formXU25 Y y3 m - (0) =
      (-5 * y3 ^ 2 * (-1 + y3) ^ 2) / m + (5 * y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3 - 2
          * Y) / 8) / m ^ 2 + (0) / (y3 * (Y - y3)) + (0) / (2 * (y3 * (Y - y3)) ^ 2) := by
  have h34 : y3 - Y ≠ 0 := by contrapose! h4; linarith
  unfold formXU25
  field_simp
  ring

/-- The derivative of `K₁`. -/
noncomputable def formXK1' (Y y3 x : ℝ) : ℝ :=
  y3 * (2 + y3 - 2 * Y) / 4 + 2 * (y3 * (-1 + y3) / 3) * x

/-- The derivative of `K_b`. -/
noncomputable def formXKb' (Y y3 x : ℝ) : ℝ :=
  -y3 * (2 - 6 * Y + 7 * y3) / 12 + 2 * (-y3 * (-1 + y3) / 3) * x

/-- **The antiderivative below `x*`** (`β = g`). -/
noncomputable def formXP1 (Y y3 m x : ℝ) : ℝ :=
  formXU1 Y y3 m x + formXK1 Y y3 x * (x * (log m - log (cornerG y3 (Y - y3))) - x * log x)

/-- **The antiderivative above `x*`** (`β = e x/(1 - x)`). -/
noncomputable def formXP2 (Y y3 m x : ℝ) : ℝ :=
  formXU2 Y y3 m x + formXK1 Y y3 x * (x * (log m - log (y3 * (Y - y3))) - 2 * (x * log x)) +
    formXKb Y y3 x * ((1 - x) * log (1 - x))

/-- **The `x`-integral of the crossed weight** at threshold `s`: `P₁(a) + P₂(s) - P₂(a)`,
`a = min(s, x*)`. -/
noncomputable def formXF (Y y3 m s : ℝ) : ℝ :=
  formXP1 Y y3 m (min s (cornInXs Y y3)) + formXP2 Y y3 m s -
    formXP2 Y y3 m (min s (cornInXs Y y3))

/-- The log-free part `(a₁ - c₂ x)/m + (a₂ x - c₃ x²/2)/m²` of the weight. -/
noncomputable def formXR (Y y3 m x : ℝ) : ℝ :=
  (crossTA1 x y3 (Y - y3) - crossTC2 x y3 (Y - y3) * x) / m +
    (crossTA2 x y3 (Y - y3) * x - crossTC3 x y3 (Y - y3) * x ^ 2 / 2) / m ^ 2

/-- The weight below `x*`, logarithms expanded. -/
noncomputable def formXE1 (Y y3 m x : ℝ) : ℝ :=
  formXR Y y3 m x + crossTC1 x y3 (Y - y3) * (log m - log (cornerG y3 (Y - y3)) - log x) +
    (crossTC2 x y3 (Y - y3) / cornerG y3 (Y - y3) +
      crossTC3 x y3 (Y - y3) / (2 * cornerG y3 (Y - y3) ^ 2))

/-- The weight above `x*`, logarithms expanded. -/
noncomputable def formXE2 (Y y3 m x : ℝ) : ℝ :=
  formXR Y y3 m x +
    crossTC1 x y3 (Y - y3) * (log m - log (y3 * (Y - y3)) - 2 * log x + log (1 - x)) +
    (crossTC2 x y3 (Y - y3) / (y3 * (Y - y3) * x / (1 - x)) +
      crossTC3 x y3 (Y - y3) / (2 * (y3 * (Y - y3) * x / (1 - x)) ^ 2))

section

variable {Y y3 m x : ℝ}

theorem hasDerivAt_formXK1 : HasDerivAt (formXK1 Y y3) (formXK1' Y y3 x) x :=
  (hasDerivAt_formOSP6 _ _ _ _ _ _ _ x).congr_deriv (by simp only [formOSP6, formXK1']; ring)

theorem hasDerivAt_formXKb : HasDerivAt (formXKb Y y3) (formXKb' Y y3 x) x :=
  (hasDerivAt_formOSP6 _ _ _ _ _ _ _ x).congr_deriv (by simp only [formOSP6, formXKb']; ring)

theorem formX_idK1 : formXK1' Y y3 x * x + formXK1 Y y3 x = crossTC1 x y3 (Y - y3) := by
  simp only [formXK1', formXK1, formOSP6, crossTC1]
  ring

theorem formX_idKb : formXKb' Y y3 x * (1 - x) - formXKb Y y3 x = crossTC1 x y3 (Y - y3) := by
  simp only [formXKb', formXKb, formOSP6, crossTC1]
  ring

theorem formX_idU1 (hm : m ≠ 0) (h3 : y3 ≠ 0) (hY : 1 - Y ≠ 0) (U' : ℝ)
    (hU : HasDerivAt (formXU1 Y y3 m) U' x) :
    U' - formXK1 Y y3 x = formXR Y y3 m x +
      (crossTC2 x y3 (Y - y3) / cornerG y3 (Y - y3) +
        crossTC3 x y3 (Y - y3) / (2 * cornerG y3 (Y - y3) ^ 2)) := by
  rw [hU.unique (hasDerivAt_formOSP6 _ _ _ _ _ _ _ x)]
  have i0 := formX_c1_0 hm h3 hY
  have i1 := formX_c1_1 hm h3 hY
  have i2 := formX_c1_2 hm h3 hY
  have i3 := formX_c1_3 hm h3 hY
  have i4 := formX_c1_4 hm h3 hY
  unfold formXK1 formOSP6 formXR crossTA1 crossTN1 crossTA2 crossTPa crossTC2 crossTN2 crossTC3
    crossTP3
  linear_combination i0 + x * i1 + x ^ 2 * i2 + x ^ 3 * i3 + x ^ 4 * i4

theorem formX_c2b (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) (hx : x ≠ 0) :
    crossTC2 x y3 (Y - y3) / (y3 * (Y - y3) * x / (1 - x)) =
      (-y3 * (-1 + x) * (-1 - y3 ^ 2 - 3 * y3 ^ 3 - 2 * Y ^ 2 + 2 * Y + 2 * x + 10 * y3 +
        x * y3 ^ 3 - 18 * x * y3 - 16 * Y * y3 - 16 * x ^ 2 * y3 ^ 2 - 2 * Y * x +
        5 * Y * y3 ^ 2 + 6 * y3 * Y ^ 2 + 8 * y3 * x ^ 2 + 8 * x ^ 2 * y3 ^ 3 + 15 * x * y3 ^ 2 -
        14 * Y * x * y3 ^ 2 + 16 * Y * x * y3) / 2) / (y3 * (Y - y3)) := by
  unfold crossTC2 crossTN2
  field_simp
  ring

theorem formX_c3b (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) (hx : x ≠ 0) :
    crossTC3 x y3 (Y - y3) / (2 * (y3 * (Y - y3) * x / (1 - x)) ^ 2) =
      (-3 * y3 ^ 2 * (-1 + x) ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3 - 2 * Y) / 4) /
        (2 * (y3 * (Y - y3)) ^ 2) := by
  unfold crossTC3 crossTP3
  field_simp
  ring

theorem formX_idU2 (hm : m ≠ 0) (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) (hx : x ≠ 0) (U' : ℝ)
    (hU : HasDerivAt (formXU2 Y y3 m) U' x) :
    U' - 2 * formXK1 Y y3 x - formXKb Y y3 x = formXR Y y3 m x +
      (crossTC2 x y3 (Y - y3) / (y3 * (Y - y3) * x / (1 - x)) +
        crossTC3 x y3 (Y - y3) / (2 * (y3 * (Y - y3) * x / (1 - x)) ^ 2)) := by
  rw [hU.unique (hasDerivAt_formOSP6 _ _ _ _ _ _ _ x), formX_c2b h3 h4 hx,
    formX_c3b h3 h4 hx]
  have i0 := formX_c2_0 hm h3 h4
  have i1 := formX_c2_1 hm h3 h4
  have i2 := formX_c2_2 hm h3 h4
  have i3 := formX_c2_3 hm h3 h4
  have i4 := formX_c2_4 hm h3 h4
  unfold formXK1 formXKb formOSP6 formXR crossTA1 crossTN1 crossTA2 crossTPa crossTC2 crossTN2
    crossTC3 crossTP3
  linear_combination i0 + x * i1 + x ^ 2 * i2 + x ^ 3 * i3 + x ^ 4 * i4

theorem hasDerivAt_formXU1 : HasDerivAt (formXU1 Y y3 m)
    (deriv (formXU1 Y y3 m) x) x := by
  unfold formXU1
  exact (hasDerivAt_formOSP6 _ _ _ _ _ _ _ x).differentiableAt.hasDerivAt

theorem hasDerivAt_formXU2 : HasDerivAt (formXU2 Y y3 m)
    (deriv (formXU2 Y y3 m) x) x := by
  unfold formXU2
  exact (hasDerivAt_formOSP6 _ _ _ _ _ _ _ x).differentiableAt.hasDerivAt

/-- **The antiderivative below `x*`.** -/
theorem hasDerivAt_formXP1 (hx : x ≠ 0) (hm : m ≠ 0) (h3 : y3 ≠ 0) (hY : 1 - Y ≠ 0) :
    HasDerivAt (formXP1 Y y3 m) (formXE1 Y y3 m x) x := by
  set c := log m - log (cornerG y3 (Y - y3))
  have hL : HasDerivAt (fun x => x * c - x * log x) (c - (log x + 1)) x := by
    exact (((hasDerivAt_id' x).mul_const c).sub (hasDerivAt_mul_log hx)).congr_deriv (by ring)
  have h := (hasDerivAt_formXU1 (Y := Y) (y3 := y3) (m := m) (x := x)).add
    ((hasDerivAt_formXK1 (Y := Y) (y3 := y3) (x := x)).mul hL)
  refine h.congr_deriv ?_
  have i1 := formX_idK1 (Y := Y) (y3 := y3) (x := x)
  have i2 := formX_idU1 hm h3 hY _ (hasDerivAt_formXU1 (x := x))
  unfold formXE1
  linear_combination (c - log x) * i1 + i2

/-- **The antiderivative above `x*`.** -/
theorem hasDerivAt_formXP2 (hx : x ≠ 0) (hx1 : 1 - x ≠ 0) (hm : m ≠ 0) (h3 : y3 ≠ 0)
    (h4 : Y - y3 ≠ 0) : HasDerivAt (formXP2 Y y3 m) (formXE2 Y y3 m x) x := by
  set c := log m - log (y3 * (Y - y3))
  have hL : HasDerivAt (fun x => x * c - 2 * (x * log x)) (c - 2 * (log x + 1)) x := by
    exact (((hasDerivAt_id' x).mul_const c).sub
      ((hasDerivAt_mul_log hx).const_mul 2)).congr_deriv (by ring)
  have hM : HasDerivAt (fun x => (1 - x) * log (1 - x)) (-(log (1 - x) + 1)) x := by
    exact ((hasDerivAt_mul_log hx1).comp x ((hasDerivAt_id' x).const_sub 1)).congr_deriv
      (by ring)
  have h := ((hasDerivAt_formXU2 (Y := Y) (y3 := y3) (m := m) (x := x)).add
    ((hasDerivAt_formXK1 (Y := Y) (y3 := y3) (x := x)).mul hL)).add
    ((hasDerivAt_formXKb (Y := Y) (y3 := y3) (x := x)).mul hM)
  refine h.congr_deriv ?_
  have i1 := formX_idK1 (Y := Y) (y3 := y3) (x := x)
  have ib := formX_idKb (Y := Y) (y3 := y3) (x := x)
  have i2 := formX_idU2 hm h3 h4 hx _ (hasDerivAt_formXU2 (x := x))
  unfold formXE2
  linear_combination (c - 2 * log x) * i1 + log (1 - x) * ib + i2


theorem continuous_formXP1 (Y y3 m : ℝ) : Continuous (formXP1 Y y3 m) := by
  have h := continuous_mul_log
  unfold formXP1 formXU1 formXK1 formOSP6
  fun_prop

theorem continuous_formXP2 (Y y3 m : ℝ) : Continuous (formXP2 Y y3 m) := by
  have h : Continuous fun x : ℝ => (1 - x) * log (1 - x) :=
    continuous_mul_log.comp (continuous_const.sub continuous_id)
  have h' := continuous_mul_log
  unfold formXP2 formXU2 formXK1 formXKb formOSP6
  fun_prop

theorem formXP1_zero (Y y3 m : ℝ) : formXP1 Y y3 m 0 = 0 := by
  simp [formXP1, formXU1, formOSP6]

/-- Below the threshold and below `x*` the weight is `formXE1`. -/
theorem crossTT_eq_formXE1 (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) (hx : 0 < x)
    (hxs : x ≤ cornInXs Y y3) (hw : cornInW0 Y y3 x < m) :
    crossTT Y y3 x m = formXE1 Y y3 m x := by
  have hx1 : x < 1 := hxs.trans_lt (cornInXs_mem h3 h34 hY).2
  have hβ := betaG_of_branch1 h3 hx1 (cornIn_branch1_of_xs h3 h34 hY hxs)
  have hg : 0 < cornerG y3 (Y - y3) := by unfold cornerG; nlinarith
  have hm : 0 < m := (cornInW0_pos hY h3 hx).trans hw
  unfold cornInW0 at hw
  unfold crossTT crossTTg
  simp only [hw, ↓reduceIte]
  rw [hβ, log_div hm.ne' (mul_ne_zero hg.ne' hx.ne'), log_mul hg.ne' hx.ne']
  unfold formXE1 formXR
  ring

/-- Below the threshold and above `x*` the weight is `formXE2`. -/
theorem crossTT_eq_formXE2 (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) (hx1 : x < 1)
    (hxs : cornInXs Y y3 ≤ x) (hw : cornInW0 Y y3 x < m) :
    crossTT Y y3 x m = formXE2 Y y3 m x := by
  have hx : 0 < x := (cornInXs_mem h3 h34 hY).1.trans_le hxs
  have hβ := betaG_of_branch2 h3 hx1 (cornIn_branch2_of_xs h3 h34 hY hxs)
  have hm : 0 < m := (cornInW0_pos hY h3 hx).trans hw
  have he : 0 < y3 * (Y - y3) := mul_pos h3 (by linarith)
  have h1x : 0 < 1 - x := by linarith
  have hL : log (m / (y3 * (Y - y3) * x / (1 - x) * x)) =
      log m - log (y3 * (Y - y3)) - 2 * log x + log (1 - x) := by
    rw [show m / (y3 * (Y - y3) * x / (1 - x) * x) = m * (1 - x) / (y3 * (Y - y3) * x ^ 2) by
        field_simp,
      log_div (by positivity) (by positivity), log_mul hm.ne' h1x.ne',
      log_mul he.ne' (by positivity), log_pow]
    push_cast
    ring
  unfold cornInW0 at hw
  unfold crossTT crossTTg
  simp only [hw, ↓reduceIte]
  rw [hβ, hL]
  unfold formXE2 formXR
  ring

/-- Above the threshold the weight vanishes. -/
theorem crossTT_eq_zero_of_le (hw : m ≤ cornInW0 Y y3 x) : crossTT Y y3 x m = 0 := by
  unfold cornInW0 at hw
  unfold crossTT crossTTg
  simp only [not_lt.2 hw, ↓reduceIte]

theorem intervalIntegrable_formXE1 (a : ℝ) :
    IntervalIntegrable (formXE1 Y y3 m) volume 0 a := by
  have hc : Continuous fun x => formXR Y y3 m x +
      crossTC1 x y3 (Y - y3) * (log m - log (cornerG y3 (Y - y3))) +
      (crossTC2 x y3 (Y - y3) / cornerG y3 (Y - y3) +
        crossTC3 x y3 (Y - y3) / (2 * cornerG y3 (Y - y3) ^ 2)) := by
    unfold formXR crossTA1 crossTN1 crossTA2 crossTPa crossTC1 crossTC2 crossTN2 crossTC3 crossTP3
    fun_prop
  have hl : IntervalIntegrable (fun x => crossTC1 x y3 (Y - y3) * log x) volume 0 a :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul
      (by unfold crossTC1; fun_prop)
  refine ((hc.intervalIntegrable 0 a).sub hl).congr_uIoo fun x _ => ?_
  simp only [formXE1]
  ring

theorem continuousAt_formXE2 (h3 : 0 < y3) (h34 : y3 < Y)
    (hx : x ∈ Ioo (0 : ℝ) 1) : ContinuousAt (formXE2 Y y3 m) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hβ : y3 * (Y - y3) * x / (1 - x) ≠ 0 := by
    have : 0 < Y - y3 := by linarith
    have : 0 < 1 - x := by linarith [hx.2]
    have := hx.1
    positivity
  have hβ2 : 2 * (y3 * (Y - y3) * x / (1 - x)) ^ 2 ≠ 0 := by positivity
  unfold formXE2 formXR crossTA1 crossTN1 crossTA2 crossTPa crossTC1 crossTC2 crossTN2 crossTC3
    crossTP3
  fun_prop (disch := assumption)

/-- **The `x`-integral of the crossed weight** at a node, given the threshold `w₀(s) = m`. -/
theorem integral_crossTT_x {Y y3 s m : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hm : cornInW0 Y y3 s = m) :
    IntegrableOn (fun x => crossTT Y y3 x m) (Ioo 0 1) ∧
      ∫ x in Ioo (0 : ℝ) 1, crossTT Y y3 x m = formXF Y y3 m s := by
  have hm0 : 0 < m := hm ▸ cornInW0_pos hY h3 hs.1
  set xs := cornInXs Y y3 with hxs_def
  have hxs := cornInXs_mem h3 h34 hY
  set a := min s xs with ha
  have ha0 : 0 < a := lt_min hs.1 hxs.1
  have has : a ≤ s := min_le_left _ _
  set f := fun x => crossTT Y y3 x m with hf
  have e1 : EqOn f (formXE1 Y y3 m) (uIoo 0 a) := by
    intro x hx
    rw [uIoo_of_le ha0.le] at hx
    have hlt : cornInW0 Y y3 x < m :=
      hm ▸ cornInW0_lt_of_lt h3 h34 hY hx.1 (hx.2.trans_le has) hs.2
    exact crossTT_eq_formXE1 h3 h34 hY hx.1 (hx.2.le.trans (min_le_right _ _)) hlt
  have e2 : EqOn f (formXE2 Y y3 m) (uIoo a s) := by
    intro x hx
    rw [uIoo_of_le has] at hx
    have hlt : cornInW0 Y y3 x < m :=
      hm ▸ cornInW0_lt_of_lt h3 h34 hY (ha0.trans hx.1) hx.2 hs.2
    have hxs' : xs ≤ x := by
      rcases min_cases s xs with h | h
      · have : a = s := by rw [ha]; exact h.1
        linarith [hx.1, hx.2]
      · have : a = xs := by rw [ha]; exact h.1
        linarith [hx.1]
    exact crossTT_eq_formXE2 h3 h34 hY (hx.2.trans hs.2) hxs' hlt
  have e3 : EqOn f (fun _ => 0) (uIoo s 1) := by
    intro x hx
    rw [uIoo_of_le hs.2.le] at hx
    exact crossTT_eq_zero_of_le (hm ▸ (cornInW0_lt_of_lt h3 h34 hY hs.1 hx.1 hx.2).le)
  have iE1 := intervalIntegrable_formXE1 (Y := Y) (y3 := y3) (m := m) a
  have cE2 : ContinuousOn (formXE2 Y y3 m) (uIcc a s) := by
    intro x hx
    rw [uIcc_of_le has] at hx
    exact (continuousAt_formXE2 h3 h34
      ⟨ha0.trans_le hx.1, hx.2.trans_lt hs.2⟩).continuousWithinAt
  have iE2 : IntervalIntegrable (formXE2 Y y3 m) volume a s := cE2.intervalIntegrable
  have i1 : IntervalIntegrable f volume 0 a := iE1.congr_uIoo fun x hx => (e1 hx).symm
  have i2 : IntervalIntegrable f volume a s := iE2.congr_uIoo fun x hx => (e2 hx).symm
  have i3 : IntervalIntegrable f volume s 1 :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo fun x hx => (e3 hx).symm
  have i123 := (i1.trans i2).trans i3
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 i123, ?_⟩
  have h3' : y3 ≠ 0 := h3.ne'
  have hY' : 1 - Y ≠ 0 := by linarith
  have h4 : Y - y3 ≠ 0 := by linarith
  have d1 : ∀ x ∈ Ioo 0 a, HasDerivAt (formXP1 Y y3 m) (formXE1 Y y3 m x) x :=
    fun x hx => hasDerivAt_formXP1 hx.1.ne' hm0.ne' h3' hY'
  have d2 : ∀ x ∈ uIcc a s, HasDerivAt (formXP2 Y y3 m) (formXE2 Y y3 m x) x := by
    intro x hx
    rw [uIcc_of_le has] at hx
    exact hasDerivAt_formXP2 (by linarith [hx.1]) (by linarith [hx.2, hs.2]) hm0.ne' h3' h4
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    intervalIntegral.integral_congr_uIoo e1, intervalIntegral.integral_congr_uIoo e2,
    intervalIntegral.integral_congr_uIoo e3, intervalIntegral.integral_const, smul_zero,
    add_zero, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha0.le
      (continuous_formXP1 Y y3 m).continuousOn d1 iE1,
    intervalIntegral.integral_eq_sub_of_hasDerivAt d2 iE2, formXP1_zero, formXF]
  ring

end

end QED.ChainProof.SetCK

end
