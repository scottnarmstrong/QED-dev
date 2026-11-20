/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXThr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the `m`-derivative `S` of the crossed `x`-integral

Helper level (no frozen statement). Route D of the crossed density `ρ_X` (scratch
`stageK/STATUS.md`, session 19+): the `x`-integral `F(m) = formXF Y y₃ m s(m)` of the crossed
weight is differentiated in `m`. With `g = y₃(1 - Y)`, `e = y₃(Y - y₃)`, `x* = (1 - Y)/(1 - y₃)`
(`cornInXs`) and the threshold `s` (`w₀(s) = m`):

* the antiderivatives depend on `m` only through `Uₐ(x)/m + U_b(x)/m² + K₁(x) x log m`
  (**`formXP1_sub`**, **`formXP2_sub`**; `Uₐ = ∫₀^x (a₁ - c₂x)`, `U_b = ∫₀^x (a₂x - c₃x²/2)`),
  so `∂ₘP = formXDm`;
* below the switch (`s = m/g ≤ x*`) `F` is the cubic polynomial `formXF1` in `m`
  (**`formXP1_eq_formXF1`**) with **`hasDerivAt_formXF1`**: `F₁′(m) = S₁(m/g)` (`formXS1`);
* above the switch (`e s² = m(1 - s)`) the bulk term plus the weight at `s` times
  `s′(m) = (1 - s)/(2es + m)` is `S₂(s)` (**`formX_S2_id`**, `formXS2`);
* `F(0⁺) = formXF0` (**`formXF1_zero`**) and **`integral_formXF0`**: `∫₀^Y F(0⁺) dy₃ = e₁M(Y)`.

`formXS` is `S` as a function of the threshold. Checks (scratch `stageK/fx`): `x1.py`, `x4.py`
(`S = dF/dm`), `xs1.py`, `xs2.py`, `xs3.py` (exact identities), generators `xg1.py`, `xg3.py`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The `1/m`-part `∫₀^x (a₁ - c₂ x)` of `U₁` and `U₂`. -/
noncomputable def formXUa (Y y3 x : ℝ) : ℝ := formOSP6
    (0)
    (Y * y3 * (-4 - 4 * Y ^ 2 - 2 * y3 + 8 * Y + Y * y3) / 4)
    (-y3 * (2 - y3 - y3 ^ 2 - 12 * Y - 2 * Y ^ 3 + 11 * Y ^ 2 + Y * y3 ^ 2 - 5 * y3 * Y ^ 2 + 5 * Y
        * y3) / 4)
    (y3 * (10 - 39 * y3 - 26 * Y + 4 * y3 ^ 2 + 7 * y3 ^ 3 + 12 * Y ^ 2 - 24 * y3 * Y ^ 2 - 18 * Y
        * y3 ^ 2 + 72 * Y * y3) / 12)
    (y3 * (-1 + y3) * (1 - Y - 6 * y3 + 5 * Y * y3) / 2)
    (-y3 ^ 2 * (-1 + y3) ^ 2)
    (0) x

/-- The `1/m²`-part `∫₀^x (a₂ x - c₃ x²/2)` of `U₁` and `U₂`. -/
noncomputable def formXUb (Y y3 x : ℝ) : ℝ := formOSP6
    (0)
    (0)
    (0)
    (Y * y3 ^ 2 * (1 + y3) * (-2 + Y) * (1 + y3 - 2 * Y) / 12)
    (-y3 ^ 2 * (1 + y3) * (-1 + Y) * (-1 + y3) * (1 + y3 - 2 * Y) / 8)
    (y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3 - 2 * Y) / 8)
    (0) x

/-- The `m`-free part of `U₁`. -/
noncomputable def formXZ1 (Y y3 x : ℝ) : ℝ := formOSP6
    (0)
    (-y3 * (2 - 4 * Y + 3 * y3) / 4)
    ((2 + y3 ^ 2 - 22 * y3 - 4 * Y + 4 * Y ^ 2 + 6 * y3 ^ 3 - 14 * y3 * Y ^ 2 - 9 * Y * y3 ^ 2 + 36
        * Y * y3) / (8 * (-1 + Y)))
    (-(-1 + y3) * (15 - 209 * y3 - 30 * Y - 3 * y3 ^ 2 + 9 * y3 ^ 3 + 24 * Y ^ 2 - 176 * y3 * Y ^ 2
        - 6 * Y * y3 ^ 2 + 376 * Y * y3) / (72 * (-1 + Y) ^ 2))
    (-y3 * (-1 + y3) ^ 2 / (-1 + Y))
    (0)
    (0) x

/-- The `m`-free part of `U₂`. -/
noncomputable def formXZ2 (Y y3 x : ℝ) : ℝ := formOSP6
    (0)
    (-(9 - 24 * Y ^ 2 - 12 * y3 - 6 * Y + 4 * y3 ^ 3 + 5 * y3 ^ 4 + 24 * Y ^ 3 + 102 * y3 ^ 2 - 194
        * Y * y3 ^ 2 - 108 * y3 * Y ^ 3 - 78 * Y * y3 - 22 * Y * y3 ^ 3 + 116 * Y ^ 2 * y3 ^ 2 + 184
        * y3 * Y ^ 2) / (24 * (y3 - Y) ^ 2))
    (-(-9 - 150 * y3 ^ 2 - 12 * Y ^ 3 + 16 * y3 ^ 4 + 18 * y3 + 24 * Y ^ 2 + 86 * y3 ^ 3 - 190 * y3
        * Y ^ 2 - 116 * Y * y3 ^ 3 + 42 * y3 * Y ^ 3 + 67 * Y ^ 2 * y3 ^ 2 + 98 * Y * y3 ^ 2 + 126
        * Y * y3) / (24 * (y3 - Y) ^ 2))
    (-(-1 + y3) * (-9 - 279 * y3 ^ 2 - 6 * Y + 15 * y3 + 24 * Y ^ 2 + 85 * y3 ^ 3 - 176 * y3 * Y ^ 2
        + 82 * Y * y3 ^ 2 + 264 * Y * y3) / (72 * (y3 - Y) ^ 2))
    (y3 * (-1 + y3) ^ 2 / (y3 - Y))
    (0)
    (0) x

/-- **The `x`-integral below the switch** as a polynomial in `m`. -/
noncomputable def formXF1 (Y y3 m : ℝ) : ℝ := formOSP6
    (-Y * (-4 - 4 * Y ^ 2 - 2 * y3 + 8 * Y + Y * y3) / (4 * (-1 + Y)))
    ((6 - 40 * Y - 37 * Y ^ 3 + 3 * y3 + 6 * Y ^ 4 + 6 * y3 ^ 2 + 64 * Y ^ 2 - 10 * Y * y3 ^ 2 - 6
        * y3 * Y ^ 2 - 2 * Y * y3 + 5 * y3 * Y ^ 3 + 5 * Y ^ 2 * y3 ^ 2) / (12 * y3 * (-1 + Y) ^ 3))
    ((-11 + y3 ^ 3 - 12 * Y ^ 2 - 8 * y3 ^ 2 + 15 * y3 + 34 * Y - 36 * Y * y3 + 6 * y3 * Y ^ 2 + 15
        * Y * y3 ^ 2) / (24 * y3 ^ 2 * (-1 + Y) ^ 3))
    ((-1 + y3) * (3 - 4 * y3 - 3 * Y + 3 * y3 ^ 2 + Y * y3) / (18 * y3 ^ 3 * (-1 + Y) ^ 4))
    (0)
    (0)
    (0) m

/-- The numerator of `S₁`. -/
noncomputable def formXN1 (Y y3 s : ℝ) : ℝ :=
  6 - 40 * Y - 37 * Y ^ 3 - 11 * s + 3 * y3 + 6 * Y ^ 4 + 6 * s ^ 2 + 6 * y3 ^ 2 + 64 * Y ^ 2 + s
      * y3 ^ 3 - 46 * s * Y ^ 2 - 14 * y3 * s ^ 2 - 12 * Y * s ^ 2 - 10 * Y * y3 ^ 2 - 8 * s
      * y3 ^ 2 - 6 * y3 * Y ^ 2 - 6 * s ^ 2 * y3 ^ 3 - 2 * Y * y3 + 5 * y3 * Y ^ 3 + 5 * Y ^ 2
      * y3 ^ 2 + 6 * Y ^ 2 * s ^ 2 + 12 * s * Y ^ 3 + 14 * s ^ 2 * y3 ^ 2 + 15 * s * y3 + 45 * Y * s
      - Y * s * y3 ^ 3 - 51 * Y * s * y3 - 16 * Y * s ^ 2 * y3 ^ 2 - 15 * s * Y ^ 2 * y3 ^ 2 - 8
      * y3 * Y ^ 2 * s ^ 2 - 6 * s * y3 * Y ^ 3 + 2 * Y ^ 2 * s ^ 2 * y3 ^ 2 + 6 * Y * s ^ 2
      * y3 ^ 3 + 22 * Y * y3 * s ^ 2 + 23 * Y * s * y3 ^ 2 + 42 * s * y3 * Y ^ 2

/-- The numerator of `S₂`. -/
noncomputable def formXN2 (Y y3 s : ℝ) : ℝ :=
  -22 * Y ^ 3 + 2 * Y + 7 * Y ^ 2 + 12 * Y ^ 4 - 113 * Y ^ 2 * s ^ 4 - 74 * Y ^ 3 * s ^ 3 - 35 * y3
      * s ^ 4 - 32 * Y ^ 2 * s ^ 2 - 24 * s * Y ^ 4 - 23 * Y * s ^ 5 - 21 * Y * s ^ 3 - 15 * s ^ 2
      * y3 ^ 2 - 15 * s ^ 4 * y3 ^ 2 - 14 * s * Y ^ 2 - 13 * y3 * Y ^ 3 - 12 * Y ^ 3 * s ^ 5 - 10
      * s ^ 2 * y3 ^ 3 - 10 * s ^ 2 * y3 ^ 4 - 9 * s ^ 5 * y3 ^ 2 - 8 * Y * y3 - 7 * y3 * s ^ 2 - 7
      * s ^ 5 * y3 ^ 3 - 6 * y3 * s ^ 6 - 6 * Y ^ 2 * s ^ 6 - 6 * Y ^ 4 * s ^ 4 - 4 * Y * s - 4 * Y
      * y3 ^ 2 - 4 * s ^ 5 * y3 ^ 4 - 2 * s ^ 6 * y3 ^ 4 + 2 * Y ^ 2 * y3 ^ 2 + 2 * s ^ 4 * y3 ^ 3
      + 2 * s ^ 6 * y3 ^ 3 + 6 * Y * s ^ 6 + 6 * Y ^ 4 * s ^ 2 + 6 * s ^ 4 * y3 ^ 4 + 6 * s ^ 6
      * y3 ^ 2 + 7 * Y * s ^ 2 + 9 * Y ^ 3 * s ^ 2 + 10 * s ^ 3 * y3 ^ 4 + 12 * Y ^ 4 * s ^ 3 + 13
      * s ^ 3 * y3 ^ 3 + 23 * y3 * s ^ 5 + 24 * y3 * Y ^ 2 + 25 * y3 * s ^ 3 + 33 * Y * s ^ 4 + 33
      * s ^ 3 * y3 ^ 2 + 44 * s * Y ^ 3 + 46 * Y ^ 2 * s ^ 5 + 55 * Y ^ 3 * s ^ 4 + 112 * Y ^ 2
      * s ^ 3 - 147 * Y * y3 * s ^ 3 - 61 * Y * s ^ 3 * y3 ^ 3 - 51 * Y ^ 2 * s ^ 2 * y3 ^ 2 - 48
      * s * y3 * Y ^ 2 - 38 * y3 * Y ^ 3 * s ^ 3 - 37 * Y * y3 * s ^ 5 - 33 * Y * s ^ 3 * y3 ^ 2
      - 32 * y3 * Y ^ 2 * s ^ 4 - 24 * y3 * Y ^ 2 * s ^ 2 - 23 * Y * s ^ 4 * y3 ^ 2 - 18 * y3
      * Y ^ 2 * s ^ 5 - 15 * Y ^ 2 * s ^ 4 * y3 ^ 2 - 10 * Y * s ^ 6 * y3 ^ 2 - 9 * Y ^ 2 * s ^ 5
      * y3 ^ 2 - 4 * s * Y ^ 2 * y3 ^ 2 - 2 * Y ^ 2 * s ^ 6 * y3 ^ 2 + 4 * Y * s ^ 6 * y3 ^ 3 + 6
      * y3 * Y ^ 3 * s ^ 5 + 7 * Y * s ^ 4 * y3 ^ 3 + 7 * Y * s ^ 5 * y3 ^ 3 + 7 * y3 * Y ^ 3
      * s ^ 4 + 8 * Y * s * y3 ^ 2 + 8 * y3 * Y ^ 2 * s ^ 6 + 12 * y3 * Y ^ 3 * s ^ 2 + 16 * Y * s
      * y3 + 25 * Y * s ^ 2 * y3 ^ 2 + 26 * s * y3 * Y ^ 3 + 37 * Y * s ^ 5 * y3 ^ 2 + 43 * Y
      * s ^ 2 * y3 ^ 3 + 47 * Y * y3 * s ^ 2 + 79 * Y ^ 2 * s ^ 3 * y3 ^ 2 + 90 * y3 * Y ^ 2 * s ^ 3
      + 129 * Y * y3 * s ^ 4

/-- The value `F(0⁺)` of the `x`-integral at `m → 0⁺`. -/
noncomputable def formXF0 (Y y3 : ℝ) : ℝ :=
  -Y * (-4 - 4 * Y ^ 2 - 2 * y3 + 8 * Y + Y * y3) / (4 * (-1 + Y))

/-- `e₁M(Y) = ∫₀^Y F(0⁺) dy₃`. -/
noncomputable def formXe1M (Y : ℝ) : ℝ := Y ^ 2 * (7 * Y ^ 2 - 14 * Y + 8) / (8 * (Y - 1))

/-- The `m`-derivative of the antiderivatives `P₁`, `P₂` at `x`. -/
noncomputable def formXDm (Y y3 m x : ℝ) : ℝ :=
  -formXUa Y y3 x / m ^ 2 - 2 * formXUb Y y3 x / m ^ 3 + formXK1 Y y3 x * x / m

/-- **`S = ∂F/∂m` below the switch**, in the threshold variable `s = m/g`. -/
noncomputable def formXS1 (Y y3 s : ℝ) : ℝ := formXN1 Y y3 s / (12 * y3 * (Y - 1) ^ 3)

/-- **`S = ∂F/∂m` above the switch**, in the threshold variable `s` (`e s² = m(1 - s)`). -/
noncomputable def formXS2 (Y y3 s : ℝ) : ℝ :=
  formXN2 Y y3 s / (12 * s ^ 3 * y3 * (y3 - Y) ^ 3 * (s - 2))

/-- **`S = ∂F/∂m`** as a function of the threshold `s`. -/
noncomputable def formXS (Y y3 s : ℝ) : ℝ :=
  if s ≤ cornInXs Y y3 then formXS1 Y y3 s else formXS2 Y y3 s

section

variable {Y y3 m : ℝ}

theorem formX_U11_eq (hm : m ≠ 0) :
    formXU11 Y y3 m = (Y * y3 * (-4 - 4 * Y ^ 2 - 2 * y3 + 8 * Y + Y * y3) / 4) / m + (-y3 * (2 - 4
        * Y + 3 * y3) / 4) := by
  unfold formXU11
  field_simp
  ring

theorem formX_U12_eq (hm : m ≠ 0) (hY : -1 + Y ≠ 0) :
    formXU12 Y y3 m = (-y3 * (2 - y3 - y3 ^ 2 - 12 * Y - 2 * Y ^ 3 + 11 * Y ^ 2 + Y * y3 ^ 2 - 5
        * y3 * Y ^ 2 + 5 * Y * y3) / 4) / m + ((2 + y3 ^ 2 - 22 * y3 - 4 * Y + 4 * Y ^ 2 + 6
        * y3 ^ 3 - 14 * y3 * Y ^ 2 - 9 * Y * y3 ^ 2 + 36 * Y * y3) / (8 * (-1 + Y))) := by
  unfold formXU12
  field_simp
  ring

theorem formX_U13_eq (hm : m ≠ 0) (hY : -1 + Y ≠ 0) :
    formXU13 Y y3 m = (y3 * (10 - 39 * y3 - 26 * Y + 4 * y3 ^ 2 + 7 * y3 ^ 3 + 12 * Y ^ 2 - 24 * y3
        * Y ^ 2 - 18 * Y * y3 ^ 2 + 72 * Y * y3) / 12) / m + (Y * y3 ^ 2 * (1 + y3) * (-2 + Y) * (1
        + y3 - 2 * Y) / 12) / m ^ 2 + (-(-1 + y3) * (15 - 209 * y3 - 30 * Y - 3 * y3 ^ 2 + 9
        * y3 ^ 3 + 24 * Y ^ 2 - 176 * y3 * Y ^ 2 - 6 * Y * y3 ^ 2 + 376 * Y * y3) / (72 * (-1
        + Y) ^ 2)) := by
  unfold formXU13
  field_simp
  ring

theorem formX_U14_eq (hm : m ≠ 0) (hY : -1 + Y ≠ 0) :
    formXU14 Y y3 m = (y3 * (-1 + y3) * (1 - Y - 6 * y3 + 5 * Y * y3) / 2) / m + (-y3 ^ 2 * (1 + y3)
        * (-1 + Y) * (-1 + y3) * (1 + y3 - 2 * Y) / 8) / m ^ 2 + (-y3 * (-1 + y3) ^ 2 / (-1
        + Y)) := by
  unfold formXU14
  field_simp
  ring

theorem formX_U15_eq (hm : m ≠ 0) :
    formXU15 Y y3 m = (-y3 ^ 2 * (-1 + y3) ^ 2) / m + (y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3
        - 2 * Y) / 8) / m ^ 2 := by
  unfold formXU15
  field_simp
  ring

theorem formX_U21_eq (hm : m ≠ 0) (h4 : y3 - Y ≠ 0) :
    formXU21 Y y3 m = (Y * y3 * (-4 - 4 * Y ^ 2 - 2 * y3 + 8 * Y + Y * y3) / 4) / m + (-(9 - 24
        * Y ^ 2 - 12 * y3 - 6 * Y + 4 * y3 ^ 3 + 5 * y3 ^ 4 + 24 * Y ^ 3 + 102 * y3 ^ 2 - 194 * Y
        * y3 ^ 2 - 108 * y3 * Y ^ 3 - 78 * Y * y3 - 22 * Y * y3 ^ 3 + 116 * Y ^ 2 * y3 ^ 2 + 184
        * y3 * Y ^ 2) / (24 * (y3 - Y) ^ 2)) := by
  unfold formXU21
  field_simp
  ring

theorem formX_U22_eq (hm : m ≠ 0) (h4 : y3 - Y ≠ 0) :
    formXU22 Y y3 m = (-y3 * (2 - y3 - y3 ^ 2 - 12 * Y - 2 * Y ^ 3 + 11 * Y ^ 2 + Y * y3 ^ 2 - 5
        * y3 * Y ^ 2 + 5 * Y * y3) / 4) / m + (-(-9 - 150 * y3 ^ 2 - 12 * Y ^ 3 + 16 * y3 ^ 4 + 18
        * y3 + 24 * Y ^ 2 + 86 * y3 ^ 3 - 190 * y3 * Y ^ 2 - 116 * Y * y3 ^ 3 + 42 * y3 * Y ^ 3 + 67
        * Y ^ 2 * y3 ^ 2 + 98 * Y * y3 ^ 2 + 126 * Y * y3) / (24 * (y3 - Y) ^ 2)) := by
  unfold formXU22
  field_simp
  ring

theorem formX_U23_eq (hm : m ≠ 0) (h4 : y3 - Y ≠ 0) :
    formXU23 Y y3 m = (y3 * (10 - 39 * y3 - 26 * Y + 4 * y3 ^ 2 + 7 * y3 ^ 3 + 12 * Y ^ 2 - 24 * y3
        * Y ^ 2 - 18 * Y * y3 ^ 2 + 72 * Y * y3) / 12) / m + (Y * y3 ^ 2 * (1 + y3) * (-2 + Y) * (1
        + y3 - 2 * Y) / 12) / m ^ 2 + (-(-1 + y3) * (-9 - 279 * y3 ^ 2 - 6 * Y + 15 * y3 + 24
        * Y ^ 2 + 85 * y3 ^ 3 - 176 * y3 * Y ^ 2 + 82 * Y * y3 ^ 2 + 264 * Y * y3) / (72 * (y3
        - Y) ^ 2)) := by
  unfold formXU23
  field_simp
  ring

theorem formX_U24_eq (hm : m ≠ 0) (h4 : y3 - Y ≠ 0) :
    formXU24 Y y3 m = (y3 * (-1 + y3) * (1 - Y - 6 * y3 + 5 * Y * y3) / 2) / m + (-y3 ^ 2 * (1 + y3)
        * (-1 + Y) * (-1 + y3) * (1 + y3 - 2 * Y) / 8) / m ^ 2 + (y3 * (-1 + y3) ^ 2 / (y3
        - Y)) := by
  unfold formXU24
  field_simp
  ring

theorem formX_U25_eq (hm : m ≠ 0) :
    formXU25 Y y3 m = (-y3 ^ 2 * (-1 + y3) ^ 2) / m + (y3 ^ 2 * (-1 + y3) ^ 2 * (1 + y3) * (1 + y3
        - 2 * Y) / 8) / m ^ 2 := by
  unfold formXU25
  field_simp
  ring

theorem formXU1_eq (hm : m ≠ 0) (hY : -1 + Y ≠ 0) (x : ℝ) :
    formXU1 Y y3 m x = formXUa Y y3 x / m + formXUb Y y3 x / m ^ 2 + formXZ1 Y y3 x := by
  rw [formXU1, formX_U11_eq hm, formX_U12_eq hm hY, formX_U13_eq hm hY, formX_U14_eq hm hY,
    formX_U15_eq hm]
  unfold formXUa formXUb formXZ1 formOSP6
  ring

theorem formXU2_eq (hm : m ≠ 0) (h4 : y3 - Y ≠ 0) (x : ℝ) :
    formXU2 Y y3 m x = formXUa Y y3 x / m + formXUb Y y3 x / m ^ 2 + formXZ2 Y y3 x := by
  rw [formXU2, formX_U21_eq hm h4, formX_U22_eq hm h4, formX_U23_eq hm h4, formX_U24_eq hm h4,
    formX_U25_eq hm]
  unfold formXUa formXUb formXZ2 formOSP6
  ring

theorem hasDerivAt_formXUa (Y y3 x : ℝ) :
    HasDerivAt (formXUa Y y3) (deriv (formXUa Y y3) x) x := by
  unfold formXUa
  exact (hasDerivAt_formOSP6 _ _ _ _ _ _ _ x).differentiableAt.hasDerivAt

theorem hasDerivAt_formXUb (Y y3 x : ℝ) :
    HasDerivAt (formXUb Y y3) (deriv (formXUb Y y3) x) x := by
  unfold formXUb
  exact (hasDerivAt_formOSP6 _ _ _ _ _ _ _ x).differentiableAt.hasDerivAt

/-- The `m`-dependence of `P₁`. -/
theorem formXP1_sub {m₀ : ℝ} (hm : m ≠ 0) (hm₀ : m₀ ≠ 0) (hY : -1 + Y ≠ 0) (x : ℝ) :
    formXP1 Y y3 m x - formXP1 Y y3 m₀ x = formXUa Y y3 x * (m⁻¹ - m₀⁻¹) +
      formXUb Y y3 x * ((m ^ 2)⁻¹ - (m₀ ^ 2)⁻¹) + formXK1 Y y3 x * x * (log m - log m₀) := by
  unfold formXP1
  rw [formXU1_eq hm hY, formXU1_eq hm₀ hY]
  ring

/-- The `m`-dependence of `P₂`. -/
theorem formXP2_sub {m₀ : ℝ} (hm : m ≠ 0) (hm₀ : m₀ ≠ 0) (h4 : y3 - Y ≠ 0) (x : ℝ) :
    formXP2 Y y3 m x - formXP2 Y y3 m₀ x = formXUa Y y3 x * (m⁻¹ - m₀⁻¹) +
      formXUb Y y3 x * ((m ^ 2)⁻¹ - (m₀ ^ 2)⁻¹) + formXK1 Y y3 x * x * (log m - log m₀) := by
  unfold formXP2
  rw [formXU2_eq hm h4, formXU2_eq hm₀ h4]
  ring

/-- **Below the switch** `F(m) = P₁(m/g)` is the polynomial `formXF1` in `m`. -/
theorem formXP1_eq_formXF1 (hm : m ≠ 0) (h3 : y3 ≠ 0) (hY : -1 + Y ≠ 0)
    (hg : cornerG y3 (Y - y3) ≠ 0) :
    formXP1 Y y3 m (m / cornerG y3 (Y - y3)) = formXF1 Y y3 m := by
  unfold formXP1
  rw [Real.log_div hm hg, formXU1_eq hm hY]
  have hgE : cornerG y3 (Y - y3) = y3 * (1 - Y) := by unfold cornerG; ring
  have hY' : 1 - Y ≠ 0 := by contrapose! hY; linarith
  rw [hgE]
  unfold formXUa formXUb formXZ1 formXF1 formOSP6
  field_simp
  ring

/-- **The derivative below the switch**: `F₁′(m) = S₁(m/g)`. -/
theorem hasDerivAt_formXF1 (h3 : y3 ≠ 0) (hY : -1 + Y ≠ 0) :
    HasDerivAt (formXF1 Y y3) (formXS1 Y y3 (m / cornerG y3 (Y - y3))) m := by
  unfold formXF1
  refine (hasDerivAt_formOSP6 _ _ _ _ _ _ _ m).congr_deriv ?_
  have hgE : cornerG y3 (Y - y3) = y3 * (1 - Y) := by unfold cornerG; ring
  have hY' : 1 - Y ≠ 0 := by contrapose! hY; linarith
  have hY'' : Y - 1 ≠ 0 := by contrapose! hY; linarith
  rw [hgE]
  unfold formXS1 formXN1 formOSP6
  field_simp
  ring

theorem formXF1_zero (Y y3 : ℝ) : formXF1 Y y3 0 = formXF0 Y y3 := by
  unfold formXF1 formXF0 formOSP6
  ring

/-- **`∫₀^Y F(0⁺) dy₃ = e₁M(Y)`.** -/
theorem integral_formXF0 (hY : Y ≠ 1) : ∫ y3 in (0 : ℝ)..Y, formXF0 Y y3 = formXe1M Y := by
  have hY' : -1 + Y ≠ 0 := by contrapose! hY; linarith
  have hY'' : Y - 1 ≠ 0 := sub_ne_zero.2 hY
  have h : ∀ y ∈ uIcc 0 Y, HasDerivAt
      (fun y => -Y * ((-4 - 4 * Y ^ 2 + 8 * Y) * y + (Y - 2) * y ^ 2 / 2) / (4 * (-1 + Y)))
      (formXF0 Y y) y := by
    intro y _
    have := ((((hasDerivAt_id y).const_mul (-4 - 4 * Y ^ 2 + 8 * Y)).add
      (((hasDerivAt_pow 2 y).const_mul (Y - 2)).div_const 2)).const_mul (-Y)).div_const
      (4 * (-1 + Y))
    refine this.congr_deriv ?_
    unfold formXF0
    field_simp
    ring
  have hc : Continuous (formXF0 Y) := by unfold formXF0; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (hc.intervalIntegrable _ _)]
  unfold formXe1M
  field_simp
  ring

end

section

variable {Y y3 s : ℝ}

theorem formX_S2_atoms {ua ub k1 a1 a2 c2 c3 e : ℝ} (he : e ≠ 0) (hs : s ≠ 0)
    (hs1 : 1 - s ≠ 0) (hs2 : s - 2 ≠ 0) :
    (-ua / (e * s ^ 2 / (1 - s)) ^ 2 - 2 * ub / (e * s ^ 2 / (1 - s)) ^ 3 +
        k1 * s / (e * s ^ 2 / (1 - s))) +
      ((a1 - c2 * s) / (e * s ^ 2 / (1 - s)) + (a2 * s - c3 * s ^ 2 / 2) / (e * s ^ 2 / (1 - s)) ^ 2
        + c2 / (e * s / (1 - s)) + c3 / (2 * (e * s / (1 - s)) ^ 2)) *
        ((1 - s) / (2 * e * s + e * s ^ 2 / (1 - s))) =
      -(s - 1) * (-a1 * e * s ^ 5 + 2 * a1 * e * s ^ 4 - a1 * e * s ^ 3 + a2 * s ^ 5 -
        3 * a2 * s ^ 4 + 3 * a2 * s ^ 3 - a2 * s ^ 2 + e ^ 2 * k1 * s ^ 6 - 2 * e ^ 2 * k1 * s ^ 5 +
        e * s ^ 4 * ua - 3 * e * s ^ 3 * ua + 2 * e * s ^ 2 * ua - 2 * s ^ 3 * ub + 8 * s ^ 2 * ub -
        10 * s * ub + 4 * ub) / (e ^ 3 * s ^ 6 * (s - 2)) := by
  have h2' : 2 - s ≠ 0 := by contrapose! hs2; linarith
  rw [show 2 * e * s + e * s ^ 2 / (1 - s) = e * s * (2 - s) / (1 - s) by field_simp; ring]
  field_simp
  ring

theorem formX_S2_poly :
    12 * (s - 1) * (-crossTA1 s y3 (Y - y3) * (y3 * (Y - y3)) * s ^ 5 +
        2 * crossTA1 s y3 (Y - y3) * (y3 * (Y - y3)) * s ^ 4 -
        crossTA1 s y3 (Y - y3) * (y3 * (Y - y3)) * s ^ 3 + crossTA2 s y3 (Y - y3) * s ^ 5 -
        3 * crossTA2 s y3 (Y - y3) * s ^ 4 + 3 * crossTA2 s y3 (Y - y3) * s ^ 3 -
        crossTA2 s y3 (Y - y3) * s ^ 2 + (y3 * (Y - y3)) ^ 2 * formXK1 Y y3 s * s ^ 6 -
        2 * (y3 * (Y - y3)) ^ 2 * formXK1 Y y3 s * s ^ 5 +
        (y3 * (Y - y3)) * s ^ 4 * formXUa Y y3 s - 3 * (y3 * (Y - y3)) * s ^ 3 * formXUa Y y3 s +
        2 * (y3 * (Y - y3)) * s ^ 2 * formXUa Y y3 s - 2 * s ^ 3 * formXUb Y y3 s +
        8 * s ^ 2 * formXUb Y y3 s - 10 * s * formXUb Y y3 s + 4 * formXUb Y y3 s) =
      formXN2 Y y3 s * y3 ^ 2 * s ^ 3 := by
  unfold crossTA1 crossTA2 crossTN1 crossTPa formXK1 formXUa formXUb formXN2 formOSP6
  ring

/-- **The derivative above the switch**: on the threshold `e s² = m(1 - s)`, the bulk term
`∂ₘP₂(m, s)` plus the weight at `s` times `s′(m) = (1 - s)/(2es + m)` is `S₂(s)`. -/
theorem formX_S2_id (h3 : y3 ≠ 0) (h4 : Y - y3 ≠ 0) (hs : s ≠ 0) (hs1 : 1 - s ≠ 0)
    (hs2 : s - 2 ≠ 0) :
    formXDm Y y3 (y3 * (Y - y3) * s ^ 2 / (1 - s)) s +
      (formXR Y y3 (y3 * (Y - y3) * s ^ 2 / (1 - s)) s +
        crossTC2 s y3 (Y - y3) / (y3 * (Y - y3) * s / (1 - s)) +
        crossTC3 s y3 (Y - y3) / (2 * (y3 * (Y - y3) * s / (1 - s)) ^ 2)) *
        ((1 - s) / (2 * (y3 * (Y - y3)) * s + y3 * (Y - y3) * s ^ 2 / (1 - s))) =
      formXS2 Y y3 s := by
  have he : y3 * (Y - y3) ≠ 0 := mul_ne_zero h3 h4
  unfold formXDm formXR
  rw [show 2 * (y3 * (Y - y3)) * s = 2 * (y3 * (Y - y3)) * s by ring,
    formX_S2_atoms he hs hs1 hs2]
  have hP := formX_S2_poly (Y := Y) (y3 := y3) (s := s)
  have h43 : y3 - Y ≠ 0 := by contrapose! h4; linarith
  unfold formXS2
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(y3 * (y3 - Y) ^ 3 * s ^ 3 * (s - 2))) * hP

end
end QED.ChainProof.SetCK

end
