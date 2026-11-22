/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3F
public import QED.ThreeLoopD.SetDMastersI13R4S

/-!
# Set (d), master `I₈`: the expansion of `F₃ - A₃` at infinity: definitions

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word of `Ψ₃` in the Lyndon basis and every basis function
other than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)` (`QED.ThreeLoopD.i13hpl_rho_01` and its
companions), each piece `Ψ₃⁽ᵍ⁾` and `-A₃(t(ξ))` becomes a singular part `S` (a polynomial in
`1/ξ` and `log ξ`) plus `ξ (Q₀ + Q₁ log ξ + Q₂ log² ξ + Q₃ log³ ξ)`, with polynomials `Qⱼ` in `ξ`
and the `ρ_w(ξ)`. This file defines `A₃(t(ξ))` (`QED.ThreeLoopD.i8Prim3x`), `F₃ - A₃` in `ξ`
(`QED.ThreeLoopD.i8D3`), and the parts `S`, `Qⱼ` of each piece.

## Main results

* `QED.ThreeLoopD.i8F3_sub_prim3`.
* `QED.ThreeLoopD.i8hw_0000`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

theorem i8hw_0000 (x : ℝ) : hpl [zero, zero, zero, zero] x = Real.log x ^ 4 / 24 := by
  rw [hpl_of_allZero (by decide)]
  simp [Nat.factorial]

/-- `A₃(t(ξ))`, with `log t = 2 log (1 - ξ) - log ξ`. -/
noncomputable def i8Prim3x (x : ℝ) : ℝ :=
    (-9 / 2) * (((1 - x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x) ^ 3) +
    (63 / 2) * (((1 - x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x) ^ 2) +
    (-99 + π ^ 2) * (((1 - x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x)) +
    (131 - 4 * zeta3 - 7 / 3 * π ^ 2) * ((1 - x) ^ 2 / x) +
    (-49 / 24) * (2 * Real.log (1 - x) - Real.log x) ^ 4 +
    (-11 / 4) * (2 * Real.log (1 - x) - Real.log x) ^ 3 +
    (203 / 8 + 5 / 6 * π ^ 2) * (2 * Real.log (1 - x) - Real.log x) ^ 2 +
    (-537 / 8 - 4 * zeta3 + 5 / 6 * π ^ 2) * (2 * Real.log (1 - x) - Real.log x)

/-- `F₃ - A₃` in terms of `ξ`. -/
noncomputable def i8D3 (x : ℝ) : ℝ := i8Psi3 x - i8Prim3x x

theorem i8F3_sub_prim3 {t : ℝ} (ht : 0 < t) : i8F3 t - i8Prim3 t = i8D3 (i13Xi t) := by
  have hT := (i13Xi_t ht.le).symm
  have hlog := (i8_log_eq ht).symm
  unfold i8D3 i8F3
  congr 1
  unfold i8Prim3x i8Prim3
  rw [hT, hlog]

/-- The singular part of `Ψ₃⁽a⁾` at `ξ = 0`. -/
noncomputable def i8L3Sa (x : ℝ) : ℝ :=
    (80 - 4 * zeta3 - 2 * π ^ 2 + 12 * Real.log x ^ 2 + 48 * Real.log x +
      4 / 3 * Real.log x ^ 3 + 133 / 16 * x - 3 * x * Real.log x ^ 3 -
      15 / 4 * x * Real.log x ^ 2 - 5 / 6 * x * Real.log x ^ 4 - 2 / 3 * Real.log x * π ^ 2 +
      5 / 4 * π ^ 2 * x + 153 / 8 * Real.log x * x + Real.log x * π ^ 2 * x / 2 +
      4 * Real.log x * x * zeta3 + 2 / 3 * π ^ 2 * x * Real.log x ^ 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₃⁽a⁾`. -/
noncomputable def i8L3Qa0 (x _r_0001 r_000m _r_001 _r_0011 _r_001m r_00m _r_00m1 r_00mm _r_01 _r_011
    _r_0111 _r_011m _r_01m _r_01m1 _r_01mm r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m r_0mm _r_0mm1 r_0mmm
    _r_1 r_m _r_m1 : ℝ) : ℝ :=
    637 / 24 - r_0mm - 4 * zeta3 - 379 / 48 * x ^ 3 - 111 / 8 * r_m - 35 / 16 * x ^ 5 -
      13 / 4 * r_0m - 5 / 2 * π ^ 2 - r_00m / 2 - x ^ 7 / 24 + x ^ 6 / 4 + 5 / 2 * x +
      33 / 8 * x ^ 2 + 73 / 12 * x ^ 4 + r_0m * x ^ 5 + r_m ^ 2 * x ^ 8 + r_m ^ 2 * x ^ 5 / 2 -
      r_m * x ^ 7 - 23 * r_m * x - 14 * r_m * x ^ 2 - 9 * r_00m * x ^ 2 - 8 * r_0mmm * x ^ 2 -
      4 * r_00mm * x ^ 2 - 3 * r_m ^ 2 * x ^ 6 - 2 * x * zeta3 + 2 * r_m ^ 2 * x ^ 4 +
      4 * r_00m * x + 4 * r_00m * x ^ 3 + 5 * r_0mm * x ^ 4 + 6 * r_m * x ^ 6 +
      6 * r_0m ^ 2 * x ^ 5 + 8 * r_0mm * x + 8 * r_0mm * x ^ 3 + 18 * r_0mm * x ^ 2 +
      22 * r_0m * x + 37 * r_0m * x ^ 3 + 46 * r_000m * x ^ 2 + 51 * r_0m * x ^ 2 -
      19 / 8 * r_m * x ^ 4 - 13 / 2 * r_m * x ^ 5 - 13 / 4 * r_m ^ 2 * x ^ 7 -
      7 / 12 * π ^ 2 * x - r_m ^ 2 * x ^ 9 / 2 - r_m ^ 3 * x ^ 6 / 3 - π ^ 2 * x ^ 3 / 4 -
      π ^ 2 * x ^ 2 / 6 + r_m ^ 3 * x ^ 10 / 3 + r_m * x ^ 8 / 4 + π ^ 2 * r_m / 6 +
      5 / 2 * r_00m * x ^ 4 + 7 / 2 * r_0m * x ^ 6 + 13 / 2 * r_m * x ^ 3 +
      13 / 4 * r_m ^ 2 * x ^ 3 + 37 / 4 * r_0m * x ^ 4 + π ^ 2 * r_m * x ^ 4 / 2 -
      r_0m * r_m * x ^ 3 - 24 * r_0m * r_m * x ^ 5 - 16 * r_0m * r_m * x ^ 4 -
      16 * r_0m * r_m * x ^ 6 - 7 * r_0m * r_m * x ^ 7 + 2 * π ^ 2 * r_m * x ^ 2 -
      2 / 3 * π ^ 2 * r_0m * x ^ 2 + 4 / 3 * π ^ 2 * r_m * x + 4 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₃⁽a⁾`. -/
noncomputable def i8L3Qa1 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m r_0mm _r_0mm1
    _r_0mmm _r_1 r_m _r_m1 : ℝ) : ℝ :=
    -11 / 2 - r_0m - x ^ 4 - 13 / 2 * r_m + 2 / 3 * π ^ 2 + 5 / 4 * x ^ 5 + 11 / 2 * x ^ 3 +
      15 / 2 * x + 25 / 2 * x ^ 2 - 73 * r_m * x ^ 2 - 52 * r_00m * x ^ 2 - 52 * r_m * x -
      38 * r_m * x ^ 3 - 16 * r_0m * x ^ 3 - 8 * r_0mm * x ^ 2 - 6 * r_0m * x ^ 2 -
      6 * r_m * x ^ 5 - 5 * r_m * x ^ 6 - 3 * r_0m * x ^ 4 + 3 * r_m ^ 2 * x ^ 3 +
      5 * r_m ^ 2 * x ^ 7 + 16 * r_m ^ 2 * x ^ 4 + 16 * r_m ^ 2 * x ^ 6 + 24 * r_m ^ 2 * x ^ 5 -
      23 / 2 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₃⁽a⁾`. -/
noncomputable def i8L3Qa2 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1
    _r_0mmm _r_1 r_m _r_m1 : ℝ) : ℝ :=
    13 - r_m - 5 * x ^ 2 + 7 * x - x ^ 3 / 2 + r_m * x ^ 4 - 12 * r_m * x + 12 * r_m * x ^ 3 +
      20 * r_0m * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₃⁽a⁾`. -/
noncomputable def i8L3Qa3 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -8 / 3 - x / 3

/-- The singular part of `Ψ₃⁽b⁾` at `ξ = 0`. -/
noncomputable def i8L3Sb (x : ℝ) : ℝ :=
    (40 + 2 * Real.log x ^ 3 + 14 * Real.log x ^ 2 + 40 * Real.log x + 52 * x - π ^ 2 / 3 -
      x * Real.log x ^ 4 - 24 * Real.log x * x - 4 * x * Real.log x ^ 2 -
      8 / 3 * x * Real.log x ^ 3 - 2 / 3 * π ^ 2 * x - Real.log x * π ^ 2 / 3 +
      π ^ 2 * x * Real.log x ^ 2 / 6 + 2 / 3 * Real.log x * π ^ 2 * x) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₃⁽b⁾`. -/
noncomputable def i8L3Qb0 (x r_0001 r_000m r_001 _r_0011 _r_001m r_00m _r_00m1 _r_00mm r_01 _r_011
    _r_0111 _r_011m _r_01m _r_01m1 _r_01mm r_0m r_0m01 r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1 _r_0mmm
    r_1 _r_m _r_m1 : ℝ) : ℝ :=
    23 - 18 * x ^ 2 - 39 / 4 * x - x ^ 5 / 2 + x ^ 3 / 4 + 4 / 3 * π ^ 2 - r_1 * x ^ 6 -
      28 * r_00m * x ^ 2 - 26 * r_1 * x ^ 3 - 19 * r_1 * x ^ 2 - 16 * r_0001 * x ^ 2 -
      16 * r_0m * x ^ 3 - 8 * r_01 * x ^ 3 - 4 * r_1 * x ^ 4 - 3 * r_0m * x ^ 4 +
      2 * r_01 * x ^ 4 + 2 * r_0m * x ^ 6 + 2 * r_1 * x ^ 5 + 4 * r_0m * x + 8 * r_001 * x ^ 2 +
      8 * r_0m * x ^ 5 + 8 * r_0m01 * x ^ 2 + 12 * r_000m * x ^ 2 + 19 * r_0m * x ^ 2 +
      32 * r_0m1 * x ^ 2 + 48 * r_1 * x + 86 * r_01 * x ^ 2 - 2 / 3 * π ^ 2 * x ^ 2 -
      π ^ 2 * x ^ 3 / 6 + π ^ 2 * x / 4 - 20 * r_0m * r_1 * x ^ 5 - 8 * r_01 * r_0m * x ^ 5 +
      4 * r_0m * r_1 * x ^ 7 + 8 * r_0m * r_1 * x ^ 4 + 8 * r_0m * r_1 * x ^ 6 -
      2 / 3 * π ^ 2 * r_1 * x - 2 / 3 * π ^ 2 * r_1 * x ^ 3 - π ^ 2 * r_1 * x ^ 4 / 3 +
      2 / 3 * π ^ 2 * r_01 * x ^ 2 + 5 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₃⁽b⁾`. -/
noncomputable def i8L3Qb1 (x _r_0001 _r_000m r_001 _r_0011 _r_001m r_00m _r_00m1 _r_00mm r_01 _r_011
    _r_0111 _r_011m r_01m _r_01m1 _r_01mm r_0m _r_0m01 r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1 _r_0mmm
    r_1 r_m r_m1 : ℝ) : ℝ :=
    -19 + x ^ 5 - 4 * x ^ 3 + 2 * x ^ 4 + 22 * x ^ 2 - 5 / 2 * x - π ^ 2 / 3 + r_m * x ^ 4 -
      70 * r_1 * x ^ 2 - 32 * r_m1 * x ^ 2 - 19 * r_m * x ^ 2 - 12 * r_00m * x ^ 2 -
      8 * r_01 * x ^ 2 - 8 * r_1 * x ^ 4 - 8 * r_m * x ^ 5 - 4 * r_m * x - 2 * r_m * x ^ 6 +
      2 * r_0m * x ^ 4 + 2 * r_1 * x ^ 6 + 4 * r_0m * x + 4 * r_0m * x ^ 3 + 8 * r_01m * x ^ 2 +
      8 * r_0m1 * x ^ 2 + 8 * r_m * x ^ 3 + 16 * r_001 * x ^ 2 + 20 * r_0m * x ^ 2 +
      24 * r_1 * x + 52 * r_1 * x ^ 3 - π ^ 2 * x / 6 - 8 * r_1 * r_m * x ^ 4 -
      8 * r_1 * r_m * x ^ 6 - 4 * r_1 * r_m * x ^ 7 + 20 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₃⁽b⁾`. -/
noncomputable def i8L3Qb2 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1
    _r_0mmm r_1 r_m _r_m1 : ℝ) : ℝ :=
    6 + x ^ 3 - 3 * x - 2 * x ^ 2 - 8 * r_01 * x ^ 2 - 6 * r_m * x ^ 2 - 4 * r_1 * x ^ 3 -
      4 * r_m * x - 4 * r_m * x ^ 3 - 2 * r_m * x ^ 4 + 4 * r_0m * x ^ 2 + 4 * r_1 * x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₃⁽b⁾`. -/
noncomputable def i8L3Qb3 (_x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -2

/-- The singular part of `Ψ₃⁽d⁾` at `ξ = 0`. -/
noncomputable def i8L3Sd (x : ℝ) : ℝ :=
    -57 / 4 + Real.log x ^ 2 + Real.log x ^ 3 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₃⁽d⁾`. -/
noncomputable def i8L3Qd0 (x _r_0001 _r_000m r_001 _r_0011 _r_001m r_00m _r_00m1 _r_00mm r_01 _r_011
    _r_0111 _r_011m r_01m _r_01m1 _r_01mm r_0m _r_0m01 r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1 _r_0mmm
    r_1 r_m _r_m1 : ℝ) : ℝ :=
    13 / 2 - 2 * x ^ 4 + 4 * x - 13 / 2 * x ^ 2 - 5 / 4 * x ^ 5 - 3 / 2 * r_m + x ^ 3 / 4 +
      r_1 * x ^ 5 - r_1 * x ^ 3 - 36 * r_01m * x ^ 2 - 20 * r_m * x - 14 * r_00m * x ^ 2 -
      4 * r_0m1 * x ^ 2 - 2 * r_001 * x ^ 2 + 9 * r_m * x ^ 5 + 11 * r_m * x ^ 3 +
      24 * r_0m * x ^ 2 + 26 * r_01 * x ^ 2 - 21 / 2 * r_m * x ^ 2 - 5 / 2 * r_1 * x ^ 6 +
      5 / 2 * r_1 * x ^ 2 + 5 / 2 * r_m * x ^ 6 + 19 / 2 * r_m * x ^ 4 - 8 * r_1 * r_m * x ^ 4 -
      5 * r_1 * r_m * x ^ 3 + 5 * r_1 * r_m * x ^ 7 + 8 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₃⁽d⁾`. -/
noncomputable def i8L3Qd1 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1
    _r_0mmm r_1 r_m r_m1 : ℝ) : ℝ :=
    -1 + x ^ 5 / 2 - 3 * r_m + 2 * x ^ 4 + 5 * x ^ 2 - 13 / 2 * x ^ 3 + 9 / 2 * x +
      r_1 * x ^ 6 - r_m * x ^ 6 - 32 * r_m1 * x ^ 2 - 22 * r_1 * x ^ 2 - 20 * r_m * x ^ 2 -
      15 * r_1 * x ^ 4 - 12 * r_m * x - 6 * r_m * x ^ 5 + 2 * r_01 * x ^ 2 + 2 * r_1 * x ^ 5 +
      4 * r_m * x ^ 4 + 14 * r_0m * x ^ 2 + 14 * r_m * x ^ 3 + 34 * r_1 * x ^ 3 -
      8 * r_1 * r_m * x ^ 4 - 8 * r_1 * r_m * x ^ 6 - 2 * r_1 * r_m * x ^ 3 -
      2 * r_1 * r_m * x ^ 7 + 20 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₃⁽d⁾`. -/
noncomputable def i8L3Qd2 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm _r_1 r_m _r_m1 : ℝ) : ℝ :=
    1 + x ^ 2 + x / 2 + x ^ 3 / 2 - r_m - r_m * x ^ 4 - 6 * r_m * x ^ 2 - 4 * r_m * x -
      4 * r_m * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₃⁽d⁾`. -/
noncomputable def i8L3Qd3 (_x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The singular part of `Ψ₃⁽e⁾` at `ξ = 0`. -/
noncomputable def i8L3Se (x : ℝ) : ℝ :=
    -23 / 16 + Real.log x ^ 2 / 8

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₃⁽e⁾`. -/
noncomputable def i8L3Qe0 (x _r_0001 r_000m _r_001 _r_0011 r_001m r_00m r_00m1 r_00mm r_01 _r_011
    _r_0111 _r_011m r_01m _r_01m1 r_01mm r_0m r_0m01 r_0m1 _r_0m11 r_0m1m r_0mm r_0mm1 _r_0mmm r_1
    r_m _r_m1 : ℝ) : ℝ :=
    5 / 4 - 5 / 2 * x ^ 2 - r_m / 2 - r_0m / 4 - x ^ 4 / 4 - x ^ 7 / 8 - x ^ 5 / 16 + x / 4 +
      x ^ 6 / 4 + 31 / 16 * x ^ 3 + r_01 * x ^ 4 + r_0m * x ^ 5 + r_1 * x ^ 7 + r_m * x ^ 3 +
      r_m * x ^ 5 + r_01 * x ^ 2 / 2 + r_0m * x ^ 6 / 2 + r_m * x ^ 8 / 2 +
      r_m ^ 2 * x ^ 5 / 2 - r_m * x ^ 6 - r_m ^ 2 * x ^ 6 - r_m ^ 2 * x ^ 8 - 4 * r_00mm * x ^ 2 -
      4 * r_01 * x ^ 3 - 4 * r_m * x ^ 4 - 3 * r_0m * x ^ 3 - 2 * r_01m * x ^ 2 - 2 * r_0m * x -
      2 * r_0m1 * x ^ 2 - 2 * r_0mm * x ^ 2 - 2 * r_1 * x ^ 6 - 2 * r_m * x + 2 * r_000m * x ^ 2 +
      2 * r_00m * x ^ 2 + 2 * r_m ^ 2 * x ^ 4 + 4 * r_001m * x ^ 2 + 4 * r_00m1 * x ^ 2 +
      4 * r_0m01 * x ^ 2 + 5 * r_m * x ^ 2 + 8 * r_01mm * x ^ 2 + 8 * r_0m1m * x ^ 2 +
      8 * r_0mm1 * x ^ 2 - 13 / 4 * r_1 * x ^ 2 - 9 / 2 * r_1 * x ^ 4 - 5 / 2 * r_0m * x ^ 2 -
      3 / 4 * r_0m * x ^ 4 - r_m ^ 2 * x ^ 9 / 2 - r_1 * x ^ 8 / 4 - r_m ^ 2 * x ^ 7 / 4 +
      r_m ^ 2 * x ^ 3 / 4 + 7 / 2 * r_1 * x ^ 5 + 11 / 2 * r_1 * x ^ 3 + r_0m * r_1 * x ^ 7 +
      r_1 * r_m * x ^ 9 + r_1 * r_m ^ 2 * x ^ 6 - r_0m * r_1 * x ^ 3 - r_1 * r_m * x ^ 5 -
      r_1 * r_m ^ 2 * x ^ 10 - 4 * r_01 * r_0m * x ^ 5 - 2 * r_1 * r_m * x ^ 6 -
      2 * r_1 * r_m * x ^ 8 + 4 * r_1 * r_m * x ^ 4 - 3 / 2 * r_1 * r_m * x ^ 3 +
      3 / 2 * r_1 * r_m * x ^ 7

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₃⁽e⁾`. -/
noncomputable def i8L3Qe1 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m r_0mm _r_0mm1
    _r_0mmm _r_1 r_m _r_m1 : ℝ) : ℝ :=
    -1 / 4 + x ^ 4 / 2 - x ^ 3 - 3 / 4 * r_m - 3 / 4 * x - r_0m / 2 - x ^ 5 / 8 +
      7 / 4 * x ^ 2 + r_0m * x ^ 4 / 2 + r_m * x ^ 6 / 2 + r_m ^ 2 * x ^ 3 / 2 - r_0m * x ^ 2 -
      r_m * x ^ 3 - r_m * x ^ 5 - 2 * r_00m * x ^ 2 + 2 * r_m * x + 4 * r_0mm * x ^ 2 -
      r_m * x ^ 2 / 2 - r_m ^ 2 * x ^ 7 / 2 + 3 / 4 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₃⁽e⁾`. -/
noncomputable def i8L3Qe2 (_x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₃⁽e⁾`. -/
noncomputable def i8L3Qe3 (_x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The singular part of `Ψ₃⁽f⁾` at `ξ = 0`. -/
noncomputable def i8L3Sf (x : ℝ) : ℝ :=
    (10 + Real.log x ^ 3 + 5 * Real.log x ^ 2 + 10 * Real.log x + 16 * x -
      4 * x * Real.log x ^ 2 - 2 / 3 * x * Real.log x ^ 3 - x * Real.log x ^ 4 / 4) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₃⁽f⁾`. -/
noncomputable def i8L3Qf0 (x r_0001 _r_000m r_001 r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01 r_011
    _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1
    _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -22 - 14 * x ^ 2 - 4 * x ^ 4 - 51 / 8 * x - 21 / 4 * x ^ 3 - 5 / 4 * x ^ 5 -
      24 * r_1 * x ^ 3 - 20 * r_001 * x ^ 2 - 11 * r_1 ^ 2 * x ^ 5 - 8 * r_0001 * x ^ 2 -
      6 * r_1 * x ^ 4 - 6 * r_1 * x ^ 5 - 5 * r_1 * x ^ 6 - 5 * r_1 ^ 2 * x ^ 7 +
      4 * r_1 ^ 2 * x ^ 6 + 8 * r_0011 * x ^ 2 + 12 * r_1 ^ 2 * x ^ 4 + 16 * r_1 * x +
      25 * r_1 * x ^ 2 + 36 * r_011 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₃⁽f⁾`. -/
noncomputable def i8L3Qf1 (x _r_0001 _r_000m r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm r_01 r_011
    _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1
    _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    14 + x ^ 5 / 2 - 3 * x ^ 2 + 3 * x ^ 4 - 13 / 4 * x + 3 / 2 * x ^ 3 - 16 * r_1 * x ^ 2 -
      10 * r_1 ^ 2 * x ^ 5 - 8 * r_011 * x ^ 2 - 6 * r_1 * x ^ 4 - 4 * r_1 * x ^ 3 +
      2 * r_1 * x ^ 6 + 2 * r_1 ^ 2 * x ^ 7 + 4 * r_1 ^ 2 * x ^ 4 + 4 * r_1 ^ 2 * x ^ 6 +
      8 * r_001 * x ^ 2 + 8 * r_1 * x ^ 5 + 16 * r_1 * x + 20 * r_01 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₃⁽f⁾`. -/
noncomputable def i8L3Qf2 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -7 + x ^ 3 + 4 * x ^ 2 - 11 / 4 * x - 10 * r_1 * x ^ 2 - 4 * r_01 * x ^ 2 + 2 * r_1 * x ^ 4 +
      4 * r_1 * x + 4 * r_1 * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₃⁽f⁾`. -/
noncomputable def i8L3Qf3 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    1 + x / 2

/-- The singular part of `Ψ₃⁽g⁾` at `ξ = 0`. -/
noncomputable def i8L3Sg (x : ℝ) : ℝ :=
    -23 / 16 + Real.log x ^ 3 / 12

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₃⁽g⁾`. -/
noncomputable def i8L3Qg0 (x _r_0001 r_000m r_001 _r_0011 r_001m r_00m r_00m1 _r_00mm r_01 r_011
    _r_0111 r_011m r_01m r_01m1 _r_01mm r_0m _r_0m01 r_0m1 r_0m11 _r_0m1m _r_0mm _r_0mm1 _r_0mmm r_1
    r_m _r_m1 : ℝ) : ℝ :=
    -13 / 8 - x ^ 4 / 4 - x ^ 6 / 4 - r_m / 8 - x ^ 7 / 8 + 9 / 8 * x ^ 2 + 15 / 16 * x ^ 3 +
      21 / 16 * x + r_m * x ^ 7 + r_1 ^ 2 * x ^ 8 - r_001 * x ^ 2 - r_00m * x ^ 2 -
      8 * r_011m * x ^ 2 - 8 * r_01m1 * x ^ 2 - 8 * r_0m11 * x ^ 2 - 2 * r_000m * x ^ 2 -
      2 * r_m * x - 2 * r_1 ^ 2 * x ^ 5 + 2 * r_01 * x ^ 2 + 2 * r_011 * x ^ 2 +
      2 * r_01m * x ^ 2 + 2 * r_0m1 * x ^ 2 + 3 * r_1 ^ 2 * x ^ 6 + 4 * r_001m * x ^ 2 +
      4 * r_00m1 * x ^ 2 + 5 * r_1 * x ^ 4 - 13 / 4 * r_m * x ^ 2 - 9 / 2 * r_1 * x ^ 3 -
      3 / 2 * r_1 ^ 2 * x ^ 7 - r_1 * x ^ 5 / 2 - r_1 * x ^ 8 / 2 - r_m * x ^ 3 / 2 -
      r_1 ^ 2 * x ^ 9 / 2 + r_1 * x ^ 2 / 4 + r_1 * x ^ 6 / 4 + r_m * x ^ 8 / 4 +
      3 / 2 * r_m * x ^ 5 + 5 / 2 * r_0m * x ^ 2 + 5 / 4 * r_m * x ^ 6 + 15 / 8 * r_m * x ^ 4 +
      r_1 * r_m * x ^ 9 + r_m * r_1 ^ 2 * x ^ 10 + r_1 * r_m * x ^ 7 / 2 - r_1 * r_m * x ^ 5 -
      r_m * r_1 ^ 2 * x ^ 6 - 4 * r_1 * r_m * x ^ 4 + 2 * r_1 * r_m * x ^ 6 +
      2 * r_1 * r_m * x ^ 8 - r_1 * r_m * x ^ 3 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₃⁽g⁾`. -/
noncomputable def i8L3Qg1 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m r_00m _r_00m1 _r_00mm r_01
    _r_011 _r_0111 _r_011m r_01m _r_01m1 _r_01mm r_0m _r_0m01 r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1
    _r_0mmm r_1 r_m _r_m1 : ℝ) : ℝ :=
    7 / 4 - r_m / 4 - x ^ 2 / 4 - x ^ 5 / 4 + x / 4 + x ^ 3 / 8 + r_01 * x ^ 2 + r_0m * x ^ 2 +
      r_1 * x ^ 5 + r_m * x ^ 3 + r_m * x ^ 5 + r_m * x ^ 6 / 2 - 4 * r_01m * x ^ 2 -
      4 * r_0m1 * x ^ 2 - 2 * r_1 * x ^ 2 - 2 * r_m * x + 2 * r_00m * x ^ 2 + 3 * r_1 * x ^ 3 -
      3 / 2 * r_1 * x ^ 4 - r_1 * x ^ 6 / 2 - r_m * x ^ 2 / 2 + r_m * x ^ 4 / 4 +
      r_1 * r_m * x ^ 7 - r_1 * r_m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₃⁽g⁾`. -/
noncomputable def i8L3Qg2 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1
    _r_0mmm _r_1 r_m _r_m1 : ℝ) : ℝ :=
    -1 / 4 - r_m / 4 - x / 8 - x ^ 3 / 8 + x ^ 2 / 4 - r_0m * x ^ 2 + r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₃⁽g⁾`. -/
noncomputable def i8L3Qg3 (_x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The singular part of `Ψ₃⁽h⁾` at `ξ = 0`. -/
noncomputable def i8L3Sh (x : ℝ) : ℝ :=
    (1 + Real.log x + Real.log x ^ 2 / 2 + 2 * x + Real.log x ^ 3 / 6 - x * Real.log x ^ 3 / 3 +
      x * Real.log x ^ 4 / 24) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₃⁽h⁾`. -/
noncomputable def i8L3Qh0 (x r_0001 _r_000m r_001 r_0011 _r_001m _r_00m _r_00m1 _r_00mm r_01 r_011
    r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1
    _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    2 - 47 / 48 * x - 7 / 4 * x ^ 2 - 5 / 3 * x ^ 3 - 3 / 8 * x ^ 5 - x ^ 4 / 2 - x ^ 6 / 3 -
      x ^ 7 / 12 + r_001 * x ^ 2 + r_1 ^ 2 * x ^ 7 / 2 - r_1 * x ^ 7 - r_1 ^ 2 * x ^ 9 -
      4 * r_0011 * x ^ 2 - 4 * r_1 ^ 2 * x ^ 6 - 2 * r_011 * x ^ 2 - 2 * r_1 * x ^ 5 -
      2 * r_1 ^ 3 * x ^ 8 + 2 * r_0001 * x ^ 2 + 2 * r_1 * x + 2 * r_1 * x ^ 3 +
      2 * r_1 ^ 2 * x ^ 4 + 8 * r_0111 * x ^ 2 - 15 / 4 * r_1 * x ^ 4 - 5 / 2 * r_01 * x ^ 2 -
      2 / 3 * r_1 ^ 3 * x ^ 10 - r_1 * x ^ 8 / 2 + 4 / 3 * r_1 ^ 3 * x ^ 7 +
      4 / 3 * r_1 ^ 3 * x ^ 9 + 5 / 2 * r_1 ^ 2 * x ^ 5 + 13 / 4 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₃⁽h⁾`. -/
noncomputable def i8L3Qh1 (x _r_0001 _r_000m r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm r_01 r_011
    _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm _r_0mm1
    _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -2 - x ^ 2 - 11 / 8 * x - x ^ 4 / 2 - x ^ 5 / 4 + r_1 * x ^ 4 / 2 - r_01 * x ^ 2 -
      r_1 * x ^ 6 - r_1 ^ 2 * x ^ 7 - 4 * r_1 * x ^ 3 - 3 * r_1 ^ 2 * x ^ 5 - 2 * r_001 * x ^ 2 +
      2 * r_1 * x + 2 * r_1 ^ 2 * x ^ 4 + 2 * r_1 ^ 2 * x ^ 6 + 4 * r_011 * x ^ 2 +
      5 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₃⁽h⁾`. -/
noncomputable def i8L3Qh2 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -x ^ 3 / 4 + 3 / 8 * x + r_01 * x ^ 2 + r_1 * x + r_1 * x ^ 3 - 3 / 2 * r_1 * x ^ 2 -
      r_1 * x ^ 4 / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₃⁽h⁾`. -/
noncomputable def i8L3Qh3 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    1 / 6 - x / 12

/-- The singular part of `-A₃` at `ξ = 0`. -/
noncomputable def i8L3SP (x : ℝ) : ℝ :=
    (-131 - 99 * Real.log x + 4 * zeta3 + 64 * x - 63 / 2 * Real.log x ^ 2 -
      9 / 2 * Real.log x ^ 3 + 7 / 3 * π ^ 2 + Real.log x * π ^ 2 - 8 * x * zeta3 -
      8 / 3 * π ^ 2 * x + 25 / 4 * x * Real.log x ^ 3 + 39 / 8 * Real.log x * x +
      49 / 24 * x * Real.log x ^ 4 + 85 / 8 * x * Real.log x ^ 2 - 4 * Real.log x * x * zeta3 -
      7 / 6 * Real.log x * π ^ 2 * x - 5 / 6 * π ^ 2 * x * Real.log x ^ 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `-A₃`. -/
noncomputable def i8L3QP0 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -377 / 4 + π ^ 2 - 110 * x ^ 2 - 4 * zeta3 - 1049 / 24 * x ^ 3 - 629 / 8 * x +
      49 / 24 * x ^ 7 + 71 / 6 * x ^ 6 + 77 / 6 * x ^ 4 + 113 / 4 * x ^ 5 - 198 * r_1 * x -
      131 * r_1 * x ^ 3 - 126 * r_1 ^ 2 * x ^ 4 - 36 * r_1 ^ 3 * x ^ 7 - 30 * r_1 ^ 2 * x ^ 6 -
      4 * x * zeta3 + 49 * r_1 ^ 2 * x ^ 9 + 50 * r_1 ^ 3 * x ^ 8 + 71 * r_1 * x ^ 7 +
      142 * r_1 ^ 2 * x ^ 8 + 163 * r_1 ^ 2 * x ^ 7 - 119 / 2 * r_1 * x ^ 4 -
      7 / 3 * π ^ 2 * x ^ 2 - 5 / 2 * π ^ 2 * x - 5 / 6 * π ^ 2 * x ^ 3 + 39 / 4 * r_1 * x ^ 2 +
      49 / 3 * r_1 * x ^ 8 + 59 / 3 * r_1 * x ^ 5 + 85 / 2 * r_1 ^ 2 * x ^ 5 +
      98 / 3 * r_1 ^ 4 * x ^ 11 + 196 / 3 * r_1 ^ 3 * x ^ 10 + 251 / 2 * r_1 * x ^ 6 +
      284 / 3 * r_1 ^ 3 * x ^ 9 - 8 * r_1 * zeta3 * x ^ 2 + 2 * π ^ 2 * r_1 * x -
      14 / 3 * π ^ 2 * r_1 * x ^ 3 - 10 / 3 * π ^ 2 * r_1 * x ^ 4 -
      10 / 3 * π ^ 2 * r_1 ^ 2 * x ^ 5 - 7 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `-A₃`. -/
noncomputable def i8L3QP1 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -131 / 2 - 119 / 4 * x - 7 / 3 * π ^ 2 + 49 / 6 * x ^ 5 + 59 / 6 * x ^ 2 + 71 / 2 * x ^ 4 +
      251 / 4 * x ^ 3 - 126 * r_1 * x - 54 * r_1 ^ 2 * x ^ 4 - 30 * r_1 * x ^ 3 +
      49 * r_1 * x ^ 6 + 75 * r_1 ^ 2 * x ^ 5 + 98 * r_1 ^ 2 * x ^ 7 + 142 * r_1 * x ^ 5 +
      142 * r_1 ^ 2 * x ^ 6 + 163 * r_1 * x ^ 4 - 5 / 3 * π ^ 2 * x + 85 / 2 * r_1 * x ^ 2 +
      196 / 3 * r_1 ^ 3 * x ^ 8 - 10 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `-A₃`. -/
noncomputable def i8L3QP2 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -15 / 2 + 49 / 4 * x ^ 3 + 71 / 2 * x ^ 2 + 163 / 4 * x - 27 * r_1 * x + 49 * r_1 * x ^ 4 +
      49 * r_1 ^ 2 * x ^ 5 + 71 * r_1 * x ^ 3 + 75 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `-A₃`. -/
noncomputable def i8L3QP3 (x _r_0001 _r_000m _r_001 _r_0011 _r_001m _r_00m _r_00m1 _r_00mm _r_01
    _r_011 _r_0111 _r_011m _r_01m _r_01m1 _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m11 _r_0m1m _r_0mm
    _r_0mm1 _r_0mmm r_1 _r_m _r_m1 : ℝ) : ℝ :=
    71 / 6 + 49 / 6 * x + 49 / 3 * r_1 * x ^ 2

end QED.ThreeLoopD
