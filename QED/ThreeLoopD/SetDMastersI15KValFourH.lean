/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValFourAsym
public import QED.Polylog.Basic
public import QED.Polylog.Zeta5
import QED.Polylog.HPLValues
import QED.Polylog.HPLValues3
import QED.Polylog.HPLValues4
import QED.Polylog.HPLValues5
import QED.Polylog.HPLValuesAlt4
import QED.Polylog.HPLValuesAlt5A
import QED.Polylog.HPLValuesAlt5B
import QED.Polylog.HPLValuesAlt5C
import QED.Polylog.HPLValuesAlt5D
import QED.Polylog.HPLValuesTrailing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₅`: the outer integral of the `u`-weighted half of `F₄`

Write `H(w) = H(w; u)` for the harmonic polylogarithms (`QED.Polylog.HPL.hpl`). The inner
`x`-integral `h₄(u) = ∫₀¹ A₂₃,₄(x, u) dx` of the `u`-weighted half
`A₂₃,₄ = (v² b₁⁴ - b₂⁴) / (24 u)` of `F₄` (`QED.ThreeLoopD.i15A23k 4`, `v = 1 - u`) is,
numerically to about `500` digits (`setDI15i/fit4.py`: an exact interpolation at dps `700` in the
HPL basis of weight `≤ 4` with coefficients `1/u, 1, u`, `363` unknowns, checked at `17` further
points; every coefficient is an integer combination of `1, π², ζ(3), π⁴`), the sum
`Σ (aₜ/u + bₜ + cₜ u) H(wₜ)` of `QED.ThreeLoopD.i15H4D` (`43` words of weight `≤ 4`).

This file defines that function (`QED.ThreeLoopD.i15H4`) and proves
`∫₀¹ h₄ = 12 ζ(5) - 2 π² ζ(3)/3 + 3 π⁴/80 + 8 π² log 2 - 119 π²/16 - 41 ζ(3)/2 + 1117/32`,
the expected value of `∫∫ A₂₃,₄`, by an explicit primitive `Σ qₜ(u) H(wₜ; u)` (quadratic `qₜ`,
words of weight `≤ 5`) and the HPL values at `1` of weight `≤ 5` (in which `Li₄(1/2)`,
`Li₅(1/2)` and the odd powers of `log 2` cancel). The identification `∫₀¹ A₂₃,₄ dx = h₄(u)` is
not proved here.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i15H4Phi`: the primitive.
* `QED.ThreeLoopD.integral_i15H4`: the value of `∫₀¹ h₄`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The terms `(qₜ, wₜ)` of `h₄ = Σ qₜ(u) H(wₜ; u)`, `qₜ = (a, b, c, d) ↦ a/u + b + c u + d u²`. -/
noncomputable def i15H4D : List ((ℝ × ℝ × ℝ × ℝ) × List Letter) :=
  [((
      0,
      (-32 - 24 * zeta3 + π ^ 4 / 20 + 4 * π ^ 2 / 3),
      (16 + 28 * zeta3 - 2 * π ^ 2 / 3 - π ^ 4 / 40),
      0),
     []),
   ((0, (16 - 4 * zeta3 - 2 * π ^ 2 / 3), (-24 + π ^ 2 + 6 * zeta3), 0), [zero]),
   (((-16 * zeta3), 0, 16 * zeta3, 0), [one]),
   ((32 * zeta3, 0, (-32 * zeta3), 0), [negOne]),
   ((0, (8 - π ^ 2 / 3), (-12 + π ^ 2 / 2), 0), [zero, zero]),
   (((16 - 2 * π ^ 2 / 3), 0, (-16 + 2 * π ^ 2 / 3), 0), [one, zero]),
   (((-32 + 4 * π ^ 2 / 3), 0, (32 - 4 * π ^ 2 / 3), 0), [negOne, zero]),
   ((0, 4, (-6), 0), [zero, zero, zero]),
   ((8, 16, (-24), 0), [zero, one, zero]),
   (((-16), (-32), 48, 0), [zero, negOne, zero]),
   ((8, 0, (-8), 0), [one, zero, zero]),
   ((16, 0, (-16), 0), [one, one, zero]),
   (((-32), 0, 32, 0), [one, negOne, zero]),
   (((-16), 0, 16, 0), [negOne, zero, zero]),
   (((-32), 0, 32, 0), [negOne, one, zero]),
   ((64, 0, (-64), 0), [negOne, negOne, zero]),
   ((0, 2, (-3), 0), [zero, zero, zero, zero]),
   ((4, 8, (-12), 0), [zero, zero, one, zero]),
   (((-8), (-16), 24, 0), [zero, zero, negOne, zero]),
   ((4, 8, (-12), 0), [zero, one, zero, zero]),
   ((8, 16, (-24), 0), [zero, one, one, zero]),
   (((-16), (-32), 48, 0), [zero, one, negOne, zero]),
   (((-8), (-16), 24, 0), [zero, negOne, zero, zero]),
   (((-16), (-32), 48, 0), [zero, negOne, one, zero]),
   ((32, 64, (-96), 0), [zero, negOne, negOne, zero]),
   ((4, 0, (-4), 0), [one, zero, zero, zero]),
   ((16, 0, (-16), 0), [one, zero, one, zero]),
   (((-32), 0, 32, 0), [one, zero, negOne, zero]),
   ((8, 0, (-8), 0), [one, one, zero, zero]),
   ((16, 0, (-16), 0), [one, one, one, zero]),
   (((-32), 0, 32, 0), [one, one, negOne, zero]),
   (((-16), 0, 16, 0), [one, negOne, zero, zero]),
   (((-32), 0, 32, 0), [one, negOne, one, zero]),
   ((64, 0, (-64), 0), [one, negOne, negOne, zero]),
   (((-8), 0, 8, 0), [negOne, zero, zero, zero]),
   (((-32), 0, 32, 0), [negOne, zero, one, zero]),
   ((64, 0, (-64), 0), [negOne, zero, negOne, zero]),
   (((-16), 0, 16, 0), [negOne, one, zero, zero]),
   (((-32), 0, 32, 0), [negOne, one, one, zero]),
   ((64, 0, (-64), 0), [negOne, one, negOne, zero]),
   ((32, 0, (-32), 0), [negOne, negOne, zero, zero]),
   ((64, 0, (-64), 0), [negOne, negOne, one, zero]),
   (((-128), 0, 128, 0), [negOne, negOne, negOne, zero])]

/-- **The inner integral `h₄(u)` of `A₂₃,₄`**, in harmonic polylogarithms. -/
noncomputable def i15H4 (u : ℝ) : ℝ := i15T3Sum i15H4D u

/-- The expected value of `∫∫ A₂₃,₄`. -/
noncomputable def i15H4Val : ℝ :=
  12 * zeta5 - 2 * π ^ 2 * zeta3 / 3 + 3 * π ^ 4 / 80 + 8 * π ^ 2 * log 2 - 119 * π ^ 2 / 16 -
    41 * zeta3 / 2 + 1117 / 32

/-- The terms `(qₜ, wₜ)` of the primitive of `h₄`. -/
noncomputable def i15H4L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter) :=
  [((
      0,
      0,
      (21 / 2 - 28 * zeta3 + 2 * π ^ 2 + π ^ 4 / 20),
      (781 / 32 - 37 * π ^ 2 / 48 - π ^ 4 / 80 + 49 * zeta3 / 2)),
     []),
   ((0, 0, (-85 / 2 - 4 * zeta3 - 2 * π ^ 2 / 3), (-525 / 16 + 3 * zeta3 + 7 * π ^ 2 / 8)), [zero]),
   ((0, (-8 * zeta3), 0, 8 * zeta3), [one]),
   ((0, 16 * zeta3, 0, (-16 * zeta3)), [negOne]),
   ((0, 0, (-1 - π ^ 2 / 3), (-111 / 8 + π ^ 2 / 4)), [zero, zero]),
   ((0, (-16 * zeta3), 0, 0), [zero, one]),
   ((0, 32 * zeta3, 0, 0), [zero, negOne]),
   ((0, (89 / 2 - π ^ 2 / 3), (-26), (-37 / 2 + π ^ 2 / 3)), [one, zero]),
   ((0, (15 + 2 * π ^ 2 / 3), 52, (37 - 2 * π ^ 2 / 3)), [negOne, zero]),
   ((0, 0, 4, (-21 / 4)), [zero, zero, zero]),
   ((0, (16 - 2 * π ^ 2 / 3), 16, (-21)), [zero, one, zero]),
   ((0, (-32 + 4 * π ^ 2 / 3), (-32), 42), [zero, negOne, zero]),
   ((0, 11, (-4), (-7)), [one, zero, zero]),
   ((0, 22, (-8), (-14)), [one, one, zero]),
   ((0, (-44), 16, 28), [one, negOne, zero]),
   ((0, (-6), 8, 14), [negOne, zero, zero]),
   ((0, (-12), 16, 28), [negOne, one, zero]),
   ((0, 24, (-32), (-56)), [negOne, negOne, zero]),
   ((0, 0, 2, (-3 / 2)), [zero, zero, zero, zero]),
   ((0, 8, 8, (-6)), [zero, zero, one, zero]),
   ((0, (-16), (-16), 12), [zero, zero, negOne, zero]),
   ((0, 8, 8, (-6)), [zero, one, zero, zero]),
   ((0, 16, 16, (-12)), [zero, one, one, zero]),
   ((0, (-32), (-32), 24), [zero, one, negOne, zero]),
   ((0, (-16), (-16), 12), [zero, negOne, zero, zero]),
   ((0, (-32), (-32), 24), [zero, negOne, one, zero]),
   ((0, 64, 64, (-48)), [zero, negOne, negOne, zero]),
   ((0, 2, 0, (-2)), [one, zero, zero, zero]),
   ((0, 8, 0, (-8)), [one, zero, one, zero]),
   ((0, (-16), 0, 16), [one, zero, negOne, zero]),
   ((0, 4, 0, (-4)), [one, one, zero, zero]),
   ((0, 8, 0, (-8)), [one, one, one, zero]),
   ((0, (-16), 0, 16), [one, one, negOne, zero]),
   ((0, (-8), 0, 8), [one, negOne, zero, zero]),
   ((0, (-16), 0, 16), [one, negOne, one, zero]),
   ((0, 32, 0, (-32)), [one, negOne, negOne, zero]),
   ((0, (-4), 0, 4), [negOne, zero, zero, zero]),
   ((0, (-16), 0, 16), [negOne, zero, one, zero]),
   ((0, 32, 0, (-32)), [negOne, zero, negOne, zero]),
   ((0, (-8), 0, 8), [negOne, one, zero, zero]),
   ((0, (-16), 0, 16), [negOne, one, one, zero]),
   ((0, 32, 0, (-32)), [negOne, one, negOne, zero]),
   ((0, 16, 0, (-16)), [negOne, negOne, zero, zero]),
   ((0, 32, 0, (-32)), [negOne, negOne, one, zero]),
   ((0, (-64), 0, 64), [negOne, negOne, negOne, zero]),
   ((0, 4, 0, 0), [zero, zero, zero, one, zero]),
   ((0, (-8), 0, 0), [zero, zero, zero, negOne, zero]),
   ((0, 4, 0, 0), [zero, zero, one, zero, zero]),
   ((0, 8, 0, 0), [zero, zero, one, one, zero]),
   ((0, (-16), 0, 0), [zero, zero, one, negOne, zero]),
   ((0, (-8), 0, 0), [zero, zero, negOne, zero, zero]),
   ((0, (-16), 0, 0), [zero, zero, negOne, one, zero]),
   ((0, 32, 0, 0), [zero, zero, negOne, negOne, zero]),
   ((0, 4, 0, 0), [zero, one, zero, zero, zero]),
   ((0, 16, 0, 0), [zero, one, zero, one, zero]),
   ((0, (-32), 0, 0), [zero, one, zero, negOne, zero]),
   ((0, 8, 0, 0), [zero, one, one, zero, zero]),
   ((0, 16, 0, 0), [zero, one, one, one, zero]),
   ((0, (-32), 0, 0), [zero, one, one, negOne, zero]),
   ((0, (-16), 0, 0), [zero, one, negOne, zero, zero]),
   ((0, (-32), 0, 0), [zero, one, negOne, one, zero]),
   ((0, 64, 0, 0), [zero, one, negOne, negOne, zero]),
   ((0, (-8), 0, 0), [zero, negOne, zero, zero, zero]),
   ((0, (-32), 0, 0), [zero, negOne, zero, one, zero]),
   ((0, 64, 0, 0), [zero, negOne, zero, negOne, zero]),
   ((0, (-16), 0, 0), [zero, negOne, one, zero, zero]),
   ((0, (-32), 0, 0), [zero, negOne, one, one, zero]),
   ((0, 64, 0, 0), [zero, negOne, one, negOne, zero]),
   ((0, 32, 0, 0), [zero, negOne, negOne, zero, zero]),
   ((0, 64, 0, 0), [zero, negOne, negOne, one, zero]),
   ((0, (-128), 0, 0), [zero, negOne, negOne, negOne, zero])]

/-- The primitive of `h₄`. -/
noncomputable def i15H4Phi (u : ℝ) : ℝ := i15T3Sum i15H4L u

/-! ### The derivative of the primitive, word by word

`d/du Σ qₜ H(wₜ) = Σ (qₜ' H(wₜ) + qₜ kₐ H(wₜ'))` for `wₜ = a wₜ'`; the coefficient of each
`H(w)` is a rational identity in `u`. -/

theorem i15H4L_c0 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q'
      (0,
       0,
       (21 / 2 - 28 * zeta3 + 2 * π ^ 2 + π ^ 4 / 20),
       (781 / 32 - 37 * π ^ 2 / 48 - π ^ 4 / 80 + 49 * zeta3 / 2))
      u +
    i15T3q
      (0,
       0,
       (-85 / 2 - 4 * zeta3 - 2 * π ^ 2 / 3),
       (-525 / 16 + 3 * zeta3 + 7 * π ^ 2 / 8))
      u * zero.kernel u +
    i15T3q (0, (-8 * zeta3), 0, 8 * zeta3) u * one.kernel u +
    i15T3q (0, 16 * zeta3, 0, (-16 * zeta3)) u * negOne.kernel u =
    i15T3q
      (0,
       (-32 - 24 * zeta3 + π ^ 4 / 20 + 4 * π ^ 2 / 3),
       (16 + 28 * zeta3 - 2 * π ^ 2 / 3 - π ^ 4 / 40),
       0)
      u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c1 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q'
      (0,
       0,
       (-85 / 2 - 4 * zeta3 - 2 * π ^ 2 / 3),
       (-525 / 16 + 3 * zeta3 + 7 * π ^ 2 / 8))
      u +
    i15T3q (0, 0, (-1 - π ^ 2 / 3), (-111 / 8 + π ^ 2 / 4)) u * zero.kernel u +
    i15T3q (0, (89 / 2 - π ^ 2 / 3), (-26), (-37 / 2 + π ^ 2 / 3)) u * one.kernel u +
    i15T3q (0, (15 + 2 * π ^ 2 / 3), 52, (37 - 2 * π ^ 2 / 3)) u * negOne.kernel u =
    i15T3q (0, (16 - 4 * zeta3 - 2 * π ^ 2 / 3), (-24 + π ^ 2 + 6 * zeta3), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c2 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-8 * zeta3), 0, 8 * zeta3) u +
    i15T3q (0, (-16 * zeta3), 0, 0) u * zero.kernel u =
    i15T3q ((-16 * zeta3), 0, 16 * zeta3, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c3 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 16 * zeta3, 0, (-16 * zeta3)) u +
    i15T3q (0, 32 * zeta3, 0, 0) u * zero.kernel u =
    i15T3q (32 * zeta3, 0, (-32 * zeta3), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c4 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 0, (-1 - π ^ 2 / 3), (-111 / 8 + π ^ 2 / 4)) u +
    i15T3q (0, 0, 4, (-21 / 4)) u * zero.kernel u +
    i15T3q (0, 11, (-4), (-7)) u * one.kernel u +
    i15T3q (0, (-6), 8, 14) u * negOne.kernel u =
    i15T3q (0, (8 - π ^ 2 / 3), (-12 + π ^ 2 / 2), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c5 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16 * zeta3), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c6 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 32 * zeta3, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c7 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (89 / 2 - π ^ 2 / 3), (-26), (-37 / 2 + π ^ 2 / 3)) u +
    i15T3q (0, (16 - 2 * π ^ 2 / 3), 16, (-21)) u * zero.kernel u +
    i15T3q (0, 22, (-8), (-14)) u * one.kernel u +
    i15T3q (0, (-12), 16, 28) u * negOne.kernel u =
    i15T3q ((16 - 2 * π ^ 2 / 3), 0, (-16 + 2 * π ^ 2 / 3), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c8 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (15 + 2 * π ^ 2 / 3), 52, (37 - 2 * π ^ 2 / 3)) u +
    i15T3q (0, (-32 + 4 * π ^ 2 / 3), (-32), 42) u * zero.kernel u +
    i15T3q (0, (-44), 16, 28) u * one.kernel u +
    i15T3q (0, 24, (-32), (-56)) u * negOne.kernel u =
    i15T3q ((-32 + 4 * π ^ 2 / 3), 0, (32 - 4 * π ^ 2 / 3), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c9 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 0, 4, (-21 / 4)) u +
    i15T3q (0, 0, 2, (-3 / 2)) u * zero.kernel u +
    i15T3q (0, 2, 0, (-2)) u * one.kernel u +
    i15T3q (0, (-4), 0, 4) u * negOne.kernel u =
    i15T3q (0, 4, (-6), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c10 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (16 - 2 * π ^ 2 / 3), 16, (-21)) u +
    i15T3q (0, 8, 8, (-6)) u * zero.kernel u +
    i15T3q (0, 8, 0, (-8)) u * one.kernel u +
    i15T3q (0, (-16), 0, 16) u * negOne.kernel u =
    i15T3q (8, 16, (-24), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c11 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-32 + 4 * π ^ 2 / 3), (-32), 42) u +
    i15T3q (0, (-16), (-16), 12) u * zero.kernel u +
    i15T3q (0, (-16), 0, 16) u * one.kernel u +
    i15T3q (0, 32, 0, (-32)) u * negOne.kernel u =
    i15T3q ((-16), (-32), 48, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c12 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 11, (-4), (-7)) u +
    i15T3q (0, 8, 8, (-6)) u * zero.kernel u +
    i15T3q (0, 4, 0, (-4)) u * one.kernel u +
    i15T3q (0, (-8), 0, 8) u * negOne.kernel u =
    i15T3q (8, 0, (-8), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c13 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 22, (-8), (-14)) u +
    i15T3q (0, 16, 16, (-12)) u * zero.kernel u +
    i15T3q (0, 8, 0, (-8)) u * one.kernel u +
    i15T3q (0, (-16), 0, 16) u * negOne.kernel u =
    i15T3q (16, 0, (-16), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c14 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-44), 16, 28) u +
    i15T3q (0, (-32), (-32), 24) u * zero.kernel u +
    i15T3q (0, (-16), 0, 16) u * one.kernel u +
    i15T3q (0, 32, 0, (-32)) u * negOne.kernel u =
    i15T3q ((-32), 0, 32, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c15 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-6), 8, 14) u +
    i15T3q (0, (-16), (-16), 12) u * zero.kernel u +
    i15T3q (0, (-8), 0, 8) u * one.kernel u +
    i15T3q (0, 16, 0, (-16)) u * negOne.kernel u =
    i15T3q ((-16), 0, 16, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c16 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-12), 16, 28) u +
    i15T3q (0, (-32), (-32), 24) u * zero.kernel u +
    i15T3q (0, (-16), 0, 16) u * one.kernel u +
    i15T3q (0, 32, 0, (-32)) u * negOne.kernel u =
    i15T3q ((-32), 0, 32, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c17 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 24, (-32), (-56)) u +
    i15T3q (0, 64, 64, (-48)) u * zero.kernel u +
    i15T3q (0, 32, 0, (-32)) u * one.kernel u +
    i15T3q (0, (-64), 0, 64) u * negOne.kernel u =
    i15T3q (64, 0, (-64), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15H4L_c18 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 0, 2, (-3 / 2)) u =
    i15T3q (0, 2, (-3), 0) u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15H4L_c19 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 8, 8, (-6)) u +
    i15T3q (0, 4, 0, 0) u * zero.kernel u =
    i15T3q (4, 8, (-12), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c20 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), (-16), 12) u +
    i15T3q (0, (-8), 0, 0) u * zero.kernel u =
    i15T3q ((-8), (-16), 24, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c21 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 8, 8, (-6)) u +
    i15T3q (0, 4, 0, 0) u * zero.kernel u =
    i15T3q (4, 8, (-12), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c22 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 16, 16, (-12)) u +
    i15T3q (0, 8, 0, 0) u * zero.kernel u =
    i15T3q (8, 16, (-24), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c23 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-32), (-32), 24) u +
    i15T3q (0, (-16), 0, 0) u * zero.kernel u =
    i15T3q ((-16), (-32), 48, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c24 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), (-16), 12) u +
    i15T3q (0, (-8), 0, 0) u * zero.kernel u =
    i15T3q ((-8), (-16), 24, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c25 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-32), (-32), 24) u +
    i15T3q (0, (-16), 0, 0) u * zero.kernel u =
    i15T3q ((-16), (-32), 48, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c26 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 64, 64, (-48)) u +
    i15T3q (0, 32, 0, 0) u * zero.kernel u =
    i15T3q (32, 64, (-96), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c27 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 2, 0, (-2)) u +
    i15T3q (0, 4, 0, 0) u * zero.kernel u =
    i15T3q (4, 0, (-4), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c28 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 8, 0, (-8)) u +
    i15T3q (0, 16, 0, 0) u * zero.kernel u =
    i15T3q (16, 0, (-16), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c29 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), 0, 16) u +
    i15T3q (0, (-32), 0, 0) u * zero.kernel u =
    i15T3q ((-32), 0, 32, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c30 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 4, 0, (-4)) u +
    i15T3q (0, 8, 0, 0) u * zero.kernel u =
    i15T3q (8, 0, (-8), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c31 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 8, 0, (-8)) u +
    i15T3q (0, 16, 0, 0) u * zero.kernel u =
    i15T3q (16, 0, (-16), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c32 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), 0, 16) u +
    i15T3q (0, (-32), 0, 0) u * zero.kernel u =
    i15T3q ((-32), 0, 32, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c33 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-8), 0, 8) u +
    i15T3q (0, (-16), 0, 0) u * zero.kernel u =
    i15T3q ((-16), 0, 16, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c34 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), 0, 16) u +
    i15T3q (0, (-32), 0, 0) u * zero.kernel u =
    i15T3q ((-32), 0, 32, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c35 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 32, 0, (-32)) u +
    i15T3q (0, 64, 0, 0) u * zero.kernel u =
    i15T3q (64, 0, (-64), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c36 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-4), 0, 4) u +
    i15T3q (0, (-8), 0, 0) u * zero.kernel u =
    i15T3q ((-8), 0, 8, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c37 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), 0, 16) u +
    i15T3q (0, (-32), 0, 0) u * zero.kernel u =
    i15T3q ((-32), 0, 32, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c38 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 32, 0, (-32)) u +
    i15T3q (0, 64, 0, 0) u * zero.kernel u =
    i15T3q (64, 0, (-64), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c39 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-8), 0, 8) u +
    i15T3q (0, (-16), 0, 0) u * zero.kernel u =
    i15T3q ((-16), 0, 16, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c40 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), 0, 16) u +
    i15T3q (0, (-32), 0, 0) u * zero.kernel u =
    i15T3q ((-32), 0, 32, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c41 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 32, 0, (-32)) u +
    i15T3q (0, 64, 0, 0) u * zero.kernel u =
    i15T3q (64, 0, (-64), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c42 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 16, 0, (-16)) u +
    i15T3q (0, 32, 0, 0) u * zero.kernel u =
    i15T3q (32, 0, (-32), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c43 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 32, 0, (-32)) u +
    i15T3q (0, 64, 0, 0) u * zero.kernel u =
    i15T3q (64, 0, (-64), 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c44 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-64), 0, 64) u +
    i15T3q (0, (-128), 0, 0) u * zero.kernel u =
    i15T3q ((-128), 0, 128, 0) u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15H4L_c45 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 4, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c46 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-8), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c47 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 4, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c48 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 8, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c49 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c50 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-8), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c51 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c52 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 32, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c53 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 4, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c54 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 16, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c55 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-32), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c56 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 8, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c57 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 16, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c58 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-32), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c59 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c60 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-32), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c61 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 64, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c62 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-8), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c63 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-32), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c64 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 64, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c65 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-16), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c66 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-32), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c67 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 64, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c68 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 32, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c69 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 64, 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_c70 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-128), 0, 0) u =
    0 := by
  simp only [i15T3q']
  field_simp
  ring

theorem i15H4L_deriv {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15T3SumD i15H4L u = i15H4 u := by
  have hu0 : u ≠ 0 := hu.1.ne'
  have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
  have hu2 : 1 + u ≠ 0 := by linarith [hu.1]
  simp only [i15H4L, i15H4, i15H4D, i15T3SumD_cons, i15T3SumD_nil, i15T3Sum_cons, i15T3Sum_nil,
    i15T3hd]
  linear_combination
    i15H4L_c0 hu0 hu1 hu2 * hpl [] u +
    i15H4L_c1 hu0 hu1 hu2 * hpl [zero] u +
    i15H4L_c2 hu0 hu1 hu2 * hpl [one] u +
    i15H4L_c3 hu0 hu1 hu2 * hpl [negOne] u +
    i15H4L_c4 hu0 hu1 hu2 * hpl [zero, zero] u +
    i15H4L_c5 hu0 hu1 hu2 * hpl [zero, one] u +
    i15H4L_c6 hu0 hu1 hu2 * hpl [zero, negOne] u +
    i15H4L_c7 hu0 hu1 hu2 * hpl [one, zero] u +
    i15H4L_c8 hu0 hu1 hu2 * hpl [negOne, zero] u +
    i15H4L_c9 hu0 hu1 hu2 * hpl [zero, zero, zero] u +
    i15H4L_c10 hu0 hu1 hu2 * hpl [zero, one, zero] u +
    i15H4L_c11 hu0 hu1 hu2 * hpl [zero, negOne, zero] u +
    i15H4L_c12 hu0 hu1 hu2 * hpl [one, zero, zero] u +
    i15H4L_c13 hu0 hu1 hu2 * hpl [one, one, zero] u +
    i15H4L_c14 hu0 hu1 hu2 * hpl [one, negOne, zero] u +
    i15H4L_c15 hu0 hu1 hu2 * hpl [negOne, zero, zero] u +
    i15H4L_c16 hu0 hu1 hu2 * hpl [negOne, one, zero] u +
    i15H4L_c17 hu0 hu1 hu2 * hpl [negOne, negOne, zero] u +
    i15H4L_c18 hu0 hu1 hu2 * hpl [zero, zero, zero, zero] u +
    i15H4L_c19 hu0 hu1 hu2 * hpl [zero, zero, one, zero] u +
    i15H4L_c20 hu0 hu1 hu2 * hpl [zero, zero, negOne, zero] u +
    i15H4L_c21 hu0 hu1 hu2 * hpl [zero, one, zero, zero] u +
    i15H4L_c22 hu0 hu1 hu2 * hpl [zero, one, one, zero] u +
    i15H4L_c23 hu0 hu1 hu2 * hpl [zero, one, negOne, zero] u +
    i15H4L_c24 hu0 hu1 hu2 * hpl [zero, negOne, zero, zero] u +
    i15H4L_c25 hu0 hu1 hu2 * hpl [zero, negOne, one, zero] u +
    i15H4L_c26 hu0 hu1 hu2 * hpl [zero, negOne, negOne, zero] u +
    i15H4L_c27 hu0 hu1 hu2 * hpl [one, zero, zero, zero] u +
    i15H4L_c28 hu0 hu1 hu2 * hpl [one, zero, one, zero] u +
    i15H4L_c29 hu0 hu1 hu2 * hpl [one, zero, negOne, zero] u +
    i15H4L_c30 hu0 hu1 hu2 * hpl [one, one, zero, zero] u +
    i15H4L_c31 hu0 hu1 hu2 * hpl [one, one, one, zero] u +
    i15H4L_c32 hu0 hu1 hu2 * hpl [one, one, negOne, zero] u +
    i15H4L_c33 hu0 hu1 hu2 * hpl [one, negOne, zero, zero] u +
    i15H4L_c34 hu0 hu1 hu2 * hpl [one, negOne, one, zero] u +
    i15H4L_c35 hu0 hu1 hu2 * hpl [one, negOne, negOne, zero] u +
    i15H4L_c36 hu0 hu1 hu2 * hpl [negOne, zero, zero, zero] u +
    i15H4L_c37 hu0 hu1 hu2 * hpl [negOne, zero, one, zero] u +
    i15H4L_c38 hu0 hu1 hu2 * hpl [negOne, zero, negOne, zero] u +
    i15H4L_c39 hu0 hu1 hu2 * hpl [negOne, one, zero, zero] u +
    i15H4L_c40 hu0 hu1 hu2 * hpl [negOne, one, one, zero] u +
    i15H4L_c41 hu0 hu1 hu2 * hpl [negOne, one, negOne, zero] u +
    i15H4L_c42 hu0 hu1 hu2 * hpl [negOne, negOne, zero, zero] u +
    i15H4L_c43 hu0 hu1 hu2 * hpl [negOne, negOne, one, zero] u +
    i15H4L_c44 hu0 hu1 hu2 * hpl [negOne, negOne, negOne, zero] u +
    i15H4L_c45 hu0 hu1 hu2 * hpl [zero, zero, zero, one, zero] u +
    i15H4L_c46 hu0 hu1 hu2 * hpl [zero, zero, zero, negOne, zero] u +
    i15H4L_c47 hu0 hu1 hu2 * hpl [zero, zero, one, zero, zero] u +
    i15H4L_c48 hu0 hu1 hu2 * hpl [zero, zero, one, one, zero] u +
    i15H4L_c49 hu0 hu1 hu2 * hpl [zero, zero, one, negOne, zero] u +
    i15H4L_c50 hu0 hu1 hu2 * hpl [zero, zero, negOne, zero, zero] u +
    i15H4L_c51 hu0 hu1 hu2 * hpl [zero, zero, negOne, one, zero] u +
    i15H4L_c52 hu0 hu1 hu2 * hpl [zero, zero, negOne, negOne, zero] u +
    i15H4L_c53 hu0 hu1 hu2 * hpl [zero, one, zero, zero, zero] u +
    i15H4L_c54 hu0 hu1 hu2 * hpl [zero, one, zero, one, zero] u +
    i15H4L_c55 hu0 hu1 hu2 * hpl [zero, one, zero, negOne, zero] u +
    i15H4L_c56 hu0 hu1 hu2 * hpl [zero, one, one, zero, zero] u +
    i15H4L_c57 hu0 hu1 hu2 * hpl [zero, one, one, one, zero] u +
    i15H4L_c58 hu0 hu1 hu2 * hpl [zero, one, one, negOne, zero] u +
    i15H4L_c59 hu0 hu1 hu2 * hpl [zero, one, negOne, zero, zero] u +
    i15H4L_c60 hu0 hu1 hu2 * hpl [zero, one, negOne, one, zero] u +
    i15H4L_c61 hu0 hu1 hu2 * hpl [zero, one, negOne, negOne, zero] u +
    i15H4L_c62 hu0 hu1 hu2 * hpl [zero, negOne, zero, zero, zero] u +
    i15H4L_c63 hu0 hu1 hu2 * hpl [zero, negOne, zero, one, zero] u +
    i15H4L_c64 hu0 hu1 hu2 * hpl [zero, negOne, zero, negOne, zero] u +
    i15H4L_c65 hu0 hu1 hu2 * hpl [zero, negOne, one, zero, zero] u +
    i15H4L_c66 hu0 hu1 hu2 * hpl [zero, negOne, one, one, zero] u +
    i15H4L_c67 hu0 hu1 hu2 * hpl [zero, negOne, one, negOne, zero] u +
    i15H4L_c68 hu0 hu1 hu2 * hpl [zero, negOne, negOne, zero, zero] u +
    i15H4L_c69 hu0 hu1 hu2 * hpl [zero, negOne, negOne, one, zero] u +
    i15H4L_c70 hu0 hu1 hu2 * hpl [zero, negOne, negOne, negOne, zero] u

theorem hasDerivAt_i15H4Phi {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i15H4Phi (i15H4 u) u :=
  (hasDerivAt_i15T3Sum i15H4L hu).congr_deriv (i15H4L_deriv hu)

theorem tendsto_i15H4Phi_zero : Tendsto i15H4Phi (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_i15T3Sum_zero ?_
  simp [i15H4L]

theorem i15H4L_value :
    (i15H4L.map fun t => i15T3q t.1 1 * hpl t.2 1).sum = i15H4Val := by
  simp only [i15H4L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, i15T3q,
    hpl_nil,
    hpl_negOne_negOne_zero_at_one, hpl_negOne_one_zero_at_one, hpl_negOne_zero_at_one,
    hpl_negOne_zero_zero_at_one, hpl_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_negOne_negOne_negOne_zero_at_one, hpl_zero_negOne_negOne_one_zero_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_negOne_zero_zero_at_one,
    hpl_zero_negOne_one_negOne_zero_at_one, hpl_zero_negOne_one_one_zero_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_negOne_one_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_zero_at_one,
    hpl_zero_negOne_zero_one_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_zero_at_one, hpl_zero_one_at_one,
    hpl_zero_one_negOne_negOne_zero_at_one, hpl_zero_one_negOne_one_zero_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_negOne_zero_zero_at_one,
    hpl_zero_one_one_negOne_zero_at_one, hpl_zero_one_one_one_zero_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_one_one_zero_zero_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_one_zero_negOne_zero_at_one, hpl_zero_one_zero_one_zero_at_one,
    hpl_zero_one_zero_zero_at_one, hpl_zero_one_zero_zero_zero_at_one, hpl_zero_zero_at_one,
    hpl_zero_zero_negOne_negOne_zero_at_one, hpl_zero_zero_negOne_one_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_one_negOne_zero_at_one, hpl_zero_zero_one_one_zero_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_zero_one_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_one_zero_at_one,
    hpl_zero_zero_zero_zero_at_one]
  unfold i15H4Val
  ring

theorem tendsto_i15H4Phi_one : Tendsto i15H4Phi (𝓝[<] 1) (𝓝 i15H4Val) := by
  rw [← i15H4L_value]
  refine tendsto_i15T3Sum_one ?_
  simp [i15H4L, i15T3q]
  norm_num
  all_goals ring_nf

/-- **`∫₀¹ h₄ = 12 ζ(5) - 2 π² ζ(3)/3 + 3 π⁴/80 + 8 π² log 2 - 119 π²/16 - 41 ζ(3)/2
+ 1117/32`**, given the integrability of `h₄`. -/
theorem integral_i15H4 (hI : IntervalIntegrable i15H4 volume 0 1) :
    ∫ u in (0 : ℝ)..1, i15H4 u = i15H4Val := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun u hu => hasDerivAt_i15H4Phi hu) hI tendsto_i15H4Phi_zero tendsto_i15H4Phi_one,
    sub_zero]

end QED.ThreeLoopD
