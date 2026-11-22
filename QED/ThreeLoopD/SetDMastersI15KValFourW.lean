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

/-!
# Set (d), master `I₁₅`: the outer integral of the `c`-weighted half of `F₄`

In the coordinate `r = x / (1 - x) ∈ (0, 1)` (the half `x < 1/2`, doubled by `x ↦ 1 - x`),
`dx / c = dr / r` and `∫∫ A₁,₄ = (1/12) ∫₀¹ W₄(r) dr / r` with
`W₄(r) = ∫₀¹ (b₁⁴ - b₂⁴) du`, `b₁ = log r + log u + 2 log (1 + r) - 2 log (r + u)
- 2 log (1 + r u)`, `b₂ = log r - 2 log (1 + r) - log u`. Numerically to about `500` digits
(`setDI15i/fit4.py`: an exact interpolation at dps `700` in the HPL basis of weight `≤ 4` with
coefficients `1/r, 1, r`, `363` unknowns, checked at `17` further points; every coefficient is an
integer combination of `1, π², ζ(3), π⁴`), `W₄ = Σ (aₜ/r + bₜ + cₜ r) H(wₜ; r)`, the sum of
`QED.ThreeLoopD.i15W4D` (`67` words of weight `≤ 4`; `QED.ThreeLoopD.i15W4`).

An explicit primitive `Φ = Σ qₜ(r) H(wₜ; r)` of `W₄ / r` (`QED.ThreeLoopD.i15W4Phi`, words of
weight `≤ 5`, found by integrating term by term) has derivative `W₄ / r` on `(0, 1)`, checked
word by word. At `1⁻` it tends to `K₁ = Σ qₜ(1) H(wₜ; 1)` (the words starting with `1` have
`qₜ(1) = 0`), evaluated with the HPL values of weight `≤ 5`; at `0⁺` its terms diverge
individually, and the leading polynomials of `QED.ThreeLoopD.SetDMastersI15KValFourAsym` give
the limit `K₀ = 4320`. Then
`K₁ - K₀ = 12 (384 Li₄(1/2) + 16 log⁴ 2 + 32 π² log² 2 - 80 π² log 2 - 16 π⁴/5 + 272 ζ(3)
+ 164 π²/3 - 360)`, twelve times the expected value of `∫∫ A₁,₄`. The identification
`∫₀¹ (b₁⁴ - b₂⁴) du = W₄(r)` is not proved here.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i15W4Phi`: the primitive.
* `QED.ThreeLoopD.tendsto_i15W4Phi_zero`, `QED.ThreeLoopD.tendsto_i15W4Phi_one`: its limits.
* `QED.ThreeLoopD.i15W4K1_sub_K0`: `K₁ - K₀`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The terms `(qₜ, wₜ)` of `W₄ = Σ qₜ(r) H(wₜ; r)`, `qₜ = (a, b, c, d) ↦ a/r + b + c r + d r²`. -/
noncomputable def i15W4D : List ((ℝ × ℝ × ℝ × ℝ) × List Letter) :=
  [((0, 1920, (-288 * zeta3 + 72 * π ^ 2 + 6 * π ^ 4 / 5), 0), []),
   ((0, 624, 1296, 0), [zero]),
   (((-48 * π ^ 2 + 192 * zeta3), 0, (-192 * zeta3 + 48 * π ^ 2), 0), [one]),
   (((-1296 - 192 * zeta3 + 48 * π ^ 2), (-1248), (-1296), 0), [negOne]),
   ((0, 192, 432, 0), [zero, zero]),
   (((-32 * π ^ 2), 0, 64 * π ^ 2, 0), [zero, one]),
   (((-864 + 32 * π ^ 2), (-384), (864 - 64 * π ^ 2), 0), [zero, negOne]),
   (((-864), 0, 864, 0), [one, zero]),
   (((-64 * π ^ 2), 0, 64 * π ^ 2, 0), [one, one]),
   ((32 * π ^ 2, 0, (-32 * π ^ 2), 0), [one, negOne]),
   ((432, (-384), (-432), 0), [negOne, zero]),
   ((32 * π ^ 2, 0, (-32 * π ^ 2), 0), [negOne, one]),
   ((0, 768, 32 * π ^ 2, 0), [negOne, negOne]),
   ((0, 48, 144, 0), [zero, zero, zero]),
   (((-576), (-96), 864, 0), [zero, zero, negOne]),
   (((-576), 0, 1152, 0), [zero, one, zero]),
   ((288, (-96), (-864), 0), [zero, negOne, zero]),
   ((0, 192, 576, 0), [zero, negOne, negOne]),
   (((-288), 0, 288, 0), [one, zero, zero]),
   (((-1152), 0, 1152, 0), [one, zero, negOne]),
   (((-1152), 0, 1152, 0), [one, one, zero]),
   ((576, 0, (-576), 0), [one, negOne, zero]),
   ((144, (-96), (-144), 0), [negOne, zero, zero]),
   ((864, 192, (-288), 0), [negOne, zero, negOne]),
   ((576, 0, (-576), 0), [negOne, one, zero]),
   ((0, 192, 576, 0), [negOne, negOne, zero]),
   (((-576), (-384), (-576), 0), [negOne, negOne, negOne]),
   ((0, 0, 48, 0), [zero, zero, zero, zero]),
   (((-384), 0, 672, 0), [zero, zero, zero, negOne]),
   (((-384), 0, 768, 0), [zero, zero, one, zero]),
   ((192, 0, (-480), 0), [zero, zero, negOne, zero]),
   ((0, 0, 192, 0), [zero, zero, negOne, negOne]),
   (((-192), 0, 384, 0), [zero, one, zero, zero]),
   (((-768), 0, 1536, 0), [zero, one, zero, negOne]),
   (((-768), 0, 1536, 0), [zero, one, one, zero]),
   ((384, 0, (-768), 0), [zero, one, negOne, zero]),
   ((96, 0, (-288), 0), [zero, negOne, zero, zero]),
   ((576, 0, (-960), 0), [zero, negOne, zero, negOne]),
   ((384, 0, (-768), 0), [zero, negOne, one, zero]),
   ((0, 0, 192, 0), [zero, negOne, negOne, zero]),
   (((-384), 0, 384, 0), [zero, negOne, negOne, negOne]),
   (((-96), 0, 96, 0), [one, zero, zero, zero]),
   (((-960), 0, 960, 0), [one, zero, zero, negOne]),
   (((-1152), 0, 1152, 0), [one, zero, one, zero]),
   ((768, 0, (-768), 0), [one, zero, negOne, zero]),
   (((-384), 0, 384, 0), [one, zero, negOne, negOne]),
   (((-384), 0, 384, 0), [one, one, zero, zero]),
   (((-1536), 0, 1536, 0), [one, one, zero, negOne]),
   (((-1536), 0, 1536, 0), [one, one, one, zero]),
   ((768, 0, (-768), 0), [one, one, negOne, zero]),
   ((192, 0, (-192), 0), [one, negOne, zero, zero]),
   ((768, 0, (-768), 0), [one, negOne, zero, negOne]),
   ((768, 0, (-768), 0), [one, negOne, one, zero]),
   (((-384), 0, 384, 0), [one, negOne, negOne, zero]),
   ((48, 0, (-48), 0), [negOne, zero, zero, zero]),
   ((672, 0, (-288), 0), [negOne, zero, zero, negOne]),
   ((768, 0, (-384), 0), [negOne, zero, one, zero]),
   (((-480), 0, 288, 0), [negOne, zero, negOne, zero]),
   ((192, 0, (-192), 0), [negOne, zero, negOne, negOne]),
   ((192, 0, (-192), 0), [negOne, one, zero, zero]),
   ((768, 0, (-768), 0), [negOne, one, zero, negOne]),
   ((768, 0, (-768), 0), [negOne, one, one, zero]),
   (((-384), 0, 384, 0), [negOne, one, negOne, zero]),
   ((0, 0, 192, 0), [negOne, negOne, zero, zero]),
   (((-384), 0, 384, 0), [negOne, negOne, zero, negOne]),
   (((-384), 0, 384, 0), [negOne, negOne, one, zero]),
   ((192, 0, (-192), 0), [negOne, negOne, negOne, zero])]

/-- **The inner integral `W₄(r)` of `A₁,₄`** (in `r = x/(1 - x)`), in harmonic polylogarithms. -/
noncomputable def i15W4 (r : ℝ) : ℝ := i15T3Sum i15W4D r

/-- The terms `(qₜ, wₜ)` of the primitive of `W₄ / r`. -/
noncomputable def i15W4L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter) :=
  [((0, 0, (-480 * zeta3 + 152 * π ^ 2 + 6 * π ^ 4 / 5), 0), []),
   ((0, (-1200), 3120, 0), [zero]),
   ((
      (-192 * zeta3 + 80 * π ^ 2),
      (-160 * π ^ 2 + 384 * zeta3),
      (-192 * zeta3 + 80 * π ^ 2),
      0),
     [one]),
   (((3120 - 80 * π ^ 2 + 192 * zeta3), (-80 * π ^ 2 + 192 * zeta3), (-3120), 0), [negOne]),
   ((0, (-288), 912, 0), [zero, zero]),
   ((32 * π ^ 2, (-32 * π ^ 2), 64 * π ^ 2, 0), [zero, one]),
   (((1824 - 32 * π ^ 2), (-1248 + 32 * π ^ 2), (1824 - 64 * π ^ 2), 0), [zero, negOne]),
   ((1824, (-3648), 1824, 0), [one, zero]),
   ((64 * π ^ 2, (-128 * π ^ 2), 64 * π ^ 2, 0), [one, one]),
   (((-32 * π ^ 2), 64 * π ^ 2, (-32 * π ^ 2), 0), [one, negOne]),
   (((-912), (-1824), (-912), 0), [negOne, zero]),
   (((-32 * π ^ 2), (-64 * π ^ 2), (-32 * π ^ 2), 0), [negOne, one]),
   ((0, 32 * π ^ 2, 32 * π ^ 2, 0), [negOne, negOne]),
   ((0, (-48), 240, 0), [zero, zero, zero]),
   ((960, (-864), 1440, 0), [zero, zero, negOne]),
   ((960, (-960), 1920, 0), [zero, one, zero]),
   (((-480), 576, (-1440), 0), [zero, negOne, zero]),
   ((0, (-192), 960, 0), [zero, negOne, negOne]),
   ((480, (-960), 480, 0), [one, zero, zero]),
   ((1920, (-3840), 1920, 0), [one, zero, negOne]),
   ((1920, (-3840), 1920, 0), [one, one, zero]),
   (((-960), 1920, (-960), 0), [one, negOne, zero]),
   (((-240), (-480), (-240), 0), [negOne, zero, zero]),
   (((-1440), (-1920), (-480), 0), [negOne, zero, negOne]),
   (((-960), (-1920), (-960), 0), [negOne, one, zero]),
   ((0, 960, 960, 0), [negOne, negOne, zero]),
   ((960, 0, (-960), 0), [negOne, negOne, negOne]),
   ((0, 0, 48, 0), [zero, zero, zero, zero]),
   ((384, (-384), 672, 0), [zero, zero, zero, negOne]),
   ((384, (-384), 768, 0), [zero, zero, one, zero]),
   (((-192), 192, (-480), 0), [zero, zero, negOne, zero]),
   ((0, 0, 192, 0), [zero, zero, negOne, negOne]),
   ((192, (-192), 384, 0), [zero, one, zero, zero]),
   ((768, (-768), 1536, 0), [zero, one, zero, negOne]),
   ((768, (-768), 1536, 0), [zero, one, one, zero]),
   (((-384), 384, (-768), 0), [zero, one, negOne, zero]),
   (((-96), 96, (-288), 0), [zero, negOne, zero, zero]),
   (((-576), 576, (-960), 0), [zero, negOne, zero, negOne]),
   (((-384), 384, (-768), 0), [zero, negOne, one, zero]),
   ((0, 0, 192, 0), [zero, negOne, negOne, zero]),
   ((384, (-384), 384, 0), [zero, negOne, negOne, negOne]),
   ((96, (-192), 96, 0), [one, zero, zero, zero]),
   ((960, (-1920), 960, 0), [one, zero, zero, negOne]),
   ((1152, (-2304), 1152, 0), [one, zero, one, zero]),
   (((-768), 1536, (-768), 0), [one, zero, negOne, zero]),
   ((384, (-768), 384, 0), [one, zero, negOne, negOne]),
   ((384, (-768), 384, 0), [one, one, zero, zero]),
   ((1536, (-3072), 1536, 0), [one, one, zero, negOne]),
   ((1536, (-3072), 1536, 0), [one, one, one, zero]),
   (((-768), 1536, (-768), 0), [one, one, negOne, zero]),
   (((-192), 384, (-192), 0), [one, negOne, zero, zero]),
   (((-768), 1536, (-768), 0), [one, negOne, zero, negOne]),
   (((-768), 1536, (-768), 0), [one, negOne, one, zero]),
   ((384, (-768), 384, 0), [one, negOne, negOne, zero]),
   (((-48), (-96), (-48), 0), [negOne, zero, zero, zero]),
   (((-672), (-960), (-288), 0), [negOne, zero, zero, negOne]),
   (((-768), (-1152), (-384), 0), [negOne, zero, one, zero]),
   ((480, 768, 288, 0), [negOne, zero, negOne, zero]),
   (((-192), (-384), (-192), 0), [negOne, zero, negOne, negOne]),
   (((-192), (-384), (-192), 0), [negOne, one, zero, zero]),
   (((-768), (-1536), (-768), 0), [negOne, one, zero, negOne]),
   (((-768), (-1536), (-768), 0), [negOne, one, one, zero]),
   ((384, 768, 384, 0), [negOne, one, negOne, zero]),
   ((0, 192, 192, 0), [negOne, negOne, zero, zero]),
   ((384, 768, 384, 0), [negOne, negOne, zero, negOne]),
   ((384, 768, 384, 0), [negOne, negOne, one, zero]),
   (((-192), (-384), (-192), 0), [negOne, negOne, negOne, zero])]

/-- The primitive of `W₄ / r`. -/
noncomputable def i15W4Phi (r : ℝ) : ℝ := i15T3Sum i15W4L r

/-! ### The derivative of the primitive, word by word

`d/dr Σ qₜ H(wₜ) = Σ (qₜ' H(wₜ) + qₜ kₐ H(wₜ'))` for `wₜ = a wₜ'`; the coefficient of each
`H(w)` is a rational identity in `r` (written `u` below). -/

theorem i15W4L_c0 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 0, (-480 * zeta3 + 152 * π ^ 2 + 6 * π ^ 4 / 5), 0) u +
    i15T3q (0, (-1200), 3120, 0) u * zero.kernel u +
    i15T3q
      ((-192 * zeta3 + 80 * π ^ 2),
       (-160 * π ^ 2 + 384 * zeta3),
       (-192 * zeta3 + 80 * π ^ 2),
       0)
      u * one.kernel u +
    i15T3q
      ((3120 - 80 * π ^ 2 + 192 * zeta3),
       (-80 * π ^ 2 + 192 * zeta3),
       (-3120),
       0)
      u * negOne.kernel u =
    i15T3q (0, 1920, (-288 * zeta3 + 72 * π ^ 2 + 6 * π ^ 4 / 5), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c1 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-1200), 3120, 0) u +
    i15T3q (0, (-288), 912, 0) u * zero.kernel u +
    i15T3q (1824, (-3648), 1824, 0) u * one.kernel u +
    i15T3q ((-912), (-1824), (-912), 0) u * negOne.kernel u =
    i15T3q (0, 624, 1296, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c2 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q'
      ((-192 * zeta3 + 80 * π ^ 2),
       (-160 * π ^ 2 + 384 * zeta3),
       (-192 * zeta3 + 80 * π ^ 2),
       0)
      u +
    i15T3q (32 * π ^ 2, (-32 * π ^ 2), 64 * π ^ 2, 0) u * zero.kernel u +
    i15T3q (64 * π ^ 2, (-128 * π ^ 2), 64 * π ^ 2, 0) u * one.kernel u +
    i15T3q ((-32 * π ^ 2), (-64 * π ^ 2), (-32 * π ^ 2), 0) u * negOne.kernel u =
    i15T3q ((-48 * π ^ 2 + 192 * zeta3), 0, (-192 * zeta3 + 48 * π ^ 2), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c3 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' ((3120 - 80 * π ^ 2 + 192 * zeta3), (-80 * π ^ 2 + 192 * zeta3), (-3120), 0) u +
    i15T3q ((1824 - 32 * π ^ 2), (-1248 + 32 * π ^ 2), (1824 - 64 * π ^ 2), 0) u * zero.kernel u +
    i15T3q ((-32 * π ^ 2), 64 * π ^ 2, (-32 * π ^ 2), 0) u * one.kernel u +
    i15T3q (0, 32 * π ^ 2, 32 * π ^ 2, 0) u * negOne.kernel u =
    i15T3q ((-1296 - 192 * zeta3 + 48 * π ^ 2), (-1248), (-1296), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c4 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-288), 912, 0) u +
    i15T3q (0, (-48), 240, 0) u * zero.kernel u +
    i15T3q (480, (-960), 480, 0) u * one.kernel u +
    i15T3q ((-240), (-480), (-240), 0) u * negOne.kernel u =
    i15T3q (0, 192, 432, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c5 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (32 * π ^ 2, (-32 * π ^ 2), 64 * π ^ 2, 0) u =
    i15T3q ((-32 * π ^ 2), 0, 64 * π ^ 2, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c6 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' ((1824 - 32 * π ^ 2), (-1248 + 32 * π ^ 2), (1824 - 64 * π ^ 2), 0) u +
    i15T3q (960, (-864), 1440, 0) u * zero.kernel u +
    i15T3q (1920, (-3840), 1920, 0) u * one.kernel u +
    i15T3q ((-1440), (-1920), (-480), 0) u * negOne.kernel u =
    i15T3q ((-864 + 32 * π ^ 2), (-384), (864 - 64 * π ^ 2), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c7 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (1824, (-3648), 1824, 0) u +
    i15T3q (960, (-960), 1920, 0) u * zero.kernel u +
    i15T3q (1920, (-3840), 1920, 0) u * one.kernel u +
    i15T3q ((-960), (-1920), (-960), 0) u * negOne.kernel u =
    i15T3q ((-864), 0, 864, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c8 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (64 * π ^ 2, (-128 * π ^ 2), 64 * π ^ 2, 0) u =
    i15T3q ((-64 * π ^ 2), 0, 64 * π ^ 2, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c9 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-32 * π ^ 2), 64 * π ^ 2, (-32 * π ^ 2), 0) u =
    i15T3q (32 * π ^ 2, 0, (-32 * π ^ 2), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c10 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' ((-912), (-1824), (-912), 0) u +
    i15T3q ((-480), 576, (-1440), 0) u * zero.kernel u +
    i15T3q ((-960), 1920, (-960), 0) u * one.kernel u +
    i15T3q (0, 960, 960, 0) u * negOne.kernel u =
    i15T3q (432, (-384), (-432), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c11 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-32 * π ^ 2), (-64 * π ^ 2), (-32 * π ^ 2), 0) u =
    i15T3q (32 * π ^ 2, 0, (-32 * π ^ 2), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c12 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 32 * π ^ 2, 32 * π ^ 2, 0) u +
    i15T3q (0, (-192), 960, 0) u * zero.kernel u +
    i15T3q (960, 0, (-960), 0) u * negOne.kernel u =
    i15T3q (0, 768, 32 * π ^ 2, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c13 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-48), 240, 0) u +
    i15T3q (0, 0, 48, 0) u * zero.kernel u +
    i15T3q (96, (-192), 96, 0) u * one.kernel u +
    i15T3q ((-48), (-96), (-48), 0) u * negOne.kernel u =
    i15T3q (0, 48, 144, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c14 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (960, (-864), 1440, 0) u +
    i15T3q (384, (-384), 672, 0) u * zero.kernel u +
    i15T3q (960, (-1920), 960, 0) u * one.kernel u +
    i15T3q ((-672), (-960), (-288), 0) u * negOne.kernel u =
    i15T3q ((-576), (-96), 864, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c15 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (960, (-960), 1920, 0) u +
    i15T3q (384, (-384), 768, 0) u * zero.kernel u +
    i15T3q (1152, (-2304), 1152, 0) u * one.kernel u +
    i15T3q ((-768), (-1152), (-384), 0) u * negOne.kernel u =
    i15T3q ((-576), 0, 1152, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c16 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' ((-480), 576, (-1440), 0) u +
    i15T3q ((-192), 192, (-480), 0) u * zero.kernel u +
    i15T3q ((-768), 1536, (-768), 0) u * one.kernel u +
    i15T3q (480, 768, 288, 0) u * negOne.kernel u =
    i15T3q (288, (-96), (-864), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c17 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, (-192), 960, 0) u +
    i15T3q (0, 0, 192, 0) u * zero.kernel u +
    i15T3q (384, (-768), 384, 0) u * one.kernel u +
    i15T3q ((-192), (-384), (-192), 0) u * negOne.kernel u =
    i15T3q (0, 192, 576, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c18 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (480, (-960), 480, 0) u +
    i15T3q (192, (-192), 384, 0) u * zero.kernel u +
    i15T3q (384, (-768), 384, 0) u * one.kernel u +
    i15T3q ((-192), (-384), (-192), 0) u * negOne.kernel u =
    i15T3q ((-288), 0, 288, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c19 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (1920, (-3840), 1920, 0) u +
    i15T3q (768, (-768), 1536, 0) u * zero.kernel u +
    i15T3q (1536, (-3072), 1536, 0) u * one.kernel u +
    i15T3q ((-768), (-1536), (-768), 0) u * negOne.kernel u =
    i15T3q ((-1152), 0, 1152, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c20 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (1920, (-3840), 1920, 0) u +
    i15T3q (768, (-768), 1536, 0) u * zero.kernel u +
    i15T3q (1536, (-3072), 1536, 0) u * one.kernel u +
    i15T3q ((-768), (-1536), (-768), 0) u * negOne.kernel u =
    i15T3q ((-1152), 0, 1152, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c21 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' ((-960), 1920, (-960), 0) u +
    i15T3q ((-384), 384, (-768), 0) u * zero.kernel u +
    i15T3q ((-768), 1536, (-768), 0) u * one.kernel u +
    i15T3q (384, 768, 384, 0) u * negOne.kernel u =
    i15T3q (576, 0, (-576), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c22 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' ((-240), (-480), (-240), 0) u +
    i15T3q ((-96), 96, (-288), 0) u * zero.kernel u +
    i15T3q ((-192), 384, (-192), 0) u * one.kernel u +
    i15T3q (0, 192, 192, 0) u * negOne.kernel u =
    i15T3q (144, (-96), (-144), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c23 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' ((-1440), (-1920), (-480), 0) u +
    i15T3q ((-576), 576, (-960), 0) u * zero.kernel u +
    i15T3q ((-768), 1536, (-768), 0) u * one.kernel u +
    i15T3q (384, 768, 384, 0) u * negOne.kernel u =
    i15T3q (864, 192, (-288), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c24 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' ((-960), (-1920), (-960), 0) u +
    i15T3q ((-384), 384, (-768), 0) u * zero.kernel u +
    i15T3q ((-768), 1536, (-768), 0) u * one.kernel u +
    i15T3q (384, 768, 384, 0) u * negOne.kernel u =
    i15T3q (576, 0, (-576), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c25 {u : ℝ} (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 960, 960, 0) u +
    i15T3q (0, 0, 192, 0) u * zero.kernel u +
    i15T3q (384, (-768), 384, 0) u * one.kernel u +
    i15T3q ((-192), (-384), (-192), 0) u * negOne.kernel u =
    i15T3q (0, 192, 576, 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne]
  field_simp
  ring

theorem i15W4L_c26 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (960, 0, (-960), 0) u +
    i15T3q (384, (-384), 384, 0) u * zero.kernel u =
    i15T3q ((-576), (-384), (-576), 0) u / u := by
  simp only [i15T3q, i15T3q', Letter.kernel_zero]
  field_simp
  ring

theorem i15W4L_c27 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 0, 48, 0) u =
    i15T3q (0, 0, 48, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c28 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (384, (-384), 672, 0) u =
    i15T3q ((-384), 0, 672, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c29 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (384, (-384), 768, 0) u =
    i15T3q ((-384), 0, 768, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c30 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-192), 192, (-480), 0) u =
    i15T3q (192, 0, (-480), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c31 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 0, 192, 0) u =
    i15T3q (0, 0, 192, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c32 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (192, (-192), 384, 0) u =
    i15T3q ((-192), 0, 384, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c33 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (768, (-768), 1536, 0) u =
    i15T3q ((-768), 0, 1536, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c34 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (768, (-768), 1536, 0) u =
    i15T3q ((-768), 0, 1536, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c35 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-384), 384, (-768), 0) u =
    i15T3q (384, 0, (-768), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c36 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-96), 96, (-288), 0) u =
    i15T3q (96, 0, (-288), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c37 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-576), 576, (-960), 0) u =
    i15T3q (576, 0, (-960), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c38 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-384), 384, (-768), 0) u =
    i15T3q (384, 0, (-768), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c39 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 0, 192, 0) u =
    i15T3q (0, 0, 192, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c40 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (384, (-384), 384, 0) u =
    i15T3q ((-384), 0, 384, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c41 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (96, (-192), 96, 0) u =
    i15T3q ((-96), 0, 96, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c42 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (960, (-1920), 960, 0) u =
    i15T3q ((-960), 0, 960, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c43 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (1152, (-2304), 1152, 0) u =
    i15T3q ((-1152), 0, 1152, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c44 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-768), 1536, (-768), 0) u =
    i15T3q (768, 0, (-768), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c45 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (384, (-768), 384, 0) u =
    i15T3q ((-384), 0, 384, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c46 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (384, (-768), 384, 0) u =
    i15T3q ((-384), 0, 384, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c47 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (1536, (-3072), 1536, 0) u =
    i15T3q ((-1536), 0, 1536, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c48 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (1536, (-3072), 1536, 0) u =
    i15T3q ((-1536), 0, 1536, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c49 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-768), 1536, (-768), 0) u =
    i15T3q (768, 0, (-768), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c50 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-192), 384, (-192), 0) u =
    i15T3q (192, 0, (-192), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c51 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-768), 1536, (-768), 0) u =
    i15T3q (768, 0, (-768), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c52 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-768), 1536, (-768), 0) u =
    i15T3q (768, 0, (-768), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c53 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (384, (-768), 384, 0) u =
    i15T3q ((-384), 0, 384, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c54 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-48), (-96), (-48), 0) u =
    i15T3q (48, 0, (-48), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c55 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-672), (-960), (-288), 0) u =
    i15T3q (672, 0, (-288), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c56 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-768), (-1152), (-384), 0) u =
    i15T3q (768, 0, (-384), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c57 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (480, 768, 288, 0) u =
    i15T3q ((-480), 0, 288, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c58 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-192), (-384), (-192), 0) u =
    i15T3q (192, 0, (-192), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c59 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-192), (-384), (-192), 0) u =
    i15T3q (192, 0, (-192), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c60 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-768), (-1536), (-768), 0) u =
    i15T3q (768, 0, (-768), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c61 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-768), (-1536), (-768), 0) u =
    i15T3q (768, 0, (-768), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c62 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (384, 768, 384, 0) u =
    i15T3q ((-384), 0, 384, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c63 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (0, 192, 192, 0) u =
    i15T3q (0, 0, 192, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c64 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (384, 768, 384, 0) u =
    i15T3q ((-384), 0, 384, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c65 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' (384, 768, 384, 0) u =
    i15T3q ((-384), 0, 384, 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_c66 {u : ℝ} (hu0 : u ≠ 0) (_hu1 : 1 - u ≠ 0) (_hu2 : 1 + u ≠ 0) :
    i15T3q' ((-192), (-384), (-192), 0) u =
    i15T3q (192, 0, (-192), 0) u / u := by
  simp only [i15T3q, i15T3q']
  field_simp
  ring

theorem i15W4L_deriv {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : i15T3SumD i15W4L u = i15W4 u / u := by
  have hu0 : u ≠ 0 := hu.1.ne'
  have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
  have hu2 : 1 + u ≠ 0 := by linarith [hu.1]
  simp only [i15W4L, i15W4, i15W4D, i15T3SumD_cons, i15T3SumD_nil, i15T3Sum_cons, i15T3Sum_nil,
    i15T3hd]
  linear_combination
    i15W4L_c0 hu0 hu1 hu2 * hpl [] u +
    i15W4L_c1 hu0 hu1 hu2 * hpl [zero] u +
    i15W4L_c2 hu0 hu1 hu2 * hpl [one] u +
    i15W4L_c3 hu0 hu1 hu2 * hpl [negOne] u +
    i15W4L_c4 hu0 hu1 hu2 * hpl [zero, zero] u +
    i15W4L_c5 hu0 hu1 hu2 * hpl [zero, one] u +
    i15W4L_c6 hu0 hu1 hu2 * hpl [zero, negOne] u +
    i15W4L_c7 hu0 hu1 hu2 * hpl [one, zero] u +
    i15W4L_c8 hu0 hu1 hu2 * hpl [one, one] u +
    i15W4L_c9 hu0 hu1 hu2 * hpl [one, negOne] u +
    i15W4L_c10 hu0 hu1 hu2 * hpl [negOne, zero] u +
    i15W4L_c11 hu0 hu1 hu2 * hpl [negOne, one] u +
    i15W4L_c12 hu0 hu1 hu2 * hpl [negOne, negOne] u +
    i15W4L_c13 hu0 hu1 hu2 * hpl [zero, zero, zero] u +
    i15W4L_c14 hu0 hu1 hu2 * hpl [zero, zero, negOne] u +
    i15W4L_c15 hu0 hu1 hu2 * hpl [zero, one, zero] u +
    i15W4L_c16 hu0 hu1 hu2 * hpl [zero, negOne, zero] u +
    i15W4L_c17 hu0 hu1 hu2 * hpl [zero, negOne, negOne] u +
    i15W4L_c18 hu0 hu1 hu2 * hpl [one, zero, zero] u +
    i15W4L_c19 hu0 hu1 hu2 * hpl [one, zero, negOne] u +
    i15W4L_c20 hu0 hu1 hu2 * hpl [one, one, zero] u +
    i15W4L_c21 hu0 hu1 hu2 * hpl [one, negOne, zero] u +
    i15W4L_c22 hu0 hu1 hu2 * hpl [negOne, zero, zero] u +
    i15W4L_c23 hu0 hu1 hu2 * hpl [negOne, zero, negOne] u +
    i15W4L_c24 hu0 hu1 hu2 * hpl [negOne, one, zero] u +
    i15W4L_c25 hu0 hu1 hu2 * hpl [negOne, negOne, zero] u +
    i15W4L_c26 hu0 hu1 hu2 * hpl [negOne, negOne, negOne] u +
    i15W4L_c27 hu0 hu1 hu2 * hpl [zero, zero, zero, zero] u +
    i15W4L_c28 hu0 hu1 hu2 * hpl [zero, zero, zero, negOne] u +
    i15W4L_c29 hu0 hu1 hu2 * hpl [zero, zero, one, zero] u +
    i15W4L_c30 hu0 hu1 hu2 * hpl [zero, zero, negOne, zero] u +
    i15W4L_c31 hu0 hu1 hu2 * hpl [zero, zero, negOne, negOne] u +
    i15W4L_c32 hu0 hu1 hu2 * hpl [zero, one, zero, zero] u +
    i15W4L_c33 hu0 hu1 hu2 * hpl [zero, one, zero, negOne] u +
    i15W4L_c34 hu0 hu1 hu2 * hpl [zero, one, one, zero] u +
    i15W4L_c35 hu0 hu1 hu2 * hpl [zero, one, negOne, zero] u +
    i15W4L_c36 hu0 hu1 hu2 * hpl [zero, negOne, zero, zero] u +
    i15W4L_c37 hu0 hu1 hu2 * hpl [zero, negOne, zero, negOne] u +
    i15W4L_c38 hu0 hu1 hu2 * hpl [zero, negOne, one, zero] u +
    i15W4L_c39 hu0 hu1 hu2 * hpl [zero, negOne, negOne, zero] u +
    i15W4L_c40 hu0 hu1 hu2 * hpl [zero, negOne, negOne, negOne] u +
    i15W4L_c41 hu0 hu1 hu2 * hpl [one, zero, zero, zero] u +
    i15W4L_c42 hu0 hu1 hu2 * hpl [one, zero, zero, negOne] u +
    i15W4L_c43 hu0 hu1 hu2 * hpl [one, zero, one, zero] u +
    i15W4L_c44 hu0 hu1 hu2 * hpl [one, zero, negOne, zero] u +
    i15W4L_c45 hu0 hu1 hu2 * hpl [one, zero, negOne, negOne] u +
    i15W4L_c46 hu0 hu1 hu2 * hpl [one, one, zero, zero] u +
    i15W4L_c47 hu0 hu1 hu2 * hpl [one, one, zero, negOne] u +
    i15W4L_c48 hu0 hu1 hu2 * hpl [one, one, one, zero] u +
    i15W4L_c49 hu0 hu1 hu2 * hpl [one, one, negOne, zero] u +
    i15W4L_c50 hu0 hu1 hu2 * hpl [one, negOne, zero, zero] u +
    i15W4L_c51 hu0 hu1 hu2 * hpl [one, negOne, zero, negOne] u +
    i15W4L_c52 hu0 hu1 hu2 * hpl [one, negOne, one, zero] u +
    i15W4L_c53 hu0 hu1 hu2 * hpl [one, negOne, negOne, zero] u +
    i15W4L_c54 hu0 hu1 hu2 * hpl [negOne, zero, zero, zero] u +
    i15W4L_c55 hu0 hu1 hu2 * hpl [negOne, zero, zero, negOne] u +
    i15W4L_c56 hu0 hu1 hu2 * hpl [negOne, zero, one, zero] u +
    i15W4L_c57 hu0 hu1 hu2 * hpl [negOne, zero, negOne, zero] u +
    i15W4L_c58 hu0 hu1 hu2 * hpl [negOne, zero, negOne, negOne] u +
    i15W4L_c59 hu0 hu1 hu2 * hpl [negOne, one, zero, zero] u +
    i15W4L_c60 hu0 hu1 hu2 * hpl [negOne, one, zero, negOne] u +
    i15W4L_c61 hu0 hu1 hu2 * hpl [negOne, one, one, zero] u +
    i15W4L_c62 hu0 hu1 hu2 * hpl [negOne, one, negOne, zero] u +
    i15W4L_c63 hu0 hu1 hu2 * hpl [negOne, negOne, zero, zero] u +
    i15W4L_c64 hu0 hu1 hu2 * hpl [negOne, negOne, zero, negOne] u +
    i15W4L_c65 hu0 hu1 hu2 * hpl [negOne, negOne, one, zero] u +
    i15W4L_c66 hu0 hu1 hu2 * hpl [negOne, negOne, negOne, zero] u

theorem hasDerivAt_i15W4Phi {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i15W4Phi (i15W4 r / r) r :=
  (hasDerivAt_i15T3Sum i15W4L hr).congr_deriv (i15W4L_deriv hr)

/-- The limit of `Φ` at `0⁺`. -/
noncomputable def i15W4K0 : ℝ :=
  4320

/-- The limit of `Φ` at `1⁻`. -/
noncomputable def i15W4K1 : ℝ :=
  192 * (log 2) ^ 4 + 656 * π ^ 2 + 3264 * zeta3 + 4608 * Li 4 (1 / 2) - 192 * π ^ 4 / 5 - 960 * log
    2 * π ^ 2 + 384 * (log 2) ^ 2 * π ^ 2

theorem tendsto_i15W4Phi_zero : Tendsto i15W4Phi (𝓝[>] 0) (𝓝 i15W4K0) := by
  refine tendsto_i15T3Sum_zero_of_lead ?_ ?_
  · simp [i15W4L]
  · intro x
    simp [i15AsSum, i15W4L, i15W4K0]
    ring

theorem i15W4L_value :
    (i15W4L.map fun t => i15T3q t.1 1 * hpl t.2 1).sum = i15W4K1 := by
  simp only [i15W4L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, i15T3q,
    hpl_nil,
    hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_negOne_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_one_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_zero_negOne_at_one, hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_one_at_one,
    hpl_negOne_one_negOne_zero_at_one, hpl_negOne_one_one_zero_at_one, hpl_negOne_one_zero_at_one,
    hpl_negOne_one_zero_negOne_at_one, hpl_negOne_one_zero_zero_at_one, hpl_negOne_zero_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_negOne_zero_negOne_negOne_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_negOne_zero_one_zero_at_one,
    hpl_negOne_zero_zero_at_one, hpl_negOne_zero_zero_negOne_at_one,
    hpl_negOne_zero_zero_zero_at_one, hpl_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_negOne_negOne_at_one,
    hpl_zero_negOne_negOne_zero_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_one_negOne_zero_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_one_zero_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_one_zero_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_zero_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_zero_at_one]
  unfold i15W4K1
  ring

theorem tendsto_i15W4Phi_one : Tendsto i15W4Phi (𝓝[<] 1) (𝓝 i15W4K1) := by
  rw [← i15W4L_value]
  refine tendsto_i15T3Sum_one ?_
  simp [i15W4L, i15T3q]
  norm_num
  all_goals ring_nf
  all_goals simp

/-- **`K₁ - K₀`**: twelve times the expected value of `∫∫ A₁,₄`. -/
theorem i15W4K1_sub_K0 :
    i15W4K1 - i15W4K0 =
      12 * (384 * Li 4 (1 / 2) + 16 * log 2 ^ 4 + 32 * π ^ 2 * log 2 ^ 2 - 80 * π ^ 2 * log 2 -
      16 * π ^ 4 / 5 + 272 * zeta3 + 164 * π ^ 2 / 3 - 360) := by
  unfold i15W4K1 i15W4K0
  ring

end QED.ThreeLoopD
