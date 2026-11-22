/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI3Wire
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Set (d), master `I₃`: the finite dotted integral `F`

**The integral.** LR96's `I₃ = ∫ 1 / (D₁ D₂ D₄ D₅ D₆ D₈)` (normalization as in
`QED.DimReg.LR96Family`). The loop `k₂` runs only through `D₂, D₄`: with `Q = k₁ - k₃` it is the
equal-mass bubble `Γ(ε) ∫₀¹ (1 + x(1 - x) Q²) ^ (-ε) dx`. What remains is the two-loop on-shell
kite with photons `D₆ = k₁²`, `D₈ = k₃²`, electrons `D₁ = (p - k₁)² + 1`, `D₅ = (p - k₃)² + 1`
and the bubble as its middle line. `F` is the same integral with `D₂` or `D₄` squared (Kira
`lbl[1,0,1,1,1,0,1,2,0]`, one dot on the bubble; the two agree by symmetry), divided by
`C(ε) = (π ^ ε Γ(1 + ε))³`. The dotted bubble is `Γ(1 + ε) / 2 ∫₀¹ (1 + c Q²) ^ (-1 - ε) dx`,
`c = x(1 - x)`, and `F` is finite at `d = 4`.

**Parametric form.** Feynman parameters `a` (middle line, power `1 + ε`, mass² `1/c`),
`d₁, e₁` (`D₆, D₁`), `d₃, e₃` (`D₈, D₅`) give `U = a(D + D') + D D'` with `D = d₁ + e₁`,
`D' = d₃ + e₃`, and `F = aU/c + a(e₁ + e₃)² + e₁² D' + e₃² D` (on shell, `p² = -1`). Cheng–Wu
with `δ(1 - D - D')`, `D = s`, `e₁ = s u`, `e₃ = (1 - s) v` and `a = s(1 - s) t` give

  `F(ε) = Γ(1 + 3ε) / (2 Γ(1 + ε)³) ∫ (c σ) ^ (2ε) t ^ ε (1 + t) ^ (4ε - 1) N ^ (-1 - 3ε)`,

over `x, s, u, v ∈ (0, 1)`, `t ∈ (0, ∞)`, with `σ = s(1 - s)`, `w = s u + (1 - s) v` and
`N = σ t (1 + t) + c ((1 + t) w² + σ (u - v)²)` (`QED.ThreeLoopD.i3FPoly`). The factorization
of the graph and the parametric formula are a convention recorded here, as for `I₉` in
`QED.ThreeLoopD.SetDMastersI9Def`. Numerically (Gauss–Legendre, 48 points per variable) the
right side is `6.49398` at `ε = 0` and its symmetric difference quotients at `ε = ±0.02` agree
with the expansion predicted by the IBP relation `QED.ThreeLoopD.SetDMasters.I3Rel` from the
L01 masters, `F = π⁴/15 - 13.1817 ε + 99.746 ε² + O(ε³)`, to `10⁻³`.

## Main definitions

* `QED.ThreeLoopD.i3FPoly`, `QED.ThreeLoopD.i3FInt`, `QED.ThreeLoopD.setDI3F`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- `N = σ t (1 + t) + c ((1 + t) w² + σ (u - v)²)`, `c = x(1 - x)`, `σ = s(1 - s)`,
`w = s u + (1 - s) v`. -/
def i3FPoly (x s u v t : ℝ) : ℝ :=
  s * (1 - s) * t * (1 + t) +
    x * (1 - x) * ((1 + t) * (s * u + (1 - s) * v) ^ 2 + s * (1 - s) * (u - v) ^ 2)

/-- The five-dimensional parametric integral of the dotted integral `F`. -/
noncomputable def i3FInt (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)))),
    ((z.1 * (1 - z.1) * (z.2.1 * (1 - z.2.1)) : ℝ) : ℂ) ^ (2 * ε) * (z.2.2.2.2 : ℂ) ^ ε *
      ((1 + z.2.2.2.2 : ℝ) : ℂ) ^ (4 * ε - 1) *
      ((i3FPoly z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 : ℝ) : ℂ) ^ (-1 - 3 * ε)

/-- **The finite dotted integral of the `I₃` sector**, Kira `lbl[1,0,1,1,1,0,1,2,0]` in LR96's
normalization divided by `C(ε)`: `Γ(1 + 3ε) / (2 Γ(1 + ε)³) · i3FInt ε`. -/
noncomputable def setDI3F (ε : ℂ) : ℂ := Gamma (1 + 3 * ε) / (2 * Gamma (1 + ε) ^ 3) * i3FInt ε

end QED.ThreeLoopD
