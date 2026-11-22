/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersGamma
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Set (d) of `A₁⁽⁶⁾`: the master `I₂`, defined through a parametric integral analytic at `ε = 0`

**The integral.** LR96's `I₂ = ∫ 1 / (D₁ D₂ D₃ D₄ D₇ D₈)` (Kira master `lbl[0,1,1,1,0,1,1,1,0]`;
normalization as in `QED.DimReg.LR96Family`) is a tetrahedron. Its four vertices are
`W` (where `p` enters), `X`, `Y` and `Z` (where `p` leaves): the unit-mass lines
`D₁ = (p - k₁)² + 1` (`W X`), `D₂ = (p - k₁ - k₂)² + 1` (`X Y`) and
`D₃ = (p - k₁ - k₂ - k₃)² + 1` (`Y W`) form the massive triangle, the photons `D₇ = k₂²` (`X Z`)
and `D₈ = k₃²` (`Y Z`) and the electron line `D₄ = (p - k₂ - k₃)² + 1` (`W Z`) join it to `Z`,
and `p² = -1`. No line pair forms a bubble, so no loop integrates in closed form.

**Parametric form.** With unit powers, three loops and `d = 4 - 2ε`, the Feynman-parameter
formula (measure `dᵈk / π ^ (d/2)` per loop, Euclidean signature) reads

  `∫ 1 / (D₁ D₂ D₃ D₄ D₇ D₈) = Γ(3ε) ∫ δ(1 - x₁ - x₂ - x₃) 𝒰 ^ (-2 + 4ε) ℱ ^ (-3ε) d⁶x`,

where we used the Cheng–Wu form of the delta function on the triangle's parameters. Write
`x₁ = α₁, x₂ = α₂, x₃ = α₃` (`α₁ + α₂ + α₃ = 1`) and `y₄ = x₄`, `y₇ = x₇`, `y₈ = x₈`.
Contracting the triangle leaves the three lines `D₄, D₇, D₈` between one vertex and `Z`, and
the Symanzik polynomials become (checked symbolically)

  `𝒰 = a b + b c + c a`, `ℱ = 𝒰 + y₄² (a + b)`,
  `a = y₇ + α₁ α₂`, `b = y₈ + α₂ α₃`, `c = y₄ + α₁ α₃`

(`QED.ThreeLoopD.i2LineA`, `QED.ThreeLoopD.i2LineB`, `QED.ThreeLoopD.i2LineC`,
`QED.ThreeLoopD.i2U`, `QED.ThreeLoopD.i2F`). On shell (`p² = -1`) the mass term `y₄ 𝒰` and the
momentum term `-y₄ (a b + α₁ α₃ (a + b))` combine to `y₄² (a + b)`. We parametrize the simplex by
`α₁ = (1 - w) x`, `α₂ = w`, `α₃ = (1 - w)(1 - x)`, `x, w ∈ (0, 1)`, with Jacobian `1 - w`;
the exchange `X ↔ Y` of the graph is `x ↦ 1 - x`, `y₇ ↔ y₈`. Thus

  `I₂ = π ^ (3ε) Γ(3ε) P(ε)`, `P(ε) = ∫ (1 - w) 𝒰 ^ (-2 + 4ε) ℱ ^ (-3ε)`

over `x, w ∈ (0, 1)`, `y₄, y₇, y₈ ∈ (0, ∞)` (`QED.ThreeLoopD.i2PInt`), and, since
`C(ε) = (π ^ ε Γ(1 + ε))³`, `I₂ C⁻¹ = Γ(1 + 3ε) / (3ε Γ(1 + ε)³) · P(ε)`. The parametric formula
is a convention recorded here, as for `I₃` in `QED.ThreeLoopD.SetDMastersI3F`.

**Why no subtraction.** The only divergence of `I₂` at `d = 4` is the overall ultraviolet one,
which is the explicit factor `Γ(3ε)`: the graph has no divergent subgraph and its infrared
region (both photons soft) is finite. So `P` itself is analytic at `0`. An iterated sector
decomposition of the projective integral (120 sectors, monomial exponents
`A + B ε` with `A ≥ 0`) shows that `P(ε)` converges absolutely for `-1/2 < re ε < 3/4`; for
`0 < re ε < 3/4` it equals the momentum integral, and on the strip it is the continuation that
defines `QED.ThreeLoopD.lr96I2`. Since `𝒰 ≤ ℱ ≤ (1 + y₄) 𝒰` (as `𝒰 ≥ c (a + b) ≥ y₄ (a + b)`),
`|𝒰 ^ (-2 + 4ε) ℱ ^ (-3ε)| ≤ 𝒰 ^ (-2 + re ε) (1 + y₄) ^ (3 |re ε|)`.

**Numerics.** `P(0) = 6ζ₃` is the period of the tetrahedron. Double-exponential quadrature over
the sectors gives `P(0), P'(0), P''(0)/2` equal to the values implied by the
Laporta (2001) expansion of `I₂ C⁻¹`, `6ζ₃`, `-13π⁴/30 + 30ζ₃ - π²` and
`12π² ln 2 + 43/2 π²ζ₃ - 13/6 π⁴ - 255/2 ζ₅ + 72ζ₃ - 4π²`, to twelve digits (`h = 0.2`,
`N = 16`); direct quadrature of the integral as written here agrees to five digits.

## Main definitions

* `QED.ThreeLoopD.i2LineA`, `QED.ThreeLoopD.i2LineB`, `QED.ThreeLoopD.i2LineC`.
* `QED.ThreeLoopD.i2U`, `QED.ThreeLoopD.i2F`, `QED.ThreeLoopD.i2Dom`, `QED.ThreeLoopD.i2PInt`.
* `QED.ThreeLoopD.lr96I2`, `QED.ThreeLoopD.setDMasterI2`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- `a = y₇ + α₁ α₂`, `α₁ = (1 - w) x`, `α₂ = w`: the photon `D₇` after the triangle. -/
def i2LineA (x w y₇ : ℝ) : ℝ := y₇ + w * (1 - w) * x

/-- `b = y₈ + α₂ α₃`, `α₂ = w`, `α₃ = (1 - w)(1 - x)`: the photon `D₈` after the triangle. -/
def i2LineB (x w y₈ : ℝ) : ℝ := y₈ + w * (1 - w) * (1 - x)

/-- `c = y₄ + α₁ α₃`: the electron line `D₄` after the triangle. -/
def i2LineC (x w y₄ : ℝ) : ℝ := y₄ + (1 - w) ^ 2 * x * (1 - x)

/-- The first Symanzik polynomial `𝒰 = a b + b c + c a`. -/
def i2U (x w y₄ y₇ y₈ : ℝ) : ℝ :=
  i2LineA x w y₇ * i2LineB x w y₈ + i2LineB x w y₈ * i2LineC x w y₄ +
    i2LineC x w y₄ * i2LineA x w y₇

/-- The second Symanzik polynomial on shell, `ℱ = 𝒰 + y₄² (a + b)`. -/
def i2F (x w y₄ y₇ y₈ : ℝ) : ℝ :=
  i2U x w y₄ y₇ y₈ + y₄ ^ 2 * (i2LineA x w y₇ + i2LineB x w y₈)

/-- The domain `(x, w, y₄, y₇, y₈) ∈ (0, 1)² × (0, ∞)³`. -/
def i2Dom : Set (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))))

/-- **The parametric integral** `P(ε) = ∫ (1 - w) 𝒰 ^ (-2 + 4ε) ℱ ^ (-3ε)` over `i2Dom`. -/
noncomputable def i2PInt (ε : ℂ) : ℂ :=
  ∫ z in i2Dom, ((1 - z.2.1 : ℝ) : ℂ) *
    ((i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 : ℝ) : ℂ) ^ (-2 + 4 * ε) *
    ((i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 : ℝ) : ℂ) ^ (-3 * ε)

/-- `I₂` in LR96's normalization, `1 / (D₁ D₂ D₃ D₄ D₇ D₈)`: `π ^ (3ε) Γ(3ε) P(ε)`. Each loop
carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I2 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 * (Gamma (3 * ω) * i2PInt ω)

/-- The master `I₂ C⁻¹`. -/
noncomputable def setDMasterI2 (ε : ℂ) : ℂ := lr96I2 ε / lr96C ε

end QED.ThreeLoopD
