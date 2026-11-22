/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Def

/-!
# Set (d) of `A₁⁽⁶⁾`: the master `I₁₂`, defined through a representation analytic at `ε = 0`

**The integral.** LR96's `I₁₂ = ∫ 1 / (D₁ D₃ D₅ D₇)` (Kira master `lbl[0,1,0,0,1,1,1,0,0]`;
normalization as in `QED.DimReg.LR96Family`) is the on-shell three-loop banana with three unit
masses and one massless line: `D₁ = (p - k₁)² + 1`, `D₃ = (p - k₁ - k₂ - k₃)² + 1`,
`D₅ = (p - k₃)² + 1`, `D₇ = k₂²`, `p² = -1`. The lines `D₁, D₅` form an equal-mass bubble in
`s = 2p - k₁ - k₃`, `Γ(ε) ∫₀¹ (s² + 1/c) ^ (-ε) c ^ (-ε) dy` with `c = y(1 - y)`
(`QED.DimReg.integral_massiveBubbleFamily_one`), and `D₃, D₇` a bubble with one unit mass in
`s - p`, `Γ(ε) ∫₀¹ ((s - p)² + 1/t) ^ (-ε) (t(1 - t)) ^ (-ε) dt`. The last loop is the on-shell
one-loop integral with masses `1/c`, `1/t` and powers `ε, ε`, in its Feynman parameter `u`. Per
loop measure `dᵈk / π ^ (d/2)`, `d = 4 - 2ε`:

  `I₁₂ = π ^ (3ε) Γ(3ε - 2) F(ε)`,
  `F(ε) = ∫_{(0,1)³} (c t)^(2ε-2) (1 - t)^(-ε) (u(1 - u))^(ε-1) N^(2-3ε) dy dt du`,

with `N = X + Y - X Y`, `X = u t`, `Y = (1 - u) c`. This factorization is a convention recorded
here, as for `I₉`, `I₁₄`, `I₁₆`. Numerically (`setDI12/i12_mb.py`, a Mellin–Barnes sum after a
binomial expansion in `u(1 - u)`) `F` agrees with direct cubature at `ε = 0.6` to seven digits.

**Why not the integral itself.** `F` converges only for `1/2 < re ε < 2/3`: the faces `y = 0, 1`
and `t = 0` carry the power divergences `c ^ (2ε - 2)`, `t ^ (2ε - 2)` of the quadratically
divergent outer loop. The master is therefore defined through a subtracted representation.

**The subtraction.** Let `a = 2 - 3ε` and `W = (c t)^(2ε-1) (1 - t)^(-ε) (u(1 - u))^ε`, so that
the weight of `F` is `W / (X Y)`. Split
`N ^ a = X ^ a + Y ^ a + X Y Φ₀(X, Y) + X Y (Φ₁(X, Y) - a X ^ (a-1) - a Y ^ (a-1))` with
`Φ₀ = ((X + Y) ^ a - X ^ a - Y ^ a) / (X Y)` (`QED.ThreeLoopD.i12Phi0`, homogeneous of degree
`-3ε`) and `Φ₁ = (N ^ a - (X + Y) ^ a) / (X Y) + a X ^ (a-1) + a Y ^ (a-1)`
(`QED.ThreeLoopD.i12Phi1`, vanishing at `X = 0` and at `Y = 0`).
* The `X ^ a`, `Y ^ a`, `a X ^ (a-1)`, `a Y ^ (a-1)` pieces are products of Beta integrals.
* `∫ W Φ₁` converges near `ε = 0`: the remainder `QED.ThreeLoopD.i12R1`.
* In `∫ W Φ₀`, write `c = v h(v)` (`y = v/2` on half the range, `h(v) = (2 - v)/4`,
  `QED.ThreeLoopD.i12H`) and split `(v, t)` into the sectors `t < v` (`v = ρ`, `t = ρθ`) and
  `v < t` (`t = ρ`, `v = ρθ`). By homogeneity each sector is
  `∫ ρ ^ (ε-1) θ ^ (2ε-1) G(ρ, θ, u)` with `G` regular at `ρ = 0` and `θ = 0`
  (`QED.ThreeLoopD.i12GA`, `QED.ThreeLoopD.i12GB`, with `θ = 0` faces `QED.ThreeLoopD.i12GA0`,
  `QED.ThreeLoopD.i12GB0`), and the product subtraction
  `G = (G - G(0,θ) - G(ρ,0) + G(0,0)) + (G(0,θ) - G(0,0)) + (G(ρ,0) - G(0,0)) + G(0,0)` gives a
  three-dimensional remainder (`QED.ThreeLoopD.i12RA3`, `QED.ThreeLoopD.i12RB3`), `ε⁻¹` times a
  two-dimensional remainder (`QED.ThreeLoopD.i12TA`, `QED.ThreeLoopD.i12TB`), and closed forms.

On `1/2 < re ε < 2/3` this gives
`F = i12Closed + R₁ + R_A + R_B + (T_A + T_B) / ε`, and the right side is the continuation
(`QED.ThreeLoopD.i12Bracket`, with `QED.ThreeLoopD.i12Closed` the sum of the closed forms). It
defines `QED.ThreeLoopD.lr96I12`. The remainder combination
`QED.ThreeLoopD.i12Rest = ε (R₁ + R_A + R_B) + T_A + T_B` vanishes at `ε = 0`.

**Numerical checks** (`setDI12/decomp_fast.py`, product Gauss–Legendre): the right side agrees
with the Mellin–Barnes sum at `ε = 0.1` to nine digits and at `ε = -0.05` to fourteen, and
`Γ(3ε - 2) F / Γ(1 + ε)³` reproduces `QED.ThreeLoopD.setDLaurentI12` (LR96, Laporta 2001) at
all six orders `ε⁻³ … ε²` to ten digits.

## Main definitions

* `QED.ThreeLoopD.i12Phi0`, `QED.ThreeLoopD.i12Phi1`, `QED.ThreeLoopD.i12Wt`.
* `QED.ThreeLoopD.i12R1`, `QED.ThreeLoopD.i12RA3`, `QED.ThreeLoopD.i12RB3`,
  `QED.ThreeLoopD.i12TA`, `QED.ThreeLoopD.i12TB`, `QED.ThreeLoopD.i12Rest`.
* `QED.ThreeLoopD.i12Closed`, `QED.ThreeLoopD.i12Bracket`.
* `QED.ThreeLoopD.lr96I12`, `QED.ThreeLoopD.setDMasterI12`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- `Φ₀(X, Y) = ((X + Y) ^ a - X ^ a - Y ^ a) / (X Y)`, `a = 2 - 3ε`. -/
noncomputable def i12Phi0 (ε : ℂ) (X Y : ℝ) : ℂ :=
  (((X + Y : ℝ) : ℂ) ^ (2 - 3 * ε) - (X : ℂ) ^ (2 - 3 * ε) - (Y : ℂ) ^ (2 - 3 * ε)) /
    ((X * Y : ℝ) : ℂ)

/-- `Φ₁(X, Y) = (N ^ a - (X + Y) ^ a) / (X Y) + a X ^ (a - 1) + a Y ^ (a - 1)`,
`N = X + Y - X Y`, `a = 2 - 3ε`. -/
noncomputable def i12Phi1 (ε : ℂ) (X Y : ℝ) : ℂ :=
  (((X + Y - X * Y : ℝ) : ℂ) ^ (2 - 3 * ε) - ((X + Y : ℝ) : ℂ) ^ (2 - 3 * ε)) /
      ((X * Y : ℝ) : ℂ) +
    (2 - 3 * ε) * ((X : ℂ) ^ (1 - 3 * ε) + (Y : ℂ) ^ (1 - 3 * ε))

/-- The weight `W = (c t) ^ (2ε - 1) (1 - t) ^ (-ε) (u(1 - u)) ^ ε`. -/
noncomputable def i12Wt (ε : ℂ) (c t u : ℝ) : ℂ :=
  ((c * t : ℝ) : ℂ) ^ (2 * ε - 1) * ((1 - t : ℝ) : ℂ) ^ (-ε) * ((u * (1 - u) : ℝ) : ℂ) ^ ε

/-- The remainder `R₁ = ∫ W Φ₁(u t, (1 - u) c)`, `c = y(1 - y)`, over `(y, t, u) ∈ (0, 1)³`. -/
noncomputable def i12R1 (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
    i12Wt ε (z.1 * (1 - z.1)) z.2.1 z.2.2 *
      i12Phi1 ε (z.2.2 * z.2.1) ((1 - z.2.2) * (z.1 * (1 - z.1)))

/-- `h(v) = (2 - v) / 4`, so that `c = v h(v)` for `y = v / 2`. -/
noncomputable def i12H (v : ℝ) : ℝ := (2 - v) / 4

/-- The sector `t < v` (`v = ρ`, `t = ρθ`):
`G_A = h(ρ) ^ (2ε - 1) (1 - ρθ) ^ (-ε) (u(1 - u)) ^ ε Φ₀(uθ, (1 - u) h(ρ))`. -/
noncomputable def i12GA (ε : ℂ) (ρ θ u : ℝ) : ℂ :=
  ((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1) * ((1 - ρ * θ : ℝ) : ℂ) ^ (-ε) *
    ((u * (1 - u) : ℝ) : ℂ) ^ ε * i12Phi0 ε (u * θ) ((1 - u) * i12H ρ)

/-- The face `θ = 0` of `G_A`: `h(ρ) ^ (2ε - 1) (u(1 - u)) ^ ε · a ((1 - u) h(ρ)) ^ (-3ε)`. -/
noncomputable def i12GA0 (ε : ℂ) (ρ u : ℝ) : ℂ :=
  ((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
    ((2 - 3 * ε) * (((1 - u) * i12H ρ : ℝ) : ℂ) ^ (-3 * ε))

/-- The sector `v < t` (`t = ρ`, `v = ρθ`):
`G_B = h(ρθ) ^ (2ε - 1) (1 - ρ) ^ (-ε) (u(1 - u)) ^ ε Φ₀(u, (1 - u) θ h(ρθ))`. -/
noncomputable def i12GB (ε : ℂ) (ρ θ u : ℝ) : ℂ :=
  ((i12H (ρ * θ) : ℝ) : ℂ) ^ (2 * ε - 1) * ((1 - ρ : ℝ) : ℂ) ^ (-ε) *
    ((u * (1 - u) : ℝ) : ℂ) ^ ε * i12Phi0 ε u ((1 - u) * θ * i12H (ρ * θ))

/-- The face `θ = 0` of `G_B`: `h(0) ^ (2ε - 1) (1 - ρ) ^ (-ε) (u(1 - u)) ^ ε · a u ^ (-3ε)`. -/
noncomputable def i12GB0 (ε : ℂ) (ρ u : ℝ) : ℂ :=
  ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((1 - ρ : ℝ) : ℂ) ^ (-ε) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
    ((2 - 3 * ε) * (u : ℂ) ^ (-3 * ε))

/-- The sector weight `ρ ^ (ε - 1) θ ^ (2ε - 1)`. -/
noncomputable def i12SecWt (ε : ℂ) (ρ θ : ℝ) : ℂ := (ρ : ℂ) ^ (ε - 1) * (θ : ℂ) ^ (2 * ε - 1)

/-- The three-dimensional remainder of the sector `t < v`, over `(ρ, θ, u) ∈ (0, 1)³`. -/
noncomputable def i12RA3 (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
    i12SecWt ε z.1 z.2.1 * (i12GA ε z.1 z.2.1 z.2.2 - i12GA ε 0 z.2.1 z.2.2 -
      i12GA0 ε z.1 z.2.2 + i12GA0 ε 0 z.2.2)

/-- The three-dimensional remainder of the sector `v < t`, over `(ρ, θ, u) ∈ (0, 1)³`. -/
noncomputable def i12RB3 (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
    i12SecWt ε z.1 z.2.1 * (i12GB ε z.1 z.2.1 z.2.2 - i12GB ε 0 z.2.1 z.2.2 -
      i12GB0 ε z.1 z.2.2 + i12GB0 ε 0 z.2.2)

/-- The two-dimensional remainder of the face `ρ = 0` of the sector `t < v`, over
`(θ, u) ∈ (0, 1)²`. -/
noncomputable def i12TA (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
    (z.1 : ℂ) ^ (2 * ε - 1) * (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2)

/-- The two-dimensional remainder of the face `ρ = 0` of the sector `v < t`, over
`(θ, u) ∈ (0, 1)²`. -/
noncomputable def i12TB (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
    (z.1 : ℂ) ^ (2 * ε - 1) * (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2)

/-- **The remainder combination** `ε (R₁ + R_A + R_B) + T_A + T_B`. -/
noncomputable def i12Rest (ε : ℂ) : ℂ :=
  ε * (i12R1 ε + i12RA3 ε + i12RB3 ε) + i12TA ε + i12TB ε

/-- **The closed part of `F`**: the Beta-function pieces `X ^ a`, `Y ^ a`, `-a X ^ (a - 1)`,
`-a Y ^ (a - 1)`, the faces `θ = 0` of both sectors, and their corners `ρ = θ = 0`
(`B(a, b) = Γ(a) Γ(b) / Γ(a + b)`, `QED.ThreeLoopD.i9Beta`). -/
noncomputable def i12Closed (ε : ℂ) : ℂ :=
  i9Beta (2 * ε - 1) (2 * ε - 1) * i9Beta (1 - ε) (1 - ε) * i9Beta (2 - 2 * ε) ε +
    i9Beta (1 - ε) (1 - ε) * i9Beta (2 * ε - 1) (1 - ε) * i9Beta ε (2 - 2 * ε) -
    (2 - 3 * ε) * (i9Beta (2 * ε) (2 * ε) * i9Beta (1 - ε) (1 - ε) * i9Beta (2 - 2 * ε) (1 + ε) +
      i9Beta (1 - ε) (1 - ε) * i9Beta (2 * ε) (1 - ε) * i9Beta (1 + ε) (2 - 2 * ε)) +
    (2 - 3 * ε) * i9Beta (1 + ε) (1 - 2 * ε) * ((4 : ℂ) ^ ε - (2 : ℂ) ^ ε) / ε ^ 2 +
    (2 - 3 * ε) * (2 : ℂ) ^ (1 - 2 * ε) * i9Beta (1 - 2 * ε) (1 + ε) *
      (i9Beta ε (1 - ε) - 1 / ε) / (2 * ε) +
    (2 - 3 * ε) * ((2 : ℂ) ^ (1 + ε) * i9Beta (1 + ε) (1 - 2 * ε) +
      (2 : ℂ) ^ (1 - 2 * ε) * i9Beta (1 - 2 * ε) (1 + ε)) / (2 * ε ^ 2)

/-- **The continued Feynman-parameter integral** `F(ε)`. -/
noncomputable def i12Bracket (ε : ℂ) : ℂ := i12Closed ε + i12Rest ε / ε

/-- `I₁₂` in LR96's normalization, `1 / (D₁ D₃ D₅ D₇)`: `π ^ (3ε) Γ(3ε - 2) F(ε)`, with `F`
continued by `QED.ThreeLoopD.i12Bracket`. Each loop carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I12 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 * (Gamma (3 * ω - 2) * i12Bracket ω)

/-- The master `I₁₂ C⁻¹`. -/
noncomputable def setDMasterI12 (ε : ℂ) : ℂ := lr96I12 ε / lr96C ε

end QED.ThreeLoopD
