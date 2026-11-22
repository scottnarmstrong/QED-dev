/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersGamma2
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Set (d) of `A₁⁽⁶⁾`: the master `I₉`, defined through a representation analytic at `ε = 0`

**The integral.** LR96's `I₉ = ∫ 1 / (D₂ D₃ D₅ D₆ D₇)` (Kira master `lbl[0,1,1,1,0,1,1,0,0]`;
normalization as in `QED.DimReg.LR96Family`). With `q = k₁ + k₂`, the photons `D₆ = k₁²`,
`D₇ = k₂²` form a massless bubble `G(1, 1) (q²) ^ (-ε)` (`QED.ThreeLoopD.masslessBubble`), the
lines `D₃, D₅` an equal-mass bubble `Γ(ε) ∫₀¹ (1 + x(1 - x) q²) ^ (-ε) dx`
(`QED.DimReg.integral_massiveBubbleFamily_one`), and `D₂ = (p - q)² + 1` closes the electron line
on shell. Joining `(q²) ^ (-ε)` and `(q² + 1/(x(1 - x))) ^ (-ε)` by a Feynman parameter `y`
(`QED.DimReg.integral_feynmanJoin`) and doing the on-shell one-loop integral with mass
`y / (x(1 - x))` and power `2ε` in its Feynman parameter `u = 1 - w`
(`QED.DimReg.integral_onShellMassFamily`) gives, per loop measure `dᵈk / π ^ (d/2)`,
`d = 4 - 2ε`,

  `I₉ = π ^ (3ε) G(1, 1) Γ(3ε - 1) / Γ(ε) · T(ε)`,
  `T(ε) = ∫_{(0,1)³} c ^ (2ε - 1) w ^ (2ε - 1) y ^ (ε - 1) (1 - y) ^ (ε - 1) P ^ (1 - 3ε)`,

with `c = x(1 - x)` and `P = c (1 - w)² + w y` (`QED.ThreeLoopD.i9Feyn`). This factorization
is a convention recorded here, as for `I₁₄` and `I₁₆` in `QED.ThreeLoopD.SetDMastersGamma2`.

**Why not the integral itself.** `T(ε)` converges only for `0 < re ε < 1/3`: it diverges at the
faces `x = 0`, `x = 1`, `w = 0`, `y = 0`, `y = 1` as soon as `re ε ≤ 0` (the faces `x = 0, 1`
come from `P ~ w y` there, which turns `c ^ (-ε) (P / c) ^ (1 - 3ε)` into `c ^ (2ε - 1)`). A
Bochner integral would silently be `0` there. The master is therefore defined through a
subtracted representation (`QED.ThreeLoopD.i9T`), valid on a neighbourhood of `ε = 0`.

**The subtraction.** Write `s = 1 - 3ε` and split `P ^ s = (w y) ^ s + c ^ s + Ψ` with
`Ψ = P ^ s - (w y) ^ s - c ^ s` (`QED.ThreeLoopD.i9Psi`); `(w y) ^ s` is the value at
`c = 0`, `c ^ s` the value at `w = 0`, and `Ψ` vanishes at both. Then split `Ψ` in `y` as
`(1 - y) Ψ|_{y=0} + y Ψ|_{y=1} + Ψ_sub` (`QED.ThreeLoopD.i9PsiSub`). Each of the first four
pieces is a product of Beta integrals or a Beta integral times the two-dimensional integral
`K(ε) = ∫∫ c ^ (2ε - 1) w ^ (2ε - 1) Ψ|_{y=1}` (`QED.ThreeLoopD.i9K`), and the rest is the
three-dimensional remainder `QED.ThreeLoopD.i9Rem`. On `0 < re ε < 1/3`,

  `T = B(2ε, 2ε) B(1 - 2ε, ε) / (1 - ε) + B(1 - ε, 1 - ε) B(ε, ε) / (2ε)
     + B(1 - ε, 1 - ε) (B(2ε, 3 - 6ε) - 1/(2ε)) B(ε, 1 + ε) + B(1 + ε, ε) K + Rem`.

`|Ψ|_{y=1}| ≤ C min(c, w) ^ (1/2)` and `|Ψ_sub| ≤ C min(c, w, y, 1 - y) ^ (1/2)`, so `K` and
`Rem` converge for `-1/16 < re ε < 1/6`: the right side is the continuation, and it is this right
side (`QED.ThreeLoopD.i9T`, with `B(a, b) = Γ(a) Γ(b) / Γ(a + b)`, `QED.ThreeLoopD.i9Beta`)
that defines `QED.ThreeLoopD.lr96I9`. Numerically (`setD4/i9_dec.py`) it agrees with the
Mellin–Barnes sum of `T` to ten digits at `ε = 0.2`.

## Main definitions

* `QED.ThreeLoopD.i9Feyn`: the Feynman-parameter integral `T(ε)`.
* `QED.ThreeLoopD.i9K`, `QED.ThreeLoopD.i9Rem`, `QED.ThreeLoopD.i9Closed`, `QED.ThreeLoopD.i9T`.
* `QED.ThreeLoopD.lr96I9`, `QED.ThreeLoopD.setDMasterI9`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- `B(a, b) = Γ(a) Γ(b) / Γ(a + b)`. -/
noncomputable def i9Beta (a b : ℂ) : ℂ := Gamma a * Gamma b / Gamma (a + b)

/-- The polynomial `P = x(1 - x)(1 - w)² + w y`. -/
def i9Poly (x w y : ℝ) : ℝ := x * (1 - x) * (1 - w) ^ 2 + w * y

/-- The weight `c ^ (2ε - 1) w ^ (2ε - 1)`, `c = x(1 - x)`. -/
noncomputable def i9Wt (ε : ℂ) (x w : ℝ) : ℂ :=
  ((x * (1 - x) : ℝ) : ℂ) ^ (2 * ε - 1) * (w : ℂ) ^ (2 * ε - 1)

/-- The weight `y ^ (ε - 1) (1 - y) ^ (ε - 1)`. -/
noncomputable def i9WtY (ε : ℂ) (y : ℝ) : ℂ := (y : ℂ) ^ (ε - 1) * ((1 - y : ℝ) : ℂ) ^ (ε - 1)

/-- **The Feynman-parameter integral of `I₉`**, `T(ε)` (convergent for `0 < re ε < 1/3`). -/
noncomputable def i9Feyn (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
    i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * ((i9Poly z.1 z.2.1 z.2.2 : ℝ) : ℂ) ^ (1 - 3 * ε)

/-- `Ψ = P ^ s - (w y) ^ s - c ^ s`, `s = 1 - 3ε`. -/
noncomputable def i9Psi (ε : ℂ) (x w y : ℝ) : ℂ :=
  ((i9Poly x w y : ℝ) : ℂ) ^ (1 - 3 * ε) - ((w * y : ℝ) : ℂ) ^ (1 - 3 * ε) -
    ((x * (1 - x) : ℝ) : ℂ) ^ (1 - 3 * ε)

/-- `Ψ_sub = Ψ - (1 - y) Ψ|_{y=0} - y Ψ|_{y=1}`. -/
noncomputable def i9PsiSub (ε : ℂ) (x w y : ℝ) : ℂ :=
  i9Psi ε x w y - (1 - y : ℂ) * i9Psi ε x w 0 - (y : ℂ) * i9Psi ε x w 1

/-- The two-dimensional integral `K(ε) = ∫∫ c ^ (2ε - 1) w ^ (2ε - 1) Ψ|_{y=1}`. -/
noncomputable def i9K (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i9Wt ε z.1 z.2 * i9Psi ε z.1 z.2 1

/-- The three-dimensional remainder
`∫ c ^ (2ε - 1) w ^ (2ε - 1) y ^ (ε - 1) (1 - y) ^ (ε - 1) Ψ_sub`. -/
noncomputable def i9Rem (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
    i9Wt ε z.1 z.2.1 * i9WtY ε z.2.2 * i9PsiSub ε z.1 z.2.1 z.2.2

/-- The Beta-function part of `T`. -/
noncomputable def i9Closed (ε : ℂ) : ℂ :=
  i9Beta (2 * ε) (2 * ε) * i9Beta (1 - 2 * ε) ε / (1 - ε) +
    i9Beta (1 - ε) (1 - ε) * i9Beta ε ε / (2 * ε) +
    i9Beta (1 - ε) (1 - ε) * (i9Beta (2 * ε) (3 - 6 * ε) - 1 / (2 * ε)) * i9Beta ε (1 + ε)

/-- **The continued Feynman-parameter integral** `T(ε)`. -/
noncomputable def i9T (ε : ℂ) : ℂ := i9Closed ε + i9Beta (1 + ε) ε * i9K ε + i9Rem ε

/-- `I₉` in LR96's normalization, `1 / (D₂ D₃ D₅ D₆ D₇)`:
`π ^ (3ε) G(1, 1) Γ(3ε - 1) / Γ(ε) T(ε)`, with `T` continued by `QED.ThreeLoopD.i9T`. Each loop
carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I9 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 *
    (masslessBubble (4 - 2 * ω) * (Gamma (3 * ω - 1) / Gamma ω * i9T ω))

/-- The master `I₉ C⁻¹`. -/
noncomputable def setDMasterI9 (ε : ℂ) : ℂ := lr96I9 ε / lr96C ε

end QED.ThreeLoopD
