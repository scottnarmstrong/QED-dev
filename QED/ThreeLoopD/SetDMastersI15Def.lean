/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Def

/-!
# Set (d) of `A₁⁽⁶⁾`: the master `I₁₅`, defined through a representation analytic at `ε = 0`

**The integral.** LR96's `I₁₅ = ∫ 1 / (D₂ D₃ D₄ D₅)` (Kira master `lbl[0,0,0,1,1,1,1,0,0]`;
normalization as in `QED.DimReg.LR96Family`). With `q = k₁ + k₂` and `k₃` fixed, `k₂` occurs only
in `D₄`, a unit tadpole `Γ(-1 + ε)` (`QED.DimReg.tadpole`); the three lines `D₂, D₃, D₅` form
the equal-mass two-loop sunrise with on-shell external momentum `p` (`p² = -1`). The lines
`D₃, D₅` give the equal-mass bubble `Γ(ε) ∫₀¹ c ^ (-ε) (q² + 1/c) ^ (-ε) dx`, `c = x(1 - x)`
(`QED.DimReg.integral_massiveBubbleFamily_one`), and the on-shell one-loop integral of `D₂`
against `((p - q)² + 1/c) ^ (-ε)` in its Feynman parameter `u` gives, per loop measure
`dᵈk / π ^ (d/2)`, `d = 4 - 2ε`,

  `sunrise = Γ(2ε - 1) T(ε)`,  `T(ε) = ∫_{(0,1)²} c ^ (ε - 1) u ^ (ε - 1) P ^ (1 - 2ε)`,

with `P = c (1 - u)² + u = (x + (1 - x) u)(1 - x + x u)` (`QED.ThreeLoopD.i9Poly x u 1`). This
factorization is a convention recorded here, as for `I₉`, `I₁₄` and `I₁₆`.

**The subtraction.** `T(ε)` converges only for `0 < re ε < 1/2` (it diverges at `x = 0, 1` and
at `u = 0`). With `s = 1 - 2ε` split `P ^ s = u ^ s + c ^ s + Ψ`, `Ψ = P ^ s - u ^ s - c ^ s`;
`u ^ s` is the value at `c = 0`, `c ^ s` the value at `u = 0`, and `Ψ` vanishes at both. Then

  `T = B(ε, ε) / (1 - ε) + B(1 - ε, 1 - ε) / ε + K(ε)`,
  `K(ε) = ∫∫ c ^ (ε - 1) u ^ (ε - 1) Ψ` (`QED.ThreeLoopD.i15K`).

`Ψ` is the `y = 1` face of `I₉`'s `Ψ` at `ε' = 2ε/3` (`QED.ThreeLoopD.i15Psi_eq_i9Psi`), so
`|Ψ| ≤ C (c u) ^ (1/4)` and `K` converges near `ε = 0`; the right side
(`QED.ThreeLoopD.i15T`) defines `QED.ThreeLoopD.lr96I15`. Numerically (`setDI15/num.py`) the
Taylor coefficients of `K` agree with those forced by the LR96 table to 18 digits.

## Main definitions

* `QED.ThreeLoopD.i15Feyn`: the Feynman-parameter integral `T(ε)`.
* `QED.ThreeLoopD.i15Psi`, `QED.ThreeLoopD.i15K`, `QED.ThreeLoopD.i15Closed`,
  `QED.ThreeLoopD.i15T`.
* `QED.ThreeLoopD.lr96I15`, `QED.ThreeLoopD.setDMasterI15`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- The weight `c ^ (ε - 1) u ^ (ε - 1)`, `c = x(1 - x)`. -/
noncomputable def i15Wt (ε : ℂ) (x u : ℝ) : ℂ :=
  ((x * (1 - x) : ℝ) : ℂ) ^ (ε - 1) * (u : ℂ) ^ (ε - 1)

/-- **The Feynman-parameter integral of the sunrise in `I₁₅`**, `T(ε)` (convergent for
`0 < re ε < 1/2`). -/
noncomputable def i15Feyn (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
    i15Wt ε z.1 z.2 * ((i9Poly z.1 z.2 1 : ℝ) : ℂ) ^ (1 - 2 * ε)

/-- `Ψ = P ^ s - u ^ s - c ^ s`, `s = 1 - 2ε`, `P = c (1 - u)² + u`. -/
noncomputable def i15Psi (ε : ℂ) (x u : ℝ) : ℂ :=
  ((i9Poly x u 1 : ℝ) : ℂ) ^ (1 - 2 * ε) - (u : ℂ) ^ (1 - 2 * ε) -
    ((x * (1 - x) : ℝ) : ℂ) ^ (1 - 2 * ε)

/-- The two-dimensional integral `K(ε) = ∫∫ c ^ (ε - 1) u ^ (ε - 1) Ψ`. -/
noncomputable def i15K (ε : ℂ) : ℂ :=
  ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i15Wt ε z.1 z.2 * i15Psi ε z.1 z.2

/-- The Beta-function part of `T`. -/
noncomputable def i15Closed (ε : ℂ) : ℂ :=
  i9Beta ε ε / (1 - ε) + i9Beta (1 - ε) (1 - ε) / ε

/-- **The continued Feynman-parameter integral** `T(ε)` of the sunrise. -/
noncomputable def i15T (ε : ℂ) : ℂ := i15Closed ε + i15K ε

/-- `I₁₅` in LR96's normalization, `1 / (D₂ D₃ D₄ D₅)`: the unit tadpole times the on-shell
sunrise `Γ(2ε - 1) T(ε)`, with `T` continued by `QED.ThreeLoopD.i15T`. Each loop carries
`QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I15 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 *
    (QED.DimReg.tadpole 1 1 (4 - 2 * ω) * (Gamma (2 * ω - 1) * i15T ω))

/-- The master `I₁₅ C⁻¹`. -/
noncomputable def setDMasterI15 (ε : ℂ) : ℂ := lr96I15 ε / lr96C ε

/-- `Ψ` is the `y = 1` face of `I₉`'s `Ψ`, at `ε' = 2ε/3`. -/
theorem i15Psi_eq_i9Psi (ε : ℂ) (x u : ℝ) : i15Psi ε x u = i9Psi (2 * ε / 3) x u 1 := by
  have e : (1 : ℂ) - 3 * (2 * ε / 3) = 1 - 2 * ε := by ring
  simp only [i15Psi, i9Psi, e, mul_one]

end QED.ThreeLoopD
