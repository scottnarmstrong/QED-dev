/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13Def
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Set (d) of `A₁⁽⁶⁾`: the master `I₅`, defined through a representation analytic at `ε = 0`

**The integral.** LR96's `I₅ = ∫ 1 / (D₁ D₃ D₄ D₅ D₇ D₈)` (Kira master
`lbl[0,1,1,1,1,1,1,0,0]`; normalization as in `QED.DimReg.LR96Family`), with
`D₁ = (p - k₁)² + 1`, `D₃ = (p - k₁ - k₂ - k₃)² + 1`, `D₄ = (p - k₂ - k₃)² + 1`,
`D₅ = (p - k₃)² + 1`, `D₇ = k₂²`, `D₈ = k₃²`, `p² = -1`. The loop `k₁` runs only through
`D₁, D₃`: it is the equal-mass bubble of momentum `s = k₂ + k₃`, `Γ(ε) b_ε(s²)`
(`QED.ThreeLoopD.i13Bub`, `QED.DimReg.integral_massiveBubbleFamily_one`). What remains is the
two-loop on-shell graph with photons `k₂, k₃`, electrons `p - k₃` and `p - s`, and the bubble on
the line `s`. Its inner loop `k = k₃` at fixed `s` is the on-shell triangle

  `Tri(s) = ∫ dᵈk / π ^ (d/2) 1 / (k² (s - k)² ((p - k)² + 1)) = Γ(1 + ε) · i5Tri`,

and the last loop is the radial integral over `t = s²` of `b_ε(t) ⟨Tri(s) / w⟩_t`, where
`w = D₄ = (p - s)² + 1` and `⟨·⟩_t` is the average over the directions of `s`. On shell,
`p·s = i √t z` and `w = t - 2 i √t z` (`QED.ThreeLoopD.i5W`), and the average is
`N_ε ∫₋₁¹ (1 - z²) ^ (1/2 - ε) (·) dz`, `N_ε = Γ(2 - ε) / (√π Γ(3/2 - ε))`
(`QED.ThreeLoopD.i5Nrm`), as for `QED.ThreeLoopD.i8Ang`.

**The triangle.** Feynman parameters `a, b, c` for `k², (s - k)², (p - k)² + 1` give
`U = a + b + c` and `F = c² + a b t + b c w` (Euclidean, `p² = -1`). The Cheng–Wu choice
`b = 1` gives

  `i5Tri ε t w = ∫₀^∞ ∫₀^∞ (1 + a + c) ^ (-1 + 2ε) (c² + a t + c w) ^ (-1 - ε) da dc`
  (`QED.ThreeLoopD.i5Tri`).

Here `re (c² + a t + c w) = c² + a t + c t > 0`, so the principal power is the continuation
from real `p`. Per loop measure `dᵈk / π ^ (d/2)`, `d = 4 - 2ε`,

  `I₅ = π ^ (3ε) Γ(ε) Γ(1 + ε) / Γ(2 - ε) · T(ε)`,  `T(ε) = ∫₀^∞ t ^ (1 - ε) b_ε(t) K_ε(t) dt`,
  `K_ε(t) = N_ε ∫₋₁¹ (1 - z²) ^ (1/2 - ε) i5Tri ε t w / w dz` (`QED.ThreeLoopD.i5Ker`).

This factorization is a convention recorded here, as for `I₈`, `I₉` and `I₁₃`.

**Why not the integral itself.** `T(ε)` converges only for `0 < re ε < 1/2`: at large `t`,
`b_ε(t) ~ α₀ t ^ (-ε)` and, by expansion by regions in `Tri` (soft `k ~ 1`: the on-shell bubble
`Γ(ε) / (1 - 2ε)` over `s²`; hard `k ~ s`: the massless integral
`Γ(1 + ε) Γ(-ε) Γ(1 - ε) / Γ(1 - 2ε) (s²) ^ (-1 - ε)`), with `G = Γ(1 - ε)² / Γ(1 - 2ε)`,

  `K_ε(t) = ε⁻¹ (t⁻² / (1 - 2ε) - G t ^ (-2 - ε)) + O(t ^ (-3 + |re ε|) log t)`.

A Bochner integral would silently be `0` near `ε = 0`, so the master is defined through a
subtracted representation (`QED.ThreeLoopD.i5T`).

**The subtraction.** The terms of `t ^ (1 - ε) b_ε(t) K_ε(t)` not integrable at infinity near
`ε = 0` are

  `α₀ ε⁻¹ (t ^ (-1 - 2ε) / (1 - 2ε) - G t ^ (-1 - 3ε))` (`QED.ThreeLoopD.i5Asym`),

with `α₀ = G / (1 - 2ε)` (`QED.ThreeLoopD.i13Al0`). We subtract them on `t > 1`, where
`∫₁^∞ t ^ a dt = -1/(a + 1)` (`QED.ThreeLoopD.i5Tail`); the rest (`QED.ThreeLoopD.i5Rem`) has
integrand `O(t ^ (-2 + 3 max(0, -re ε)) log t)` at infinity and `O(t ^ (-2 re ε))` at `0`, so it
converges for `-1/3 < re ε < 1/2`. On `0 < re ε < 1/2` both sides agree, and the right side
`QED.ThreeLoopD.i5T = i5Tail + i5Rem` is the continuation that defines `QED.ThreeLoopD.lr96I5`.
The leading pole is `Γ(ε) Γ(1 + ε) α₀ ε⁻¹ (1/(2ε) - G/(3ε)) ~ 1/(6ε³)`, as in the LR96 table.

**Numerics.** With `a = c(μ - c)/t` the triangle becomes `∫₀^∞ dμ h(t, μ) W(t, μ)`, two
one-dimensional integrals. Evaluated with ε-Taylor arithmetic in 192-bit ball
arithmetic, the Laurent coefficients of `I₅ C⁻¹` at `ε⁻¹, ε⁰, ε¹` agree with the LR96 table
(with Laporta's `2 C₁` at order `ε`) to `4·10⁻³⁹`, `1·10⁻³⁶` and `2·10⁻³⁴`, and those at `ε²`,
`ε³` agree with the 30-digit values of Laporta (2001) to `4·10⁻²⁹` and `4·10⁻²⁸`.

## Main definitions

* `QED.ThreeLoopD.i5Nrm`, `QED.ThreeLoopD.i5W`, `QED.ThreeLoopD.i5Tri`, `QED.ThreeLoopD.i5Ker`.
* `QED.ThreeLoopD.i5Asym`, `QED.ThreeLoopD.i5Tail`, `QED.ThreeLoopD.i5Rem`,
  `QED.ThreeLoopD.i5T`.
* `QED.ThreeLoopD.lr96I5`, `QED.ThreeLoopD.setDMasterI5`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- The normalization of the on-shell angular average, `N_ε = Γ(2 - ε) / (√π Γ(3/2 - ε))`. -/
noncomputable def i5Nrm (ε : ℂ) : ℂ := Gamma (2 - ε) / (Gamma (1 / 2) * Gamma (3 / 2 - ε))

/-- `w = (p - s)² + 1 = t - 2 i √t z` at `s² = t`, `p·s = i √t z`, `p² = -1`. -/
noncomputable def i5W (t z : ℝ) : ℂ := (t : ℂ) - 2 * ((Real.sqrt t * z : ℝ) : ℂ) * I

/-- The on-shell triangle `∫ dᵈk / π ^ (d/2) 1 / (k² (s - k)² ((p - k)² + 1))` divided by
`Γ(1 + ε)`, in Cheng–Wu form: `∫₀^∞ ∫₀^∞ (1 + a + c) ^ (-1 + 2ε) (c² + a t + c w) ^ (-1 - ε)`,
with `t = s²` and `w = (p - s)² + 1`. -/
noncomputable def i5Tri (ε : ℂ) (t : ℝ) (w : ℂ) : ℂ :=
  ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), ((1 + q.1 + q.2 : ℝ) : ℂ) ^ (-1 + 2 * ε) *
    (((q.2 ^ 2 + q.1 * t : ℝ) : ℂ) + q.2 * w) ^ (-1 - ε)

/-- The two-loop on-shell kernel `⟨i5Tri / w⟩_t`, the angular average at `s² = t` of the
triangle times `1 / ((p - s)² + 1)`. -/
noncomputable def i5Ker (ε : ℂ) (t : ℝ) : ℂ :=
  i5Nrm ε * ∫ z in Ioo (-1 : ℝ) 1,
    ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) * i5Tri ε t (i5W t z) / i5W t z

/-- The two large-`t` terms of `t ^ (1 - ε) b_ε(t) K_ε(t)` that are not integrable at infinity
near `ε = 0`. -/
noncomputable def i5Asym (ε : ℂ) (t : ℝ) : ℂ :=
  i13Al0 ε / ε * ((t : ℂ) ^ (-1 - 2 * ε) / (1 - 2 * ε) - i13G ε * (t : ℂ) ^ (-1 - 3 * ε))

/-- The continued integrals `∫₁^∞` of the two terms of `QED.ThreeLoopD.i5Asym`,
`∫₁^∞ t ^ a dt = -1/(a + 1)`. -/
noncomputable def i5Tail (ε : ℂ) : ℂ :=
  i13Al0 ε / ε * (1 / ((1 - 2 * ε) * (2 * ε)) - i13G ε / (3 * ε))

/-- The subtracted radial integral, convergent for `-1/3 < re ε < 1/2`. -/
noncomputable def i5Rem (ε : ℂ) : ℂ :=
  (∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t) +
    ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (1 - ε) * i13Bub ε t * i5Ker ε t - i5Asym ε t)

/-- **The continued radial integral** `T(ε) = ∫₀^∞ t ^ (1 - ε) b_ε(t) K_ε(t) dt`. -/
noncomputable def i5T (ε : ℂ) : ℂ := i5Tail ε + i5Rem ε

/-- `I₅` in LR96's normalization, `1 / (D₁ D₃ D₄ D₅ D₇ D₈)`:
`π ^ (3ε) Γ(ε) Γ(1 + ε) / Γ(2 - ε) T(ε)`, with `T` continued by `QED.ThreeLoopD.i5T`. Each
loop carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I5 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 * (Gamma ω * Gamma (1 + ω) / Gamma (2 - ω) * i5T ω)

/-- The master `I₅ C⁻¹`. -/
noncomputable def setDMasterI5 (ε : ℂ) : ℂ := lr96I5 ε / lr96C ε

end QED.ThreeLoopD
