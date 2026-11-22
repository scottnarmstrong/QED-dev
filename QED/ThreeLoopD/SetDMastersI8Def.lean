/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13Def

/-!
# Set (d) of `A₁⁽⁶⁾`: the master `I₈`, defined through a representation analytic at `ε = 0`

**The integral.** LR96's `I₈ = ∫ 1 / (D₁ D₂ D₃ D₄ D₅)` (Kira master `lbl[0,0,0,1,1,1,1,1,0]`;
normalization as in `QED.DimReg.LR96Family`) has five unit-mass lines and no photon. Its three
vertices are joined as follows: lines `D₁, D₄` form an equal-mass bubble and lines `D₂, D₅` a
second one, both with total momentum `q = 2p - k₁ - k₂ - k₃` (`(p - k₁) + (p - k₂ - k₃) =
(p - k₁ - k₂) + (p - k₃) = q`), and `D₃ = (p - q)² + 1` closes the electron line on shell.
Each bubble is `Γ(ε) b_ε(q²)` (`QED.ThreeLoopD.i13Bub`,
`QED.DimReg.integral_massiveBubbleFamily_one`), and the last loop is
the radial integral `∫ dᵈq / π ^ (d/2) f(q²) g = Γ(d/2)⁻¹ ∫₀^∞ t ^ (d/2 - 1) f(t) ⟨g⟩_t dt`,
where `⟨g⟩_t` is the average of `g = 1 / ((p - q)² + 1)` over the directions of `q` at `q² = t`.
On shell (`p² = -1`), `(p - q)² + 1 = t - 2 p·q`, and symmetrizing `z ↦ -z` in `p·q = i √t z`
gives

  `A_ε(t) = ⟨1 / (t + 4 z²)⟩ = 2 N_ε ∫₀¹ (1 - z²) ^ (1/2 - ε) / (t + 4 z²) dz`,
  `N_ε = Γ(2 - ε) / (√π Γ(3/2 - ε))` (`QED.ThreeLoopD.i8Ang`),

i.e. `A_ε(t) = t⁻¹ ₂F₁(1, 1/2; 2 - ε; -4/t)`. Per loop measure `dᵈk / π ^ (d/2)`, `d = 4 - 2ε`,

  `I₈ = π ^ (3ε) Γ(ε)² / Γ(2 - ε) · T(ε)`,  `T(ε) = ∫₀^∞ t ^ (1 - ε) b_ε(t)² A_ε(t) dt`.

This factorization is a convention recorded here, as for `I₉`, `I₁₃`, `I₁₄` and `I₁₆`.

**Why not the integral itself.** `T(ε)` converges only for `1/3 < re ε < 3/2`: at large `t`,
`b_ε(t) ~ B(1 - ε, 1 - ε) t ^ (-ε)` and `A_ε(t) ~ 1/t`. A Bochner integral would silently be `0`
near `ε = 0`, so the master is defined through a subtracted representation
(`QED.ThreeLoopD.i8T`).

**The subtraction.** With the large-`t` expansion of `b_ε` recorded in
`QED.ThreeLoopD.SetDMastersI13Def` (`b_ε = α₀ u + (α₁ u + β₀)/t + O(t ^ (-2 + |re ε|))`,
`u = t ^ (-ε)`) and `A_ε(t) = 1/t - κ/t² + O(t ^ (-3))`, `κ = 4/d = 2/(2 - ε)`
(`QED.ThreeLoopD.i8Kap`), the terms of `t ^ (1 - ε) b_ε(t)² A_ε(t)` not integrable at infinity
near `ε = 0` are

  `α₀² t ^ (-3ε) + (2 α₀ α₁ - κ α₀²) t ^ (-1 - 3ε) + 2 α₀ β₀ t ^ (-1 - 2ε)`
  (`QED.ThreeLoopD.i8Asym`).

We subtract them on `t > 1`, where `∫₁^∞ t ^ a dt = -1/(a + 1)` (`QED.ThreeLoopD.i8Tail`); the
rest (`QED.ThreeLoopD.i8Rem`) has integrand `O(t ^ (-2 + 3 max(0, -re ε)))` at infinity and
`O(t ^ (1/2 - re ε))` at `0`, so it converges for `-1/3 < re ε < 3/2`. On `1/3 < re ε < 3/2`
both sides agree, and the right side `QED.ThreeLoopD.i8T = i8Tail + i8Rem` is the continuation
that defines `QED.ThreeLoopD.lr96I8`. Numerically the one-loop
normalization of `A_ε` reproduces `Γ(ε)/(1 - 2ε)` to twenty digits, the subtracted form agrees
with the direct integral at `ε = 0.45`, and the Laurent coefficients of `I₈ C⁻¹` reproduce the
LR96 table through `ε²`.

## Main definitions

* `QED.ThreeLoopD.i8Ang`, `QED.ThreeLoopD.i8Kap`.
* `QED.ThreeLoopD.i8Asym`, `QED.ThreeLoopD.i8Tail`, `QED.ThreeLoopD.i8Rem`,
  `QED.ThreeLoopD.i8T`.
* `QED.ThreeLoopD.lr96I8`, `QED.ThreeLoopD.setDMasterI8`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- The on-shell angular average `A_ε(t) = ⟨1 / ((p - q)² + 1)⟩` at `q² = t`, `p² = -1`:
`2 Γ(2 - ε) / (√π Γ(3/2 - ε)) ∫₀¹ (1 - z²) ^ (1/2 - ε) / (t + 4 z²) dz`. -/
noncomputable def i8Ang (ε : ℂ) (t : ℝ) : ℂ :=
  2 * Gamma (2 - ε) / (Gamma (1 / 2) * Gamma (3 / 2 - ε)) *
    ∫ z in Ioo (0 : ℝ) 1, ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - ε) / ((t + 4 * z ^ 2 : ℝ) : ℂ)

/-- `κ = 4 / d = 2 / (2 - ε)`, the `t⁻²` coefficient of `-A_ε(t)` at large `t`. -/
noncomputable def i8Kap (ε : ℂ) : ℂ := 2 / (2 - ε)

/-- The three large-`t` terms of `t ^ (1 - ε) b_ε(t)² A_ε(t)` that are not integrable at infinity
near `ε = 0`. -/
noncomputable def i8Asym (ε : ℂ) (t : ℝ) : ℂ :=
  i13Al0 ε ^ 2 * (t : ℂ) ^ (-3 * ε) +
    (2 * i13Al0 ε * i13Al1 ε - i8Kap ε * i13Al0 ε ^ 2) * (t : ℂ) ^ (-1 - 3 * ε) +
    2 * i13Al0 ε * i13Be0 ε * (t : ℂ) ^ (-1 - 2 * ε)

/-- The continued integrals `∫₁^∞` of the three terms of `QED.ThreeLoopD.i8Asym`,
`∫₁^∞ t ^ a dt = -1/(a + 1)`. -/
noncomputable def i8Tail (ε : ℂ) : ℂ :=
  i13Al0 ε ^ 2 / (3 * ε - 1) +
    (2 * i13Al0 ε * i13Al1 ε - i8Kap ε * i13Al0 ε ^ 2) / (3 * ε) +
    2 * i13Al0 ε * i13Be0 ε / (2 * ε)

/-- The subtracted radial integral, convergent for `-1/3 < re ε < 3/2`. -/
noncomputable def i8Rem (ε : ℂ) : ℂ :=
  (∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (1 - ε) * i13Bub ε t ^ 2 * i8Ang ε t) +
    ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (1 - ε) * i13Bub ε t ^ 2 * i8Ang ε t - i8Asym ε t)

/-- **The continued radial integral** `T(ε) = ∫₀^∞ t ^ (1 - ε) b_ε(t)² A_ε(t) dt`. -/
noncomputable def i8T (ε : ℂ) : ℂ := i8Tail ε + i8Rem ε

/-- `I₈` in LR96's normalization, `1 / (D₁ D₂ D₃ D₄ D₅)`: `π ^ (3ε) Γ(ε)² / Γ(2 - ε) T(ε)`,
with `T` continued by `QED.ThreeLoopD.i8T`. Each loop carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I8 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 * (Gamma ω ^ 2 / Gamma (2 - ω) * i8T ω)

/-- The master `I₈ C⁻¹`. -/
noncomputable def setDMasterI8 (ε : ℂ) : ℂ := lr96I8 ε / lr96C ε

end QED.ThreeLoopD
