/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValThreeHxArg
public import QED.ThreeLoopD.SetDMastersI15KValThreeA
import QED.ThreeLoopD.SetDMastersI15KValTwoA
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₅`: the `x`-primitive of `A₂₃,₃`

For `u ∈ (0, 1)` this file gives an explicit primitive `Φ` in `x` of the slice
`A₂₃,₃(x, u) = QED.ThreeLoopD.i15HxF u x`: a polynomial in `x`, `log x`, `log (1 - x)`,
`A = log (1 + (1 - u) x / u)` and `B = log (1 - (1 - u) x)` (coefficients in `u`, `1/u`, `log u`,
`log (1 - u)`, `log (1 + u)`) plus multiples of `G(X) = Li₃ X - Li₂ X log X` and `Li₂ X` at the
twenty arguments of `QED.ThreeLoopD.SetDMastersI15KValThreeHxArg` (found by an ansatz in these
functions, `setDI15f/hside.py`). Its derivative is a polynomial identity in the logarithms and the
inverses of `x`, `1 - x`, `u + (1 - u) x`, `1 - (1 - u) x`, `u`.

At `x → 0⁺` the polynomial has no pure powers of `log x` once `log (u + (1 - u) x) = log u + A`;
at `x → 1⁻` it is rewritten in `s = 1 - x` (`QED.ThreeLoopD.i15HxP_reflect`: `A, B` become
`B(s) - log u, A(s) + log u`) and has no pure powers of `log s`. The arguments are continuous on
`[0, 1]`, with values in `{0, 1, u, 1 - u, u², 1 - u², 1/(1 + u), u/(1 + u)}` at the ends.
Given the integrability of the slice, the fundamental theorem of calculus gives
`∫₀¹ A₂₃,₃(x, u) dx = Φ(1⁻) - Φ(0⁺)` (`QED.ThreeLoopD.integral_i15A23k_three_slice`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i15HxPhi`, `QED.ThreeLoopD.tendsto_i15HxPhi_zero`,
  `QED.ThreeLoopD.tendsto_i15HxPhi_one`.
* `QED.ThreeLoopD.integral_i15A23k_three_slice`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

theorem i15Hx_tendsto_TG {l : Filter ℝ} {X : ℝ → ℝ} {c : ℝ} (hX : Tendsto X l (𝓝 c))
    (hc : c ∈ Ioc (0 : ℝ) 1) (hev : ∀ᶠ y in l, X y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun y => i15TG (X y)) l (𝓝 (i15TG c)) :=
  (continuousOn_i15TG c hc).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hX, hev.mono fun _ hy => ⟨hy.1, hy.2.le⟩⟩)

theorem i15Hx_tendsto_TG_zero {l : Filter ℝ} {X : ℝ → ℝ} (hX : Tendsto X l (𝓝 0))
    (hev : ∀ᶠ y in l, X y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun y => i15TG (X y)) l (𝓝 (i15TG 0)) := by
  rw [show i15TG 0 = 0 by simp [i15TG]]
  exact tendsto_i15TG_zero.comp (tendsto_nhdsWithin_iff.2 ⟨hX, hev.mono fun _ hy => hy.1⟩)

theorem i15Hx_tendsto_Li₂ {l : Filter ℝ} {X : ℝ → ℝ} {c : ℝ} (hX : Tendsto X l (𝓝 c))
    (hc : c ∈ Icc (0 : ℝ) 1) (hev : ∀ᶠ y in l, X y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun y => Li₂ (X y)) l (𝓝 (Li₂ c)) :=
  tendsto_Li₂_comp ⟨by linarith [hc.1], hc.2⟩ hX
    (hev.mono fun _ hy => ⟨by linarith [hy.1], hy.2.le⟩)

/-- The polynomial part of the primitive, in `x`, `log x`, `log (1 - x)`, `A`, `B`. -/
noncomputable def i15HxP0 (u : ℝ) : List (ℝ × (ℕ × ℕ × ℕ × ℕ × ℕ)) :=
  [((-1 / 3 : ℝ) + u⁻¹ / 3 + u / 6, (1, 3, 0, 0, 0)),
   (-1 + u⁻¹ + u / 2, (1, 2, 1, 0, 0)),
   (2 - u⁻¹ - u, (1, 2, 0, 1, 0)),
   (2 - u⁻¹ - u, (1, 2, 0, 0, 1)),
   (-2 + log u + u - log u * u⁻¹ - log u * u / 2, (1, 2, 0, 0, 0)),
   (-1 + u⁻¹ + u / 2, (1, 1, 2, 0, 0)),
   (4 - 2 * u⁻¹ - 2 * u, (1, 1, 1, 1, 0)),
   (4 - 2 * u⁻¹ - 2 * u, (1, 1, 1, 0, 1)),
   (-4 + 2 * log u + 2 * u - log u * u - 2 * log u * u⁻¹, (1, 1, 1, 0, 0)),
   (-4 + 2 * u⁻¹ + 2 * u, (1, 1, 0, 2, 0)),
   (-8 + 4 * u⁻¹ + 4 * u, (1, 1, 0, 1, 1)),
   (8 - 4 * log u - 4 * u⁻¹ - 4 * u + 2 * log u * u⁻¹ + 2 * log u * u, (1, 1, 0, 1, 0)),
   (-4 + 2 * u⁻¹ + 2 * u, (1, 1, 0, 0, 2)),
   (8 - 4 * log u - 4 * u⁻¹ - 4 * u + 2 * log u * u⁻¹ + 2 * log u * u, (1, 1, 0, 0, 1)),
   (-8 - log u ^ 2 + 4 * log u + 4 * u + 8 * u⁻¹ + u⁻¹ * log u ^ 2 + u * log u ^ 2 / 2 - 2 * log u
       * u, (1, 1, 0, 0, 0)),
   ((-1 / 3 : ℝ) + u⁻¹ / 3 + u / 6, (1, 0, 3, 0, 0)),
   (2 - u⁻¹ - u, (1, 0, 2, 1, 0)),
   (2 - u⁻¹ - u, (1, 0, 2, 0, 1)),
   (-2 + log u + u - log u * u⁻¹ - log u * u / 2, (1, 0, 2, 0, 0)),
   (-4 + 2 * u⁻¹ + 2 * u, (1, 0, 1, 2, 0)),
   (-8 + 4 * u⁻¹ + 4 * u, (1, 0, 1, 1, 1)),
   (8 - 4 * log u - 4 * u⁻¹ - 4 * u + 2 * log u * u⁻¹ + 2 * log u * u, (1, 0, 1, 1, 0)),
   (-4 + 2 * u⁻¹ + 2 * u, (1, 0, 1, 0, 2)),
   (8 - 4 * log u - 4 * u⁻¹ - 4 * u + 2 * log u * u⁻¹ + 2 * log u * u, (1, 0, 1, 0, 1)),
   (-8 - log u ^ 2 + 4 * log u + 4 * u + 8 * u⁻¹ + u⁻¹ * log u ^ 2 + u * log u ^ 2 / 2 - 2 * log u
       * u, (1, 0, 1, 0, 0)),
   ((8 / 3 : ℝ) - 4 * u⁻¹ / 3 - 4 * u / 3, (1, 0, 0, 3, 0)),
   (8 - 4 * u⁻¹ - 4 * u, (1, 0, 0, 2, 1)),
   (-8 + 4 * log u + 4 * u⁻¹ + 4 * u - 2 * log u * u⁻¹ - 2 * log u * u, (1, 0, 0, 2, 0)),
   (8 - 4 * u⁻¹ - 4 * u, (1, 0, 0, 1, 2)),
   (-16 + 8 * log u + 8 * u⁻¹ + 8 * u - 4 * log u * u⁻¹ - 4 * log u * u, (1, 0, 0, 1, 1)),
   (16 - 8 * log u - 8 * u⁻¹ - 8 * u + 2 * log u ^ 2 - u⁻¹ * log u ^ 2 - u * log u ^ 2 + 4 * log u
       * u⁻¹ + 4 * log u * u, (1, 0, 0, 1, 0)),
   ((8 / 3 : ℝ) - 4 * u⁻¹ / 3 - 4 * u / 3, (1, 0, 0, 0, 3)),
   (-8 + 4 * log u + 4 * u⁻¹ + 4 * u - 2 * log u * u⁻¹ - 2 * log u * u, (1, 0, 0, 0, 2)),
   (16 - 8 * log u - 8 * u⁻¹ - 8 * u + 2 * log u ^ 2 - u⁻¹ * log u ^ 2 - u * log u ^ 2 + 4 * log u
       * u⁻¹ + 4 * log u * u, (1, 0, 0, 0, 1)),
   (-16 - 2 * log u ^ 2 + 8 * log u + 8 * u + log u ^ 3 / 3 + u * log u ^ 2 - 8 * log u * u⁻¹ - 4 *
       log u * u - u⁻¹ * log u ^ 3 / 3 - u * log u ^ 3 / 6, (1, 0, 0, 0, 0)),
   (1 - u⁻¹ - u / 2, (0, 2, 1, 0, 0)),
   (-1 + u, (0, 2, 0, 1, 0)),
   (-1 + u⁻¹, (0, 2, 0, 0, 1)),
   (-2 + 2 * u⁻¹, (0, 1, 1, 1, 0)),
   (-2 + 2 * u, (0, 1, 1, 0, 1)),
   (-2 * log u + 2 * log u * u⁻¹, (0, 1, 1, 0, 0)),
   (2 - 2 * u, (0, 1, 0, 2, 0)),
   (-4 * u⁻¹ + 4 * u, (0, 1, 0, 1, 1)),
   (2 * log u + log (1 - u) * u - log (1 - u) * u⁻¹ - 2 * log u * u - 2 * log (1 + u) * u⁻¹ + 2 *
       log (1 + u) * u, (0, 1, 0, 1, 0)),
   (2 - 2 * u, (0, 1, 0, 0, 2)),
   (-4 * log u * u⁻¹ + 4 * log u * u, (0, 1, 0, 0, 1)),
   ((1 / 3 : ℝ) - u⁻¹ / 3 - u / 6, (0, 0, 3, 0, 0)),
   (-1 + u, (0, 0, 2, 1, 0)),
   (-1 + u⁻¹, (0, 0, 2, 0, 1)),
   (2 - log u - u + 3 * log u * u / 2, (0, 0, 2, 0, 0)),
   (2 - 2 * u⁻¹, (0, 0, 1, 2, 0)),
   (8 - 8 * u, (0, 0, 1, 1, 1)),
   (4 * log u - 4 * log u * u⁻¹, (0, 0, 1, 1, 0)),
   (2 - 2 * u⁻¹, (0, 0, 1, 0, 2)),
   (-8 + 4 * u⁻¹ + 4 * u + 6 * log u + log (1 - u) * u⁻¹ - log (1 - u) * u - 8 * log u * u - 2 *
       log (1 + u) * u + 2 * log u * u⁻¹ + 2 * log (1 + u) * u⁻¹, (0, 0, 1, 0, 1)),
   (8 - 8 * u⁻¹ - 4 * u + 3 * log u ^ 2 + 4 * log u - 4 * log u * u⁻¹ - 3 * u⁻¹ * log u ^ 2 - 2 *
       log u * u - u * log u ^ 2 / 2 + log u * log (1 - u) * u - log u * log (1 - u) * u⁻¹ - 2 *
       log u * log (1 + u) * u⁻¹ + 2 * log u * log (1 + u) * u, (0, 0, 1, 0, 0)),
   ((-4 / 3 : ℝ) + 4 * u / 3, (0, 0, 0, 3, 0)),
   (-4 * u + 4 * u⁻¹, (0, 0, 0, 2, 1)),
   (2 - 2 * log u - 2 * u + 2 * log u * u, (0, 0, 0, 2, 0)),
   (-8 + 8 * u, (0, 0, 0, 1, 2)),
   (-8 * log u * u + 8 * log u * u⁻¹, (0, 0, 0, 1, 1)),
   (-8 - log u ^ 2 + 8 * u + u * log u ^ 2, (0, 0, 0, 1, 0)),
   ((-4 / 3 : ℝ) + 4 * u⁻¹ / 3, (0, 0, 0, 0, 3)),
   (6 - 6 * log u - 4 * u⁻¹ - 2 * u - 2 * log u * u⁻¹ + 8 * log u * u, (0, 0, 0, 0, 2)),
   (-8 - log u ^ 2 - 4 * log u + 8 * u⁻¹ - 4 * u * log u ^ 2 + 4 * log u * u⁻¹ + 5 * u⁻¹ * log u ^
       2, (0, 0, 0, 0, 1)),
   (-8 * log u - 2 * log u ^ 2 - log u ^ 3 / 3 + 2 * u * log u ^ 2 + 8 * log u * u + u * log u ^ 3
       / 3, (0, 0, 0, 0, 0))]

/-- The polynomial part in `s = 1 - x`, `log s`, `log (1 - s)`, `B(s)`, `A(s)`. -/
noncomputable def i15HxP1 (u : ℝ) : List (ℝ × (ℕ × ℕ × ℕ × ℕ × ℕ)) :=
  [((1 / 3 : ℝ) - u⁻¹ / 3 - u / 6, (1, 3, 0, 0, 0)),
   (1 - u⁻¹ - u / 2, (1, 2, 1, 0, 0)),
   (-2 + u⁻¹ + u, (1, 2, 0, 1, 0)),
   (-2 + u⁻¹ + u, (1, 2, 0, 0, 1)),
   (2 - log u - u + log u * u⁻¹ + log u * u / 2, (1, 2, 0, 0, 0)),
   (1 - u⁻¹ - u / 2, (1, 1, 2, 0, 0)),
   (-4 + 2 * u⁻¹ + 2 * u, (1, 1, 1, 1, 0)),
   (-4 + 2 * u⁻¹ + 2 * u, (1, 1, 1, 0, 1)),
   (4 - 2 * log u - 2 * u + log u * u + 2 * log u * u⁻¹, (1, 1, 1, 0, 0)),
   (4 - 2 * u⁻¹ - 2 * u, (1, 1, 0, 2, 0)),
   (8 - 4 * u⁻¹ - 4 * u, (1, 1, 0, 1, 1)),
   (-8 + 4 * log u + 4 * u⁻¹ + 4 * u - 2 * log u * u⁻¹ - 2 * log u * u, (1, 1, 0, 1, 0)),
   (4 - 2 * u⁻¹ - 2 * u, (1, 1, 0, 0, 2)),
   (-8 + 4 * log u + 4 * u⁻¹ + 4 * u - 2 * log u * u⁻¹ - 2 * log u * u, (1, 1, 0, 0, 1)),
   (8 + log u ^ 2 - 8 * u⁻¹ - 4 * log u - 4 * u - u⁻¹ * log u ^ 2 + 2 * log u * u - u * log u ^ 2 /
       2, (1, 1, 0, 0, 0)),
   ((1 / 3 : ℝ) - u⁻¹ / 3 - u / 6, (1, 0, 3, 0, 0)),
   (-2 + u⁻¹ + u, (1, 0, 2, 1, 0)),
   (-2 + u⁻¹ + u, (1, 0, 2, 0, 1)),
   (2 - log u - u + log u * u⁻¹ + log u * u / 2, (1, 0, 2, 0, 0)),
   (4 - 2 * u⁻¹ - 2 * u, (1, 0, 1, 2, 0)),
   (8 - 4 * u⁻¹ - 4 * u, (1, 0, 1, 1, 1)),
   (-8 + 4 * log u + 4 * u⁻¹ + 4 * u - 2 * log u * u⁻¹ - 2 * log u * u, (1, 0, 1, 1, 0)),
   (4 - 2 * u⁻¹ - 2 * u, (1, 0, 1, 0, 2)),
   (-8 + 4 * log u + 4 * u⁻¹ + 4 * u - 2 * log u * u⁻¹ - 2 * log u * u, (1, 0, 1, 0, 1)),
   (8 + log u ^ 2 - 8 * u⁻¹ - 4 * log u - 4 * u - u⁻¹ * log u ^ 2 + 2 * log u * u - u * log u ^ 2 /
       2, (1, 0, 1, 0, 0)),
   ((-8 / 3 : ℝ) + 4 * u⁻¹ / 3 + 4 * u / 3, (1, 0, 0, 3, 0)),
   (-8 + 4 * u⁻¹ + 4 * u, (1, 0, 0, 2, 1)),
   (8 - 4 * log u - 4 * u⁻¹ - 4 * u + 2 * log u * u⁻¹ + 2 * log u * u, (1, 0, 0, 2, 0)),
   (-8 + 4 * u⁻¹ + 4 * u, (1, 0, 0, 1, 2)),
   (16 - 8 * log u - 8 * u⁻¹ - 8 * u + 4 * log u * u⁻¹ + 4 * log u * u, (1, 0, 0, 1, 1)),
   (-16 - 2 * log u ^ 2 + 8 * log u + 8 * u⁻¹ + 8 * u + u⁻¹ * log u ^ 2 + u * log u ^ 2 - 4 * log u
       * u⁻¹ - 4 * log u * u, (1, 0, 0, 1, 0)),
   ((-8 / 3 : ℝ) + 4 * u⁻¹ / 3 + 4 * u / 3, (1, 0, 0, 0, 3)),
   (8 - 4 * log u - 4 * u⁻¹ - 4 * u + 2 * log u * u⁻¹ + 2 * log u * u, (1, 0, 0, 0, 2)),
   (-16 - 2 * log u ^ 2 + 8 * log u + 8 * u⁻¹ + 8 * u + u⁻¹ * log u ^ 2 + u * log u ^ 2 - 4 * log u
       * u⁻¹ - 4 * log u * u, (1, 0, 0, 0, 1)),
   (16 - 8 * log u - 8 * u + 2 * log u ^ 2 - log u ^ 3 / 3 - u * log u ^ 2 + 4 * log u * u + 8 *
       log u * u⁻¹ + u⁻¹ * log u ^ 3 / 3 + u * log u ^ 3 / 6, (1, 0, 0, 0, 0)),
   (-1 + u⁻¹ + u / 2, (0, 2, 1, 0, 0)),
   (1 - u⁻¹, (0, 2, 0, 1, 0)),
   (1 - u, (0, 2, 0, 0, 1)),
   (2 - 2 * u, (0, 1, 1, 1, 0)),
   (2 - 2 * u⁻¹, (0, 1, 1, 0, 1)),
   (-4 + 2 * u + log u * u - 2 * log u * u⁻¹, (0, 1, 1, 0, 0)),
   (-2 + 2 * u, (0, 1, 0, 2, 0)),
   (-4 * u + 4 * u⁻¹, (0, 1, 0, 1, 1)),
   (8 - 4 * u⁻¹ - 4 * u + 4 * log u - 6 * log u * u + 2 * log u * u⁻¹, (0, 1, 0, 1, 0)),
   (-2 + 2 * u, (0, 1, 0, 0, 2)),
   (-2 * log u + log (1 - u) * u⁻¹ - log (1 - u) * u - 2 * log (1 + u) * u + 2 * log u * u + 2 *
       log (1 + u) * u⁻¹, (0, 1, 0, 0, 1)),
   ((-1 / 3 : ℝ) + u⁻¹ / 3 + u / 6, (0, 0, 3, 0, 0)),
   (1 - u⁻¹, (0, 0, 2, 1, 0)),
   (1 - u, (0, 0, 2, 0, 1)),
   (-2 + log u + u - 3 * log u * u / 2, (0, 0, 2, 0, 0)),
   (-2 + 2 * u⁻¹, (0, 0, 1, 2, 0)),
   (-8 + 8 * u, (0, 0, 1, 1, 1)),
   (8 - 6 * log u - 4 * u⁻¹ - 4 * u + log (1 - u) * u - log (1 - u) * u⁻¹ - 2 * log u * u⁻¹ - 2 *
       log (1 + u) * u⁻¹ + 2 * log (1 + u) * u + 8 * log u * u, (0, 0, 1, 1, 0)),
   (-2 + 2 * u⁻¹, (0, 0, 1, 0, 2)),
   (8 - 4 * u⁻¹ - 4 * u - 2 * log u * u + 2 * log u * u⁻¹, (0, 0, 1, 0, 1)),
   (-8 + log u ^ 2 + 4 * log u + 4 * u + 8 * u⁻¹ + u⁻¹ * log u ^ 2 - 2 * log u * u - 3 * u * log u
       ^ 2 / 2 + log u * log (1 - u) * u⁻¹ - log u * log (1 - u) * u - 2 * log u * log (1 + u) * u
       + 2 * log u * log (1 + u) * u⁻¹, (0, 0, 1, 0, 0)),
   ((4 / 3 : ℝ) - 4 * u⁻¹ / 3, (0, 0, 0, 3, 0)),
   (8 - 8 * u, (0, 0, 0, 2, 1)),
   (-6 + 2 * u + 4 * u⁻¹ + 6 * log u - 8 * log u * u + 2 * log u * u⁻¹, (0, 0, 0, 2, 0)),
   (-4 * u⁻¹ + 4 * u, (0, 0, 0, 1, 2)),
   (-16 - 8 * log u + 8 * u⁻¹ + 8 * u - 4 * log u * u⁻¹ + 12 * log u * u, (0, 0, 0, 1, 1)),
   (8 - 12 * log u - 8 * u⁻¹ - 7 * log u ^ 2 - u⁻¹ * log u ^ 2 + 4 * log u * u⁻¹ + 8 * log u * u +
       8 * u * log u ^ 2, (0, 0, 0, 1, 0)),
   ((4 / 3 : ℝ) - 4 * u / 3, (0, 0, 0, 0, 3)),
   (-2 + 2 * log u + 2 * u - 2 * log u * u, (0, 0, 0, 0, 2)),
   (8 + log u ^ 2 - 8 * u - u * log u ^ 2, (0, 0, 0, 0, 1)),
   (-16 + 8 * u - u * log u ^ 2 - 4 * log u * u - u * log u ^ 3 / 6, (0, 0, 0, 0, 0))]

/-- **The primitive `Φ`** of `A₂₃,₃(·, u)`. -/
noncomputable def i15HxPhi (u t : ℝ) : ℝ :=
  i15TPoly (i15HxP0 u) t (log t) (log (1 - t)) (i15HxA u t) (i15HxB u t) +
    (2 - 2 * u) * i15TG (i15HxX0 u t) +
    (-2 + 2 * u⁻¹) * i15TG (i15HxX1 u t) +
    (2 - 2 * u⁻¹) * i15TG (i15HxX2 u t) +
    (-2 + 2 * u) * i15TG (i15HxX3 u t) +
    (-2 + u) * i15TG (i15HxX4 u t) +
    (2 - u) * i15TG (i15HxX5 u t) +
    (-4 + 4 * u) * i15TG (i15HxX6 u t) +
    (-4 * u⁻¹ + 4 * u) * i15TG (i15HxX7 u t) +
    (4 - 4 * u) * i15TG (i15HxX8 u t) +
    (-2 * u + 2 * u⁻¹) * i15TG (i15HxX9 u t) +
    (4 - 2 * u⁻¹ - 2 * u) * i15TG (i15HxX10 u t) +
    (-2 * u + 2 * u⁻¹) * i15TG (i15HxX11 u t) +
    (4 - 4 * u) * i15TG (i15HxX12 u t) +
    (-4 * u + 4 * u⁻¹) * i15TG (i15HxX13 u t) +
    (-4 + 2 * u⁻¹ + 2 * u) * i15TG (i15HxX14 u t) +
    (-2 * u⁻¹ + 2 * u) * i15TG (i15HxX15 u t) +
    (-4 + 4 * u) * i15TG (i15HxX16 u t) +
    (-2 * u⁻¹ + 2 * u) * i15TG (i15HxX17 u t) +
    (-4 * u + 4 * u⁻¹) * i15TG (i15HxX18 u t) +
    (-4 * u⁻¹ + 4 * u) * i15TG (i15HxX19 u t) +
    (-8 - 2 * log u + 4 * u⁻¹ + 4 * u - 4 * log (1 + u) * u⁻¹ - 2 * log (1 - u) * u⁻¹ + 2 * log u *
        u⁻¹ + 2 * log (1 - u) * u + 4 * log (1 + u) * u) * Li₂ (i15HxX0 u t) +
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 8 * log (1 + u) * u - 3 * log (1 - u) * u + 3 *
        log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹) * Li₂ (i15HxX1 u t) +
    (log (1 - u) * u⁻¹ - log (1 - u) * u - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹) * Li₂
        (i15HxX2 u t) +
    (-4 * u - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log u * u - 6 * log (1 + u) * u⁻¹ - 2 * log (1 -
        u) * u⁻¹ + 2 * log (1 - u) * u + 6 * log (1 + u) * u) * Li₂ (i15HxX3 u t) +
    (4 - 4 * u⁻¹ - 2 * u + 2 * log u + log (1 - u) * u⁻¹ - log u * u - log (1 - u) * u - 2 * log u
        * u⁻¹ - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹) * Li₂ (i15HxX4 u t) +
    (log (1 - u) * u - log (1 - u) * u⁻¹ - 2 * log (1 + u) * u⁻¹ + 2 * log (1 + u) * u) * Li₂
        (i15HxX5 u t) +
    (8 - 8 * u⁻¹ - 8 * log (1 + u) * u - 4 * log u * u⁻¹ - 4 * log (1 - u) * u + 4 * log u * u + 4
        * log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹) * Li₂ (i15HxX6 u t) +
    (-8 * u + 8 * u⁻¹ - 12 * log (1 + u) * u⁻¹ - 6 * log (1 - u) * u⁻¹ - 2 * log u * u + 2 * log u
        * u⁻¹ + 6 * log (1 - u) * u + 12 * log (1 + u) * u) * Li₂ (i15HxX7 u t) +
    (-4 + 2 * log u + 4 * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ - 4 * log u * u - 2 * log (1 +
        u) * u⁻¹ + 2 * log u * u⁻¹ + 2 * log (1 + u) * u) * Li₂ (i15HxX8 u t) +
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
        log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹) * Li₂ (i15HxX9 u t) +
    (-4 - 2 * log u + 4 * u⁻¹ - 6 * log (1 + u) * u⁻¹ - 3 * log (1 - u) * u⁻¹ + 2 * log u * u⁻¹ + 3
        * log (1 - u) * u + 6 * log (1 + u) * u) * Li₂ (i15HxX10 u t) +
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
        log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹) * Li₂ (i15HxX11 u t) +
    (8 - 8 * u⁻¹ + 8 * log u - 6 * log u * u - 4 * log (1 + u) * u - 2 * log u * u⁻¹ - 2 * log (1 -
        u) * u + 2 * log (1 - u) * u⁻¹ + 4 * log (1 + u) * u⁻¹) * Li₂ (i15HxX12 u t) +
    (-4 - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log u * u + log (1 - u) * u⁻¹ - log (1 - u) * u - 4 *
        log (1 + u) * u + 4 * log (1 + u) * u⁻¹) * Li₂ (i15HxX14 u t) +
    (-4 - 6 * log u + 4 * u⁻¹ + log u * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ + 5 * log u * u)
        * Li₂ (i15HxX16 u t)

/-- The value of the primitive at `0⁺`. -/
noncomputable def i15HxPhi0 (u : ℝ) : ℝ :=
  i15TPoly (i15HxP0 u) 0 1 0 0 0 +
    (2 - 2 * u) * i15TG (1) +
    (-2 + 2 * u⁻¹) * i15TG (0) +
    (2 - 2 * u⁻¹) * i15TG (1) +
    (-2 + 2 * u) * i15TG (0) +
    (-2 + u) * i15TG (1) +
    (2 - u) * i15TG (0) +
    (-4 + 4 * u) * i15TG (1) +
    (-4 * u⁻¹ + 4 * u) * i15TG (0) +
    (4 - 4 * u) * i15TG (1) +
    (-2 * u + 2 * u⁻¹) * i15TG (0) +
    (4 - 2 * u⁻¹ - 2 * u) * i15TG (1) +
    (-2 * u + 2 * u⁻¹) * i15TG (0) +
    (4 - 4 * u) * i15TG (u ^ 2) +
    (-4 * u + 4 * u⁻¹) * i15TG ((1 - u) * (1 + u)) +
    (-4 + 2 * u⁻¹ + 2 * u) * i15TG (u) +
    (-2 * u⁻¹ + 2 * u) * i15TG (1 - u) +
    (-4 + 4 * u) * i15TG (u) +
    (-2 * u⁻¹ + 2 * u) * i15TG (1 - u) +
    (-4 * u + 4 * u⁻¹) * i15TG (1 / (1 + u)) +
    (-4 * u⁻¹ + 4 * u) * i15TG (u / (1 + u)) +
    (-8 - 2 * log u + 4 * u⁻¹ + 4 * u - 4 * log (1 + u) * u⁻¹ - 2 * log (1 - u) * u⁻¹ + 2 * log u *
        u⁻¹ + 2 * log (1 - u) * u + 4 * log (1 + u) * u) * Li₂ (1) +
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 8 * log (1 + u) * u - 3 * log (1 - u) * u + 3 *
        log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹) * Li₂ (0) +
    (log (1 - u) * u⁻¹ - log (1 - u) * u - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹) * Li₂ (1) +
    (-4 * u - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log u * u - 6 * log (1 + u) * u⁻¹ - 2 * log (1 -
        u) * u⁻¹ + 2 * log (1 - u) * u + 6 * log (1 + u) * u) * Li₂ (0) +
    (4 - 4 * u⁻¹ - 2 * u + 2 * log u + log (1 - u) * u⁻¹ - log u * u - log (1 - u) * u - 2 * log u
        * u⁻¹ - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹) * Li₂ (1) +
    (log (1 - u) * u - log (1 - u) * u⁻¹ - 2 * log (1 + u) * u⁻¹ + 2 * log (1 + u) * u) * Li₂ (0) +
    (8 - 8 * u⁻¹ - 8 * log (1 + u) * u - 4 * log u * u⁻¹ - 4 * log (1 - u) * u + 4 * log u * u + 4
        * log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹) * Li₂ (1) +
    (-8 * u + 8 * u⁻¹ - 12 * log (1 + u) * u⁻¹ - 6 * log (1 - u) * u⁻¹ - 2 * log u * u + 2 * log u
        * u⁻¹ + 6 * log (1 - u) * u + 12 * log (1 + u) * u) * Li₂ (0) +
    (-4 + 2 * log u + 4 * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ - 4 * log u * u - 2 * log (1 +
        u) * u⁻¹ + 2 * log u * u⁻¹ + 2 * log (1 + u) * u) * Li₂ (1) +
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
        log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹) * Li₂ (0) +
    (-4 - 2 * log u + 4 * u⁻¹ - 6 * log (1 + u) * u⁻¹ - 3 * log (1 - u) * u⁻¹ + 2 * log u * u⁻¹ + 3
        * log (1 - u) * u + 6 * log (1 + u) * u) * Li₂ (1) +
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
        log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹) * Li₂ (0) +
    (8 - 8 * u⁻¹ + 8 * log u - 6 * log u * u - 4 * log (1 + u) * u - 2 * log u * u⁻¹ - 2 * log (1 -
        u) * u + 2 * log (1 - u) * u⁻¹ + 4 * log (1 + u) * u⁻¹) * Li₂ (u ^ 2) +
    (-4 - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log u * u + log (1 - u) * u⁻¹ - log (1 - u) * u - 4 *
        log (1 + u) * u + 4 * log (1 + u) * u⁻¹) * Li₂ (u) +
    (-4 - 6 * log u + 4 * u⁻¹ + log u * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ + 5 * log u * u)
        * Li₂ (u)

/-- The value of the primitive at `1⁻`. -/
noncomputable def i15HxPhi1 (u : ℝ) : ℝ :=
  i15TPoly (i15HxP1 u) 0 1 0 0 0 +
    (2 - 2 * u) * i15TG (0) +
    (-2 + 2 * u⁻¹) * i15TG (1) +
    (2 - 2 * u⁻¹) * i15TG (0) +
    (-2 + 2 * u) * i15TG (1) +
    (-2 + u) * i15TG (0) +
    (2 - u) * i15TG (1) +
    (-4 + 4 * u) * i15TG (u ^ 2) +
    (-4 * u⁻¹ + 4 * u) * i15TG ((1 - u) * (1 + u)) +
    (4 - 4 * u) * i15TG (u) +
    (-2 * u + 2 * u⁻¹) * i15TG (1 - u) +
    (4 - 2 * u⁻¹ - 2 * u) * i15TG (u) +
    (-2 * u + 2 * u⁻¹) * i15TG (1 - u) +
    (4 - 4 * u) * i15TG (1) +
    (-4 * u + 4 * u⁻¹) * i15TG (0) +
    (-4 + 2 * u⁻¹ + 2 * u) * i15TG (1) +
    (-2 * u⁻¹ + 2 * u) * i15TG (0) +
    (-4 + 4 * u) * i15TG (1) +
    (-2 * u⁻¹ + 2 * u) * i15TG (0) +
    (-4 * u + 4 * u⁻¹) * i15TG (u / (1 + u)) +
    (-4 * u⁻¹ + 4 * u) * i15TG (1 / (1 + u)) +
    (-8 - 2 * log u + 4 * u⁻¹ + 4 * u - 4 * log (1 + u) * u⁻¹ - 2 * log (1 - u) * u⁻¹ + 2 * log u *
        u⁻¹ + 2 * log (1 - u) * u + 4 * log (1 + u) * u) * Li₂ (0) +
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 8 * log (1 + u) * u - 3 * log (1 - u) * u + 3 *
        log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹) * Li₂ (1) +
    (log (1 - u) * u⁻¹ - log (1 - u) * u - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹) * Li₂ (0) +
    (-4 * u - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log u * u - 6 * log (1 + u) * u⁻¹ - 2 * log (1 -
        u) * u⁻¹ + 2 * log (1 - u) * u + 6 * log (1 + u) * u) * Li₂ (1) +
    (4 - 4 * u⁻¹ - 2 * u + 2 * log u + log (1 - u) * u⁻¹ - log u * u - log (1 - u) * u - 2 * log u
        * u⁻¹ - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹) * Li₂ (0) +
    (log (1 - u) * u - log (1 - u) * u⁻¹ - 2 * log (1 + u) * u⁻¹ + 2 * log (1 + u) * u) * Li₂ (1) +
    (8 - 8 * u⁻¹ - 8 * log (1 + u) * u - 4 * log u * u⁻¹ - 4 * log (1 - u) * u + 4 * log u * u + 4
        * log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹) * Li₂ (u ^ 2) +
    (-8 * u + 8 * u⁻¹ - 12 * log (1 + u) * u⁻¹ - 6 * log (1 - u) * u⁻¹ - 2 * log u * u + 2 * log u
        * u⁻¹ + 6 * log (1 - u) * u + 12 * log (1 + u) * u) * Li₂ ((1 - u) * (1 + u)) +
    (-4 + 2 * log u + 4 * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ - 4 * log u * u - 2 * log (1 +
        u) * u⁻¹ + 2 * log u * u⁻¹ + 2 * log (1 + u) * u) * Li₂ (u) +
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
        log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹) * Li₂ (1 - u) +
    (-4 - 2 * log u + 4 * u⁻¹ - 6 * log (1 + u) * u⁻¹ - 3 * log (1 - u) * u⁻¹ + 2 * log u * u⁻¹ + 3
        * log (1 - u) * u + 6 * log (1 + u) * u) * Li₂ (u) +
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
        log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹) * Li₂ (1 - u) +
    (8 - 8 * u⁻¹ + 8 * log u - 6 * log u * u - 4 * log (1 + u) * u - 2 * log u * u⁻¹ - 2 * log (1 -
        u) * u + 2 * log (1 - u) * u⁻¹ + 4 * log (1 + u) * u⁻¹) * Li₂ (1) +
    (-4 - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log u * u + log (1 - u) * u⁻¹ - log (1 - u) * u - 4 *
        log (1 + u) * u + 4 * log (1 + u) * u⁻¹) * Li₂ (1) +
    (-4 - 6 * log u + 4 * u⁻¹ + log u * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ + 5 * log u * u)
        * Li₂ (1)

theorem hasDerivAt_i15HxPhi {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i15HxPhi u) (i15HxF u t) t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  have hLx : HasDerivAt (fun t => log t) t⁻¹ t := hasDerivAt_log h3.ne'
  have hLy : HasDerivAt (fun t => log (1 - t)) (-(1 - t)⁻¹) t := by
    refine (((hasDerivAt_id' t).const_sub 1).log h4.ne').congr_deriv ?_
    ring
  have hLa : HasDerivAt (fun t => i15HxA u t) ((1 - u) * (u + (1 - u) * t)⁻¹) t := by
    refine ((((hasDerivAt_id' t).const_mul (1 - u)).div_const u).const_add 1).log
      h7.ne' |>.congr_deriv ?_
    field_simp
  have hLb : HasDerivAt (fun t => i15HxB u t) (-((1 - u) * (1 - (1 - u) * t)⁻¹)) t := by
    refine (((hasDerivAt_id' t).const_mul (1 - u)).const_sub 1).log h6.ne' |>.congr_deriv ?_
    ring
  have hP := hasDerivAt_i15TPoly (i15HxP0 u) hLx hLy hLa hLb
  have hX0 := i15T_hasDerivAt_of_log (X := i15HxX0 u) (ℓ := fun t => log (1 - t) + -i15HxA u t)
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX0_pos hu ht, i15HxX0_log hu ht⟩) (hLy.add hLa.neg)
  have hS0 : log (1 - i15HxX0 u t) = log t + -i15HxA u t + (-log u) := by
    rw [i15HxX0_one_sub hu ht]; exact i15HxX1_log hu ht
  have hG0 := (hasDerivAt_i15TG_comp hX0 (i15HxX0_mem hu ht) (i15HxX0_log hu ht)
    hS0).const_mul (2 - 2 * u)
  have hL0 := (hasDerivAt_i15TLi₂_comp hX0 (i15HxX0_mem hu ht) hS0).const_mul
    (-8 - 2 * log u + 4 * u⁻¹ + 4 * u - 4 * log (1 + u) * u⁻¹ - 2 * log (1 - u) * u⁻¹ + 2 * log u *
        u⁻¹ + 2 * log (1 - u) * u + 4 * log (1 + u) * u)
  have hX1 := i15T_hasDerivAt_of_log (X := i15HxX1 u) (ℓ := fun t => log t + -i15HxA u t + (-log u))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX1_pos hu ht, i15HxX1_log hu ht⟩) ((hLx.add
        hLa.neg).add_const (-log u))
  have hS1 : log (1 - i15HxX1 u t) = log (1 - t) + -i15HxA u t := by
    rw [i15HxX1_one_sub hu ht]; exact i15HxX0_log hu ht
  have hG1 := (hasDerivAt_i15TG_comp hX1 (i15HxX1_mem hu ht) (i15HxX1_log hu ht)
    hS1).const_mul (-2 + 2 * u⁻¹)
  have hL1 := (hasDerivAt_i15TLi₂_comp hX1 (i15HxX1_mem hu ht) hS1).const_mul
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 8 * log (1 + u) * u - 3 * log (1 - u) * u + 3 *
        log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹)
  have hX2 := i15T_hasDerivAt_of_log (X := i15HxX2 u) (ℓ := fun t => log (1 - t) + -i15HxB u t)
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX2_pos hu ht, i15HxX2_log hu ht⟩) (hLy.add hLb.neg)
  have hS2 : log (1 - i15HxX2 u t) = log t + -i15HxB u t + (log u) := by
    rw [i15HxX2_one_sub hu ht]; exact i15HxX3_log hu ht
  have hG2 := (hasDerivAt_i15TG_comp hX2 (i15HxX2_mem hu ht) (i15HxX2_log hu ht)
    hS2).const_mul (2 - 2 * u⁻¹)
  have hL2 := (hasDerivAt_i15TLi₂_comp hX2 (i15HxX2_mem hu ht) hS2).const_mul
    (log (1 - u) * u⁻¹ - log (1 - u) * u - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹)
  have hX3 := i15T_hasDerivAt_of_log (X := i15HxX3 u) (ℓ := fun t => log t + -i15HxB u t + (log u))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX3_pos hu ht, i15HxX3_log hu ht⟩) ((hLx.add
        hLb.neg).add_const (log u))
  have hS3 : log (1 - i15HxX3 u t) = log (1 - t) + -i15HxB u t := by
    rw [i15HxX3_one_sub hu ht]; exact i15HxX2_log hu ht
  have hG3 := (hasDerivAt_i15TG_comp hX3 (i15HxX3_mem hu ht) (i15HxX3_log hu ht)
    hS3).const_mul (-2 + 2 * u)
  have hL3 := (hasDerivAt_i15TLi₂_comp hX3 (i15HxX3_mem hu ht) hS3).const_mul
    (-4 * u - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log u * u - 6 * log (1 + u) * u⁻¹ - 2 * log (1 -
        u) * u⁻¹ + 2 * log (1 - u) * u + 6 * log (1 + u) * u)
  have hX4 := i15T_hasDerivAt_of_log (X := i15HxX4 u) (ℓ := fun t => log (1 - t))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX4_pos hu ht, i15HxX4_log hu ht⟩) hLy
  have hS4 : log (1 - i15HxX4 u t) = log t := by
    rw [i15HxX4_one_sub hu ht]; exact i15HxX5_log hu ht
  have hG4 := (hasDerivAt_i15TG_comp hX4 (i15HxX4_mem hu ht) (i15HxX4_log hu ht)
    hS4).const_mul (-2 + u)
  have hL4 := (hasDerivAt_i15TLi₂_comp hX4 (i15HxX4_mem hu ht) hS4).const_mul
    (4 - 4 * u⁻¹ - 2 * u + 2 * log u + log (1 - u) * u⁻¹ - log u * u - log (1 - u) * u - 2 * log u
        * u⁻¹ - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹)
  have hX5 := i15T_hasDerivAt_of_log (X := i15HxX5 u) (ℓ := fun t => log t)
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX5_pos hu ht, i15HxX5_log hu ht⟩) hLx
  have hS5 : log (1 - i15HxX5 u t) = log (1 - t) := by
    rw [i15HxX5_one_sub hu ht]; exact i15HxX4_log hu ht
  have hG5 := (hasDerivAt_i15TG_comp hX5 (i15HxX5_mem hu ht) (i15HxX5_log hu ht)
    hS5).const_mul (2 - u)
  have hL5 := (hasDerivAt_i15TLi₂_comp hX5 (i15HxX5_mem hu ht) hS5).const_mul
    (log (1 - u) * u - log (1 - u) * u⁻¹ - 2 * log (1 + u) * u⁻¹ + 2 * log (1 + u) * u)
  have hX6 := i15T_hasDerivAt_of_log (X := i15HxX6 u) (ℓ := fun t => -i15HxA u t + i15HxB u t)
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX6_pos hu ht, i15HxX6_log hu ht⟩) (hLa.neg.add hLb)
  have hS6 : log (1 - i15HxX6 u t) = log t + -i15HxA u t + (-log u + log (1 - u) + log (1 + u)) :=
      by
    rw [i15HxX6_one_sub hu ht]; exact i15HxX7_log hu ht
  have hG6 := (hasDerivAt_i15TG_comp hX6 (i15HxX6_mem hu ht) (i15HxX6_log hu ht)
    hS6).const_mul (-4 + 4 * u)
  have hL6 := (hasDerivAt_i15TLi₂_comp hX6 (i15HxX6_mem hu ht) hS6).const_mul
    (8 - 8 * u⁻¹ - 8 * log (1 + u) * u - 4 * log u * u⁻¹ - 4 * log (1 - u) * u + 4 * log u * u + 4
        * log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹)
  have hX7 := i15T_hasDerivAt_of_log (X := i15HxX7 u) (ℓ := fun t => log t + -i15HxA u t + (-log u
      + log (1 - u) + log (1 + u)))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX7_pos hu ht, i15HxX7_log hu ht⟩) ((hLx.add
        hLa.neg).add_const (-log u + log (1 - u) + log (1 + u)))
  have hS7 : log (1 - i15HxX7 u t) = -i15HxA u t + i15HxB u t := by
    rw [i15HxX7_one_sub hu ht]; exact i15HxX6_log hu ht
  have hG7 := (hasDerivAt_i15TG_comp hX7 (i15HxX7_mem hu ht) (i15HxX7_log hu ht)
    hS7).const_mul (-4 * u⁻¹ + 4 * u)
  have hL7 := (hasDerivAt_i15TLi₂_comp hX7 (i15HxX7_mem hu ht) hS7).const_mul
    (-8 * u + 8 * u⁻¹ - 12 * log (1 + u) * u⁻¹ - 6 * log (1 - u) * u⁻¹ - 2 * log u * u + 2 * log u
        * u⁻¹ + 6 * log (1 - u) * u + 12 * log (1 + u) * u)
  have hX8 := i15T_hasDerivAt_of_log (X := i15HxX8 u) (ℓ := fun t => -i15HxA u t)
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX8_pos hu ht, i15HxX8_log hu ht⟩) hLa.neg
  have hS8 : log (1 - i15HxX8 u t) = log t + -i15HxA u t + (-log u + log (1 - u)) := by
    rw [i15HxX8_one_sub hu ht]; exact i15HxX9_log hu ht
  have hG8 := (hasDerivAt_i15TG_comp hX8 (i15HxX8_mem hu ht) (i15HxX8_log hu ht)
    hS8).const_mul (4 - 4 * u)
  have hL8 := (hasDerivAt_i15TLi₂_comp hX8 (i15HxX8_mem hu ht) hS8).const_mul
    (-4 + 2 * log u + 4 * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ - 4 * log u * u - 2 * log (1 +
        u) * u⁻¹ + 2 * log u * u⁻¹ + 2 * log (1 + u) * u)
  have hX9 := i15T_hasDerivAt_of_log (X := i15HxX9 u) (ℓ := fun t => log t + -i15HxA u t + (-log u
      + log (1 - u)))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX9_pos hu ht, i15HxX9_log hu ht⟩) ((hLx.add
        hLa.neg).add_const (-log u + log (1 - u)))
  have hS9 : log (1 - i15HxX9 u t) = -i15HxA u t := by
    rw [i15HxX9_one_sub hu ht]; exact i15HxX8_log hu ht
  have hG9 := (hasDerivAt_i15TG_comp hX9 (i15HxX9_mem hu ht) (i15HxX9_log hu ht)
    hS9).const_mul (-2 * u + 2 * u⁻¹)
  have hL9 := (hasDerivAt_i15TLi₂_comp hX9 (i15HxX9_mem hu ht) hS9).const_mul
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
        log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹)
  have hX10 := i15T_hasDerivAt_of_log (X := i15HxX10 u) (ℓ := fun t => i15HxB u t)
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX10_pos hu ht, i15HxX10_log hu ht⟩) hLb
  have hS10 : log (1 - i15HxX10 u t) = log t + (log (1 - u)) := by
    rw [i15HxX10_one_sub hu ht]; exact i15HxX11_log hu ht
  have hG10 := (hasDerivAt_i15TG_comp hX10 (i15HxX10_mem hu ht) (i15HxX10_log hu ht)
    hS10).const_mul (4 - 2 * u⁻¹ - 2 * u)
  have hL10 := (hasDerivAt_i15TLi₂_comp hX10 (i15HxX10_mem hu ht) hS10).const_mul
    (-4 - 2 * log u + 4 * u⁻¹ - 6 * log (1 + u) * u⁻¹ - 3 * log (1 - u) * u⁻¹ + 2 * log u * u⁻¹ + 3
        * log (1 - u) * u + 6 * log (1 + u) * u)
  have hX11 := i15T_hasDerivAt_of_log (X := i15HxX11 u) (ℓ := fun t => log t + (log (1 - u)))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX11_pos hu ht, i15HxX11_log hu ht⟩) (hLx.add_const
        (log (1 - u)))
  have hS11 : log (1 - i15HxX11 u t) = i15HxB u t := by
    rw [i15HxX11_one_sub hu ht]; exact i15HxX10_log hu ht
  have hG11 := (hasDerivAt_i15TG_comp hX11 (i15HxX11_mem hu ht) (i15HxX11_log hu ht)
    hS11).const_mul (-2 * u + 2 * u⁻¹)
  have hL11 := (hasDerivAt_i15TLi₂_comp hX11 (i15HxX11_mem hu ht) hS11).const_mul
    (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
        log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹)
  have hX12 := i15T_hasDerivAt_of_log (X := i15HxX12 u) (ℓ := fun t => i15HxA u t + -i15HxB u t +
      (log u + log u))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX12_pos hu ht, i15HxX12_log hu ht⟩) ((hLa.add
        hLb.neg).add_const (log u + log u))
  have hS12 : log (1 - i15HxX12 u t) = log (1 - t) + -i15HxB u t + (log (1 - u) + log (1 + u)) := by
    rw [i15HxX12_one_sub hu ht]; exact i15HxX13_log hu ht
  have hG12 := (hasDerivAt_i15TG_comp hX12 (i15HxX12_mem hu ht) (i15HxX12_log hu ht)
    hS12).const_mul (4 - 4 * u)
  have hL12 := (hasDerivAt_i15TLi₂_comp hX12 (i15HxX12_mem hu ht) hS12).const_mul
    (8 - 8 * u⁻¹ + 8 * log u - 6 * log u * u - 4 * log (1 + u) * u - 2 * log u * u⁻¹ - 2 * log (1 -
        u) * u + 2 * log (1 - u) * u⁻¹ + 4 * log (1 + u) * u⁻¹)
  have hX13 := i15T_hasDerivAt_of_log (X := i15HxX13 u) (ℓ := fun t => log (1 - t) + -i15HxB u t +
      (log (1 - u) + log (1 + u)))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX13_pos hu ht, i15HxX13_log hu ht⟩) ((hLy.add
        hLb.neg).add_const (log (1 - u) + log (1 + u)))
  have hS13 : log (1 - i15HxX13 u t) = i15HxA u t + -i15HxB u t + (log u + log u) := by
    rw [i15HxX13_one_sub hu ht]; exact i15HxX12_log hu ht
  have hG13 := (hasDerivAt_i15TG_comp hX13 (i15HxX13_mem hu ht) (i15HxX13_log hu ht)
    hS13).const_mul (-4 * u + 4 * u⁻¹)
  have hX14 := i15T_hasDerivAt_of_log (X := i15HxX14 u) (ℓ := fun t => i15HxA u t + (log u))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX14_pos hu ht, i15HxX14_log hu ht⟩) (hLa.add_const
        (log u))
  have hS14 : log (1 - i15HxX14 u t) = log (1 - t) + (log (1 - u)) := by
    rw [i15HxX14_one_sub hu ht]; exact i15HxX15_log hu ht
  have hG14 := (hasDerivAt_i15TG_comp hX14 (i15HxX14_mem hu ht) (i15HxX14_log hu ht)
    hS14).const_mul (-4 + 2 * u⁻¹ + 2 * u)
  have hL14 := (hasDerivAt_i15TLi₂_comp hX14 (i15HxX14_mem hu ht) hS14).const_mul
    (-4 - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log u * u + log (1 - u) * u⁻¹ - log (1 - u) * u - 4 *
        log (1 + u) * u + 4 * log (1 + u) * u⁻¹)
  have hX15 := i15T_hasDerivAt_of_log (X := i15HxX15 u) (ℓ := fun t => log (1 - t) + (log (1 - u)))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX15_pos hu ht, i15HxX15_log hu ht⟩) (hLy.add_const
        (log (1 - u)))
  have hS15 : log (1 - i15HxX15 u t) = i15HxA u t + (log u) := by
    rw [i15HxX15_one_sub hu ht]; exact i15HxX14_log hu ht
  have hG15 := (hasDerivAt_i15TG_comp hX15 (i15HxX15_mem hu ht) (i15HxX15_log hu ht)
    hS15).const_mul (-2 * u⁻¹ + 2 * u)
  have hX16 := i15T_hasDerivAt_of_log (X := i15HxX16 u) (ℓ := fun t => -i15HxB u t + (log u))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX16_pos hu ht, i15HxX16_log hu ht⟩)
        (hLb.neg.add_const (log u))
  have hS16 : log (1 - i15HxX16 u t) = log (1 - t) + -i15HxB u t + (log (1 - u)) := by
    rw [i15HxX16_one_sub hu ht]; exact i15HxX17_log hu ht
  have hG16 := (hasDerivAt_i15TG_comp hX16 (i15HxX16_mem hu ht) (i15HxX16_log hu ht)
    hS16).const_mul (-4 + 4 * u)
  have hL16 := (hasDerivAt_i15TLi₂_comp hX16 (i15HxX16_mem hu ht) hS16).const_mul
    (-4 - 6 * log u + 4 * u⁻¹ + log u * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ + 5 * log u * u)
  have hX17 := i15T_hasDerivAt_of_log (X := i15HxX17 u) (ℓ := fun t => log (1 - t) + -i15HxB u t +
      (log (1 - u)))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX17_pos hu ht, i15HxX17_log hu ht⟩) ((hLy.add
        hLb.neg).add_const (log (1 - u)))
  have hS17 : log (1 - i15HxX17 u t) = -i15HxB u t + (log u) := by
    rw [i15HxX17_one_sub hu ht]; exact i15HxX16_log hu ht
  have hG17 := (hasDerivAt_i15TG_comp hX17 (i15HxX17_mem hu ht) (i15HxX17_log hu ht)
    hS17).const_mul (-2 * u⁻¹ + 2 * u)
  have hX18 := i15T_hasDerivAt_of_log (X := i15HxX18 u) (ℓ := fun t => i15HxB u t + (-log (1 + u)))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX18_pos hu ht, i15HxX18_log hu ht⟩) (hLb.add_const
        (-log (1 + u)))
  have hS18 : log (1 - i15HxX18 u t) = i15HxA u t + (log u + -log (1 + u)) := by
    rw [i15HxX18_one_sub hu ht]; exact i15HxX19_log hu ht
  have hG18 := (hasDerivAt_i15TG_comp hX18 (i15HxX18_mem hu ht) (i15HxX18_log hu ht)
    hS18).const_mul (-4 * u + 4 * u⁻¹)
  have hX19 := i15T_hasDerivAt_of_log (X := i15HxX19 u) (ℓ := fun t => i15HxA u t + (log u + -log
      (1 + u)))
    (Ioo_mem_nhds ht.1 ht.2) (fun t ht => ⟨i15HxX19_pos hu ht, i15HxX19_log hu ht⟩) (hLa.add_const
        (log u + -log (1 + u)))
  have hS19 : log (1 - i15HxX19 u t) = i15HxB u t + (-log (1 + u)) := by
    rw [i15HxX19_one_sub hu ht]; exact i15HxX18_log hu ht
  have hG19 := (hasDerivAt_i15TG_comp hX19 (i15HxX19_mem hu ht) (i15HxX19_log hu ht)
    hS19).const_mul (-4 * u⁻¹ + 4 * u)
  have h := (((((((((((((((((((((((((((((((((((hP.add hG0).add hG1).add hG2).add hG3).add hG4).add
      hG5).add hG6).add hG7).add hG8).add hG9).add hG10).add hG11).add hG12).add hG13).add
      hG14).add hG15).add hG16).add hG17).add hG18).add hG19).add hL0).add hL1).add hL2).add
      hL3).add hL4).add hL5).add hL6).add hL7).add hL8).add hL9).add hL10).add hL11).add hL12).add
      hL14).add hL16)
  refine HasDerivAt.congr_deriv (f := i15HxPhi u) h ?_
  have ex : t * t⁻¹ = 1 := mul_inv_cancel₀ h3.ne'
  have ey : (1 - t) * (1 - t)⁻¹ = 1 := mul_inv_cancel₀ h4.ne'
  have ea : (u + (1 - u) * t) * (u + (1 - u) * t)⁻¹ = 1 := mul_inv_cancel₀ h5.ne'
  have eb : (1 - (1 - u) * t) * (1 - (1 - u) * t)⁻¹ = 1 := mul_inv_cancel₀ h6.ne'
  have eu : u * u⁻¹ = 1 := mul_inv_cancel₀ h0.ne'
  simp only [i15HxP0, i15TPolyD, i15TMonoD, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.reduceSub, i15HxF]
  linear_combination (-8 - log t ^ 2 - log (1 - t) ^ 2 - log u ^ 2 - 4 * log t - 4 * log (1 - t) -
      4 * i15HxA u t ^ 2 - 4 * i15HxB u t ^ 2 + 4 * log u + 4 * u + 8 * i15HxA u t + 8 * i15HxB u t
      + 8 * u⁻¹ + u⁻¹ * log t ^ 2 + u⁻¹ * log (1 - t) ^ 2 + u⁻¹ * log u ^ 2 + u * log t ^ 2 / 2 + u
      * log (1 - t) ^ 2 / 2 + u * log u ^ 2 / 2 - 8 * i15HxA u t * i15HxB u t - 4 * i15HxA u t *
      log u - 4 * i15HxA u t * u⁻¹ - 4 * i15HxA u t * u - 4 * i15HxB u t * log u - 4 * i15HxB u t *
      u⁻¹ - 4 * i15HxB u t * u - 2 * log t * log (1 - t) - 2 * log u * u + 2 * log t * log u + 2 *
      log t * u + 2 * log (1 - t) * log u + 2 * log (1 - t) * u + 2 * u⁻¹ * i15HxA u t ^ 2 + 2 *
      u⁻¹ * i15HxB u t ^ 2 + 2 * u * i15HxA u t ^ 2 + 2 * u * i15HxB u t ^ 2 + 4 * i15HxA u t * log
      t + 4 * i15HxA u t * log (1 - t) + 4 * i15HxB u t * log t + 4 * i15HxB u t * log (1 - t) +
      log t * log (1 - t) * u - log t * log u * u - log (1 - t) * log u * u - 2 * i15HxA u t * log
      t * u⁻¹ - 2 * i15HxA u t * log t * u - 2 * i15HxA u t * log (1 - t) * u⁻¹ - 2 * i15HxA u t *
      log (1 - t) * u - 2 * i15HxB u t * log t * u⁻¹ - 2 * i15HxB u t * log t * u - 2 * i15HxB u t
      * log (1 - t) * u⁻¹ - 2 * i15HxB u t * log (1 - t) * u - 2 * log t * log u * u⁻¹ - 2 * log (1
      - t) * log u * u⁻¹ + 2 * i15HxA u t * log u * u⁻¹ + 2 * i15HxA u t * log u * u + 2 * i15HxB u
      t * log u * u⁻¹ + 2 * i15HxB u t * log u * u + 2 * log t * log (1 - t) * u⁻¹ + 4 * i15HxA u t
      * i15HxB u t * u⁻¹ + 4 * i15HxA u t * i15HxB u t * u) * ex + (-8 - log t ^ 2 - log (1 - t) ^
      2 - log u ^ 2 - 4 * log t - 4 * log (1 - t) - 4 * i15HxA u t ^ 2 - 4 * i15HxB u t ^ 2 + 4 *
      log u + 4 * u + 8 * i15HxA u t + 8 * i15HxB u t + 8 * u⁻¹ + u⁻¹ * log t ^ 2 + u⁻¹ * log (1 -
      t) ^ 2 + u⁻¹ * log u ^ 2 + u * log t ^ 2 / 2 + u * log (1 - t) ^ 2 / 2 + u * log u ^ 2 / 2 -
      8 * i15HxA u t * i15HxB u t - 4 * i15HxA u t * log u - 4 * i15HxA u t * u⁻¹ - 4 * i15HxA u t
      * u - 4 * i15HxB u t * log u - 4 * i15HxB u t * u⁻¹ - 4 * i15HxB u t * u - 2 * log t * log (1
      - t) - 2 * log u * u + 2 * log t * log u + 2 * log t * u + 2 * log (1 - t) * log u + 2 * log
      (1 - t) * u + 2 * u⁻¹ * i15HxA u t ^ 2 + 2 * u⁻¹ * i15HxB u t ^ 2 + 2 * u * i15HxA u t ^ 2 +
      2 * u * i15HxB u t ^ 2 + 4 * i15HxA u t * log t + 4 * i15HxA u t * log (1 - t) + 4 * i15HxB u
      t * log t + 4 * i15HxB u t * log (1 - t) + log t * log (1 - t) * u - log t * log u * u - log
      (1 - t) * log u * u - 2 * i15HxA u t * log t * u⁻¹ - 2 * i15HxA u t * log t * u - 2 * i15HxA
      u t * log (1 - t) * u⁻¹ - 2 * i15HxA u t * log (1 - t) * u - 2 * i15HxB u t * log t * u⁻¹ - 2
      * i15HxB u t * log t * u - 2 * i15HxB u t * log (1 - t) * u⁻¹ - 2 * i15HxB u t * log (1 - t)
      * u - 2 * log t * log u * u⁻¹ - 2 * log (1 - t) * log u * u⁻¹ + 2 * i15HxA u t * log u * u⁻¹
      + 2 * i15HxA u t * log u * u + 2 * i15HxB u t * log u * u⁻¹ + 2 * i15HxB u t * log u * u + 2
      * log t * log (1 - t) * u⁻¹ + 4 * i15HxA u t * i15HxB u t * u⁻¹ + 4 * i15HxA u t * i15HxB u t
      * u) * ey + (16 - 16 * i15HxA u t - 16 * i15HxB u t - 8 * log u - 8 * u⁻¹ - 8 * u + 2 * log t
      ^ 2 + 2 * log (1 - t) ^ 2 + 2 * log u ^ 2 + 8 * log t + 8 * log (1 - t) + 8 * i15HxA u t ^ 2
      + 8 * i15HxB u t ^ 2 - u⁻¹ * log t ^ 2 - u⁻¹ * log (1 - t) ^ 2 - u⁻¹ * log u ^ 2 - u * log t
      ^ 2 - u * log (1 - t) ^ 2 - u * log u ^ 2 - 8 * i15HxA u t * log t - 8 * i15HxA u t * log (1
      - t) - 8 * i15HxB u t * log t - 8 * i15HxB u t * log (1 - t) - 4 * log t * log u - 4 * log t
      * u⁻¹ - 4 * log t * u - 4 * log (1 - t) * log u - 4 * log (1 - t) * u⁻¹ - 4 * log (1 - t) * u
      - 4 * u⁻¹ * i15HxA u t ^ 2 - 4 * u⁻¹ * i15HxB u t ^ 2 - 4 * u * i15HxA u t ^ 2 - 4 * u *
      i15HxB u t ^ 2 + 4 * log t * log (1 - t) + 4 * log u * u⁻¹ + 4 * log u * u + 8 * i15HxA u t *
      log u + 8 * i15HxA u t * u⁻¹ + 8 * i15HxA u t * u + 8 * i15HxB u t * log u + 8 * i15HxB u t *
      u⁻¹ + 8 * i15HxB u t * u + 16 * i15HxA u t * i15HxB u t - 8 * i15HxA u t * i15HxB u t * u⁻¹ -
      8 * i15HxA u t * i15HxB u t * u - 4 * i15HxA u t * log u * u⁻¹ - 4 * i15HxA u t * log u * u -
      4 * i15HxB u t * log u * u⁻¹ - 4 * i15HxB u t * log u * u - 2 * log t * log (1 - t) * u⁻¹ - 2
      * log t * log (1 - t) * u + 2 * log t * log u * u⁻¹ + 2 * log t * log u * u + 2 * log (1 - t)
      * log u * u⁻¹ + 2 * log (1 - t) * log u * u + 4 * i15HxA u t * log t * u⁻¹ + 4 * i15HxA u t *
      log t * u + 4 * i15HxA u t * log (1 - t) * u⁻¹ + 4 * i15HxA u t * log (1 - t) * u + 4 *
      i15HxB u t * log t * u⁻¹ + 4 * i15HxB u t * log t * u + 4 * i15HxB u t * log (1 - t) * u⁻¹ +
      4 * i15HxB u t * log (1 - t) * u) * ea + (16 - 16 * i15HxA u t - 16 * i15HxB u t - 8 * log u
      - 8 * u⁻¹ - 8 * u + 2 * log t ^ 2 + 2 * log (1 - t) ^ 2 + 2 * log u ^ 2 + 8 * log t + 8 * log
      (1 - t) + 8 * i15HxA u t ^ 2 + 8 * i15HxB u t ^ 2 - u⁻¹ * log t ^ 2 - u⁻¹ * log (1 - t) ^ 2 -
      u⁻¹ * log u ^ 2 - u * log t ^ 2 - u * log (1 - t) ^ 2 - u * log u ^ 2 - 8 * i15HxA u t * log
      t - 8 * i15HxA u t * log (1 - t) - 8 * i15HxB u t * log t - 8 * i15HxB u t * log (1 - t) - 4
      * log t * log u - 4 * log t * u⁻¹ - 4 * log t * u - 4 * log (1 - t) * log u - 4 * log (1 - t)
      * u⁻¹ - 4 * log (1 - t) * u - 4 * u⁻¹ * i15HxA u t ^ 2 - 4 * u⁻¹ * i15HxB u t ^ 2 - 4 * u *
      i15HxA u t ^ 2 - 4 * u * i15HxB u t ^ 2 + 4 * log t * log (1 - t) + 4 * log u * u⁻¹ + 4 * log
      u * u + 8 * i15HxA u t * log u + 8 * i15HxA u t * u⁻¹ + 8 * i15HxA u t * u + 8 * i15HxB u t *
      log u + 8 * i15HxB u t * u⁻¹ + 8 * i15HxB u t * u + 16 * i15HxA u t * i15HxB u t - 8 * i15HxA
      u t * i15HxB u t * u⁻¹ - 8 * i15HxA u t * i15HxB u t * u - 4 * i15HxA u t * log u * u⁻¹ - 4 *
      i15HxA u t * log u * u - 4 * i15HxB u t * log u * u⁻¹ - 4 * i15HxB u t * log u * u - 2 * log
      t * log (1 - t) * u⁻¹ - 2 * log t * log (1 - t) * u + 2 * log t * log u * u⁻¹ + 2 * log t *
      log u * u + 2 * log (1 - t) * log u * u⁻¹ + 2 * log (1 - t) * log u * u + 4 * i15HxA u t *
      log t * u⁻¹ + 4 * i15HxA u t * log t * u + 4 * i15HxA u t * log (1 - t) * u⁻¹ + 4 * i15HxA u
      t * log (1 - t) * u + 4 * i15HxB u t * log t * u⁻¹ + 4 * i15HxB u t * log t * u + 4 * i15HxB
      u t * log (1 - t) * u⁻¹ + 4 * i15HxB u t * log (1 - t) * u) * eb + (8 * (u + (1 - u) * t)⁻¹ +
      8 * (1 - (1 - u) * t)⁻¹ - 8 * i15HxA u t ^ 3 / 3 - 8 * i15HxB u t ^ 3 / 3 - log u ^ 3 / 3 +
      log t ^ 3 / 3 + log (1 - t) ^ 3 / 3 + log t * log (1 - t) ^ 2 + log t * log u ^ 2 + log (1 -
      t) * log t ^ 2 + log (1 - t) * log u ^ 2 + (u + (1 - u) * t)⁻¹ * log t ^ 2 + (u + (1 - u) *
      t)⁻¹ * log (1 - t) ^ 2 + (u + (1 - u) * t)⁻¹ * log u ^ 2 + (1 - (1 - u) * t)⁻¹ * log t ^ 2 +
      (1 - (1 - u) * t)⁻¹ * log (1 - t) ^ 2 + (1 - (1 - u) * t)⁻¹ * log u ^ 2 - log u * log t ^ 2 -
      log u * log (1 - t) ^ 2 - 8 * i15HxA u t * (u + (1 - u) * t)⁻¹ - 8 * i15HxA u t * (1 - (1 -
      u) * t)⁻¹ - 8 * i15HxA u t * i15HxB u t ^ 2 - 8 * i15HxB u t * (u + (1 - u) * t)⁻¹ - 8 *
      i15HxB u t * (1 - (1 - u) * t)⁻¹ - 8 * i15HxB u t * i15HxA u t ^ 2 - 4 * log u * (u + (1 - u)
      * t)⁻¹ - 4 * log u * (1 - (1 - u) * t)⁻¹ - 4 * log u * i15HxA u t ^ 2 - 4 * log u * i15HxB u
      t ^ 2 - 2 * i15HxA u t * log t ^ 2 - 2 * i15HxA u t * log (1 - t) ^ 2 - 2 * i15HxA u t * log
      u ^ 2 - 2 * i15HxB u t * log t ^ 2 - 2 * i15HxB u t * log (1 - t) ^ 2 - 2 * i15HxB u t * log
      u ^ 2 + 4 * log t * (u + (1 - u) * t)⁻¹ + 4 * log t * (1 - (1 - u) * t)⁻¹ + 4 * log t *
      i15HxA u t ^ 2 + 4 * log t * i15HxB u t ^ 2 + 4 * log (1 - t) * (u + (1 - u) * t)⁻¹ + 4 * log
      (1 - t) * (1 - (1 - u) * t)⁻¹ + 4 * log (1 - t) * i15HxA u t ^ 2 + 4 * log (1 - t) * i15HxB u
      t ^ 2 + 4 * (u + (1 - u) * t)⁻¹ * i15HxA u t ^ 2 + 4 * (u + (1 - u) * t)⁻¹ * i15HxB u t ^ 2 +
      4 * (1 - (1 - u) * t)⁻¹ * i15HxA u t ^ 2 + 4 * (1 - (1 - u) * t)⁻¹ * i15HxB u t ^ 2 - u * log
      t ^ 3 / 6 - u * log (1 - t) ^ 3 / 6 + u * log u ^ 3 / 6 + 4 * u * i15HxA u t ^ 3 / 3 + 4 * u
      * i15HxB u t ^ 3 / 3 + i15HxA u t * u * log t ^ 2 + i15HxA u t * u * log (1 - t) ^ 2 + i15HxA
      u t * u * log u ^ 2 + i15HxB u t * u * log t ^ 2 + i15HxB u t * u * log (1 - t) ^ 2 + i15HxB
      u t * u * log u ^ 2 + log u * u * log t ^ 2 / 2 + log u * u * log (1 - t) ^ 2 / 2 - 8 *
      i15HxA u t * i15HxB u t * log u - 4 * i15HxA u t * log t * log (1 - t) - 4 * i15HxA u t * log
      t * (u + (1 - u) * t)⁻¹ - 4 * i15HxA u t * log t * (1 - (1 - u) * t)⁻¹ - 4 * i15HxA u t * log
      (1 - t) * (u + (1 - u) * t)⁻¹ - 4 * i15HxA u t * log (1 - t) * (1 - (1 - u) * t)⁻¹ - 4 *
      i15HxB u t * log t * log (1 - t) - 4 * i15HxB u t * log t * (u + (1 - u) * t)⁻¹ - 4 * i15HxB
      u t * log t * (1 - (1 - u) * t)⁻¹ - 4 * i15HxB u t * log (1 - t) * (u + (1 - u) * t)⁻¹ - 4 *
      i15HxB u t * log (1 - t) * (1 - (1 - u) * t)⁻¹ - 2 * log t * log (1 - t) * log u - 2 * log t
      * log u * (u + (1 - u) * t)⁻¹ - 2 * log t * log u * (1 - (1 - u) * t)⁻¹ - 2 * log t * u *
      i15HxA u t ^ 2 - 2 * log t * u * i15HxB u t ^ 2 - 2 * log (1 - t) * log u * (u + (1 - u) *
      t)⁻¹ - 2 * log (1 - t) * log u * (1 - (1 - u) * t)⁻¹ - 2 * log (1 - t) * u * i15HxA u t ^ 2 -
      2 * log (1 - t) * u * i15HxB u t ^ 2 + 2 * log t * log (1 - t) * (u + (1 - u) * t)⁻¹ + 2 *
      log t * log (1 - t) * (1 - (1 - u) * t)⁻¹ + 2 * log u * u * i15HxA u t ^ 2 + 2 * log u * u *
      i15HxB u t ^ 2 + 4 * i15HxA u t * log t * log u + 4 * i15HxA u t * log (1 - t) * log u + 4 *
      i15HxA u t * log u * (u + (1 - u) * t)⁻¹ + 4 * i15HxA u t * log u * (1 - (1 - u) * t)⁻¹ + 4 *
      i15HxA u t * u * i15HxB u t ^ 2 + 4 * i15HxB u t * log t * log u + 4 * i15HxB u t * log (1 -
      t) * log u + 4 * i15HxB u t * log u * (u + (1 - u) * t)⁻¹ + 4 * i15HxB u t * log u * (1 - (1
      - u) * t)⁻¹ + 4 * i15HxB u t * u * i15HxA u t ^ 2 + 8 * i15HxA u t * i15HxB u t * log t + 8 *
      i15HxA u t * i15HxB u t * log (1 - t) + 8 * i15HxA u t * i15HxB u t * (u + (1 - u) * t)⁻¹ + 8
      * i15HxA u t * i15HxB u t * (1 - (1 - u) * t)⁻¹ - log t * u * log (1 - t) ^ 2 / 2 - log t * u
      * log u ^ 2 / 2 - log (1 - t) * u * log t ^ 2 / 2 - log (1 - t) * u * log u ^ 2 / 2 + log t *
      log (1 - t) * log u * u - 4 * i15HxA u t * i15HxB u t * log t * u - 4 * i15HxA u t * i15HxB u
      t * log (1 - t) * u - 2 * i15HxA u t * log t * log u * u - 2 * i15HxA u t * log (1 - t) * log
      u * u - 2 * i15HxB u t * log t * log u * u - 2 * i15HxB u t * log (1 - t) * log u * u + 2 *
      i15HxA u t * log t * log (1 - t) * u + 2 * i15HxB u t * log t * log (1 - t) * u + 4 * i15HxA
      u t * i15HxB u t * log u * u) * eu

theorem i15HxP_reflect (u x l₁ l₂ a b : ℝ) :
    i15TPoly (i15HxP0 u) x l₁ l₂ a b = i15TPoly (i15HxP1 u) (1 - x) l₂ l₁ (log u + a) (b - log u)
        := by
  simp only [i15HxP0, i15HxP1, i15TPoly, i15TMono, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ring

theorem i15HxB_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxB u (1 - t) = log u + i15HxA u t := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxA i15HxB
  rw [← log_mul h0.ne' h7.ne']
  congr 1
  field_simp
  ring

theorem i15HxA_one_sub {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    i15HxA u (1 - t) = i15HxB u t - log u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu ht
  unfold i15HxA i15HxB
  rw [← log_div h6.ne' h0.ne']
  congr 1
  field_simp
  ring

theorem tendsto_i15HxPhi_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i15HxPhi u) (𝓝[>] 0) (𝓝 (i15HxPhi0 u)) := by
  obtain ⟨hb1, hb2, hb3⟩ := i15Hx_bounds hu
  have hC : 0 ≤ 2 + u⁻¹ := by have := inv_pos.2 hu.1; linarith
  have hm := i15Hx_val_mem hu
  have ev : ∀ᶠ y in 𝓝[>] 0, y ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hP := i15Hx_tendsto_poly (i15HxP0 u) hC hb1 hb2 hb3
    (by simp only [i15HxP0, List.map_cons, List.map_nil]; decide)
  have hX0 : Tendsto (i15HxX0 u) (𝓝[>] 0) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX0 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX0_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm0 : ∀ᶠ y in 𝓝[>] 0, i15HxX0 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX0_mem hu hy
  have hG0 := i15Hx_tendsto_TG hX0 ⟨one_pos, le_rfl⟩ hm0
  have hL0 := i15Hx_tendsto_Li₂ hX0 (⟨zero_le_one, le_rfl⟩) hm0
  have hX1 : Tendsto (i15HxX1 u) (𝓝[>] 0) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX1 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX1_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm1 : ∀ᶠ y in 𝓝[>] 0, i15HxX1 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX1_mem hu hy
  have hG1 := i15Hx_tendsto_TG_zero hX1 hm1
  have hL1 := i15Hx_tendsto_Li₂ hX1 (⟨le_rfl, zero_le_one⟩) hm1
  have hX2 : Tendsto (i15HxX2 u) (𝓝[>] 0) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX2 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX2_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm2 : ∀ᶠ y in 𝓝[>] 0, i15HxX2 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX2_mem hu hy
  have hG2 := i15Hx_tendsto_TG hX2 ⟨one_pos, le_rfl⟩ hm2
  have hL2 := i15Hx_tendsto_Li₂ hX2 (⟨zero_le_one, le_rfl⟩) hm2
  have hX3 : Tendsto (i15HxX3 u) (𝓝[>] 0) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX3 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX3_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm3 : ∀ᶠ y in 𝓝[>] 0, i15HxX3 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX3_mem hu hy
  have hG3 := i15Hx_tendsto_TG_zero hX3 hm3
  have hL3 := i15Hx_tendsto_Li₂ hX3 (⟨le_rfl, zero_le_one⟩) hm3
  have hX4 : Tendsto (i15HxX4 u) (𝓝[>] 0) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX4 u 0).tendsto
    rw [i15HxX4_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm4 : ∀ᶠ y in 𝓝[>] 0, i15HxX4 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX4_mem hu hy
  have hG4 := i15Hx_tendsto_TG hX4 ⟨one_pos, le_rfl⟩ hm4
  have hL4 := i15Hx_tendsto_Li₂ hX4 (⟨zero_le_one, le_rfl⟩) hm4
  have hX5 : Tendsto (i15HxX5 u) (𝓝[>] 0) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX5 u 0).tendsto
    rw [i15HxX5_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm5 : ∀ᶠ y in 𝓝[>] 0, i15HxX5 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX5_mem hu hy
  have hG5 := i15Hx_tendsto_TG_zero hX5 hm5
  have hL5 := i15Hx_tendsto_Li₂ hX5 (⟨le_rfl, zero_le_one⟩) hm5
  have hX6 : Tendsto (i15HxX6 u) (𝓝[>] 0) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX6 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX6_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm6 : ∀ᶠ y in 𝓝[>] 0, i15HxX6 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX6_mem hu hy
  have hG6 := i15Hx_tendsto_TG hX6 ⟨one_pos, le_rfl⟩ hm6
  have hL6 := i15Hx_tendsto_Li₂ hX6 (⟨zero_le_one, le_rfl⟩) hm6
  have hX7 : Tendsto (i15HxX7 u) (𝓝[>] 0) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX7 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX7_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm7 : ∀ᶠ y in 𝓝[>] 0, i15HxX7 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX7_mem hu hy
  have hG7 := i15Hx_tendsto_TG_zero hX7 hm7
  have hL7 := i15Hx_tendsto_Li₂ hX7 (⟨le_rfl, zero_le_one⟩) hm7
  have hX8 : Tendsto (i15HxX8 u) (𝓝[>] 0) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX8 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX8_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm8 : ∀ᶠ y in 𝓝[>] 0, i15HxX8 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX8_mem hu hy
  have hG8 := i15Hx_tendsto_TG hX8 ⟨one_pos, le_rfl⟩ hm8
  have hL8 := i15Hx_tendsto_Li₂ hX8 (⟨zero_le_one, le_rfl⟩) hm8
  have hX9 : Tendsto (i15HxX9 u) (𝓝[>] 0) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX9 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX9_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm9 : ∀ᶠ y in 𝓝[>] 0, i15HxX9 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX9_mem hu hy
  have hG9 := i15Hx_tendsto_TG_zero hX9 hm9
  have hL9 := i15Hx_tendsto_Li₂ hX9 (⟨le_rfl, zero_le_one⟩) hm9
  have hX10 : Tendsto (i15HxX10 u) (𝓝[>] 0) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX10 u 0).tendsto
    rw [i15HxX10_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm10 : ∀ᶠ y in 𝓝[>] 0, i15HxX10 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX10_mem hu hy
  have hG10 := i15Hx_tendsto_TG hX10 ⟨one_pos, le_rfl⟩ hm10
  have hL10 := i15Hx_tendsto_Li₂ hX10 (⟨zero_le_one, le_rfl⟩) hm10
  have hX11 : Tendsto (i15HxX11 u) (𝓝[>] 0) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX11 u 0).tendsto
    rw [i15HxX11_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm11 : ∀ᶠ y in 𝓝[>] 0, i15HxX11 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX11_mem hu hy
  have hG11 := i15Hx_tendsto_TG_zero hX11 hm11
  have hL11 := i15Hx_tendsto_Li₂ hX11 (⟨le_rfl, zero_le_one⟩) hm11
  have hX12 : Tendsto (i15HxX12 u) (𝓝[>] 0) (𝓝 (u ^ 2)) := by
    have h := (continuousAt_i15HxX12 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX12_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm12 : ∀ᶠ y in 𝓝[>] 0, i15HxX12 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX12_mem hu hy
  have hG12 := i15Hx_tendsto_TG hX12 hm.1 hm12
  have hL12 := i15Hx_tendsto_Li₂ hX12 (Ioc_subset_Icc_self hm.1) hm12
  have hX13 : Tendsto (i15HxX13 u) (𝓝[>] 0) (𝓝 ((1 - u) * (1 + u))) := by
    have h := (continuousAt_i15HxX13 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX13_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm13 : ∀ᶠ y in 𝓝[>] 0, i15HxX13 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX13_mem hu hy
  have hG13 := i15Hx_tendsto_TG hX13 hm.2.1 hm13
  have hX14 : Tendsto (i15HxX14 u) (𝓝[>] 0) (𝓝 (u)) := by
    have h := (continuousAt_i15HxX14 u 0).tendsto
    rw [i15HxX14_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm14 : ∀ᶠ y in 𝓝[>] 0, i15HxX14 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX14_mem hu hy
  have hG14 := i15Hx_tendsto_TG hX14 hm.2.2.1 hm14
  have hL14 := i15Hx_tendsto_Li₂ hX14 (Ioc_subset_Icc_self hm.2.2.1) hm14
  have hX15 : Tendsto (i15HxX15 u) (𝓝[>] 0) (𝓝 (1 - u)) := by
    have h := (continuousAt_i15HxX15 u 0).tendsto
    rw [i15HxX15_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm15 : ∀ᶠ y in 𝓝[>] 0, i15HxX15 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX15_mem hu hy
  have hG15 := i15Hx_tendsto_TG hX15 hm.2.2.2.1 hm15
  have hX16 : Tendsto (i15HxX16 u) (𝓝[>] 0) (𝓝 (u)) := by
    have h := (continuousAt_i15HxX16 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX16_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm16 : ∀ᶠ y in 𝓝[>] 0, i15HxX16 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX16_mem hu hy
  have hG16 := i15Hx_tendsto_TG hX16 hm.2.2.1 hm16
  have hL16 := i15Hx_tendsto_Li₂ hX16 (Ioc_subset_Icc_self hm.2.2.1) hm16
  have hX17 : Tendsto (i15HxX17 u) (𝓝[>] 0) (𝓝 (1 - u)) := by
    have h := (continuousAt_i15HxX17 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX17_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm17 : ∀ᶠ y in 𝓝[>] 0, i15HxX17 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX17_mem hu hy
  have hG17 := i15Hx_tendsto_TG hX17 hm.2.2.2.1 hm17
  have hX18 : Tendsto (i15HxX18 u) (𝓝[>] 0) (𝓝 (1 / (1 + u))) := by
    have h := (continuousAt_i15HxX18 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX18_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm18 : ∀ᶠ y in 𝓝[>] 0, i15HxX18 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX18_mem hu hy
  have hG18 := i15Hx_tendsto_TG hX18 hm.2.2.2.2.1 hm18
  have hX19 : Tendsto (i15HxX19 u) (𝓝[>] 0) (𝓝 (u / (1 + u))) := by
    have h := (continuousAt_i15HxX19 hu ⟨le_rfl, zero_le_one⟩).tendsto
    rw [i15HxX19_zero hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm19 : ∀ᶠ y in 𝓝[>] 0, i15HxX19 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX19_mem hu hy
  have hG19 := i15Hx_tendsto_TG hX19 hm.2.2.2.2.2 hm19
  exact (((((((((((((((((((((((((((((((((((hP.add (hG0.const_mul (2 - 2 * u))).add (hG1.const_mul
      (-2 + 2 * u⁻¹))).add (hG2.const_mul (2 - 2 * u⁻¹))).add (hG3.const_mul (-2 + 2 * u))).add
      (hG4.const_mul (-2 + u))).add (hG5.const_mul (2 - u))).add (hG6.const_mul (-4 + 4 * u))).add
      (hG7.const_mul (-4 * u⁻¹ + 4 * u))).add (hG8.const_mul (4 - 4 * u))).add (hG9.const_mul (-2 *
      u + 2 * u⁻¹))).add (hG10.const_mul (4 - 2 * u⁻¹ - 2 * u))).add (hG11.const_mul (-2 * u + 2 *
      u⁻¹))).add (hG12.const_mul (4 - 4 * u))).add (hG13.const_mul (-4 * u + 4 * u⁻¹))).add
      (hG14.const_mul (-4 + 2 * u⁻¹ + 2 * u))).add (hG15.const_mul (-2 * u⁻¹ + 2 * u))).add
      (hG16.const_mul (-4 + 4 * u))).add (hG17.const_mul (-2 * u⁻¹ + 2 * u))).add (hG18.const_mul
      (-4 * u + 4 * u⁻¹))).add (hG19.const_mul (-4 * u⁻¹ + 4 * u))).add (hL0.const_mul (-8 - 2 *
      log u + 4 * u⁻¹ + 4 * u - 4 * log (1 + u) * u⁻¹ - 2 * log (1 - u) * u⁻¹ + 2 * log u * u⁻¹ + 2
      * log (1 - u) * u + 4 * log (1 + u) * u))).add (hL1.const_mul (-4 * u⁻¹ + 4 * u + log u * u -
      log u * u⁻¹ - 8 * log (1 + u) * u - 3 * log (1 - u) * u + 3 * log (1 - u) * u⁻¹ + 8 * log (1
      + u) * u⁻¹))).add (hL2.const_mul (log (1 - u) * u⁻¹ - log (1 - u) * u - 2 * log (1 + u) * u +
      2 * log (1 + u) * u⁻¹))).add (hL3.const_mul (-4 * u - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log
      u * u - 6 * log (1 + u) * u⁻¹ - 2 * log (1 - u) * u⁻¹ + 2 * log (1 - u) * u + 6 * log (1 + u)
      * u))).add (hL4.const_mul (4 - 4 * u⁻¹ - 2 * u + 2 * log u + log (1 - u) * u⁻¹ - log u * u -
      log (1 - u) * u - 2 * log u * u⁻¹ - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹))).add
      (hL5.const_mul (log (1 - u) * u - log (1 - u) * u⁻¹ - 2 * log (1 + u) * u⁻¹ + 2 * log (1 + u)
      * u))).add (hL6.const_mul (8 - 8 * u⁻¹ - 8 * log (1 + u) * u - 4 * log u * u⁻¹ - 4 * log (1 -
      u) * u + 4 * log u * u + 4 * log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹))).add (hL7.const_mul
      (-8 * u + 8 * u⁻¹ - 12 * log (1 + u) * u⁻¹ - 6 * log (1 - u) * u⁻¹ - 2 * log u * u + 2 * log
      u * u⁻¹ + 6 * log (1 - u) * u + 12 * log (1 + u) * u))).add (hL8.const_mul (-4 + 2 * log u +
      4 * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ - 4 * log u * u - 2 * log (1 + u) * u⁻¹ + 2 *
      log u * u⁻¹ + 2 * log (1 + u) * u))).add (hL9.const_mul (-4 * u⁻¹ + 4 * u + log u * u - log u
      * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 * log (1 - u) * u⁻¹ + 2 * log (1 + u) *
      u⁻¹))).add (hL10.const_mul (-4 - 2 * log u + 4 * u⁻¹ - 6 * log (1 + u) * u⁻¹ - 3 * log (1 -
      u) * u⁻¹ + 2 * log u * u⁻¹ + 3 * log (1 - u) * u + 6 * log (1 + u) * u))).add (hL11.const_mul
      (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
      log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹))).add (hL12.const_mul (8 - 8 * u⁻¹ + 8 * log u - 6
      * log u * u - 4 * log (1 + u) * u - 2 * log u * u⁻¹ - 2 * log (1 - u) * u + 2 * log (1 - u) *
      u⁻¹ + 4 * log (1 + u) * u⁻¹))).add (hL14.const_mul (-4 - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ +
      log u * u + log (1 - u) * u⁻¹ - log (1 - u) * u - 4 * log (1 + u) * u + 4 * log (1 + u) *
      u⁻¹))).add (hL16.const_mul (-4 - 6 * log u + 4 * u⁻¹ + log u * u⁻¹ + log (1 - u) * u - log (1
      - u) * u⁻¹ + 5 * log u * u)))

theorem tendsto_i15HxPhi_one {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i15HxPhi u) (𝓝[<] 1) (𝓝 (i15HxPhi1 u)) := by
  obtain ⟨hb1, hb2, hb3⟩ := i15Hx_bounds hu
  have hC : 0 ≤ 2 + u⁻¹ := by have := inv_pos.2 hu.1; linarith
  have hm := i15Hx_val_mem hu
  have ev : ∀ᶠ y in 𝓝[<] 1, y ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  have hg := i15Hx_tendsto_poly (i15HxP1 u) hC hb1 hb3 hb2
    (by simp only [i15HxP1, List.map_cons, List.map_nil]; decide)
  have hr : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.2 ht
  have hP : Tendsto (fun t => i15TPoly (i15HxP0 u) t (log t) (log (1 - t)) (i15HxA u t)
      (i15HxB u t)) (𝓝[<] 1) (𝓝 (i15TPoly (i15HxP1 u) 0 1 0 0 0)) := by
    refine (hg.comp hr).congr' ?_
    filter_upwards [ev] with t ht
    simp only [Function.comp_apply]
    rw [sub_sub_cancel, i15HxB_one_sub hu ht, i15HxA_one_sub hu ht, i15HxP_reflect]
  have hX0 : Tendsto (i15HxX0 u) (𝓝[<] 1) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX0 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX0_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm0 : ∀ᶠ y in 𝓝[<] 1, i15HxX0 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX0_mem hu hy
  have hG0 := i15Hx_tendsto_TG_zero hX0 hm0
  have hL0 := i15Hx_tendsto_Li₂ hX0 (⟨le_rfl, zero_le_one⟩) hm0
  have hX1 : Tendsto (i15HxX1 u) (𝓝[<] 1) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX1 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX1_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm1 : ∀ᶠ y in 𝓝[<] 1, i15HxX1 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX1_mem hu hy
  have hG1 := i15Hx_tendsto_TG hX1 ⟨one_pos, le_rfl⟩ hm1
  have hL1 := i15Hx_tendsto_Li₂ hX1 (⟨zero_le_one, le_rfl⟩) hm1
  have hX2 : Tendsto (i15HxX2 u) (𝓝[<] 1) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX2 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX2_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm2 : ∀ᶠ y in 𝓝[<] 1, i15HxX2 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX2_mem hu hy
  have hG2 := i15Hx_tendsto_TG_zero hX2 hm2
  have hL2 := i15Hx_tendsto_Li₂ hX2 (⟨le_rfl, zero_le_one⟩) hm2
  have hX3 : Tendsto (i15HxX3 u) (𝓝[<] 1) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX3 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX3_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm3 : ∀ᶠ y in 𝓝[<] 1, i15HxX3 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX3_mem hu hy
  have hG3 := i15Hx_tendsto_TG hX3 ⟨one_pos, le_rfl⟩ hm3
  have hL3 := i15Hx_tendsto_Li₂ hX3 (⟨zero_le_one, le_rfl⟩) hm3
  have hX4 : Tendsto (i15HxX4 u) (𝓝[<] 1) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX4 u 1).tendsto
    rw [i15HxX4_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm4 : ∀ᶠ y in 𝓝[<] 1, i15HxX4 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX4_mem hu hy
  have hG4 := i15Hx_tendsto_TG_zero hX4 hm4
  have hL4 := i15Hx_tendsto_Li₂ hX4 (⟨le_rfl, zero_le_one⟩) hm4
  have hX5 : Tendsto (i15HxX5 u) (𝓝[<] 1) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX5 u 1).tendsto
    rw [i15HxX5_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm5 : ∀ᶠ y in 𝓝[<] 1, i15HxX5 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX5_mem hu hy
  have hG5 := i15Hx_tendsto_TG hX5 ⟨one_pos, le_rfl⟩ hm5
  have hL5 := i15Hx_tendsto_Li₂ hX5 (⟨zero_le_one, le_rfl⟩) hm5
  have hX6 : Tendsto (i15HxX6 u) (𝓝[<] 1) (𝓝 (u ^ 2)) := by
    have h := (continuousAt_i15HxX6 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX6_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm6 : ∀ᶠ y in 𝓝[<] 1, i15HxX6 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX6_mem hu hy
  have hG6 := i15Hx_tendsto_TG hX6 hm.1 hm6
  have hL6 := i15Hx_tendsto_Li₂ hX6 (Ioc_subset_Icc_self hm.1) hm6
  have hX7 : Tendsto (i15HxX7 u) (𝓝[<] 1) (𝓝 ((1 - u) * (1 + u))) := by
    have h := (continuousAt_i15HxX7 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX7_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm7 : ∀ᶠ y in 𝓝[<] 1, i15HxX7 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX7_mem hu hy
  have hG7 := i15Hx_tendsto_TG hX7 hm.2.1 hm7
  have hL7 := i15Hx_tendsto_Li₂ hX7 (Ioc_subset_Icc_self hm.2.1) hm7
  have hX8 : Tendsto (i15HxX8 u) (𝓝[<] 1) (𝓝 (u)) := by
    have h := (continuousAt_i15HxX8 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX8_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm8 : ∀ᶠ y in 𝓝[<] 1, i15HxX8 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX8_mem hu hy
  have hG8 := i15Hx_tendsto_TG hX8 hm.2.2.1 hm8
  have hL8 := i15Hx_tendsto_Li₂ hX8 (Ioc_subset_Icc_self hm.2.2.1) hm8
  have hX9 : Tendsto (i15HxX9 u) (𝓝[<] 1) (𝓝 (1 - u)) := by
    have h := (continuousAt_i15HxX9 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX9_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm9 : ∀ᶠ y in 𝓝[<] 1, i15HxX9 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX9_mem hu hy
  have hG9 := i15Hx_tendsto_TG hX9 hm.2.2.2.1 hm9
  have hL9 := i15Hx_tendsto_Li₂ hX9 (Ioc_subset_Icc_self hm.2.2.2.1) hm9
  have hX10 : Tendsto (i15HxX10 u) (𝓝[<] 1) (𝓝 (u)) := by
    have h := (continuousAt_i15HxX10 u 1).tendsto
    rw [i15HxX10_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm10 : ∀ᶠ y in 𝓝[<] 1, i15HxX10 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX10_mem hu hy
  have hG10 := i15Hx_tendsto_TG hX10 hm.2.2.1 hm10
  have hL10 := i15Hx_tendsto_Li₂ hX10 (Ioc_subset_Icc_self hm.2.2.1) hm10
  have hX11 : Tendsto (i15HxX11 u) (𝓝[<] 1) (𝓝 (1 - u)) := by
    have h := (continuousAt_i15HxX11 u 1).tendsto
    rw [i15HxX11_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm11 : ∀ᶠ y in 𝓝[<] 1, i15HxX11 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX11_mem hu hy
  have hG11 := i15Hx_tendsto_TG hX11 hm.2.2.2.1 hm11
  have hL11 := i15Hx_tendsto_Li₂ hX11 (Ioc_subset_Icc_self hm.2.2.2.1) hm11
  have hX12 : Tendsto (i15HxX12 u) (𝓝[<] 1) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX12 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX12_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm12 : ∀ᶠ y in 𝓝[<] 1, i15HxX12 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX12_mem hu hy
  have hG12 := i15Hx_tendsto_TG hX12 ⟨one_pos, le_rfl⟩ hm12
  have hL12 := i15Hx_tendsto_Li₂ hX12 (⟨zero_le_one, le_rfl⟩) hm12
  have hX13 : Tendsto (i15HxX13 u) (𝓝[<] 1) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX13 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX13_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm13 : ∀ᶠ y in 𝓝[<] 1, i15HxX13 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX13_mem hu hy
  have hG13 := i15Hx_tendsto_TG_zero hX13 hm13
  have hX14 : Tendsto (i15HxX14 u) (𝓝[<] 1) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX14 u 1).tendsto
    rw [i15HxX14_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm14 : ∀ᶠ y in 𝓝[<] 1, i15HxX14 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX14_mem hu hy
  have hG14 := i15Hx_tendsto_TG hX14 ⟨one_pos, le_rfl⟩ hm14
  have hL14 := i15Hx_tendsto_Li₂ hX14 (⟨zero_le_one, le_rfl⟩) hm14
  have hX15 : Tendsto (i15HxX15 u) (𝓝[<] 1) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX15 u 1).tendsto
    rw [i15HxX15_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm15 : ∀ᶠ y in 𝓝[<] 1, i15HxX15 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX15_mem hu hy
  have hG15 := i15Hx_tendsto_TG_zero hX15 hm15
  have hX16 : Tendsto (i15HxX16 u) (𝓝[<] 1) (𝓝 (1)) := by
    have h := (continuousAt_i15HxX16 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX16_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm16 : ∀ᶠ y in 𝓝[<] 1, i15HxX16 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX16_mem hu hy
  have hG16 := i15Hx_tendsto_TG hX16 ⟨one_pos, le_rfl⟩ hm16
  have hL16 := i15Hx_tendsto_Li₂ hX16 (⟨zero_le_one, le_rfl⟩) hm16
  have hX17 : Tendsto (i15HxX17 u) (𝓝[<] 1) (𝓝 (0)) := by
    have h := (continuousAt_i15HxX17 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX17_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm17 : ∀ᶠ y in 𝓝[<] 1, i15HxX17 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX17_mem hu hy
  have hG17 := i15Hx_tendsto_TG_zero hX17 hm17
  have hX18 : Tendsto (i15HxX18 u) (𝓝[<] 1) (𝓝 (u / (1 + u))) := by
    have h := (continuousAt_i15HxX18 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX18_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm18 : ∀ᶠ y in 𝓝[<] 1, i15HxX18 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX18_mem hu hy
  have hG18 := i15Hx_tendsto_TG hX18 hm.2.2.2.2.2 hm18
  have hX19 : Tendsto (i15HxX19 u) (𝓝[<] 1) (𝓝 (1 / (1 + u))) := by
    have h := (continuousAt_i15HxX19 hu ⟨zero_le_one, le_rfl⟩).tendsto
    rw [i15HxX19_one hu] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hm19 : ∀ᶠ y in 𝓝[<] 1, i15HxX19 u y ∈ Ioo (0 : ℝ) 1 := ev.mono fun y hy => i15HxX19_mem hu hy
  have hG19 := i15Hx_tendsto_TG hX19 hm.2.2.2.2.1 hm19
  exact (((((((((((((((((((((((((((((((((((hP.add (hG0.const_mul (2 - 2 * u))).add (hG1.const_mul
      (-2 + 2 * u⁻¹))).add (hG2.const_mul (2 - 2 * u⁻¹))).add (hG3.const_mul (-2 + 2 * u))).add
      (hG4.const_mul (-2 + u))).add (hG5.const_mul (2 - u))).add (hG6.const_mul (-4 + 4 * u))).add
      (hG7.const_mul (-4 * u⁻¹ + 4 * u))).add (hG8.const_mul (4 - 4 * u))).add (hG9.const_mul (-2 *
      u + 2 * u⁻¹))).add (hG10.const_mul (4 - 2 * u⁻¹ - 2 * u))).add (hG11.const_mul (-2 * u + 2 *
      u⁻¹))).add (hG12.const_mul (4 - 4 * u))).add (hG13.const_mul (-4 * u + 4 * u⁻¹))).add
      (hG14.const_mul (-4 + 2 * u⁻¹ + 2 * u))).add (hG15.const_mul (-2 * u⁻¹ + 2 * u))).add
      (hG16.const_mul (-4 + 4 * u))).add (hG17.const_mul (-2 * u⁻¹ + 2 * u))).add (hG18.const_mul
      (-4 * u + 4 * u⁻¹))).add (hG19.const_mul (-4 * u⁻¹ + 4 * u))).add (hL0.const_mul (-8 - 2 *
      log u + 4 * u⁻¹ + 4 * u - 4 * log (1 + u) * u⁻¹ - 2 * log (1 - u) * u⁻¹ + 2 * log u * u⁻¹ + 2
      * log (1 - u) * u + 4 * log (1 + u) * u))).add (hL1.const_mul (-4 * u⁻¹ + 4 * u + log u * u -
      log u * u⁻¹ - 8 * log (1 + u) * u - 3 * log (1 - u) * u + 3 * log (1 - u) * u⁻¹ + 8 * log (1
      + u) * u⁻¹))).add (hL2.const_mul (log (1 - u) * u⁻¹ - log (1 - u) * u - 2 * log (1 + u) * u +
      2 * log (1 + u) * u⁻¹))).add (hL3.const_mul (-4 * u - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ + log
      u * u - 6 * log (1 + u) * u⁻¹ - 2 * log (1 - u) * u⁻¹ + 2 * log (1 - u) * u + 6 * log (1 + u)
      * u))).add (hL4.const_mul (4 - 4 * u⁻¹ - 2 * u + 2 * log u + log (1 - u) * u⁻¹ - log u * u -
      log (1 - u) * u - 2 * log u * u⁻¹ - 2 * log (1 + u) * u + 2 * log (1 + u) * u⁻¹))).add
      (hL5.const_mul (log (1 - u) * u - log (1 - u) * u⁻¹ - 2 * log (1 + u) * u⁻¹ + 2 * log (1 + u)
      * u))).add (hL6.const_mul (8 - 8 * u⁻¹ - 8 * log (1 + u) * u - 4 * log u * u⁻¹ - 4 * log (1 -
      u) * u + 4 * log u * u + 4 * log (1 - u) * u⁻¹ + 8 * log (1 + u) * u⁻¹))).add (hL7.const_mul
      (-8 * u + 8 * u⁻¹ - 12 * log (1 + u) * u⁻¹ - 6 * log (1 - u) * u⁻¹ - 2 * log u * u + 2 * log
      u * u⁻¹ + 6 * log (1 - u) * u + 12 * log (1 + u) * u))).add (hL8.const_mul (-4 + 2 * log u +
      4 * u⁻¹ + log (1 - u) * u - log (1 - u) * u⁻¹ - 4 * log u * u - 2 * log (1 + u) * u⁻¹ + 2 *
      log u * u⁻¹ + 2 * log (1 + u) * u))).add (hL9.const_mul (-4 * u⁻¹ + 4 * u + log u * u - log u
      * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 * log (1 - u) * u⁻¹ + 2 * log (1 + u) *
      u⁻¹))).add (hL10.const_mul (-4 - 2 * log u + 4 * u⁻¹ - 6 * log (1 + u) * u⁻¹ - 3 * log (1 -
      u) * u⁻¹ + 2 * log u * u⁻¹ + 3 * log (1 - u) * u + 6 * log (1 + u) * u))).add (hL11.const_mul
      (-4 * u⁻¹ + 4 * u + log u * u - log u * u⁻¹ - 2 * log (1 - u) * u - 2 * log (1 + u) * u + 2 *
      log (1 - u) * u⁻¹ + 2 * log (1 + u) * u⁻¹))).add (hL12.const_mul (8 - 8 * u⁻¹ + 8 * log u - 6
      * log u * u - 4 * log (1 + u) * u - 2 * log u * u⁻¹ - 2 * log (1 - u) * u + 2 * log (1 - u) *
      u⁻¹ + 4 * log (1 + u) * u⁻¹))).add (hL14.const_mul (-4 - 2 * log u + 4 * u⁻¹ + log u * u⁻¹ +
      log u * u + log (1 - u) * u⁻¹ - log (1 - u) * u - 4 * log (1 + u) * u + 4 * log (1 + u) *
      u⁻¹))).add (hL16.const_mul (-4 - 6 * log u + 4 * u⁻¹ + log u * u⁻¹ + log (1 - u) * u - log (1
      - u) * u⁻¹ + 5 * log u * u)))

theorem i15A23k_three_eq_i15HxF {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15A23k 3 (x, u) = i15HxF u x := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := i15Hx_pos hu hx
  have hA : log (u + (1 - u) * x) = log u + i15HxA u x := by
    unfold i15HxA
    rw [← log_mul h0.ne' h7.ne']
    congr 1
    field_simp
  simp only [i15A23k, i15HxF, i15HxB, i15B1_eq hx hu, i15B2_eq hx, hA, Nat.factorial]
  push_cast
  ring

/-- **`∫₀¹ A₂₃,₃(x, u) dx = Φ(1⁻) - Φ(0⁺)`**, given the integrability of the slice. -/
theorem integral_i15A23k_three_slice {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hI : IntegrableOn (fun x => i15A23k 3 (x, u)) (Ioo 0 1)) :
    ∫ x in Ioo (0 : ℝ) 1, i15A23k 3 (x, u) = i15HxPhi1 u - i15HxPhi0 u := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun x hx => (hasDerivAt_i15HxPhi hu hx).congr_deriv (i15A23k_three_eq_i15HxF hx hu).symm)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hI)
    (tendsto_i15HxPhi_zero hu) (tendsto_i15HxPhi_one hu)

end QED.ThreeLoopD
