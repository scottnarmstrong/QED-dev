/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValThreeSum
public import QED.Polylog.Basic
import QED.Polylog.HPLValues
import QED.Polylog.HPLValues3
import QED.Polylog.HPLValues4
import QED.Polylog.HPLValuesTrailing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₅`: the outer integral of the `u`-weighted half of `F₃`

Write `H(w) = H(w; u)` for the harmonic polylogarithms (`QED.Polylog.HPL.hpl`). The inner
`x`-integral `h₃(u) = ∫₀¹ A₂₃,₃(x, u) dx` of the `u`-weighted half
`A₂₃,₃ = (v² b₁³ + b₂³) / (6 u)` of `F₃` (`QED.ThreeLoopD.i15A23k 3`, `v = 1 - u`) is,
numerically to 370 digits (`setDI15e/fit.py`, an exact interpolation in the HPL basis of
weight `≤ 3` with coefficients `1/u, 1, u`),

  `h₃ = (1/u - u) S + (1 - u)(8 H(0,1,0) - 16 H(0,-1,0))`
    `+ (2π²/3 - 12 ζ(3) - 16) + (8 - π²/3) H(0) + 4 H(0,0) + 2 H(0,0,0)`
    `+ u ((14 ζ(3) - π²/3 + 8) + (π²/2 - 12) H(0) - 6 H(0,0) - 3 H(0,0,0))`,

  `S = 8 H(1,0) - 16 H(-1,0) + 4 H(0,1,0) - 8 H(0,-1,0) + 4 H(1,0,0) + 8 H(1,1,0)`
    `- 16 H(1,-1,0) - 8 H(-1,0,0) - 16 H(-1,1,0) + 32 H(-1,-1,0)`.

This file defines that function (`QED.ThreeLoopD.i15H3`) and proves
`∫₀¹ h₃ = 5 ζ(3) - 5π²/8 - 65/16`, the expected value of `∫∫ A₂₃,₃`, by an explicit primitive
`Σ qₜ(u) H(wₜ; u)` (quadratic `qₜ`, words of weight `≤ 4`) and the weight-`4` HPL values at `1`
(in which `Li₄(1/2)`, `log 2` and `π⁴` cancel). The identification `∫₀¹ A₂₃,₃ dx = h₃(u)` is
not proved here.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i15H3Phi`: the primitive.
* `QED.ThreeLoopD.integral_i15H3`: `∫₀¹ h₃ = 5 ζ(3) - 5π²/8 - 65/16`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The `(1/u - u)` part `S` of `h₃`. -/
noncomputable def i15H3S (u : ℝ) : ℝ :=
  8 * hpl [one, zero] u - 16 * hpl [negOne, zero] u + 4 * hpl [zero, one, zero] u -
    8 * hpl [zero, negOne, zero] u + 4 * hpl [one, zero, zero] u + 8 * hpl [one, one, zero] u -
    16 * hpl [one, negOne, zero] u - 8 * hpl [negOne, zero, zero] u -
    16 * hpl [negOne, one, zero] u + 32 * hpl [negOne, negOne, zero] u

/-- **The inner integral `h₃(u)` of `A₂₃,₃`**, in harmonic polylogarithms. -/
noncomputable def i15H3 (u : ℝ) : ℝ :=
  (1 / u - u) * i15H3S u + (1 - u) * (8 * hpl [zero, one, zero] u -
      16 * hpl [zero, negOne, zero] u) +
    ((2 * π ^ 2 / 3 - 12 * zeta3 - 16) + (8 - π ^ 2 / 3) * hpl [zero] u +
      4 * hpl [zero, zero] u + 2 * hpl [zero, zero, zero] u) +
    u * ((14 * zeta3 - π ^ 2 / 3 + 8) + (π ^ 2 / 2 - 12) * hpl [zero] u -
      6 * hpl [zero, zero] u - 3 * hpl [zero, zero, zero] u)

/-- The terms `(qₜ, wₜ)` of the primitive of `h₃`, `qₜ = (a, b, c, d) ↦ a/u + b + c u + d u²`. -/
noncomputable def i15H3L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter) :=
  [((0, 0, π ^ 2 - 12 * zeta3 - 15, -7 * π ^ 2 / 24 + 7 * zeta3 + 175 / 16), []),
   ((0, 0, -π ^ 2 / 3 - 1, π ^ 2 / 4 - 111 / 8), [zero]),
   ((0, 0, 4, -21 / 4), [zero, zero]),
   ((0, 11, -4, -7), [one, zero]),
   ((0, -6, 8, 14), [negOne, zero]),
   ((0, 0, 2, -3 / 2), [zero, zero, zero]),
   ((0, 8, 8, -6), [zero, one, zero]),
   ((0, -16, -16, 12), [zero, negOne, zero]),
   ((0, 2, 0, -2), [one, zero, zero]),
   ((0, 4, 0, -4), [one, one, zero]),
   ((0, -8, 0, 8), [one, negOne, zero]),
   ((0, -4, 0, 4), [negOne, zero, zero]),
   ((0, -8, 0, 8), [negOne, one, zero]),
   ((0, 16, 0, -16), [negOne, negOne, zero]),
   ((0, 4, 0, 0), [zero, zero, one, zero]),
   ((0, -8, 0, 0), [zero, zero, negOne, zero]),
   ((0, 4, 0, 0), [zero, one, zero, zero]),
   ((0, 8, 0, 0), [zero, one, one, zero]),
   ((0, -16, 0, 0), [zero, one, negOne, zero]),
   ((0, -8, 0, 0), [zero, negOne, zero, zero]),
   ((0, -16, 0, 0), [zero, negOne, one, zero]),
   ((0, 32, 0, 0), [zero, negOne, negOne, zero])]

/-- The primitive of `h₃`. -/
noncomputable def i15H3Phi (u : ℝ) : ℝ := i15T3Sum i15H3L u

theorem hasDerivAt_i15H3Phi {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i15H3Phi (i15H3 u) u := by
  have h := hasDerivAt_i15T3Sum i15H3L hu
  refine h.congr_deriv ?_
  have hu0 : u ≠ 0 := hu.1.ne'
  have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
  have hu2 : 1 + u ≠ 0 := by linarith [hu.1]
  simp only [i15H3L, i15T3SumD_cons, i15T3SumD_nil, i15T3q, i15T3q', i15T3hd,
    Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne, hpl_nil]
  unfold i15H3 i15H3S
  field_simp
  ring

theorem tendsto_i15H3Phi_zero : Tendsto i15H3Phi (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_i15T3Sum_zero ?_
  simp [i15H3L]

theorem i15H3L_value :
    (i15H3L.map fun t => i15T3q t.1 1 * hpl t.2 1).sum = 5 * zeta3 - 5 * π ^ 2 / 8 - 65 / 16 := by
  simp only [i15H3L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, i15T3q,
    hpl_nil, hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_negOne_zero_at_one, hpl_zero_one_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_negOne_zero_zero_at_one, hpl_negOne_one_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_zero_zero_one_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_one_zero_zero_at_one, hpl_zero_one_one_zero_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_negOne_negOne_zero_at_one]
  ring

theorem tendsto_i15H3Phi_one :
    Tendsto i15H3Phi (𝓝[<] 1) (𝓝 (5 * zeta3 - 5 * π ^ 2 / 8 - 65 / 16)) := by
  rw [← i15H3L_value]
  refine tendsto_i15T3Sum_one ?_
  simp [i15H3L, i15T3q]
  norm_num

/-- **`∫₀¹ h₃ = 5 ζ(3) - 5π²/8 - 65/16`**, given the integrability of `h₃`. -/
theorem integral_i15H3 (hI : IntervalIntegrable i15H3 volume 0 1) :
    ∫ u in (0 : ℝ)..1, i15H3 u = 5 * zeta3 - 5 * π ^ 2 / 8 - 65 / 16 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun u hu => hasDerivAt_i15H3Phi hu) hI tendsto_i15H3Phi_zero tendsto_i15H3Phi_one,
    sub_zero]

end QED.ThreeLoopD
