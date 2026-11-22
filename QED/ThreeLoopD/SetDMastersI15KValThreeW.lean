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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₅`: the outer integral of the `c`-weighted half of `F₃`

In the coordinate `r = x / (1 - x) ∈ (0, 1)` (the half `x < 1/2`, doubled by `x ↦ 1 - x`),
`dx / c = dr / r` and `∫∫ A₁,₃ = (1/3) ∫₀¹ W₃(r) dr / r` with
`W₃(r) = ∫₀¹ (b₁³ - b₂³) du`, `b₁ = log r + log u + 2 log (1 + r) - 2 log (r + u)
- 2 log (1 + r u)`, `b₂ = log r - 2 log (1 + r) - log u`. Numerically to 370 digits
(`setDI15e/fit.py`), `W₃` is the HPL combination `QED.ThreeLoopD.i15W3` (coefficients
`1/r, 1, r`, words of weight `≤ 3` over `{0, 1, -1}`).

This file gives the explicit primitive `Φ = Σ qₜ(r) H(wₜ; r)` of `W₃ / r` (with `qₜ` having a
`1/r` part) and its limit `42 π² + 168 ζ(3) - 48 π² log 2` at `1⁻`. At `0⁺` the terms of `Φ`
diverge individually (`H(w; r)/r` and `log r`); numerically (`setDI15e/phi0.py`) `Φ → 300`,
which is taken as a hypothesis here. Granting it,
`∫₀¹ W₃ / r = 3 (14 π² + 56 ζ(3) - 16 π² log 2 - 100)`, the expected value of `3 ∫∫ A₁,₃`.
Neither `∫₀¹ (b₁³ - b₂³) du = W₃(r)` nor the limit at `0⁺` is proved here.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i15W3Phi`: the primitive.
* `QED.ThreeLoopD.tendsto_i15W3Phi_one`: its limit at `1⁻`.
* `QED.ThreeLoopD.integral_i15W3_of_tendsto`: the integral, given the limit `300` at `0⁺`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- **The inner integral `W₃(r)` of `A₁,₃`** (in `r = x/(1 - x)`), in harmonic polylogarithms. -/
noncomputable def i15W3 (r : ℝ) : ℝ :=
  r⁻¹ * (-4 * π ^ 2 * hpl [one] r + (4 * π ^ 2 - 108) * hpl [negOne] r -
      72 * hpl [zero, negOne] r - 72 * hpl [one, zero] r + 36 * hpl [negOne, zero] r -
      48 * hpl [zero, zero, negOne] r - 48 * hpl [zero, one, zero] r +
      24 * hpl [zero, negOne, zero] r - 24 * hpl [one, zero, zero] r -
      96 * hpl [one, zero, negOne] r - 96 * hpl [one, one, zero] r +
      48 * hpl [one, negOne, zero] r + 12 * hpl [negOne, zero, zero] r +
      72 * hpl [negOne, zero, negOne] r + 48 * hpl [negOne, one, zero] r -
      48 * hpl [negOne, negOne, negOne] r) +
    (156 + 48 * hpl [zero] r - 96 * hpl [negOne] r + 12 * hpl [zero, zero] r -
      24 * hpl [zero, negOne] r - 24 * hpl [negOne, zero] r + 48 * hpl [negOne, negOne] r) +
    r * ((6 * π ^ 2 - 24 * zeta3) + 108 * hpl [zero] r + 4 * π ^ 2 * hpl [one] r -
      108 * hpl [negOne] r + 36 * hpl [zero, zero] r + 72 * hpl [zero, negOne] r +
      72 * hpl [one, zero] r - 36 * hpl [negOne, zero] r + 12 * hpl [zero, zero, zero] r +
      72 * hpl [zero, zero, negOne] r + 96 * hpl [zero, one, zero] r -
      72 * hpl [zero, negOne, zero] r + 48 * hpl [zero, negOne, negOne] r +
      24 * hpl [one, zero, zero] r + 96 * hpl [one, zero, negOne] r +
      96 * hpl [one, one, zero] r - 48 * hpl [one, negOne, zero] r -
      12 * hpl [negOne, zero, zero] r - 24 * hpl [negOne, zero, negOne] r -
      48 * hpl [negOne, one, zero] r + 48 * hpl [negOne, negOne, zero] r -
      48 * hpl [negOne, negOne, negOne] r)

/-- The terms `(qₜ, wₜ)` of the primitive of `W₃ / r`. -/
noncomputable def i15W3L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter) :=
  [((0, 0, 10 * π ^ 2 - 24 * zeta3, 0), []),
   ((0, -72, 228, 0), [zero]),
   ((4 * π ^ 2, -8 * π ^ 2, 4 * π ^ 2, 0), [one]),
   ((228 - 4 * π ^ 2, -4 * π ^ 2, -228, 0), [negOne]),
   ((0, -12, 60, 0), [zero, zero]),
   ((120, -96, 120, 0), [zero, negOne]),
   ((120, -240, 120, 0), [one, zero]),
   ((-60, -120, -60, 0), [negOne, zero]),
   ((0, 0, 12, 0), [zero, zero, zero]),
   ((48, -48, 72, 0), [zero, zero, negOne]),
   ((48, -48, 96, 0), [zero, one, zero]),
   ((-24, 24, -72, 0), [zero, negOne, zero]),
   ((0, 0, 48, 0), [zero, negOne, negOne]),
   ((24, -48, 24, 0), [one, zero, zero]),
   ((96, -192, 96, 0), [one, zero, negOne]),
   ((96, -192, 96, 0), [one, one, zero]),
   ((-48, 96, -48, 0), [one, negOne, zero]),
   ((-12, -24, -12, 0), [negOne, zero, zero]),
   ((-72, -96, -24, 0), [negOne, zero, negOne]),
   ((-48, -96, -48, 0), [negOne, one, zero]),
   ((0, 48, 48, 0), [negOne, negOne, zero]),
   ((48, 0, -48, 0), [negOne, negOne, negOne])]

/-- The primitive of `W₃ / r`. -/
noncomputable def i15W3Phi (r : ℝ) : ℝ := i15T3Sum i15W3L r

theorem hasDerivAt_i15W3Phi {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i15W3Phi (i15W3 r / r) r := by
  have h := hasDerivAt_i15T3Sum i15W3L hr
  refine h.congr_deriv ?_
  have hr0 : r ≠ 0 := hr.1.ne'
  have hr1 : 1 - r ≠ 0 := by linarith [hr.2]
  have hr2 : 1 + r ≠ 0 := by linarith [hr.1]
  simp only [i15W3L, i15T3SumD_cons, i15T3SumD_nil, i15T3q, i15T3q', i15T3hd,
    Letter.kernel_zero, Letter.kernel_one, Letter.kernel_negOne, hpl_nil]
  unfold i15W3
  field_simp
  ring

theorem i15W3L_value :
    (i15W3L.map fun t => i15T3q t.1 1 * hpl t.2 1).sum =
      42 * π ^ 2 + 168 * zeta3 - 48 * π ^ 2 * log 2 := by
  simp only [i15W3L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, i15T3q,
    hpl_nil, hpl_zero_at_one, hpl_zero_zero_at_one, hpl_zero_zero_zero_at_one,
    hpl_negOne_at_one, hpl_zero_negOne_at_one, hpl_negOne_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_one_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_negOne_at_one, hpl_negOne_zero_zero_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_negOne_one_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_negOne_at_one]
  ring

theorem tendsto_i15W3Phi_one :
    Tendsto i15W3Phi (𝓝[<] 1) (𝓝 (42 * π ^ 2 + 168 * zeta3 - 48 * π ^ 2 * log 2)) := by
  rw [← i15W3L_value]
  refine tendsto_i15T3Sum_one ?_
  simp [i15W3L, i15T3q]
  ring_nf
  simp

/-- **`∫₀¹ W₃ / r = 3 (14 π² + 56 ζ(3) - 16 π² log 2 - 100)`**, given the integrability of
`W₃ / r` and the limit `300` of the primitive at `0⁺`. -/
theorem integral_i15W3_of_tendsto (hI : IntervalIntegrable (fun r => i15W3 r / r) volume 0 1)
    (h0 : Tendsto i15W3Phi (𝓝[>] 0) (𝓝 300)) :
    ∫ r in (0 : ℝ)..1, i15W3 r / r =
      3 * (14 * π ^ 2 + 56 * zeta3 - 16 * π ^ 2 * log 2 - 100) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun r hr => hasDerivAt_i15W3Phi hr) hI h0 tendsto_i15W3Phi_one]
  ring

end QED.ThreeLoopD
