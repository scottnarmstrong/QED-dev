/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import QED.Polylog.HPLBasic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.Polylog.HPLCalculus
import QED.Polylog.HPLValues
import QED.Polylog.HPLValues3
import QED.Polylog.HPLValues4
import QED.Polylog.HPLValuesAlt4
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Set (d), master `I₉`: the outer `w`-integral of the third Taylor coefficient

Write `λ = log w`, `ζ₂ = π²/6` and `H(v) = H(v; w)` (harmonic polylogarithms, `m = -1`). The
outer integrand of the third Taylor coefficient is

  `G = (1 + w)²/w · K + (1 + w)(9w + 1)/w · (18 H(0,0,m) - 12 H(0,0,1))
      + (1 + w)(3λw - λ - 2w - 2)/w · (12 H(0,1) - 18 H(0,m))
      + (1 + w)(7λ³ + 18λ² + 24λ + 12ζ₂ - 48ζ₃)`,

  `K = -108 (H(0,m,m) + H(m,0,m)) - 48 (H(0,1,1) + H(1,0,1))
      + 72 (H(0,1,m) + H(0,m,1) + H(1,0,m) + H(m,0,1)) - 72λ (H(1,m) + H(m,1))
      + 48λ H(1,1) + 108λ H(m,m) + (3λ² + 4λ + 2ζ₂)(6 H(1) - 9 H(m))`

(`QED.ThreeLoopD.i9M3O`). It has the explicit antiderivative `Φ = QED.ThreeLoopD.i9M3Phi` on
`(0, 1)`, a sum of 46 terms `p(w) λᵏ H(v)` with `p` of degree at most two. Each word `v` either
does not start with `1`, so that `H(v)` has a finite value at `1`, or its coefficient `p`
vanishes at `w = 1`. Hence `Φ(0⁺) = 0` and

  `Φ(1⁻) = -621/2 + 235π²/4 + 147 ζ₃ - π⁴/12 - 72 π² log 2`,

using the values of the harmonic polylogarithms of weight at most four at `1`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i9M3Phi`: `Φ' = G` on `(0, 1)`;
* `QED.ThreeLoopD.tendsto_i9M3Phi_zero`, `QED.ThreeLoopD.tendsto_i9M3Phi_one`: the limits;
* `QED.ThreeLoopD.integral_i9M3O`: `∫₀¹ G = Φ(1⁻) - Φ(0⁺)`, for integrable `G`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The outer integrand `G` of the third Taylor coefficient of `I₉` (see the module docstring). -/
noncomputable def i9M3O (w : ℝ) : ℝ :=
  (1 + w) ^ 2 / w *
      (-108 * (hpl [zero, negOne, negOne] w + hpl [negOne, zero, negOne] w)
        - 48 * (hpl [zero, one, one] w + hpl [one, zero, one] w)
        + 72 * (hpl [zero, one, negOne] w + hpl [zero, negOne, one] w
          + hpl [one, zero, negOne] w + hpl [negOne, zero, one] w)
        - 72 * Real.log w * (hpl [one, negOne] w + hpl [negOne, one] w)
        + 48 * Real.log w * hpl [one, one] w + 108 * Real.log w * hpl [negOne, negOne] w
        + (3 * Real.log w ^ 2 + 4 * Real.log w + 2 * (π ^ 2 / 6))
          * (6 * hpl [one] w - 9 * hpl [negOne] w))
    + (1 + w) * (9 * w + 1) / w * (18 * hpl [zero, zero, negOne] w - 12 * hpl [zero, zero, one] w)
    + (1 + w) * (3 * Real.log w * w - Real.log w - 2 * w - 2) / w
      * (12 * hpl [zero, one] w - 18 * hpl [zero, negOne] w)
    + (1 + w) * (7 * Real.log w ^ 3 + 18 * Real.log w ^ 2 + 24 * Real.log w + 12 * (π ^ 2 / 6)
      - 48 * zeta3)

/-- The antiderivative `Φ` of `QED.ThreeLoopD.i9M3O` on `(0, 1)`. -/
noncomputable def i9M3Phi (w : ℝ) : ℝ :=
  (3*w*(9*w*(π ^ 2 / 6) - 16*w*zeta3 - 9*w + 46*(π ^ 2 / 6) - 32*zeta3 - 198)/2) +
    (27*w*(w + 11)) * Real.log w +
    (15*w*(2*w + 11)/2) * Real.log w ^ 2 +
    (7*w*(w + 2)/2) * Real.log w ^ 3 +
    (-9*(π ^ 2 / 6)*(w + 1)*(w + 3)) * hpl [negOne] w +
    (-18*(w + 1)*(2*w + 13)) * Real.log w * hpl [negOne] w +
    (-27*(w + 1)*(w + 3)/2) * Real.log w ^ 2 * hpl [negOne] w +
    (6*(π ^ 2 / 6)*(w - 1)*(w + 5)) * hpl [one] w +
    (12*(w - 1)*(2*w + 17)) * Real.log w * hpl [one] w +
    (9*(w - 1)*(w + 5)) * Real.log w ^ 2 * hpl [one] w +
    (54*(w + 1)*(w + 3)) * Real.log w * hpl [negOne, negOne] w +
    (-36*(w + 1)*(w + 3)) * Real.log w * hpl [negOne, one] w +
    (-18*(-2*w ^ 2 - 15*w + (π ^ 2 / 6) - 13)) * hpl [zero, negOne] w +
    (-9*(3*w ^ 2 + 4*w - 5)) * Real.log w * hpl [zero, negOne] w +
    (-27) * Real.log w ^ 2 * hpl [zero, negOne] w +
    (12*(-2*w ^ 2 - 15*w + (π ^ 2 / 6) + 17)) * hpl [zero, one] w +
    (6*(3*w ^ 2 + 4*w + 19)) * Real.log w * hpl [zero, one] w +
    (18) * Real.log w ^ 2 * hpl [zero, one] w +
    (-36*(w - 1)*(w + 5)) * Real.log w * hpl [one, negOne] w +
    (24*(w - 1)*(w + 5)) * Real.log w * hpl [one, one] w +
    (-54*(w + 1)*(w + 3)) * hpl [negOne, zero, negOne] w +
    (36*(w + 1)*(w + 3)) * hpl [negOne, zero, one] w +
    (-54*(w + 1)*(w + 3)) * hpl [zero, negOne, negOne] w +
    (108) * Real.log w * hpl [zero, negOne, negOne] w +
    (36*(w + 1)*(w + 3)) * hpl [zero, negOne, one] w +
    (-72) * Real.log w * hpl [zero, negOne, one] w +
    (9*(9*w ^ 2 + 20*w - 1)) * hpl [zero, zero, negOne] w +
    (72) * Real.log w * hpl [zero, zero, negOne] w +
    (-6*(9*w ^ 2 + 20*w + 23)) * hpl [zero, zero, one] w +
    (-48) * Real.log w * hpl [zero, zero, one] w +
    (36*(w - 1)*(w + 5)) * hpl [zero, one, negOne] w +
    (-72) * Real.log w * hpl [zero, one, negOne] w +
    (-24*(w - 1)*(w + 5)) * hpl [zero, one, one] w +
    (48) * Real.log w * hpl [zero, one, one] w +
    (36*(w - 1)*(w + 5)) * hpl [one, zero, negOne] w +
    (-24*(w - 1)*(w + 5)) * hpl [one, zero, one] w +
    (-108) * hpl [zero, negOne, zero, negOne] w +
    (72) * hpl [zero, negOne, zero, one] w +
    (-216) * hpl [zero, zero, negOne, negOne] w +
    (144) * hpl [zero, zero, negOne, one] w +
    (-54) * hpl [zero, zero, zero, negOne] w +
    (36) * hpl [zero, zero, zero, one] w +
    (144) * hpl [zero, zero, one, negOne] w +
    (-96) * hpl [zero, zero, one, one] w +
    (72) * hpl [zero, one, zero, negOne] w +
    (-48) * hpl [zero, one, zero, one] w

/-- A single term `(a + b w + c w²) λᵏ H(v)` of `Φ`. -/
noncomputable def i9M3PhiT (a b c : ℝ) (k : ℕ) (v : List Letter) (w : ℝ) : ℝ :=
  (a + b * w + c * w ^ 2) * Real.log w ^ k * hpl v w

/-- `Φ` as a sum of the terms `QED.ThreeLoopD.i9M3PhiT`. -/
theorem i9M3Phi_eq_sum : i9M3Phi = fun w =>
    i9M3PhiT 0 (69 * (π ^ 2 / 6) - 48 * zeta3 - 297) (27 * (π ^ 2 / 6) / 2 - 24 * zeta3 - 27 / 2) 0
      [] w +
    i9M3PhiT 0 297 27 1 [] w +
    i9M3PhiT 0 (165 / 2) 15 2 [] w +
    i9M3PhiT 0 7 (7 / 2) 3 [] w +
    i9M3PhiT (-27 * (π ^ 2 / 6)) (-36 * (π ^ 2 / 6)) (-9 * (π ^ 2 / 6)) 0 [negOne] w +
    i9M3PhiT (-234) (-270) (-36) 1 [negOne] w +
    i9M3PhiT (-81 / 2) (-54) (-27 / 2) 2 [negOne] w +
    i9M3PhiT (-30 * (π ^ 2 / 6)) (24 * (π ^ 2 / 6)) (6 * (π ^ 2 / 6)) 0 [one] w +
    i9M3PhiT (-204) 180 24 1 [one] w +
    i9M3PhiT (-45) 36 9 2 [one] w +
    i9M3PhiT 162 216 54 1 [negOne, negOne] w +
    i9M3PhiT (-108) (-144) (-36) 1 [negOne, one] w +
    i9M3PhiT (234 - 18 * (π ^ 2 / 6)) 270 36 0 [zero, negOne] w +
    i9M3PhiT 45 (-36) (-27) 1 [zero, negOne] w +
    i9M3PhiT (-27) 0 0 2 [zero, negOne] w +
    i9M3PhiT (12 * (π ^ 2 / 6) + 204) (-180) (-24) 0 [zero, one] w +
    i9M3PhiT 114 24 18 1 [zero, one] w +
    i9M3PhiT 18 0 0 2 [zero, one] w +
    i9M3PhiT 180 (-144) (-36) 1 [one, negOne] w +
    i9M3PhiT (-120) 96 24 1 [one, one] w +
    i9M3PhiT (-162) (-216) (-54) 0 [negOne, zero, negOne] w +
    i9M3PhiT 108 144 36 0 [negOne, zero, one] w +
    i9M3PhiT (-162) (-216) (-54) 0 [zero, negOne, negOne] w +
    i9M3PhiT 108 0 0 1 [zero, negOne, negOne] w +
    i9M3PhiT 108 144 36 0 [zero, negOne, one] w +
    i9M3PhiT (-72) 0 0 1 [zero, negOne, one] w +
    i9M3PhiT (-9) 180 81 0 [zero, zero, negOne] w +
    i9M3PhiT 72 0 0 1 [zero, zero, negOne] w +
    i9M3PhiT (-138) (-120) (-54) 0 [zero, zero, one] w +
    i9M3PhiT (-48) 0 0 1 [zero, zero, one] w +
    i9M3PhiT (-180) 144 36 0 [zero, one, negOne] w +
    i9M3PhiT (-72) 0 0 1 [zero, one, negOne] w +
    i9M3PhiT 120 (-96) (-24) 0 [zero, one, one] w +
    i9M3PhiT 48 0 0 1 [zero, one, one] w +
    i9M3PhiT (-180) 144 36 0 [one, zero, negOne] w +
    i9M3PhiT 120 (-96) (-24) 0 [one, zero, one] w +
    i9M3PhiT (-108) 0 0 0 [zero, negOne, zero, negOne] w +
    i9M3PhiT 72 0 0 0 [zero, negOne, zero, one] w +
    i9M3PhiT (-216) 0 0 0 [zero, zero, negOne, negOne] w +
    i9M3PhiT 144 0 0 0 [zero, zero, negOne, one] w +
    i9M3PhiT (-54) 0 0 0 [zero, zero, zero, negOne] w +
    i9M3PhiT 36 0 0 0 [zero, zero, zero, one] w +
    i9M3PhiT 144 0 0 0 [zero, zero, one, negOne] w +
    i9M3PhiT (-96) 0 0 0 [zero, zero, one, one] w +
    i9M3PhiT 72 0 0 0 [zero, one, zero, negOne] w +
    i9M3PhiT (-48) 0 0 0 [zero, one, zero, one] w
  := by
  funext w
  simp only [i9M3Phi, i9M3PhiT, hpl_nil]
  ring

/-! ### The derivative -/

theorem hasDerivAt_i9M3PhiT (a b c : ℝ) {k : ℕ} {v : List Letter} {L' H' w : ℝ}
    (hl : HasDerivAt (fun x => Real.log x ^ k) L' w) (hh : HasDerivAt (hpl v) H' w) :
    HasDerivAt (i9M3PhiT a b c k v)
      (((b + 2 * c * w) * Real.log w ^ k + (a + b * w + c * w ^ 2) * L') * hpl v w
        + (a + b * w + c * w ^ 2) * Real.log w ^ k * H') w := by
  have hp : HasDerivAt (fun x => a + b * x + c * x ^ 2) (b + 2 * c * w) w := by
    have := (((hasDerivAt_id' w).const_mul b).const_add a).add
      ((hasDerivAt_pow 2 w).const_mul c)
    exact this.congr_deriv (by norm_num; ring)
  exact (hp.mul hl).mul hh

theorem hasDerivAt_i9M3_hpl_nil (w : ℝ) : HasDerivAt (hpl []) 0 w := by
  rw [show hpl [] = fun _ => (1 : ℝ) from funext hpl_nil]
  exact hasDerivAt_const w 1

/-- `Φ' = G` on `(0, 1)`. -/
theorem hasDerivAt_i9M3Phi {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i9M3Phi (i9M3O w) w := by
  have w0 : w ≠ 0 := hw.1.ne'
  have w1 : 1 - w ≠ 0 := by linarith [hw.2]
  have w2 : 1 + w ≠ 0 := by linarith [hw.1]
  have l0 : HasDerivAt (fun x => Real.log x ^ 0) 0 w := by
    simpa using hasDerivAt_const w (1 : ℝ)
  have l1 : HasDerivAt (fun x => Real.log x ^ 1) w⁻¹ w := by
    simpa using hasDerivAt_log w0
  have l2 : HasDerivAt (fun x => Real.log x ^ 2) (2 * Real.log w * w⁻¹) w := by
    convert (hasDerivAt_log w0).pow 2 using 1
    norm_num
  have l3 : HasDerivAt (fun x => Real.log x ^ 3) (3 * Real.log w ^ 2 * w⁻¹) w := by
    convert (hasDerivAt_log w0).pow 3 using 1
  have t0 := hasDerivAt_i9M3PhiT 0 (69 * (π ^ 2 / 6) - 48 * zeta3 - 297)
      (27 * (π ^ 2 / 6) / 2 - 24 * zeta3 - 27 / 2) l0 (hasDerivAt_i9M3_hpl_nil w)
  have t1 := hasDerivAt_i9M3PhiT 0 297 27 l1 (hasDerivAt_i9M3_hpl_nil w)
  have t2 := hasDerivAt_i9M3PhiT 0 (165 / 2) 15 l2 (hasDerivAt_i9M3_hpl_nil w)
  have t3 := hasDerivAt_i9M3PhiT 0 7 (7 / 2) l3 (hasDerivAt_i9M3_hpl_nil w)
  have t4 := hasDerivAt_i9M3PhiT (-27 * (π ^ 2 / 6)) (-36 * (π ^ 2 / 6)) (-9 * (π ^ 2 / 6)) l0
      (hasDerivAt_hpl_cons negOne [] hw)
  have t5 := hasDerivAt_i9M3PhiT (-234) (-270) (-36) l1 (hasDerivAt_hpl_cons negOne [] hw)
  have t6 := hasDerivAt_i9M3PhiT (-81 / 2) (-54) (-27 / 2) l2 (hasDerivAt_hpl_cons negOne [] hw)
  have t7 := hasDerivAt_i9M3PhiT (-30 * (π ^ 2 / 6)) (24 * (π ^ 2 / 6)) (6 * (π ^ 2 / 6)) l0
      (hasDerivAt_hpl_cons one [] hw)
  have t8 := hasDerivAt_i9M3PhiT (-204) 180 24 l1 (hasDerivAt_hpl_cons one [] hw)
  have t9 := hasDerivAt_i9M3PhiT (-45) 36 9 l2 (hasDerivAt_hpl_cons one [] hw)
  have t10 := hasDerivAt_i9M3PhiT 162 216 54 l1 (hasDerivAt_hpl_cons negOne [negOne] hw)
  have t11 := hasDerivAt_i9M3PhiT (-108) (-144) (-36) l1 (hasDerivAt_hpl_cons negOne [one] hw)
  have t12 := hasDerivAt_i9M3PhiT (234 - 18 * (π ^ 2 / 6)) 270 36 l0
      (hasDerivAt_hpl_cons zero [negOne] hw)
  have t13 := hasDerivAt_i9M3PhiT 45 (-36) (-27) l1 (hasDerivAt_hpl_cons zero [negOne] hw)
  have t14 := hasDerivAt_i9M3PhiT (-27) 0 0 l2 (hasDerivAt_hpl_cons zero [negOne] hw)
  have t15 := hasDerivAt_i9M3PhiT (12 * (π ^ 2 / 6) + 204) (-180) (-24) l0
      (hasDerivAt_hpl_cons zero [one] hw)
  have t16 := hasDerivAt_i9M3PhiT 114 24 18 l1 (hasDerivAt_hpl_cons zero [one] hw)
  have t17 := hasDerivAt_i9M3PhiT 18 0 0 l2 (hasDerivAt_hpl_cons zero [one] hw)
  have t18 := hasDerivAt_i9M3PhiT 180 (-144) (-36) l1 (hasDerivAt_hpl_cons one [negOne] hw)
  have t19 := hasDerivAt_i9M3PhiT (-120) 96 24 l1 (hasDerivAt_hpl_cons one [one] hw)
  have t20 := hasDerivAt_i9M3PhiT (-162) (-216) (-54) l0
      (hasDerivAt_hpl_cons negOne [zero, negOne] hw)
  have t21 := hasDerivAt_i9M3PhiT 108 144 36 l0 (hasDerivAt_hpl_cons negOne [zero, one] hw)
  have t22 := hasDerivAt_i9M3PhiT (-162) (-216) (-54) l0
      (hasDerivAt_hpl_cons zero [negOne, negOne] hw)
  have t23 := hasDerivAt_i9M3PhiT 108 0 0 l1 (hasDerivAt_hpl_cons zero [negOne, negOne] hw)
  have t24 := hasDerivAt_i9M3PhiT 108 144 36 l0 (hasDerivAt_hpl_cons zero [negOne, one] hw)
  have t25 := hasDerivAt_i9M3PhiT (-72) 0 0 l1 (hasDerivAt_hpl_cons zero [negOne, one] hw)
  have t26 := hasDerivAt_i9M3PhiT (-9) 180 81 l0 (hasDerivAt_hpl_cons zero [zero, negOne] hw)
  have t27 := hasDerivAt_i9M3PhiT 72 0 0 l1 (hasDerivAt_hpl_cons zero [zero, negOne] hw)
  have t28 := hasDerivAt_i9M3PhiT (-138) (-120) (-54) l0 (hasDerivAt_hpl_cons zero [zero, one] hw)
  have t29 := hasDerivAt_i9M3PhiT (-48) 0 0 l1 (hasDerivAt_hpl_cons zero [zero, one] hw)
  have t30 := hasDerivAt_i9M3PhiT (-180) 144 36 l0 (hasDerivAt_hpl_cons zero [one, negOne] hw)
  have t31 := hasDerivAt_i9M3PhiT (-72) 0 0 l1 (hasDerivAt_hpl_cons zero [one, negOne] hw)
  have t32 := hasDerivAt_i9M3PhiT 120 (-96) (-24) l0 (hasDerivAt_hpl_cons zero [one, one] hw)
  have t33 := hasDerivAt_i9M3PhiT 48 0 0 l1 (hasDerivAt_hpl_cons zero [one, one] hw)
  have t34 := hasDerivAt_i9M3PhiT (-180) 144 36 l0 (hasDerivAt_hpl_cons one [zero, negOne] hw)
  have t35 := hasDerivAt_i9M3PhiT 120 (-96) (-24) l0 (hasDerivAt_hpl_cons one [zero, one] hw)
  have t36 := hasDerivAt_i9M3PhiT (-108) 0 0 l0 (hasDerivAt_hpl_cons zero [negOne, zero, negOne] hw)
  have t37 := hasDerivAt_i9M3PhiT 72 0 0 l0 (hasDerivAt_hpl_cons zero [negOne, zero, one] hw)
  have t38 := hasDerivAt_i9M3PhiT (-216) 0 0 l0 (hasDerivAt_hpl_cons zero [zero, negOne, negOne] hw)
  have t39 := hasDerivAt_i9M3PhiT 144 0 0 l0 (hasDerivAt_hpl_cons zero [zero, negOne, one] hw)
  have t40 := hasDerivAt_i9M3PhiT (-54) 0 0 l0 (hasDerivAt_hpl_cons zero [zero, zero, negOne] hw)
  have t41 := hasDerivAt_i9M3PhiT 36 0 0 l0 (hasDerivAt_hpl_cons zero [zero, zero, one] hw)
  have t42 := hasDerivAt_i9M3PhiT 144 0 0 l0 (hasDerivAt_hpl_cons zero [zero, one, negOne] hw)
  have t43 := hasDerivAt_i9M3PhiT (-96) 0 0 l0 (hasDerivAt_hpl_cons zero [zero, one, one] hw)
  have t44 := hasDerivAt_i9M3PhiT 72 0 0 l0 (hasDerivAt_hpl_cons zero [one, zero, negOne] hw)
  have t45 := hasDerivAt_i9M3PhiT (-48) 0 0 l0 (hasDerivAt_hpl_cons zero [one, zero, one] hw)
  have h := t0.add t1 |>.add t2 |>.add t3 |>.add t4 |>.add t5 |>.add t6 |>.add t7 |>.add t8
    |>.add t9 |>.add t10 |>.add t11 |>.add t12 |>.add t13 |>.add t14 |>.add t15 |>.add t16
    |>.add t17 |>.add t18 |>.add t19 |>.add t20 |>.add t21 |>.add t22 |>.add t23 |>.add t24
    |>.add t25 |>.add t26 |>.add t27 |>.add t28 |>.add t29 |>.add t30 |>.add t31 |>.add t32
    |>.add t33 |>.add t34 |>.add t35 |>.add t36 |>.add t37 |>.add t38 |>.add t39 |>.add t40
    |>.add t41 |>.add t42 |>.add t43 |>.add t44 |>.add t45
  rw [i9M3Phi_eq_sum]
  refine h.congr_deriv ?_
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, i9M3O]
  field_simp
  ring


/-! ### The limit at `0` -/

/-- `logᵏ x · xʳ → 0` as `x → 0⁺`, for `0 < r`. -/
theorem tendsto_i9M3_log_pow_mul_rpow_zero (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => Real.log x ^ k * x ^ r) (𝓝[>] 0) (𝓝 0) := by
  cases k with
  | zero => simpa using tendsto_rpow_nhdsGT_zero hr
  | succ k =>
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := r / (k + 1)) (by positivity)).pow (k + 1)
    rw [zero_pow (Nat.succ_ne_zero k)] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [mul_pow, ← rpow_natCast (x ^ (r / (k + 1))) (k + 1), ← rpow_mul (le_of_lt hx)]
    congr 2
    push_cast
    field_simp

/-- `logᵏ x · H(v; x) → 0` as `x → 0⁺`, for a word `v` that is not all zeros. -/
theorem tendsto_i9M3_log_pow_mul_hpl_zero (k : ℕ) {v : List Letter} (hv : ¬AllZero v) :
    Tendsto (fun x => Real.log x ^ k * hpl v x) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, -, h⟩ := abs_hpl_le_sqrt hv (b := 1 / 2) (by norm_num)
  have hlim : Tendsto (fun x => C * |Real.log x ^ k * x ^ (1 / 2 : ℝ)|) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_i9M3_log_pow_mul_rpow_zero k (r := 1 / 2) (by norm_num)).abs.const_mul C
    rwa [abs_zero, mul_zero] at this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (rpow_nonneg hx.1.le _)]
  calc |Real.log x ^ k| * |hpl v x| ≤ |Real.log x ^ k| * (C * x ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (h x hx) (abs_nonneg _)
    _ = C * (|Real.log x ^ k| * x ^ (1 / 2 : ℝ)) := by ring

theorem tendsto_i9M3PhiT_zero (a b c : ℝ) (k : ℕ) {v : List Letter} (hv : ¬AllZero v) :
    Tendsto (i9M3PhiT a b c k v) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => a + b * x + c * x ^ 2) (𝓝[>] 0)
      (𝓝 (a + b * 0 + c * 0 ^ 2)) :=
    ((by fun_prop : Continuous fun x : ℝ => a + b * x + c * x ^ 2).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have := hp.mul (tendsto_i9M3_log_pow_mul_hpl_zero k hv)
  rw [mul_zero] at this
  exact this.congr fun x => by simp only [i9M3PhiT]; ring

theorem tendsto_i9M3PhiT_nil_zero (b c : ℝ) (k : ℕ) :
    Tendsto (i9M3PhiT 0 b c k []) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => b + c * x) (𝓝[>] 0) (𝓝 (b + c * 0)) :=
    ((by fun_prop : Continuous fun x : ℝ => b + c * x).tendsto 0).mono_left nhdsWithin_le_nhds
  have := hp.mul (tendsto_i9M3_log_pow_mul_rpow_zero k (r := 1) one_pos)
  rw [mul_zero] at this
  exact this.congr fun x => by simp only [i9M3PhiT, hpl_nil, rpow_one]; ring

/-- `Φ(0⁺) = 0`. -/
theorem tendsto_i9M3Phi_zero : Tendsto i9M3Phi (𝓝[>] 0) (𝓝 0) := by
  have t0 := tendsto_i9M3PhiT_nil_zero (69 * (π ^ 2 / 6) - 48 * zeta3 - 297)
      (27 * (π ^ 2 / 6) / 2 - 24 * zeta3 - 27 / 2) 0
  have t1 := tendsto_i9M3PhiT_nil_zero 297 27 1
  have t2 := tendsto_i9M3PhiT_nil_zero (165 / 2) 15 2
  have t3 := tendsto_i9M3PhiT_nil_zero 7 (7 / 2) 3
  have t4 := tendsto_i9M3PhiT_zero (-27 * (π ^ 2 / 6)) (-36 * (π ^ 2 / 6)) (-9 * (π ^ 2 / 6)) 0
      (v := [negOne]) (by decide)
  have t5 := tendsto_i9M3PhiT_zero (-234) (-270) (-36) 1 (v := [negOne]) (by decide)
  have t6 := tendsto_i9M3PhiT_zero (-81 / 2) (-54) (-27 / 2) 2 (v := [negOne]) (by decide)
  have t7 := tendsto_i9M3PhiT_zero (-30 * (π ^ 2 / 6)) (24 * (π ^ 2 / 6)) (6 * (π ^ 2 / 6)) 0
      (v := [one]) (by decide)
  have t8 := tendsto_i9M3PhiT_zero (-204) 180 24 1 (v := [one]) (by decide)
  have t9 := tendsto_i9M3PhiT_zero (-45) 36 9 2 (v := [one]) (by decide)
  have t10 := tendsto_i9M3PhiT_zero 162 216 54 1 (v := [negOne, negOne]) (by decide)
  have t11 := tendsto_i9M3PhiT_zero (-108) (-144) (-36) 1 (v := [negOne, one]) (by decide)
  have t12 := tendsto_i9M3PhiT_zero (234 - 18 * (π ^ 2 / 6)) 270 36 0 (v := [zero, negOne])
      (by decide)
  have t13 := tendsto_i9M3PhiT_zero 45 (-36) (-27) 1 (v := [zero, negOne]) (by decide)
  have t14 := tendsto_i9M3PhiT_zero (-27) 0 0 2 (v := [zero, negOne]) (by decide)
  have t15 := tendsto_i9M3PhiT_zero (12 * (π ^ 2 / 6) + 204) (-180) (-24) 0 (v := [zero, one])
      (by decide)
  have t16 := tendsto_i9M3PhiT_zero 114 24 18 1 (v := [zero, one]) (by decide)
  have t17 := tendsto_i9M3PhiT_zero 18 0 0 2 (v := [zero, one]) (by decide)
  have t18 := tendsto_i9M3PhiT_zero 180 (-144) (-36) 1 (v := [one, negOne]) (by decide)
  have t19 := tendsto_i9M3PhiT_zero (-120) 96 24 1 (v := [one, one]) (by decide)
  have t20 := tendsto_i9M3PhiT_zero (-162) (-216) (-54) 0 (v := [negOne, zero, negOne]) (by decide)
  have t21 := tendsto_i9M3PhiT_zero 108 144 36 0 (v := [negOne, zero, one]) (by decide)
  have t22 := tendsto_i9M3PhiT_zero (-162) (-216) (-54) 0 (v := [zero, negOne, negOne]) (by decide)
  have t23 := tendsto_i9M3PhiT_zero 108 0 0 1 (v := [zero, negOne, negOne]) (by decide)
  have t24 := tendsto_i9M3PhiT_zero 108 144 36 0 (v := [zero, negOne, one]) (by decide)
  have t25 := tendsto_i9M3PhiT_zero (-72) 0 0 1 (v := [zero, negOne, one]) (by decide)
  have t26 := tendsto_i9M3PhiT_zero (-9) 180 81 0 (v := [zero, zero, negOne]) (by decide)
  have t27 := tendsto_i9M3PhiT_zero 72 0 0 1 (v := [zero, zero, negOne]) (by decide)
  have t28 := tendsto_i9M3PhiT_zero (-138) (-120) (-54) 0 (v := [zero, zero, one]) (by decide)
  have t29 := tendsto_i9M3PhiT_zero (-48) 0 0 1 (v := [zero, zero, one]) (by decide)
  have t30 := tendsto_i9M3PhiT_zero (-180) 144 36 0 (v := [zero, one, negOne]) (by decide)
  have t31 := tendsto_i9M3PhiT_zero (-72) 0 0 1 (v := [zero, one, negOne]) (by decide)
  have t32 := tendsto_i9M3PhiT_zero 120 (-96) (-24) 0 (v := [zero, one, one]) (by decide)
  have t33 := tendsto_i9M3PhiT_zero 48 0 0 1 (v := [zero, one, one]) (by decide)
  have t34 := tendsto_i9M3PhiT_zero (-180) 144 36 0 (v := [one, zero, negOne]) (by decide)
  have t35 := tendsto_i9M3PhiT_zero 120 (-96) (-24) 0 (v := [one, zero, one]) (by decide)
  have t36 := tendsto_i9M3PhiT_zero (-108) 0 0 0 (v := [zero, negOne, zero, negOne]) (by decide)
  have t37 := tendsto_i9M3PhiT_zero 72 0 0 0 (v := [zero, negOne, zero, one]) (by decide)
  have t38 := tendsto_i9M3PhiT_zero (-216) 0 0 0 (v := [zero, zero, negOne, negOne]) (by decide)
  have t39 := tendsto_i9M3PhiT_zero 144 0 0 0 (v := [zero, zero, negOne, one]) (by decide)
  have t40 := tendsto_i9M3PhiT_zero (-54) 0 0 0 (v := [zero, zero, zero, negOne]) (by decide)
  have t41 := tendsto_i9M3PhiT_zero 36 0 0 0 (v := [zero, zero, zero, one]) (by decide)
  have t42 := tendsto_i9M3PhiT_zero 144 0 0 0 (v := [zero, zero, one, negOne]) (by decide)
  have t43 := tendsto_i9M3PhiT_zero (-96) 0 0 0 (v := [zero, zero, one, one]) (by decide)
  have t44 := tendsto_i9M3PhiT_zero 72 0 0 0 (v := [zero, one, zero, negOne]) (by decide)
  have t45 := tendsto_i9M3PhiT_zero (-48) 0 0 0 (v := [zero, one, zero, one]) (by decide)
  have h := t0.add t1 |>.add t2 |>.add t3 |>.add t4 |>.add t5 |>.add t6 |>.add t7 |>.add t8
    |>.add t9 |>.add t10 |>.add t11 |>.add t12 |>.add t13 |>.add t14 |>.add t15 |>.add t16
    |>.add t17 |>.add t18 |>.add t19 |>.add t20 |>.add t21 |>.add t22 |>.add t23 |>.add t24
    |>.add t25 |>.add t26 |>.add t27 |>.add t28 |>.add t29 |>.add t30 |>.add t31 |>.add t32
    |>.add t33 |>.add t34 |>.add t35 |>.add t36 |>.add t37 |>.add t38 |>.add t39 |>.add t40
    |>.add t41 |>.add t42 |>.add t43 |>.add t44 |>.add t45
  rw [i9M3Phi_eq_sum]
  simpa only [add_zero] using h

/-! ### The limit at `1` -/

theorem tendsto_i9M3_poly_one (a b c : ℝ) :
    Tendsto (fun x : ℝ => a + b * x + c * x ^ 2) (𝓝[<] 1) (𝓝 (a + b + c)) := by
  have := ((by fun_prop : Continuous fun x : ℝ => a + b * x + c * x ^ 2).tendsto 1).mono_left
    (nhdsWithin_le_nhds (s := Iio 1))
  simpa using this

theorem tendsto_i9M3PhiT_one (a b c : ℝ) (k : ℕ) {l : Letter} (hl : l ≠ one)
    (t : List Letter) :
    Tendsto (i9M3PhiT a b c k (l :: t)) (𝓝[<] 1) (𝓝 ((a + b + c) * 0 ^ k * hpl (l :: t) 1)) :=
  ((tendsto_i9M3_poly_one a b c).mul (tendsto_log_one.pow k)).mul (tendsto_hpl_one hl t)

theorem tendsto_i9M3PhiT_nil_one (a b c : ℝ) (k : ℕ) :
    Tendsto (i9M3PhiT a b c k []) (𝓝[<] 1) (𝓝 ((a + b + c) * 0 ^ k)) :=
  ((tendsto_i9M3_poly_one a b c).mul (tendsto_log_one.pow k)).congr fun x => by
    simp only [i9M3PhiT, hpl_nil, mul_one]

/-- `(x - 1) H(v; x) → 0` as `x → 1⁻`, for every word `v`. -/
theorem tendsto_i9M3_sub_one_mul_hpl_one (v : List Letter) :
    Tendsto (fun x => (x - 1) * hpl v x) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨C, -, h⟩ := abs_hpl_le_one_sub_rpow v (ε := 1 / 2) (by norm_num)
  have hlim : Tendsto (fun x : ℝ => C * (1 - x) ^ (1 / 2 : ℝ)) (𝓝[<] 1) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 0) :=
      ((continuous_const.sub continuous_id).tendsto' (1 : ℝ) 0 (by norm_num)).mono_left
        nhdsWithin_le_nhds
    have := (h1.rpow_const (p := 1 / 2) (Or.inr (by norm_num))).const_mul C
    rwa [zero_rpow (by norm_num), mul_zero] at this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with x hx
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith [hx.2] : x - 1 ≤ 0), neg_sub]
  calc (1 - x) * |hpl v x| ≤ (1 - x) * (C * (1 - x) ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (h x hx) hx1.le
    _ = C * ((1 - x) ^ (1 : ℝ) * (1 - x) ^ (-(1 / 2) : ℝ)) := by rw [rpow_one]; ring
    _ = C * (1 - x) ^ (1 / 2 : ℝ) := by rw [← rpow_add hx1]; norm_num

theorem tendsto_i9M3PhiT_one_one (a b c : ℝ) (k : ℕ) (t : List Letter) (habc : a + b + c = 0) :
    Tendsto (i9M3PhiT a b c k (one :: t)) (𝓝[<] 1) (𝓝 0) := by
  have hq : Tendsto (fun x : ℝ => (b + c * (x + 1)) * Real.log x ^ k) (𝓝[<] 1)
      (𝓝 ((b + c * (1 + 1)) * 0 ^ k)) :=
    (((by fun_prop : Continuous fun x : ℝ => b + c * (x + 1)).tendsto 1).mono_left
      nhdsWithin_le_nhds).mul (tendsto_log_one.pow k)
  have := hq.mul (tendsto_i9M3_sub_one_mul_hpl_one (one :: t))
  rw [mul_zero] at this
  refine this.congr fun x => ?_
  simp only [i9M3PhiT]
  rw [show a = -b - c by linarith]
  ring

/-- `Φ(1⁻) = -621/2 + 235π²/4 + 147 ζ₃ - π⁴/12 - 72 π² log 2`. -/
theorem tendsto_i9M3Phi_one : Tendsto i9M3Phi (𝓝[<] 1)
    (𝓝 (-621 / 2 + 235 * π ^ 2 / 4 + 147 * zeta3 - π ^ 4 / 12 - 72 * π ^ 2 * Real.log 2)) := by
  have t0 := tendsto_i9M3PhiT_nil_one 0 (69 * (π ^ 2 / 6) - 48 * zeta3 - 297)
      (27 * (π ^ 2 / 6) / 2 - 24 * zeta3 - 27 / 2) 0
  have t1 := tendsto_i9M3PhiT_nil_one 0 297 27 1
  have t2 := tendsto_i9M3PhiT_nil_one 0 (165 / 2) 15 2
  have t3 := tendsto_i9M3PhiT_nil_one 0 7 (7 / 2) 3
  have t4 := tendsto_i9M3PhiT_one (-27 * (π ^ 2 / 6)) (-36 * (π ^ 2 / 6)) (-9 * (π ^ 2 / 6)) 0
      (l := negOne) (by decide) []
  have t5 := tendsto_i9M3PhiT_one (-234) (-270) (-36) 1 (l := negOne) (by decide) []
  have t6 := tendsto_i9M3PhiT_one (-81 / 2) (-54) (-27 / 2) 2 (l := negOne) (by decide) []
  have t7 := tendsto_i9M3PhiT_one_one (-30 * (π ^ 2 / 6)) (24 * (π ^ 2 / 6)) (6 * (π ^ 2 / 6)) 0 []
      (by ring)
  have t8 := tendsto_i9M3PhiT_one_one (-204) 180 24 1 [] (by ring)
  have t9 := tendsto_i9M3PhiT_one_one (-45) 36 9 2 [] (by ring)
  have t10 := tendsto_i9M3PhiT_one 162 216 54 1 (l := negOne) (by decide) [negOne]
  have t11 := tendsto_i9M3PhiT_one (-108) (-144) (-36) 1 (l := negOne) (by decide) [one]
  have t12 := tendsto_i9M3PhiT_one (234 - 18 * (π ^ 2 / 6)) 270 36 0 (l := zero) (by decide)
      [negOne]
  have t13 := tendsto_i9M3PhiT_one 45 (-36) (-27) 1 (l := zero) (by decide) [negOne]
  have t14 := tendsto_i9M3PhiT_one (-27) 0 0 2 (l := zero) (by decide) [negOne]
  have t15 := tendsto_i9M3PhiT_one (12 * (π ^ 2 / 6) + 204) (-180) (-24) 0 (l := zero) (by decide)
      [one]
  have t16 := tendsto_i9M3PhiT_one 114 24 18 1 (l := zero) (by decide) [one]
  have t17 := tendsto_i9M3PhiT_one 18 0 0 2 (l := zero) (by decide) [one]
  have t18 := tendsto_i9M3PhiT_one_one 180 (-144) (-36) 1 [negOne] (by ring)
  have t19 := tendsto_i9M3PhiT_one_one (-120) 96 24 1 [one] (by ring)
  have t20 := tendsto_i9M3PhiT_one (-162) (-216) (-54) 0 (l := negOne) (by decide) [zero, negOne]
  have t21 := tendsto_i9M3PhiT_one 108 144 36 0 (l := negOne) (by decide) [zero, one]
  have t22 := tendsto_i9M3PhiT_one (-162) (-216) (-54) 0 (l := zero) (by decide) [negOne, negOne]
  have t23 := tendsto_i9M3PhiT_one 108 0 0 1 (l := zero) (by decide) [negOne, negOne]
  have t24 := tendsto_i9M3PhiT_one 108 144 36 0 (l := zero) (by decide) [negOne, one]
  have t25 := tendsto_i9M3PhiT_one (-72) 0 0 1 (l := zero) (by decide) [negOne, one]
  have t26 := tendsto_i9M3PhiT_one (-9) 180 81 0 (l := zero) (by decide) [zero, negOne]
  have t27 := tendsto_i9M3PhiT_one 72 0 0 1 (l := zero) (by decide) [zero, negOne]
  have t28 := tendsto_i9M3PhiT_one (-138) (-120) (-54) 0 (l := zero) (by decide) [zero, one]
  have t29 := tendsto_i9M3PhiT_one (-48) 0 0 1 (l := zero) (by decide) [zero, one]
  have t30 := tendsto_i9M3PhiT_one (-180) 144 36 0 (l := zero) (by decide) [one, negOne]
  have t31 := tendsto_i9M3PhiT_one (-72) 0 0 1 (l := zero) (by decide) [one, negOne]
  have t32 := tendsto_i9M3PhiT_one 120 (-96) (-24) 0 (l := zero) (by decide) [one, one]
  have t33 := tendsto_i9M3PhiT_one 48 0 0 1 (l := zero) (by decide) [one, one]
  have t34 := tendsto_i9M3PhiT_one_one (-180) 144 36 0 [zero, negOne] (by ring)
  have t35 := tendsto_i9M3PhiT_one_one 120 (-96) (-24) 0 [zero, one] (by ring)
  have t36 := tendsto_i9M3PhiT_one (-108) 0 0 0 (l := zero) (by decide) [negOne, zero, negOne]
  have t37 := tendsto_i9M3PhiT_one 72 0 0 0 (l := zero) (by decide) [negOne, zero, one]
  have t38 := tendsto_i9M3PhiT_one (-216) 0 0 0 (l := zero) (by decide) [zero, negOne, negOne]
  have t39 := tendsto_i9M3PhiT_one 144 0 0 0 (l := zero) (by decide) [zero, negOne, one]
  have t40 := tendsto_i9M3PhiT_one (-54) 0 0 0 (l := zero) (by decide) [zero, zero, negOne]
  have t41 := tendsto_i9M3PhiT_one 36 0 0 0 (l := zero) (by decide) [zero, zero, one]
  have t42 := tendsto_i9M3PhiT_one 144 0 0 0 (l := zero) (by decide) [zero, one, negOne]
  have t43 := tendsto_i9M3PhiT_one (-96) 0 0 0 (l := zero) (by decide) [zero, one, one]
  have t44 := tendsto_i9M3PhiT_one 72 0 0 0 (l := zero) (by decide) [one, zero, negOne]
  have t45 := tendsto_i9M3PhiT_one (-48) 0 0 0 (l := zero) (by decide) [one, zero, one]
  have h := t0.add t1 |>.add t2 |>.add t3 |>.add t4 |>.add t5 |>.add t6 |>.add t7 |>.add t8
    |>.add t9 |>.add t10 |>.add t11 |>.add t12 |>.add t13 |>.add t14 |>.add t15 |>.add t16
    |>.add t17 |>.add t18 |>.add t19 |>.add t20 |>.add t21 |>.add t22 |>.add t23 |>.add t24
    |>.add t25 |>.add t26 |>.add t27 |>.add t28 |>.add t29 |>.add t30 |>.add t31 |>.add t32
    |>.add t33 |>.add t34 |>.add t35 |>.add t36 |>.add t37 |>.add t38 |>.add t39 |>.add t40
    |>.add t41 |>.add t42 |>.add t43 |>.add t44 |>.add t45
  rw [i9M3Phi_eq_sum]
  convert h using 2
  simp only [ hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_negOne_one_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_negOne_zero_one_at_one, hpl_zero_negOne_at_one,
    hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_one_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_one_at_one, hpl_zero_one_zero_negOne_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_negOne_negOne_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_one_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_zero_one_one_at_one, hpl_zero_zero_zero_negOne_at_one, hpl_zero_zero_zero_one_at_one]
  ring

/-! ### The integral -/

/-- `∫₀¹ G = -621/2 + 235π²/4 + 147 ζ₃ - π⁴/12 - 72 π² log 2`, given integrability of `G`. -/
theorem integral_i9M3O (hint : IntervalIntegrable i9M3O volume 0 1) :
    ∫ w in (0 : ℝ)..1, i9M3O w =
      -621 / 2 + 235 * π ^ 2 / 4 + 147 * zeta3 - π ^ 4 / 12 - 72 * π ^ 2 * Real.log 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun x hx => hasDerivAt_i9M3Phi hx) hint tendsto_i9M3Phi_zero tendsto_i9M3Phi_one, sub_zero]

end QED.ThreeLoopD
