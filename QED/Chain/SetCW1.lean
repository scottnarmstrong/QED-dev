/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetCKernel
public import QED.Chain.SetCW3
import QED.Polylog.AlphabetPM
import QED.Polylog.LiCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c): the rational-coefficient part

Helper analysis for the sixth-order set (c) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

In the atoms `log u, log (1 - u), log (1 + u), Li 2 u, Li 2 (-u)` the set (c) integrand
`QED.Chain.setCJ` is `G₁' + g₃ + w₄`, where `g₃ = QED.Chain.setCg3` has simple poles only,
`w₄ = QED.Chain.setCw4 = (5/3) log u Φ(u)/u` (`Φ = QED.Polylog.setCPhi`), and
`G₁ = QED.Chain.setCG1` is a combination of the atom monomials of weight at most three with
rational coefficients whose denominators are powers of `u`, `1 - u` and `1 + u` (obtained by
repeated integration by parts of the highest-weight monomial; generator
`scratchpad/setC/gen_w1.py`). The coefficients (`QED.Chain.SetCW1.h21000`, ...) are indexed by
the exponents of the five atoms.

## Main statements

* `QED.Chain.SetCW1.setCg3_add_eq`: `g₃ + w₄` in atoms.
* `QED.Chain.hasDerivAt_setCG1`: `G₁' = setCJ - g₃ - w₄` on `(0, 1)`.
-/

@[expose] public section

open Real Set QED.Polylog QED.Chain.SetCKernel

namespace QED.Chain

/-- The weight-four part `w₄ = (5/3) log u Φ(u)/u` of the set (c) integrand, written out
(`Φ = QED.Polylog.setCPhi`). -/
noncomputable def setCw4 (u : ℝ) : ℝ :=
  5 / 3 * (log u ^ 2 * log (1 - u) / u + 2 * (log u ^ 2 * log (1 + u) / u) +
    2 * (log u * Li 2 u / u) + 4 * (log u * Li 2 (-u) / u))

namespace SetCW1

/-- Coefficient of the monomial `21000` in `G₁`. -/
noncomputable def h21000 (x : ℝ) : ℝ :=
  (3 - 7 * x + 95 * x ^ 2 - 175 * x ^ 3 + 101 * x ^ 4 + 3 * x ^ 5 - 7 * x ^ 6 + 3 * x ^ 7) / (18
      * x ^ 2 * (1 - x) ^ 3)

/-- Derivative of `h21000`. -/
noncomputable def hd21000 (x : ℝ) : ℝ :=
  (-3 + 11 * x - 14 * x ^ 2 + 55 * x ^ 3 - 74 * x ^ 4 + 55 * x ^ 5 - 14 * x ^ 6 + 11 * x ^ 7 - 3
      * x ^ 8) / (9 * x ^ 3 * (1 - x) ^ 4)

/-- Coefficient of the monomial `20100` in `G₁`. -/
noncomputable def h20100 (x : ℝ) : ℝ :=
  (3 - 7 * x + 95 * x ^ 2 - 175 * x ^ 3 + 101 * x ^ 4 + 3 * x ^ 5 - 7 * x ^ 6 + 3 * x ^ 7) / (9
      * x ^ 2 * (1 - x) ^ 3)

/-- Derivative of `h20100`. -/
noncomputable def hd20100 (x : ℝ) : ℝ :=
  (-6 + 22 * x - 28 * x ^ 2 + 110 * x ^ 3 - 148 * x ^ 4 + 110 * x ^ 5 - 28 * x ^ 6 + 22 * x ^ 7
      - 6 * x ^ 8) / (9 * x ^ 3 * (1 - x) ^ 4)

/-- Coefficient of the monomial `20000` in `G₁`. -/
noncomputable def h20000 (x : ℝ) : ℝ :=
  (-6 + 23 * x + 17 * x ^ 2 - 56 * x ^ 3 + 24 * x ^ 4 - x ^ 5 - 17 * x ^ 6) / (36 * x * (1 - x) ^ 3)

/-- Derivative of `h20000`. -/
noncomputable def hd20000 (x : ℝ) : ℝ :=
  (3 - 12 * x + 43 * x ^ 2 - 39 * x ^ 3 + 8 * x ^ 4 - 2 * x ^ 5 - 42 * x ^ 6 + 17 * x ^ 7) / (18
      * x ^ 2 * (1 - x) ^ 4)

/-- Coefficient of the monomial `11000` in `G₁`. -/
noncomputable def h11000 (x : ℝ) : ℝ :=
  (12 - 112 * x + 245 * x ^ 2 - 172 * x ^ 3 + 27 * x ^ 4) / (108 * x ^ 2)

/-- Derivative of `h11000`. -/
noncomputable def hd11000 (x : ℝ) : ℝ :=
  (-12 + 56 * x - 86 * x ^ 3 + 27 * x ^ 4) / (54 * x ^ 3)

/-- Coefficient of the monomial `10100` in `G₁`. -/
noncomputable def h10100 (x : ℝ) : ℝ :=
  (39 - 284 * x - 284 * x ^ 3 + 39 * x ^ 4) / (108 * x ^ 2)

/-- Derivative of `h10100`. -/
noncomputable def hd10100 (x : ℝ) : ℝ :=
  (-39 + 142 * x - 142 * x ^ 3 + 39 * x ^ 4) / (54 * x ^ 3)

/-- Coefficient of the monomial `10010` in `G₁`. -/
noncomputable def h10010 (x : ℝ) : ℝ :=
  (3 - 7 * x + 95 * x ^ 2 - 175 * x ^ 3 + 101 * x ^ 4 + 3 * x ^ 5 - 7 * x ^ 6 + 3 * x ^ 7) / (9
      * x ^ 2 * (1 - x) ^ 3)

/-- Derivative of `h10010`. -/
noncomputable def hd10010 (x : ℝ) : ℝ :=
  (-6 + 22 * x - 28 * x ^ 2 + 110 * x ^ 3 - 148 * x ^ 4 + 110 * x ^ 5 - 28 * x ^ 6 + 22 * x ^ 7
      - 6 * x ^ 8) / (9 * x ^ 3 * (1 - x) ^ 4)

/-- Coefficient of the monomial `10001` in `G₁`. -/
noncomputable def h10001 (x : ℝ) : ℝ :=
  (6 - 14 * x + 190 * x ^ 2 - 350 * x ^ 3 + 202 * x ^ 4 + 6 * x ^ 5 - 14 * x ^ 6 + 6 * x ^ 7) /
      (9 * x ^ 2 * (1 - x) ^ 3)

/-- Derivative of `h10001`. -/
noncomputable def hd10001 (x : ℝ) : ℝ :=
  (-12 + 44 * x - 56 * x ^ 2 + 220 * x ^ 3 - 296 * x ^ 4 + 220 * x ^ 5 - 56 * x ^ 6 + 44 * x ^ 7
      - 12 * x ^ 8) / (9 * x ^ 3 * (1 - x) ^ 4)

/-- Coefficient of the monomial `10000` in `G₁`. -/
noncomputable def h10000 (x : ℝ) : ℝ :=
  (18 + 371 * x - 51 * x ^ 2 - 72 * x ^ 3 + 98 * x ^ 4 + 349 * x ^ 5 - 185 * x ^ 6) / (216 * x *
      (1 + x) * (1 - x) ^ 2)

/-- Derivative of `h10000`. -/
noncomputable def hd10000 (x : ℝ) : ℝ :=
  (-9 + 9 * x + 196 * x ^ 2 + 459 * x ^ 3 + 60 * x ^ 4 + 711 * x ^ 5 - 288 * x ^ 6 - 267 * x ^ 7
      + 185 * x ^ 8) / (108 * x ^ 2 * (1 + x) ^ 2 * (1 - x) ^ 3)

/-- Coefficient of the monomial `01000` in `G₁`. -/
noncomputable def h01000 (x : ℝ) : ℝ :=
  (-126 + 678 * x - 1143 * x ^ 2 + 407 * x ^ 3 + 53 * x ^ 4 - 61 * x ^ 5) / (216 * x ^ 2 * (1 - x))

/-- Derivative of `h01000`. -/
noncomputable def hd01000 (x : ℝ) : ℝ :=
  (126 - 528 * x + 678 * x ^ 2 - 368 * x ^ 3 + 53 * x ^ 4 - 118 * x ^ 5 + 61 * x ^ 6) / (108
      * x ^ 3 * (1 - x) ^ 2)

/-- Coefficient of the monomial `00100` in `G₁`. -/
noncomputable def h00100 (x : ℝ) : ℝ :=
  (-187 + 731 * x - 928 * x ^ 2 - 544 * x ^ 3 + 731 * x ^ 4 - 187 * x ^ 5) / (216 * x ^ 2 * (1 - x))

/-- Derivative of `h00100`. -/
noncomputable def hd00100 (x : ℝ) : ℝ :=
  (187 - 646 * x + 731 * x ^ 2 - 736 * x ^ 3 + 731 * x ^ 4 - 646 * x ^ 5 + 187 * x ^ 6) / (108
      * x ^ 3 * (1 - x) ^ 2)

/-- Coefficient of the monomial `00010` in `G₁`. -/
noncomputable def h00010 (x : ℝ) : ℝ :=
  (39 - 190 * x + 263 * x ^ 2 - 128 * x ^ 3 + 263 * x ^ 4 - 190 * x ^ 5 + 39 * x ^ 6) / (54
      * x ^ 2 * (1 - x) ^ 2)

/-- Derivative of `h00010`. -/
noncomputable def hd00010 (x : ℝ) : ℝ :=
  (-39 + 173 * x - 285 * x ^ 2 + 199 * x ^ 3 + 199 * x ^ 4 - 285 * x ^ 5 + 173 * x ^ 6 - 39
      * x ^ 7) / (27 * x ^ 3 * (1 - x) ^ 3)

/-- Coefficient of the monomial `00001` in `G₁`. -/
noncomputable def h00001 (x : ℝ) : ℝ :=
  (39 - 190 * x + 263 * x ^ 2 - 128 * x ^ 3 + 263 * x ^ 4 - 190 * x ^ 5 + 39 * x ^ 6) / (27
      * x ^ 2 * (1 - x) ^ 2)

/-- Derivative of `h00001`. -/
noncomputable def hd00001 (x : ℝ) : ℝ :=
  (-78 + 346 * x - 570 * x ^ 2 + 398 * x ^ 3 + 398 * x ^ 4 - 570 * x ^ 5 + 346 * x ^ 6 - 78
      * x ^ 7) / (27 * x ^ 3 * (1 - x) ^ 3)

/-- Coefficient of the monomial `00000` in `G₁`. -/
noncomputable def h00000 (x : ℝ) : ℝ :=
  (434 + 286 * x + 2244 * x ^ 2 - 2517 * x ^ 3 + 273 * x ^ 4) / (432 * x * (1 - x))

/-- Derivative of `h00000`. -/
noncomputable def hd00000 (x : ℝ) : ℝ :=
  (-217 + 434 * x + 1265 * x ^ 2 - 2517 * x ^ 3 + 1668 * x ^ 4 - 273 * x ^ 5) / (216 * x ^ 2 * (1
      - x) ^ 2)

/-- Coefficient of `21000` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w21000 (x : ℝ) : ℝ :=
  (5) / (3 * x)

/-- Coefficient of `20100` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w20100 (x : ℝ) : ℝ :=
  (10) / (3 * x)

/-- Coefficient of `20000` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w20000 (x : ℝ) : ℝ :=
  (-145 + 48 * x) / (18 * (1 + x) * (1 - x))

/-- Coefficient of `11000` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w11000 (x : ℝ) : ℝ :=
  (3 + 13 * x) / (6 * x * (1 - x))

/-- Coefficient of `10100` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w10100 (x : ℝ) : ℝ :=
  (8 + 8 * x) / (3 * x * (1 - x))

/-- Coefficient of `10010` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w10010 (x : ℝ) : ℝ :=
  (10) / (3 * x)

/-- Coefficient of `10001` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w10001 (x : ℝ) : ℝ :=
  (20) / (3 * x)

/-- Coefficient of `10000` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w10000 (x : ℝ) : ℝ :=
  (-129 + 133 * x) / (54 * (1 + x) * (1 - x))

/-- Coefficient of `01000` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w01000 (x : ℝ) : ℝ :=
  (-55) / (12 * x)

/-- Coefficient of `00100` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w00100 (x : ℝ) : ℝ :=
  (-125) / (27 * x)

/-- Coefficient of `00010` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w00010 (x : ℝ) : ℝ :=
  (-46) / (9 * x)

/-- Coefficient of `00001` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w00001 (x : ℝ) : ℝ :=
  (-92) / (9 * x)

/-- Coefficient of `00000` in `g₃ + (5/3) log x Φ(x)/x`. -/
noncomputable def w00000 (x : ℝ) : ℝ :=
  (8) / (9 * (1 + x))

theorem hasDerivAt_h21000 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h21000 (hd21000 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := ((((((((hasDerivAt_const u (3 : ℝ)).sub ((hasDerivAt_id' u).const_mul (7 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (95 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (175 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (101 : ℝ))).add
      ((hasDerivAt_pow 5 u).const_mul (3 : ℝ))).sub ((hasDerivAt_pow 6 u).const_mul (7 : ℝ))).add
      ((hasDerivAt_pow 7 u).const_mul (3 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (18 : ℝ)).mul (((hasDerivAt_id' u).const_sub 1).pow 3))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd21000
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h20100 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h20100 (hd20100 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := ((((((((hasDerivAt_const u (3 : ℝ)).sub ((hasDerivAt_id' u).const_mul (7 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (95 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (175 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (101 : ℝ))).add
      ((hasDerivAt_pow 5 u).const_mul (3 : ℝ))).sub ((hasDerivAt_pow 6 u).const_mul (7 : ℝ))).add
      ((hasDerivAt_pow 7 u).const_mul (3 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (9 : ℝ)).mul (((hasDerivAt_id' u).const_sub 1).pow 3))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd20100
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h20000 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h20000 (hd20000 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := (((((((hasDerivAt_const u (6 : ℝ)).neg.add ((hasDerivAt_id' u).const_mul
      (23 : ℝ))).add ((hasDerivAt_pow 2 u).const_mul (17 : ℝ))).sub
      ((hasDerivAt_pow 3 u).const_mul (56 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul
      (24 : ℝ))).sub (hasDerivAt_pow 5 u)).sub ((hasDerivAt_pow 6 u).const_mul (17 : ℝ))).div
    (((hasDerivAt_id' u).const_mul (36 : ℝ)).mul (((hasDerivAt_id' u).const_sub 1).pow 3))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd20000
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h11000 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h11000 (hd11000 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := (((((hasDerivAt_const u (12 : ℝ)).sub ((hasDerivAt_id' u).const_mul (112 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (245 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (172 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (27 : ℝ))).div
    ((hasDerivAt_pow 2 u).const_mul (108 : ℝ))
    (by positivity)
  refine h.congr_deriv ?_
  unfold hd11000
  simp only [Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h10100 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h10100 (hd10100 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := ((((hasDerivAt_const u (39 : ℝ)).sub ((hasDerivAt_id' u).const_mul (284 : ℝ))).sub
      ((hasDerivAt_pow 3 u).const_mul (284 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (39 : ℝ))).div
    ((hasDerivAt_pow 2 u).const_mul (108 : ℝ))
    (by positivity)
  refine h.congr_deriv ?_
  unfold hd10100
  simp only [Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h10010 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h10010 (hd10010 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := ((((((((hasDerivAt_const u (3 : ℝ)).sub ((hasDerivAt_id' u).const_mul (7 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (95 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (175 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (101 : ℝ))).add
      ((hasDerivAt_pow 5 u).const_mul (3 : ℝ))).sub ((hasDerivAt_pow 6 u).const_mul (7 : ℝ))).add
      ((hasDerivAt_pow 7 u).const_mul (3 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (9 : ℝ)).mul (((hasDerivAt_id' u).const_sub 1).pow 3))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd10010
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h10001 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h10001 (hd10001 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := ((((((((hasDerivAt_const u (6 : ℝ)).sub ((hasDerivAt_id' u).const_mul (14 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (190 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (350 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (202 : ℝ))).add
      ((hasDerivAt_pow 5 u).const_mul (6 : ℝ))).sub ((hasDerivAt_pow 6 u).const_mul (14 : ℝ))).add
      ((hasDerivAt_pow 7 u).const_mul (6 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (9 : ℝ)).mul (((hasDerivAt_id' u).const_sub 1).pow 3))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd10001
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h10000 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h10000 (hd10000 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := (((((((hasDerivAt_const u (18 : ℝ)).add ((hasDerivAt_id' u).const_mul (371 : ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (51 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (72 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (98 : ℝ))).add
      ((hasDerivAt_pow 5 u).const_mul (349 : ℝ))).sub ((hasDerivAt_pow 6 u).const_mul
      (185 : ℝ))).div
    ((((hasDerivAt_id' u).const_mul (216 : ℝ)).mul ((hasDerivAt_id' u).const_add 1)).mul
        (((hasDerivAt_id' u).const_sub 1).pow 2))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd10000
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h01000 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h01000 (hd01000 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := ((((((hasDerivAt_const u (126 : ℝ)).neg.add ((hasDerivAt_id' u).const_mul
      (678 : ℝ))).sub ((hasDerivAt_pow 2 u).const_mul (1143 : ℝ))).add
      ((hasDerivAt_pow 3 u).const_mul (407 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul
      (53 : ℝ))).sub ((hasDerivAt_pow 5 u).const_mul (61 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (216 : ℝ)).mul ((hasDerivAt_id' u).const_sub 1))
    (by simp only [Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd01000
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00100 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h00100 (hd00100 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := ((((((hasDerivAt_const u (187 : ℝ)).neg.add ((hasDerivAt_id' u).const_mul
      (731 : ℝ))).sub ((hasDerivAt_pow 2 u).const_mul (928 : ℝ))).sub
      ((hasDerivAt_pow 3 u).const_mul (544 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul
      (731 : ℝ))).sub ((hasDerivAt_pow 5 u).const_mul (187 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (216 : ℝ)).mul ((hasDerivAt_id' u).const_sub 1))
    (by simp only [Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00100
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00010 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h00010 (hd00010 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := (((((((hasDerivAt_const u (39 : ℝ)).sub ((hasDerivAt_id' u).const_mul (190 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (263 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (128 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (263 : ℝ))).sub
      ((hasDerivAt_pow 5 u).const_mul (190 : ℝ))).add ((hasDerivAt_pow 6 u).const_mul (39 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (54 : ℝ)).mul (((hasDerivAt_id' u).const_sub 1).pow 2))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00010
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00001 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h00001 (hd00001 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := (((((((hasDerivAt_const u (39 : ℝ)).sub ((hasDerivAt_id' u).const_mul (190 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (263 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (128 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (263 : ℝ))).sub
      ((hasDerivAt_pow 5 u).const_mul (190 : ℝ))).add ((hasDerivAt_pow 6 u).const_mul (39 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (27 : ℝ)).mul (((hasDerivAt_id' u).const_sub 1).pow 2))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00001
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00000 {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt h00000 (hd00000 u) u := by
  have hm : (0 : ℝ) < 1 - u := by linarith
  have h := (((((hasDerivAt_const u (434 : ℝ)).add ((hasDerivAt_id' u).const_mul (286 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (2244 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (2517 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (273 : ℝ))).div
    (((hasDerivAt_id' u).const_mul (432 : ℝ)).mul ((hasDerivAt_id' u).const_sub 1))
    (by simp only [Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00000
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  have hm' : 1 - u ≠ 0 := hm.ne'
  push_cast
  field_simp
  ring

theorem setCg3_add_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    setCg3 u + setCw4 u = w21000 u * log u ^ 2 * log (1 - u) + w20100 u * log u ^ 2 * log (1 + u)
        + w20000 u * log u ^ 2 + w11000 u * log u * log (1 - u) + w10100 u * log u * log (1 + u)
        + w10010 u * log u * Li 2 u + w10001 u * log u * Li 2 (-u) + w10000 u * log u + w01000 u
        * log (1 - u) + w00100 u * log (1 + u) + w00010 u * Li 2 u + w00001 u * Li 2 (-u)
        + w00000 u := by
  obtain ⟨h0, h1⟩ := hu
  have hz : u ≠ 0 := h0.ne'
  have hm : u - 1 ≠ 0 := by linarith
  have hm' : 1 - u ≠ 0 := by linarith
  have hp : u + 1 ≠ 0 := by linarith
  have hp' : 1 + u ≠ 0 := by linarith
  unfold setCg3 setCw4 w21000 w20100 w20000 w11000 w10100 w10010 w10001 w10000 w01000 w00100 w00010
      w00001 w00000
  field_simp
  ring

end SetCW1

open SetCW1

/-- The rational-coefficient antiderivative `G₁`. -/
noncomputable def setCG1 (x : ℝ) : ℝ :=
  h21000 x * (log x ^ 2 * log (1 - x)) +
    h20100 x * (log x ^ 2 * log (1 + x)) +
    h20000 x * (log x ^ 2) +
    h11000 x * (log x * log (1 - x)) +
    h10100 x * (log x * log (1 + x)) +
    h10010 x * (log x * Li 2 x) +
    h10001 x * (log x * Li 2 (-x)) +
    h10000 x * (log x) +
    h01000 x * (log (1 - x)) +
    h00100 x * (log (1 + x)) +
    h00010 x * (Li 2 x) +
    h00001 x * (Li 2 (-x)) +
    h00000 x

/-- **The rational-coefficient part**: `G₁' = setCJ - g₃ - w₄` on `(0, 1)`. -/
theorem hasDerivAt_setCG1 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt setCG1 (setCJ u - setCg3 u - setCw4 u) u := by
  have hw := setCg3_add_eq hu
  obtain ⟨h0, h1⟩ := hu
  obtain ⟨di, ai, ni, li, -, gi1⟩ := PM.data_id h0 h1
  obtain ⟨dA, aA, nA, lA, -, gA1⟩ := PM.data_neg h0 h1
  obtain ⟨dB, -, nB, lB, -, -⟩ := PM.data_oneSub h0 h1
  have e0 := hasDerivAt_log_of di ni li
  have e1 := hasDerivAt_log_of dB nB lB
  have em : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + u)) u := by
    have := ((hasDerivAt_id' u).const_add 1).log (by linarith)
    simpa [one_div] using this
  have qP := hasDerivAt_Li_two_of di ai ni li gi1
  have qM := hasDerivAt_Li_two_of dA aA nA lA gA1
  have t0 := (hasDerivAt_h21000 h0 h1).mul ((e0.pow 2).mul e1)
  have t1 := (hasDerivAt_h20100 h0 h1).mul ((e0.pow 2).mul em)
  have t2 := (hasDerivAt_h20000 h0 h1).mul (e0.pow 2)
  have t3 := (hasDerivAt_h11000 h0 h1).mul (e0.mul e1)
  have t4 := (hasDerivAt_h10100 h0 h1).mul (e0.mul em)
  have t5 := (hasDerivAt_h10010 h0 h1).mul (e0.mul qP)
  have t6 := (hasDerivAt_h10001 h0 h1).mul (e0.mul qM)
  have t7 := (hasDerivAt_h10000 h0 h1).mul e0
  have t8 := (hasDerivAt_h01000 h0 h1).mul e1
  have t9 := (hasDerivAt_h00100 h0 h1).mul em
  have t10 := (hasDerivAt_h00010 h0 h1).mul qP
  have t11 := (hasDerivAt_h00001 h0 h1).mul qM
  have t12 := hasDerivAt_h00000 h0 h1
  have h :=
      ((((((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add
      t10).add t11).add t12)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hp : 1 + u ≠ 0 := by linarith
  have hm : 1 - u ≠ 0 := by linarith
  have hz : u ≠ 0 := h0.ne'
  have c0 : hd21000 u = j21000 u - w21000 u := by
    simp only [hd21000, j21000, w21000]
    field_simp
    ring
  have c1 : hd20100 u = j20100 u - w20100 u := by
    simp only [hd20100, j20100, w20100]
    field_simp
    ring
  have c2 : hd20000 u - h21000 u * (1 - u)⁻¹ + h20100 u * (1 + u)⁻¹ = j20000 u - w20000 u := by
    simp only [h20100, h21000, hd20000, j20000, w20000]
    field_simp
    ring
  have c3 : hd11000 u + 2 * h21000 u * u⁻¹ - h10010 u * u⁻¹ = j11000 u - w11000 u := by
    simp only [h10010, h21000, hd11000, j11000, w11000]
    field_simp
    ring
  have c4 : hd10100 u + 2 * h20100 u * u⁻¹ - h10001 u * u⁻¹ = j10100 u - w10100 u := by
    simp only [h10001, h20100, hd10100, j10100, w10100]
    field_simp
    ring
  have c5 : hd10010 u = j10010 u - w10010 u := by
    simp only [hd10010, j10010, w10010]
    field_simp
    ring
  have c6 : hd10001 u = j10001 u - w10001 u := by
    simp only [hd10001, j10001, w10001]
    field_simp
    ring
  have c7 : hd10000 u + 2 * h20000 u * u⁻¹ - h11000 u * (1 - u)⁻¹ + h10100 u * (1
      + u)⁻¹ = j10000 u - w10000 u := by
    simp only [h10100, h11000, h20000, hd10000, j10000, w10000]
    field_simp
    ring
  have c8 : hd01000 u + h11000 u * u⁻¹ - h00010 u * u⁻¹ = j01000 u - w01000 u := by
    simp only [h00010, h11000, hd01000, j01000, w01000]
    field_simp
    ring
  have c9 : hd00100 u + h10100 u * u⁻¹ - h00001 u * u⁻¹ = j00100 u - w00100 u := by
    simp only [h00001, h10100, hd00100, j00100, w00100]
    field_simp
    ring
  have c10 : hd00010 u + h10010 u * u⁻¹ = j00010 u - w00010 u := by
    simp only [h10010, hd00010, j00010, w00010]
    field_simp
    ring
  have c11 : hd00001 u + h10001 u * u⁻¹ = j00001 u - w00001 u := by
    simp only [h10001, hd00001, j00001, w00001]
    field_simp
    ring
  have c12 : hd00000 u + h10000 u * u⁻¹ - h01000 u * (1 - u)⁻¹ + h00100 u * (1 + u)⁻¹ = j00000 u
      - w00000 u := by
    simp only [h00100, h01000, h10000, hd00000, j00000, w00000]
    field_simp
    ring
  unfold setCJ
  linear_combination log u ^ 2 * log (1 - u) * c0 + log u ^ 2 * log (1 + u) * c1 + log u ^ 2 * c2
      + log u * log (1 - u) * c3 + log u * log (1 + u) * c4 + log u * Li 2 u * c5 + log u * Li 2
      (-u) * c6 + log u * c7 + log (1 - u) * c8 + log (1 + u) * c9 + Li 2 u * c10 + Li 2 (-u)
      * c11 + c12 + hw

end QED.Chain
