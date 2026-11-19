/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetASubst
public import QED.Chain.SetAW3
public import QED.Chain.SetAW4
import QED.Polylog.AlphabetPM
import QED.Polylog.LiCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (a): the rational-coefficient part

Helper analysis for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

In the atoms `log u, log (1 - u), log (1 + u), Li 2 u, Li 2 (-u)` the set (a) integrand
`QED.Chain.setAJ` is `G₁' + g₃ + g₄`, where `g₃ = QED.Chain.setAg3`, `g₄ = -(8/3) Φ ψ'`
(`QED.Chain.setAPhi`, `QED.Chain.setAPsiD`) and `G₁ = QED.Chain.setAG1` is a combination of
the atom monomials of weight at most three with rational coefficients in `u` whose denominators
are powers of `u` and `1 + u`. The coefficients (`QED.Chain.SetAW1.h21000`, ...) are indexed by
the exponents of the five atoms.

## Main statements

* `QED.Chain.SetAW1.setAJ_eq_atoms`: `setAJ` as a product of its prefactor, `ρ⁽⁴⁾` and `K̃` in
    atoms.
* `QED.Chain.hasDerivAt_setAG1`: `G₁' = setAJ - g₃ + (8/3) Φ ψ'` on `(0, 1)`.
-/

@[expose] public section

open Real Set QED.Polylog

namespace QED.Chain

namespace SetAW1

/-! ### Rational coefficients -/

/-- Coefficient of the monomial `21000` in `G₁`. -/
noncomputable def h21000 (x : ℝ) : ℝ :=
  (-38 - 66 * x + 12 * x ^ 2 + 68 * x ^ 3 + 18 * x ^ 4 + 6 * x ^ 5) / (9 * (1 + x) ^ 3)

/-- Derivative of `h21000`. -/
noncomputable def hd21000 (x : ℝ) : ℝ :=
  (16 + 52 * x + 64 * x ^ 2 + 24 * x ^ 3 + 16 * x ^ 4 + 4 * x ^ 5) / (3 * (1 + x) ^ 4)

/-- Coefficient of the monomial `20100` in `G₁`. -/
noncomputable def h20100 (x : ℝ) : ℝ :=
  (-44 - 108 * x - 69 * x ^ 2 + 9 * x ^ 3 + 9 * x ^ 4 + 3 * x ^ 5) / (9 * (1 + x) ^ 3)

/-- Derivative of `h20100`. -/
noncomputable def hd20100 (x : ℝ) : ℝ :=
  (8 + 26 * x + 32 * x ^ 2 + 12 * x ^ 3 + 8 * x ^ 4 + 2 * x ^ 5) / (3 * (1 + x) ^ 4)

/-- Coefficient of the monomial `20000` in `G₁`. -/
noncomputable def h20000 (x : ℝ) : ℝ :=
  (12 * x - 126 * x ^ 2 - 308 * x ^ 3 - 225 * x ^ 4 - 81 * x ^ 5) / (54 * (1 + x) ^ 3)

/-- Derivative of `h20000`. -/
noncomputable def hd20000 (x : ℝ) : ℝ :=
  (2 - 46 * x - 133 * x ^ 2 - 150 * x ^ 3 - 105 * x ^ 4 - 27 * x ^ 5) / (9 * (1 + x) ^ 4)

/-- Coefficient of the monomial `11100` in `G₁`. -/
noncomputable def h11100 (x : ℝ) : ℝ :=
  (-2 - 4 * x - 6 * x ^ 2 + 24 * x ^ 3 - 6 * x ^ 4 - 4 * x ^ 5 - 2 * x ^ 6) / (3 * x ^ 2 * (1
      + x) ^ 2)

/-- Derivative of `h11100`. -/
noncomputable def hd11100 (x : ℝ) : ℝ :=
  (4 + 12 * x + 12 * x ^ 2 + 36 * x ^ 3 - 36 * x ^ 4 - 12 * x ^ 5 - 12 * x ^ 6 - 4 * x ^ 7) / (3
      * x ^ 3 * (1 + x) ^ 3)

/-- Coefficient of the monomial `11000` in `G₁`. -/
noncomputable def h11000 (x : ℝ) : ℝ :=
  (8 - 51 * x - 116 * x ^ 2 - 54 * x ^ 3 + 60 * x ^ 4 + 85 * x ^ 5 + 56 * x ^ 6 + 12 * x ^ 7) /
      (12 * x * (1 + x) ^ 4)

/-- Derivative of `h11000`. -/
noncomputable def hd11000 (x : ℝ) : ℝ :=
  (-2 - 10 * x + 22 * x ^ 2 + 60 * x ^ 3 + 72 * x ^ 4 + 70 * x ^ 5 + 70 * x ^ 6 + 32 * x ^ 7 + 6
      * x ^ 8) / (3 * x ^ 2 * (1 + x) ^ 5)

/-- Coefficient of the monomial `10200` in `G₁`. -/
noncomputable def h10200 (x : ℝ) : ℝ :=
  (-1 - 2 * x - x ^ 2 + 16 * x ^ 3 - x ^ 4 - 2 * x ^ 5 - x ^ 6) / (3 * x ^ 2 * (1 + x) ^ 2)

/-- Derivative of `h10200`. -/
noncomputable def hd10200 (x : ℝ) : ℝ :=
  (2 + 6 * x + 6 * x ^ 2 + 18 * x ^ 3 - 18 * x ^ 4 - 6 * x ^ 5 - 6 * x ^ 6 - 2 * x ^ 7) / (3
      * x ^ 3 * (1 + x) ^ 3)

/-- Coefficient of the monomial `10100` in `G₁`. -/
noncomputable def h10100 (x : ℝ) : ℝ :=
  (-127 + 860 * x + 3270 * x ^ 2 + 4028 * x ^ 3 + 2321 * x ^ 4 + 864 * x ^ 5 + 216 * x ^ 6) /
      (108 * (1 + x) ^ 4)

/-- Derivative of `h10100`. -/
noncomputable def hd10100 (x : ℝ) : ℝ :=
  (38 + 110 * x + 154 * x ^ 2 + 146 * x ^ 3 + 120 * x ^ 4 + 60 * x ^ 5 + 12 * x ^ 6) / (3 * (1
      + x) ^ 5)

/-- Coefficient of the monomial `10010` in `G₁`. -/
noncomputable def h10010 (x : ℝ) : ℝ :=
  (-176 - 432 * x - 276 * x ^ 2 + 36 * x ^ 3 + 36 * x ^ 4 + 12 * x ^ 5) / (9 * (1 + x) ^ 3)

/-- Derivative of `h10010`. -/
noncomputable def hd10010 (x : ℝ) : ℝ :=
  (32 + 104 * x + 128 * x ^ 2 + 48 * x ^ 3 + 32 * x ^ 4 + 8 * x ^ 5) / (3 * (1 + x) ^ 4)

/-- Coefficient of the monomial `10001` in `G₁`. -/
noncomputable def h10001 (x : ℝ) : ℝ :=
  (-88 - 216 * x - 138 * x ^ 2 + 18 * x ^ 3 + 18 * x ^ 4 + 6 * x ^ 5) / (9 * (1 + x) ^ 3)

/-- Derivative of `h10001`. -/
noncomputable def hd10001 (x : ℝ) : ℝ :=
  (16 + 52 * x + 64 * x ^ 2 + 24 * x ^ 3 + 16 * x ^ 4 + 4 * x ^ 5) / (3 * (1 + x) ^ 4)

/-- Coefficient of the monomial `10000` in `G₁`. -/
noncomputable def h10000 (x : ℝ) : ℝ :=
  (72 + 248 * x - 917 * x ^ 2 - 3028 * x ^ 3 - 2646 * x ^ 4 - 828 * x ^ 5 - 27 * x ^ 6) / (216 *
      (1 + x) ^ 4)

/-- Derivative of `h10000`. -/
noncomputable def hd10000 (x : ℝ) : ℝ :=
  (-20 - 1289 * x - 3625 * x ^ 2 - 3778 * x ^ 3 - 2070 * x ^ 4 - 495 * x ^ 5 - 27 * x ^ 6) / (108
      * (1 + x) ^ 5)

/-- Coefficient of the monomial `01100` in `G₁`. -/
noncomputable def h01100 (x : ℝ) : ℝ :=
  (3 + 3 * x + 16 * x ^ 2 - 16 * x ^ 3 - 3 * x ^ 4 - 3 * x ^ 5) / (3 * x ^ 2 * (1 + x))

/-- Derivative of `h01100`. -/
noncomputable def hd01100 (x : ℝ) : ℝ :=
  (-6 - 12 * x - 6 * x ^ 2 - 32 * x ^ 3 - 6 * x ^ 4 - 12 * x ^ 5 - 6 * x ^ 6) / (3 * x ^ 3 * (1
      + x) ^ 2)

/-- Coefficient of the monomial `01000` in `G₁`. -/
noncomputable def h01000 (x : ℝ) : ℝ :=
  (-9 + 8 * x + 11 * x ^ 2 - 11 * x ^ 3 - 8 * x ^ 4 + 9 * x ^ 5) / (9 * x * (1 + x) ^ 3)

/-- Derivative of `h01000`. -/
noncomputable def hd01000 (x : ℝ) : ℝ :=
  (9 + 36 * x - 13 * x ^ 2 - 44 * x ^ 3 - 13 * x ^ 4 + 36 * x ^ 5 + 9 * x ^ 6) / (9 * x ^ 2 * (1
      + x) ^ 4)

/-- Coefficient of the monomial `00200` in `G₁`. -/
noncomputable def h00200 (x : ℝ) : ℝ :=
  (3 + 3 * x + 16 * x ^ 2 - 16 * x ^ 3 - 3 * x ^ 4 - 3 * x ^ 5) / (6 * x ^ 2 * (1 + x))

/-- Derivative of `h00200`. -/
noncomputable def hd00200 (x : ℝ) : ℝ :=
  (-3 - 6 * x - 3 * x ^ 2 - 16 * x ^ 3 - 3 * x ^ 4 - 6 * x ^ 5 - 3 * x ^ 6) / (3 * x ^ 3 * (1
      + x) ^ 2)

/-- Coefficient of the monomial `00110` in `G₁`. -/
noncomputable def h00110 (x : ℝ) : ℝ :=
  (-4 - 8 * x - 4 * x ^ 2 + 64 * x ^ 3 - 4 * x ^ 4 - 8 * x ^ 5 - 4 * x ^ 6) / (3 * x ^ 2 * (1
      + x) ^ 2)

/-- Derivative of `h00110`. -/
noncomputable def hd00110 (x : ℝ) : ℝ :=
  (8 + 24 * x + 24 * x ^ 2 + 72 * x ^ 3 - 72 * x ^ 4 - 24 * x ^ 5 - 24 * x ^ 6 - 8 * x ^ 7) / (3
      * x ^ 3 * (1 + x) ^ 3)

/-- Coefficient of the monomial `00101` in `G₁`. -/
noncomputable def h00101 (x : ℝ) : ℝ :=
  (-2 - 4 * x - 2 * x ^ 2 + 32 * x ^ 3 - 2 * x ^ 4 - 4 * x ^ 5 - 2 * x ^ 6) / (3 * x ^ 2 * (1
      + x) ^ 2)

/-- Derivative of `h00101`. -/
noncomputable def hd00101 (x : ℝ) : ℝ :=
  (4 + 12 * x + 12 * x ^ 2 + 36 * x ^ 3 - 36 * x ^ 4 - 12 * x ^ 5 - 12 * x ^ 6 - 4 * x ^ 7) / (3
      * x ^ 3 * (1 + x) ^ 3)

/-- Coefficient of the monomial `00100` in `G₁`. -/
noncomputable def h00100 (x : ℝ) : ℝ :=
  (-9 - 195 * x - 703 * x ^ 2 - 541 * x ^ 3 + 541 * x ^ 4 + 703 * x ^ 5 + 195 * x ^ 6 + 9
      * x ^ 7) / (72 * x ^ 2 * (1 + x) ^ 3)

/-- Derivative of `h00100`. -/
noncomputable def hd00100 (x : ℝ) : ℝ :=
  (9 + 120 * x + 390 * x ^ 2 + 784 * x ^ 3 + 1082 * x ^ 4 + 784 * x ^ 5 + 390 * x ^ 6 + 120
      * x ^ 7 + 9 * x ^ 8) / (36 * x ^ 3 * (1 + x) ^ 4)

/-- Coefficient of the monomial `00010` in `G₁`. -/
noncomputable def h00010 (x : ℝ) : ℝ :=
  (48 - 69 * x - 4 * x ^ 2 + 130 * x ^ 3 - 4 * x ^ 4 - 69 * x ^ 5 + 48 * x ^ 6) / (36 * x * (1
      + x) ^ 4)

/-- Derivative of `h00010`. -/
noncomputable def hd00010 (x : ℝ) : ℝ :=
  (-12 - 60 * x + 68 * x ^ 2 + 68 * x ^ 3 - 68 * x ^ 4 - 68 * x ^ 5 + 60 * x ^ 6 + 12 * x ^ 7) /
      (9 * x ^ 2 * (1 + x) ^ 5)

/-- Coefficient of the monomial `00001` in `G₁`. -/
noncomputable def h00001 (x : ℝ) : ℝ :=
  (72 + 575 * x + 2708 * x ^ 2 + 4266 * x ^ 3 + 2708 * x ^ 4 + 575 * x ^ 5 + 72 * x ^ 6) / (108
      * x * (1 + x) ^ 4)

/-- Derivative of `h00001`. -/
noncomputable def hd00001 (x : ℝ) : ℝ :=
  (-6 - 30 * x + 34 * x ^ 2 + 34 * x ^ 3 - 34 * x ^ 4 - 34 * x ^ 5 + 30 * x ^ 6 + 6 * x ^ 7) / (9
      * x ^ 2 * (1 + x) ^ 5)

/-- Coefficient of the monomial `00000` in `G₁`. -/
noncomputable def h00000 (x : ℝ) : ℝ :=
  (27 - 1846 * x - 3701 * x ^ 2 - 2080 * x ^ 3 - 81 * x ^ 4 - 27 * x ^ 5) / (216 * x * (1 + x) ^ 3)

/-- Derivative of `h00000`. -/
noncomputable def hd00000 (x : ℝ) : ℝ :=
  (-27 - 108 * x + 1837 * x ^ 2 + 3242 * x ^ 3 + 1837 * x ^ 4 - 108 * x ^ 5 - 27 * x ^ 6) / (216
      * x ^ 2 * (1 + x) ^ 4)

/-- Coefficient of `11000` in `ρ⁽⁴⁾((1-u)/(1+u))`. -/
noncomputable def r11000 (x : ℝ) : ℝ :=
  (4 + 16 * x + 8 * x ^ 2 + 16 * x ^ 3 + 4 * x ^ 4) / (3 * (1 + x) ^ 4)

/-- Coefficient of `10100` in `ρ⁽⁴⁾((1-u)/(1+u))`. -/
noncomputable def r10100 (x : ℝ) : ℝ :=
  (2 + 8 * x + 4 * x ^ 2 + 8 * x ^ 3 + 2 * x ^ 4) / (3 * (1 + x) ^ 4)

/-- Coefficient of `10000` in `ρ⁽⁴⁾((1-u)/(1+u))`. -/
noncomputable def r10000 (x : ℝ) : ℝ :=
  (2 * x - 7 * x ^ 2 - 22 * x ^ 3 - 6 * x ^ 4) / (3 * (1 + x) ^ 4)

/-- Coefficient of `01000` in `ρ⁽⁴⁾((1-u)/(1+u))`. -/
noncomputable def r01000 (x : ℝ) : ℝ :=
  (-4 - 12 * x + 12 * x ^ 2 + 4 * x ^ 3) / (3 * (1 + x) ^ 3)

/-- Coefficient of `00100` in `ρ⁽⁴⁾((1-u)/(1+u))`. -/
noncomputable def r00100 (x : ℝ) : ℝ :=
  (-2 - 6 * x + 6 * x ^ 2 + 2 * x ^ 3) / (3 * (1 + x) ^ 3)

/-- Coefficient of `00010` in `ρ⁽⁴⁾((1-u)/(1+u))`. -/
noncomputable def r00010 (x : ℝ) : ℝ :=
  (8 + 32 * x + 16 * x ^ 2 + 32 * x ^ 3 + 8 * x ^ 4) / (3 * (1 + x) ^ 4)

/-- Coefficient of `00001` in `ρ⁽⁴⁾((1-u)/(1+u))`. -/
noncomputable def r00001 (x : ℝ) : ℝ :=
  (4 + 16 * x + 8 * x ^ 2 + 16 * x ^ 3 + 4 * x ^ 4) / (3 * (1 + x) ^ 4)

/-- Coefficient of `00000` in `ρ⁽⁴⁾((1-u)/(1+u))`. -/
noncomputable def r00000 (x : ℝ) : ℝ :=
  (1 + 7 * x - 7 * x ^ 2 - x ^ 3) / (4 * (1 + x) ^ 3)

/-- Coefficient of `10000` in `K̃((1-u)/(1+u))`. -/
noncomputable def k10000 (x : ℝ) : ℝ :=
  (x ^ 2 + x ^ 3) / ((1 - x))

/-- Coefficient of `00100` in `K̃((1-u)/(1+u))`. -/
noncomputable def k00100 (x : ℝ) : ℝ :=
  (1 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3 + x ^ 4) / (x ^ 2)

/-- Coefficient of `00000` in `K̃((1-u)/(1+u))`. -/
noncomputable def k00000 (x : ℝ) : ℝ :=
  (-2 - 3 * x - 2 * x ^ 2) / (2 * x)

/-- The prefactor of `setAJ`. -/
noncomputable def pref (x : ℝ) : ℝ :=
  (1 - x) / (x * (1 + x))

theorem hasDerivAt_h21000 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h21000 (hd21000 u) u := by
  have h := ((((((hasDerivAt_const u (38 : ℝ)).neg.sub ((hasDerivAt_id' u).const_mul
      (66 : ℝ))).add ((hasDerivAt_pow 2 u).const_mul (12 : ℝ))).add
      ((hasDerivAt_pow 3 u).const_mul (68 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul
      (18 : ℝ))).add ((hasDerivAt_pow 5 u).const_mul (6 : ℝ))).div
    ((((hasDerivAt_id' u).const_add 1).pow 3).const_mul (9 : ℝ))
    (by simp only [Pi.pow_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd21000
  simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h20100 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h20100 (hd20100 u) u := by
  have h := ((((((hasDerivAt_const u (44 : ℝ)).neg.sub ((hasDerivAt_id' u).const_mul
      (108 : ℝ))).sub ((hasDerivAt_pow 2 u).const_mul (69 : ℝ))).add
      ((hasDerivAt_pow 3 u).const_mul (9 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (9 : ℝ))).add
      ((hasDerivAt_pow 5 u).const_mul (3 : ℝ))).div
    ((((hasDerivAt_id' u).const_add 1).pow 3).const_mul (9 : ℝ))
    (by simp only [Pi.pow_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd20100
  simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h20000 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h20000 (hd20000 u) u := by
  have h := ((((((hasDerivAt_id' u).const_mul (12 : ℝ)).sub ((hasDerivAt_pow 2 u).const_mul
      (126 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul (308 : ℝ))).sub
      ((hasDerivAt_pow 4 u).const_mul (225 : ℝ))).sub ((hasDerivAt_pow 5 u).const_mul (81 : ℝ))).div
    ((((hasDerivAt_id' u).const_add 1).pow 3).const_mul (54 : ℝ))
    (by simp only [Pi.pow_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd20000
  simp only [Pi.pow_apply, Pi.sub_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h11100 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h11100 (hd11100 u) u := by
  have h := (((((((hasDerivAt_const u (2 : ℝ)).neg.sub ((hasDerivAt_id' u).const_mul (4 : ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (6 : ℝ))).add ((hasDerivAt_pow 3 u).const_mul (24 : ℝ))).sub
      ((hasDerivAt_pow 4 u).const_mul (6 : ℝ))).sub ((hasDerivAt_pow 5 u).const_mul (4 : ℝ))).sub
      ((hasDerivAt_pow 6 u).const_mul (2 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (3 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 2))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd11100
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h11000 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h11000 (hd11000 u) u := by
  have h := ((((((((hasDerivAt_const u (8 : ℝ)).sub ((hasDerivAt_id' u).const_mul (51 : ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (116 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (54 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (60 : ℝ))).add
      ((hasDerivAt_pow 5 u).const_mul (85 : ℝ))).add ((hasDerivAt_pow 6 u).const_mul
      (56 : ℝ))).add ((hasDerivAt_pow 7 u).const_mul (12 : ℝ))).div
    (((hasDerivAt_id' u).const_mul (12 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 4))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd11000
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h10200 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h10200 (hd10200 u) u := by
  have h := (((((((hasDerivAt_const u (1 : ℝ)).neg.sub ((hasDerivAt_id' u).const_mul (2 : ℝ))).sub
      (hasDerivAt_pow 2 u)).add ((hasDerivAt_pow 3 u).const_mul (16 : ℝ))).sub
      (hasDerivAt_pow 4 u)).sub ((hasDerivAt_pow 5 u).const_mul (2 : ℝ))).sub
      (hasDerivAt_pow 6 u)).div
    (((hasDerivAt_pow 2 u).const_mul (3 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 2))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd10200
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h10100 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h10100 (hd10100 u) u := by
  have h := (((((((hasDerivAt_const u (127 : ℝ)).neg.add ((hasDerivAt_id' u).const_mul
      (860 : ℝ))).add ((hasDerivAt_pow 2 u).const_mul (3270 : ℝ))).add
      ((hasDerivAt_pow 3 u).const_mul (4028 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul
      (2321 : ℝ))).add ((hasDerivAt_pow 5 u).const_mul (864 : ℝ))).add
      ((hasDerivAt_pow 6 u).const_mul (216 : ℝ))).div
    ((((hasDerivAt_id' u).const_add 1).pow 4).const_mul (108 : ℝ))
    (by simp only [Pi.pow_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd10100
  simp only [Pi.pow_apply, Pi.add_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h10010 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h10010 (hd10010 u) u := by
  have h := ((((((hasDerivAt_const u (176 : ℝ)).neg.sub ((hasDerivAt_id' u).const_mul
      (432 : ℝ))).sub ((hasDerivAt_pow 2 u).const_mul (276 : ℝ))).add
      ((hasDerivAt_pow 3 u).const_mul (36 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul
      (36 : ℝ))).add ((hasDerivAt_pow 5 u).const_mul (12 : ℝ))).div
    ((((hasDerivAt_id' u).const_add 1).pow 3).const_mul (9 : ℝ))
    (by simp only [Pi.pow_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd10010
  simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h10001 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h10001 (hd10001 u) u := by
  have h := ((((((hasDerivAt_const u (88 : ℝ)).neg.sub ((hasDerivAt_id' u).const_mul
      (216 : ℝ))).sub ((hasDerivAt_pow 2 u).const_mul (138 : ℝ))).add
      ((hasDerivAt_pow 3 u).const_mul (18 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul
      (18 : ℝ))).add ((hasDerivAt_pow 5 u).const_mul (6 : ℝ))).div
    ((((hasDerivAt_id' u).const_add 1).pow 3).const_mul (9 : ℝ))
    (by simp only [Pi.pow_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd10001
  simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h10000 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h10000 (hd10000 u) u := by
  have h := (((((((hasDerivAt_const u (72 : ℝ)).add ((hasDerivAt_id' u).const_mul (248 : ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (917 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (3028 : ℝ))).sub ((hasDerivAt_pow 4 u).const_mul (2646 : ℝ))).sub
      ((hasDerivAt_pow 5 u).const_mul (828 : ℝ))).sub ((hasDerivAt_pow 6 u).const_mul (27 : ℝ))).div
    ((((hasDerivAt_id' u).const_add 1).pow 4).const_mul (216 : ℝ))
    (by simp only [Pi.pow_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd10000
  simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h01100 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h01100 (hd01100 u) u := by
  have h := ((((((hasDerivAt_const u (3 : ℝ)).add ((hasDerivAt_id' u).const_mul (3 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (16 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (16 : ℝ))).sub ((hasDerivAt_pow 4 u).const_mul (3 : ℝ))).sub ((hasDerivAt_pow 5 u).const_mul
      (3 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (3 : ℝ)).mul ((hasDerivAt_id' u).const_add 1))
    (by simp only [Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd01100
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h01000 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h01000 (hd01000 u) u := by
  have h := ((((((hasDerivAt_const u (9 : ℝ)).neg.add ((hasDerivAt_id' u).const_mul (8 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (11 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (11 : ℝ))).sub ((hasDerivAt_pow 4 u).const_mul (8 : ℝ))).add ((hasDerivAt_pow 5 u).const_mul
      (9 : ℝ))).div
    (((hasDerivAt_id' u).const_mul (9 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 3))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd01000
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00200 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h00200 (hd00200 u) u := by
  have h := ((((((hasDerivAt_const u (3 : ℝ)).add ((hasDerivAt_id' u).const_mul (3 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (16 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (16 : ℝ))).sub ((hasDerivAt_pow 4 u).const_mul (3 : ℝ))).sub ((hasDerivAt_pow 5 u).const_mul
      (3 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (6 : ℝ)).mul ((hasDerivAt_id' u).const_add 1))
    (by simp only [Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00200
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00110 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h00110 (hd00110 u) u := by
  have h := (((((((hasDerivAt_const u (4 : ℝ)).neg.sub ((hasDerivAt_id' u).const_mul (8 : ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (4 : ℝ))).add ((hasDerivAt_pow 3 u).const_mul (64 : ℝ))).sub
      ((hasDerivAt_pow 4 u).const_mul (4 : ℝ))).sub ((hasDerivAt_pow 5 u).const_mul (8 : ℝ))).sub
      ((hasDerivAt_pow 6 u).const_mul (4 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (3 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 2))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00110
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00101 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h00101 (hd00101 u) u := by
  have h := (((((((hasDerivAt_const u (2 : ℝ)).neg.sub ((hasDerivAt_id' u).const_mul (4 : ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (2 : ℝ))).add ((hasDerivAt_pow 3 u).const_mul (32 : ℝ))).sub
      ((hasDerivAt_pow 4 u).const_mul (2 : ℝ))).sub ((hasDerivAt_pow 5 u).const_mul (4 : ℝ))).sub
      ((hasDerivAt_pow 6 u).const_mul (2 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (3 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 2))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00101
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00100 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h00100 (hd00100 u) u := by
  have h := ((((((((hasDerivAt_const u (9 : ℝ)).neg.sub ((hasDerivAt_id' u).const_mul
      (195 : ℝ))).sub ((hasDerivAt_pow 2 u).const_mul (703 : ℝ))).sub
      ((hasDerivAt_pow 3 u).const_mul (541 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul
      (541 : ℝ))).add ((hasDerivAt_pow 5 u).const_mul (703 : ℝ))).add
      ((hasDerivAt_pow 6 u).const_mul (195 : ℝ))).add ((hasDerivAt_pow 7 u).const_mul (9 : ℝ))).div
    (((hasDerivAt_pow 2 u).const_mul (72 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 3))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00100
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00010 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h00010 (hd00010 u) u := by
  have h := (((((((hasDerivAt_const u (48 : ℝ)).sub ((hasDerivAt_id' u).const_mul (69 : ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (4 : ℝ))).add ((hasDerivAt_pow 3 u).const_mul
      (130 : ℝ))).sub ((hasDerivAt_pow 4 u).const_mul (4 : ℝ))).sub
      ((hasDerivAt_pow 5 u).const_mul (69 : ℝ))).add ((hasDerivAt_pow 6 u).const_mul (48 : ℝ))).div
    (((hasDerivAt_id' u).const_mul (36 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 4))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00010
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00001 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h00001 (hd00001 u) u := by
  have h := (((((((hasDerivAt_const u (72 : ℝ)).add ((hasDerivAt_id' u).const_mul (575 : ℝ))).add
      ((hasDerivAt_pow 2 u).const_mul (2708 : ℝ))).add ((hasDerivAt_pow 3 u).const_mul
      (4266 : ℝ))).add ((hasDerivAt_pow 4 u).const_mul (2708 : ℝ))).add
      ((hasDerivAt_pow 5 u).const_mul (575 : ℝ))).add ((hasDerivAt_pow 6 u).const_mul (72 : ℝ))).div
    (((hasDerivAt_id' u).const_mul (108 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 4))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00001
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_h00000 {u : ℝ} (h0 : 0 < u) :
    HasDerivAt h00000 (hd00000 u) u := by
  have h := ((((((hasDerivAt_const u (27 : ℝ)).sub ((hasDerivAt_id' u).const_mul (1846 : ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (3701 : ℝ))).sub ((hasDerivAt_pow 3 u).const_mul
      (2080 : ℝ))).sub ((hasDerivAt_pow 4 u).const_mul (81 : ℝ))).sub
      ((hasDerivAt_pow 5 u).const_mul (27 : ℝ))).div
    (((hasDerivAt_id' u).const_mul (216 : ℝ)).mul (((hasDerivAt_id' u).const_add 1).pow 3))
    (by simp only [Pi.pow_apply, Pi.mul_apply]; positivity)
  refine h.congr_deriv ?_
  unfold hd00000
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply]
  push_cast
  field_simp
  ring


private theorem ksDelta_aux {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    1 - ksDelta u = 2 * u / (1 + u) ∧ 1 + ksDelta u = 2 / (1 + u) ∧
      1 - ksDelta u ^ 2 = 4 * u / (1 + u) ^ 2 := by
  have hp : 1 + u ≠ 0 := by linarith [hu.1]
  unfold ksDelta
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem ksRhoU_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ksRhoU u = r11000 u * log u * log (1 - u) + r10100 u * log u * log (1 + u) + r10000 u * log u
        + r01000 u * log (1 - u) + r00100 u * log (1 + u) + r00010 u * Li 2 u + r00001 u * Li 2
        (-u) + r00000 u := by
  have hp : 1 + u ≠ 0 := by linarith [hu.1]
  unfold ksRhoU ksDelta r10000 r11000 r10100 r01000 r00100 r00000 r00010 r00001
  simp only [Li_two]
  field_simp
  ring

theorem setAKtU_eq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    setAKtU u = k10000 u * log u + k00100 u * log (1 + u) + k00000 u := by
  obtain ⟨e1, e2, e3⟩ := ksDelta_aux hu
  have h0 : u ≠ 0 := hu.1.ne'
  have hp : 1 + u ≠ 0 := by linarith [hu.1]
  have hm : 1 - u ≠ 0 := by linarith [hu.2]
  unfold setAKtU
  rw [e1, e2, e3]
  unfold ksDelta k00000 k10000 k00100
  field_simp
  ring

theorem setAJ_eq_atoms {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    setAJ u = pref u * (r11000 u * log u * log (1 - u) + r10100 u * log u * log (1 + u)
        + r10000 u * log u + r01000 u * log (1 - u) + r00100 u * log (1 + u) + r00010 u * Li 2 u
        + r00001 u * Li 2 (-u) + r00000 u) *
      (k10000 u * log u + k00100 u * log (1 + u) + k00000 u) := by
  obtain ⟨e1, e2, e3⟩ := ksDelta_aux hu
  have h0 : u ≠ 0 := hu.1.ne'
  have hp : 1 + u ≠ 0 := by linarith [hu.1]
  have hpref : 2 / (1 + u) ^ 2 * (2 * ksDelta u / (1 - ksDelta u ^ 2)) = pref u := by
    rw [e3]
    unfold ksDelta pref
    field_simp
    ring
  unfold setAJ
  rw [hpref, ksRhoU_eq hu, setAKtU_eq hu]

end SetAW1

open SetAW1

/-- The rational-coefficient antiderivative `G₁`. -/
noncomputable def setAG1 (x : ℝ) : ℝ :=
  h21000 x * (log x ^ 2 * log (1 - x)) +
    h20100 x * (log x ^ 2 * log (1 + x)) +
    h20000 x * (log x ^ 2) +
    h11100 x * (log x * log (1 - x) * log (1 + x)) +
    h11000 x * (log x * log (1 - x)) +
    h10200 x * (log x * log (1 + x) ^ 2) +
    h10100 x * (log x * log (1 + x)) +
    h10010 x * (log x * Li 2 x) +
    h10001 x * (log x * Li 2 (-x)) +
    h10000 x * (log x) +
    h01100 x * (log (1 - x) * log (1 + x)) +
    h01000 x * (log (1 - x)) +
    h00200 x * (log (1 + x) ^ 2) +
    h00110 x * (log (1 + x) * Li 2 x) +
    h00101 x * (log (1 + x) * Li 2 (-x)) +
    h00100 x * (log (1 + x)) +
    h00010 x * (Li 2 x) +
    h00001 x * (Li 2 (-x)) +
    h00000 x

/-- The derivative of `G₁`: `setAJ - g₃ - g₄` with `g₄ = -(8/3) Φ ψ'`. -/
noncomputable def setAg1 (u : ℝ) : ℝ :=
  setAJ u - setAg3 u + 8 / 3 * (setAPhi u * setAPsiD u)

theorem hasDerivAt_setAG1 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt setAG1 (setAg1 u) u := by
  obtain ⟨h0, h1⟩ := hu
  have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
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
  have t0 := (hasDerivAt_h21000 h0).mul ((e0.pow 2).mul e1)
  have t1 := (hasDerivAt_h20100 h0).mul ((e0.pow 2).mul em)
  have t2 := (hasDerivAt_h20000 h0).mul (e0.pow 2)
  have t3 := (hasDerivAt_h11100 h0).mul ((e0.mul e1).mul em)
  have t4 := (hasDerivAt_h11000 h0).mul (e0.mul e1)
  have t5 := (hasDerivAt_h10200 h0).mul (e0.mul (em.pow 2))
  have t6 := (hasDerivAt_h10100 h0).mul (e0.mul em)
  have t7 := (hasDerivAt_h10010 h0).mul (e0.mul qP)
  have t8 := (hasDerivAt_h10001 h0).mul (e0.mul qM)
  have t9 := (hasDerivAt_h10000 h0).mul e0
  have t10 := (hasDerivAt_h01100 h0).mul (e1.mul em)
  have t11 := (hasDerivAt_h01000 h0).mul e1
  have t12 := (hasDerivAt_h00200 h0).mul (em.pow 2)
  have t13 := (hasDerivAt_h00110 h0).mul (em.mul qP)
  have t14 := (hasDerivAt_h00101 h0).mul (em.mul qM)
  have t15 := (hasDerivAt_h00100 h0).mul em
  have t16 := (hasDerivAt_h00010 h0).mul qP
  have t17 := (hasDerivAt_h00001 h0).mul qM
  have t18 := hasDerivAt_h00000 h0
  have h :=
      ((((((((((((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add t7).add t8).add
      t9).add t10).add t11).add t12).add t13).add t14).add t15).add t16).add t17).add t18)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hp : 1 + u ≠ 0 := by linarith
  have hm : 1 - u ≠ 0 := by linarith
  have hz : u ≠ 0 := h0.ne'
  have c0 : hd21000 u = 16*(1 + u)⁻¹/3 + k10000 u*pref u*r11000 u := by
    simp only [hd21000, k10000, pref, r11000]
    field_simp
    ring
  have c1 : hd20100 u = 8*(1 + u)⁻¹/3 + k10000 u*pref u*r10100 u := by
    simp only [hd20100, k10000, pref, r10100]
    field_simp
    ring
  have c2 : h20100 u*(1 + u)⁻¹ - h21000 u*(1 - u)⁻¹ + hd20000 u = -4*(1 + u)⁻¹/9
      + k10000 u*pref u*r10000 u := by
    simp only [h20100, h21000, hd20000, k10000, pref, r10000]
    field_simp
    ring
  have c3 : hd11100 u = -32*(1 + u)⁻¹/3 + 16*u⁻¹/3 + k00100 u*pref u*r11000 u := by
    simp only [hd11100, k00100, pref, r11000]
    field_simp
    ring
  have c4 : -h10010 u*u⁻¹ + h11100 u*(1 + u)⁻¹ + 2*h21000 u*u⁻¹ + hd11000 u = 20*(1 + u)⁻¹/3
      + 100*u⁻¹/9 + k00000 u*pref u*r11000 u + k10000 u*pref u*r01000 u := by
    simp only [h10010, h11100, h21000, hd11000, k00000, k10000, pref, r01000, r11000]
    field_simp
    ring
  have c5 : hd10200 u = -16*(1 + u)⁻¹/3 + 8*u⁻¹/3 + k00100 u*pref u*r10100 u := by
    simp only [hd10200, k00100, pref, r10100]
    field_simp
    ring
  have c6 : -h10001 u*u⁻¹ + 2*h10200 u*(1 + u)⁻¹ - h11100 u*(1 - u)⁻¹ + 2*h20100 u*u⁻¹
      + hd10100 u = 8*(1 + u)⁻¹/3 + 6*u⁻¹ + k00000 u*pref u*r10100 u + k00100 u*pref u*r10000 u
      + k10000 u*pref u*r00100 u := by
    simp only [h10001, h10200, h11100, h20100, hd10100, k00000, k00100, k10000, pref, r00100,
        r10000, r10100]
    field_simp
    ring
  have c7 : hd10010 u = 32*(1 + u)⁻¹/3 + k10000 u*pref u*r00010 u := by
    simp only [hd10010, k10000, pref, r00010]
    field_simp
    ring
  have c8 : hd10001 u = 16*(1 + u)⁻¹/3 + k10000 u*pref u*r00001 u := by
    simp only [hd10001, k10000, pref, r00001]
    field_simp
    ring
  have c9 : h10100 u*(1 + u)⁻¹ - h11000 u*(1 - u)⁻¹ + 2*h20000 u*u⁻¹
      + hd10000 u = k00000 u*pref u*r10000 u + k10000 u*pref u*r00000 u := by
    simp only [h10100, h11000, h20000, hd10000, k00000, k10000, pref, r00000, r10000]
    field_simp
    ring
  have c10 : -h00110 u*u⁻¹ + h11100 u*u⁻¹ + hd01100 u = -28*u⁻¹/3 + k00100 u*pref u*r01000 u := by
    simp only [h00110, h11100, hd01100, k00100, pref, r01000]
    field_simp
    ring
  have c11 : -h00010 u*u⁻¹ + h01100 u*(1 + u)⁻¹ + h11000 u*u⁻¹
      + hd01000 u = k00000 u*pref u*r01000 u := by
    simp only [h00010, h01100, h11000, hd01000, k00000, pref, r01000]
    field_simp
    ring
  have c12 : -h00101 u*u⁻¹ + h10200 u*u⁻¹ + hd00200 u = -4*u⁻¹ + k00100 u*pref u*r00100 u := by
    simp only [h00101, h10200, hd00200, k00100, pref, r00100]
    field_simp
    ring
  have c13 : hd00110 u = -64*(1 + u)⁻¹/3 + 32*u⁻¹/3 + k00100 u*pref u*r00010 u := by
    simp only [hd00110, k00100, pref, r00010]
    field_simp
    ring
  have c14 : hd00101 u = -32*(1 + u)⁻¹/3 + 16*u⁻¹/3 + k00100 u*pref u*r00001 u := by
    simp only [hd00101, k00100, pref, r00001]
    field_simp
    ring
  have c15 : -h00001 u*u⁻¹ + 2*h00200 u*(1 + u)⁻¹ - h01100 u*(1 - u)⁻¹ + h10100 u*u⁻¹
      + hd00100 u = k00000 u*pref u*r00100 u + k00100 u*pref u*r00000 u := by
    simp only [h00001, h00200, h01100, h10100, hd00100, k00000, k00100, pref, r00000, r00100]
    field_simp
    ring
  have c16 : h00110 u*(1 + u)⁻¹ + h10010 u*u⁻¹ + hd00010 u = 176*(1 + u)⁻¹/9 - 176*u⁻¹/9
      + k00000 u*pref u*r00010 u := by
    simp only [h00110, h10010, hd00010, k00000, pref, r00010]
    field_simp
    ring
  have c17 : h00101 u*(1 + u)⁻¹ + h10001 u*u⁻¹ + hd00001 u = 88*(1 + u)⁻¹/9 - 88*u⁻¹/9
      + k00000 u*pref u*r00001 u := by
    simp only [h00101, h10001, hd00001, k00000, pref, r00001]
    field_simp
    ring
  have c18 : h00100 u*(1 + u)⁻¹ - h01000 u*(1 - u)⁻¹ + h10000 u*u⁻¹
      + hd00000 u = k00000 u*pref u*r00000 u := by
    simp only [h00100, h01000, h10000, hd00000, k00000, pref, r00000]
    field_simp
    ring
  rw [setAg1, setAJ_eq_atoms hu]
  unfold setAg3 setAPhi setAPsiD
  linear_combination log u ^ 2 * log (1 - u) * c0 + log u ^ 2 * log (1 + u) * c1 + log u ^ 2 * c2
      + log u * log (1 - u) * log (1 + u) * c3 + log u * log (1 - u) * c4 + log u * log (1
      + u) ^ 2 * c5 + log u * log (1 + u) * c6 + log u * Li 2 u * c7 + log u * Li 2 (-u) * c8
      + log u * c9 + log (1 - u) * log (1 + u) * c10 + log (1 - u) * c11 + log (1 + u) ^ 2 * c12
      + log (1 + u) * Li 2 u * c13 + log (1 + u) * Li 2 (-u) * c14 + log (1 + u) * c15 + Li 2 u
      * c16 + Li 2 (-u) * c17 + c18

end QED.Chain
