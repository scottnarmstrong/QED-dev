/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetCRem
public import QED.Chain.SetCKernel
import QED.Polylog.ExtraIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (c): integrability of the integrand

Helper analysis for the sixth-order set (c) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

Substituting the second-order expansions of the atoms (`QED.Chain.SetCRem`) into the integrand
`QED.Chain.setCJ`, every pole of the coefficients cancels: on `(0, 1)`, `setCJ x = T₀(x)` and
`setCJ (1 - y) = T₁(y)`, sums of terms `d(x) logʲ x r(x)` with `d` rational (poles only at
`1, -1, 2`), `j ≤ 2` and `r` a product of bounded remainders. Hence `|setCJ x|` is
`O(1 + log² x)` near `0` and `O(1 + log² (1 - x))` near `1`, and `setCJ` is integrable on
`[0, 1]`. Generator: `scratchpad/setC/gen_lim.py J`.

## Main statements

* `QED.Chain.continuousAt_setCJ`: `setCJ` is continuous on `(0, 1)`.
* `QED.Chain.intervalIntegrable_setCJ`: `setCJ` is integrable on `[0, 1]`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Chain.SetCKernel QED.Chain.SetCRem

namespace QED.Chain

namespace SetCJInt

/-- Expansion coefficient `21000` of `setCJ` at 0. -/
noncomputable def jz21000 (x : ℝ) : ℝ :=
  (-3 + 11 * x + x ^ 2 - 5 * x ^ 3 + 16 * x ^ 4 - 5 * x ^ 5 + x ^ 6 + 11 * x ^ 7 - 3 * x ^ 8) /
      (9 * (1 - x) ^ 4)

/-- Expansion coefficient `20100` of `setCJ` at 0. -/
noncomputable def jz20100 (x : ℝ) : ℝ :=
  (-6 + 22 * x + 2 * x ^ 2 - 10 * x ^ 3 + 32 * x ^ 4 - 10 * x ^ 5 + 2 * x ^ 6 + 22 * x ^ 7 - 6
      * x ^ 8) / (9 * (1 - x) ^ 4)

/-- Expansion coefficient `20000` of `setCJ` at 0. -/
noncomputable def jz20000 (x : ℝ) : ℝ :=
  (2 - 17 * x + 50 * x ^ 2 - 16 * x ^ 3 - 149 * x ^ 4 + 35 * x ^ 5 - 12 * x ^ 6 - 30 * x ^ 7 + 9
      * x ^ 8) / (18 * (1 + x) * (1 - x) ^ 4)

/-- Expansion coefficient `11000` of `setCJ` at 0. -/
noncomputable def jz11000 (x : ℝ) : ℝ :=
  (-12 + 68 * x - 29 * x ^ 2 + 31 * x ^ 3 + 113 * x ^ 4 - 27 * x ^ 5) / (54 * (1 - x))

/-- Expansion coefficient `10100` of `setCJ` at 0. -/
noncomputable def jz10100 (x : ℝ) : ℝ :=
  (-39 + 181 * x + 2 * x ^ 2 + 2 * x ^ 3 + 181 * x ^ 4 - 39 * x ^ 5) / (54 * (1 - x))

/-- Expansion coefficient `10010` of `setCJ` at 0. -/
noncomputable def jz10010 (x : ℝ) : ℝ :=
  (-6 + 22 * x + 2 * x ^ 2 - 10 * x ^ 3 + 32 * x ^ 4 - 10 * x ^ 5 + 2 * x ^ 6 + 22 * x ^ 7 - 6
      * x ^ 8) / (9 * (1 - x) ^ 4)

/-- Expansion coefficient `10001` of `setCJ` at 0. -/
noncomputable def jz10001 (x : ℝ) : ℝ :=
  (-12 + 44 * x + 4 * x ^ 2 - 20 * x ^ 3 + 64 * x ^ 4 - 20 * x ^ 5 + 4 * x ^ 6 + 44 * x ^ 7 - 12
      * x ^ 8) / (9 * (1 - x) ^ 4)

/-- Expansion coefficient `10000` of `setCJ` at 0. -/
noncomputable def jz10000 (x : ℝ) : ℝ :=
  (28 - 117 * x + 165 * x ^ 2 - 387 * x ^ 3 - 489 * x ^ 4 + 837 * x ^ 5 - 505 * x ^ 6 - 33
      * x ^ 7 + 273 * x ^ 8 - 60 * x ^ 9) / (54 * (1 + x) ^ 2 * (1 - x) ^ 4)

/-- Expansion coefficient `01000` of `setCJ` at 0. -/
noncomputable def jz01000 (x : ℝ) : ℝ :=
  (30 - 142 * x + 69 * x ^ 2 + 52 * x ^ 3 - 176 * x ^ 4 + 18 * x ^ 5 + 5 * x ^ 6) / (54 * (1
      - x) ^ 2)

/-- Expansion coefficient `00100` of `setCJ` at 0. -/
noncomputable def jz00100 (x : ℝ) : ℝ :=
  (35 - 124 * x - 107 * x ^ 2 + 104 * x ^ 3 - 107 * x ^ 4 - 124 * x ^ 5 + 35 * x ^ 6) / (54 * (1
      - x) ^ 2)

/-- Expansion coefficient `00010` of `setCJ` at 0. -/
noncomputable def jz00010 (x : ℝ) : ℝ :=
  (-30 + 152 * x - 138 * x ^ 2 + 88 * x ^ 3 + 88 * x ^ 4 - 138 * x ^ 5 + 152 * x ^ 6 - 30
      * x ^ 7) / (27 * (1 - x) ^ 3)

/-- Expansion coefficient `00001` of `setCJ` at 0. -/
noncomputable def jz00001 (x : ℝ) : ℝ :=
  (-60 + 304 * x - 276 * x ^ 2 + 176 * x ^ 3 + 176 * x ^ 4 - 276 * x ^ 5 + 304 * x ^ 6 - 60
      * x ^ 7) / (27 * (1 - x) ^ 3)

/-- Expansion coefficient `00000` of `setCJ` at 0. -/
noncomputable def jz00000 (x : ℝ) : ℝ :=
  (30 - 102 * x - 182 * x ^ 2 + 437 * x ^ 3 - 272 * x ^ 4 - 190 * x ^ 5 + 160 * x ^ 6 - 25
      * x ^ 7) / (54 * (1 + x) * (1 - x) ^ 3)

/-- The expansion of `setCJ` at 0. -/
noncomputable def jzSum (x : ℝ) : ℝ :=
  jz21000 x * log x ^ 2 * (remA x) +
    jz20100 x * log x ^ 2 * (remB x) +
    jz20000 x * log x ^ 2 * (1) +
    jz11000 x * log x ^ 1 * (remA x) +
    jz10100 x * log x ^ 1 * (remB x) +
    jz10010 x * log x ^ 1 * (remC x) +
    jz10001 x * log x ^ 1 * (remD x) +
    jz10000 x * log x ^ 1 * (1) +
    jz01000 x * log x ^ 0 * (remA x) +
    jz00100 x * log x ^ 0 * (remB x) +
    jz00010 x * log x ^ 0 * (remC x) +
    jz00001 x * log x ^ 0 * (remD x) +
    jz00000 x * log x ^ 0 * (1)

theorem jz_e0 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j21000 x * x ^ 3 = jz21000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j21000, jz21000]
  field_simp

theorem jz_e1 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j20100 x * x ^ 3 = jz20100 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j20100, jz20100]
  field_simp

theorem jz_e2 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    -j21000 x * x - 1 / 2 * j21000 x * x ^ 2 + j20100 x * x - 1 / 2 * j20100 x * x ^ 2
        + j20000 x = jz20000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j20000, j20100, j21000, jz20000]
  field_simp
  ring

theorem jz_e3 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j11000 x * x ^ 3 = jz11000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j11000, jz11000]
  field_simp

theorem jz_e4 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j10100 x * x ^ 3 = jz10100 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j10100, jz10100]
  field_simp

theorem jz_e5 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j10010 x * x ^ 3 = jz10010 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j10010, jz10010]
  field_simp

theorem jz_e6 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j10001 x * x ^ 3 = jz10001 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j10001, jz10001]
  field_simp

theorem jz_e7 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    -j11000 x * x - 1 / 2 * j11000 x * x ^ 2 + j10100 x * x - 1 / 2 * j10100 x * x ^ 2 + j10010 x
        * x + 1 / 4 * j10010 x * x ^ 2 - j10001 x * x + 1 / 4 * j10001 x * x ^ 2
        + j10000 x = jz10000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j10000, j10001, j10010, j10100, j11000, jz10000]
  field_simp
  ring

theorem jz_e8 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j01000 x * x ^ 3 = jz01000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j01000, jz01000]
  field_simp

theorem jz_e9 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j00100 x * x ^ 3 = jz00100 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j00100, jz00100]
  field_simp

theorem jz_e10 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j00010 x * x ^ 3 = jz00010 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j00010, jz00010]
  field_simp

theorem jz_e11 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    j00001 x * x ^ 3 = jz00001 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j00001, jz00001]
  field_simp

theorem jz_e12 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    -j01000 x * x - 1 / 2 * j01000 x * x ^ 2 + j00100 x * x - 1 / 2 * j00100 x * x ^ 2 + j00010 x
        * x + 1 / 4 * j00010 x * x ^ 2 - j00001 x * x + 1 / 4 * j00001 x * x ^ 2
        + j00000 x = jz00000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [j00000, j00001, j00010, j00100, j01000, jz00000]
  field_simp
  ring

theorem setCJ_eq_near_zero {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    setCJ x = jzSum x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  unfold setCJ jzSum
  rw [log_one_sub_eq h0, log_one_add_eq h0, Li_two_neg_eq h0, Li_two_eq h0]
  linear_combination log x ^ 2 * remA x * (jz_e0 h0 h1) + log x ^ 2 * remB x * (jz_e1 h0 h1)
      + log x ^ 2 * (jz_e2 h0 h1) + log x ^ 1 * remA x * (jz_e3 h0 h1) + log x ^ 1 * remB x *
      (jz_e4 h0 h1) + log x ^ 1 * remC x * (jz_e5 h0 h1) + log x ^ 1 * remD x * (jz_e6 h0 h1)
      + log x ^ 1 * (jz_e7 h0 h1) + remA x * (jz_e8 h0 h1) + remB x * (jz_e9 h0 h1) + remC x *
      (jz_e10 h0 h1) + remD x * (jz_e11 h0 h1) + (jz_e12 h0 h1)

theorem logSqBound_jzSum : LogSqBound jzSum := by
  have bddC := @Bdd.of_continuousAt
  have t0 := logSqBound_term (d := jz21000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz21000; fun_prop (disch := simp [*])) bdd_remA (j := 2) (by norm_num)
  have t1 := logSqBound_term (d := jz20100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz20100; fun_prop (disch := simp [*])) bdd_remB (j := 2) (by norm_num)
  have t2 := logSqBound_term (d := jz20000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz20000; fun_prop (disch := simp [*])) bdd_one (j := 2) (by norm_num)
  have t3 := logSqBound_term (d := jz11000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz11000; fun_prop (disch := simp [*])) bdd_remA (j := 1) (by norm_num)
  have t4 := logSqBound_term (d := jz10100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz10100; fun_prop (disch := simp [*])) bdd_remB (j := 1) (by norm_num)
  have t5 := logSqBound_term (d := jz10010) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz10010; fun_prop (disch := simp [*])) bdd_remC (j := 1) (by norm_num)
  have t6 := logSqBound_term (d := jz10001) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz10001; fun_prop (disch := simp [*])) bdd_remD (j := 1) (by norm_num)
  have t7 := logSqBound_term (d := jz10000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz10000; fun_prop (disch := simp [*])) bdd_one (j := 1) (by norm_num)
  have t8 := logSqBound_term (d := jz01000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz01000; fun_prop (disch := simp [*])) bdd_remA (j := 0) (by norm_num)
  have t9 := logSqBound_term (d := jz00100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz00100; fun_prop (disch := simp [*])) bdd_remB (j := 0) (by norm_num)
  have t10 := logSqBound_term (d := jz00010) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz00010; fun_prop (disch := simp [*])) bdd_remC (j := 0) (by norm_num)
  have t11 := logSqBound_term (d := jz00001) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz00001; fun_prop (disch := simp [*])) bdd_remD (j := 0) (by norm_num)
  have t12 := logSqBound_term (d := jz00000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jz00000; fun_prop (disch := simp [*])) bdd_one (j := 0) (by norm_num)
  exact ((((((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add
      t10).add t11).add t12)

/-- Expansion coefficient `12000` of `setCJ` at 1. -/
noncomputable def jo12000 (x : ℝ) : ℝ :=
  (-24 * x ^ 2 + 96 * x ^ 3 - 194 * x ^ 4 + 246 * x ^ 5 - 181 * x ^ 6 + 64 * x ^ 7 + 6 * x ^ 8
      - 13 * x ^ 9 + 3 * x ^ 10) / (9 * (1 - x) ^ 3)

/-- Expansion coefficient `11000` of `setCJ` at 1. -/
noncomputable def jo11000 (x : ℝ) : ℝ :=
  (48 * x ^ 2 - 108 * x ^ 3 - 88 * x ^ 4 + 393 * x ^ 5 - 362 * x ^ 6 + 87 * x ^ 7 + 42 * x ^ 8
      - 18 * x ^ 9) / (54 * (1 - x) ^ 3)

/-- Expansion coefficient `10000` of `setCJ` at 1. -/
noncomputable def jo10000 (x : ℝ) : ℝ :=
  (64 * x ^ 2 - 128 * x ^ 3 + 44 * x ^ 4 + 80 * x ^ 5 - 69 * x ^ 6 - 3 * x ^ 7 + 9 * x ^ 8) /
      (108 * (1 - x) ^ 3)

/-- Expansion coefficient `02100` of `setCJ` at 1. -/
noncomputable def jo02100 (x : ℝ) : ℝ :=
  (-24 * x ^ 5 + 96 * x ^ 6 - 194 * x ^ 7 + 246 * x ^ 8 - 181 * x ^ 9 + 64 * x ^ 10 + 6 * x ^ 11
      - 13 * x ^ 12 + 3 * x ^ 13) / (36 * (1 - x) ^ 3)

/-- Expansion coefficient `02000` of `setCJ` at 1. -/
noncomputable def jo02000 (x : ℝ) : ℝ :=
  (-160 * x ^ 2 - 384 * x ^ 2 * log 2 + 1336 * x ^ 3 + 1728 * x ^ 3 * log 2 - 4376 * x ^ 4 - 3872
      * x ^ 4 * log 2 + 7708 * x ^ 5 + 5488 * x ^ 5 * log 2 - 7880 * x ^ 6 - 4864 * x ^ 6 * log 2
      + 4406 * x ^ 7 + 2472 * x ^ 7 * log 2 - 862 * x ^ 8 - 416 * x ^ 8 * log 2 - 445 * x ^ 9
      - 256 * x ^ 9 * log 2 + 322 * x ^ 10 + 152 * x ^ 10 * log 2 - 60 * x ^ 11 - 24 * x ^ 11
      * log 2 - 7 * x ^ 12 + 3 * x ^ 13) / (36 * (2 - x) * (1 - x) ^ 3)

/-- Expansion coefficient `01100` of `setCJ` at 1. -/
noncomputable def jo01100 (x : ℝ) : ℝ :=
  (96 * x ^ 5 - 96 * x ^ 6 - 416 * x ^ 7 + 876 * x ^ 8 - 694 * x ^ 9 + 159 * x ^ 10 + 84 * x ^ 11
      - 36 * x ^ 12) / (432 * (1 - x) ^ 3)

/-- Expansion coefficient `01010` of `setCJ` at 1. -/
noncomputable def jo01010 (x : ℝ) : ℝ :=
  (48 * x ^ 2 - 192 * x ^ 3 + 388 * x ^ 4 - 492 * x ^ 5 + 362 * x ^ 6 - 128 * x ^ 7 - 12 * x ^ 8
      + 26 * x ^ 9 - 6 * x ^ 10) / (9 * (1 - x) ^ 3)

/-- Expansion coefficient `01001` of `setCJ` at 1. -/
noncomputable def jo01001 (x : ℝ) : ℝ :=
  (-384 * x ^ 2 + 2112 * x ^ 3 - 5696 * x ^ 4 + 9792 * x ^ 5 - 11320 * x ^ 6 + 8708 * x ^ 7
      - 4104 * x ^ 8 + 778 * x ^ 9 + 304 * x ^ 10 - 240 * x ^ 11 + 62 * x ^ 12 - 6 * x ^ 13) / (9
      * (1 - x) ^ 3)

/-- Expansion coefficient `01000` of `setCJ` at 1. -/
noncomputable def jo01000 (x : ℝ) : ℝ :=
  (1152 - 9792 * x + 32608 * x ^ 2 + 3072 * x ^ 2 * log 2 - 56208 * x ^ 3 - 6144 * x ^ 3 * log 2
      + 58048 * x ^ 4 - 9472 * x ^ 4 * log 2 - 54696 * x ^ 5 + 40576 * x ^ 5 * log 2 + 74248
      * x ^ 6 - 53568 * x ^ 6 * log 2 - 85708 * x ^ 7 + 34304 * x ^ 7 * log 2 + 56840 * x ^ 8
      - 7952 * x ^ 8 * log 2 - 16580 * x ^ 9 - 2568 * x ^ 9 * log 2 - 2138 * x ^ 10 + 1824
      * x ^ 10 * log 2 + 3225 * x ^ 11 - 288 * x ^ 11 * log 2 - 972 * x ^ 12 + 108 * x ^ 13) /
      (432 * (2 - x) ^ 2 * (1 - x) ^ 3)

/-- Expansion coefficient `00100` of `setCJ` at 1. -/
noncomputable def jo00100 (x : ℝ) : ℝ :=
  (128 * x ^ 5 - 176 * x ^ 6 - 12 * x ^ 7 + 160 * x ^ 8 - 123 * x ^ 9 - 6 * x ^ 10 + 18
      * x ^ 11) / (864 * (1 - x) ^ 3)

/-- Expansion coefficient `00010` of `setCJ` at 1. -/
noncomputable def jo00010 (x : ℝ) : ℝ :=
  (48 * x ^ 2 - 156 * x ^ 3 + 280 * x ^ 4 - 303 * x ^ 5 + 170 * x ^ 6 - 30 * x ^ 7 - 21 * x ^ 8
      + 9 * x ^ 9) / (27 * (1 - x) ^ 3)

/-- Expansion coefficient `00001` of `setCJ` at 1. -/
noncomputable def jo00001 (x : ℝ) : ℝ :=
  (-384 * x ^ 2 + 1824 * x ^ 3 - 4400 * x ^ 4 + 6768 * x ^ 5 - 6832 * x ^ 6 + 4378 * x ^ 7 - 1515
      * x ^ 8 + 26 * x ^ 9 + 204 * x ^ 10 - 75 * x ^ 11 + 9 * x ^ 12) / (27 * (1 - x) ^ 3)

/-- Expansion coefficient `00000` of `setCJ` at 1. -/
noncomputable def jo00000 (x : ℝ) : ℝ :=
  (768 - 5952 * x + 18272 * x ^ 2 + 4096 * x ^ 2 * log 2 - 31664 * x ^ 3 - 9728 * x ^ 3 * log 2
      + 39384 * x ^ 4 + 6272 * x ^ 4 * log 2 - 48264 * x ^ 5 + 4096 * x ^ 5 * log 2 + 55316
      * x ^ 6 - 9152 * x ^ 6 * log 2 - 42372 * x ^ 7 + 5024 * x ^ 7 * log 2 + 16636 * x ^ 8 - 216
      * x ^ 8 * log 2 - 692 * x ^ 9 - 624 * x ^ 9 * log 2 - 2037 * x ^ 10 + 144 * x ^ 10 * log 2
      + 750 * x ^ 11 - 90 * x ^ 12) / (864 * (2 - x) ^ 2 * (1 - x) ^ 3)

/-- The expansion of `setCJ` at 1. -/
noncomputable def joSum (x : ℝ) : ℝ :=
  jo12000 x * log x ^ 1 * (remA x * remA x) +
    jo11000 x * log x ^ 1 * (remA x) +
    jo10000 x * log x ^ 1 * (1) +
    jo02100 x * log x ^ 0 * (remA x * remA x * remA (x / 2)) +
    jo02000 x * log x ^ 0 * (remA x * remA x) +
    jo01100 x * log x ^ 0 * (remA x * remA (x / 2)) +
    jo01010 x * log x ^ 0 * (remA x * remC x) +
    jo01001 x * log x ^ 0 * (remA x * remC (x * (2 - x))) +
    jo01000 x * log x ^ 0 * (remA x) +
    jo00100 x * log x ^ 0 * (remA (x / 2)) +
    jo00010 x * log x ^ 0 * (remC x) +
    jo00001 x * log x ^ 0 * (remC (x * (2 - x))) +
    jo00000 x * log x ^ 0 * (1)

theorem jo_e0 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    j21000 (1 - y) * y ^ 6 - j10010 (1 - y) * y ^ 6 = jo12000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j10010, j21000, jo12000]
  field_simp
  ring

theorem jo_e1 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    -2 * j21000 (1 - y) * y ^ 4 - j21000 (1 - y) * y ^ 5 + j11000 (1 - y) * y ^ 3 + 2 * j10010 (1
        - y) * y ^ 4 + j10010 (1 - y) * y ^ 5 - j00010 (1 - y) * y ^ 3 = jo11000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j00010, j10010, j11000, j21000, jo11000]
  field_simp
  ring

theorem jo_e2 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    j21000 (1 - y) * y ^ 2 + j21000 (1 - y) * y ^ 3 + 1 / 4 * j21000 (1 - y) * y ^ 4 - j11000 (1
        - y) * y - 1 / 2 * j11000 (1 - y) * y ^ 2 - j10010 (1 - y) * y ^ 2 - j10010 (1 - y)
        * y ^ 3 - 1 / 4 * j10010 (1 - y) * y ^ 4 + j01000 (1 - y) + j00010 (1 - y) * y + 1 / 2
        * j00010 (1 - y) * y ^ 2 = jo10000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j00010, j01000, j10010, j11000, j21000, jo10000]
  field_simp
  ring

theorem jo_e3 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    1 / 8 * j20100 (1 - y) * y ^ 9 - 1 / 8 * j10001 (1 - y) * y ^ 9 = jo02100 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j10001, j20100, jo02100]
  field_simp
  ring

theorem jo_e4 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    j20100 (1 - y) * y ^ 6 * log 2 - 1 / 2 * j20100 (1 - y) * y ^ 7 - 1 / 8 * j20100 (1 - y)
        * y ^ 8 + j20000 (1 - y) * y ^ 6 - j10001 (1 - y) * y ^ 6 * log 2 + 1 / 2 * j10001 (1
        - y) * y ^ 7 + 1 / 8 * j10001 (1 - y) * y ^ 8 = jo02000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j10001, j20000, j20100, jo02000]
  field_simp
  ring

theorem jo_e5 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    -1 / 4 * j20100 (1 - y) * y ^ 7 - 1 / 8 * j20100 (1 - y) * y ^ 8 + 1 / 8 * j10100 (1 - y)
        * y ^ 6 + 1 / 4 * j10001 (1 - y) * y ^ 7 + 1 / 8 * j10001 (1 - y) * y ^ 8 - 1 / 8 * j00001
        (1 - y) * y ^ 6 = jo01100 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j00001, j10001, j10100, j20100, jo01100]
  field_simp
  ring

theorem jo_e6 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    -j10010 (1 - y) * y ^ 6 + j10001 (1 - y) * y ^ 6 = jo01010 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j10001, j10010, jo01010]
  field_simp
  ring

theorem jo_e7 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    -4 * j10001 (1 - y) * y ^ 6 + 6 * j10001 (1 - y) * y ^ 7 - 3 * j10001 (1 - y) * y ^ 8 + 1 / 2
        * j10001 (1 - y) * y ^ 9 = jo01001 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j10001, jo01001]
  field_simp
  ring

theorem jo_e8 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    -2 * j20100 (1 - y) * y ^ 4 * log 2 + j20100 (1 - y) * y ^ 5 - j20100 (1 - y) * y ^ 5 * log 2
        + 3 / 4 * j20100 (1 - y) * y ^ 6 + 1 / 8 * j20100 (1 - y) * y ^ 7 - 2 * j20000 (1 - y)
        * y ^ 4 - j20000 (1 - y) * y ^ 5 + j10100 (1 - y) * y ^ 3 * log 2 - 1 / 2 * j10100 (1
        - y) * y ^ 4 - 1 / 8 * j10100 (1 - y) * y ^ 5 + 1 / 6 * j10010 (1 - y) * y ^ 3 * π ^ 2
        - j10010 (1 - y) * y ^ 4 - 1 / 4 * j10010 (1 - y) * y ^ 5 - 1 / 12 * j10001 (1 - y)
        * y ^ 3 * π ^ 2 + 2 * j10001 (1 - y) * y ^ 4 * log 2 - 3 / 4 * j10001 (1 - y) * y ^ 5
        + j10001 (1 - y) * y ^ 5 * log 2 - 1 / 4 * j10001 (1 - y) * y ^ 6 - 1 / 4 * j10001 (1
        - y) * y ^ 7 + j10000 (1 - y) * y ^ 3 - j00001 (1 - y) * y ^ 3 * log 2 + 1 / 2 * j00001
        (1 - y) * y ^ 4 + 1 / 8 * j00001 (1 - y) * y ^ 5 = jo01000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j00001, j10000, j10001, j10010, j10100, j20000, j20100, jo01000]
  field_simp
  ring

theorem jo_e9 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    1 / 8 * j20100 (1 - y) * y ^ 5 + 1 / 8 * j20100 (1 - y) * y ^ 6 + 1 / 32 * j20100 (1 - y)
        * y ^ 7 - 1 / 8 * j10100 (1 - y) * y ^ 4 - 1 / 16 * j10100 (1 - y) * y ^ 5 - 1 / 8
        * j10001 (1 - y) * y ^ 5 - 1 / 8 * j10001 (1 - y) * y ^ 6 - 1 / 32 * j10001 (1 - y)
        * y ^ 7 + 1 / 8 * j00100 (1 - y) * y ^ 3 + 1 / 8 * j00001 (1 - y) * y ^ 4 + 1 / 16
        * j00001 (1 - y) * y ^ 5 = jo00100 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j00001, j00100, j10001, j10100, j20100, jo00100]
  field_simp
  ring

theorem jo_e10 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    j10010 (1 - y) * y ^ 4 + 1 / 2 * j10010 (1 - y) * y ^ 5 - j10001 (1 - y) * y ^ 4 - 1 / 2
        * j10001 (1 - y) * y ^ 5 - j00010 (1 - y) * y ^ 3 + j00001 (1 - y) * y ^ 3 = jo00010 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j00001, j00010, j10001, j10010, jo00010]
  field_simp
  ring

theorem jo_e11 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    4 * j10001 (1 - y) * y ^ 4 - 4 * j10001 (1 - y) * y ^ 5 + j10001 (1 - y) * y ^ 7 - 1 / 4
        * j10001 (1 - y) * y ^ 8 - 4 * j00001 (1 - y) * y ^ 3 + 6 * j00001 (1 - y) * y ^ 4 - 3
        * j00001 (1 - y) * y ^ 5 + 1 / 2 * j00001 (1 - y) * y ^ 6 = jo00001 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j00001, j10001, jo00001]
  field_simp
  ring

theorem jo_e12 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    j20100 (1 - y) * y ^ 2 * log 2 - 1 / 2 * j20100 (1 - y) * y ^ 3 + j20100 (1 - y) * y ^ 3
        * log 2 - 5 / 8 * j20100 (1 - y) * y ^ 4 + 1 / 4 * j20100 (1 - y) * y ^ 4 * log 2 - 1 / 4
        * j20100 (1 - y) * y ^ 5 - 1 / 32 * j20100 (1 - y) * y ^ 6 + j20000 (1 - y) * y ^ 2
        + j20000 (1 - y) * y ^ 3 + 1 / 4 * j20000 (1 - y) * y ^ 4 - j10100 (1 - y) * y * log 2
        + 1 / 2 * j10100 (1 - y) * y ^ 2 - 1 / 2 * j10100 (1 - y) * y ^ 2 * log 2 + 3 / 8 * j10100
        (1 - y) * y ^ 3 + 1 / 16 * j10100 (1 - y) * y ^ 4 - 1 / 6 * j10010 (1 - y) * y * π ^ 2
        + j10010 (1 - y) * y ^ 2 - 1 / 12 * j10010 (1 - y) * y ^ 2 * π ^ 2 + 3 / 4 * j10010 (1
        - y) * y ^ 3 + 1 / 8 * j10010 (1 - y) * y ^ 4 + 1 / 12 * j10001 (1 - y) * y * π ^ 2
        + 1 / 24 * j10001 (1 - y) * y ^ 2 * π ^ 2 - j10001 (1 - y) * y ^ 2 * log 2 + 1 / 4
        * j10001 (1 - y) * y ^ 3 - j10001 (1 - y) * y ^ 3 * log 2 - 1 / 4 * j10001 (1 - y)
        * y ^ 4 * log 2 + 1 / 8 * j10001 (1 - y) * y ^ 5 + 3 / 32 * j10001 (1 - y) * y ^ 6
        - j10000 (1 - y) * y - 1 / 2 * j10000 (1 - y) * y ^ 2 + j00100 (1 - y) * log 2 - 1 / 2
        * j00100 (1 - y) * y - 1 / 8 * j00100 (1 - y) * y ^ 2 + 1 / 6 * j00010 (1 - y) * π ^ 2
        - j00010 (1 - y) * y - 1 / 4 * j00010 (1 - y) * y ^ 2 - 1 / 12 * j00001 (1 - y) * π ^ 2
        + j00001 (1 - y) * y * log 2 - 1 / 4 * j00001 (1 - y) * y ^ 2 + 1 / 2 * j00001 (1 - y)
        * y ^ 2 * log 2 + 1 / 8 * j00001 (1 - y) * y ^ 3 - 3 / 16 * j00001 (1 - y) * y ^ 4
        + j00000 (1 - y) = jo00000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [j00000, j00001, j00010, j00100, j10000, j10001, j10010, j10100, j20000, j20100,
      jo00000]
  field_simp
  ring

theorem setCJ_eq_near_one {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    setCJ (1 - y) = joSum y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  have hw : 0 < y * (2 - y) := by nlinarith
  unfold setCJ joSum
  rw [show 1 - (1 - y) = y by ring, Li_two_neg_one_sub_eq h0 h1, Li_two_one_sub_eq h0 h1,
    log_two_sub_eq h0 h1, log_one_sub_eq h0, Li_two_eq h0, Li_two_eq hw]
  linear_combination log y ^ 1 * remA y * remA y * (jo_e0 h0 h1) + log y ^ 1 * remA y *
      (jo_e1 h0 h1) + log y ^ 1 * (jo_e2 h0 h1) + remA y * remA y * remA (y / 2) * (jo_e3 h0 h1)
      + remA y * remA y * (jo_e4 h0 h1) + remA y * remA (y / 2) * (jo_e5 h0 h1) + remA y * remC y
      * (jo_e6 h0 h1) + remA y * remC (y * (2 - y)) * (jo_e7 h0 h1) + remA y * (jo_e8 h0 h1)
      + remA (y / 2) * (jo_e9 h0 h1) + remC y * (jo_e10 h0 h1) + remC (y * (2 - y)) *
      (jo_e11 h0 h1) + (jo_e12 h0 h1)

theorem logSqBound_joSum : LogSqBound joSum := by
  have bddC := @Bdd.of_continuousAt
  have t0 := logSqBound_term (d := jo12000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo12000; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remA) (j := 1) (by norm_num)
  have t1 := logSqBound_term (d := jo11000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo11000; fun_prop (disch := simp [*])) bdd_remA (j := 1) (by norm_num)
  have t2 := logSqBound_term (d := jo10000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo10000; fun_prop (disch := simp [*])) bdd_one (j := 1) (by norm_num)
  have t3 := logSqBound_term (d := jo02100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo02100; fun_prop (disch := simp [*])) ((bdd_remA.mul bdd_remA).mul bdd_remA_half)
        (j := 0) (by norm_num)
  have t4 := logSqBound_term (d := jo02000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo02000; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remA) (j := 0) (by norm_num)
  have t5 := logSqBound_term (d := jo01100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo01100; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remA_half) (j := 0)
        (by norm_num)
  have t6 := logSqBound_term (d := jo01010) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo01010; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remC) (j := 0) (by norm_num)
  have t7 := logSqBound_term (d := jo01001) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo01001; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remC_w) (j := 0) (by norm_num)
  have t8 := logSqBound_term (d := jo01000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo01000; fun_prop (disch := simp [*])) bdd_remA (j := 0) (by norm_num)
  have t9 := logSqBound_term (d := jo00100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo00100; fun_prop (disch := simp [*])) bdd_remA_half (j := 0) (by norm_num)
  have t10 := logSqBound_term (d := jo00010) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo00010; fun_prop (disch := simp [*])) bdd_remC (j := 0) (by norm_num)
  have t11 := logSqBound_term (d := jo00001) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo00001; fun_prop (disch := simp [*])) bdd_remC_w (j := 0) (by norm_num)
  have t12 := logSqBound_term (d := jo00000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold jo00000; fun_prop (disch := simp [*])) bdd_one (j := 0) (by norm_num)
  exact ((((((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add
      t10).add t11).add t12)

end SetCJInt

open SetCJInt

theorem continuousAt_setCJ {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : ContinuousAt setCJ x := by
  obtain ⟨h0, h1⟩ := hx
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  have cP : ContinuousAt (Li 2) x :=
    (continuousOn_Li le_rfl).continuousAt (Icc_mem_nhds (by linarith) h1)
  have cM : ContinuousAt (Li 2) (-x) :=
    (continuousOn_Li le_rfl).continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  unfold setCJ j21000 j20100 j20000 j11000 j10100 j10010 j10001 j10000 j01000 j00100 j00010
    j00001 j00000
  fun_prop (disch := simp [*])

/-- **`setCJ` is integrable on `[0, 1]`.** -/
theorem intervalIntegrable_setCJ : IntervalIntegrable setCJ volume 0 1 := by
  have hA : IntervalIntegrable setCJ volume 0 (1 / 2) :=
    intervalIntegrable_of_logSqBound (logSqBound_jzSum.congr fun x hx =>
      setCJ_eq_near_zero hx.1 (by linarith [hx.2])) fun x hx =>
      continuousAt_setCJ ⟨hx.1, by linarith [hx.2]⟩
  have hB : IntervalIntegrable (fun y => setCJ (1 - y)) volume 0 (1 / 2) :=
    intervalIntegrable_of_logSqBound (logSqBound_joSum.congr fun y hy =>
      setCJ_eq_near_one hy.1 (by linarith [hy.2])) fun y hy =>
      ContinuousAt.comp (g := setCJ) (continuousAt_setCJ ⟨by linarith [hy.2], by linarith [hy.1]⟩)
        (by fun_prop)
  have h := hB.comp_sub_left 1
  simp only [sub_sub_cancel] at h
  norm_num at h
  exact hA.trans h.symm

end QED.Chain
