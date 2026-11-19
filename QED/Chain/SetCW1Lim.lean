/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetCRem
public import QED.Chain.SetCW1
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (c): endpoint limits of the rational-coefficient part

Helper analysis for the sixth-order set (c) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

Substituting the second-order expansions of the atoms (`QED.Chain.SetCRem`) into
`G₁ = QED.Chain.setCG1`, every pole of the coefficients cancels: on `(0, 1)`,
`G₁(x) = 2147/432 + x S₀(x)` and `G₁(1 - y) = 3509/432 - (8/9) log 2 + y S₁(y)`, where `S₀, S₁`
are sums of terms `d(x) logʲ x r(x)` with `d` rational (poles only at `1, -1, 2`), `j ≤ 2` and
`r` a product of bounded remainders. Hence `S₀, S₁ = O(1 + log² x)` on `(0, 1/2)` and the limits
follow. Generator: `scratchpad/setC/gen_lim.py G`.

## Main statements

* `QED.Chain.tendsto_setCG1_zero`: `G₁(0⁺) = 2147/432`.
* `QED.Chain.tendsto_setCG1_one`: `G₁(1⁻) = 3509/432 - (8/9) log 2`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog QED.Chain.SetCW1 QED.Chain.SetCRem

namespace QED.Chain

namespace SetCW1Lim

/-- Expansion coefficient `21000` of `setCG1` at 0. -/
noncomputable def gz21000 (x : ℝ) : ℝ :=
  (3 - 7 * x + 95 * x ^ 2 - 175 * x ^ 3 + 101 * x ^ 4 + 3 * x ^ 5 - 7 * x ^ 6 + 3 * x ^ 7) / (18 *
      (1 - x) ^ 3)

/-- Expansion coefficient `20100` of `setCG1` at 0. -/
noncomputable def gz20100 (x : ℝ) : ℝ :=
  (3 - 7 * x + 95 * x ^ 2 - 175 * x ^ 3 + 101 * x ^ 4 + 3 * x ^ 5 - 7 * x ^ 6 + 3 * x ^ 7) / (9 *
      (1 - x) ^ 3)

/-- Expansion coefficient `20000` of `setCG1` at 0. -/
noncomputable def gz20000 (x : ℝ) : ℝ :=
  (228 - 691 * x + 751 * x ^ 2 - 298 * x ^ 3 - 40 * x ^ 4 + 27 * x ^ 5 - 9 * x ^ 6) / (36 * (1
      - x) ^ 3)

/-- Expansion coefficient `11000` of `setCG1` at 0. -/
noncomputable def gz11000 (x : ℝ) : ℝ :=
  (1 / 9 - 28 / 27 * x + 245 / 108 * x ^ 2 - 43 / 27 * x ^ 3 + 1 / 4 * x ^ 4)

/-- Expansion coefficient `10100` of `setCG1` at 0. -/
noncomputable def gz10100 (x : ℝ) : ℝ :=
  (13 / 36 - 71 / 27 * x - 71 / 27 * x ^ 3 + 13 / 36 * x ^ 4)

/-- Expansion coefficient `10010` of `setCG1` at 0. -/
noncomputable def gz10010 (x : ℝ) : ℝ :=
  (3 - 7 * x + 95 * x ^ 2 - 175 * x ^ 3 + 101 * x ^ 4 + 3 * x ^ 5 - 7 * x ^ 6 + 3 * x ^ 7) / (9 *
      (1 - x) ^ 3)

/-- Expansion coefficient `10001` of `setCG1` at 0. -/
noncomputable def gz10001 (x : ℝ) : ℝ :=
  (6 - 14 * x + 190 * x ^ 2 - 350 * x ^ 3 + 202 * x ^ 4 + 6 * x ^ 5 - 14 * x ^ 6 + 6 * x ^ 7) /
      (9 * (1 - x) ^ 3)

/-- Expansion coefficient `10000` of `setCG1` at 0. -/
noncomputable def gz10000 (x : ℝ) : ℝ :=
  (-955 + 1655 * x + 540 * x ^ 2 - 2198 * x ^ 3 + 361 * x ^ 4 + 819 * x ^ 5 - 378 * x ^ 6 + 60
      * x ^ 7) / (108 * (1 + x) * (1 - x) ^ 3)

/-- Expansion coefficient `01000` of `setCG1` at 0. -/
noncomputable def gz01000 (x : ℝ) : ℝ :=
  (-126 + 678 * x - 1143 * x ^ 2 + 407 * x ^ 3 + 53 * x ^ 4 - 61 * x ^ 5) / (216 * (1 - x))

/-- Expansion coefficient `00100` of `setCG1` at 0. -/
noncomputable def gz00100 (x : ℝ) : ℝ :=
  (-187 + 731 * x - 928 * x ^ 2 - 544 * x ^ 3 + 731 * x ^ 4 - 187 * x ^ 5) / (216 * (1 - x))

/-- Expansion coefficient `00010` of `setCG1` at 0. -/
noncomputable def gz00010 (x : ℝ) : ℝ :=
  (39 - 190 * x + 263 * x ^ 2 - 128 * x ^ 3 + 263 * x ^ 4 - 190 * x ^ 5 + 39 * x ^ 6) / (54 * (1
      - x) ^ 2)

/-- Expansion coefficient `00001` of `setCG1` at 0. -/
noncomputable def gz00001 (x : ℝ) : ℝ :=
  (39 - 190 * x + 263 * x ^ 2 - 128 * x ^ 3 + 263 * x ^ 4 - 190 * x ^ 5 + 39 * x ^ 6) / (27 * (1
      - x) ^ 2)

/-- Expansion coefficient `00000` of `setCG1` at 0. -/
noncomputable def gz00000 (x : ℝ) : ℝ :=
  (805 - 1579 * x + 621 * x ^ 2 + 148 * x ^ 3 - 84 * x ^ 4 - 7 * x ^ 5) / (216 * (1 - x) ^ 2)

/-- The expansion of `setCG1` at 0. -/
noncomputable def gzSum (x : ℝ) : ℝ :=
  gz21000 x * log x ^ 2 * (remA x) +
    gz20100 x * log x ^ 2 * (remB x) +
    gz20000 x * log x ^ 2 * (1) +
    gz11000 x * log x ^ 1 * (remA x) +
    gz10100 x * log x ^ 1 * (remB x) +
    gz10010 x * log x ^ 1 * (remC x) +
    gz10001 x * log x ^ 1 * (remD x) +
    gz10000 x * log x ^ 1 * (1) +
    gz01000 x * log x ^ 0 * (remA x) +
    gz00100 x * log x ^ 0 * (remB x) +
    gz00010 x * log x ^ 0 * (remC x) +
    gz00001 x * log x ^ 0 * (remD x) +
    gz00000 x * log x ^ 0 * (1)

theorem gz_e0 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h21000 x * x ^ 3 = x * gz21000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h21000, gz21000]
  field_simp

theorem gz_e1 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h20100 x * x ^ 3 = x * gz20100 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h20100, gz20100]
  field_simp

theorem gz_e2 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h20000 x - h21000 x * x - 1 / 2 * h21000 x * x ^ 2 + h20100 x * x - 1 / 2 * h20100 x
        * x ^ 2 = x * gz20000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h20000, h20100, h21000, gz20000]
  field_simp
  ring

theorem gz_e3 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h11000 x * x ^ 3 = x * gz11000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h11000, gz11000]
  field_simp
  ring

theorem gz_e4 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h10100 x * x ^ 3 = x * gz10100 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h10100, gz10100]
  field_simp
  ring

theorem gz_e5 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h10010 x * x ^ 3 = x * gz10010 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h10010, gz10010]
  field_simp

theorem gz_e6 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h10001 x * x ^ 3 = x * gz10001 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h10001, gz10001]
  field_simp

theorem gz_e7 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h10000 x - h11000 x * x - 1 / 2 * h11000 x * x ^ 2 + h10100 x * x - 1 / 2 * h10100 x * x ^ 2
        + h10010 x * x + 1 / 4 * h10010 x * x ^ 2 - h10001 x * x + 1 / 4 * h10001 x * x ^ 2 = x
        * gz10000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h10000, h10001, h10010, h10100, h11000, gz10000]
  field_simp
  ring

theorem gz_e8 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h01000 x * x ^ 3 = x * gz01000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h01000, gz01000]
  field_simp

theorem gz_e9 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h00100 x * x ^ 3 = x * gz00100 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h00100, gz00100]
  field_simp

theorem gz_e10 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h00010 x * x ^ 3 = x * gz00010 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h00010, gz00010]
  field_simp

theorem gz_e11 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h00001 x * x ^ 3 = x * gz00001 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h00001, gz00001]
  field_simp

theorem gz_e12 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    h00000 x - h01000 x * x - 1 / 2 * h01000 x * x ^ 2 + h00100 x * x - 1 / 2 * h00100 x * x ^ 2
        + h00010 x * x + 1 / 4 * h00010 x * x ^ 2 - h00001 x * x + 1 / 4 * h00001 x
        * x ^ 2 = 2147 / 432 + x * gz00000 x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  simp only [h00000, h00001, h00010, h00100, h01000, gz00000]
  field_simp
  ring

theorem setCG1_eq_near_zero {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    setCG1 x = 2147 / 432 + x * gzSum x := by
  have hz : x ≠ 0 := h0.ne'
  have hm : 1 - x ≠ 0 := by linarith
  have hp : 1 + x ≠ 0 := by linarith
  unfold setCG1 gzSum
  rw [log_one_sub_eq h0, log_one_add_eq h0, Li_two_neg_eq h0, Li_two_eq h0]
  linear_combination log x ^ 2 * remA x * (gz_e0 h0 h1) + log x ^ 2 * remB x * (gz_e1 h0 h1)
      + log x ^ 2 * (gz_e2 h0 h1) + log x ^ 1 * remA x * (gz_e3 h0 h1) + log x ^ 1 * remB x *
      (gz_e4 h0 h1) + log x ^ 1 * remC x * (gz_e5 h0 h1) + log x ^ 1 * remD x * (gz_e6 h0 h1)
      + log x ^ 1 * (gz_e7 h0 h1) + remA x * (gz_e8 h0 h1) + remB x * (gz_e9 h0 h1) + remC x *
      (gz_e10 h0 h1) + remD x * (gz_e11 h0 h1) + (gz_e12 h0 h1)

theorem logSqBound_gzSum : LogSqBound gzSum := by
  have bddC := @Bdd.of_continuousAt
  have t0 := logSqBound_term (d := gz21000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz21000; fun_prop (disch := simp [*])) bdd_remA (j := 2) (by norm_num)
  have t1 := logSqBound_term (d := gz20100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz20100; fun_prop (disch := simp [*])) bdd_remB (j := 2) (by norm_num)
  have t2 := logSqBound_term (d := gz20000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz20000; fun_prop (disch := simp [*])) bdd_one (j := 2) (by norm_num)
  have t3 := logSqBound_term (d := gz11000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz11000; fun_prop (disch := simp [*])) bdd_remA (j := 1) (by norm_num)
  have t4 := logSqBound_term (d := gz10100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz10100; fun_prop (disch := simp [*])) bdd_remB (j := 1) (by norm_num)
  have t5 := logSqBound_term (d := gz10010) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz10010; fun_prop (disch := simp [*])) bdd_remC (j := 1) (by norm_num)
  have t6 := logSqBound_term (d := gz10001) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz10001; fun_prop (disch := simp [*])) bdd_remD (j := 1) (by norm_num)
  have t7 := logSqBound_term (d := gz10000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz10000; fun_prop (disch := simp [*])) bdd_one (j := 1) (by norm_num)
  have t8 := logSqBound_term (d := gz01000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz01000; fun_prop (disch := simp [*])) bdd_remA (j := 0) (by norm_num)
  have t9 := logSqBound_term (d := gz00100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz00100; fun_prop (disch := simp [*])) bdd_remB (j := 0) (by norm_num)
  have t10 := logSqBound_term (d := gz00010) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz00010; fun_prop (disch := simp [*])) bdd_remC (j := 0) (by norm_num)
  have t11 := logSqBound_term (d := gz00001) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz00001; fun_prop (disch := simp [*])) bdd_remD (j := 0) (by norm_num)
  have t12 := logSqBound_term (d := gz00000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold gz00000; fun_prop (disch := simp [*])) bdd_one (j := 0) (by norm_num)
  exact ((((((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add
      t10).add t11).add t12)

/-- Expansion coefficient `12000` of `setCG1` at 1. -/
noncomputable def go12000 (x : ℝ) : ℝ :=
  (-16 * x ^ 2 + 56 * x ^ 3 - 164 * x ^ 4 + 224 * x ^ 5 - 116 * x ^ 6 + 24 * x ^ 7 - 14 * x ^ 8
      + 3 * x ^ 9) / (18 * (1 - x) ^ 2)

/-- Expansion coefficient `11000` of `setCG1` at 1. -/
noncomputable def go11000 (x : ℝ) : ℝ :=
  (1348 * x ^ 2 - 2066 * x ^ 3 + 143 * x ^ 4 + 560 * x ^ 5 - 27 * x ^ 6 + 48 * x ^ 7 - 18
      * x ^ 8) / (108 * (1 - x) ^ 2)

/-- Expansion coefficient `10000` of `setCG1` at 1. -/
noncomputable def go10000 (x : ℝ) : ℝ :=
  (-1566 + 1887 * x + 724 * x ^ 2 - 770 * x ^ 3 - 278 * x ^ 4 - 9 * x ^ 5 - 6 * x ^ 6 + 9
      * x ^ 7) / (216 * (1 - x) ^ 2)

/-- Expansion coefficient `02100` of `setCG1` at 1. -/
noncomputable def go02100 (x : ℝ) : ℝ :=
  (-16 * x ^ 5 + 56 * x ^ 6 - 164 * x ^ 7 + 224 * x ^ 8 - 116 * x ^ 9 + 24 * x ^ 10 - 14 * x ^ 11
      + 3 * x ^ 12) / (72 * (1 - x) ^ 2)

/-- Expansion coefficient `02000` of `setCG1` at 1. -/
noncomputable def go02000 (x : ℝ) : ℝ :=
  (-32 * x ^ 2 - 128 * x ^ 2 * log 2 + 340 * x ^ 3 + 448 * x ^ 3 * log 2 - 996 * x ^ 4 - 1312
      * x ^ 4 * log 2 + 1764 * x ^ 5 + 1792 * x ^ 5 * log 2 - 1824 * x ^ 6 - 928 * x ^ 6 * log 2
      + 918 * x ^ 7 + 192 * x ^ 7 * log 2 - 220 * x ^ 8 - 112 * x ^ 8 * log 2 + 66 * x ^ 9 + 24
      * x ^ 9 * log 2 + 2 * x ^ 10 - 3 * x ^ 11) / (72 * (1 - x) ^ 2)

/-- Expansion coefficient `01100` of `setCG1` at 1. -/
noncomputable def go01100 (x : ℝ) : ℝ :=
  (2206 * x ^ 5 - 3212 * x ^ 6 - 114 * x ^ 7 + 1120 * x ^ 8 - 69 * x ^ 9 + 96 * x ^ 10 - 36
      * x ^ 11) / (864 * (1 - x) ^ 2)

/-- Expansion coefficient `01010` of `setCG1` at 1. -/
noncomputable def go01010 (x : ℝ) : ℝ :=
  (16 * x ^ 2 - 56 * x ^ 3 + 164 * x ^ 4 - 224 * x ^ 5 + 116 * x ^ 6 - 24 * x ^ 7 + 14 * x ^ 8
      - 3 * x ^ 9) / (9 * (1 - x) ^ 2)

/-- Expansion coefficient `01001` of `setCG1` at 1. -/
noncomputable def go01001 (x : ℝ) : ℝ :=
  (-128 * x ^ 2 + 640 * x ^ 3 - 2080 * x ^ 4 + 4112 * x ^ 5 - 4656 * x ^ 6 + 3092 * x ^ 7 - 1320
      * x ^ 8 + 452 * x ^ 9 - 144 * x ^ 10 + 32 * x ^ 11 - 3 * x ^ 12) / (9 * (1 - x) ^ 2)

/-- Expansion coefficient `01000` of `setCG1` at 1. -/
noncomputable def go01000 (x : ℝ) : ℝ :=
  (576 - 6624 * x + 9040 * x ^ 2 + 35296 * x ^ 2 * log 2 - 19880 * x ^ 3 - 69040 * x ^ 3 * log 2
      + 51252 * x ^ 4 + 23872 * x ^ 4 * log 2 - 56390 * x ^ 5 + 18832 * x ^ 5 * log 2 + 31768
      * x ^ 6 - 10064 * x ^ 6 * log 2 - 13598 * x ^ 7 + 2088 * x ^ 7 * log 2 + 5494 * x ^ 8
      - 1344 * x ^ 8 * log 2 - 2277 * x ^ 9 + 288 * x ^ 9 * log 2 + 792 * x ^ 10 - 108 * x ^ 11) /
      (864 * (2 - x) * (1 - x) ^ 2)

/-- Expansion coefficient `00100` of `setCG1` at 1. -/
noncomputable def go00100 (x : ℝ) : ℝ :=
  (-192 * x ^ 2 - 1768 * x ^ 3 + 1932 * x ^ 4 + 1628 * x ^ 5 - 1075 * x ^ 6 - 526 * x ^ 7 - 3
      * x ^ 8 - 12 * x ^ 9 + 18 * x ^ 10) / (1728 * (1 - x) ^ 2)

/-- Expansion coefficient `00010` of `setCG1` at 1. -/
noncomputable def go00010 (x : ℝ) : ℝ :=
  (-674 * x ^ 2 + 1048 * x ^ 3 - 126 * x ^ 4 - 248 * x ^ 5 + 27 * x ^ 6 - 24 * x ^ 7 + 9
      * x ^ 8) / (54 * (1 - x) ^ 2)

/-- Expansion coefficient `00001` of `setCG1` at 1. -/
noncomputable def go00001 (x : ℝ) : ℝ :=
  (5392 * x ^ 2 - 16472 * x ^ 3 + 17628 * x ^ 4 - 6490 * x ^ 5 - 1388 * x ^ 6 + 1878 * x ^ 7
      - 770 * x ^ 8 + 279 * x ^ 9 - 78 * x ^ 10 + 9 * x ^ 11) / (54 * (1 - x) ^ 2)

/-- Expansion coefficient `00000` of `setCG1` at 1. -/
noncomputable def go00000 (x : ℝ) : ℝ :=
  (26848 - 34432 * log 2 - 45096 * x + 51200 * x * log 2 - 19636 * x ^ 2 + 9056 * x ^ 2 * log 2
      + 79200 * x ^ 3 - 30224 * x ^ 3 * log 2 - 49836 * x ^ 4 + 184 * x ^ 4 * log 2 + 3654
      * x ^ 5 + 4160 * x ^ 5 * log 2 + 7465 * x ^ 6 - 168 * x ^ 6 * log 2 - 3596 * x ^ 7 + 384
      * x ^ 7 * log 2 + 1497 * x ^ 8 - 144 * x ^ 8 * log 2 - 600 * x ^ 9 + 90 * x ^ 10) / (1728 *
      (2 - x) * (1 - x) ^ 2)

/-- The expansion of `setCG1` at 1. -/
noncomputable def goSum (x : ℝ) : ℝ :=
  go12000 x * log x ^ 1 * (remA x * remA x) +
    go11000 x * log x ^ 1 * (remA x) +
    go10000 x * log x ^ 1 * (1) +
    go02100 x * log x ^ 0 * (remA x * remA x * remA (x / 2)) +
    go02000 x * log x ^ 0 * (remA x * remA x) +
    go01100 x * log x ^ 0 * (remA x * remA (x / 2)) +
    go01010 x * log x ^ 0 * (remA x * remC x) +
    go01001 x * log x ^ 0 * (remA x * remC (x * (2 - x))) +
    go01000 x * log x ^ 0 * (remA x) +
    go00100 x * log x ^ 0 * (remA (x / 2)) +
    go00010 x * log x ^ 0 * (remC x) +
    go00001 x * log x ^ 0 * (remC (x * (2 - x))) +
    go00000 x * log x ^ 0 * (1)

theorem go_e0 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    h21000 (1 - y) * y ^ 6 - h10010 (1 - y) * y ^ 6 = y * go12000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h10010, h21000, go12000]
  field_simp
  ring

theorem go_e1 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    h11000 (1 - y) * y ^ 3 - h00010 (1 - y) * y ^ 3 - 2 * h21000 (1 - y) * y ^ 4 - h21000 (1 - y)
        * y ^ 5 + 2 * h10010 (1 - y) * y ^ 4 + h10010 (1 - y) * y ^ 5 = y * go11000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h00010, h10010, h11000, h21000, go11000]
  field_simp
  ring

theorem go_e2 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    h01000 (1 - y) - h11000 (1 - y) * y - 1 / 2 * h11000 (1 - y) * y ^ 2 + h00010 (1 - y) * y
        + 1 / 2 * h00010 (1 - y) * y ^ 2 + h21000 (1 - y) * y ^ 2 + h21000 (1 - y) * y ^ 3
        + 1 / 4 * h21000 (1 - y) * y ^ 4 - h10010 (1 - y) * y ^ 2 - h10010 (1 - y) * y ^ 3
        - 1 / 4 * h10010 (1 - y) * y ^ 4 = y * go10000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h00010, h01000, h10010, h11000, h21000, go10000]
  field_simp
  ring

theorem go_e3 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    1 / 8 * h20100 (1 - y) * y ^ 9 - 1 / 8 * h10001 (1 - y) * y ^ 9 = y * go02100 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h10001, h20100, go02100]
  field_simp
  ring

theorem go_e4 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    h20000 (1 - y) * y ^ 6 + h20100 (1 - y) * y ^ 6 * log 2 - 1 / 2 * h20100 (1 - y) * y ^ 7
        - 1 / 8 * h20100 (1 - y) * y ^ 8 - h10001 (1 - y) * y ^ 6 * log 2 + 1 / 2 * h10001 (1
        - y) * y ^ 7 + 1 / 8 * h10001 (1 - y) * y ^ 8 = y * go02000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h10001, h20000, h20100, go02000]
  field_simp
  ring

theorem go_e5 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    1 / 8 * h10100 (1 - y) * y ^ 6 - 1 / 8 * h00001 (1 - y) * y ^ 6 - 1 / 4 * h20100 (1 - y)
        * y ^ 7 - 1 / 8 * h20100 (1 - y) * y ^ 8 + 1 / 4 * h10001 (1 - y) * y ^ 7 + 1 / 8 * h10001
        (1 - y) * y ^ 8 = y * go01100 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h00001, h10001, h10100, h20100, go01100]
  field_simp
  ring

theorem go_e6 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    -h10010 (1 - y) * y ^ 6 + h10001 (1 - y) * y ^ 6 = y * go01010 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h10001, h10010, go01010]
  field_simp
  ring

theorem go_e7 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    -4 * h10001 (1 - y) * y ^ 6 + 6 * h10001 (1 - y) * y ^ 7 - 3 * h10001 (1 - y) * y ^ 8 + 1 / 2
        * h10001 (1 - y) * y ^ 9 = y * go01001 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h10001, go01001]
  field_simp
  ring

theorem go_e8 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    h10000 (1 - y) * y ^ 3 - 2 * h20000 (1 - y) * y ^ 4 - h20000 (1 - y) * y ^ 5 + h10100 (1 - y)
        * y ^ 3 * log 2 - 1 / 2 * h10100 (1 - y) * y ^ 4 - 1 / 8 * h10100 (1 - y) * y ^ 5 - h00001
        (1 - y) * y ^ 3 * log 2 + 1 / 2 * h00001 (1 - y) * y ^ 4 + 1 / 8 * h00001 (1 - y) * y ^ 5
        - 2 * h20100 (1 - y) * y ^ 4 * log 2 + h20100 (1 - y) * y ^ 5 - h20100 (1 - y) * y ^ 5
        * log 2 + 3 / 4 * h20100 (1 - y) * y ^ 6 + 1 / 8 * h20100 (1 - y) * y ^ 7 + 1 / 6 * h10010
        (1 - y) * y ^ 3 * π ^ 2 - h10010 (1 - y) * y ^ 4 - 1 / 4 * h10010 (1 - y) * y ^ 5
        - 1 / 12 * h10001 (1 - y) * y ^ 3 * π ^ 2 + 2 * h10001 (1 - y) * y ^ 4 * log 2 - 3 / 4
        * h10001 (1 - y) * y ^ 5 + h10001 (1 - y) * y ^ 5 * log 2 - 1 / 4 * h10001 (1 - y)
        * y ^ 6 - 1 / 4 * h10001 (1 - y) * y ^ 7 = y * go01000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h00001, h10000, h10001, h10010, h10100, h20000, h20100, go01000]
  field_simp
  ring

theorem go_e9 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    1 / 8 * h00100 (1 - y) * y ^ 3 - 1 / 8 * h10100 (1 - y) * y ^ 4 - 1 / 16 * h10100 (1 - y)
        * y ^ 5 + 1 / 8 * h00001 (1 - y) * y ^ 4 + 1 / 16 * h00001 (1 - y) * y ^ 5 + 1 / 8
        * h20100 (1 - y) * y ^ 5 + 1 / 8 * h20100 (1 - y) * y ^ 6 + 1 / 32 * h20100 (1 - y)
        * y ^ 7 - 1 / 8 * h10001 (1 - y) * y ^ 5 - 1 / 8 * h10001 (1 - y) * y ^ 6 - 1 / 32
        * h10001 (1 - y) * y ^ 7 = y * go00100 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h00001, h00100, h10001, h10100, h20100, go00100]
  field_simp
  ring

theorem go_e10 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    -h00010 (1 - y) * y ^ 3 + h00001 (1 - y) * y ^ 3 + h10010 (1 - y) * y ^ 4 + 1 / 2 * h10010 (1
        - y) * y ^ 5 - h10001 (1 - y) * y ^ 4 - 1 / 2 * h10001 (1 - y) * y ^ 5 = y * go00010 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h00001, h00010, h10001, h10010, go00010]
  field_simp
  ring

theorem go_e11 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    -4 * h00001 (1 - y) * y ^ 3 + 6 * h00001 (1 - y) * y ^ 4 - 3 * h00001 (1 - y) * y ^ 5 + 1 / 2
        * h00001 (1 - y) * y ^ 6 + 4 * h10001 (1 - y) * y ^ 4 - 4 * h10001 (1 - y) * y ^ 5
        + h10001 (1 - y) * y ^ 7 - 1 / 4 * h10001 (1 - y) * y ^ 8 = y * go00001 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h00001, h10001, go00001]
  field_simp
  ring

theorem go_e12 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    h00000 (1 - y) - h10000 (1 - y) * y - 1 / 2 * h10000 (1 - y) * y ^ 2 + h00100 (1 - y) * log 2
        - 1 / 2 * h00100 (1 - y) * y - 1 / 8 * h00100 (1 - y) * y ^ 2 + h20000 (1 - y) * y ^ 2
        + h20000 (1 - y) * y ^ 3 + 1 / 4 * h20000 (1 - y) * y ^ 4 - h10100 (1 - y) * y * log 2
        + 1 / 2 * h10100 (1 - y) * y ^ 2 - 1 / 2 * h10100 (1 - y) * y ^ 2 * log 2 + 3 / 8 * h10100
        (1 - y) * y ^ 3 + 1 / 16 * h10100 (1 - y) * y ^ 4 + 1 / 6 * h00010 (1 - y) * π ^ 2
        - h00010 (1 - y) * y - 1 / 4 * h00010 (1 - y) * y ^ 2 - 1 / 12 * h00001 (1 - y) * π ^ 2
        + h00001 (1 - y) * y * log 2 - 1 / 4 * h00001 (1 - y) * y ^ 2 + 1 / 2 * h00001 (1 - y)
        * y ^ 2 * log 2 + 1 / 8 * h00001 (1 - y) * y ^ 3 - 3 / 16 * h00001 (1 - y) * y ^ 4
        + h20100 (1 - y) * y ^ 2 * log 2 - 1 / 2 * h20100 (1 - y) * y ^ 3 + h20100 (1 - y)
        * y ^ 3 * log 2 - 5 / 8 * h20100 (1 - y) * y ^ 4 + 1 / 4 * h20100 (1 - y) * y ^ 4 * log 2
        - 1 / 4 * h20100 (1 - y) * y ^ 5 - 1 / 32 * h20100 (1 - y) * y ^ 6 - 1 / 6 * h10010 (1
        - y) * y * π ^ 2 + h10010 (1 - y) * y ^ 2 - 1 / 12 * h10010 (1 - y) * y ^ 2 * π ^ 2
        + 3 / 4 * h10010 (1 - y) * y ^ 3 + 1 / 8 * h10010 (1 - y) * y ^ 4 + 1 / 12 * h10001 (1
        - y) * y * π ^ 2 + 1 / 24 * h10001 (1 - y) * y ^ 2 * π ^ 2 - h10001 (1 - y) * y ^ 2
        * log 2 + 1 / 4 * h10001 (1 - y) * y ^ 3 - h10001 (1 - y) * y ^ 3 * log 2 - 1 / 4 * h10001
        (1 - y) * y ^ 4 * log 2 + 1 / 8 * h10001 (1 - y) * y ^ 5 + 3 / 32 * h10001 (1 - y)
        * y ^ 6 = (3509 / 432 - 8 / 9 * log 2) + y * go00000 y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  simp only [h00000, h00001, h00010, h00100, h10000, h10001, h10010, h10100, h20000, h20100,
      go00000]
  field_simp
  ring

theorem setCG1_eq_near_one {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    setCG1 (1 - y) = (3509 / 432 - 8 / 9 * log 2) + y * goSum y := by
  have hz : y ≠ 0 := h0.ne'
  have hm : 1 - y ≠ 0 := by linarith
  have h2 : 2 - y ≠ 0 := by linarith
  have hy : 1 - (1 - y) ≠ 0 := by linarith
  have hq : 1 + (1 - y) ≠ 0 := by linarith
  have hw : 0 < y * (2 - y) := by nlinarith
  unfold setCG1 goSum
  rw [show 1 - (1 - y) = y by ring, Li_two_neg_one_sub_eq h0 h1, Li_two_one_sub_eq h0 h1,
    log_two_sub_eq h0 h1, log_one_sub_eq h0, Li_two_eq h0, Li_two_eq hw]
  linear_combination log y ^ 1 * remA y * remA y * (go_e0 h0 h1) + log y ^ 1 * remA y *
      (go_e1 h0 h1) + log y ^ 1 * (go_e2 h0 h1) + remA y * remA y * remA (y / 2) * (go_e3 h0 h1)
      + remA y * remA y * (go_e4 h0 h1) + remA y * remA (y / 2) * (go_e5 h0 h1) + remA y * remC y
      * (go_e6 h0 h1) + remA y * remC (y * (2 - y)) * (go_e7 h0 h1) + remA y * (go_e8 h0 h1)
      + remA (y / 2) * (go_e9 h0 h1) + remC y * (go_e10 h0 h1) + remC (y * (2 - y)) *
      (go_e11 h0 h1) + (go_e12 h0 h1)

theorem logSqBound_goSum : LogSqBound goSum := by
  have bddC := @Bdd.of_continuousAt
  have t0 := logSqBound_term (d := go12000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go12000; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remA) (j := 1) (by norm_num)
  have t1 := logSqBound_term (d := go11000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go11000; fun_prop (disch := simp [*])) bdd_remA (j := 1) (by norm_num)
  have t2 := logSqBound_term (d := go10000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go10000; fun_prop (disch := simp [*])) bdd_one (j := 1) (by norm_num)
  have t3 := logSqBound_term (d := go02100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go02100; fun_prop (disch := simp [*])) ((bdd_remA.mul bdd_remA).mul bdd_remA_half)
        (j := 0) (by norm_num)
  have t4 := logSqBound_term (d := go02000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go02000; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remA) (j := 0) (by norm_num)
  have t5 := logSqBound_term (d := go01100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go01100; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remA_half) (j := 0)
        (by norm_num)
  have t6 := logSqBound_term (d := go01010) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go01010; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remC) (j := 0) (by norm_num)
  have t7 := logSqBound_term (d := go01001) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go01001; fun_prop (disch := simp [*])) (bdd_remA.mul bdd_remC_w) (j := 0) (by norm_num)
  have t8 := logSqBound_term (d := go01000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go01000; fun_prop (disch := simp [*])) bdd_remA (j := 0) (by norm_num)
  have t9 := logSqBound_term (d := go00100) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go00100; fun_prop (disch := simp [*])) bdd_remA_half (j := 0) (by norm_num)
  have t10 := logSqBound_term (d := go00010) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go00010; fun_prop (disch := simp [*])) bdd_remC (j := 0) (by norm_num)
  have t11 := logSqBound_term (d := go00001) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go00001; fun_prop (disch := simp [*])) bdd_remC_w (j := 0) (by norm_num)
  have t12 := logSqBound_term (d := go00000) (bddC fun x hx => by
    have a : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have b : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
    have c : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    unfold go00000; fun_prop (disch := simp [*])) bdd_one (j := 0) (by norm_num)
  exact ((((((((((((t0.add t1).add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add
      t10).add t11).add t12)

end SetCW1Lim

open SetCW1Lim

/-- `G₁(0⁺) = 2147/432`. -/
theorem tendsto_setCG1_zero : Tendsto setCG1 (𝓝[>] 0) (𝓝 (2147 / 432)) :=
  tendsto_of_eq_add_mul logSqBound_gzSum fun x hx =>
    setCG1_eq_near_zero hx.1 (by linarith [hx.2])

/-- `G₁(1⁻) = 3509/432 - (8/9) log 2`. -/
theorem tendsto_setCG1_one : Tendsto setCG1 (𝓝[<] 1) (𝓝 (3509 / 432 - 8 / 9 * log 2)) := by
  have h := (tendsto_of_eq_add_mul (f := fun y => setCG1 (1 - y)) logSqBound_goSum
    fun y hy => setCG1_eq_near_one hy.1 (by linarith [hy.2])).comp tendsto_one_sub_nhdsLT_one
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, sub_sub_cancel]

end QED.Chain
