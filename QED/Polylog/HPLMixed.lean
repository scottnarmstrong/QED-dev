/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLLowWeight
import QED.Polylog.AlphabetPM
import QED.Polylog.LiCalculus
import QED.Polylog.Reflection
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Harmonic polylogarithms of weight three with both letters `1` and `-1`

Closed forms on `(0, 1)` of the weight-3 words over `{0, 1, -1}` that contain both `1` and
`-1` and are reachable from the Lyndon words `(1, 1, -1)` and `(1, -1, -1)` (in the order
`0 < 1 < -1`) by the shuffle product, in terms of `log`, `Li 2`, `Li 3` at the arguments
`(1 ∓ x)/2` and the constants `Li 2 (1/2)`, `Li 3 (1/2)`, `log 2`, `π`.

The closed forms of the two Lyndon words were found numerically (least squares and PSLQ) and
are proved here by the uniqueness theorem `QED.Polylog.HPL.eq_hpl_cons_of_hasDerivAt`; for
`(1, -1, -1)` the derivative check uses Euler's reflection formula for `Li 2` at `(1 + x)/2`.

## Main results

* `QED.Polylog.HPL.hpl_one_one_negOne`:
  `H(1, 1, -1) = Li 3 (1/2) - Li 3 ((1-x)/2) + Li 2 (1/2) log (1-x) + (log 2 / 2) log² (1-x)`.
* `QED.Polylog.HPL.hpl_one_negOne_negOne`:
  `H(1, -1, -1) = Li 3 ((1+x)/2) - Li 3 (1/2) + log (1+x) Li 2 ((1-x)/2)
  + log (1-x) log² (1+x) / 2 - (log 2 / 2) log² (1+x) - log 2 log (1-x) log (1+x)
  + (log² 2 - π²/6) log (1+x)`.
* `QED.Polylog.HPL.hpl_one_negOne_one`, `QED.Polylog.HPL.hpl_negOne_one_one`,
  `QED.Polylog.HPL.hpl_negOne_one_negOne`, `QED.Polylog.HPL.hpl_negOne_negOne_one`: the
  shuffle consequences.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-- The closed form of `H(1, 1, -1; x)` on `(0, 1)`. -/
theorem hpl_one_one_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, negOne] x = Li 3 (1 / 2) - Li 3 ((1 - x) / 2) +
      Li 2 (1 / 2) * log (1 - x) + log 2 / 2 * log (1 - x) ^ 2 := by
  refine eq_hpl_cons_of_hasDerivAt (a := one) (w := [one, negOne]) (by simp)
    (F := fun y => Li 3 (1 / 2) - Li 3 ((1 - y) / 2) + Li 2 (1 / 2) * log (1 - y) +
      log 2 / 2 * log (1 - y) ^ 2) (fun y hy => ?_) ?_ x hx
  · obtain ⟨hf, h1, h0, hd, -, -⟩ := PM.data_halfOneSub hy.1 hy.2
    have h3 := hasDerivAt_Li_three_of hf h1 h0 hd rfl
    have h1y : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    have hl := ((hasDerivAt_id y).const_sub 1).log h1y
    refine ((((hasDerivAt_const y (Li 3 (1 / 2))).sub h3).add (hl.const_mul (Li 2 (1 / 2)))).add
      ((hl.pow 2).const_mul (log 2 / 2))).congr_deriv ?_
    rw [kernel_one, hpl_one_negOne hy]
    simp only [id]
    field_simp
    ring
  · have t3 := tendsto_Li_comp_zero (k := 3) (g := fun y => (1 - y) / 2) (by norm_num)
      (by fun_prop) (by norm_num) fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have tl := tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 - y)) (c := 0)
      (by fun_prop (disch := norm_num)) (by simp)
    have h := (((tendsto_const_nhds (x := Li 3 (1 / 2))).sub t3).add
      (tl.const_mul (Li 2 (1 / 2)))).add ((tl.pow 2).const_mul (log 2 / 2))
    simpa using h

/-- The closed form of `H(1, -1, -1; x)` on `(0, 1)`. -/
theorem hpl_one_negOne_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, negOne] x = Li 3 ((1 + x) / 2) - Li 3 (1 / 2) +
      log (1 + x) * Li 2 ((1 - x) / 2) + log (1 - x) * log (1 + x) ^ 2 / 2 -
      log 2 / 2 * log (1 + x) ^ 2 - log 2 * log (1 - x) * log (1 + x) +
      (log 2 ^ 2 - π ^ 2 / 6) * log (1 + x) := by
  refine eq_hpl_cons_of_hasDerivAt (a := one) (w := [negOne, negOne]) (by simp)
    (F := fun y => Li 3 ((1 + y) / 2) - Li 3 (1 / 2) + log (1 + y) * Li 2 ((1 - y) / 2) +
      log (1 - y) * log (1 + y) ^ 2 / 2 - log 2 / 2 * log (1 + y) ^ 2 -
      log 2 * log (1 - y) * log (1 + y) + (log 2 ^ 2 - π ^ 2 / 6) * log (1 + y))
    (fun y hy => ?_) ?_ x hx
  · obtain ⟨hfp, h1p, h0p, hdp, -, -⟩ := PM.data_halfOneAdd hy.1 hy.2
    obtain ⟨hfm, h1m, h0m, hdm, -, hl1m⟩ := PM.data_halfOneSub hy.1 hy.2
    have hR : Li 2 ((1 + y) / 2) = π ^ 2 / 6 - (log (1 + y) - log 2) * (log (1 - y) - log 2) -
        Li 2 ((1 - y) / 2) := by
      have h := Li₂_add_Li₂_one_sub (x := (1 + y) / 2) (by linarith [hy.1]) (by linarith [hy.2])
      rw [show 1 - (1 + y) / 2 = (1 - y) / 2 by ring, log_div (by linarith [hy.1]) (by norm_num),
        log_div (by linarith [hy.2]) (by norm_num)] at h
      rw [Li_two]
      linarith
    have h3 := hasDerivAt_Li_three_of hfp h1p h0p hdp hR
    have h2 := hasDerivAt_Li_two_of hfm h1m h0m hdm hl1m
    have h1y : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    have h1y' : (1 : ℝ) + y ≠ 0 := by linarith [hy.1]
    have hlm := ((hasDerivAt_id y).const_sub 1).log h1y
    have hlp := ((hasDerivAt_id y).const_add 1).log h1y'
    refine ((((((h3.sub_const (Li 3 (1 / 2))).add (hlp.mul h2)).add
      ((hlm.mul (hlp.pow 2)).div_const 2)).sub ((hlp.pow 2).const_mul (log 2 / 2))).sub
      ((hlm.const_mul (log 2)).mul hlp)).add
      (hlp.const_mul (log 2 ^ 2 - π ^ 2 / 6))).congr_deriv ?_
    rw [kernel_one, hpl_negOne_negOne hy]
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  · have t3 := tendsto_Li_comp_zero (k := 3) (g := fun y => (1 + y) / 2) (by norm_num)
      (by fun_prop) (by norm_num) fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have t2 := tendsto_Li_comp_zero (k := 2) (g := fun y => (1 - y) / 2) le_rfl
      (by fun_prop) (by norm_num) fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have tm := tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 - y)) (c := 0)
      (by fun_prop (disch := norm_num)) (by simp)
    have tp := tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 + y)) (c := 0)
      (by fun_prop (disch := norm_num)) (by simp)
    have h := (((((t3.sub_const (Li 3 (1 / 2))).add (tp.mul t2)).add
      ((tm.mul (tp.pow 2)).div_const 2)).sub ((tp.pow 2).const_mul (log 2 / 2))).sub
      ((tm.const_mul (log 2)).mul tp)).add (tp.const_mul (log 2 ^ 2 - π ^ 2 / 6))
    simpa using h

/-- The closed form of `H(1, -1, 1; x)` on `(0, 1)`, by the shuffle `H(1) H(1, -1)`. -/
theorem hpl_one_negOne_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, one] x =
      -log (1 - x) * hpl [one, negOne] x - 2 * hpl [one, one, negOne] x := by
  have h := hpl_mul_hpl [one] [one, negOne] hx
  simp [shuffle, shuffleAux, hpl_one hx] at h
  linarith

/-- The closed form of `H(-1, 1, 1; x)` on `(0, 1)`, by the shuffle `H(-1) H(1, 1)`. -/
theorem hpl_negOne_one_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, one] x = log (1 + x) * (log (1 - x) ^ 2 / 2) -
      hpl [one, negOne, one] x - hpl [one, one, negOne] x := by
  have h := hpl_mul_hpl [negOne] [one, one] hx
  simp [shuffle, shuffleAux, hpl_negOne hx, hpl_one_one hx] at h
  linarith

/-- The closed form of `H(-1, 1, -1; x)` on `(0, 1)`, by the shuffle `H(-1) H(1, -1)`. -/
theorem hpl_negOne_one_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, negOne] x = log (1 + x) * hpl [one, negOne] x -
      2 * hpl [one, negOne, negOne] x := by
  have h := hpl_mul_hpl [negOne] [one, negOne] hx
  simp [shuffle, shuffleAux, hpl_negOne hx] at h
  linarith

/-- The closed form of `H(-1, -1, 1; x)` on `(0, 1)`, by the shuffle `H(1) H(-1, -1)`. -/
theorem hpl_negOne_negOne_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne, one] x = -log (1 - x) * (log (1 + x) ^ 2 / 2) -
      hpl [one, negOne, negOne] x - hpl [negOne, one, negOne] x := by
  have h := hpl_mul_hpl [one] [negOne, negOne] hx
  simp [shuffle, shuffleAux, hpl_one hx, hpl_negOne_negOne hx] at h
  linarith

end QED.Polylog.HPL
