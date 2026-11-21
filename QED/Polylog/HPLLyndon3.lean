/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLMixed
import QED.Polylog.AlphabetPM
import QED.Polylog.DilogPM
import QED.Polylog.LiCalculus
import QED.Polylog.LiHalf
import QED.Polylog.Reflection
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The weight-three Lyndon words `(0, 1, -1)` and `(0, -1, 1)`

Closed forms on `(0, 1)` of the last two weight-3 Lyndon words over `{0, 1, -1}` (in the order
`0 < 1 < -1`), in terms of `Li 3` at the arguments `x`, `-x`, `1 - x`, `(1 ± x)/2`,
`1/(1 + x)`, `(1 - x)/(1 + x)`, `2x/(1 + x)`, products of `log x`, `log (1 ± x)`, `log 2` and
`Li 2`, and the constants `Li 2 (1/2)`, `Li 3 (1/2)`, `ζ(3) = zeta3`. With them, the shuffle
product gives the four remaining weight-3 words `(1, 0, -1)`, `(-1, 0, 1)`, `(1, -1, 0)`,
`(-1, 1, 0)`, so every weight-3 harmonic polylogarithm now has a closed form.

The closed forms were found by a least-squares fit against targets computed from the
nested-sum representation `QED.Polylog.HPL.hasSum_coef_mul_pow` (110 digits) followed by PSLQ
on the constant coefficients; they are proved by the uniqueness theorem
`QED.Polylog.HPL.eq_hpl_cons_of_hasDerivAt`, the dilogarithms of the derivative being reduced
to `Li 2 x`, `Li 2 (-x)`, `Li 2 ((1 - x)/2)` by the identities of `QED.Polylog.DilogPM`.

## Main results

* `QED.Polylog.HPL.hpl_zero_one_negOne`, `QED.Polylog.HPL.hpl_zero_negOne_one`: the two
  Lyndon words.
* `QED.Polylog.HPL.hpl_negOne_zero_one`, `QED.Polylog.HPL.hpl_negOne_one_zero`,
  `QED.Polylog.HPL.hpl_one_zero_negOne`, `QED.Polylog.HPL.hpl_one_negOne_zero`: the shuffle
  consequences.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-- The closed form of `H(0, 1, -1; x)` on `(0, 1)`. -/
theorem hpl_zero_one_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, negOne] x = -Li 3 x + Li 3 (-x) - Li 3 ((1 + x) / 2) + Li 3 (1 / (1 + x)) +
      Li 3 (2 * x / (1 + x)) + log (1 + x) * Li 2 x + log x * log (1 + x) ^ 2 / 2 -
      log (1 + x) ^ 3 / 3 + log 2 / 2 * log (1 + x) ^ 2 +
      (Li 2 (1 / 2) + π ^ 2 / 6) * log (1 + x) + (Li 3 (1 / 2) - zeta3) := by
  refine eq_hpl_cons_of_hasDerivAt (a := zero) (w := [one, negOne]) (by simp)
    (F := fun y => -Li 3 y + Li 3 (-y) - Li 3 ((1 + y) / 2) + Li 3 (1 / (1 + y)) +
      Li 3 (2 * y / (1 + y)) + log (1 + y) * Li 2 y + log y * log (1 + y) ^ 2 / 2 -
      log (1 + y) ^ 3 / 3 + log 2 / 2 * log (1 + y) ^ 2 +
      (Li 2 (1 / 2) + π ^ 2 / 6) * log (1 + y) + (Li 3 (1 / 2) - zeta3)) (fun y hy => ?_) ?_ x hx
  · obtain ⟨hfi, h1i, h0i, hdi, -, hl1i⟩ := PM.data_id hy.1 hy.2
    obtain ⟨hfn, h1n, h0n, hdn, -, -⟩ := PM.data_neg hy.1 hy.2
    obtain ⟨hfh, h1h, h0h, hdh, -, -⟩ := PM.data_halfOneAdd hy.1 hy.2
    obtain ⟨hfv, h1v, h0v, hdv, -, -⟩ := PM.data_invOneAdd hy.1 hy.2
    obtain ⟨hft, h1t, h0t, hdt, -, -⟩ := PM.data_twoMulDiv hy.1 hy.2
    have a1 := hasDerivAt_Li_three_of hfi h1i h0i hdi rfl
    have a2 := hasDerivAt_Li_three_of hfn h1n h0n hdn rfl
    have a3 := hasDerivAt_Li_three_of hfh h1h h0h hdh (Li_two_one_add_div_two hy)
    have a4 := hasDerivAt_Li_three_of hfv h1v h0v hdv (Li_two_inv_one_add hy)
    have a5 := hasDerivAt_Li_three_of hft h1t h0t hdt (Li_two_two_mul_div hy)
    have b2 := hasDerivAt_Li_two_of hfi h1i h0i hdi hl1i
    have hy0 : y ≠ 0 := hy.1.ne'
    have h1y : (1 : ℝ) + y ≠ 0 := by linarith [hy.1]
    have h1y' : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    have hlp := ((hasDerivAt_id y).const_add 1).log h1y
    have hlx := hasDerivAt_log hy0
    refine ((((((((((a1.neg.add a2).sub a3).add a4).add a5).add (hlp.mul b2)).add
      ((hlx.mul (hlp.pow 2)).div_const 2)).sub ((hlp.pow 3).div_const 3)).add
      ((hlp.pow 2).const_mul (log 2 / 2))).add
      (hlp.const_mul (Li 2 (1 / 2) + π ^ 2 / 6))).add_const _).congr_deriv ?_
    rw [kernel_zero, hpl_one_negOne hy, Li_two_one_half]
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  · have t1 := tendsto_Li_comp_zero (k := 3) (g := fun y => y) (by norm_num) continuousAt_id
      (by norm_num) fun y hy => ⟨by linarith [hy.1], hy.2.le⟩
    have t2 := tendsto_Li_comp_zero (k := 3) (g := fun y => -y) (by norm_num) continuousAt_neg
      (by norm_num) fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have t3 := tendsto_Li_comp_zero (k := 3) (g := fun y => (1 + y) / 2) (by norm_num)
      (by fun_prop) (by norm_num) fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have t4 := tendsto_Li_comp_zero (k := 3) (g := fun y => 1 / (1 + y)) (by norm_num)
      (by fun_prop (disch := norm_num)) (by norm_num) fun y hy =>
        ⟨by have : 0 < 1 / (1 + y) := by have := hy.1; positivity
            linarith, by rw [div_le_one (by linarith [hy.1])]; linarith [hy.1]⟩
    have t5 := tendsto_Li_comp_zero (k := 3) (g := fun y => 2 * y / (1 + y)) (by norm_num)
      (by fun_prop (disch := norm_num)) (by norm_num) fun y hy =>
        ⟨by have : 0 < 2 * y / (1 + y) := by have := hy.1; have := hy.2; positivity
            linarith, by rw [div_le_one (by linarith [hy.1])]; linarith [hy.2]⟩
    have t6 := tendsto_Li_comp_zero (k := 2) (g := fun y => y) le_rfl continuousAt_id
      (by norm_num) fun y hy => ⟨by linarith [hy.1], hy.2.le⟩
    have tp := tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 + y)) (c := 0)
      (by fun_prop (disch := norm_num)) (by simp)
    have txp := QED.Polylog.HPL.tendsto_log_mul_log_one_add_zero
    have h := (((((((((t1.neg.add t2).sub t3).add t4).add t5).add (tp.mul t6)).add
      ((txp.mul tp).div_const 2)).sub ((tp.pow 3).div_const 3)).add
      ((tp.pow 2).const_mul (log 2 / 2))).add (tp.const_mul (Li 2 (1 / 2) + π ^ 2 / 6))).add_const
      (Li 3 (1 / 2) - zeta3)
    convert h using 2
    · ring
    · norm_num [Li_three_one]

/-- The closed form of `H(0, -1, 1; x)` on `(0, 1)`. -/
theorem hpl_zero_negOne_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, one] x = Li 3 x - Li 3 (-x) + Li 3 (1 - x) - Li 3 ((1 - x) / 2) -
      Li 3 ((1 - x) / (1 + x)) - Li 3 (2 * x / (1 + x)) + log (1 - x) * Li 2 (-x) +
      log x * log (1 - x) * log (1 + x) - log x * log (1 + x) ^ 2 / 2 -
      log (1 - x) * log (1 + x) ^ 2 / 2 + log 2 * log (1 - x) * log (1 + x) +
      log (1 + x) ^ 3 / 3 - log 2 / 2 * log (1 + x) ^ 2 + Li 2 (1 / 2) * log (1 - x) -
      π ^ 2 / 6 * log (1 + x) + Li 3 (1 / 2) := by
  refine eq_hpl_cons_of_hasDerivAt (a := zero) (w := [negOne, one]) (by simp)
    (F := fun y => Li 3 y - Li 3 (-y) + Li 3 (1 - y) - Li 3 ((1 - y) / 2) -
      Li 3 ((1 - y) / (1 + y)) - Li 3 (2 * y / (1 + y)) + log (1 - y) * Li 2 (-y) +
      log y * log (1 - y) * log (1 + y) - log y * log (1 + y) ^ 2 / 2 -
      log (1 - y) * log (1 + y) ^ 2 / 2 + log 2 * log (1 - y) * log (1 + y) +
      log (1 + y) ^ 3 / 3 - log 2 / 2 * log (1 + y) ^ 2 + Li 2 (1 / 2) * log (1 - y) -
      π ^ 2 / 6 * log (1 + y) + Li 3 (1 / 2)) (fun y hy => ?_) ?_ x hx
  · obtain ⟨hfi, h1i, h0i, hdi, -, -⟩ := PM.data_id hy.1 hy.2
    obtain ⟨hfn, h1n, h0n, hdn, -, hl1n⟩ := PM.data_neg hy.1 hy.2
    obtain ⟨hfo, h1o, h0o, hdo, -, -⟩ := PM.data_oneSub hy.1 hy.2
    obtain ⟨hfh, h1h, h0h, hdh, -, -⟩ := PM.data_halfOneSub hy.1 hy.2
    obtain ⟨hfk, h1k, h0k, hdk, -, -⟩ := PM.data_ksT hy.1 hy.2
    obtain ⟨hft, h1t, h0t, hdt, -, -⟩ := PM.data_twoMulDiv hy.1 hy.2
    have a1 := hasDerivAt_Li_three_of hfi h1i h0i hdi rfl
    have a2 := hasDerivAt_Li_three_of hfn h1n h0n hdn rfl
    have a3 := hasDerivAt_Li_three_of hfo h1o h0o hdo (Li_two_one_sub' hy)
    have a4 := hasDerivAt_Li_three_of hfh h1h h0h hdh rfl
    have a5 := hasDerivAt_Li_three_of hfk h1k h0k hdk (Li_two_ksT hy)
    have a6 := hasDerivAt_Li_three_of hft h1t h0t hdt (Li_two_two_mul_div hy)
    have b2 := hasDerivAt_Li_two_of hfn h1n h0n hdn hl1n
    have hy0 : y ≠ 0 := hy.1.ne'
    have h1y : (1 : ℝ) + y ≠ 0 := by linarith [hy.1]
    have h1y' : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    have hlp := ((hasDerivAt_id y).const_add 1).log h1y
    have hlm := ((hasDerivAt_id y).const_sub 1).log h1y'
    have hlx := hasDerivAt_log hy0
    refine (((((((((((((((a1.sub a2).add a3).sub a4).sub a5).sub a6).add (hlm.mul b2)).add
      ((hlx.mul hlm).mul hlp)).sub ((hlx.mul (hlp.pow 2)).div_const 2)).sub
      ((hlm.mul (hlp.pow 2)).div_const 2)).add ((hlm.const_mul (log 2)).mul hlp)).add
      ((hlp.pow 3).div_const 3)).sub ((hlp.pow 2).const_mul (log 2 / 2))).add
      (hlm.const_mul (Li 2 (1 / 2)))).sub
      (hlp.const_mul (π ^ 2 / 6))).add_const _).congr_deriv ?_
    rw [kernel_zero, hpl_negOne_one hy, Li_two_one_add_div_two hy, Li_two_one_half]
    simp only [id, Pi.pow_apply, Pi.mul_apply]
    field_simp
    ring
  · have t1 := tendsto_Li_comp_zero (k := 3) (g := fun y => y) (by norm_num) continuousAt_id
      (by norm_num) fun y hy => ⟨by linarith [hy.1], hy.2.le⟩
    have t2 := tendsto_Li_comp_zero (k := 3) (g := fun y => -y) (by norm_num) continuousAt_neg
      (by norm_num) fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have t3 := tendsto_Li_comp_zero (k := 3) (g := fun y => 1 - y) (by norm_num)
      (by fun_prop) (by norm_num) fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have t4 := tendsto_Li_comp_zero (k := 3) (g := fun y => (1 - y) / 2) (by norm_num)
      (by fun_prop) (by norm_num) fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have t5 := tendsto_Li_comp_zero (k := 3) (g := fun y => (1 - y) / (1 + y)) (by norm_num)
      (by fun_prop (disch := norm_num)) (by norm_num) fun y hy =>
        ⟨by have : 0 < (1 - y) / (1 + y) := div_pos (by linarith [hy.2]) (by linarith [hy.1])
            linarith, by rw [div_le_one (by linarith [hy.1])]; linarith [hy.1]⟩
    have t6 := tendsto_Li_comp_zero (k := 3) (g := fun y => 2 * y / (1 + y)) (by norm_num)
      (by fun_prop (disch := norm_num)) (by norm_num) fun y hy =>
        ⟨by have : 0 < 2 * y / (1 + y) := by have := hy.1; have := hy.2; positivity
            linarith, by rw [div_le_one (by linarith [hy.1])]; linarith [hy.2]⟩
    have t7 := tendsto_Li_comp_zero (k := 2) (g := fun y => -y) le_rfl continuousAt_neg
      (by norm_num) fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have tp := tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 + y)) (c := 0)
      (by fun_prop (disch := norm_num)) (by simp)
    have tm := tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 - y)) (c := 0)
      (by fun_prop (disch := norm_num)) (by simp)
    have txp := QED.Polylog.HPL.tendsto_log_mul_log_one_add_zero
    have h := ((((((((((((((t1.sub t2).add t3).sub t4).sub t5).sub t6).add (tm.mul t7)).add
      ((txp.mul tm))).sub ((txp.mul tp).div_const 2)).sub ((tm.mul (tp.pow 2)).div_const 2)).add
      ((tm.const_mul (log 2)).mul tp)).add ((tp.pow 3).div_const 3)).sub
      ((tp.pow 2).const_mul (log 2 / 2))).add (tm.const_mul (Li 2 (1 / 2)))).sub
      (tp.const_mul (π ^ 2 / 6))).add_const (Li 3 (1 / 2))
    convert h using 2
    · ring
    · norm_num [Li_three_one]

/-- The closed form of `H(-1, 0, 1; x)` on `(0, 1)`, by the shuffle `H(-1) H(0, 1)`. -/
theorem hpl_negOne_zero_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero, one] x =
      log (1 + x) * Li 2 x - hpl [zero, negOne, one] x - hpl [zero, one, negOne] x := by
  have h := hpl_mul_hpl [negOne] [zero, one] hx
  simp [shuffle, shuffleAux, hpl_negOne hx, hpl_zero_one hx] at h
  linarith

/-- The closed form of `H(-1, 1, 0; x)` on `(0, 1)`, by the shuffle `H(0) H(-1, 1)`. -/
theorem hpl_negOne_one_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, zero] x =
      log x * hpl [negOne, one] x - hpl [zero, negOne, one] x - hpl [negOne, zero, one] x := by
  have h := hpl_mul_hpl [zero] [negOne, one] hx
  simp [shuffle, shuffleAux, hpl_zero] at h
  linarith

/-- The closed form of `H(1, 0, -1; x)` on `(0, 1)`, by the shuffle `H(1) H(0, -1)`. -/
theorem hpl_one_zero_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, negOne] x =
      log (1 - x) * Li 2 (-x) - hpl [zero, one, negOne] x - hpl [zero, negOne, one] x := by
  have h := hpl_mul_hpl [one] [zero, negOne] hx
  simp [shuffle, shuffleAux, hpl_one hx, hpl_zero_negOne hx] at h
  linarith

/-- The closed form of `H(1, -1, 0; x)` on `(0, 1)`, by the shuffle `H(0) H(1, -1)`. -/
theorem hpl_one_negOne_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, zero] x =
      log x * hpl [one, negOne] x - hpl [zero, one, negOne] x - hpl [one, zero, negOne] x := by
  have h := hpl_mul_hpl [zero] [one, negOne] hx
  simp [shuffle, shuffleAux, hpl_zero] at h
  linarith

end QED.Polylog.HPL
