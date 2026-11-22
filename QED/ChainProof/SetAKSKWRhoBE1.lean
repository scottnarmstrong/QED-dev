/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBS

/-!
# Set (a), stage D: the `β`-integrand on `β < σ₋` as a `ksWYe` combination

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. For
`β ∈ (0, σ₋)` (`σ± = (1 ± δ)/2`) the `w`-integrated `VB` density `ksWWEI β δ` is the combination
`ksWYe` of the generated lists `ksWY1L`, ..., `ksWY1S` (logarithms of `β - σ±` with polynomial
coefficients, difference quotients, poles at `β = 1`). The identity is split by logarithm: the
differences `ksWPH j a σ₊ - ksWPH j a σ₋` in closed form (`ksWY1_H*`), the logarithmic
coefficients of `ksWW3P` (`ksWY1_p*`) and one rational identity per logarithm (`ksWY1_k*`).
The lists and these lemmas are machine-generated; every coefficient is checked by the proofs.

Main result:

* **`ksWY1_eqOn`**: `ksWYe (ksWY1L δ) ... = ksWWEI · δ` on `(0, σ₋)`.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetAKS

variable {b d : ℝ}

/-- Region `1`: the terms `c β^j log (β - a)`. -/
noncomputable def ksWY1L (d : ℝ) : List (ℝ × ℕ × ℝ) := [
  ((2 * d ^ 3 + 4 * d ^ 2 - 6 * d + 8) / 3, 0, ((1 - d) / 2)),
  (-((8 * d ^ 2 + 32) / 3), 1, ((1 - d) / 2)),
  (12, 2, ((1 - d) / 2)),
  (-16 / 3, 3, ((1 - d) / 2)),
  ((2 * d ^ 3 - 4 * d ^ 2 - 6 * d - 8) / 3, 0, ((1 + d) / 2)),
  ((8 * d ^ 2 + 32) / 3, 1, ((1 + d) / 2)),
  (-12, 2, ((1 + d) / 2)),
  (16 / 3, 3, ((1 + d) / 2))]

/-- Region `1`: the monomials. -/
noncomputable def ksWY1P (d : ℝ) : List (ℝ × ℕ) := [
  (4 * log 2 * d * (d ^ 2 - 3) / 3 - 2 * log (1 - d) * d * (d ^ 2 - 3) / 3 - 2 * log (1 + d) * d
    * (d ^ 2 - 3) / 3 + d * (37 * d ^ 2 + 27) / 9, 0),
  (-(28 * d / 3), 1),
  (16 * d / 3, 2)]

/-- Region `1`: the difference quotients. -/
noncomputable def ksWY1D (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3), 1, ((1 - d) / 2)),
  (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3, 1, ((1 + d) / 2)),
  (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3, ((1 - d) / 2), 1),
  (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3), ((1 - d) / 2), ((1 + d) / 2)),
  (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3), ((1 + d) / 2), 1),
  (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3, ((1 + d) / 2), ((1 - d) / 2))]

/-- Region `1`: the double poles. -/
noncomputable def ksWY1Q (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  ((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12, ((1 - d) / 2), 1),
  (-((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12), ((1 + d) / 2), 1)]

/-- Region `1`: the triple poles. -/
noncomputable def ksWY1C (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3), ((1 - d) / 2), 1),
  ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3, ((1 + d) / 2), 1)]

/-- Region `1`: the rational simple and double poles. -/
noncomputable def ksWY1R (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (1, -(d * (d + 1) * (d - 1) / 3), log (1 - d) * (d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12
    - log (1 + d) * (d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12 + 4 * d * (d + 1) * (d - 1) * (2
    * d ^ 2 - 3) / 3)]

/-- Region `1`: the rational triple poles. -/
noncomputable def ksWY1S (d : ℝ) : List (ℝ × ℝ) := [
  (1, -(log (1 - d) * (d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) + log (1 + d) * (d + 1) ^ 2
    * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)]


theorem ksWY1_H1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 0 1 ((1 + d)
  / 2) - ksWPH 0 1 ((1 - d) / 2) = log (1 - d) * ((d - 1) / 2) + log (1 + d) * ((d + 1) / 2)
  + log 2 * (-d) + (-d) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    pow_zero, pow_one, one_pow, zero_add, mul_one, one_mul]
  simp only [ksWY_log_l1 hd.2, ksWY_log_l2 (by linarith [hd.1] : -1 < d)]
  field_simp
  ring

theorem ksWY1_H2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 1 1 ((1 + d)
  / 2) - ksWPH 1 1 ((1 - d) / 2) = log (1 - d) * ((d - 1) * (d + 3) / 8) + log (1 + d) * (-((d
  + 1) * (d - 3) / 8)) + log 2 * (-(d / 2)) + (-(3 * d / 4)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add, mul_one]
  simp only [ksWY_log_l1 hd.2, ksWY_log_l2 (by linarith [hd.1] : -1 < d)]
  field_simp
  ring

theorem ksWY1_H3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 2 1 ((1 + d)
  / 2) - ksWPH 2 1 ((1 - d) / 2) = log (1 - d) * ((d - 1) * (d ^ 2 + 4 * d + 7) / 24) + log (1
  + d) * ((d + 1) * (d ^ 2 - 4 * d + 7) / 24) + log 2 * (-(d * (d ^ 2 + 3) / 12)) + (-(d * (d ^ 2
  + 21) / 36)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add, mul_one]
  simp only [ksWY_log_l1 hd.2, ksWY_log_l2 (by linarith [hd.1] : -1 < d)]
  field_simp
  ring

theorem ksWY1_H4 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 1 ((1 - d)
  / 2) ((1 + d) / 2) - ksWPH 1 ((1 - d) / 2) ((1 - d) / 2) = log d * (d / 2) + (d * (d - 2)
  / 4) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_log_l3, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY1_H5 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 2 ((1 - d)
  / 2) ((1 + d) / 2) - ksWPH 2 ((1 - d) / 2) ((1 - d) / 2) = log d * (d * (d ^ 2 + 3) / 12) + (-(d
  * (4 * d ^ 2 - 9 * d + 9) / 36)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_l3, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY1_H6 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 1 ((1 + d)
  / 2) ((1 + d) / 2) - ksWPH 1 ((1 + d) / 2) ((1 - d) / 2) = log d * (d / 2) + (-(d * (d + 2)
  / 4)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_log_l4, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY1_H7 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 2 ((1 + d)
  / 2) ((1 + d) / 2) - ksWPH 2 ((1 + d) / 2) ((1 - d) / 2) = log d * (d * (d ^ 2 + 3) / 12) + (-(d
  * (4 * d ^ 2 + 9 * d + 9) / 36)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_l4, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY1_H8 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 0 b ((1 + d)
  / 2) - ksWPH 0 b ((1 - d) / 2) = log (b - (1 - d) / 2) * ((2 * b + d - 1) / 2) + log (b - (1
  + d) / 2) * (-((2 * b - d - 1) / 2)) + (-d) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.reduceSub, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_log_swap ((1 - d) / 2) b, ksWY_log_swap ((1 + d) / 2) b]
  field_simp
  ring

theorem ksWY1_H9 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 1 b ((1 + d)
  / 2) - ksWPH 1 b ((1 - d) / 2) = log (b - (1 - d) / 2) * ((2 * b - d + 1) * (2 * b + d - 1) / 8)
  + log (b - (1 + d) / 2) * (-((2 * b + d + 1) * (2 * b - d - 1) / 8)) + (-(d * (2 * b + 1)
  / 4)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_log_swap ((1 - d) / 2) b, ksWY_log_swap ((1 + d) / 2) b]
  field_simp
  ring

theorem ksWY1_H10 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 2 b ((1 + d)
  / 2) - ksWPH 2 b ((1 - d) / 2) = log (b - (1 - d) / 2) * ((2 * b + d - 1) * (4 * b ^ 2 - 2 * b
  * d + 2 * b + d ^ 2 - 2 * d + 1) / 24) + log (b - (1 + d) / 2) * (-((2 * b - d - 1) * (4 * b ^ 2
  + 2 * b * d + 2 * b + d ^ 2 + 2 * d + 1) / 24)) + (-(d * (12 * b ^ 2 + 6 * b + d ^ 2 + 3)
  / 36)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_swap ((1 - d) / 2) b, ksWY_log_swap ((1 + d) / 2) b]
  field_simp
  ring

theorem ksWY1_H11 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 0 (1 - 1
  / ((1 - b) * ksDT 1 d)) ((1 + d) / 2) - ksWPH 0 (1 - 1 / ((1 - b) * ksDT 1 d)) ((1 - d)
  / 2) = log (b - (1 - d) / 2) * ((d - 1) * (2 * b + d - 1) / (4 * b - 4)) + log (b - (1 + d) / 2)
  * ((d + 1) * (2 * b - d - 1) / (4 * b - 4)) + log (1 - b) * (-d) + log (1 - d) * ((d - 1) * (2
  * b + d - 1) / (4 * b - 4)) + log (1 + d) * ((d + 1) * (2 * b - d - 1) / (4 * b - 4)) + log 2
  * (-d) + (-d) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.reduceSub, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_sp_sub_w0 hd hb1, ksWY_sm_sub_w0 hd hb1, ksWY_log_w0p hd hm hb1,
    ksWY_log_w0m hd hp hb1]
  field_simp
  ring

theorem ksWY1_H12 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 1 (1 - 1
  / ((1 - b) * ksDT 1 d)) ((1 + d) / 2) - ksWPH 1 (1 - 1 / ((1 - b) * ksDT 1 d)) ((1 - d)
  / 2) = log (b - (1 - d) / 2) * ((d - 1) * (2 * b + d - 1) * (2 * b * d + 6 * b - d ^ 2 - 2 * d
  - 5) / (32 * (b - 1) ^ 2)) + log (b - (1 + d) / 2) * (-((d + 1) * (2 * b - d - 1) * (2 * b * d
  - 6 * b + d ^ 2 - 2 * d + 5) / (32 * (b - 1) ^ 2))) + log (1 - b) * (-(d / 2)) + log (1 - d)
  * ((d - 1) * (2 * b + d - 1) * (2 * b * d + 6 * b - d ^ 2 - 2 * d - 5) / (32 * (b - 1) ^ 2))
  + log (1 + d) * (-((d + 1) * (2 * b - d - 1) * (2 * b * d - 6 * b + d ^ 2 - 2 * d + 5) / (32
  * (b - 1) ^ 2))) + log 2 * (-(d / 2)) + (-(d * (6 * b - d ^ 2 - 5) / (8 * b - 8))) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_sp_sub_w0 hd hb1, ksWY_sm_sub_w0 hd hb1, ksWY_log_w0p hd hm hb1,
    ksWY_log_w0m hd hp hb1]
  try rw [ksWW_inv_K hd h1b]
  field_simp
  ring

theorem ksWY1_H13 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ksWPH 2 (1 - 1
  / ((1 - b) * ksDT 1 d)) ((1 + d) / 2) - ksWPH 2 (1 - 1 / ((1 - b) * ksDT 1 d)) ((1 - d)
  / 2) = log (b - (1 - d) / 2) * ((d - 1) * (2 * b + d - 1) * (4 * b ^ 2 * d ^ 2 + 16 * d * b ^ 2
  + 28 * b ^ 2 - 2 * b * d ^ 3 - 18 * b * d ^ 2 - 30 * b * d - 46 * b + d ^ 4 + 2 * d ^ 3 + 12
  * d ^ 2 + 14 * d + 19) / (192 * (b - 1) ^ 3)) + log (b - (1 + d) / 2) * ((d + 1) * (2 * b - d
  - 1) * (4 * b ^ 2 * d ^ 2 - 16 * d * b ^ 2 + 28 * b ^ 2 + 2 * b * d ^ 3 - 18 * b * d ^ 2 + 30
  * b * d - 46 * b + d ^ 4 - 2 * d ^ 3 + 12 * d ^ 2 - 14 * d + 19) / (192 * (b - 1) ^ 3)) + log (1
  - b) * (-(d * (d ^ 2 + 3) / 12)) + log (1 - d) * ((d - 1) * (2 * b + d - 1) * (4 * b ^ 2 * d ^ 2
  + 16 * d * b ^ 2 + 28 * b ^ 2 - 2 * b * d ^ 3 - 18 * b * d ^ 2 - 30 * b * d - 46 * b + d ^ 4 + 2
  * d ^ 3 + 12 * d ^ 2 + 14 * d + 19) / (192 * (b - 1) ^ 3)) + log (1 + d) * ((d + 1) * (2 * b - d
  - 1) * (4 * b ^ 2 * d ^ 2 - 16 * d * b ^ 2 + 28 * b ^ 2 + 2 * b * d ^ 3 - 18 * b * d ^ 2 + 30
  * b * d - 46 * b + d ^ 4 - 2 * d ^ 3 + 12 * d ^ 2 - 14 * d + 19) / (192 * (b - 1) ^ 3)) + log 2
  * (-(d * (d ^ 2 + 3) / 12)) + (-(d * (4 * b ^ 2 * d ^ 2 + 84 * b ^ 2 - 38 * b * d ^ 2 - 138 * b
  + 3 * d ^ 4 + 28 * d ^ 2 + 57) / (144 * (b - 1) ^ 2))) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_sp_sub_w0 hd hb1, ksWY_sm_sub_w0 hd hb1, ksWY_log_w0p hd hm hb1,
    ksWY_log_w0m hd hp hb1]
  try rw [ksWW_inv_K hd h1b]
  field_simp
  ring

theorem ksWY1_p0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ((16 * log (1 - b)
  * ksDT 1 d ^ 2 * b ^ 3 - 32 * log (1 - b) * ksDT 1 d ^ 2 * b ^ 2 + 16 * log (1 - b) * b
  * ksDT 1 d ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d ^ 2 * b ^ 3 + 32
  * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d ^ 2 * b ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b) * b
  * ksDT 1 d ^ 2 + 16 * log (ksDT 1 d) * ksDT 1 d ^ 2 * b ^ 3 - 32 * log (ksDT 1 d) * ksDT 1 d ^ 2
  * b ^ 2 + 16 * log (ksDT 1 d) * b * ksDT 1 d ^ 2 - 16 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b + 8
  * ksDT 1 d + 48) / (ksDT 1 d ^ 2 * (b - 1) ^ 2)) = log (1 - b) * (16 * b)
  + log (ksDA 1 (-ksDT 1 d) b) * (-(16 * b)) + log (ksDT 1 d) * (16 * b) + (-((16 * ksDT 1 d
  * b ^ 2 - 8 * ksDT 1 d * b - 8 * ksDT 1 d - 48) / (ksDT 1 d ^ 2 * (b - 1) ^ 2))) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY1_p1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (-((16 * log (1
  - b) * ksDT 1 d * b ^ 2 - 8 * log (1 - b) * ksDT 1 d * b - 8 * log (1 - b) * ksDT 1 d - 16
  * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b ^ 2 + 16 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b
  + 16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 - 8 * log (ksDT 1 d) * ksDT 1 d * b - 8
  * log (ksDT 1 d) * ksDT 1 d - 4 * ksDT 1 d * b + 4 * ksDT 1 d - 40) / (ksDT 1 d * (b
  - 1)))) = log (1 - b) * (-((16 * b + 8))) + log (ksDA 1 (-ksDT 1 d) b) * (16 * b)
  + log (ksDT 1 d) * (-((16 * b + 8))) + ((4 * ksDT 1 d * b - 4 * ksDT 1 d + 40) / (ksDT 1 d * (b
  - 1))) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY1_p2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ((8 * log (1 - b)
  + 8 * log (ksDT 1 d) - 4)) = log (1 - b) * (8) + log (ksDT 1 d) * (8) + (-4) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY1_k0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (-(16 * b)) * (-d)
  + ((16 * b + 8)) * (-(3 * d / 4)) + (-8) * (-(d * (d ^ 2 + 21) / 36)) + (-((16 * ksDT 1 d - 32)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (d * (d - 2) / 4) + ((16 * ksDT 1 d - 32)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * (-(d * (4 * d ^ 2 - 9 * d + 9) / 36)) + (-((16
  * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (-(d * (d + 2) / 4)) + ((16
  * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * (-(d * (4 * d ^ 2 + 9 * d + 9)
  / 36)) + (16 * b) * (-d) + (-((16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b
  - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (-(d * (2 * b + 1)
  / 4)) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2
  - ksDT 1 d * b + 1)) * (-(d * (12 * b ^ 2 + 6 * b + d ^ 2 + 3) / 36)) + (16 * b) * (-d) + (-((16
  * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (-(d * (6 * b - d ^ 2 - 5) / (8 * b - 8))) + ((8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) * (-(d * (4 * b ^ 2 * d ^ 2 + 84 * b ^ 2 - 38 * b * d ^ 2 - 138 * b + 3 * d ^ 4 + 28
  * d ^ 2 + 57) / (144 * (b - 1) ^ 2))) + (1 * (-((16 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 8
  * ksDT 1 d - 48) / (ksDT 1 d ^ 2 * (b - 1) ^ 2)))) * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1)
  / 1) + (1 * ((4 * ksDT 1 d * b - 4 * ksDT 1 d + 40) / (ksDT 1 d * (b - 1)))) * ((((1 + d)
  / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (1 * (-4)) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3)
  + -(((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4 * (b - 1) ^ 4)) / ((1 - d)
  / 2 * (b - (1 - d) / 2) / (1 - b)) - ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8)
  / (ksDT 1 d ^ 4 * (b - 1) ^ 4)) / ((1 + d) / 2 * (b - (1 + d) / 2) / (1 - b))) = (d * (37
  * d ^ 2 + 27) / 9) * b ^ 0 + (-(28 * d / 3)) * b ^ 1 + (16 * d / 3) * b ^ 2 + (-(d * (d + 1)
  * (d - 1) / 3)) * (b - 1)⁻¹ + (4 * d * (d + 1) * (d - 1) * (2 * d ^ 2 - 3) / 3) * ((b
  - 1) ^ 2)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWY_ksDT_quad hd]
  obtain ⟨x, rfl⟩ : ∃ x, d = 1 - 2 * x := ⟨(1 - d) / 2, by ring⟩
  have hx : x ≠ 0 := (by linarith [hd.2] : 0 < x).ne'
  have h1x : 1 - x ≠ 0 := (by linarith [hd.1] : 0 < 1 - x).ne'
  have e1 : (1 - (1 - 2 * x)) / 2 = x := by ring
  have e2 : (1 + (1 - 2 * x)) / 2 = 1 - x := by ring
  have hden : (1 : ℝ) - (1 - 2 * x) ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
    exact mul_ne_zero four_ne_zero (mul_ne_zero hx h1x)
  have eT : ksDT 1 (1 - 2 * x) = 1 / (x * (1 - x)) := by
    unfold ksDT
    rw [div_eq_div_iff hden (mul_ne_zero hx h1x)]
    ring
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY1_kA (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (16 * b) * ((2 * b
  + d - 1) / 2) + (-((16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * ((2 * b - d + 1) * (2 * b
  + d - 1) / 8) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1)) * ((2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2 * d
  + 1) / 24) + (16 * b) * ((d - 1) * (2 * b + d - 1) / (4 * b - 4)) + (-((16 * ksDT 1 d * b ^ 3
  - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2
  - ksDT 1 d * b + 1))) * ((d - 1) * (2 * b + d - 1) * (2 * b * d + 6 * b - d ^ 2 - 2 * d - 5)
  / (32 * (b - 1) ^ 2)) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * ((d - 1) * (2 * b + d - 1) * (4 * b ^ 2 * d ^ 2 + 16
  * d * b ^ 2 + 28 * b ^ 2 - 2 * b * d ^ 3 - 18 * b * d ^ 2 - 30 * b * d - 46 * b + d ^ 4 + 2
  * d ^ 3 + 12 * d ^ 2 + 14 * d + 19) / (192 * (b - 1) ^ 3)) + (1 * (-(16 * b))) * ((((1 + d)
  / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (1 * (16 * b)) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2)
  / 2) + 1 * (-((8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d - 56) / (ksDT 1 d ^ 3
  * (b - 1) ^ 3))) = ((2 * d ^ 3 + 4 * d ^ 2 - 6 * d + 8) / 3) * b ^ 0 + (-((8 * d ^ 2 + 32) / 3))
  * b ^ 1 + 12 * b ^ 2 + (-16 / 3) * b ^ 3 + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - 1)⁻¹
  + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 + d) / 2))⁻¹ + ((d + 1) * (d - 1) * (17
  * d ^ 2 - 25) / 12) * ((b - 1) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3))
  * ((b - 1) ^ 3)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWY_ksDT_quad hd]
  obtain ⟨x, rfl⟩ : ∃ x, d = 1 - 2 * x := ⟨(1 - d) / 2, by ring⟩
  have hx : x ≠ 0 := (by linarith [hd.2] : 0 < x).ne'
  have h1x : 1 - x ≠ 0 := (by linarith [hd.1] : 0 < 1 - x).ne'
  have e1 : (1 - (1 - 2 * x)) / 2 = x := by ring
  have e2 : (1 + (1 - 2 * x)) / 2 = 1 - x := by ring
  have hden : (1 : ℝ) - (1 - 2 * x) ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
    exact mul_ne_zero four_ne_zero (mul_ne_zero hx h1x)
  have eT : ksDT 1 (1 - 2 * x) = 1 / (x * (1 - x)) := by
    unfold ksDT
    rw [div_eq_div_iff hden (mul_ne_zero hx h1x)]
    ring
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY1_kB (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (16 * b) * (-((2
  * b - d - 1) / 2)) + (-((16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (-((2 * b + d + 1) * (2
  * b - d - 1) / 8)) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1)) * (-((2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2
  * d + 1) / 24)) + (16 * b) * ((d + 1) * (2 * b - d - 1) / (4 * b - 4)) + (-((16 * ksDT 1 d
  * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1))) * (-((d + 1) * (2 * b - d - 1) * (2 * b * d - 6 * b + d ^ 2 - 2
  * d + 5) / (32 * (b - 1) ^ 2))) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d
  + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * ((d + 1) * (2 * b - d - 1) * (4 * b ^ 2 * d ^ 2
  - 16 * d * b ^ 2 + 28 * b ^ 2 + 2 * b * d ^ 3 - 18 * b * d ^ 2 + 30 * b * d - 46 * b + d ^ 4 - 2
  * d ^ 3 + 12 * d ^ 2 - 14 * d + 19) / (192 * (b - 1) ^ 3)) + (1 * (-(16 * b))) * ((((1 + d)
  / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (1 * (16 * b)) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2)
  / 2) + -1 * (-((8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d - 56) / (ksDT 1 d ^ 3
  * (b - 1) ^ 3))) = ((2 * d ^ 3 - 4 * d ^ 2 - 6 * d - 8) / 3) * b ^ 0 + ((8 * d ^ 2 + 32) / 3)
  * b ^ 1 + (-12) * b ^ 2 + (16 / 3) * b ^ 3 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - 1)⁻¹
  + (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 - d) / 2))⁻¹ + (-((d + 1) * (d - 1) * (17
  * d ^ 2 - 25) / 12)) * ((b - 1) ^ 2)⁻¹ + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) * ((b
  - 1) ^ 3)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWY_ksDT_quad hd]
  obtain ⟨x, rfl⟩ : ∃ x, d = 1 - 2 * x := ⟨(1 - d) / 2, by ring⟩
  have hx : x ≠ 0 := (by linarith [hd.2] : 0 < x).ne'
  have h1x : 1 - x ≠ 0 := (by linarith [hd.1] : 0 < 1 - x).ne'
  have e1 : (1 - (1 - 2 * x)) / 2 = x := by ring
  have e2 : (1 + (1 - 2 * x)) / 2 = 1 - x := by ring
  have hden : (1 : ℝ) - (1 - 2 * x) ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
    exact mul_ne_zero four_ne_zero (mul_ne_zero hx h1x)
  have eT : ksDT 1 (1 - 2 * x) = 1 / (x * (1 - x)) := by
    unfold ksDT
    rw [div_eq_div_iff hden (mul_ne_zero hx h1x)]
    ring
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY1_kC (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (16 * b) * (-d)
  + (-((16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b
  + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (-(d / 2)) + ((8 * ksDT 1 d * b ^ 2 - 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * (-(d * (d ^ 2
  + 3) / 12)) + (1 * (16 * b)) * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (1 * (-((16 * b
  + 8)))) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (1 * (8)) * ((((1 + d) / 2) ^ 3 - ((1
  - d) / 2) ^ 3) / 3) = (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ + (2
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d) / 2))⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWY_ksDT_quad hd]
  obtain ⟨x, rfl⟩ : ∃ x, d = 1 - 2 * x := ⟨(1 - d) / 2, by ring⟩
  have hx : x ≠ 0 := (by linarith [hd.2] : 0 < x).ne'
  have h1x : 1 - x ≠ 0 := (by linarith [hd.1] : 0 < 1 - x).ne'
  have e1 : (1 - (1 - 2 * x)) / 2 = x := by ring
  have e2 : (1 + (1 - 2 * x)) / 2 = 1 - x := by ring
  have hden : (1 : ℝ) - (1 - 2 * x) ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
    exact mul_ne_zero four_ne_zero (mul_ne_zero hx h1x)
  have eT : ksDT 1 (1 - 2 * x) = 1 / (x * (1 - x)) := by
    unfold ksDT
    rw [div_eq_div_iff hden (mul_ne_zero hx h1x)]
    ring
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY1_kM (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (-(16 * b)) * ((d
  - 1) / 2) + ((16 * b + 8)) * ((d - 1) * (d + 3) / 8) + (-8) * ((d - 1) * (d ^ 2 + 4 * d + 7)
  / 24) + (16 * b) * ((d - 1) * (2 * b + d - 1) / (4 * b - 4)) + (-((16 * ksDT 1 d * b ^ 3 - 8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2
  - ksDT 1 d * b + 1))) * ((d - 1) * (2 * b + d - 1) * (2 * b * d + 6 * b - d ^ 2 - 2 * d - 5)
  / (32 * (b - 1) ^ 2)) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * ((d - 1) * (2 * b + d - 1) * (4 * b ^ 2 * d ^ 2 + 16
  * d * b ^ 2 + 28 * b ^ 2 - 2 * b * d ^ 3 - 18 * b * d ^ 2 - 30 * b * d - 46 * b + d ^ 4 + 2
  * d ^ 3 + 12 * d ^ 2 + 14 * d + 19) / (192 * (b - 1) ^ 3)) + (-1 * (-(16 * b)) + -1 * (16 * b))
  * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (-1 * (16 * b) + -1 * (-((16 * b + 8))))
  * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (-1 * (8)) * ((((1 + d) / 2) ^ 3 - ((1 - d)
  / 2) ^ 3) / 3) + 1 * (-((8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d - 56)
  / (ksDT 1 d ^ 3 * (b - 1) ^ 3))) = (-(2 * d * (d ^ 2 - 3) / 3)) * b ^ 0 + (-(2 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3)) * (b - ((1 + d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - 1)⁻¹
  + ((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12) * ((b - 1) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2
  * (2 * d ^ 2 - 3) / 3)) * ((b - 1) ^ 3)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWY_ksDT_quad hd]
  obtain ⟨x, rfl⟩ : ∃ x, d = 1 - 2 * x := ⟨(1 - d) / 2, by ring⟩
  have hx : x ≠ 0 := (by linarith [hd.2] : 0 < x).ne'
  have h1x : 1 - x ≠ 0 := (by linarith [hd.1] : 0 < 1 - x).ne'
  have e1 : (1 - (1 - 2 * x)) / 2 = x := by ring
  have e2 : (1 + (1 - 2 * x)) / 2 = 1 - x := by ring
  have hden : (1 : ℝ) - (1 - 2 * x) ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
    exact mul_ne_zero four_ne_zero (mul_ne_zero hx h1x)
  have eT : ksDT 1 (1 - 2 * x) = 1 / (x * (1 - x)) := by
    unfold ksDT
    rw [div_eq_div_iff hden (mul_ne_zero hx h1x)]
    ring
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY1_kN (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (-(16 * b)) * ((d
  + 1) / 2) + ((16 * b + 8)) * (-((d + 1) * (d - 3) / 8)) + (-8) * ((d + 1) * (d ^ 2 - 4 * d + 7)
  / 24) + (16 * b) * ((d + 1) * (2 * b - d - 1) / (4 * b - 4)) + (-((16 * ksDT 1 d * b ^ 3 - 8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2
  - ksDT 1 d * b + 1))) * (-((d + 1) * (2 * b - d - 1) * (2 * b * d - 6 * b + d ^ 2 - 2 * d + 5)
  / (32 * (b - 1) ^ 2))) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * ((d + 1) * (2 * b - d - 1) * (4 * b ^ 2 * d ^ 2 - 16
  * d * b ^ 2 + 28 * b ^ 2 + 2 * b * d ^ 3 - 18 * b * d ^ 2 + 30 * b * d - 46 * b + d ^ 4 - 2
  * d ^ 3 + 12 * d ^ 2 - 14 * d + 19) / (192 * (b - 1) ^ 3)) + (-1 * (-(16 * b)) + -1 * (16 * b))
  * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (-1 * (16 * b) + -1 * (-((16 * b + 8))))
  * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (-1 * (8)) * ((((1 + d) / 2) ^ 3 - ((1 - d)
  / 2) ^ 3) / 3) + -1 * (-((8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d - 56)
  / (ksDT 1 d ^ 3 * (b - 1) ^ 3))) = (-(2 * d * (d ^ 2 - 3) / 3)) * b ^ 0 + (2 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3) * (b - ((1 - d) / 2))⁻¹ + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - 1)⁻¹
  + (-((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12)) * ((b - 1) ^ 2)⁻¹ + ((d + 1) ^ 2 * (d - 1) ^ 2
  * (2 * d ^ 2 - 3) / 3) * ((b - 1) ^ 3)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWY_ksDT_quad hd]
  obtain ⟨x, rfl⟩ : ∃ x, d = 1 - 2 * x := ⟨(1 - d) / 2, by ring⟩
  have hx : x ≠ 0 := (by linarith [hd.2] : 0 < x).ne'
  have h1x : 1 - x ≠ 0 := (by linarith [hd.1] : 0 < 1 - x).ne'
  have e1 : (1 - (1 - 2 * x)) / 2 = x := by ring
  have e2 : (1 + (1 - 2 * x)) / 2 = 1 - x := by ring
  have hden : (1 : ℝ) - (1 - 2 * x) ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
    exact mul_ne_zero four_ne_zero (mul_ne_zero hx h1x)
  have eT : ksDT 1 (1 - 2 * x) = 1 / (x * (1 - x)) := by
    unfold ksDT
    rw [div_eq_div_iff hden (mul_ne_zero hx h1x)]
    ring
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY1_kK (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (-(16 * b)) * (-d)
  + ((16 * b + 8)) * (-(d / 2)) + (-8) * (-(d * (d ^ 2 + 3) / 12)) + (16 * b) * (-d) + (-((16
  * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (-(d / 2)) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d
  * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * (-(d * (d ^ 2 + 3) / 12))
  + (2 * (-(16 * b)) + 2 * (16 * b)) * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (2 * (16
  * b) + 2 * (-((16 * b + 8)))) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (2 * (8))
  * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) = (4 * d * (d ^ 2 - 3) / 3) * b ^ 0 + (-(2
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)
  * (b - ((1 + d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - 1)⁻¹ + (-(2 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3)) * (b - 1)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWY_ksDT_quad hd]
  obtain ⟨x, rfl⟩ : ∃ x, d = 1 - 2 * x := ⟨(1 - d) / 2, by ring⟩
  have hx : x ≠ 0 := (by linarith [hd.2] : 0 < x).ne'
  have h1x : 1 - x ≠ 0 := (by linarith [hd.1] : 0 < 1 - x).ne'
  have e1 : (1 - (1 - 2 * x)) / 2 = x := by ring
  have e2 : (1 + (1 - 2 * x)) / 2 = 1 - x := by ring
  have hden : (1 : ℝ) - (1 - 2 * x) ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
    exact mul_ne_zero four_ne_zero (mul_ne_zero hx h1x)
  have eT : ksDT 1 (1 - 2 * x) = 1 / (x * (1 - x)) := by
    unfold ksDT
    rw [div_eq_div_iff hden (mul_ne_zero hx h1x)]
    ring
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY1_kD (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (-((16 * ksDT 1 d
  - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (d / 2) + ((16 * ksDT 1 d - 32) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1)) * (d * (d ^ 2 + 3) / 12) + (-((16 * ksDT 1 d - 32) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1))) * (d / 2) + ((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d
  * b + 1)) * (d * (d ^ 2 + 3) / 12) = (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d) / 2))⁻¹
  + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWY_ksDT_quad hd]
  obtain ⟨x, rfl⟩ : ∃ x, d = 1 - 2 * x := ⟨(1 - d) / 2, by ring⟩
  have hx : x ≠ 0 := (by linarith [hd.2] : 0 < x).ne'
  have h1x : 1 - x ≠ 0 := (by linarith [hd.1] : 0 < 1 - x).ne'
  have e1 : (1 - (1 - 2 * x)) / 2 = x := by ring
  have e2 : (1 + (1 - 2 * x)) / 2 = 1 - x := by ring
  have hden : (1 : ℝ) - (1 - 2 * x) ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
    exact mul_ne_zero four_ne_zero (mul_ne_zero hx h1x)
  have eT : ksDT 1 (1 - 2 * x) = 1 / (x * (1 - x)) := by
    unfold ksDT
    rw [div_eq_div_iff hden (mul_ne_zero hx h1x)]
    ring
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY1_eqOn (hd : d ∈ Ioo (0 : ℝ) 1) :
    EqOn (ksWYe (ksWY1L d) (ksWY1P d) (ksWY1D d) (ksWY1Q d) (ksWY1C d) (ksWY1R d) (ksWY1S d))
      (fun b => ksWWEI b d) (Ioo 0 ((1 - d) / 2)) := by
  intro b hb
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.2]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.2, hd.1]
  have hb1 : b ≠ 1 := by linarith [hb.2, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  obtain ⟨c1, hc1⟩ : ∃ x : ℝ, x = -(16 * b) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = (16 * b + 8) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ x : ℝ, x = -8 := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ x : ℝ, x = -((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
    + 1)) := ⟨_, rfl⟩
  obtain ⟨c5, hc5⟩ : ∃ x : ℝ, x = (16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
    + 1) := ⟨_, rfl⟩
  obtain ⟨c6, hc6⟩ : ∃ x : ℝ, x = 16 * b := ⟨_, rfl⟩
  obtain ⟨c7, hc7⟩ : ∃ x : ℝ, x = -((16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d
    * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) := ⟨_, rfl⟩
  obtain ⟨c8, hc8⟩ : ∃ x : ℝ, x = (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1) := ⟨_, rfl⟩
  obtain ⟨c9, hc9⟩ : ∃ x : ℝ, x = (16 * log (1 - b) * ksDT 1 d ^ 2 * b ^ 3 - 32 * log (1 - b)
    * ksDT 1 d ^ 2 * b ^ 2 + 16 * log (1 - b) * b * ksDT 1 d ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b)
    * ksDT 1 d ^ 2 * b ^ 3 + 32 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d ^ 2 * b ^ 2 - 16
    * log (ksDA 1 (-ksDT 1 d) b) * b * ksDT 1 d ^ 2 + 16 * log (ksDT 1 d) * ksDT 1 d ^ 2 * b ^ 3
    - 32 * log (ksDT 1 d) * ksDT 1 d ^ 2 * b ^ 2 + 16 * log (ksDT 1 d) * b * ksDT 1 d ^ 2 - 16
    * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b + 8 * ksDT 1 d + 48) / (ksDT 1 d ^ 2 * (b
    - 1) ^ 2) := ⟨_, rfl⟩
  obtain ⟨c10, hc10⟩ : ∃ x : ℝ, x = -((16 * log (1 - b) * ksDT 1 d * b ^ 2 - 8 * log (1 - b)
    * ksDT 1 d * b - 8 * log (1 - b) * ksDT 1 d - 16 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d
    * b ^ 2 + 16 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b + 16 * log (ksDT 1 d) * ksDT 1 d
    * b ^ 2 - 8 * log (ksDT 1 d) * ksDT 1 d * b - 8 * log (ksDT 1 d) * ksDT 1 d - 4 * ksDT 1 d * b
    + 4 * ksDT 1 d - 40) / (ksDT 1 d * (b - 1))) := ⟨_, rfl⟩
  obtain ⟨c11, hc11⟩ : ∃ x : ℝ, x = (8 * log (1 - b) + 8 * log (ksDT 1 d) - 4) := ⟨_, rfl⟩
  obtain ⟨c12, hc12⟩ : ∃ x : ℝ, x = -((8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d
    - 56) / (ksDT 1 d ^ 3 * (b - 1) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨c13, hc13⟩ : ∃ x : ℝ, x = (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4
    * (b - 1) ^ 4) := ⟨_, rfl⟩
  obtain ⟨k14, hk14⟩ : ∃ x : ℝ, x = (d - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨k15, hk15⟩ : ∃ x : ℝ, x = (d + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨k16, hk16⟩ : ∃ x : ℝ, x = -d := ⟨_, rfl⟩
  obtain ⟨k17, hk17⟩ : ∃ x : ℝ, x = -d := ⟨_, rfl⟩
  obtain ⟨k18, hk18⟩ : ∃ x : ℝ, x = (d - 1) * (d + 3) / 8 := ⟨_, rfl⟩
  obtain ⟨k19, hk19⟩ : ∃ x : ℝ, x = -((d + 1) * (d - 3) / 8) := ⟨_, rfl⟩
  obtain ⟨k20, hk20⟩ : ∃ x : ℝ, x = -(d / 2) := ⟨_, rfl⟩
  obtain ⟨k21, hk21⟩ : ∃ x : ℝ, x = -(3 * d / 4) := ⟨_, rfl⟩
  obtain ⟨k22, hk22⟩ : ∃ x : ℝ, x = (d - 1) * (d ^ 2 + 4 * d + 7) / 24 := ⟨_, rfl⟩
  obtain ⟨k23, hk23⟩ : ∃ x : ℝ, x = (d + 1) * (d ^ 2 - 4 * d + 7) / 24 := ⟨_, rfl⟩
  obtain ⟨k24, hk24⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 3) / 12) := ⟨_, rfl⟩
  obtain ⟨k25, hk25⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 21) / 36) := ⟨_, rfl⟩
  obtain ⟨k26, hk26⟩ : ∃ x : ℝ, x = d / 2 := ⟨_, rfl⟩
  obtain ⟨k27, hk27⟩ : ∃ x : ℝ, x = d * (d - 2) / 4 := ⟨_, rfl⟩
  obtain ⟨k28, hk28⟩ : ∃ x : ℝ, x = d * (d ^ 2 + 3) / 12 := ⟨_, rfl⟩
  obtain ⟨k29, hk29⟩ : ∃ x : ℝ, x = -(d * (4 * d ^ 2 - 9 * d + 9) / 36) := ⟨_, rfl⟩
  obtain ⟨k30, hk30⟩ : ∃ x : ℝ, x = d / 2 := ⟨_, rfl⟩
  obtain ⟨k31, hk31⟩ : ∃ x : ℝ, x = -(d * (d + 2) / 4) := ⟨_, rfl⟩
  obtain ⟨k32, hk32⟩ : ∃ x : ℝ, x = d * (d ^ 2 + 3) / 12 := ⟨_, rfl⟩
  obtain ⟨k33, hk33⟩ : ∃ x : ℝ, x = -(d * (4 * d ^ 2 + 9 * d + 9) / 36) := ⟨_, rfl⟩
  obtain ⟨k34, hk34⟩ : ∃ x : ℝ, x = (2 * b + d - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨k35, hk35⟩ : ∃ x : ℝ, x = -((2 * b - d - 1) / 2) := ⟨_, rfl⟩
  obtain ⟨k36, hk36⟩ : ∃ x : ℝ, x = -d := ⟨_, rfl⟩
  obtain ⟨k37, hk37⟩ : ∃ x : ℝ, x = (2 * b - d + 1) * (2 * b + d - 1) / 8 := ⟨_, rfl⟩
  obtain ⟨k38, hk38⟩ : ∃ x : ℝ, x = -((2 * b + d + 1) * (2 * b - d - 1) / 8) := ⟨_, rfl⟩
  obtain ⟨k39, hk39⟩ : ∃ x : ℝ, x = -(d * (2 * b + 1) / 4) := ⟨_, rfl⟩
  obtain ⟨k40, hk40⟩ : ∃ x : ℝ, x = (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2
    * d + 1) / 24 := ⟨_, rfl⟩
  obtain ⟨k41, hk41⟩ : ∃ x : ℝ, x = -((2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2
    * d + 1) / 24) := ⟨_, rfl⟩
  obtain ⟨k42, hk42⟩ : ∃ x : ℝ, x = -(d * (12 * b ^ 2 + 6 * b + d ^ 2 + 3) / 36) := ⟨_, rfl⟩
  obtain ⟨k43, hk43⟩ : ∃ x : ℝ, x = (d - 1) * (2 * b + d - 1) / (4 * b - 4) := ⟨_, rfl⟩
  obtain ⟨k44, hk44⟩ : ∃ x : ℝ, x = (d + 1) * (2 * b - d - 1) / (4 * b - 4) := ⟨_, rfl⟩
  obtain ⟨k45, hk45⟩ : ∃ x : ℝ, x = -d := ⟨_, rfl⟩
  obtain ⟨k46, hk46⟩ : ∃ x : ℝ, x = (d - 1) * (2 * b + d - 1) / (4 * b - 4) := ⟨_, rfl⟩
  obtain ⟨k47, hk47⟩ : ∃ x : ℝ, x = (d + 1) * (2 * b - d - 1) / (4 * b - 4) := ⟨_, rfl⟩
  obtain ⟨k48, hk48⟩ : ∃ x : ℝ, x = -d := ⟨_, rfl⟩
  obtain ⟨k49, hk49⟩ : ∃ x : ℝ, x = -d := ⟨_, rfl⟩
  obtain ⟨k50, hk50⟩ : ∃ x : ℝ, x = (d - 1) * (2 * b + d - 1) * (2 * b * d + 6 * b - d ^ 2 - 2 * d
    - 5) / (32 * (b - 1) ^ 2) := ⟨_, rfl⟩
  obtain ⟨k51, hk51⟩ : ∃ x : ℝ, x = -((d + 1) * (2 * b - d - 1) * (2 * b * d - 6 * b + d ^ 2 - 2
    * d + 5) / (32 * (b - 1) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨k52, hk52⟩ : ∃ x : ℝ, x = -(d / 2) := ⟨_, rfl⟩
  obtain ⟨k53, hk53⟩ : ∃ x : ℝ, x = (d - 1) * (2 * b + d - 1) * (2 * b * d + 6 * b - d ^ 2 - 2 * d
    - 5) / (32 * (b - 1) ^ 2) := ⟨_, rfl⟩
  obtain ⟨k54, hk54⟩ : ∃ x : ℝ, x = -((d + 1) * (2 * b - d - 1) * (2 * b * d - 6 * b + d ^ 2 - 2
    * d + 5) / (32 * (b - 1) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨k55, hk55⟩ : ∃ x : ℝ, x = -(d / 2) := ⟨_, rfl⟩
  obtain ⟨k56, hk56⟩ : ∃ x : ℝ, x = -(d * (6 * b - d ^ 2 - 5) / (8 * b - 8)) := ⟨_, rfl⟩
  obtain ⟨k57, hk57⟩ : ∃ x : ℝ, x = (d - 1) * (2 * b + d - 1) * (4 * b ^ 2 * d ^ 2 + 16 * d
    * b ^ 2 + 28 * b ^ 2 - 2 * b * d ^ 3 - 18 * b * d ^ 2 - 30 * b * d - 46 * b + d ^ 4 + 2
    * d ^ 3 + 12 * d ^ 2 + 14 * d + 19) / (192 * (b - 1) ^ 3) := ⟨_, rfl⟩
  obtain ⟨k58, hk58⟩ : ∃ x : ℝ, x = (d + 1) * (2 * b - d - 1) * (4 * b ^ 2 * d ^ 2 - 16 * d
    * b ^ 2 + 28 * b ^ 2 + 2 * b * d ^ 3 - 18 * b * d ^ 2 + 30 * b * d - 46 * b + d ^ 4 - 2
    * d ^ 3 + 12 * d ^ 2 - 14 * d + 19) / (192 * (b - 1) ^ 3) := ⟨_, rfl⟩
  obtain ⟨k59, hk59⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 3) / 12) := ⟨_, rfl⟩
  obtain ⟨k60, hk60⟩ : ∃ x : ℝ, x = (d - 1) * (2 * b + d - 1) * (4 * b ^ 2 * d ^ 2 + 16 * d
    * b ^ 2 + 28 * b ^ 2 - 2 * b * d ^ 3 - 18 * b * d ^ 2 - 30 * b * d - 46 * b + d ^ 4 + 2
    * d ^ 3 + 12 * d ^ 2 + 14 * d + 19) / (192 * (b - 1) ^ 3) := ⟨_, rfl⟩
  obtain ⟨k61, hk61⟩ : ∃ x : ℝ, x = (d + 1) * (2 * b - d - 1) * (4 * b ^ 2 * d ^ 2 - 16 * d
    * b ^ 2 + 28 * b ^ 2 + 2 * b * d ^ 3 - 18 * b * d ^ 2 + 30 * b * d - 46 * b + d ^ 4 - 2
    * d ^ 3 + 12 * d ^ 2 - 14 * d + 19) / (192 * (b - 1) ^ 3) := ⟨_, rfl⟩
  obtain ⟨k62, hk62⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 3) / 12) := ⟨_, rfl⟩
  obtain ⟨k63, hk63⟩ : ∃ x : ℝ, x = -(d * (4 * b ^ 2 * d ^ 2 + 84 * b ^ 2 - 38 * b * d ^ 2 - 138
    * b + 3 * d ^ 4 + 28 * d ^ 2 + 57) / (144 * (b - 1) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨p64, hp64⟩ : ∃ x : ℝ, x = 16 * b := ⟨_, rfl⟩
  obtain ⟨p65, hp65⟩ : ∃ x : ℝ, x = -(16 * b) := ⟨_, rfl⟩
  obtain ⟨p66, hp66⟩ : ∃ x : ℝ, x = 16 * b := ⟨_, rfl⟩
  obtain ⟨p67, hp67⟩ : ∃ x : ℝ, x = -((16 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 8 * ksDT 1 d
    - 48) / (ksDT 1 d ^ 2 * (b - 1) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨p68, hp68⟩ : ∃ x : ℝ, x = -((16 * b + 8)) := ⟨_, rfl⟩
  obtain ⟨p69, hp69⟩ : ∃ x : ℝ, x = 16 * b := ⟨_, rfl⟩
  obtain ⟨p70, hp70⟩ : ∃ x : ℝ, x = -((16 * b + 8)) := ⟨_, rfl⟩
  obtain ⟨p71, hp71⟩ : ∃ x : ℝ, x = (4 * ksDT 1 d * b - 4 * ksDT 1 d + 40) / (ksDT 1 d * (b
    - 1)) := ⟨_, rfl⟩
  obtain ⟨p72, hp72⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨p73, hp73⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨p74, hp74⟩ : ∃ x : ℝ, x = -4 := ⟨_, rfl⟩
  have hL : ksWW3L b d = [(c1, 0, 1), (c2, 1, 1), (c3, 2, 1), (c4, 1, ((1 - d) / 2)), (c5, 2, ((1
    - d) / 2)), (c4, 1, ((1 + d) / 2)), (c5, 2, ((1 + d)
    / 2)), (c6, 0, b), (c7, 1, b), (c8, 2, b), (c6, 0, (1 - 1 / ((1 - b) * ksDT 1 d))), (c7, 1, (1
    - 1 / ((1 - b) * ksDT 1 d))), (c8, 2, (1 - 1 / ((1 - b) * ksDT 1 d)))] := by
    rw [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]
    rfl
  have hP : ksWW3P b d = [(c9, 0), (c10, 1), (c11, 2)] := by
    rw [hc9, hc10, hc11]
    rfl
  have hcc : ksWW3c b d = c12 := by rw [hc12]; rfl
  have hce : ksWW3e b d = c13 := by rw [hc13]; rfl
  have hH1 : ksWPH 0 1 ((1 + d) / 2) - ksWPH 0 1 ((1 - d) / 2) = log (1 - d) * k14 + log (1 + d)
    * k15 + log 2 * k16 + k17 := by
    rw [hk14, hk15, hk16, hk17]
    exact ksWY1_H1 hd hb
  have hH2 : ksWPH 1 1 ((1 + d) / 2) - ksWPH 1 1 ((1 - d) / 2) = log (1 - d) * k18 + log (1 + d)
    * k19 + log 2 * k20 + k21 := by
    rw [hk18, hk19, hk20, hk21]
    exact ksWY1_H2 hd hb
  have hH3 : ksWPH 2 1 ((1 + d) / 2) - ksWPH 2 1 ((1 - d) / 2) = log (1 - d) * k22 + log (1 + d)
    * k23 + log 2 * k24 + k25 := by
    rw [hk22, hk23, hk24, hk25]
    exact ksWY1_H3 hd hb
  have hH4 : ksWPH 1 ((1 - d) / 2) ((1 + d) / 2) - ksWPH 1 ((1 - d) / 2) ((1 - d) / 2) = log d
    * k26 + k27 := by
    rw [hk26, hk27]
    exact ksWY1_H4 hd hb
  have hH5 : ksWPH 2 ((1 - d) / 2) ((1 + d) / 2) - ksWPH 2 ((1 - d) / 2) ((1 - d) / 2) = log d
    * k28 + k29 := by
    rw [hk28, hk29]
    exact ksWY1_H5 hd hb
  have hH6 : ksWPH 1 ((1 + d) / 2) ((1 + d) / 2) - ksWPH 1 ((1 + d) / 2) ((1 - d) / 2) = log d
    * k30 + k31 := by
    rw [hk30, hk31]
    exact ksWY1_H6 hd hb
  have hH7 : ksWPH 2 ((1 + d) / 2) ((1 + d) / 2) - ksWPH 2 ((1 + d) / 2) ((1 - d) / 2) = log d
    * k32 + k33 := by
    rw [hk32, hk33]
    exact ksWY1_H7 hd hb
  have hH8 : ksWPH 0 b ((1 + d) / 2) - ksWPH 0 b ((1 - d) / 2) = log (b - (1 - d) / 2) * k34
    + log (b - (1 + d) / 2) * k35 + k36 := by
    rw [hk34, hk35, hk36]
    exact ksWY1_H8 hd hb
  have hH9 : ksWPH 1 b ((1 + d) / 2) - ksWPH 1 b ((1 - d) / 2) = log (b - (1 - d) / 2) * k37
    + log (b - (1 + d) / 2) * k38 + k39 := by
    rw [hk37, hk38, hk39]
    exact ksWY1_H9 hd hb
  have hH10 : ksWPH 2 b ((1 + d) / 2) - ksWPH 2 b ((1 - d) / 2) = log (b - (1 - d) / 2) * k40
    + log (b - (1 + d) / 2) * k41 + k42 := by
    rw [hk40, hk41, hk42]
    exact ksWY1_H10 hd hb
  have hH11 : ksWPH 0 (1 - 1 / ((1 - b) * ksDT 1 d)) ((1 + d) / 2) - ksWPH 0 (1 - 1 / ((1 - b)
    * ksDT 1 d)) ((1 - d) / 2) = log (b - (1 - d) / 2) * k43 + log (b - (1 + d) / 2) * k44
    + log (1 - b) * k45 + log (1 - d) * k46 + log (1 + d) * k47 + log 2 * k48 + k49 := by
    rw [hk43, hk44, hk45, hk46, hk47, hk48, hk49]
    exact ksWY1_H11 hd hb
  have hH12 : ksWPH 1 (1 - 1 / ((1 - b) * ksDT 1 d)) ((1 + d) / 2) - ksWPH 1 (1 - 1 / ((1 - b)
    * ksDT 1 d)) ((1 - d) / 2) = log (b - (1 - d) / 2) * k50 + log (b - (1 + d) / 2) * k51
    + log (1 - b) * k52 + log (1 - d) * k53 + log (1 + d) * k54 + log 2 * k55 + k56 := by
    rw [hk50, hk51, hk52, hk53, hk54, hk55, hk56]
    exact ksWY1_H12 hd hb
  have hH13 : ksWPH 2 (1 - 1 / ((1 - b) * ksDT 1 d)) ((1 + d) / 2) - ksWPH 2 (1 - 1 / ((1 - b)
    * ksDT 1 d)) ((1 - d) / 2) = log (b - (1 - d) / 2) * k57 + log (b - (1 + d) / 2) * k58
    + log (1 - b) * k59 + log (1 - d) * k60 + log (1 + d) * k61 + log 2 * k62 + k63 := by
    rw [hk57, hk58, hk59, hk60, hk61, hk62, hk63]
    exact ksWY1_H13 hd hb
  have hp0 : c9 = log (1 - b) * p64 + log (ksDA 1 (-ksDT 1 d) b) * p65 + log (ksDT 1 d) * p66
    + p67 := by
    rw [hc9, hp64, hp65, hp66, hp67]
    exact ksWY1_p0 hd hb
  have hp1 : c10 = log (1 - b) * p68 + log (ksDA 1 (-ksDT 1 d) b) * p69 + log (ksDT 1 d) * p70
    + p71 := by
    rw [hc10, hp68, hp69, hp70, hp71]
    exact ksWY1_p1 hd hb
  have hp2 : c11 = log (1 - b) * p72 + log (ksDT 1 d) * p73 + p74 := by
    rw [hc11, hp72, hp73, hp74]
    exact ksWY1_p2 hd hb
  have k0 : c1 * k17 + c2 * k21 + c3 * k25 + c4 * k27 + c5 * k29 + c4 * k31 + c5 * k33 + c6 * k36
    + c7 * k39 + c8 * k42 + c6 * k49 + c7 * k56 + c8 * k63 + (1 * p67) * ((((1 + d) / 2) ^ 1 - ((1
    - d) / 2) ^ 1) / 1) + (1 * p71) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (1 * p74)
    * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) + -(c13 / ((1 - d) / 2 * (b - (1 - d) / 2)
    / (1 - b)) - c13 / ((1 + d) / 2 * (b - (1 + d) / 2) / (1 - b))) = (d * (37 * d ^ 2 + 27) / 9)
    * b ^ 0 + (-(28 * d / 3)) * b ^ 1 + (16 * d / 3) * b ^ 2 + (-(d * (d + 1) * (d - 1) / 3)) * (b
    - 1)⁻¹ + (4 * d * (d + 1) * (d - 1) * (2 * d ^ 2 - 3) / 3) * ((b - 1) ^ 2)⁻¹ := by
    rw [hc1, hk17, hc2, hk21, hc3, hk25, hc4, hk27, hc5, hk29, hk31, hk33, hc6, hk36, hc7, hk39,
      hc8, hk42, hk49, hk56, hk63, hp67, hp71, hp74, hc13]
    exact ksWY1_k0 hd hb
  have kA : c6 * k34 + c7 * k37 + c8 * k40 + c6 * k43 + c7 * k50 + c8 * k57 + (1 * p65) * ((((1
    + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (1 * p69) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2)
    / 2) + 1 * c12 = ((2 * d ^ 3 + 4 * d ^ 2 - 6 * d + 8) / 3) * b ^ 0 + (-((8 * d ^ 2 + 32) / 3))
    * b ^ 1 + 12 * b ^ 2 + (-16 / 3) * b ^ 3 + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - 1)⁻¹
    + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 + d) / 2))⁻¹ + ((d + 1) * (d - 1) * (17
    * d ^ 2 - 25) / 12) * ((b - 1) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3))
    * ((b - 1) ^ 3)⁻¹ := by
    rw [hc6, hk34, hc7, hk37, hc8, hk40, hk43, hk50, hk57, hp65, hp69, hc12]
    exact ksWY1_kA hd hb
  have kB : c6 * k35 + c7 * k38 + c8 * k41 + c6 * k44 + c7 * k51 + c8 * k58 + (1 * p65) * ((((1
    + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (1 * p69) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2)
    / 2) + -1 * c12 = ((2 * d ^ 3 - 4 * d ^ 2 - 6 * d - 8) / 3) * b ^ 0 + ((8 * d ^ 2 + 32) / 3)
    * b ^ 1 + (-12) * b ^ 2 + (16 / 3) * b ^ 3 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b
    - 1)⁻¹ + (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 - d) / 2))⁻¹ + (-((d + 1) * (d - 1)
    * (17 * d ^ 2 - 25) / 12)) * ((b - 1) ^ 2)⁻¹ + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3)
    / 3) * ((b - 1) ^ 3)⁻¹ := by
    rw [hc6, hk35, hc7, hk38, hc8, hk41, hk44, hk51, hk58, hp65, hp69, hc12]
    exact ksWY1_kB hd hb
  have kC : c6 * k45 + c7 * k52 + c8 * k59 + (1 * p64) * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1)
    / 1) + (1 * p68) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (1 * p72) * ((((1 + d)
    / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) = (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d)
    / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d) / 2))⁻¹ := by
    rw [hc6, hk45, hc7, hk52, hc8, hk59, hp64, hp68, hp72]
    exact ksWY1_kC hd hb
  have kM : c1 * k14 + c2 * k18 + c3 * k22 + c6 * k46 + c7 * k53 + c8 * k60 + (-1 * p65 + -1
    * p66) * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (-1 * p69 + -1 * p70) * ((((1 + d)
    / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (-1 * p73) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3)
    / 3) + 1 * c12 = (-(2 * d * (d ^ 2 - 3) / 3)) * b ^ 0 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3))
    * (b - ((1 + d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - 1)⁻¹ + ((d + 1) * (d - 1)
    * (17 * d ^ 2 - 25) / 12) * ((b - 1) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3)
    / 3)) * ((b - 1) ^ 3)⁻¹ := by
    rw [hc1, hk14, hc2, hk18, hc3, hk22, hc6, hk46, hc7, hk53, hc8, hk60, hp65, hp66, hp69, hp70,
      hp73, hc12]
    exact ksWY1_kM hd hb
  have kN : c1 * k15 + c2 * k19 + c3 * k23 + c6 * k47 + c7 * k54 + c8 * k61 + (-1 * p65 + -1
    * p66) * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (-1 * p69 + -1 * p70) * ((((1 + d)
    / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (-1 * p73) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3)
    / 3) + -1 * c12 = (-(2 * d * (d ^ 2 - 3) / 3)) * b ^ 0 + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)
    * (b - ((1 - d) / 2))⁻¹ + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - 1)⁻¹ + (-((d + 1) * (d
    - 1) * (17 * d ^ 2 - 25) / 12)) * ((b - 1) ^ 2)⁻¹ + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2
    - 3) / 3) * ((b - 1) ^ 3)⁻¹ := by
    rw [hc1, hk15, hc2, hk19, hc3, hk23, hc6, hk47, hc7, hk54, hc8, hk61, hp65, hp66, hp69, hp70,
      hp73, hc12]
    exact ksWY1_kN hd hb
  have kK : c1 * k16 + c2 * k20 + c3 * k24 + c6 * k48 + c7 * k55 + c8 * k62 + (2 * p65 + 2 * p66)
    * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (2 * p69 + 2 * p70) * ((((1 + d) / 2) ^ 2
    - ((1 - d) / 2) ^ 2) / 2) + (2 * p73) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) = (4 * d
    * (d ^ 2 - 3) / 3) * b ^ 0 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹
    + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3)
    / 3) * (b - 1)⁻¹ + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - 1)⁻¹ := by
    rw [hc1, hk16, hc2, hk20, hc3, hk24, hc6, hk48, hc7, hk55, hc8, hk62, hp65, hp66, hp69, hp70,
      hp73]
    exact ksWY1_kK hd hb
  have kD : c4 * k26 + c5 * k28 + c4 * k30 + c5 * k32 = (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b
    - ((1 + d) / 2))⁻¹ + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ := by
    rw [hc4, hk26, hc5, hk28, hk30, hk32]
    exact ksWY1_kD hd hb
  simp only [ksWWEI, hL, hP, hcc, hce, ksWPv, ksWPQ, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  rw [hH1, hH2, hH3, hH4, hH5, hH6, hH7, hH8, hH9, hH10, hH11, hH12, hH13]
  rw [hp0, hp1, hp2]
  simp only [ksWY_sp_sub_w0 hd hb1, ksWY_sm_sub_w0 hd hb1]
  simp only [ksWY_log_w0p hd hm hb1, ksWY_log_w0m hd hp hb1, ksWY_log_ksDA hd hm hp,
    ksWY_log_ksDT hd]
  simp only [ksWYe, ksWPe, ksWYq, ksWPq, ksWY1L, ksWY1P, ksWY1D, ksWY1Q, ksWY1C, ksWY1R, ksWY1S,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWY_log_l1 hd.2, ksWY_log_l2 (by linarith [hd.1] : -1 < d), ksWY_log_l3, ksWY_log_l4,
    ksWY_log_l5 (by linarith [hd.1] : -1 < d), ksWY_log_l6 hd.2, ksWY_log_swap b 1]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  linear_combination (-1 : ℝ) * (k0 + A * kA + B * kB + C * kC + M * kM + N * kN + K * kK + D * kD)

end QED.ChainProof.SetAKS

end
