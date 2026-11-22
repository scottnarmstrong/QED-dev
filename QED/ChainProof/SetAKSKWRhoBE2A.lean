/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBS

/-!
# Set (a), stage D: the `β`-integrand on `(σ₋, σ₊)`, logarithmic parts

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route, range
`β ∈ (σ₋, σ₊)` (`σ± = (1 ± δ)/2`), part 1 of 4. The `w`-integrated `VB` density `ksWWEII β δ` has
four pieces (`w ∈ (0, σ₋)`, `(σ₋, β)`, `(β, σ₊)`, `(σ₊, 1)`). This file holds the generated
lists `ksWY2L`, ..., `ksWY2S` of the target `ksWYe` combination, the logarithms of the poles at
the endpoints `0` and `1` (`ksWY_log_w1z`, `ksWY_log_w0o`), the splitting of a `ksWPv` list
(`ksWY_ksWPv_split`), the differences `ksWPH j a u - ksWPH j a l` in closed form (`ksWY2_H*`) and
the logarithmic coefficients of the polynomial parts (`ksWY2_p*`).
Machine-generated; every coefficient is checked by the proofs.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetAKS

variable {b d : ℝ}

/-- Region `2`: the terms `c β^j log (β - a)`. -/
noncomputable def ksWY2L (d : ℝ) : List (ℝ × ℕ × ℝ) := [
  (-((4 * d ^ 2 + 4) / 3), 0, 0),
  ((8 * d ^ 2 + 8) / 3, 1, 0),
  (-4, 2, 0),
  (16 / 3, 3, 0),
  ((4 * d ^ 2 + 8) / 3, 0, 1),
  (-((8 * d ^ 2 + 32) / 3), 1, 1),
  (12, 2, 1),
  (-16 / 3, 3, 1),
  ((2 * d ^ 3 + 4 * d ^ 2 - 6 * d + 8) / 3, 0, ((1 - d) / 2)),
  (-((8 * d ^ 2 + 32) / 3), 1, ((1 - d) / 2)),
  (12, 2, ((1 - d) / 2)),
  (-16 / 3, 3, ((1 - d) / 2)),
  ((2 * d ^ 3 - 4 * d ^ 2 - 6 * d - 4) / 3, 0, ((1 + d) / 2)),
  ((8 * d ^ 2 + 8) / 3, 1, ((1 + d) / 2)),
  (-4, 2, ((1 + d) / 2)),
  (16 / 3, 3, ((1 + d) / 2))]

/-- Region `2`: the monomials. -/
noncomputable def ksWY2P (d : ℝ) : List (ℝ × ℕ) := [
  (4 * log 2 * (d - 1) ^ 2 * (d + 2) / 3 - 4 * log (1 - d) * (d ^ 3 - 3 * d + 1) / 3 - 4 * log (1
    + d) / 3 + (37 * d ^ 3 - 45 * d ^ 2 + 9 * d + 87) / 9, 0),
  (-(16 * log 2) + 8 * log (1 - d) + 8 * log (1 + d) - (16 * d + 16) / 3, 1),
  (16 * log 2 - 8 * log (1 - d) - 8 * log (1 + d) + (16 * d + 16) / 3, 2)]

/-- Region `2`: the difference quotients. -/
noncomputable def ksWY2D (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3, 0, ((1 + d) / 2)),
  (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3), 1, ((1 - d) / 2)),
  (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3, ((1 - d) / 2), 1),
  (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3), ((1 - d) / 2), ((1 + d) / 2)),
  (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3), ((1 + d) / 2), 0),
  (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3, ((1 + d) / 2), ((1 - d) / 2))]

/-- Region `2`: the double poles. -/
noncomputable def ksWY2Q (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  ((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12, ((1 - d) / 2), 1),
  ((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12, ((1 + d) / 2), 0)]

/-- Region `2`: the triple poles. -/
noncomputable def ksWY2C (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3), ((1 - d) / 2), 1),
  ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3, ((1 + d) / 2), 0)]

/-- Region `2`: the rational simple and double poles. -/
noncomputable def ksWY2R (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (1, -((d + 1) * (d - 1) * (8 * d ^ 2 + d - 13) / 6), log 2 * (d + 1) * (d - 1) * (17 * d ^ 2
    - 25) / 12 - log (1 + d) * (d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12 + 2 * (d - 1) ^ 2 * (d
    + 1) * (2 * d ^ 2 - 3) / 3),
  (0, (d + 1) * (d - 1) * (8 * d ^ 2 + d - 13) / 6, log 2 * (d + 1) * (d - 1) * (17 * d ^ 2 - 25)
    / 12 - log (1 + d) * (d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12 + 2 * (d - 1) ^ 2 * (d + 1)
    * (2 * d ^ 2 - 3) / 3)]

/-- Region `2`: the rational triple poles. -/
noncomputable def ksWY2S (d : ℝ) : List (ℝ × ℝ) := [
  (1, -(log 2 * (d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) + log (1 + d) * (d + 1) ^ 2 * (d
    - 1) ^ 2 * (2 * d ^ 2 - 3) / 3),
  (0, log 2 * (d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3 - log (1 + d) * (d + 1) ^ 2 * (d
    - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)]


theorem ksWY_log_w1z (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ≠ 0) :
    log (1 / (b * ksDT 1 d)) = log (1 - d) + log (1 + d) - 2 * log 2 - log b := by
  rw [one_div, log_inv, log_mul hb (ksWW_T_pos hd).ne', ksWY_log_ksDT hd]
  ring

theorem ksWY_log_w0o (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ≠ 1) :
    log (1 / ((1 - b) * ksDT 1 d)) = log (1 - d) + log (1 + d) - 2 * log 2 - log (1 - b) := by
  rw [one_div, log_inv, log_mul (sub_ne_zero.2 (Ne.symm hb)) (ksWW_T_pos hd).ne',
    ksWY_log_ksDT hd]
  ring

theorem ksWY_ksWPv_split (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ)) (l u : ℝ) (n : ℕ) :
    ksWPv L P l u = ksWPv (L.take n) [] l u + ksWPv (L.drop n) P l u := by
  conv_lhs => rw [← List.take_append_drop n L]
  simp only [ksWPv, List.map_append, List.sum_append, List.map_nil, List.sum_nil]
  ring

theorem ksWY2_H1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k9 k10 k11 : ℝ} (hk9 : k9 = (d - 1) ^ 2 / 8) (hk10 : k10 = -((d - 1) ^ 2
  / 8)) (hk11 : k11 = -((d - 1) ^ 2 / 16)) :
    ksWPH 1 0 ((1 - d) / 2) - ksWPH 1 0 0 = log (1
  - d) * k9 + log 2 * k10 + k11 := by
  subst hk9 hk10 hk11
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul,
    add_zero]
  simp only [ksWY_log_sm hd.2, sub_zero, zero_sub, sub_self, log_zero, mul_zero, zero_add]
  field_simp
  ring

theorem ksWY2_H2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k12 k13 k14 : ℝ} (hk12 : k12 = (d - 1) ^ 2 / 8) (hk13 : k13 = -((d - 1) ^ 2
  / 8)) (hk14 : k14 = -(3 * (d - 1) ^ 2 / 16)) :
    ksWPH 1 ((1 - d) / 2) ((1 - d) / 2)
  - ksWPH 1 ((1 - d) / 2) 0 = log (1 - d) * k12 + log 2 * k13 + k14 := by
  subst hk12 hk13 hk14
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul,
    add_zero]
  simp only [ksWY_log_sm hd.2, zero_sub, log_neg_eq_log, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY2_H3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k15 k16 k17 : ℝ} (hk15 : k15 = -((d - 1) ^ 3 / 24)) (hk16 : k16 = (d - 1) ^ 3
  / 24) (hk17 : k17 = 11 * (d - 1) ^ 3 / 144) :
    ksWPH 2 ((1 - d) / 2) ((1 - d) / 2)
  - ksWPH 2 ((1 - d) / 2) 0 = log (1 - d) * k15 + log 2 * k16 + k17 := by
  subst hk15 hk16 hk17
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_sm hd.2, zero_sub, log_neg_eq_log, sub_self, log_zero, mul_zero, zero_mul,
    add_zero]
  field_simp
  ring

theorem ksWY2_H4 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k18 k19 k20 k21 : ℝ} (hk18 : k18 = (d + 1) ^ 2 / 8) (hk19 : k19 = -((d + 1) ^ 2
  / 8)) (hk20 : k20 = -(d / 2)) (hk21 : k21 = (d - 1) * (d + 3) / 16) :
    ksWPH 1 ((1 + d)
  / 2) ((1 - d) / 2) - ksWPH 1 ((1 + d) / 2) 0 = log (1 + d) * k18 + log 2 * k19 + log d * k20
  + k21 := by
  subst hk18 hk19 hk20 hk21
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul,
    add_zero]
  simp only [ksWY_log_l4, ksWY_log_sp (by linarith [hd.1] : -1 < d), zero_sub, log_neg_eq_log]
  field_simp
  ring

theorem ksWY2_H5 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k22 k23 k24 k25 : ℝ} (hk22 : k22 = (d + 1) ^ 3 / 24) (hk23 : k23 = -((d + 1) ^ 3
  / 24)) (hk24 : k24 = -(d * (d ^ 2 + 3) / 12)) (hk25 : k25 = (d - 1) * (5 * d ^ 2 + 8 * d + 11)
  / 144) :
    ksWPH 2 ((1 + d) / 2) ((1 - d) / 2) - ksWPH 2 ((1 + d) / 2) 0 = log (1 + d) * k22
  + log 2 * k23 + log d * k24 + k25 := by
  subst hk22 hk23 hk24 hk25
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_l4, ksWY_log_sp (by linarith [hd.1] : -1 < d), zero_sub, log_neg_eq_log,
    zero_mul, add_zero]
  field_simp
  ring

theorem ksWY2_H6 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k26 k27 k28 : ℝ} (hk26 : k26 = -((2 * b - d + 1) * (2 * b + d - 1)
  / 8)) (hk27 : k27 = b ^ 2 / 2) (hk28 : k28 = (d - 1) * (4 * b - d + 1) / 16) :
    ksWPH 1 b ((1
  - d) / 2) - ksWPH 1 b 0 = log (b - (1 - d) / 2) * k26 + log b * k27 + k28 := by
  subst hk26 hk27 hk28
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul,
    add_zero]
  simp only [zero_sub, log_neg_eq_log, ksWY_log_swap ((1 - d) / 2) b]
  field_simp
  ring

theorem ksWY2_H7 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k29 k30 k31 : ℝ} (hk29 : k29 = -((2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2
  - 2 * d + 1) / 24)) (hk30 : k30 = b ^ 3 / 3) (hk31 : k31 = (d - 1) * (12 * b ^ 2 - 3 * b * d + 3
  * b + d ^ 2 - 2 * d + 1) / 72) :
    ksWPH 2 b ((1 - d) / 2) - ksWPH 2 b 0 = log (b - (1 - d)
  / 2) * k29 + log b * k30 + k31 := by
  subst hk29 hk30 hk31
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [zero_sub, log_neg_eq_log, ksWY_log_swap ((1 - d) / 2) b, zero_mul, add_zero]
  field_simp
  ring

theorem ksWY2_H8 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k32 k33 k34 k35 k36 k37 : ℝ} (hk32 : k32 = (d - 1) ^ 2 * (2 * b + d + 1) * (2 * b - d
  - 1) / (32 * b ^ 2)) (hk33 : k33 = (d - 1) ^ 2 / 8) (hk34 : k34 = (d + 1) ^ 2 * (d - 1) ^ 2
  / (32 * b ^ 2)) (hk35 : k35 = -((d - 1) ^ 2 * (4 * b ^ 2 + d ^ 2 + 2 * d + 1) / (32
  * b ^ 2))) (hk36 : k36 = -((d - 1) ^ 2 / 8)) (hk37 : k37 = -((d - 1) ^ 2 * (b + d + 1) / (16
  * b))) :
    ksWPH 1 (1 / (b * ksDT 1 d)) ((1 - d) / 2) - ksWPH 1 (1 / (b
  * ksDT 1 d)) 0 = log (b - (1 + d) / 2) * k32 + log (1 - d) * k33 + log (1 + d) * k34 + log 2
  * k35 + log b * k36 + k37 := by
  subst hk32 hk33 hk34 hk35 hk36 hk37
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul,
    add_zero]
  simp only [ksWY_sm_sub_w1 hd hb0, ksWY_log_w1m hd hp hb0, zero_sub, log_neg_eq_log,
    ksWY_log_w1z hd hb0]
  try rw [ksWW_inv_K hd hb0]
  field_simp
  ring

theorem ksWY2_H9 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k38 k39 k40 k41 k42 k43 : ℝ} (hk38 : k38 = -((d - 1) ^ 3 * (2 * b - d - 1) * (4 * b ^ 2
  + 2 * b * d + 2 * b + d ^ 2 + 2 * d + 1) / (192 * b ^ 3))) (hk39 : k39 = -((d - 1) ^ 3
  / 24)) (hk40 : k40 = -((d + 1) ^ 3 * (d - 1) ^ 3 / (192 * b ^ 3))) (hk41 : k41 = (d - 1) ^ 3
  * (2 * b + d + 1) * (4 * b ^ 2 - 2 * b * d - 2 * b + d ^ 2 + 2 * d + 1) / (192
  * b ^ 3)) (hk42 : k42 = (d - 1) ^ 3 / 24) (hk43 : k43 = (d - 1) ^ 3 * (4 * b ^ 2 + 3 * b * d + 3
  * b + 3 * d ^ 2 + 6 * d + 3) / (288 * b ^ 2)) :
    ksWPH 2 (1 / (b * ksDT 1 d)) ((1 - d) / 2)
  - ksWPH 2 (1 / (b * ksDT 1 d)) 0 = log (b - (1 + d) / 2) * k38 + log (1 - d) * k39 + log (1 + d)
  * k40 + log 2 * k41 + log b * k42 + k43 := by
  subst hk38 hk39 hk40 hk41 hk42 hk43
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_sm_sub_w1 hd hb0, ksWY_log_w1m hd hp hb0, zero_sub, log_neg_eq_log,
    ksWY_log_w1z hd hb0, zero_mul, add_zero]
  try rw [ksWW_inv_K hd hb0]
  field_simp
  ring

theorem ksWY2_H10 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k52 k53 k54 k55 : ℝ} (hk52 : k52 = -((d - 1) ^ 2 / 8)) (hk53 : k53 = (d - 1) ^ 2
  / 8) (hk54 : k54 = b ^ 2 / 2) (hk55 : k55 = -((2 * b - d + 1) * (2 * b + d - 1)
  / 16)) :
    ksWPH 1 0 b - ksWPH 1 0 ((1 - d) / 2) = log (1 - d) * k52 + log 2 * k53 + log b
  * k54 + k55 := by
  subst hk52 hk53 hk54 hk55
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul,
    add_zero]
  simp only [ksWY_log_sm hd.2, sub_zero, mul_zero, zero_add]
  field_simp
  ring

theorem ksWY2_H11 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k56 k57 k58 k59 : ℝ} (hk56 : k56 = (d - 1) ^ 3 / 24) (hk57 : k57 = -((d - 1) ^ 3
  / 24)) (hk58 : k58 = b ^ 3 / 3) (hk59 : k59 = -((2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b
  + d ^ 2 - 2 * d + 1) / 72)) :
    ksWPH 2 0 b - ksWPH 2 0 ((1 - d) / 2) = log (1 - d) * k56
  + log 2 * k57 + log b * k58 + k59 := by
  subst hk56 hk57 hk58 hk59
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_sm hd.2, sub_zero, mul_zero, add_zero]
  field_simp
  ring

theorem ksWY2_H12 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k60 k61 : ℝ} (hk60 : k60 = (2 * b - d + 1) * (2 * b + d - 1) / 8) (hk61 : k61 = -((2 * b
  + d - 1) * (2 * b - 3 * d + 3) / 16)) :
    ksWPH 1 ((1 - d) / 2) b - ksWPH 1 ((1 - d) / 2) ((1
  - d) / 2) = log (b - (1 - d) / 2) * k60 + k61 := by
  subst hk60 hk61
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY2_H13 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k62 k63 : ℝ} (hk62 : k62 = (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2
  * d + 1) / 24) (hk63 : k63 = -((2 * b + d - 1) * (8 * b ^ 2 - 10 * b * d + 10 * b + 11 * d ^ 2
  - 22 * d + 11) / 144)) :
    ksWPH 2 ((1 - d) / 2) b - ksWPH 2 ((1 - d) / 2) ((1 - d)
  / 2) = log (b - (1 - d) / 2) * k62 + k63 := by
  subst hk62 hk63
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY2_H14 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k64 k65 k66 : ℝ} (hk64 : k64 = (2 * b + d + 1) * (2 * b - d - 1) / 8) (hk65 : k65 = d
  / 2) (hk66 : k66 = -((2 * b + d - 1) * (2 * b + d + 3) / 16)) :
    ksWPH 1 ((1 + d) / 2) b
  - ksWPH 1 ((1 + d) / 2) ((1 - d) / 2) = log (b - (1 + d) / 2) * k64 + log d * k65 + k66 := by
  subst hk64 hk65 hk66
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_log_l4]
  field_simp
  ring

theorem ksWY2_H15 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k67 k68 k69 : ℝ} (hk67 : k67 = (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2
  + 2 * d + 1) / 24) (hk68 : k68 = d * (d ^ 2 + 3) / 12) (hk69 : k69 = -((2 * b + d - 1) * (8
  * b ^ 2 + 2 * b * d + 10 * b + 5 * d ^ 2 + 8 * d + 11) / 144)) :
    ksWPH 2 ((1 + d) / 2) b
  - ksWPH 2 ((1 + d) / 2) ((1 - d) / 2) = log (b - (1 + d) / 2) * k67 + log d * k68 + k69 := by
  subst hk67 hk68 hk69
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_l4]
  field_simp
  ring

theorem ksWY2_H16 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k80 k81 k82 k83 : ℝ} (hk80 : k80 = -((b + 1) * (b - 1) / 2)) (hk81 : k81 = (d - 1) * (d
  + 3) / 8) (hk82 : k82 = -((d - 1) * (d + 3) / 8)) (hk83 : k83 = (2 * b - d - 1) * (2 * b + d
  + 5) / 16) :
    ksWPH 1 1 ((1 + d) / 2) - ksWPH 1 1 b = log (1 - b) * k80 + log (1 - d) * k81
  + log 2 * k82 + k83 := by
  subst hk80 hk81 hk82 hk83
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add, mul_one]
  simp only [ksWY_log_l1 hd.2, ksWY_log_swap b 1]
  field_simp
  ring

theorem ksWY2_H17 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k84 k85 k86 k87 : ℝ} (hk84 : k84 = -((b - 1) * (b ^ 2 + b + 1) / 3)) (hk85 : k85 = (d
  - 1) * (d ^ 2 + 4 * d + 7) / 24) (hk86 : k86 = -((d - 1) * (d ^ 2 + 4 * d + 7)
  / 24)) (hk87 : k87 = (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 8 * b + d ^ 2 + 5 * d + 16)
  / 72) :
    ksWPH 2 1 ((1 + d) / 2) - ksWPH 2 1 b = log (1 - b) * k84 + log (1 - d) * k85
  + log 2 * k86 + k87 := by
  subst hk84 hk85 hk86 hk87
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add, mul_one]
  simp only [ksWY_log_l1 hd.2, ksWY_log_swap b 1]
  field_simp
  ring

theorem ksWY2_H18 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k88 k89 k90 : ℝ} (hk88 : k88 = -((2 * b - d + 1) * (2 * b + d - 1) / 8)) (hk89 : k89 = d
  / 2) (hk90 : k90 = (2 * b - d - 1) * (2 * b - d + 3) / 16) :
    ksWPH 1 ((1 - d) / 2) ((1 + d)
  / 2) - ksWPH 1 ((1 - d) / 2) b = log (b - (1 - d) / 2) * k88 + log d * k89 + k90 := by
  subst hk88 hk89 hk90
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_log_l3]
  field_simp
  ring

theorem ksWY2_H19 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k91 k92 k93 : ℝ} (hk91 : k91 = -((2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2
  - 2 * d + 1) / 24)) (hk92 : k92 = d * (d ^ 2 + 3) / 12) (hk93 : k93 = (2 * b - d - 1) * (8
  * b ^ 2 - 2 * b * d + 10 * b + 5 * d ^ 2 - 8 * d + 11) / 144) :
    ksWPH 2 ((1 - d) / 2) ((1
  + d) / 2) - ksWPH 2 ((1 - d) / 2) b = log (b - (1 - d) / 2) * k91 + log d * k92 + k93 := by
  subst hk91 hk92 hk93
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_l3]
  field_simp
  ring

theorem ksWY2_H20 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k94 k95 : ℝ} (hk94 : k94 = -((2 * b + d + 1) * (2 * b - d - 1) / 8)) (hk95 : k95 = (2 * b
  - d - 1) * (2 * b + 3 * d + 3) / 16) :
    ksWPH 1 ((1 + d) / 2) ((1 + d) / 2) - ksWPH 1 ((1
  + d) / 2) b = log (b - (1 + d) / 2) * k94 + k95 := by
  subst hk94 hk95
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY2_H21 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k96 k97 : ℝ} (hk96 : k96 = -((2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2
  * d + 1) / 24)) (hk97 : k97 = (2 * b - d - 1) * (8 * b ^ 2 + 10 * b * d + 10 * b + 11 * d ^ 2
  + 22 * d + 11) / 144) :
    ksWPH 2 ((1 + d) / 2) ((1 + d) / 2) - ksWPH 2 ((1 + d)
  / 2) b = log (b - (1 + d) / 2) * k96 + k97 := by
  subst hk96 hk97
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one,
    one_mul]
  simp only [zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY2_H22 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k114 k115 k116 : ℝ} (hk114 : k114 = -((d - 1) / 2)) (hk115 : k115 = (d - 1)
  / 2) (hk116 : k116 = (d - 1) / 2) :
    ksWPH 0 1 1 - ksWPH 0 1 ((1 + d) / 2) = log (1 - d)
  * k114 + log 2 * k115 + k116 := by
  subst hk114 hk115 hk116
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    pow_zero, pow_one, one_pow, zero_add, mul_one, one_mul]
  simp only [ksWY_log_l1 hd.2, zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY2_H23 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k117 k118 k119 : ℝ} (hk117 : k117 = -((d - 1) * (d + 3) / 8)) (hk118 : k118 = (d - 1)
  * (d + 3) / 8) (hk119 : k119 = (d - 1) * (d + 7) / 16) :
    ksWPH 1 1 1 - ksWPH 1 1 ((1 + d)
  / 2) = log (1 - d) * k117 + log 2 * k118 + k119 := by
  subst hk117 hk118 hk119
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add, mul_one]
  simp only [ksWY_log_l1 hd.2, zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY2_H24 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k120 k121 k122 k123 : ℝ} (hk120 : k120 = -((d + 1) * (d - 3) / 8)) (hk121 : k121 = (d
  + 1) * (d - 3) / 8) (hk122 : k122 = -(d / 2)) (hk123 : k123 = -((d - 1) * (d - 5)
  / 16)) :
    ksWPH 1 ((1 - d) / 2) 1 - ksWPH 1 ((1 - d) / 2) ((1 + d) / 2) = log (1 + d) * k120
  + log 2 * k121 + log d * k122 + k123 := by
  subst hk120 hk121 hk122 hk123
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_l3, ksWY_log_l5 (by linarith [hd.1] : -1 < d)]
  field_simp
  ring

theorem ksWY2_H25 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k124 k125 k126 k127 : ℝ} (hk124 : k124 = (d + 1) * (d ^ 2 - 4 * d + 7)
  / 24) (hk125 : k125 = -((d + 1) * (d ^ 2 - 4 * d + 7) / 24)) (hk126 : k126 = -(d * (d ^ 2 + 3)
  / 12)) (hk127 : k127 = (d - 1) * (5 * d ^ 2 - 10 * d + 29) / 144) :
    ksWPH 2 ((1 - d) / 2) 1
  - ksWPH 2 ((1 - d) / 2) ((1 + d) / 2) = log (1 + d) * k124 + log 2 * k125 + log d * k126
  + k127 := by
  subst hk124 hk125 hk126 hk127
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add,
    mul_one, one_mul]
  simp only [ksWY_log_l3, ksWY_log_l5 (by linarith [hd.1] : -1 < d)]
  field_simp
  ring

theorem ksWY2_H26 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k128 k129 k130 : ℝ} (hk128 : k128 = -((d - 1) * (d + 3) / 8)) (hk129 : k129 = (d - 1)
  * (d + 3) / 8) (hk130 : k130 = (d - 1) * (3 * d + 5) / 16) :
    ksWPH 1 ((1 + d) / 2) 1
  - ksWPH 1 ((1 + d) / 2) ((1 + d) / 2) = log (1 - d) * k128 + log 2 * k129 + k130 := by
  subst hk128 hk129 hk130
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_l6 hd.2, zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY2_H27 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k131 k132 k133 : ℝ} (hk131 : k131 = -((d - 1) * (d ^ 2 + 4 * d + 7)
  / 24)) (hk132 : k132 = (d - 1) * (d ^ 2 + 4 * d + 7) / 24) (hk133 : k133 = (d - 1) * (11 * d ^ 2
  + 32 * d + 29) / 144) :
    ksWPH 2 ((1 + d) / 2) 1 - ksWPH 2 ((1 + d) / 2) ((1 + d)
  / 2) = log (1 - d) * k131 + log 2 * k132 + k133 := by
  subst hk131 hk132 hk133
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add,
    mul_one, one_mul]
  simp only [ksWY_log_l6 hd.2, zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY2_H28 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k134 k135 k136 : ℝ} (hk134 : k134 = (2 * b - d - 1) / 2) (hk135 : k135 = 1
  - b) (hk136 : k136 = (d - 1) / 2) :
    ksWPH 0 b 1 - ksWPH 0 b ((1 + d) / 2) = log (b - (1 + d)
  / 2) * k134 + log (1 - b) * k135 + k136 := by
  subst hk134 hk135 hk136
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.reduceSub, pow_zero, pow_one, one_pow, zero_add, mul_one, one_mul]
  simp only [ksWY_log_swap ((1 + d) / 2) b]
  field_simp
  ring

theorem ksWY2_H29 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k137 k138 k139 : ℝ} (hk137 : k137 = (2 * b + d + 1) * (2 * b - d - 1)
  / 8) (hk138 : k138 = -((b + 1) * (b - 1) / 2)) (hk139 : k139 = (d - 1) * (4 * b + d + 3)
  / 16) :
    ksWPH 1 b 1 - ksWPH 1 b ((1 + d) / 2) = log (b - (1 + d) / 2) * k137 + log (1 - b)
  * k138 + k139 := by
  subst hk137 hk138 hk139
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add, mul_one,
    one_mul]
  simp only [ksWY_log_swap ((1 + d) / 2) b]
  field_simp
  ring

theorem ksWY2_H30 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k140 k141 k142 : ℝ} (hk140 : k140 = (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b
  + d ^ 2 + 2 * d + 1) / 24) (hk141 : k141 = -((b - 1) * (b ^ 2 + b + 1) / 3)) (hk142 : k142 = (d
  - 1) * (12 * b ^ 2 + 3 * b * d + 9 * b + d ^ 2 + 4 * d + 7) / 72) :
    ksWPH 2 b 1
  - ksWPH 2 b ((1 + d) / 2) = log (b - (1 + d) / 2) * k140 + log (1 - b) * k141 + k142 := by
  subst hk140 hk141 hk142
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add,
    mul_one, one_mul]
  simp only [ksWY_log_swap ((1 + d) / 2) b]
  field_simp
  ring

theorem ksWY2_H31 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k143 k144 k145 k146 k147 k148 : ℝ} (hk143 : k143 = -((d - 1) * (2 * b + d - 1) / (4 * b
  - 4))) (hk144 : k144 = (d - 1) / 2) (hk145 : k145 = -((d - 1) / 2)) (hk146 : k146 = (d + 1) * (d
  - 1) / (4 * b - 4)) (hk147 : k147 = (d - 1) * (2 * b - d - 3) / (4 * b - 4)) (hk148 : k148 = (d
  - 1) / 2) :
    ksWPH 0 (1 - 1 / ((1 - b) * ksDT 1 d)) 1 - ksWPH 0 (1 - 1 / ((1 - b)
  * ksDT 1 d)) ((1 + d) / 2) = log (b - (1 - d) / 2) * k143 + log (1 - b) * k144 + log (1 - d)
  * k145 + log (1 + d) * k146 + log 2 * k147 + k148 := by
  subst hk143 hk144 hk145 hk146 hk147 hk148
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.reduceSub, pow_zero, pow_one, one_pow, zero_add, mul_one, one_mul]
  simp only [ksWY_sp_sub_w0 hd hb1, ksWY_log_w0p hd hm hb1,
    sub_sub_cancel 1 (1 / ((1 - b) * ksDT 1 d)), ksWY_log_w0o hd hb1]
  try rw [ksWW_inv_K hd h1b]
  field_simp
  ring

theorem ksWY2_H32 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k149 k150 k151 k152 k153 k154 : ℝ} (hk149 : k149 = -((d - 1) * (2 * b + d - 1) * (2 * b
  * d + 6 * b - d ^ 2 - 2 * d - 5) / (32 * (b - 1) ^ 2))) (hk150 : k150 = (d - 1) * (d + 3)
  / 8) (hk151 : k151 = -((d - 1) * (d + 3) / 8)) (hk152 : k152 = (d + 1) * (d - 1) * (8 * b
  - d ^ 2 - 7) / (32 * (b - 1) ^ 2)) (hk153 : k153 = (d - 1) * (4 * d * b ^ 2 + 12 * b ^ 2 - 16
  * b * d - 32 * b + d ^ 3 + d ^ 2 + 11 * d + 19) / (32 * (b - 1) ^ 2)) (hk154 : k154 = (d - 1)
  * (b * d + 7 * b - d ^ 2 - d - 6) / (16 * b - 16)) :
    ksWPH 1 (1 - 1 / ((1 - b)
  * ksDT 1 d)) 1 - ksWPH 1 (1 - 1 / ((1 - b) * ksDT 1 d)) ((1 + d) / 2) = log (b - (1 - d) / 2)
  * k149 + log (1 - b) * k150 + log (1 - d) * k151 + log (1 + d) * k152 + log 2 * k153 + k154 := by
  subst hk149 hk150 hk151 hk152 hk153 hk154
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add, mul_one,
    one_mul]
  simp only [ksWY_sp_sub_w0 hd hb1, ksWY_log_w0p hd hm hb1,
    sub_sub_cancel 1 (1 / ((1 - b) * ksDT 1 d)), ksWY_log_w0o hd hb1]
  try rw [ksWW_inv_K hd h1b]
  field_simp
  ring

theorem ksWY2_H33 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {k155 k156 k157 k158 k159 k160 : ℝ} (hk155 : k155 = -((d - 1) * (2 * b + d - 1) * (4
  * b ^ 2 * d ^ 2 + 16 * d * b ^ 2 + 28 * b ^ 2 - 2 * b * d ^ 3 - 18 * b * d ^ 2 - 30 * b * d - 46
  * b + d ^ 4 + 2 * d ^ 3 + 12 * d ^ 2 + 14 * d + 19) / (192 * (b - 1) ^ 3))) (hk156 : k156 = (d
  - 1) * (d ^ 2 + 4 * d + 7) / 24) (hk157 : k157 = -((d - 1) * (d ^ 2 + 4 * d + 7)
  / 24)) (hk158 : k158 = (d + 1) * (d - 1) * (48 * b ^ 2 - 12 * b * d ^ 2 - 84 * b + d ^ 4 + 10
  * d ^ 2 + 37) / (192 * (b - 1) ^ 3)) (hk159 : k159 = (d - 1) * (8 * b ^ 3 * d ^ 2 + 32 * d
  * b ^ 3 + 56 * b ^ 3 - 24 * b ^ 2 * d ^ 2 - 144 * d * b ^ 2 - 216 * b ^ 2 + 12 * b * d ^ 3 + 36
  * b * d ^ 2 + 180 * b * d + 252 * b - d ^ 5 - d ^ 4 - 10 * d ^ 3 - 18 * d ^ 2 - 69 * d - 93)
  / (192 * (b - 1) ^ 3)) (hk160 : k160 = (d - 1) * (4 * b ^ 2 * d ^ 2 + 28 * d * b ^ 2 + 112
  * b ^ 2 - 3 * b * d ^ 3 - 41 * b * d ^ 2 - 53 * b * d - 191 * b + 3 * d ^ 4 + 3 * d ^ 3 + 31
  * d ^ 2 + 25 * d + 82) / (288 * (b - 1) ^ 2)) :
    ksWPH 2 (1 - 1 / ((1 - b) * ksDT 1 d)) 1
  - ksWPH 2 (1 - 1 / ((1 - b) * ksDT 1 d)) ((1 + d) / 2) = log (b - (1 - d) / 2) * k155 + log (1
  - b) * k156 + log (1 - d) * k157 + log (1 + d) * k158 + log 2 * k159 + k160 := by
  subst hk155 hk156 hk157 hk158 hk159 hk160
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, zero_add,
    mul_one, one_mul]
  simp only [ksWY_sp_sub_w0 hd hb1, ksWY_log_w0p hd hm hb1,
    sub_sub_cancel 1 (1 / ((1 - b) * ksDT 1 d)), ksWY_log_w0o hd hb1]
  try rw [ksWW_inv_K hd h1b]
  field_simp
  ring

theorem ksWY2_p1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c6 p45 p46 p47 : ℝ} (hc6 : c6 = (16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 - 16
  * log (ksDT 1 d) * ksDT 1 d * b + 16 * log b * ksDT 1 d * b ^ 2 - 16 * log b * ksDT 1 d * b + 24
  * ksDT 1 d * b ^ 2 - 24 * ksDT 1 d * b + 16 * ksDT 1 d - 40) / (ksDT 1 d * b)) (hp45 : p45 = (16
  * b - 16)) (hp46 : p46 = (16 * b - 16)) (hp47 : p47 = (24 * ksDT 1 d * b ^ 2 - 24 * ksDT 1 d * b
  + 16 * ksDT 1 d - 40) / (ksDT 1 d * b)) :
    c6 = log (ksDT 1 d) * p45 + log b * p46 + p47 := by
  subst hc6 hp45 hp46 hp47
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY2_p2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c50 p70 p71 p72 p73 : ℝ} (hc50 : c50 = (16 * log (ksDA 1 (-ksDT 1 d) b) * b ^ 2 - 16
  * log (ksDA 1 (-ksDT 1 d) b) * b - 8 * log (ksDT 1 d) * b - 8 * log b * b + 24 * b ^ 2 - 20 * b
  + 16) / b) (hp70 : p70 = (16 * b - 16)) (hp71 : p71 = -8) (hp72 : p72 = -8) (hp73 : p73 = (24
  * b ^ 2 - 20 * b + 16) / b) :
    c50 = log (ksDA 1 (-ksDT 1 d) b) * p70 + log (ksDT 1 d) * p71
  + log b * p72 + p73 := by
  subst hc50 hp70 hp71 hp72 hp73
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY2_p3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c51 p74 p75 p76 : ℝ} (hc51 : c51 = (8 * log (ksDT 1 d) + 8 * log b
  - 4)) (hp74 : p74 = 8) (hp75 : p75 = 8) (hp76 : p76 = -4) :
    c51 = log (ksDT 1 d) * p74
  + log b * p75 + p76 := by
  subst hc51 hp74 hp75 hp76
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY2_p4 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c77 p98 p99 : ℝ} (hc77 : c77 = -((16 * log (ksDA 1 (-ksDT 1 d) b) * b ^ 2 - 16
  * log (ksDA 1 (-ksDT 1 d) b) * b + 24 * b ^ 2 - 24 * b + 16) / (b - 1))) (hp98 : p98 = -(16
  * b)) (hp99 : p99 = -((24 * b ^ 2 - 24 * b + 16) / (b
  - 1))) :
    c77 = log (ksDA 1 (-ksDT 1 d) b) * p98 + p99 := by
  subst hc77 hp98 hp99
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY2_p5 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c78 p100 p101 p102 p103 : ℝ} (hc78 : c78 = (-(8 * log (1 - b) * b) + 8 * log (1 - b) + 16
  * log (ksDA 1 (-ksDT 1 d) b) * b ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b) * b - 8 * log (ksDT 1 d)
  * b + 8 * log (ksDT 1 d) + 24 * b ^ 2 - 20 * b + 12) / (b
  - 1)) (hp100 : p100 = -8) (hp101 : p101 = 16 * b) (hp102 : p102 = -8) (hp103 : p103 = (24
  * b ^ 2 - 20 * b + 12) / (b - 1)) :
    c78 = log (1 - b) * p100 + log (ksDA 1 (-ksDT 1 d) b)
  * p101 + log (ksDT 1 d) * p102 + p103 := by
  subst hc78 hp100 hp101 hp102 hp103
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY2_p6 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c79 p104 p105 p106 : ℝ} (hc79 : c79 = (8 * log (1 - b) + 8 * log (ksDT 1 d)
  - 4)) (hp104 : p104 = 8) (hp105 : p105 = 8) (hp106 : p106 = -4) :
    c79 = log (1 - b) * p104
  + log (ksDT 1 d) * p105 + p106 := by
  subst hc79 hp104 hp105 hp106
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY2_p7 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c110 p161 p162 p163 : ℝ} (hc110 : c110 = -((16 * log (1 - b) * ksDT 1 d ^ 2 * b ^ 3 - 32
  * log (1 - b) * ksDT 1 d ^ 2 * b ^ 2 + 16 * log (1 - b) * b * ksDT 1 d ^ 2 + 16 * log (ksDT 1 d)
  * ksDT 1 d ^ 2 * b ^ 3 - 32 * log (ksDT 1 d) * ksDT 1 d ^ 2 * b ^ 2 + 16 * log (ksDT 1 d) * b
  * ksDT 1 d ^ 2 + 24 * ksDT 1 d ^ 2 * b ^ 3 - 48 * ksDT 1 d ^ 2 * b ^ 2 + 40 * b * ksDT 1 d ^ 2
  - 16 * ksDT 1 d ^ 2 - 16 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b + 8 * ksDT 1 d + 48)
  / (ksDT 1 d ^ 2 * (b - 1) ^ 2))) (hp161 : p161 = -(16 * b)) (hp162 : p162 = -(16
  * b)) (hp163 : p163 = -((24 * ksDT 1 d ^ 2 * b ^ 3 - 48 * ksDT 1 d ^ 2 * b ^ 2 + 40 * b
  * ksDT 1 d ^ 2 - 16 * ksDT 1 d ^ 2 - 16 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b + 8 * ksDT 1 d
  + 48) / (ksDT 1 d ^ 2 * (b - 1) ^ 2))) :
    c110 = log (1 - b) * p161 + log (ksDT 1 d) * p162
  + p163 := by
  subst hc110 hp161 hp162 hp163
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY2_p8 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c111 p164 p165 p166 : ℝ} (hc111 : c111 = (16 * log (1 - b) * ksDT 1 d * b ^ 2 - 16
  * log (1 - b) * ksDT 1 d * b + 16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 - 16 * log (ksDT 1 d)
  * ksDT 1 d * b + 24 * ksDT 1 d * b ^ 2 - 24 * ksDT 1 d * b + 16 * ksDT 1 d - 40) / (ksDT 1 d
  * (b - 1))) (hp164 : p164 = 16 * b) (hp165 : p165 = 16 * b) (hp166 : p166 = (24 * ksDT 1 d
  * b ^ 2 - 24 * ksDT 1 d * b + 16 * ksDT 1 d - 40) / (ksDT 1 d * (b - 1))) :
    c111 = log (1
  - b) * p164 + log (ksDT 1 d) * p165 + p166 := by
  subst hc111 hp164 hp165 hp166
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY2_k0_0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c1 k11 c2 k14 c3 k17 k21 k25 : ℝ} (hc1 : c1 = -((16 * b - 16))) (hk11 : k11 = -((d
  - 1) ^ 2 / 16)) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk14 : k14 = -(3 * (d - 1) ^ 2 / 16)) (hc3 : c3 = (8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk17 : k17 = 11 * (d - 1) ^ 3 / 144) (hk21 : k21 = (d - 1) * (d + 3)
  / 16) (hk25 : k25 = (d - 1) * (5 * d ^ 2 + 8 * d + 11) / 144) {r : ℝ} (hr : r = ((4 / 9) * ((1
  - d) / 2) * (9 * ((1 - d) / 2) * b ^ 3 - 16 * ((1 - d) / 2) ^ 2 * b ^ 2 + 3 * b ^ 2 - 9 * b
  * ((1 - d) / 2) ^ 3 + 25 * b * ((1 - d) / 2) ^ 2 - 9 * ((1 - d) / 2) * b - 3 * b + 80 * ((1 - d)
  / 2) ^ 4 - 161 * ((1 - d) / 2) ^ 3 + 98 * ((1 - d) / 2) ^ 2 - 21 * ((1 - d) / 2) - 6) / ((b - (1
  - d) / 2) * (b - (1 + d) / 2)))) :
    c1 * k11 + c2 * k14 + c3 * k17 + c2 * k21 + c3
  * k25 = r := by
  subst hr hc1 hk11 hc2 hk14 hc3 hk17 hk21 hk25
  have hm : b ≠ (1 - d) / 2 := ne_of_gt hb.1
  have hp : b ≠ (1 + d) / 2 := ne_of_lt hb.2
  have hb1 : b ≠ 1 := (by linarith only [hb.2, hd.2] : b < 1).ne
  have hb0 : b ≠ 0 := (by linarith only [hb.1, hd.2] : 0 < b).ne'
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := (by linarith only [hd.2] : 0 < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith only [hd.1] : 0 < 1 + d).ne'
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  try simp only [ksWY_ksDT_quad hd]
  obtain ⟨x, rfl⟩ : ∃ x, d = 1 - 2 * x := ⟨(1 - d) / 2, by ring⟩
  have hx : x ≠ 0 := (by linarith only [hd.2] : 0 < x).ne'
  have h1x : 1 - x ≠ 0 := (by linarith only [hd.1] : 0 < 1 - x).ne'
  have e1 : (1 - (1 - 2 * x)) / 2 = x := by ring
  have e2 : (1 + (1 - 2 * x)) / 2 = 1 - x := by ring
  have hden : (1 : ℝ) - (1 - 2 * x) ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
    exact mul_ne_zero four_ne_zero (mul_ne_zero hx h1x)
  have eT : ksDT 1 (1 - 2 * x) = 1 / (x * (1 - x)) := by
    unfold ksDT
    rw [div_eq_div_iff hden (mul_ne_zero hx h1x)]
    ring
  have hd0 : 1 - 2 * x ≠ 0 := hd.1.ne'
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

end QED.ChainProof.SetAKS

end
