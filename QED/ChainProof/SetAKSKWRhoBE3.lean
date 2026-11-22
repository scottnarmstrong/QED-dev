/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBS

/-!
# Set (a), stage D: the `β`-integrand on `β > σ₊` as a `ksWYe` combination

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. For
`β ∈ (σ₊, 1)` (`σ± = (1 ± δ)/2`) the `w`-integrated `VB` density `ksWWEIII β δ` is the combination
`ksWYe` of the generated lists `ksWY3L`, ..., `ksWY3S` (logarithms of `β - σ±` and of `β`, with
polynomial coefficients, difference quotients, poles at `β = 0`). The identity is split by
logarithm: the differences `ksWPH j a σ₊ - ksWPH j a σ₋` in closed form (`ksWY3_H*`), the
logarithmic coefficients of `ksWW5P` (`ksWY3_p*`) and one rational identity per logarithm
(`ksWY3_k*`).
The lists and these lemmas are machine-generated; every coefficient is checked by the proofs.

Main result:

* **`ksWY3_eqOn`**: `ksWYe (ksWY3L δ) ... = ksWWEIII · δ` on `(σ₊, 1)`.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetAKS

variable {b d : ℝ}

/-- Region `3`: the terms `c β^j log (β - a)`. -/
noncomputable def ksWY3L (d : ℝ) : List (ℝ × ℕ × ℝ) := [
  ((2 * d ^ 3 + 4 * d ^ 2 - 6 * d + 4) / 3, 0, ((1 - d) / 2)),
  (-((8 * d ^ 2 + 8) / 3), 1, ((1 - d) / 2)),
  (4, 2, ((1 - d) / 2)),
  (-16 / 3, 3, ((1 - d) / 2)),
  ((2 * d ^ 3 - 4 * d ^ 2 - 6 * d - 4) / 3, 0, ((1 + d) / 2)),
  ((8 * d ^ 2 + 8) / 3, 1, ((1 + d) / 2)),
  (-4, 2, ((1 + d) / 2)),
  (16 / 3, 3, ((1 + d) / 2))]

/-- Region `3`: the monomials. -/
noncomputable def ksWY3P (d : ℝ) : List (ℝ × ℕ) := [
  (4 * log 2 * d * (d ^ 2 - 3) / 3 - 2 * log (1 - d) * d * (d ^ 2 - 3) / 3 - 2 * log (1 + d) * d
    * (d ^ 2 - 3) / 3 + d * (37 * d ^ 2 - 9) / 9, 0),
  (-(4 * d / 3), 1),
  (16 * d / 3, 2)]

/-- Region `3`: the difference quotients. -/
noncomputable def ksWY3D (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3), 0, ((1 - d) / 2)),
  (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3, 0, ((1 + d) / 2)),
  (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3, ((1 - d) / 2), 0),
  (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3), ((1 - d) / 2), ((1 + d) / 2)),
  (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3), ((1 + d) / 2), 0),
  (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3, ((1 + d) / 2), ((1 - d) / 2))]

/-- Region `3`: the double poles. -/
noncomputable def ksWY3Q (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (-((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12), ((1 - d) / 2), 0),
  ((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12, ((1 + d) / 2), 0)]

/-- Region `3`: the triple poles. -/
noncomputable def ksWY3C (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3), ((1 - d) / 2), 0),
  ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3, ((1 + d) / 2), 0)]

/-- Region `3`: the rational simple and double poles. -/
noncomputable def ksWY3R (d : ℝ) : List (ℝ × ℝ × ℝ) := [
  (0, d * (d + 1) * (d - 1) / 3, log (1 - d) * (d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12 - log (1
    + d) * (d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12 + 4 * d * (d + 1) * (d - 1) * (2 * d ^ 2
    - 3) / 3)]

/-- Region `3`: the rational triple poles. -/
noncomputable def ksWY3S (d : ℝ) : List (ℝ × ℝ) := [
  (0, log (1 - d) * (d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3 - log (1 + d) * (d + 1) ^ 2
    * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)]


theorem ksWY3_H1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 1 0 ((1 + d)
  / 2) - ksWPH 1 0 ((1 - d) / 2) = log (1 - d) * (-((d - 1) ^ 2 / 8)) + log (1 + d) * ((d + 1) ^ 2
  / 8) + log 2 * (-(d / 2)) + (-(d / 4)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul,
    add_zero]
  simp only [ksWY_log_sm hd.2, ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_zero, mul_zero,
    zero_add]
  field_simp
  ring

theorem ksWY3_H2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 2 0 ((1 + d)
  / 2) - ksWPH 2 0 ((1 - d) / 2) = log (1 - d) * ((d - 1) ^ 3 / 24) + log (1 + d) * ((d + 1) ^ 3
  / 24) + log 2 * (-(d * (d ^ 2 + 3) / 12)) + (-(d * (d ^ 2 + 3) / 36)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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
  simp only [ksWY_log_sm hd.2, ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_zero, mul_zero,
    add_zero]
  field_simp
  ring

theorem ksWY3_H3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 1 ((1 - d)
  / 2) ((1 + d) / 2) - ksWPH 1 ((1 - d) / 2) ((1 - d) / 2) = log d * (d / 2) + (d * (d - 2)
  / 4) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_log_l3, zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY3_H4 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 2 ((1 - d)
  / 2) ((1 + d) / 2) - ksWPH 2 ((1 - d) / 2) ((1 - d) / 2) = log d * (d * (d ^ 2 + 3) / 12) + (-(d
  * (4 * d ^ 2 - 9 * d + 9) / 36)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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
  simp only [ksWY_log_l3, zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY3_H5 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 1 ((1 + d)
  / 2) ((1 + d) / 2) - ksWPH 1 ((1 + d) / 2) ((1 - d) / 2) = log d * (d / 2) + (-(d * (d + 2)
  / 4)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_log_l4, zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY3_H6 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 2 ((1 + d)
  / 2) ((1 + d) / 2) - ksWPH 2 ((1 + d) / 2) ((1 - d) / 2) = log d * (d * (d ^ 2 + 3) / 12) + (-(d
  * (4 * d ^ 2 + 9 * d + 9) / 36)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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
  simp only [ksWY_log_l4, zero_sub, sub_self, log_zero, mul_zero]
  field_simp
  ring

theorem ksWY3_H7 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 1 b ((1 + d)
  / 2) - ksWPH 1 b ((1 - d) / 2) = log (b - (1 - d) / 2) * ((2 * b - d + 1) * (2 * b + d - 1) / 8)
  + log (b - (1 + d) / 2) * (-((2 * b + d + 1) * (2 * b - d - 1) / 8)) + (-(d * (2 * b + 1)
  / 4)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_H8 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 2 b ((1 + d)
  / 2) - ksWPH 2 b ((1 - d) / 2) = log (b - (1 - d) / 2) * ((2 * b + d - 1) * (4 * b ^ 2 - 2 * b
  * d + 2 * b + d ^ 2 - 2 * d + 1) / 24) + log (b - (1 + d) / 2) * (-((2 * b - d - 1) * (4 * b ^ 2
  + 2 * b * d + 2 * b + d ^ 2 + 2 * d + 1) / 24)) + (-(d * (12 * b ^ 2 + 6 * b + d ^ 2 + 3)
  / 36)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_H9 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 1 (1 / (b
  * ksDT 1 d)) ((1 + d) / 2) - ksWPH 1 (1 / (b * ksDT 1 d)) ((1 - d) / 2) = log (b - (1 - d) / 2)
  * ((d + 1) ^ 2 * (2 * b - d + 1) * (2 * b + d - 1) / (32 * b ^ 2)) + log (b - (1 + d) / 2)
  * (-((d - 1) ^ 2 * (2 * b + d + 1) * (2 * b - d - 1) / (32 * b ^ 2))) + log (1 - d) * (-((d
  - 1) ^ 2 * (2 * b + d + 1) * (2 * b - d - 1) / (32 * b ^ 2))) + log (1 + d) * ((d + 1) ^ 2 * (2
  * b - d + 1) * (2 * b + d - 1) / (32 * b ^ 2)) + log 2 * (-(d / 2)) + log b * (-(d / 2)) + (-(d
  * (2 * b - d ^ 2 + 1) / (8 * b))) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, zero_add, mul_one, one_mul]
  simp only [ksWY_sp_sub_w1 hd hb0, ksWY_sm_sub_w1 hd hb0, ksWY_log_w1p hd hm hb0,
    ksWY_log_w1m hd hp hb0]
  try rw [ksWW_inv_K hd hb0]
  field_simp
  ring

theorem ksWY3_H10 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ksWPH 2 (1 / (b
  * ksDT 1 d)) ((1 + d) / 2) - ksWPH 2 (1 / (b * ksDT 1 d)) ((1 - d) / 2) = log (b - (1 - d) / 2)
  * ((d + 1) ^ 3 * (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2 * d + 1) / (192
  * b ^ 3)) + log (b - (1 + d) / 2) * ((d - 1) ^ 3 * (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2
  * b + d ^ 2 + 2 * d + 1) / (192 * b ^ 3)) + log (1 - d) * ((d - 1) ^ 3 * (2 * b - d - 1) * (4
  * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2 * d + 1) / (192 * b ^ 3)) + log (1 + d) * ((d + 1) ^ 3
  * (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2 * d + 1) / (192 * b ^ 3)) + log 2
  * (-(d * (d ^ 2 + 3) / 12)) + log b * (-(d * (d ^ 2 + 3) / 12)) + (-(d * (4 * b ^ 2 * d ^ 2 + 12
  * b ^ 2 - 6 * b * d ^ 2 + 6 * b + 3 * d ^ 4 - 6 * d ^ 2 + 3) / (144 * b ^ 2))) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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
  simp only [ksWY_sp_sub_w1 hd hb0, ksWY_sm_sub_w1 hd hb0, ksWY_log_w1p hd hm hb0,
    ksWY_log_w1m hd hp hb0]
  try rw [ksWW_inv_K hd hb0]
  field_simp
  ring

theorem ksWY3_p1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ((16
  * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b
  - 16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 + 8 * log (ksDT 1 d) * ksDT 1 d * b - 16 * log b
  * ksDT 1 d * b ^ 2 + 8 * log b * ksDT 1 d * b + 4 * ksDT 1 d * b + 40) / (ksDT 1 d
  * b)) = log (ksDA 1 (-ksDT 1 d) b) * ((16 * b - 16)) + log (ksDT 1 d) * (-((16 * b - 8)))
  + log b * (-((16 * b - 8))) + ((4 * ksDT 1 d * b + 40) / (ksDT 1 d * b)) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY3_p2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ((8
  * log (ksDT 1 d) + 8 * log b - 4)) = log (ksDT 1 d) * (8) + log b * (8) + (-4) := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  field_simp
  ring

theorem ksWY3_k0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ((16 * b - 8))
  * (-(d / 4)) + (-8) * (-(d * (d ^ 2 + 3) / 36)) + (-((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2
  - ksDT 1 d * b + 1))) * (d * (d - 2) / 4) + ((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d
  * b + 1)) * (-(d * (4 * d ^ 2 - 9 * d + 9) / 36)) + (-((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2
  - ksDT 1 d * b + 1))) * (-(d * (d + 2) / 4)) + ((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2
  - ksDT 1 d * b + 1)) * (-(d * (4 * d ^ 2 + 9 * d + 9) / 36)) + (-((16 * ksDT 1 d * b ^ 3 - 24
  * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2
  - ksDT 1 d * b + 1))) * (-(d * (2 * b + 1) / 4)) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b
  - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * (-(d * (12 * b ^ 2 + 6 * b
  + d ^ 2 + 3) / 36)) + (-((16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (-(d * (2 * b - d ^ 2 + 1)
  / (8 * b))) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1)) * (-(d * (4 * b ^ 2 * d ^ 2 + 12 * b ^ 2 - 6 * b * d ^ 2 + 6 * b
  + 3 * d ^ 4 - 6 * d ^ 2 + 3) / (144 * b ^ 2))) + (1 * (-((16 * ksDT 1 d * b ^ 2 + 16 * ksDT 1 d
  * b - 48) / (ksDT 1 d ^ 2 * b ^ 2)))) * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (1 * ((4
  * ksDT 1 d * b + 40) / (ksDT 1 d * b))) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (1
  * (-4)) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) + -(((8 * ksDT 1 d * b ^ 2 - 8
  * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4 * b ^ 4)) / ((1 + d) / 2 * (b - (1 - d) / 2) / b) - ((8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4 * b ^ 4)) / ((1 - d) / 2 * (b - (1
  + d) / 2) / b)) = (d * (37 * d ^ 2 - 9) / 9) * b ^ 0 + (-(4 * d / 3)) * b ^ 1 + (16 * d / 3)
  * b ^ 2 + (d * (d + 1) * (d - 1) / 3) * (b - 0)⁻¹ + (4 * d * (d + 1) * (d - 1) * (2 * d ^ 2 - 3)
  / 3) * ((b - 0) ^ 2)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_kA (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    (-((16 * ksDT 1 d
  * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1))) * ((2 * b - d + 1) * (2 * b + d - 1) / 8) + ((8 * ksDT 1 d * b ^ 2
  - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * ((2 * b + d
  - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2 * d + 1) / 24) + (-((16 * ksDT 1 d * b ^ 3
  - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2
  - ksDT 1 d * b + 1))) * ((d + 1) ^ 2 * (2 * b - d + 1) * (2 * b + d - 1) / (32 * b ^ 2)) + ((8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) * ((d + 1) ^ 3 * (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2 * d + 1)
  / (192 * b ^ 3)) + (1 * ((16 * b - 16))) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + 1
  * (-((8 * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56) / (ksDT 1 d ^ 3 * b ^ 3))) = ((2 * d ^ 3
  + 4 * d ^ 2 - 6 * d + 4) / 3) * b ^ 0 + (-((8 * d ^ 2 + 8) / 3)) * b ^ 1 + 4 * b ^ 2 + (-16 / 3)
  * b ^ 3 + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - 0)⁻¹ + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3)
  / 3)) * (b - ((1 + d) / 2))⁻¹ + (-((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12)) * ((b
  - 0) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)) * ((b - 0) ^ 3)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_kB (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    (-((16 * ksDT 1 d
  * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1))) * (-((2 * b + d + 1) * (2 * b - d - 1) / 8)) + ((8 * ksDT 1 d
  * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))
  * (-((2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2 * d + 1) / 24)) + (-((16
  * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (-((d - 1) ^ 2 * (2 * b + d + 1) * (2 * b - d - 1)
  / (32 * b ^ 2))) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1)) * ((d - 1) ^ 3 * (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b
  + d ^ 2 + 2 * d + 1) / (192 * b ^ 3)) + (1 * ((16 * b - 16))) * ((((1 + d) / 2) ^ 2 - ((1 - d)
  / 2) ^ 2) / 2) + -1 * (-((8 * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56) / (ksDT 1 d ^ 3
  * b ^ 3))) = ((2 * d ^ 3 - 4 * d ^ 2 - 6 * d - 4) / 3) * b ^ 0 + ((8 * d ^ 2 + 8) / 3) * b ^ 1
  + (-4) * b ^ 2 + (16 / 3) * b ^ 3 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - 0)⁻¹ + (4
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 - d) / 2))⁻¹ + ((d + 1) * (d - 1) * (17 * d ^ 2
  - 25) / 12) * ((b - 0) ^ 2)⁻¹ + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) * ((b
  - 0) ^ 3)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_kM (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ((16 * b - 8))
  * (-((d - 1) ^ 2 / 8)) + (-8) * ((d - 1) ^ 3 / 24) + (-((16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d
  * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1))) * (-((d - 1) ^ 2 * (2 * b + d + 1) * (2 * b - d - 1) / (32 * b ^ 2))) + ((8 * ksDT 1 d
  * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * ((d
  - 1) ^ 3 * (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2 * d + 1) / (192
  * b ^ 3)) + (-1 * ((16 * b - 16)) + -1 * (-((16 * b - 8)))) * ((((1 + d) / 2) ^ 2 - ((1 - d)
  / 2) ^ 2) / 2) + (-1 * (8)) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) + -1 * (-((8
  * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56) / (ksDT 1 d ^ 3 * b ^ 3))) = (-(2 * d * (d ^ 2 - 3)
  / 3)) * b ^ 0 + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 - d) / 2))⁻¹ + (-(2 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3)) * (b - 0)⁻¹ + ((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12) * ((b - 0) ^ 2)⁻¹
  + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) * ((b - 0) ^ 3)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_kN (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ((16 * b - 8))
  * ((d + 1) ^ 2 / 8) + (-8) * ((d + 1) ^ 3 / 24) + (-((16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d
  * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1))) * ((d + 1) ^ 2 * (2 * b - d + 1) * (2 * b + d - 1) / (32 * b ^ 2)) + ((8 * ksDT 1 d
  * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * ((d
  + 1) ^ 3 * (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2 * d + 1) / (192
  * b ^ 3)) + (-1 * ((16 * b - 16)) + -1 * (-((16 * b - 8)))) * ((((1 + d) / 2) ^ 2 - ((1 - d)
  / 2) ^ 2) / 2) + (-1 * (8)) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) + 1 * (-((8
  * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56) / (ksDT 1 d ^ 3 * b ^ 3))) = (-(2 * d * (d ^ 2 - 3)
  / 3)) * b ^ 0 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 + d) / 2))⁻¹ + (2 * (d ^ 2
  + 1) * (d ^ 2 - 3) / 3) * (b - 0)⁻¹ + (-((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12)) * ((b
  - 0) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)) * ((b - 0) ^ 3)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_kK (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ((16 * b - 8))
  * (-(d / 2)) + (-8) * (-(d * (d ^ 2 + 3) / 12)) + (-((16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d
  * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1))) * (-(d / 2)) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * (-(d * (d ^ 2 + 3) / 12)) + (2 * ((16 * b - 16)) + 2
  * (-((16 * b - 8)))) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (2 * (8)) * ((((1 + d)
  / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) = (4 * d * (d ^ 2 - 3) / 3) * b ^ 0 + (-(2 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1
  + d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - 0)⁻¹ + (-(2 * (d ^ 2 + 1) * (d ^ 2
  - 3) / 3)) * (b - 0)⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_kD (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    (-((16 * ksDT 1 d
  - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) * (d / 2) + ((16 * ksDT 1 d - 32) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1)) * (d * (d ^ 2 + 3) / 12) + (-((16 * ksDT 1 d - 32) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1))) * (d / 2) + ((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d
  * b + 1)) * (d * (d ^ 2 + 3) / 12) = (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d) / 2))⁻¹
  + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_kE (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    (-((16 * ksDT 1 d
  * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1))) * (-(d / 2)) + ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) * (-(d * (d ^ 2 + 3) / 12)) + (1
  * (-((16 * b - 8)))) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (1 * (8)) * ((((1 + d)
  / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) = (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d)
  / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d) / 2))⁻¹ := by
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
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

theorem ksWY3_eqOn (hd : d ∈ Ioo (0 : ℝ) 1) :
        EqOn (ksWYe (ksWY3L d) (ksWY3P d) (ksWY3D d) (ksWY3Q d) (ksWY3C d) (ksWY3R d) (ksWY3S d))
      (fun b => ksWWEIII b d) (Ioo ((1 + d) / 2) 1) := by
  intro b hb
  have hm : b ≠ (1 - d) / 2 := by linarith [hb.1, hd.1]
  have hp : b ≠ (1 + d) / 2 := by linarith [hb.1]
  have hb1 : b ≠ 1 := by linarith [hb.2]
  have hb0 : b ≠ 0 := by linarith [hb.1, hd.1]
  have hbm : b - (1 - d) / 2 ≠ 0 := sub_ne_zero.2 hm
  have hbp : b - (1 + d) / 2 ≠ 0 := sub_ne_zero.2 hp
  have h1b : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb1)
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.2 hb1
  have hdm : 1 - d ≠ 0 := by linarith [hd.2]
  have hdp : 1 + d ≠ 0 := by linarith [hd.1]
  have hT0 : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  obtain ⟨c1, hc1⟩ : ∃ x : ℝ, x = (16 * b - 8) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = -8 := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ x : ℝ, x = -((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
    + 1)) := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ x : ℝ, x = (16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
    + 1) := ⟨_, rfl⟩
  obtain ⟨c5, hc5⟩ : ∃ x : ℝ, x = -((16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d
    * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) := ⟨_, rfl⟩
  obtain ⟨c6, hc6⟩ : ∃ x : ℝ, x = (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1) := ⟨_, rfl⟩
  obtain ⟨c7, hc7⟩ : ∃ x : ℝ, x = -((16 * ksDT 1 d * b ^ 2 + 16 * ksDT 1 d * b - 48)
    / (ksDT 1 d ^ 2 * b ^ 2)) := ⟨_, rfl⟩
  obtain ⟨c8, hc8⟩ : ∃ x : ℝ, x = (16 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b ^ 2 - 16
    * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b - 16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 + 8
    * log (ksDT 1 d) * ksDT 1 d * b - 16 * log b * ksDT 1 d * b ^ 2 + 8 * log b * ksDT 1 d * b + 4
    * ksDT 1 d * b + 40) / (ksDT 1 d * b) := ⟨_, rfl⟩
  obtain ⟨c9, hc9⟩ : ∃ x : ℝ, x = (8 * log (ksDT 1 d) + 8 * log b - 4) := ⟨_, rfl⟩
  obtain ⟨c10, hc10⟩ : ∃ x : ℝ, x = -((8 * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56)
    / (ksDT 1 d ^ 3 * b ^ 3)) := ⟨_, rfl⟩
  obtain ⟨c11, hc11⟩ : ∃ x : ℝ, x = (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4
    * b ^ 4) := ⟨_, rfl⟩
  obtain ⟨k12, hk12⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 / 8) := ⟨_, rfl⟩
  obtain ⟨k13, hk13⟩ : ∃ x : ℝ, x = (d + 1) ^ 2 / 8 := ⟨_, rfl⟩
  obtain ⟨k14, hk14⟩ : ∃ x : ℝ, x = -(d / 2) := ⟨_, rfl⟩
  obtain ⟨k15, hk15⟩ : ∃ x : ℝ, x = -(d / 4) := ⟨_, rfl⟩
  obtain ⟨k16, hk16⟩ : ∃ x : ℝ, x = (d - 1) ^ 3 / 24 := ⟨_, rfl⟩
  obtain ⟨k17, hk17⟩ : ∃ x : ℝ, x = (d + 1) ^ 3 / 24 := ⟨_, rfl⟩
  obtain ⟨k18, hk18⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 3) / 12) := ⟨_, rfl⟩
  obtain ⟨k19, hk19⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 3) / 36) := ⟨_, rfl⟩
  obtain ⟨k20, hk20⟩ : ∃ x : ℝ, x = d / 2 := ⟨_, rfl⟩
  obtain ⟨k21, hk21⟩ : ∃ x : ℝ, x = d * (d - 2) / 4 := ⟨_, rfl⟩
  obtain ⟨k22, hk22⟩ : ∃ x : ℝ, x = d * (d ^ 2 + 3) / 12 := ⟨_, rfl⟩
  obtain ⟨k23, hk23⟩ : ∃ x : ℝ, x = -(d * (4 * d ^ 2 - 9 * d + 9) / 36) := ⟨_, rfl⟩
  obtain ⟨k24, hk24⟩ : ∃ x : ℝ, x = d / 2 := ⟨_, rfl⟩
  obtain ⟨k25, hk25⟩ : ∃ x : ℝ, x = -(d * (d + 2) / 4) := ⟨_, rfl⟩
  obtain ⟨k26, hk26⟩ : ∃ x : ℝ, x = d * (d ^ 2 + 3) / 12 := ⟨_, rfl⟩
  obtain ⟨k27, hk27⟩ : ∃ x : ℝ, x = -(d * (4 * d ^ 2 + 9 * d + 9) / 36) := ⟨_, rfl⟩
  obtain ⟨k28, hk28⟩ : ∃ x : ℝ, x = (2 * b - d + 1) * (2 * b + d - 1) / 8 := ⟨_, rfl⟩
  obtain ⟨k29, hk29⟩ : ∃ x : ℝ, x = -((2 * b + d + 1) * (2 * b - d - 1) / 8) := ⟨_, rfl⟩
  obtain ⟨k30, hk30⟩ : ∃ x : ℝ, x = -(d * (2 * b + 1) / 4) := ⟨_, rfl⟩
  obtain ⟨k31, hk31⟩ : ∃ x : ℝ, x = (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2
    * d + 1) / 24 := ⟨_, rfl⟩
  obtain ⟨k32, hk32⟩ : ∃ x : ℝ, x = -((2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2
    * d + 1) / 24) := ⟨_, rfl⟩
  obtain ⟨k33, hk33⟩ : ∃ x : ℝ, x = -(d * (12 * b ^ 2 + 6 * b + d ^ 2 + 3) / 36) := ⟨_, rfl⟩
  obtain ⟨k34, hk34⟩ : ∃ x : ℝ, x = (d + 1) ^ 2 * (2 * b - d + 1) * (2 * b + d - 1) / (32
    * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨k35, hk35⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 * (2 * b + d + 1) * (2 * b - d - 1) / (32
    * b ^ 2)) := ⟨_, rfl⟩
  obtain ⟨k36, hk36⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 * (2 * b + d + 1) * (2 * b - d - 1) / (32
    * b ^ 2)) := ⟨_, rfl⟩
  obtain ⟨k37, hk37⟩ : ∃ x : ℝ, x = (d + 1) ^ 2 * (2 * b - d + 1) * (2 * b + d - 1) / (32
    * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨k38, hk38⟩ : ∃ x : ℝ, x = -(d / 2) := ⟨_, rfl⟩
  obtain ⟨k39, hk39⟩ : ∃ x : ℝ, x = -(d / 2) := ⟨_, rfl⟩
  obtain ⟨k40, hk40⟩ : ∃ x : ℝ, x = -(d * (2 * b - d ^ 2 + 1) / (8 * b)) := ⟨_, rfl⟩
  obtain ⟨k41, hk41⟩ : ∃ x : ℝ, x = (d + 1) ^ 3 * (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b
    + d ^ 2 - 2 * d + 1) / (192 * b ^ 3) := ⟨_, rfl⟩
  obtain ⟨k42, hk42⟩ : ∃ x : ℝ, x = (d - 1) ^ 3 * (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b
    + d ^ 2 + 2 * d + 1) / (192 * b ^ 3) := ⟨_, rfl⟩
  obtain ⟨k43, hk43⟩ : ∃ x : ℝ, x = (d - 1) ^ 3 * (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b
    + d ^ 2 + 2 * d + 1) / (192 * b ^ 3) := ⟨_, rfl⟩
  obtain ⟨k44, hk44⟩ : ∃ x : ℝ, x = (d + 1) ^ 3 * (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b
    + d ^ 2 - 2 * d + 1) / (192 * b ^ 3) := ⟨_, rfl⟩
  obtain ⟨k45, hk45⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 3) / 12) := ⟨_, rfl⟩
  obtain ⟨k46, hk46⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 3) / 12) := ⟨_, rfl⟩
  obtain ⟨k47, hk47⟩ : ∃ x : ℝ, x = -(d * (4 * b ^ 2 * d ^ 2 + 12 * b ^ 2 - 6 * b * d ^ 2 + 6 * b
    + 3 * d ^ 4 - 6 * d ^ 2 + 3) / (144 * b ^ 2)) := ⟨_, rfl⟩
  obtain ⟨p48, hp48⟩ : ∃ x : ℝ, x = -((16 * ksDT 1 d * b ^ 2 + 16 * ksDT 1 d * b - 48)
    / (ksDT 1 d ^ 2 * b ^ 2)) := ⟨_, rfl⟩
  obtain ⟨p49, hp49⟩ : ∃ x : ℝ, x = (16 * b - 16) := ⟨_, rfl⟩
  obtain ⟨p50, hp50⟩ : ∃ x : ℝ, x = -((16 * b - 8)) := ⟨_, rfl⟩
  obtain ⟨p51, hp51⟩ : ∃ x : ℝ, x = -((16 * b - 8)) := ⟨_, rfl⟩
  obtain ⟨p52, hp52⟩ : ∃ x : ℝ, x = (4 * ksDT 1 d * b + 40) / (ksDT 1 d * b) := ⟨_, rfl⟩
  obtain ⟨p53, hp53⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨p54, hp54⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨p55, hp55⟩ : ∃ x : ℝ, x = -4 := ⟨_, rfl⟩
  have hL : ksWW5L b d = [(c1, 1, 0), (c2, 2, 0), (c3, 1, ((1 - d) / 2)), (c4, 2, ((1 - d)
    / 2)), (c3, 1, ((1 + d) / 2)), (c4, 2, ((1 + d) / 2)), (c5, 1, b), (c6, 2, b), (c5, 1, (1 / (b
    * ksDT 1 d))), (c6, 2, (1 / (b * ksDT 1 d)))] := by
    rw [hc1, hc2, hc3, hc4, hc5, hc6]
    rfl
  have hP : ksWW5P b d = [(c7, 0), (c8, 1), (c9, 2)] := by
    rw [hc7, hc8, hc9]
    rfl
  have hcc : ksWW5c b d = c10 := by rw [hc10]; rfl
  have hce : ksWW5e b d = c11 := by rw [hc11]; rfl
  have hH1 : ksWPH 1 0 ((1 + d) / 2) - ksWPH 1 0 ((1 - d) / 2) = log (1 - d) * k12 + log (1 + d)
    * k13 + log 2 * k14 + k15 := by
    rw [hk12, hk13, hk14, hk15]
    exact ksWY3_H1 hd hb
  have hH2 : ksWPH 2 0 ((1 + d) / 2) - ksWPH 2 0 ((1 - d) / 2) = log (1 - d) * k16 + log (1 + d)
    * k17 + log 2 * k18 + k19 := by
    rw [hk16, hk17, hk18, hk19]
    exact ksWY3_H2 hd hb
  have hH3 : ksWPH 1 ((1 - d) / 2) ((1 + d) / 2) - ksWPH 1 ((1 - d) / 2) ((1 - d) / 2) = log d
    * k20 + k21 := by
    rw [hk20, hk21]
    exact ksWY3_H3 hd hb
  have hH4 : ksWPH 2 ((1 - d) / 2) ((1 + d) / 2) - ksWPH 2 ((1 - d) / 2) ((1 - d) / 2) = log d
    * k22 + k23 := by
    rw [hk22, hk23]
    exact ksWY3_H4 hd hb
  have hH5 : ksWPH 1 ((1 + d) / 2) ((1 + d) / 2) - ksWPH 1 ((1 + d) / 2) ((1 - d) / 2) = log d
    * k24 + k25 := by
    rw [hk24, hk25]
    exact ksWY3_H5 hd hb
  have hH6 : ksWPH 2 ((1 + d) / 2) ((1 + d) / 2) - ksWPH 2 ((1 + d) / 2) ((1 - d) / 2) = log d
    * k26 + k27 := by
    rw [hk26, hk27]
    exact ksWY3_H6 hd hb
  have hH7 : ksWPH 1 b ((1 + d) / 2) - ksWPH 1 b ((1 - d) / 2) = log (b - (1 - d) / 2) * k28
    + log (b - (1 + d) / 2) * k29 + k30 := by
    rw [hk28, hk29, hk30]
    exact ksWY3_H7 hd hb
  have hH8 : ksWPH 2 b ((1 + d) / 2) - ksWPH 2 b ((1 - d) / 2) = log (b - (1 - d) / 2) * k31
    + log (b - (1 + d) / 2) * k32 + k33 := by
    rw [hk31, hk32, hk33]
    exact ksWY3_H8 hd hb
  have hH9 : ksWPH 1 (1 / (b * ksDT 1 d)) ((1 + d) / 2) - ksWPH 1 (1 / (b * ksDT 1 d)) ((1 - d)
    / 2) = log (b - (1 - d) / 2) * k34 + log (b - (1 + d) / 2) * k35 + log (1 - d) * k36 + log (1
    + d) * k37 + log 2 * k38 + log b * k39 + k40 := by
    rw [hk34, hk35, hk36, hk37, hk38, hk39, hk40]
    exact ksWY3_H9 hd hb
  have hH10 : ksWPH 2 (1 / (b * ksDT 1 d)) ((1 + d) / 2) - ksWPH 2 (1 / (b * ksDT 1 d)) ((1 - d)
    / 2) = log (b - (1 - d) / 2) * k41 + log (b - (1 + d) / 2) * k42 + log (1 - d) * k43 + log (1
    + d) * k44 + log 2 * k45 + log b * k46 + k47 := by
    rw [hk41, hk42, hk43, hk44, hk45, hk46, hk47]
    exact ksWY3_H10 hd hb
  have hp0 : c7 = p48 := by
    rw [hc7, hp48]
  have hp1 : c8 = log (ksDA 1 (-ksDT 1 d) b) * p49 + log (ksDT 1 d) * p50 + log b * p51 + p52 := by
    rw [hc8, hp49, hp50, hp51, hp52]
    exact ksWY3_p1 hd hb
  have hp2 : c9 = log (ksDT 1 d) * p53 + log b * p54 + p55 := by
    rw [hc9, hp53, hp54, hp55]
    exact ksWY3_p2 hd hb
  have k0 : c1 * k15 + c2 * k19 + c3 * k21 + c4 * k23 + c3 * k25 + c4 * k27 + c5 * k30 + c6 * k33
    + c5 * k40 + c6 * k47 + (1 * p48) * ((((1 + d) / 2) ^ 1 - ((1 - d) / 2) ^ 1) / 1) + (1 * p52)
    * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (1 * p55) * ((((1 + d) / 2) ^ 3 - ((1 - d)
    / 2) ^ 3) / 3) + -(c11 / ((1 + d) / 2 * (b - (1 - d) / 2) / b) - c11 / ((1 - d) / 2 * (b - (1
    + d) / 2) / b)) = (d * (37 * d ^ 2 - 9) / 9) * b ^ 0 + (-(4 * d / 3)) * b ^ 1 + (16 * d / 3)
    * b ^ 2 + (d * (d + 1) * (d - 1) / 3) * (b - 0)⁻¹ + (4 * d * (d + 1) * (d - 1) * (2 * d ^ 2
    - 3) / 3) * ((b - 0) ^ 2)⁻¹ := by
    rw [hc1, hk15, hc2, hk19, hc3, hk21, hc4, hk23, hk25, hk27, hc5, hk30, hc6, hk33, hk40, hk47,
      hp48, hp52, hp55, hc11]
    exact ksWY3_k0 hd hb
  have kA : c5 * k28 + c6 * k31 + c5 * k34 + c6 * k41 + (1 * p49) * ((((1 + d) / 2) ^ 2 - ((1 - d)
    / 2) ^ 2) / 2) + 1 * c10 = ((2 * d ^ 3 + 4 * d ^ 2 - 6 * d + 4) / 3) * b ^ 0 + (-((8 * d ^ 2
    + 8) / 3)) * b ^ 1 + 4 * b ^ 2 + (-16 / 3) * b ^ 3 + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b
    - 0)⁻¹ + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 + d) / 2))⁻¹ + (-((d + 1) * (d - 1)
    * (17 * d ^ 2 - 25) / 12)) * ((b - 0) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3)
    / 3)) * ((b - 0) ^ 3)⁻¹ := by
    rw [hc5, hk28, hc6, hk31, hk34, hk41, hp49, hc10]
    exact ksWY3_kA hd hb
  have kB : c5 * k29 + c6 * k32 + c5 * k35 + c6 * k42 + (1 * p49) * ((((1 + d) / 2) ^ 2 - ((1 - d)
    / 2) ^ 2) / 2) + -1 * c10 = ((2 * d ^ 3 - 4 * d ^ 2 - 6 * d - 4) / 3) * b ^ 0 + ((8 * d ^ 2
    + 8) / 3) * b ^ 1 + (-4) * b ^ 2 + (16 / 3) * b ^ 3 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3))
    * (b - 0)⁻¹ + (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 - d) / 2))⁻¹ + ((d + 1) * (d - 1)
    * (17 * d ^ 2 - 25) / 12) * ((b - 0) ^ 2)⁻¹ + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3)
    / 3) * ((b - 0) ^ 3)⁻¹ := by
    rw [hc5, hk29, hc6, hk32, hk35, hk42, hp49, hc10]
    exact ksWY3_kB hd hb
  have kM : c1 * k12 + c2 * k16 + c5 * k36 + c6 * k43 + (-1 * p49 + -1 * p50) * ((((1 + d)
    / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (-1 * p53) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3)
    / 3) + -1 * c10 = (-(2 * d * (d ^ 2 - 3) / 3)) * b ^ 0 + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)
    * (b - ((1 - d) / 2))⁻¹ + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - 0)⁻¹ + ((d + 1) * (d
    - 1) * (17 * d ^ 2 - 25) / 12) * ((b - 0) ^ 2)⁻¹ + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2
    - 3) / 3) * ((b - 0) ^ 3)⁻¹ := by
    rw [hc1, hk12, hc2, hk16, hc5, hk36, hc6, hk43, hp49, hp50, hp53, hc10]
    exact ksWY3_kM hd hb
  have kN : c1 * k13 + c2 * k17 + c5 * k37 + c6 * k44 + (-1 * p49 + -1 * p50) * ((((1 + d)
    / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (-1 * p53) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3)
    / 3) + 1 * c10 = (-(2 * d * (d ^ 2 - 3) / 3)) * b ^ 0 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3))
    * (b - ((1 + d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - 0)⁻¹ + (-((d + 1) * (d
    - 1) * (17 * d ^ 2 - 25) / 12)) * ((b - 0) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2
    - 3) / 3)) * ((b - 0) ^ 3)⁻¹ := by
    rw [hc1, hk13, hc2, hk17, hc5, hk37, hc6, hk44, hp49, hp50, hp53, hc10]
    exact ksWY3_kN hd hb
  have kK : c1 * k14 + c2 * k18 + c5 * k38 + c6 * k45 + (2 * p49 + 2 * p50) * ((((1 + d) / 2) ^ 2
    - ((1 - d) / 2) ^ 2) / 2) + (2 * p53) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) = (4 * d
    * (d ^ 2 - 3) / 3) * b ^ 0 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹
    + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3)
    / 3) * (b - 0)⁻¹ + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - 0)⁻¹ := by
    rw [hc1, hk14, hc2, hk18, hc5, hk38, hc6, hk45, hp49, hp50, hp53]
    exact ksWY3_kK hd hb
  have kD : c3 * k20 + c4 * k22 + c3 * k24 + c4 * k26 = (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b
    - ((1 + d) / 2))⁻¹ + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ := by
    rw [hc3, hk20, hc4, hk22, hk24, hk26]
    exact ksWY3_kD hd hb
  have kE : c5 * k39 + c6 * k46 + (1 * p51) * ((((1 + d) / 2) ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (1
    * p54) * ((((1 + d) / 2) ^ 3 - ((1 - d) / 2) ^ 3) / 3) = (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3)
    / 3)) * (b - ((1 - d) / 2))⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d)
    / 2))⁻¹ := by
    rw [hc5, hk39, hc6, hk46, hp51, hp54]
    exact ksWY3_kE hd hb
  simp only [ksWWEIII, hL, hP, hcc, hce, ksWPv, ksWPQ, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  rw [hH1, hH2, hH3, hH4, hH5, hH6, hH7, hH8, hH9, hH10]
  rw [hp0, hp1, hp2]
  simp only [ksWY_sp_sub_w1 hd hb0, ksWY_sm_sub_w1 hd hb0]
  simp only [ksWY_log_w1p hd hm hb0, ksWY_log_w1m hd hp hb0, ksWY_log_ksDA hd hm hp,
    ksWY_log_ksDT hd]
  simp only [ksWYe, ksWPe, ksWYq, ksWPq, ksWY3L, ksWY3P, ksWY3D, ksWY3Q, ksWY3C, ksWY3R, ksWY3S,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWY_log_l3, ksWY_log_l4, ksWY_log_sm hd.2, ksWY_log_sp (by linarith [hd.1] : -1 < d),
    sub_zero, zero_sub, log_neg_eq_log]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination (-1 : ℝ) * (k0 + A * kA + B * kB + M * kM + N * kN + K * kK + D * kD + E * kE)

end QED.ChainProof.SetAKS

end
