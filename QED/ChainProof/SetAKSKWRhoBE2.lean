/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBE2C

/-!
# Set (a), stage D: the `β`-integrand on `(σ₋, σ₊)` as a `ksWYe` combination

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route, range
`β ∈ (σ₋, σ₊)`, part 4 of 4: the last rational identities, then the parts. Each part of
`ksWWEII` (the two longer lists split by `ksWY_ksWPv_split`: `ksWY2_BL*`, `ksWY2_BR*`; the pole
parts `ksWY2_BQ*`, through `ksWY2_Q*`) is a combination of the logarithms with rational
coefficients; summing the parts gives the target combination.
Machine-generated; every coefficient is checked by the proofs.

Main result:

* **`ksWY2_eqOn`**: `ksWYe (ksWY2L δ) ... = ksWWEII · δ` on `(σ₋, σ₊)`.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetAKS

variable {b d : ℝ}

theorem ksWY2_kD_t (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ((4
  / 3) * d * (-(2 * ((1 - d) / 2) ^ 2 * b ^ 2) + 2 * ((1 - d) / 2) * b ^ 2 + b ^ 2 + 2 * b * ((1
  - d) / 2) ^ 2 - 2 * ((1 - d) / 2) * b - b + 10 * ((1 - d) / 2) ^ 4 - 20 * ((1 - d) / 2) ^ 3 + 9
  * ((1 - d) / 2) ^ 2 + ((1 - d) / 2) - 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2))) + ((4 / 3)
  * d * (2 * ((1 - d) / 2) ^ 2 - 2 * ((1 - d) / 2) - 1)) + ((4 / 3) * d * (2 * ((1 - d) / 2) ^ 2
  - 2 * ((1 - d) / 2) - 1)) + ((4 / 3) * d * (-(2 * ((1 - d) / 2) ^ 2 * b ^ 2) + 2 * ((1 - d) / 2)
  * b ^ 2 + b ^ 2 + 2 * b * ((1 - d) / 2) ^ 2 - 2 * ((1 - d) / 2) * b - b + 10 * ((1 - d) / 2) ^ 4
  - 20 * ((1 - d) / 2) ^ 3 + 9 * ((1 - d) / 2) ^ 2 + ((1 - d) / 2) - 2) / ((b - (1 - d) / 2) * (b
  - (1 + d) / 2))) = (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d) / 2))⁻¹ + (-(4 * (d ^ 2
  + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ := by
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
  simp only [e1, e2] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY2_kE_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c48 k54 c49 k58 p72 p75 : ℝ} (hc48 : c48 = 8) (hk54 : k54 = b ^ 2
  / 2) (hc49 : c49 = -8) (hk58 : k58 = b ^ 3
  / 3) (hp72 : p72 = -8) (hp75 : p75 = 8) {r : ℝ} (hr : r = ((-4 / 3) * ((1 - d) / 2) ^ 2 * (2
  * ((1 - d) / 2) - 3))) :
    c48 * k54 + c49 * k58 + (1 * p72) * ((b ^ 2 - ((1 - d) / 2) ^ 2)
  / 2) + (1 * p75) * ((b ^ 3 - ((1 - d) / 2) ^ 3) / 3) = r := by
  subst hr hc48 hk54 hc49 hk58 hp72 hp75
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
  simp only [e1, e2] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY2_kE_100 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c4 k27 c2 k30 k36 k42 p46 : ℝ} (hc4 : c4 = (16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2
  + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk27 : k27 = b ^ 2 / 2) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk30 : k30 = b ^ 3
  / 3) (hk36 : k36 = -((d - 1) ^ 2 / 8)) (hk42 : k42 = (d - 1) ^ 3 / 24) (hp46 : p46 = (16 * b
  - 16)) {r : ℝ} (hr : r = ((4 / 3) * (4 * b ^ 4 + 4 * ((1 - d) / 2) * b ^ 3 - 7 * b ^ 3 + 8 * ((1
  - d) / 2) ^ 2 * b ^ 2 - 11 * ((1 - d) / 2) * b ^ 2 + 7 * b ^ 2 + 10 * b * ((1 - d) / 2) ^ 3 - 23
  * b * ((1 - d) / 2) ^ 2 + 16 * ((1 - d) / 2) * b - 6 * b + 10 * ((1 - d) / 2) ^ 4 - 25 * ((1
  - d) / 2) ^ 3 + 19 * ((1 - d) / 2) ^ 2 - 6 * ((1 - d) / 2)) / ((b - (1 + d) / 2)))) :
    c4
  * k27 + c2 * k30 + c4 * k36 + c2 * k42 + (1 * p46) * ((((1 - d) / 2) ^ 2 - 0 ^ 2) / 2) = r := by
  subst hr hc4 hk27 hc2 hk30 hk36 hk42 hp46
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

theorem ksWY2_kE_t (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ((-4
  / 3) * ((1 - d) / 2) ^ 2 * (2 * ((1 - d) / 2) - 3)) + ((4 / 3) * (4 * b ^ 4 + 4 * ((1 - d) / 2)
  * b ^ 3 - 7 * b ^ 3 + 8 * ((1 - d) / 2) ^ 2 * b ^ 2 - 11 * ((1 - d) / 2) * b ^ 2 + 7 * b ^ 2
  + 10 * b * ((1 - d) / 2) ^ 3 - 23 * b * ((1 - d) / 2) ^ 2 + 16 * ((1 - d) / 2) * b - 6 * b + 10
  * ((1 - d) / 2) ^ 4 - 25 * ((1 - d) / 2) ^ 3 + 19 * ((1 - d) / 2) ^ 2 - 6 * ((1 - d) / 2)) / ((b
  - (1 + d) / 2))) = (-((4 * d ^ 2 + 4) / 3)) * b ^ 0 + ((8 * d ^ 2 + 8) / 3) * b ^ 1 + (-4)
  * b ^ 2 + (16 / 3) * b ^ 3 + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d) / 2))⁻¹ := by
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
  simp only [e1, e2] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY2_B0_0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {rkM rkN rkK rkD rk0 : ℝ} (hrkM : rkM = ((-4 / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 3 - 2
  * ((1 - d) / 2) * b ^ 2 - 9 * b ^ 2 - 6 * b * ((1 - d) / 2) ^ 2 + 8 * ((1 - d) / 2) * b + 3 * b
  + 10 * ((1 - d) / 2) ^ 3 - 19 * ((1 - d) / 2) ^ 2 + 13 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2)
  * (b - (1 + d) / 2)))) (hrkN : rkN = ((4 / 3) * ((1 + d) / 2) ^ 2 * (-(2 * ((1 - d) / 2)
  * b ^ 2) - b ^ 2 + 2 * ((1 - d) / 2) * b + b + 10 * ((1 - d) / 2) ^ 3 - 5 * ((1 - d) / 2) ^ 2
  - ((1 - d) / 2) + 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) (hrkK : rkK = ((-4 / 3) * (-(6
  * ((1 - d) / 2) ^ 2 * b ^ 3) + 12 * ((1 - d) / 2) ^ 2 * b ^ 2 - b ^ 2 + 6 * b * ((1 - d)
  / 2) ^ 4 - 6 * b * ((1 - d) / 2) ^ 3 - 6 * b * ((1 - d) / 2) ^ 2 + b - 6 * ((1 - d) / 2) ^ 4 + 6
  * ((1 - d) / 2) ^ 3 + 5 * ((1 - d) / 2) ^ 2 - 5 * ((1 - d) / 2) + 2) / ((b - (1 - d) / 2) * (b
  - (1 + d) / 2)))) (hrkD : rkD = ((4 / 3) * d * (-(2 * ((1 - d) / 2) ^ 2 * b ^ 2) + 2 * ((1 - d)
  / 2) * b ^ 2 + b ^ 2 + 2 * b * ((1 - d) / 2) ^ 2 - 2 * ((1 - d) / 2) * b - b + 10 * ((1 - d)
  / 2) ^ 4 - 20 * ((1 - d) / 2) ^ 3 + 9 * ((1 - d) / 2) ^ 2 + ((1 - d) / 2) - 2) / ((b - (1 - d)
  / 2) * (b - (1 + d) / 2)))) (hrk0 : rk0 = ((4 / 9) * ((1 - d) / 2) * (9 * ((1 - d) / 2) * b ^ 3
  - 16 * ((1 - d) / 2) ^ 2 * b ^ 2 + 3 * b ^ 2 - 9 * b * ((1 - d) / 2) ^ 3 + 25 * b * ((1 - d)
  / 2) ^ 2 - 9 * ((1 - d) / 2) * b - 3 * b + 80 * ((1 - d) / 2) ^ 4 - 161 * ((1 - d) / 2) ^ 3 + 98
  * ((1 - d) / 2) ^ 2 - 21 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) :
    ksWPv ((ksWW4AL b d).take 5) [] 0 ((1 - d) / 2) =
      log (1 - d) * rkM + log (1
  + d) * rkN + log 2 * rkK + log d * rkD + rk0 := by
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
  obtain ⟨c1, hc1⟩ : ∃ x : ℝ, x = -((16 * b - 16)) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ x : ℝ, x = (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1) := ⟨_, rfl⟩
  obtain ⟨k9, hk9⟩ : ∃ x : ℝ, x = (d - 1) ^ 2 / 8 := ⟨_, rfl⟩
  obtain ⟨k10, hk10⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 / 8) := ⟨_, rfl⟩
  obtain ⟨k11, hk11⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 / 16) := ⟨_, rfl⟩
  obtain ⟨k12, hk12⟩ : ∃ x : ℝ, x = (d - 1) ^ 2 / 8 := ⟨_, rfl⟩
  obtain ⟨k13, hk13⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 / 8) := ⟨_, rfl⟩
  obtain ⟨k14, hk14⟩ : ∃ x : ℝ, x = -(3 * (d - 1) ^ 2 / 16) := ⟨_, rfl⟩
  obtain ⟨k15, hk15⟩ : ∃ x : ℝ, x = -((d - 1) ^ 3 / 24) := ⟨_, rfl⟩
  obtain ⟨k16, hk16⟩ : ∃ x : ℝ, x = (d - 1) ^ 3 / 24 := ⟨_, rfl⟩
  obtain ⟨k17, hk17⟩ : ∃ x : ℝ, x = 11 * (d - 1) ^ 3 / 144 := ⟨_, rfl⟩
  obtain ⟨k18, hk18⟩ : ∃ x : ℝ, x = (d + 1) ^ 2 / 8 := ⟨_, rfl⟩
  obtain ⟨k19, hk19⟩ : ∃ x : ℝ, x = -((d + 1) ^ 2 / 8) := ⟨_, rfl⟩
  obtain ⟨k20, hk20⟩ : ∃ x : ℝ, x = -(d / 2) := ⟨_, rfl⟩
  obtain ⟨k21, hk21⟩ : ∃ x : ℝ, x = (d - 1) * (d + 3) / 16 := ⟨_, rfl⟩
  obtain ⟨k22, hk22⟩ : ∃ x : ℝ, x = (d + 1) ^ 3 / 24 := ⟨_, rfl⟩
  obtain ⟨k23, hk23⟩ : ∃ x : ℝ, x = -((d + 1) ^ 3 / 24) := ⟨_, rfl⟩
  obtain ⟨k24, hk24⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 3) / 12) := ⟨_, rfl⟩
  obtain ⟨k25, hk25⟩ : ∃ x : ℝ, x = (d - 1) * (5 * d ^ 2 + 8 * d + 11) / 144 := ⟨_, rfl⟩
  have hL : ((ksWW4AL b d).take 5) = [(c1, 1, 0), (c2, 1, ((1 - d) / 2)), (c3, 2, ((1 - d)
    / 2)), (c2, 1, ((1 + d) / 2)), (c3, 2, ((1 + d) / 2))] := by
    rw [hc1, hc2, hc3]
    rfl
  have hH1 := ksWY2_H1 hd hb hk9 hk10 hk11
  have hH2 := ksWY2_H2 hd hb hk12 hk13 hk14
  have hH3 := ksWY2_H3 hd hb hk15 hk16 hk17
  have hH4 := ksWY2_H4 hd hb hk18 hk19 hk20 hk21
  have hH5 := ksWY2_H5 hd hb hk22 hk23 hk24 hk25
  have k0_0 := ksWY2_k0_0 hd hb hc1 hk11 hc2 hk14 hc3 hk17 hk21 hk25 hrk0
  have kM_0 := ksWY2_kM_0 hd hb hc1 hk9 hc2 hk12 hc3 hk15 hrkM
  have kN_0 := ksWY2_kN_0 hd hb hc2 hk18 hc3 hk22 hrkN
  have kK_0 := ksWY2_kK_0 hd hb hc1 hk10 hc2 hk13 hc3 hk16 hk19 hk23 hrkK
  have kD_0 := ksWY2_kD_0 hd hb hc2 hk20 hc3 hk24 hrkD
  simp only [ksWPv, hL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hH1, hH2, hH3, hH4, hH5]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination k0_0 + M * kM_0 + N * kN_0 + K * kK_0 + D * kD_0

theorem ksWY2_B0_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {rkA rkB rkM rkN rkK rkE rk0 : ℝ} (hrkA : rkA = ((-4 / 3) * (4 * b ^ 4 + 4 * ((1 - d) / 2)
  * b ^ 3 - 7 * b ^ 3 + 2 * ((1 - d) / 2) ^ 2 * b ^ 2 - 11 * ((1 - d) / 2) * b ^ 2 + 7 * b ^ 2 + 4
  * b * ((1 - d) / 2) ^ 3 - 11 * b * ((1 - d) / 2) ^ 2 + 16 * ((1 - d) / 2) * b - 6 * b + 10 * ((1
  - d) / 2) ^ 4 - 19 * ((1 - d) / 2) ^ 3 + 13 * ((1 - d) / 2) ^ 2 - 6 * ((1 - d) / 2)) / ((b - (1
  + d) / 2)))) (hrkB : rkB = ((4 / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 5 - 8 * ((1 - d) / 2) * b ^ 4
  - 3 * b ^ 4 - 4 * ((1 - d) / 2) ^ 2 * b ^ 3 + 15 * ((1 - d) / 2) * b ^ 3 - 6 * b ^ 3 + 14 * ((1
  - d) / 2) ^ 3 * b ^ 2 - 29 * ((1 - d) / 2) ^ 2 * b ^ 2 + 16 * ((1 - d) / 2) * b ^ 2 - 3 * b ^ 2
  - 10 * b * ((1 - d) / 2) ^ 4 + 31 * b * ((1 - d) / 2) ^ 3 - 36 * b * ((1 - d) / 2) ^ 2 + 21
  * ((1 - d) / 2) * b - 6 * b + 10 * ((1 - d) / 2) ^ 5 - 30 * ((1 - d) / 2) ^ 4 + 34 * ((1 - d)
  / 2) ^ 3 - 18 * ((1 - d) / 2) ^ 2 + 4 * ((1 - d) / 2)) / (b ^ 3 * (b - (1 - d)
  / 2)))) (hrkM : rkM = ((4 / 3) * ((1 - d) / 2) ^ 2 * (-(2 * ((1 - d) / 2) * b ^ 2) + 3 * b ^ 2
  + 2 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 3 - 25 * ((1 - d) / 2) ^ 2 + 19 * ((1
  - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) (hrkN : rkN = ((-4 / 3) * ((1 - d)
  / 2) ^ 2 * (6 * b ^ 6 - 12 * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4 + 18 * ((1 - d) / 2) * b ^ 4
  + 15 * ((1 - d) / 2) ^ 2 * b ^ 3 - 24 * ((1 - d) / 2) * b ^ 3 + 9 * b ^ 3 + 4 * ((1 - d)
  / 2) ^ 4 * b ^ 2 - 12 * ((1 - d) / 2) ^ 3 * b ^ 2 + 9 * ((1 - d) / 2) ^ 2 * b ^ 2 + 2 * ((1 - d)
  / 2) * b ^ 2 - 3 * b ^ 2 + 11 * b * ((1 - d) / 2) ^ 4 - 33 * b * ((1 - d) / 2) ^ 3 + 39 * b
  * ((1 - d) / 2) ^ 2 - 23 * ((1 - d) / 2) * b + 6 * b + 10 * ((1 - d) / 2) ^ 6 - 40 * ((1 - d)
  / 2) ^ 5 + 64 * ((1 - d) / 2) ^ 4 - 52 * ((1 - d) / 2) ^ 3 + 22 * ((1 - d) / 2) ^ 2 - 4 * ((1
  - d) / 2)) / (b ^ 3 * (b - (1 - d) / 2) * (b - (1 + d) / 2)))) (hrkK : rkK = ((4 / 3) * ((1 - d)
  / 2) ^ 2 * (6 * b ^ 6 + 2 * ((1 - d) / 2) * b ^ 5 - 15 * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4
  + 16 * ((1 - d) / 2) * b ^ 4 + 3 * b ^ 4 - 10 * ((1 - d) / 2) ^ 3 * b ^ 3 + 40 * ((1 - d)
  / 2) ^ 2 * b ^ 3 - 43 * ((1 - d) / 2) * b ^ 3 + 15 * b ^ 3 + 4 * ((1 - d) / 2) ^ 4 * b ^ 2 - 12
  * ((1 - d) / 2) ^ 3 * b ^ 2 + 9 * ((1 - d) / 2) ^ 2 * b ^ 2 + 2 * ((1 - d) / 2) * b ^ 2 - 3
  * b ^ 2 + 11 * b * ((1 - d) / 2) ^ 4 - 33 * b * ((1 - d) / 2) ^ 3 + 39 * b * ((1 - d) / 2) ^ 2
  - 23 * ((1 - d) / 2) * b + 6 * b + 10 * ((1 - d) / 2) ^ 6 - 40 * ((1 - d) / 2) ^ 5 + 64 * ((1
  - d) / 2) ^ 4 - 52 * ((1 - d) / 2) ^ 3 + 22 * ((1 - d) / 2) ^ 2 - 4 * ((1 - d) / 2)) / (b ^ 3
  * (b - (1 - d) / 2) * (b - (1 + d) / 2)))) (hrkE : rkE = ((4 / 3) * (4 * b ^ 4 + 4 * ((1 - d)
  / 2) * b ^ 3 - 7 * b ^ 3 + 8 * ((1 - d) / 2) ^ 2 * b ^ 2 - 11 * ((1 - d) / 2) * b ^ 2 + 7
  * b ^ 2 + 10 * b * ((1 - d) / 2) ^ 3 - 23 * b * ((1 - d) / 2) ^ 2 + 16 * ((1 - d) / 2) * b - 6
  * b + 10 * ((1 - d) / 2) ^ 4 - 25 * ((1 - d) / 2) ^ 3 + 19 * ((1 - d) / 2) ^ 2 - 6 * ((1 - d)
  / 2)) / ((b - (1 + d) / 2)))) (hrk0 : rk0 = ((4 / 9) * ((1 - d) / 2) * (-(12 * b ^ 6) + 12 * ((1
  - d) / 2) * b ^ 5 + 21 * b ^ 5 - 26 * ((1 - d) / 2) ^ 2 * b ^ 4 - 21 * b ^ 4 + 18 * ((1 - d)
  / 2) ^ 3 * b ^ 3 - 22 * ((1 - d) / 2) ^ 2 * b ^ 3 + 30 * ((1 - d) / 2) * b ^ 3 + 18 * b ^ 3
  - 104 * ((1 - d) / 2) ^ 4 * b ^ 2 + 200 * ((1 - d) / 2) ^ 3 * b ^ 2 - 59 * ((1 - d) / 2) ^ 2
  * b ^ 2 - 45 * ((1 - d) / 2) * b ^ 2 - 30 * b * ((1 - d) / 2) ^ 5 + 171 * b * ((1 - d) / 2) ^ 4
  - 264 * b * ((1 - d) / 2) ^ 3 + 105 * b * ((1 - d) / 2) ^ 2 + 18 * ((1 - d) / 2) * b + 78 * ((1
  - d) / 2) ^ 6 - 234 * ((1 - d) / 2) ^ 5 + 222 * ((1 - d) / 2) ^ 4 - 54 * ((1 - d) / 2) ^ 3 - 12
  * ((1 - d) / 2) ^ 2) / (b ^ 2 * (b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) :
    ksWPv ((ksWW4AL b d).drop 5) (ksWW4AP b d) 0 ((1 - d) / 2) =
      log (b - (1
  - d) / 2) * rkA + log (b - (1 + d) / 2) * rkB + log (1 - d) * rkM + log (1 + d) * rkN + log 2
  * rkK + log b * rkE + rk0 := by
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
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ x : ℝ, x = (16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d
    * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1) := ⟨_, rfl⟩
  obtain ⟨c5, hc5⟩ : ∃ x : ℝ, x = (16 * ksDT 1 d * b ^ 2 + 16 * ksDT 1 d * b - 48) / (ksDT 1 d ^ 2
    * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨c6, hc6⟩ : ∃ x : ℝ, x = (16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 - 16 * log (ksDT 1 d)
    * ksDT 1 d * b + 16 * log b * ksDT 1 d * b ^ 2 - 16 * log b * ksDT 1 d * b + 24 * ksDT 1 d
    * b ^ 2 - 24 * ksDT 1 d * b + 16 * ksDT 1 d - 40) / (ksDT 1 d * b) := ⟨_, rfl⟩
  obtain ⟨k26, hk26⟩ : ∃ x : ℝ, x = -((2 * b - d + 1) * (2 * b + d - 1) / 8) := ⟨_, rfl⟩
  obtain ⟨k27, hk27⟩ : ∃ x : ℝ, x = b ^ 2 / 2 := ⟨_, rfl⟩
  obtain ⟨k28, hk28⟩ : ∃ x : ℝ, x = (d - 1) * (4 * b - d + 1) / 16 := ⟨_, rfl⟩
  obtain ⟨k29, hk29⟩ : ∃ x : ℝ, x = -((2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2
    * d + 1) / 24) := ⟨_, rfl⟩
  obtain ⟨k30, hk30⟩ : ∃ x : ℝ, x = b ^ 3 / 3 := ⟨_, rfl⟩
  obtain ⟨k31, hk31⟩ : ∃ x : ℝ, x = (d - 1) * (12 * b ^ 2 - 3 * b * d + 3 * b + d ^ 2 - 2 * d + 1)
    / 72 := ⟨_, rfl⟩
  obtain ⟨k32, hk32⟩ : ∃ x : ℝ, x = (d - 1) ^ 2 * (2 * b + d + 1) * (2 * b - d - 1) / (32
    * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨k33, hk33⟩ : ∃ x : ℝ, x = (d - 1) ^ 2 / 8 := ⟨_, rfl⟩
  obtain ⟨k34, hk34⟩ : ∃ x : ℝ, x = (d + 1) ^ 2 * (d - 1) ^ 2 / (32 * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨k35, hk35⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 * (4 * b ^ 2 + d ^ 2 + 2 * d + 1) / (32
    * b ^ 2)) := ⟨_, rfl⟩
  obtain ⟨k36, hk36⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 / 8) := ⟨_, rfl⟩
  obtain ⟨k37, hk37⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 * (b + d + 1) / (16 * b)) := ⟨_, rfl⟩
  obtain ⟨k38, hk38⟩ : ∃ x : ℝ, x = -((d - 1) ^ 3 * (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2
    * b + d ^ 2 + 2 * d + 1) / (192 * b ^ 3)) := ⟨_, rfl⟩
  obtain ⟨k39, hk39⟩ : ∃ x : ℝ, x = -((d - 1) ^ 3 / 24) := ⟨_, rfl⟩
  obtain ⟨k40, hk40⟩ : ∃ x : ℝ, x = -((d + 1) ^ 3 * (d - 1) ^ 3 / (192 * b ^ 3)) := ⟨_, rfl⟩
  obtain ⟨k41, hk41⟩ : ∃ x : ℝ, x = (d - 1) ^ 3 * (2 * b + d + 1) * (4 * b ^ 2 - 2 * b * d - 2 * b
    + d ^ 2 + 2 * d + 1) / (192 * b ^ 3) := ⟨_, rfl⟩
  obtain ⟨k42, hk42⟩ : ∃ x : ℝ, x = (d - 1) ^ 3 / 24 := ⟨_, rfl⟩
  obtain ⟨k43, hk43⟩ : ∃ x : ℝ, x = (d - 1) ^ 3 * (4 * b ^ 2 + 3 * b * d + 3 * b + 3 * d ^ 2 + 6
    * d + 3) / (288 * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨p44, hp44⟩ : ∃ x : ℝ, x = (16 * ksDT 1 d * b ^ 2 + 16 * ksDT 1 d * b - 48)
    / (ksDT 1 d ^ 2 * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨p45, hp45⟩ : ∃ x : ℝ, x = (16 * b - 16) := ⟨_, rfl⟩
  obtain ⟨p46, hp46⟩ : ∃ x : ℝ, x = (16 * b - 16) := ⟨_, rfl⟩
  obtain ⟨p47, hp47⟩ : ∃ x : ℝ, x = (24 * ksDT 1 d * b ^ 2 - 24 * ksDT 1 d * b + 16 * ksDT 1 d
    - 40) / (ksDT 1 d * b) := ⟨_, rfl⟩
  have hL : ((ksWW4AL b d).drop 5) = [(c4, 1, b), (c2, 2, b), (c4, 1, (1 / (b
    * ksDT 1 d))), (c2, 2, (1 / (b * ksDT 1 d)))] := by
    rw [hc4, hc2]
    rfl
  have hP : ksWW4AP b d = [(c5, 0), (c6, 1)] := by
    rw [hc5, hc6]
    rfl
  have hH6 := ksWY2_H6 hd hb hk26 hk27 hk28
  have hH7 := ksWY2_H7 hd hb hk29 hk30 hk31
  have hH8 := ksWY2_H8 hd hb hk32 hk33 hk34 hk35 hk36 hk37
  have hH9 := ksWY2_H9 hd hb hk38 hk39 hk40 hk41 hk42 hk43
  have hp0 : c5 = p44 := by
    rw [hc5, hp44]
  have hp1 := ksWY2_p1 hd hb hc6 hp45 hp46 hp47
  have k0_100 := ksWY2_k0_100 hd hb hc4 hk28 hc2 hk31 hk37 hk43 hp44 hp47 hrk0
  have kA_100 := ksWY2_kA_100 hd hb hc4 hk26 hc2 hk29 hrkA
  have kB_100 := ksWY2_kB_100 hd hb hc4 hk32 hc2 hk38 hrkB
  have kM_100 := ksWY2_kM_100 hd hb hc4 hk33 hc2 hk39 hp45 hrkM
  have kN_100 := ksWY2_kN_100 hd hb hc4 hk34 hc2 hk40 hp45 hrkN
  have kK_100 := ksWY2_kK_100 hd hb hc4 hk35 hc2 hk41 hp45 hrkK
  have kE_100 := ksWY2_kE_100 hd hb hc4 hk27 hc2 hk30 hk36 hk42 hp46 hrkE
  simp only [ksWPv, hL, hP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hH6, hH7, hH8, hH9]
  rw [hp0, hp1]
  try rw [ksWY_log_ksDT hd]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination k0_100 + A * kA_100 + B * kB_100 + M * kM_100 + N * kN_100 + K * kK_100 + E
    * kE_100

theorem ksWY2_Q0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) (c e : ℝ) :
    ksWPQ (1 / (b * ksDT 1 d)) c e ((1 - d) / 2) - ksWPQ (1 / (b
  * ksDT 1 d)) c e 0 =
      c * (log (b - (1 + d) / 2) + log 2 - log (1 + d)) + -(e / ((1 - d)
  / 2 * (b - (1 + d) / 2) / b) - e / -(1 / (b * ksDT 1 d))) := by
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
  simp only [ksWPQ, ksWY_sm_sub_w1 hd hb0, ksWY_log_w1m hd hp hb0, zero_sub, log_neg_eq_log,
    ksWY_log_w1z hd hb0]
  ring

theorem ksWY2_BQ0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {rkB rkN rkK rk0 : ℝ} (hrkB : rkB = (8 * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2
  + 3 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2)) / (b ^ 3))) (hrkN : rkN = ((-8) * ((1 + d)
  / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2 + 3 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2))
  / (b ^ 3))) (hrkK : rkK = (8 * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2 + 3 * b + 7 * ((1
  - d) / 2) ^ 2 - 7 * ((1 - d) / 2)) / (b ^ 3))) (hrk0 : rk0 = (8 * ((1 + d) / 2) ^ 2 * ((1 - d)
  / 2) ^ 2 * (b - (1 - d) / 2) / (b ^ 2))) :
    (ksWPQ (1 / (b
  * ksDT 1 d)) (ksWW4Ac b d) (ksWW4Ae b d) ((1 - d) / 2) - ksWPQ (1 / (b
  * ksDT 1 d)) (ksWW4Ac b d) (ksWW4Ae b d) 0) =
      log (b - (1 + d) / 2) * rkB + log (1 + d)
  * rkN + log 2 * rkK + rk0 := by
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
  obtain ⟨c7, hc7⟩ : ∃ x : ℝ, x = (8 * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56) / (ksDT 1 d ^ 3
    * b ^ 3) := ⟨_, rfl⟩
  obtain ⟨c8, hc8⟩ : ∃ x : ℝ, x = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4
    * b ^ 4)) := ⟨_, rfl⟩
  have hc : ksWW4Ac b d = c7 := by rw [hc7]; rfl
  have he : ksWW4Ae b d = c8 := by rw [hc8]; rfl
  have k0_10 := ksWY2_k0_10 hd hb hc8 hrk0
  have kB_10 := ksWY2_kB_10 hd hb hc7 hrkB
  have kN_10 := ksWY2_kN_10 hd hb hc7 hrkN
  have kK_10 := ksWY2_kK_10 hd hb hc7 hrkK
  rw [hc, he, ksWY2_Q0 hd hb]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination k0_10 + B * kB_10 + N * kN_10 + K * kK_10

theorem ksWY2_B1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {rkA rkB rkM rkN rkK rkD rkE rk0 : ℝ} (hrkA : rkA = ((4 / 3) * (b - (1 - d) / 2) * (8
  * b ^ 2 + 8 * ((1 - d) / 2) * b - 9 * b + 2 * ((1 - d) / 2) ^ 2 - 9 * ((1 - d)
  / 2)))) (hrkB : rkB = ((4 / 3) * (8 * b ^ 3 - 9 * b ^ 2 - 6 * b * ((1 - d) / 2) ^ 2 + 2 * ((1
  - d) / 2) ^ 3 + 3 * ((1 - d) / 2) ^ 2 + 1))) (hrkM : rkM = ((4 / 3) * (-(8 * b ^ 3) + 9 * b ^ 2
  + 6 * b * ((1 - d) / 2) ^ 2 + 4 * ((1 - d) / 2) ^ 3 - 12 * ((1 - d)
  / 2) ^ 2))) (hrkN : rkN = ((-4 / 3) * (b - (1 - d) / 2) * (8 * b ^ 2 + 8 * ((1 - d) / 2) * b - 9
  * b + 2 * ((1 - d) / 2) ^ 2 - 9 * ((1 - d) / 2)))) (hrkK : rkK = ((-4 / 3) * (-(16 * b ^ 3) + 18
  * b ^ 2 + 12 * b * ((1 - d) / 2) ^ 2 + 6 * ((1 - d) / 2) ^ 3 - 21 * ((1 - d)
  / 2) ^ 2))) (hrkD : rkD = ((4 / 3) * d * (2 * ((1 - d) / 2) ^ 2 - 2 * ((1 - d) / 2)
  - 1))) (hrkE : rkE = ((-4 / 3) * ((1 - d) / 2) ^ 2 * (2 * ((1 - d) / 2)
  - 3))) (hrk0 : rk0 = ((-4 / 9) * (b - (1 - d) / 2) * (-(22 * b ^ 3) - 22 * ((1 - d) / 2) * b ^ 2
  + 21 * b ^ 2 + 17 * b * ((1 - d) / 2) ^ 2 + 9 * ((1 - d) / 2) * b - 21 * b - 18 * ((1 - d) / 2))
  / (b))) :
    ksWPv (ksWW2AL b d) (ksWW2AP b d) ((1 - d) / 2) b =
      log (b - (1 - d) / 2)
  * rkA + log (b - (1 + d) / 2) * rkB + log (1 - d) * rkM + log (1 + d) * rkN + log 2 * rkK
  + log d * rkD + log b * rkE + rk0 := by
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
  obtain ⟨c48, hc48⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨c49, hc49⟩ : ∃ x : ℝ, x = -8 := ⟨_, rfl⟩
  obtain ⟨c50, hc50⟩ : ∃ x : ℝ, x = (16 * log (ksDA 1 (-ksDT 1 d) b) * b ^ 2 - 16
    * log (ksDA 1 (-ksDT 1 d) b) * b - 8 * log (ksDT 1 d) * b - 8 * log b * b + 24 * b ^ 2 - 20
    * b + 16) / b := ⟨_, rfl⟩
  obtain ⟨c51, hc51⟩ : ∃ x : ℝ, x = (8 * log (ksDT 1 d) + 8 * log b - 4) := ⟨_, rfl⟩
  obtain ⟨k52, hk52⟩ : ∃ x : ℝ, x = -((d - 1) ^ 2 / 8) := ⟨_, rfl⟩
  obtain ⟨k53, hk53⟩ : ∃ x : ℝ, x = (d - 1) ^ 2 / 8 := ⟨_, rfl⟩
  obtain ⟨k54, hk54⟩ : ∃ x : ℝ, x = b ^ 2 / 2 := ⟨_, rfl⟩
  obtain ⟨k55, hk55⟩ : ∃ x : ℝ, x = -((2 * b - d + 1) * (2 * b + d - 1) / 16) := ⟨_, rfl⟩
  obtain ⟨k56, hk56⟩ : ∃ x : ℝ, x = (d - 1) ^ 3 / 24 := ⟨_, rfl⟩
  obtain ⟨k57, hk57⟩ : ∃ x : ℝ, x = -((d - 1) ^ 3 / 24) := ⟨_, rfl⟩
  obtain ⟨k58, hk58⟩ : ∃ x : ℝ, x = b ^ 3 / 3 := ⟨_, rfl⟩
  obtain ⟨k59, hk59⟩ : ∃ x : ℝ, x = -((2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2
    * d + 1) / 72) := ⟨_, rfl⟩
  obtain ⟨k60, hk60⟩ : ∃ x : ℝ, x = (2 * b - d + 1) * (2 * b + d - 1) / 8 := ⟨_, rfl⟩
  obtain ⟨k61, hk61⟩ : ∃ x : ℝ, x = -((2 * b + d - 1) * (2 * b - 3 * d + 3) / 16) := ⟨_, rfl⟩
  obtain ⟨k62, hk62⟩ : ∃ x : ℝ, x = (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2
    * d + 1) / 24 := ⟨_, rfl⟩
  obtain ⟨k63, hk63⟩ : ∃ x : ℝ, x = -((2 * b + d - 1) * (8 * b ^ 2 - 10 * b * d + 10 * b + 11
    * d ^ 2 - 22 * d + 11) / 144) := ⟨_, rfl⟩
  obtain ⟨k64, hk64⟩ : ∃ x : ℝ, x = (2 * b + d + 1) * (2 * b - d - 1) / 8 := ⟨_, rfl⟩
  obtain ⟨k65, hk65⟩ : ∃ x : ℝ, x = d / 2 := ⟨_, rfl⟩
  obtain ⟨k66, hk66⟩ : ∃ x : ℝ, x = -((2 * b + d - 1) * (2 * b + d + 3) / 16) := ⟨_, rfl⟩
  obtain ⟨k67, hk67⟩ : ∃ x : ℝ, x = (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2
    * d + 1) / 24 := ⟨_, rfl⟩
  obtain ⟨k68, hk68⟩ : ∃ x : ℝ, x = d * (d ^ 2 + 3) / 12 := ⟨_, rfl⟩
  obtain ⟨k69, hk69⟩ : ∃ x : ℝ, x = -((2 * b + d - 1) * (8 * b ^ 2 + 2 * b * d + 10 * b + 5
    * d ^ 2 + 8 * d + 11) / 144) := ⟨_, rfl⟩
  obtain ⟨p70, hp70⟩ : ∃ x : ℝ, x = (16 * b - 16) := ⟨_, rfl⟩
  obtain ⟨p71, hp71⟩ : ∃ x : ℝ, x = -8 := ⟨_, rfl⟩
  obtain ⟨p72, hp72⟩ : ∃ x : ℝ, x = -8 := ⟨_, rfl⟩
  obtain ⟨p73, hp73⟩ : ∃ x : ℝ, x = (24 * b ^ 2 - 20 * b + 16) / b := ⟨_, rfl⟩
  obtain ⟨p74, hp74⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨p75, hp75⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨p76, hp76⟩ : ∃ x : ℝ, x = -4 := ⟨_, rfl⟩
  have hL : ksWW2AL b d = [(c48, 1, 0), (c49, 2, 0), (c49, 1, ((1 - d) / 2)), (c48, 2, ((1 - d)
    / 2)), (c49, 1, ((1 + d) / 2)), (c48, 2, ((1 + d) / 2))] := by
    rw [hc48, hc49]
    rfl
  have hP : ksWW2AP b d = [(c50, 1), (c51, 2)] := by
    rw [hc50, hc51]
    rfl
  have hH10 := ksWY2_H10 hd hb hk52 hk53 hk54 hk55
  have hH11 := ksWY2_H11 hd hb hk56 hk57 hk58 hk59
  have hH12 := ksWY2_H12 hd hb hk60 hk61
  have hH13 := ksWY2_H13 hd hb hk62 hk63
  have hH14 := ksWY2_H14 hd hb hk64 hk65 hk66
  have hH15 := ksWY2_H15 hd hb hk67 hk68 hk69
  have hp2 := ksWY2_p2 hd hb hc50 hp70 hp71 hp72 hp73
  have hp3 := ksWY2_p3 hd hb hc51 hp74 hp75 hp76
  have k0_1 := ksWY2_k0_1 hd hb hc48 hk55 hc49 hk59 hk61 hk63 hk66 hk69 hp73 hp76 hrk0
  have kA_1 := ksWY2_kA_1 hd hb hc49 hk60 hc48 hk62 hp70 hrkA
  have kB_1 := ksWY2_kB_1 hd hb hc49 hk64 hc48 hk67 hp70 hrkB
  have kM_1 := ksWY2_kM_1 hd hb hc48 hk52 hc49 hk56 hp70 hp71 hp74 hrkM
  have kN_1 := ksWY2_kN_1 hd hb hp70 hp71 hp74 hrkN
  have kK_1 := ksWY2_kK_1 hd hb hc48 hk53 hc49 hk57 hp70 hp71 hp74 hrkK
  have kD_1 := ksWY2_kD_1 hd hb hc49 hk65 hc48 hk68 hrkD
  have kE_1 := ksWY2_kE_1 hd hb hc48 hk54 hc49 hk58 hp72 hp75 hrkE
  simp only [ksWPv, hL, hP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hH10, hH11, hH12, hH13, hH14, hH15]
  rw [hp2, hp3]
  try rw [ksWY_log_ksDA hd hm hp]
  try rw [ksWY_log_ksDT hd]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination k0_1 + A * kA_1 + B * kB_1 + M * kM_1 + N * kN_1 + K * kK_1 + D * kD_1 + E
    * kE_1

theorem ksWY2_B2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {rkA rkB rkC rkM rkN rkK rkD rk0 : ℝ} (hrkA : rkA = ((4 / 3) * (-(8 * b ^ 3) + 15 * b ^ 2
  + 6 * b * ((1 - d) / 2) ^ 2 - 6 * b + 2 * ((1 - d) / 2) ^ 3 - 3 * ((1 - d)
  / 2) ^ 2))) (hrkB : rkB = ((-4 / 3) * (b - (1 + d) / 2) * (8 * b ^ 2 - 8 * ((1 - d) / 2) * b - 7
  * b + 2 * ((1 - d) / 2) ^ 2 - ((1 - d) / 2) - 1))) (hrkC : rkC = ((-4 / 3) * ((1 - d) / 2) ^ 2
  * (2 * ((1 - d) / 2) - 3))) (hrkM : rkM = ((4 / 3) * (8 * b ^ 3 - 15 * b ^ 2 - 6 * b * ((1 - d)
  / 2) ^ 2 + 6 * b + 4 * ((1 - d) / 2) ^ 3 - 6 * ((1 - d) / 2) ^ 2 + 1))) (hrkN : rkN = ((4 / 3)
  * (b - (1 + d) / 2) * (8 * b ^ 2 - 8 * ((1 - d) / 2) * b - 7 * b + 2 * ((1 - d) / 2) ^ 2 - ((1
  - d) / 2) - 1))) (hrkK : rkK = ((-4 / 3) * (16 * b ^ 3 - 30 * b ^ 2 - 12 * b * ((1 - d) / 2) ^ 2
  + 12 * b + 6 * ((1 - d) / 2) ^ 3 - 9 * ((1 - d) / 2) ^ 2 + 2))) (hrkD : rkD = ((4 / 3) * d * (2
  * ((1 - d) / 2) ^ 2 - 2 * ((1 - d) / 2) - 1))) (hrk0 : rk0 = ((4 / 9) * (b - (1 + d) / 2)
  * (-(22 * b ^ 3) + 22 * ((1 - d) / 2) * b ^ 2 + 45 * b ^ 2 + 17 * b * ((1 - d) / 2) ^ 2 - 35
  * ((1 - d) / 2) * b - 45 * b - 17 * ((1 - d) / 2) ^ 2 + 31 * ((1 - d) / 2) + 22) / ((b
  - 1)))) :
    ksWPv (ksWW2BL b d) (ksWW2BP b d) b ((1 + d) / 2) =
      log (b - (1 - d) / 2)
  * rkA + log (b - (1 + d) / 2) * rkB + log (1 - b) * rkC + log (1 - d) * rkM + log (1 + d) * rkN
  + log 2 * rkK + log d * rkD + rk0 := by
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
  obtain ⟨c48, hc48⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨c49, hc49⟩ : ∃ x : ℝ, x = -8 := ⟨_, rfl⟩
  obtain ⟨c77, hc77⟩ : ∃ x : ℝ, x = -((16 * log (ksDA 1 (-ksDT 1 d) b) * b ^ 2 - 16
    * log (ksDA 1 (-ksDT 1 d) b) * b + 24 * b ^ 2 - 24 * b + 16) / (b - 1)) := ⟨_, rfl⟩
  obtain ⟨c78, hc78⟩ : ∃ x : ℝ, x = (-(8 * log (1 - b) * b) + 8 * log (1 - b) + 16
    * log (ksDA 1 (-ksDT 1 d) b) * b ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b) * b - 8
    * log (ksDT 1 d) * b + 8 * log (ksDT 1 d) + 24 * b ^ 2 - 20 * b + 12) / (b - 1) := ⟨_, rfl⟩
  obtain ⟨c79, hc79⟩ : ∃ x : ℝ, x = (8 * log (1 - b) + 8 * log (ksDT 1 d) - 4) := ⟨_, rfl⟩
  obtain ⟨k80, hk80⟩ : ∃ x : ℝ, x = -((b + 1) * (b - 1) / 2) := ⟨_, rfl⟩
  obtain ⟨k81, hk81⟩ : ∃ x : ℝ, x = (d - 1) * (d + 3) / 8 := ⟨_, rfl⟩
  obtain ⟨k82, hk82⟩ : ∃ x : ℝ, x = -((d - 1) * (d + 3) / 8) := ⟨_, rfl⟩
  obtain ⟨k83, hk83⟩ : ∃ x : ℝ, x = (2 * b - d - 1) * (2 * b + d + 5) / 16 := ⟨_, rfl⟩
  obtain ⟨k84, hk84⟩ : ∃ x : ℝ, x = -((b - 1) * (b ^ 2 + b + 1) / 3) := ⟨_, rfl⟩
  obtain ⟨k85, hk85⟩ : ∃ x : ℝ, x = (d - 1) * (d ^ 2 + 4 * d + 7) / 24 := ⟨_, rfl⟩
  obtain ⟨k86, hk86⟩ : ∃ x : ℝ, x = -((d - 1) * (d ^ 2 + 4 * d + 7) / 24) := ⟨_, rfl⟩
  obtain ⟨k87, hk87⟩ : ∃ x : ℝ, x = (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 8 * b + d ^ 2 + 5
    * d + 16) / 72 := ⟨_, rfl⟩
  obtain ⟨k88, hk88⟩ : ∃ x : ℝ, x = -((2 * b - d + 1) * (2 * b + d - 1) / 8) := ⟨_, rfl⟩
  obtain ⟨k89, hk89⟩ : ∃ x : ℝ, x = d / 2 := ⟨_, rfl⟩
  obtain ⟨k90, hk90⟩ : ∃ x : ℝ, x = (2 * b - d - 1) * (2 * b - d + 3) / 16 := ⟨_, rfl⟩
  obtain ⟨k91, hk91⟩ : ∃ x : ℝ, x = -((2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2
    * d + 1) / 24) := ⟨_, rfl⟩
  obtain ⟨k92, hk92⟩ : ∃ x : ℝ, x = d * (d ^ 2 + 3) / 12 := ⟨_, rfl⟩
  obtain ⟨k93, hk93⟩ : ∃ x : ℝ, x = (2 * b - d - 1) * (8 * b ^ 2 - 2 * b * d + 10 * b + 5 * d ^ 2
    - 8 * d + 11) / 144 := ⟨_, rfl⟩
  obtain ⟨k94, hk94⟩ : ∃ x : ℝ, x = -((2 * b + d + 1) * (2 * b - d - 1) / 8) := ⟨_, rfl⟩
  obtain ⟨k95, hk95⟩ : ∃ x : ℝ, x = (2 * b - d - 1) * (2 * b + 3 * d + 3) / 16 := ⟨_, rfl⟩
  obtain ⟨k96, hk96⟩ : ∃ x : ℝ, x = -((2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2
    * d + 1) / 24) := ⟨_, rfl⟩
  obtain ⟨k97, hk97⟩ : ∃ x : ℝ, x = (2 * b - d - 1) * (8 * b ^ 2 + 10 * b * d + 10 * b + 11
    * d ^ 2 + 22 * d + 11) / 144 := ⟨_, rfl⟩
  obtain ⟨p98, hp98⟩ : ∃ x : ℝ, x = -(16 * b) := ⟨_, rfl⟩
  obtain ⟨p99, hp99⟩ : ∃ x : ℝ, x = -((24 * b ^ 2 - 24 * b + 16) / (b - 1)) := ⟨_, rfl⟩
  obtain ⟨p100, hp100⟩ : ∃ x : ℝ, x = -8 := ⟨_, rfl⟩
  obtain ⟨p101, hp101⟩ : ∃ x : ℝ, x = 16 * b := ⟨_, rfl⟩
  obtain ⟨p102, hp102⟩ : ∃ x : ℝ, x = -8 := ⟨_, rfl⟩
  obtain ⟨p103, hp103⟩ : ∃ x : ℝ, x = (24 * b ^ 2 - 20 * b + 12) / (b - 1) := ⟨_, rfl⟩
  obtain ⟨p104, hp104⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨p105, hp105⟩ : ∃ x : ℝ, x = 8 := ⟨_, rfl⟩
  obtain ⟨p106, hp106⟩ : ∃ x : ℝ, x = -4 := ⟨_, rfl⟩
  have hL : ksWW2BL b d = [(c48, 1, 1), (c49, 2, 1), (c49, 1, ((1 - d) / 2)), (c48, 2, ((1 - d)
    / 2)), (c49, 1, ((1 + d) / 2)), (c48, 2, ((1 + d) / 2))] := by
    rw [hc48, hc49]
    rfl
  have hP : ksWW2BP b d = [(c77, 0), (c78, 1), (c79, 2)] := by
    rw [hc77, hc78, hc79]
    rfl
  have hH16 := ksWY2_H16 hd hb hk80 hk81 hk82 hk83
  have hH17 := ksWY2_H17 hd hb hk84 hk85 hk86 hk87
  have hH18 := ksWY2_H18 hd hb hk88 hk89 hk90
  have hH19 := ksWY2_H19 hd hb hk91 hk92 hk93
  have hH20 := ksWY2_H20 hd hb hk94 hk95
  have hH21 := ksWY2_H21 hd hb hk96 hk97
  have hp4 := ksWY2_p4 hd hb hc77 hp98 hp99
  have hp5 := ksWY2_p5 hd hb hc78 hp100 hp101 hp102 hp103
  have hp6 := ksWY2_p6 hd hb hc79 hp104 hp105 hp106
  have k0_2 := ksWY2_k0_2 hd hb hc48 hk83 hc49 hk87 hk90 hk93 hk95 hk97 hp99 hp103 hp106 hrk0
  have kA_2 := ksWY2_kA_2 hd hb hc49 hk88 hc48 hk91 hp98 hp101 hrkA
  have kB_2 := ksWY2_kB_2 hd hb hc49 hk94 hc48 hk96 hp98 hp101 hrkB
  have kC_2 := ksWY2_kC_2 hd hb hc48 hk80 hc49 hk84 hp100 hp104 hrkC
  have kM_2 := ksWY2_kM_2 hd hb hc48 hk81 hc49 hk85 hp98 hp101 hp102 hp105 hrkM
  have kN_2 := ksWY2_kN_2 hd hb hp98 hp101 hp102 hp105 hrkN
  have kK_2 := ksWY2_kK_2 hd hb hc48 hk82 hc49 hk86 hp98 hp101 hp102 hp105 hrkK
  have kD_2 := ksWY2_kD_2 hd hb hc49 hk89 hc48 hk92 hrkD
  simp only [ksWPv, hL, hP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hH16, hH17, hH18, hH19, hH20, hH21]
  rw [hp4, hp5, hp6]
  try rw [ksWY_log_ksDA hd hm hp]
  try rw [ksWY_log_ksDT hd]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination k0_2 + A * kA_2 + B * kB_2 + C * kC_2 + M * kM_2 + N * kN_2 + K * kK_2 + D
    * kD_2

theorem ksWY2_B3_0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {rkM rkN rkK rkD rk0 : ℝ} (hrkM : rkM = ((-4 / 3) * ((1 - d) / 2) ^ 2 * (-(6 * b ^ 3) - 2
  * ((1 - d) / 2) * b ^ 2 + 9 * b ^ 2 + 6 * b * ((1 - d) / 2) ^ 2 - 4 * ((1 - d) / 2) * b - 3 * b
  + 10 * ((1 - d) / 2) ^ 3 - 25 * ((1 - d) / 2) ^ 2 + 19 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2)
  * (b - (1 + d) / 2)))) (hrkN : rkN = ((4 / 3) * ((1 + d) / 2) ^ 2 * (-(2 * ((1 - d) / 2)
  * b ^ 2) - b ^ 2 + 2 * ((1 - d) / 2) * b + b + 10 * ((1 - d) / 2) ^ 3 - 5 * ((1 - d) / 2) ^ 2
  - ((1 - d) / 2) + 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) (hrkK : rkK = ((4 / 3) * (-(6
  * ((1 - d) / 2) ^ 2 * b ^ 3) + 6 * ((1 - d) / 2) ^ 2 * b ^ 2 + b ^ 2 + 6 * b * ((1 - d) / 2) ^ 4
  - 6 * b * ((1 - d) / 2) ^ 3 - b - 5 * ((1 - d) / 2) ^ 2 + 5 * ((1 - d) / 2) - 2) / ((b - (1 - d)
  / 2) * (b - (1 + d) / 2)))) (hrkD : rkD = ((4 / 3) * d * (-(2 * ((1 - d) / 2) ^ 2 * b ^ 2) + 2
  * ((1 - d) / 2) * b ^ 2 + b ^ 2 + 2 * b * ((1 - d) / 2) ^ 2 - 2 * ((1 - d) / 2) * b - b + 10
  * ((1 - d) / 2) ^ 4 - 20 * ((1 - d) / 2) ^ 3 + 9 * ((1 - d) / 2) ^ 2 + ((1 - d) / 2) - 2) / ((b
  - (1 - d) / 2) * (b - (1 + d) / 2)))) (hrk0 : rk0 = ((4 / 9) * ((1 - d) / 2) * (-(9 * ((1 - d)
  / 2) * b ^ 3) - 16 * ((1 - d) / 2) ^ 2 * b ^ 2 + 27 * ((1 - d) / 2) * b ^ 2 + 3 * b ^ 2 + 9 * b
  * ((1 - d) / 2) ^ 3 + 7 * b * ((1 - d) / 2) ^ 2 - 18 * ((1 - d) / 2) * b - 3 * b + 80 * ((1 - d)
  / 2) ^ 4 - 170 * ((1 - d) / 2) ^ 3 + 107 * ((1 - d) / 2) ^ 2 - 21 * ((1 - d) / 2) - 6) / ((b
  - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    ksWPv ((ksWW4BL b d).take 6) [] ((1 + d)
  / 2) 1 =
      log (1 - d) * rkM + log (1 + d) * rkN + log 2 * rkK + log d * rkD + rk0 := by
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
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ x : ℝ, x = (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1) := ⟨_, rfl⟩
  obtain ⟨c107, hc107⟩ : ∃ x : ℝ, x = 16 * b := ⟨_, rfl⟩
  obtain ⟨c108, hc108⟩ : ∃ x : ℝ, x = -(16 * b) := ⟨_, rfl⟩
  obtain ⟨k114, hk114⟩ : ∃ x : ℝ, x = -((d - 1) / 2) := ⟨_, rfl⟩
  obtain ⟨k115, hk115⟩ : ∃ x : ℝ, x = (d - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨k116, hk116⟩ : ∃ x : ℝ, x = (d - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨k117, hk117⟩ : ∃ x : ℝ, x = -((d - 1) * (d + 3) / 8) := ⟨_, rfl⟩
  obtain ⟨k118, hk118⟩ : ∃ x : ℝ, x = (d - 1) * (d + 3) / 8 := ⟨_, rfl⟩
  obtain ⟨k119, hk119⟩ : ∃ x : ℝ, x = (d - 1) * (d + 7) / 16 := ⟨_, rfl⟩
  obtain ⟨k120, hk120⟩ : ∃ x : ℝ, x = -((d + 1) * (d - 3) / 8) := ⟨_, rfl⟩
  obtain ⟨k121, hk121⟩ : ∃ x : ℝ, x = (d + 1) * (d - 3) / 8 := ⟨_, rfl⟩
  obtain ⟨k122, hk122⟩ : ∃ x : ℝ, x = -(d / 2) := ⟨_, rfl⟩
  obtain ⟨k123, hk123⟩ : ∃ x : ℝ, x = -((d - 1) * (d - 5) / 16) := ⟨_, rfl⟩
  obtain ⟨k124, hk124⟩ : ∃ x : ℝ, x = (d + 1) * (d ^ 2 - 4 * d + 7) / 24 := ⟨_, rfl⟩
  obtain ⟨k125, hk125⟩ : ∃ x : ℝ, x = -((d + 1) * (d ^ 2 - 4 * d + 7) / 24) := ⟨_, rfl⟩
  obtain ⟨k126, hk126⟩ : ∃ x : ℝ, x = -(d * (d ^ 2 + 3) / 12) := ⟨_, rfl⟩
  obtain ⟨k127, hk127⟩ : ∃ x : ℝ, x = (d - 1) * (5 * d ^ 2 - 10 * d + 29) / 144 := ⟨_, rfl⟩
  obtain ⟨k128, hk128⟩ : ∃ x : ℝ, x = -((d - 1) * (d + 3) / 8) := ⟨_, rfl⟩
  obtain ⟨k129, hk129⟩ : ∃ x : ℝ, x = (d - 1) * (d + 3) / 8 := ⟨_, rfl⟩
  obtain ⟨k130, hk130⟩ : ∃ x : ℝ, x = (d - 1) * (3 * d + 5) / 16 := ⟨_, rfl⟩
  obtain ⟨k131, hk131⟩ : ∃ x : ℝ, x = -((d - 1) * (d ^ 2 + 4 * d + 7) / 24) := ⟨_, rfl⟩
  obtain ⟨k132, hk132⟩ : ∃ x : ℝ, x = (d - 1) * (d ^ 2 + 4 * d + 7) / 24 := ⟨_, rfl⟩
  obtain ⟨k133, hk133⟩ : ∃ x : ℝ, x = (d - 1) * (11 * d ^ 2 + 32 * d + 29) / 144 := ⟨_, rfl⟩
  have hL : ((ksWW4BL b d).take 6) = [(c107, 0, 1), (c108, 1, 1), (c2, 1, ((1 - d)
    / 2)), (c3, 2, ((1 - d) / 2)), (c2, 1, ((1 + d) / 2)), (c3, 2, ((1 + d) / 2))] := by
    rw [hc107, hc108, hc2, hc3]
    rfl
  have hH22 := ksWY2_H22 hd hb hk114 hk115 hk116
  have hH23 := ksWY2_H23 hd hb hk117 hk118 hk119
  have hH24 := ksWY2_H24 hd hb hk120 hk121 hk122 hk123
  have hH25 := ksWY2_H25 hd hb hk124 hk125 hk126 hk127
  have hH26 := ksWY2_H26 hd hb hk128 hk129 hk130
  have hH27 := ksWY2_H27 hd hb hk131 hk132 hk133
  have k0_3 := ksWY2_k0_3 hd hb hc107 hk116 hc108 hk119 hc2 hk123 hc3 hk127 hk130 hk133 hrk0
  have kM_3 := ksWY2_kM_3 hd hb hc107 hk114 hc108 hk117 hc2 hk128 hc3 hk131 hrkM
  have kN_3 := ksWY2_kN_3 hd hb hc2 hk120 hc3 hk124 hrkN
  have kK_3 := ksWY2_kK_3 hd hb hc107 hk115 hc108 hk118 hc2 hk121 hc3 hk125 hk129 hk132 hrkK
  have kD_3 := ksWY2_kD_3 hd hb hc2 hk122 hc3 hk126 hrkD
  simp only [ksWPv, hL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hH22, hH23, hH24, hH25, hH26, hH27]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination k0_3 + M * kM_3 + N * kN_3 + K * kK_3 + D * kD_3

theorem ksWY2_B3_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {rkB rkC rk0 : ℝ} (hrkB : rkB = ((4 / 3) * (4 * b ^ 4 - 4 * ((1 - d) / 2) * b ^ 3 - 9
  * b ^ 3 + 2 * ((1 - d) / 2) ^ 2 * b ^ 2 + ((1 - d) / 2) * b ^ 2 + 10 * b ^ 2 - 4 * b * ((1 - d)
  / 2) ^ 3 + 7 * b * ((1 - d) / 2) ^ 2 - 6 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 4
  - 15 * ((1 - d) / 2) ^ 3 + 4 * ((1 - d) / 2) ^ 2 + 3 * ((1 - d) / 2) - 2) / ((b - (1 - d)
  / 2)))) (hrkC : rkC = ((-4 / 3) * (b - 1) ^ 2 * (4 * b ^ 3 - 5 * b ^ 2 + 4 * b * ((1 - d)
  / 2) ^ 2 - 4 * ((1 - d) / 2) * b + 5 * b + 5 * ((1 - d) / 2) ^ 2 - 5 * ((1 - d) / 2) + 2) / ((b
  - (1 - d) / 2) * (b - (1 + d) / 2)))) (hrk0 : rk0 = ((-2 / 9) * ((1 - d) / 2) * (24 * b ^ 4 - 12
  * ((1 - d) / 2) * b ^ 3 - 54 * b ^ 3 + 20 * ((1 - d) / 2) ^ 2 * b ^ 2 - 9 * ((1 - d) / 2)
  * b ^ 2 + 60 * b ^ 2 - 12 * b * ((1 - d) / 2) ^ 3 + 22 * b * ((1 - d) / 2) ^ 2 - 21 * ((1 - d)
  / 2) * b - 18 * b + 20 * ((1 - d) / 2) ^ 4 - 35 * ((1 - d) / 2) ^ 3 - 7 * ((1 - d) / 2) ^ 2 + 24
  * ((1 - d) / 2) - 12) / ((b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) :
    ksWPv (((ksWW4BL b d).drop 6).take 3) [] ((1 + d) / 2) 1 =
      log (b - (1 + d)
  / 2) * rkB + log (1 - b) * rkC + rk0 := by
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
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) := ⟨_, rfl⟩
  obtain ⟨c108, hc108⟩ : ∃ x : ℝ, x = -(16 * b) := ⟨_, rfl⟩
  obtain ⟨c109, hc109⟩ : ∃ x : ℝ, x = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d
    * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1) := ⟨_, rfl⟩
  obtain ⟨k134, hk134⟩ : ∃ x : ℝ, x = (2 * b - d - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨k135, hk135⟩ : ∃ x : ℝ, x = 1 - b := ⟨_, rfl⟩
  obtain ⟨k136, hk136⟩ : ∃ x : ℝ, x = (d - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨k137, hk137⟩ : ∃ x : ℝ, x = (2 * b + d + 1) * (2 * b - d - 1) / 8 := ⟨_, rfl⟩
  obtain ⟨k138, hk138⟩ : ∃ x : ℝ, x = -((b + 1) * (b - 1) / 2) := ⟨_, rfl⟩
  obtain ⟨k139, hk139⟩ : ∃ x : ℝ, x = (d - 1) * (4 * b + d + 3) / 16 := ⟨_, rfl⟩
  obtain ⟨k140, hk140⟩ : ∃ x : ℝ, x = (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2
    * d + 1) / 24 := ⟨_, rfl⟩
  obtain ⟨k141, hk141⟩ : ∃ x : ℝ, x = -((b - 1) * (b ^ 2 + b + 1) / 3) := ⟨_, rfl⟩
  obtain ⟨k142, hk142⟩ : ∃ x : ℝ, x = (d - 1) * (12 * b ^ 2 + 3 * b * d + 9 * b + d ^ 2 + 4 * d
    + 7) / 72 := ⟨_, rfl⟩
  have hL : (((ksWW4BL b d).drop 6).take 3) = [(c108, 0, b), (c109, 1, b), (c2, 2, b)] := by
    rw [hc108, hc109, hc2]
    rfl
  have hH28 := ksWY2_H28 hd hb hk134 hk135 hk136
  have hH29 := ksWY2_H29 hd hb hk137 hk138 hk139
  have hH30 := ksWY2_H30 hd hb hk140 hk141 hk142
  have k0_103 := ksWY2_k0_103 hd hb hc108 hk136 hc109 hk139 hc2 hk142 hrk0
  have kB_103 := ksWY2_kB_103 hd hb hc108 hk134 hc109 hk137 hc2 hk140 hrkB
  have kC_103 := ksWY2_kC_103 hd hb hc108 hk135 hc109 hk138 hc2 hk141 hrkC
  simp only [ksWPv, hL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hH28, hH29, hH30]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination k0_103 + B * kB_103 + C * kC_103

theorem ksWY2_B3_2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {rkA rkC rkM rkN rkK rk0 : ℝ} (hrkA : rkA = ((4 / 3) * ((1 - d) / 2) ^ 2 * (-(6 * b ^ 5)
  - 8 * ((1 - d) / 2) * b ^ 4 + 27 * b ^ 4 + 4 * ((1 - d) / 2) ^ 2 * b ^ 3 + 17 * ((1 - d) / 2)
  * b ^ 3 - 42 * b ^ 3 + 14 * ((1 - d) / 2) ^ 3 * b ^ 2 - 41 * ((1 - d) / 2) ^ 2 * b ^ 2 + 13
  * ((1 - d) / 2) * b ^ 2 + 21 * b ^ 2 + 10 * b * ((1 - d) / 2) ^ 4 - 59 * b * ((1 - d) / 2) ^ 3
  + 106 * b * ((1 - d) / 2) ^ 2 - 66 * ((1 - d) / 2) * b + 12 * b + 10 * ((1 - d) / 2) ^ 5 - 40
  * ((1 - d) / 2) ^ 4 + 79 * ((1 - d) / 2) ^ 3 - 87 * ((1 - d) / 2) ^ 2 + 48 * ((1 - d) / 2) - 12)
  / ((b - 1) ^ 3 * (b - (1 + d) / 2)))) (hrkC : rkC = ((-4 / 3) * ((1 - d) / 2) ^ 2 * (-(2 * ((1
  - d) / 2) * b ^ 2) + 3 * b ^ 2 + 2 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 3 - 25
  * ((1 - d) / 2) ^ 2 + 19 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) (hrkM : rkM = ((4 / 3) * ((1 - d) / 2) ^ 2 * (-(2 * ((1 - d) / 2) * b ^ 2) + 3 * b ^ 2
  + 2 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 3 - 25 * ((1 - d) / 2) ^ 2 + 19 * ((1
  - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) (hrkN : rkN = ((4 / 3) * ((1 - d)
  / 2) ^ 2 * (6 * b ^ 6 - 24 * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4 + 18 * ((1 - d) / 2) * b ^ 4
  + 30 * b ^ 4 + 33 * ((1 - d) / 2) ^ 2 * b ^ 3 - 48 * ((1 - d) / 2) * b ^ 3 - 9 * b ^ 3 + 4 * ((1
  - d) / 2) ^ 4 * b ^ 2 - 12 * ((1 - d) / 2) ^ 3 * b ^ 2 - 18 * ((1 - d) / 2) ^ 2 * b ^ 2 + 38
  * ((1 - d) / 2) * b ^ 2 - 6 * b ^ 2 - 19 * b * ((1 - d) / 2) ^ 4 + 57 * b * ((1 - d) / 2) ^ 3
  - 54 * b * ((1 - d) / 2) ^ 2 + 19 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 6 - 40
  * ((1 - d) / 2) ^ 5 + 79 * ((1 - d) / 2) ^ 4 - 97 * ((1 - d) / 2) ^ 3 + 73 * ((1 - d) / 2) ^ 2
  - 31 * ((1 - d) / 2) + 6) / ((b - 1) ^ 3 * (b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) (hrkK : rkK = ((-4 / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 6 - 2 * ((1 - d) / 2) * b ^ 5
  - 21 * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4 + 26 * ((1 - d) / 2) * b ^ 4 + 18 * b ^ 4 + 10
  * ((1 - d) / 2) ^ 3 * b ^ 3 + 8 * ((1 - d) / 2) ^ 2 * b ^ 3 - 41 * ((1 - d) / 2) * b ^ 3 + 3
  * b ^ 3 + 4 * ((1 - d) / 2) ^ 4 * b ^ 2 - 42 * ((1 - d) / 2) ^ 3 * b ^ 2 + 57 * ((1 - d)
  / 2) ^ 2 * b ^ 2 - 11 * ((1 - d) / 2) * b ^ 2 - 19 * b * ((1 - d) / 2) ^ 4 + 87 * b * ((1 - d)
  / 2) ^ 3 - 129 * b * ((1 - d) / 2) ^ 2 + 74 * ((1 - d) / 2) * b - 18 * b + 10 * ((1 - d)
  / 2) ^ 6 - 40 * ((1 - d) / 2) ^ 5 + 79 * ((1 - d) / 2) ^ 4 - 107 * ((1 - d) / 2) ^ 3 + 98 * ((1
  - d) / 2) ^ 2 - 50 * ((1 - d) / 2) + 12) / ((b - 1) ^ 3 * (b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) (hrk0 : rk0 = ((2 / 9) * ((1 - d) / 2) ^ 2 * (-(36 * b ^ 5) - 32 * ((1 - d) / 2) * b ^ 4
  + 135 * b ^ 4 - 48 * ((1 - d) / 2) ^ 2 * b ^ 3 + 234 * ((1 - d) / 2) * b ^ 3 - 315 * b ^ 3 - 188
  * ((1 - d) / 2) ^ 3 * b ^ 2 + 497 * ((1 - d) / 2) ^ 2 * b ^ 2 - 593 * ((1 - d) / 2) * b ^ 2
  + 387 * b ^ 2 + 60 * b * ((1 - d) / 2) ^ 4 + 34 * b * ((1 - d) / 2) ^ 3 - 322 * b * ((1 - d)
  / 2) ^ 2 + 402 * ((1 - d) / 2) * b - 225 * b + 156 * ((1 - d) / 2) ^ 5 - 528 * ((1 - d) / 2) ^ 4
  + 598 * ((1 - d) / 2) ^ 3 - 235 * ((1 - d) / 2) ^ 2 - 35 * ((1 - d) / 2) + 54) / ((b - 1) ^ 2
  * (b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) :
    ksWPv (((ksWW4BL b d).drop 6).drop 3) (ksWW4BP b d) ((1 + d) / 2) 1 =
      log (b
  - (1 - d) / 2) * rkA + log (1 - b) * rkC + log (1 - d) * rkM + log (1 + d) * rkN + log 2 * rkK
  + rk0 := by
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
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) := ⟨_, rfl⟩
  obtain ⟨c108, hc108⟩ : ∃ x : ℝ, x = -(16 * b) := ⟨_, rfl⟩
  obtain ⟨c109, hc109⟩ : ∃ x : ℝ, x = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d
    * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1) := ⟨_, rfl⟩
  obtain ⟨c110, hc110⟩ : ∃ x : ℝ, x = -((16 * log (1 - b) * ksDT 1 d ^ 2 * b ^ 3 - 32 * log (1
    - b) * ksDT 1 d ^ 2 * b ^ 2 + 16 * log (1 - b) * b * ksDT 1 d ^ 2 + 16 * log (ksDT 1 d)
    * ksDT 1 d ^ 2 * b ^ 3 - 32 * log (ksDT 1 d) * ksDT 1 d ^ 2 * b ^ 2 + 16 * log (ksDT 1 d) * b
    * ksDT 1 d ^ 2 + 24 * ksDT 1 d ^ 2 * b ^ 3 - 48 * ksDT 1 d ^ 2 * b ^ 2 + 40 * b * ksDT 1 d ^ 2
    - 16 * ksDT 1 d ^ 2 - 16 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b + 8 * ksDT 1 d + 48)
    / (ksDT 1 d ^ 2 * (b - 1) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨c111, hc111⟩ : ∃ x : ℝ, x = (16 * log (1 - b) * ksDT 1 d * b ^ 2 - 16 * log (1 - b)
    * ksDT 1 d * b + 16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 - 16 * log (ksDT 1 d) * ksDT 1 d * b
    + 24 * ksDT 1 d * b ^ 2 - 24 * ksDT 1 d * b + 16 * ksDT 1 d - 40) / (ksDT 1 d * (b
    - 1)) := ⟨_, rfl⟩
  obtain ⟨k143, hk143⟩ : ∃ x : ℝ, x = -((d - 1) * (2 * b + d - 1) / (4 * b - 4)) := ⟨_, rfl⟩
  obtain ⟨k144, hk144⟩ : ∃ x : ℝ, x = (d - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨k145, hk145⟩ : ∃ x : ℝ, x = -((d - 1) / 2) := ⟨_, rfl⟩
  obtain ⟨k146, hk146⟩ : ∃ x : ℝ, x = (d + 1) * (d - 1) / (4 * b - 4) := ⟨_, rfl⟩
  obtain ⟨k147, hk147⟩ : ∃ x : ℝ, x = (d - 1) * (2 * b - d - 3) / (4 * b - 4) := ⟨_, rfl⟩
  obtain ⟨k148, hk148⟩ : ∃ x : ℝ, x = (d - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨k149, hk149⟩ : ∃ x : ℝ, x = -((d - 1) * (2 * b + d - 1) * (2 * b * d + 6 * b - d ^ 2 - 2
    * d - 5) / (32 * (b - 1) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨k150, hk150⟩ : ∃ x : ℝ, x = (d - 1) * (d + 3) / 8 := ⟨_, rfl⟩
  obtain ⟨k151, hk151⟩ : ∃ x : ℝ, x = -((d - 1) * (d + 3) / 8) := ⟨_, rfl⟩
  obtain ⟨k152, hk152⟩ : ∃ x : ℝ, x = (d + 1) * (d - 1) * (8 * b - d ^ 2 - 7) / (32 * (b
    - 1) ^ 2) := ⟨_, rfl⟩
  obtain ⟨k153, hk153⟩ : ∃ x : ℝ, x = (d - 1) * (4 * d * b ^ 2 + 12 * b ^ 2 - 16 * b * d - 32 * b
    + d ^ 3 + d ^ 2 + 11 * d + 19) / (32 * (b - 1) ^ 2) := ⟨_, rfl⟩
  obtain ⟨k154, hk154⟩ : ∃ x : ℝ, x = (d - 1) * (b * d + 7 * b - d ^ 2 - d - 6) / (16 * b
    - 16) := ⟨_, rfl⟩
  obtain ⟨k155, hk155⟩ : ∃ x : ℝ, x = -((d - 1) * (2 * b + d - 1) * (4 * b ^ 2 * d ^ 2 + 16 * d
    * b ^ 2 + 28 * b ^ 2 - 2 * b * d ^ 3 - 18 * b * d ^ 2 - 30 * b * d - 46 * b + d ^ 4 + 2
    * d ^ 3 + 12 * d ^ 2 + 14 * d + 19) / (192 * (b - 1) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨k156, hk156⟩ : ∃ x : ℝ, x = (d - 1) * (d ^ 2 + 4 * d + 7) / 24 := ⟨_, rfl⟩
  obtain ⟨k157, hk157⟩ : ∃ x : ℝ, x = -((d - 1) * (d ^ 2 + 4 * d + 7) / 24) := ⟨_, rfl⟩
  obtain ⟨k158, hk158⟩ : ∃ x : ℝ, x = (d + 1) * (d - 1) * (48 * b ^ 2 - 12 * b * d ^ 2 - 84 * b
    + d ^ 4 + 10 * d ^ 2 + 37) / (192 * (b - 1) ^ 3) := ⟨_, rfl⟩
  obtain ⟨k159, hk159⟩ : ∃ x : ℝ, x = (d - 1) * (8 * b ^ 3 * d ^ 2 + 32 * d * b ^ 3 + 56 * b ^ 3
    - 24 * b ^ 2 * d ^ 2 - 144 * d * b ^ 2 - 216 * b ^ 2 + 12 * b * d ^ 3 + 36 * b * d ^ 2 + 180
    * b * d + 252 * b - d ^ 5 - d ^ 4 - 10 * d ^ 3 - 18 * d ^ 2 - 69 * d - 93) / (192 * (b
    - 1) ^ 3) := ⟨_, rfl⟩
  obtain ⟨k160, hk160⟩ : ∃ x : ℝ, x = (d - 1) * (4 * b ^ 2 * d ^ 2 + 28 * d * b ^ 2 + 112 * b ^ 2
    - 3 * b * d ^ 3 - 41 * b * d ^ 2 - 53 * b * d - 191 * b + 3 * d ^ 4 + 3 * d ^ 3 + 31 * d ^ 2
    + 25 * d + 82) / (288 * (b - 1) ^ 2) := ⟨_, rfl⟩
  obtain ⟨p161, hp161⟩ : ∃ x : ℝ, x = -(16 * b) := ⟨_, rfl⟩
  obtain ⟨p162, hp162⟩ : ∃ x : ℝ, x = -(16 * b) := ⟨_, rfl⟩
  obtain ⟨p163, hp163⟩ : ∃ x : ℝ, x = -((24 * ksDT 1 d ^ 2 * b ^ 3 - 48 * ksDT 1 d ^ 2 * b ^ 2
    + 40 * b * ksDT 1 d ^ 2 - 16 * ksDT 1 d ^ 2 - 16 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b + 8
    * ksDT 1 d + 48) / (ksDT 1 d ^ 2 * (b - 1) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨p164, hp164⟩ : ∃ x : ℝ, x = 16 * b := ⟨_, rfl⟩
  obtain ⟨p165, hp165⟩ : ∃ x : ℝ, x = 16 * b := ⟨_, rfl⟩
  obtain ⟨p166, hp166⟩ : ∃ x : ℝ, x = (24 * ksDT 1 d * b ^ 2 - 24 * ksDT 1 d * b + 16 * ksDT 1 d
    - 40) / (ksDT 1 d * (b - 1)) := ⟨_, rfl⟩
  have hL : (((ksWW4BL b d).drop 6).drop 3) = [(c108, 0, (1 - 1 / ((1 - b)
    * ksDT 1 d))), (c109, 1, (1 - 1 / ((1 - b) * ksDT 1 d))), (c2, 2, (1 - 1 / ((1 - b)
    * ksDT 1 d)))] := by
    rw [hc108, hc109, hc2]
    rfl
  have hP : ksWW4BP b d = [(c110, 0), (c111, 1)] := by
    rw [hc110, hc111]
    rfl
  have hH31 := ksWY2_H31 hd hb hk143 hk144 hk145 hk146 hk147 hk148
  have hH32 := ksWY2_H32 hd hb hk149 hk150 hk151 hk152 hk153 hk154
  have hH33 := ksWY2_H33 hd hb hk155 hk156 hk157 hk158 hk159 hk160
  have hp7 := ksWY2_p7 hd hb hc110 hp161 hp162 hp163
  have hp8 := ksWY2_p8 hd hb hc111 hp164 hp165 hp166
  have k0_203 := ksWY2_k0_203 hd hb hc108 hk148 hc109 hk154 hc2 hk160 hp163 hp166 hrk0
  have kA_203 := ksWY2_kA_203 hd hb hc108 hk143 hc109 hk149 hc2 hk155 hrkA
  have kC_203 := ksWY2_kC_203 hd hb hc108 hk144 hc109 hk150 hc2 hk156 hp161 hp164 hrkC
  have kM_203 := ksWY2_kM_203 hd hb hc108 hk145 hc109 hk151 hc2 hk157 hp162 hp165 hrkM
  have kN_203 := ksWY2_kN_203 hd hb hc108 hk146 hc109 hk152 hc2 hk158 hp162 hp165 hrkN
  have kK_203 := ksWY2_kK_203 hd hb hc108 hk147 hc109 hk153 hc2 hk159 hp162 hp165 hrkK
  simp only [ksWPv, hL, hP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hH31, hH32, hH33]
  rw [hp7, hp8]
  try rw [ksWY_log_ksDT hd]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination k0_203 + A * kA_203 + C * kC_203 + M * kM_203 + N * kN_203 + K * kK_203

theorem ksWY2_Q3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) (c e : ℝ) :
    ksWPQ (1 - 1 / ((1 - b) * ksDT 1 d)) c e 1 - ksWPQ (1 - 1 / ((1 - b)
  * ksDT 1 d)) c e ((1 + d) / 2) =
      c * (log (1 + d) - log 2 - log (b - (1 - d) / 2)) + -(e
  / (1 / ((1 - b) * ksDT 1 d)) - e / ((1 - d) / 2 * (b - (1 - d) / 2) / (1 - b))) := by
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
  simp only [ksWPQ, ksWY_sp_sub_w0 hd hb1, ksWY_log_w0p hd hm hb1,
    sub_sub_cancel 1 (1 / ((1 - b) * ksDT 1 d)), ksWY_log_w0o hd hb1]
  ring

theorem ksWY2_BQ3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {rkA rkN rkK rk0 : ℝ} (hrkA : rkA = ((-8) * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2
  - 5 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2) + 4) / ((b - 1) ^ 3))) (hrkN : rkN = (8
  * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2 - 5 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d)
  / 2) + 4) / ((b - 1) ^ 3))) (hrkK : rkK = ((-8) * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2
  - 5 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2) + 4) / ((b - 1) ^ 3))) (hrk0 : rk0 = ((-8)
  * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b - (1 + d) / 2) / ((b - 1) ^ 2))) :
    (ksWPQ (1
  - 1 / ((1 - b) * ksDT 1 d)) (ksWW4Bc b d) (ksWW4Be b d) 1 - ksWPQ (1 - 1 / ((1 - b)
  * ksDT 1 d)) (ksWW4Bc b d) (ksWW4Be b d) ((1 + d) / 2)) =
      log (b - (1 - d) / 2) * rkA
  + log (1 + d) * rkN + log 2 * rkK + rk0 := by
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
  obtain ⟨c112, hc112⟩ : ∃ x : ℝ, x = (8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d
    - 56) / (ksDT 1 d ^ 3 * (b - 1) ^ 3) := ⟨_, rfl⟩
  obtain ⟨c113, hc113⟩ : ∃ x : ℝ, x = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8)
    / (ksDT 1 d ^ 4 * (b - 1) ^ 4)) := ⟨_, rfl⟩
  have hc : ksWW4Bc b d = c112 := by rw [hc112]; rfl
  have he : ksWW4Be b d = c113 := by rw [hc113]; rfl
  have k0_13 := ksWY2_k0_13 hd hb hc113 hrk0
  have kA_13 := ksWY2_kA_13 hd hb hc112 hrkA
  have kN_13 := ksWY2_kN_13 hd hb hc112 hrkN
  have kK_13 := ksWY2_kK_13 hd hb hc112 hrkK
  rw [hc, he, ksWY2_Q3 hd hb]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination k0_13 + A * kA_13 + N * kN_13 + K * kK_13

theorem ksWY2_eqOn (hd : d ∈ Ioo (0 : ℝ) 1) :
        EqOn (ksWYe (ksWY2L d) (ksWY2P d) (ksWY2D d) (ksWY2Q d) (ksWY2C d) (ksWY2R d) (ksWY2S d))
      (fun b => ksWWEII b d) (Ioo ((1 - d) / 2) ((1 + d) / 2)) := by
  intro b hb
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
  simp only [ksWWEII]
  rw [ksWY_ksWPv_split (ksWW4AL b d) (ksWW4AP b d) 0 ((1 - d) / 2) 5]
  rw [ksWY_ksWPv_split (ksWW4BL b d) (ksWW4BP b d) ((1 + d) / 2) 1 6]
  rw [ksWY_ksWPv_split ((ksWW4BL b d).drop 6) (ksWW4BP b d) ((1 + d) / 2) 1 3]
  rw [ksWY2_B0_0 hd hb rfl rfl rfl rfl rfl, ksWY2_B0_1 hd hb rfl rfl rfl rfl rfl rfl rfl, ksWY2_BQ0
    hd hb rfl rfl rfl rfl, ksWY2_B1 hd hb rfl rfl rfl rfl rfl rfl rfl rfl, ksWY2_B2 hd hb rfl rfl
    rfl rfl rfl rfl rfl rfl, ksWY2_B3_0 hd hb rfl rfl rfl rfl rfl, ksWY2_B3_1 hd hb rfl rfl rfl,
    ksWY2_B3_2 hd hb rfl rfl rfl rfl rfl rfl, ksWY2_BQ3 hd hb rfl rfl rfl rfl]
  simp only [ksWYe, ksWPe, ksWYq, ksWPq, ksWY2L, ksWY2P, ksWY2D, ksWY2Q, ksWY2C, ksWY2R, ksWY2S,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWY_log_l2 (by linarith [hd.1] : -1 < d), ksWY_log_l3, ksWY_log_l4,
    ksWY_log_l5 (by linarith [hd.1] : -1 < d), ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_zero,
    zero_sub, log_neg_eq_log, ksWY_log_swap b 1]
  generalize log (b - (1 - d) / 2) = A
  generalize log (b - (1 + d) / 2) = B
  generalize log (1 - b) = C
  generalize log (1 - d) = M
  generalize log (1 + d) = N
  generalize log 2 = K
  generalize log d = D
  generalize log b = E
  linear_combination (-1 : ℝ) * (ksWY2_k0_t hd hb + A * ksWY2_kA_t hd hb + B * ksWY2_kB_t hd hb
    + C * ksWY2_kC_t hd hb + M * ksWY2_kM_t hd hb + N * ksWY2_kN_t hd hb + K * ksWY2_kK_t hd hb
    + D * ksWY2_kD_t hd hb + E * ksWY2_kE_t hd hb)

end QED.ChainProof.SetAKS

end
