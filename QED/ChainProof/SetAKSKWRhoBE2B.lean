/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBE2A

/-!
# Set (a), stage D: the `β`-integrand on `(σ₋, σ₊)`, rational identities I

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route, range
`β ∈ (σ₋, σ₊)`, part 2 of 4: the rational identities, one per logarithm and per part of the
`w`-interval (`ksWY2_k*_i`), and their sums over the parts (`ksWY2_k*_t`), first half.
Machine-generated; every coefficient is checked by the proofs.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetAKS

variable {b d : ℝ}

theorem ksWY2_k0_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c48 k55 c49 k59 k61 k63 k66 k69 p73 p76 : ℝ} (hc48 : c48 = 8) (hk55 : k55 = -((2 * b - d
  + 1) * (2 * b + d - 1) / 16)) (hc49 : c49 = -8) (hk59 : k59 = -((2 * b + d - 1) * (4 * b ^ 2 - 2
  * b * d + 2 * b + d ^ 2 - 2 * d + 1) / 72)) (hk61 : k61 = -((2 * b + d - 1) * (2 * b - 3 * d
  + 3) / 16)) (hk63 : k63 = -((2 * b + d - 1) * (8 * b ^ 2 - 10 * b * d + 10 * b + 11 * d ^ 2 - 22
  * d + 11) / 144)) (hk66 : k66 = -((2 * b + d - 1) * (2 * b + d + 3) / 16)) (hk69 : k69 = -((2
  * b + d - 1) * (8 * b ^ 2 + 2 * b * d + 10 * b + 5 * d ^ 2 + 8 * d + 11)
  / 144)) (hp73 : p73 = (24 * b ^ 2 - 20 * b + 16) / b) (hp76 : p76 = -4) {r : ℝ} (hr : r = ((-4
  / 9) * (b - (1 - d) / 2) * (-(22 * b ^ 3) - 22 * ((1 - d) / 2) * b ^ 2 + 21 * b ^ 2 + 17 * b
  * ((1 - d) / 2) ^ 2 + 9 * ((1 - d) / 2) * b - 21 * b - 18 * ((1 - d) / 2)) / (b))) :
    c48
  * k55 + c49 * k59 + c49 * k61 + c48 * k63 + c49 * k66 + c48 * k69 + (1 * p73) * ((b ^ 2 - ((1
  - d) / 2) ^ 2) / 2) + (1 * p76) * ((b ^ 3 - ((1 - d) / 2) ^ 3) / 3) = r := by
  subst hr hc48 hk55 hc49 hk59 hk61 hk63 hk66 hk69 hp73 hp76
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

theorem ksWY2_k0_2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c48 k83 c49 k87 k90 k93 k95 k97 p99 p103 p106 : ℝ} (hc48 : c48 = 8) (hk83 : k83 = (2 * b
  - d - 1) * (2 * b + d + 5) / 16) (hc49 : c49 = -8) (hk87 : k87 = (2 * b - d - 1) * (4 * b ^ 2
  + 2 * b * d + 8 * b + d ^ 2 + 5 * d + 16) / 72) (hk90 : k90 = (2 * b - d - 1) * (2 * b - d + 3)
  / 16) (hk93 : k93 = (2 * b - d - 1) * (8 * b ^ 2 - 2 * b * d + 10 * b + 5 * d ^ 2 - 8 * d + 11)
  / 144) (hk95 : k95 = (2 * b - d - 1) * (2 * b + 3 * d + 3) / 16) (hk97 : k97 = (2 * b - d - 1)
  * (8 * b ^ 2 + 10 * b * d + 10 * b + 11 * d ^ 2 + 22 * d + 11) / 144) (hp99 : p99 = -((24
  * b ^ 2 - 24 * b + 16) / (b - 1))) (hp103 : p103 = (24 * b ^ 2 - 20 * b + 12) / (b
  - 1)) (hp106 : p106 = -4) {r : ℝ} (hr : r = ((4 / 9) * (b - (1 + d) / 2) * (-(22 * b ^ 3) + 22
  * ((1 - d) / 2) * b ^ 2 + 45 * b ^ 2 + 17 * b * ((1 - d) / 2) ^ 2 - 35 * ((1 - d) / 2) * b - 45
  * b - 17 * ((1 - d) / 2) ^ 2 + 31 * ((1 - d) / 2) + 22) / ((b - 1)))) :
    c48 * k83 + c49
  * k87 + c49 * k90 + c48 * k93 + c49 * k95 + c48 * k97 + (1 * p99) * ((((1 + d) / 2) ^ 1 - b ^ 1)
  / 1) + (1 * p103) * ((((1 + d) / 2) ^ 2 - b ^ 2) / 2) + (1 * p106) * ((((1 + d) / 2) ^ 3
  - b ^ 3) / 3) = r := by
  subst hr hc48 hk83 hc49 hk87 hk90 hk93 hk95 hk97 hp99 hp103 hp106
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

theorem ksWY2_k0_3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c107 k116 c108 k119 c2 k123 c3 k127 k130 k133 : ℝ} (hc107 : c107 = 16
  * b) (hk116 : k116 = (d - 1) / 2) (hc108 : c108 = -(16 * b)) (hk119 : k119 = (d - 1) * (d + 7)
  / 16) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1))) (hk123 : k123 = -((d - 1) * (d - 5) / 16)) (hc3 : c3 = (8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk127 : k127 = (d - 1) * (5 * d ^ 2 - 10 * d + 29) / 144) (hk130 : k130 = (d - 1) * (3
  * d + 5) / 16) (hk133 : k133 = (d - 1) * (11 * d ^ 2 + 32 * d + 29) / 144) {r : ℝ} (hr : r = ((4
  / 9) * ((1 - d) / 2) * (-(9 * ((1 - d) / 2) * b ^ 3) - 16 * ((1 - d) / 2) ^ 2 * b ^ 2 + 27 * ((1
  - d) / 2) * b ^ 2 + 3 * b ^ 2 + 9 * b * ((1 - d) / 2) ^ 3 + 7 * b * ((1 - d) / 2) ^ 2 - 18 * ((1
  - d) / 2) * b - 3 * b + 80 * ((1 - d) / 2) ^ 4 - 170 * ((1 - d) / 2) ^ 3 + 107 * ((1 - d)
  / 2) ^ 2 - 21 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c107 * k116
  + c108 * k119 + c2 * k123 + c3 * k127 + c2 * k130 + c3 * k133 = r := by
  subst hr hc107 hk116 hc108 hk119 hc2 hk123 hc3 hk127 hk130 hk133
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

theorem ksWY2_k0_10 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c8 : ℝ} (hc8 : c8 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4
  * b ^ 4))) {r : ℝ} (hr : r = (8 * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b - (1 - d) / 2)
  / (b ^ 2))) :
    -(c8 / ((1 - d) / 2 * (b - (1 + d) / 2) / b) - c8 / -(1 / (b
  * ksDT 1 d))) = r := by
  subst hr hc8
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
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY2_k0_13 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c113 : ℝ} (hc113 : c113 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4
  * (b - 1) ^ 4))) {r : ℝ} (hr : r = ((-8) * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b - (1 + d)
  / 2) / ((b - 1) ^ 2))) :
    -(c113 / (1 / ((1 - b) * ksDT 1 d)) - c113 / ((1 - d) / 2 * (b - (1
  - d) / 2) / (1 - b))) = r := by
  subst hr hc113
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
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY2_k0_100 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c4 k28 c2 k31 k37 k43 p44 p47 : ℝ} (hc4 : c4 = (16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d
  * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk28 : k28 = (d - 1) * (4 * b - d + 1) / 16) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk31 : k31 = (d
  - 1) * (12 * b ^ 2 - 3 * b * d + 3 * b + d ^ 2 - 2 * d + 1) / 72) (hk37 : k37 = -((d - 1) ^ 2
  * (b + d + 1) / (16 * b))) (hk43 : k43 = (d - 1) ^ 3 * (4 * b ^ 2 + 3 * b * d + 3 * b + 3
  * d ^ 2 + 6 * d + 3) / (288 * b ^ 2)) (hp44 : p44 = (16 * ksDT 1 d * b ^ 2 + 16 * ksDT 1 d * b
  - 48) / (ksDT 1 d ^ 2 * b ^ 2)) (hp47 : p47 = (24 * ksDT 1 d * b ^ 2 - 24 * ksDT 1 d * b + 16
  * ksDT 1 d - 40) / (ksDT 1 d * b)) {r : ℝ} (hr : r = ((4 / 9) * ((1 - d) / 2) * (-(12 * b ^ 6)
  + 12 * ((1 - d) / 2) * b ^ 5 + 21 * b ^ 5 - 26 * ((1 - d) / 2) ^ 2 * b ^ 4 - 21 * b ^ 4 + 18
  * ((1 - d) / 2) ^ 3 * b ^ 3 - 22 * ((1 - d) / 2) ^ 2 * b ^ 3 + 30 * ((1 - d) / 2) * b ^ 3 + 18
  * b ^ 3 - 104 * ((1 - d) / 2) ^ 4 * b ^ 2 + 200 * ((1 - d) / 2) ^ 3 * b ^ 2 - 59 * ((1 - d)
  / 2) ^ 2 * b ^ 2 - 45 * ((1 - d) / 2) * b ^ 2 - 30 * b * ((1 - d) / 2) ^ 5 + 171 * b * ((1 - d)
  / 2) ^ 4 - 264 * b * ((1 - d) / 2) ^ 3 + 105 * b * ((1 - d) / 2) ^ 2 + 18 * ((1 - d) / 2) * b
  + 78 * ((1 - d) / 2) ^ 6 - 234 * ((1 - d) / 2) ^ 5 + 222 * ((1 - d) / 2) ^ 4 - 54 * ((1 - d)
  / 2) ^ 3 - 12 * ((1 - d) / 2) ^ 2) / (b ^ 2 * (b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c4
  * k28 + c2 * k31 + c4 * k37 + c2 * k43 + (1 * p44) * ((((1 - d) / 2) ^ 1 - 0 ^ 1) / 1) + (1
  * p47) * ((((1 - d) / 2) ^ 2 - 0 ^ 2) / 2) = r := by
  subst hr hc4 hk28 hc2 hk31 hk37 hk43 hp44 hp47
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

theorem ksWY2_k0_103 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c108 k136 c109 k139 c2 k142 : ℝ} (hc108 : c108 = -(16 * b)) (hk136 : k136 = (d - 1)
  / 2) (hc109 : c109 = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) (hk139 : k139 = (d - 1) * (4
  * b + d + 3) / 16) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk142 : k142 = (d - 1) * (12 * b ^ 2 + 3 * b * d + 9
  * b + d ^ 2 + 4 * d + 7) / 72) {r : ℝ} (hr : r = ((-2 / 9) * ((1 - d) / 2) * (24 * b ^ 4 - 12
  * ((1 - d) / 2) * b ^ 3 - 54 * b ^ 3 + 20 * ((1 - d) / 2) ^ 2 * b ^ 2 - 9 * ((1 - d) / 2)
  * b ^ 2 + 60 * b ^ 2 - 12 * b * ((1 - d) / 2) ^ 3 + 22 * b * ((1 - d) / 2) ^ 2 - 21 * ((1 - d)
  / 2) * b - 18 * b + 20 * ((1 - d) / 2) ^ 4 - 35 * ((1 - d) / 2) ^ 3 - 7 * ((1 - d) / 2) ^ 2 + 24
  * ((1 - d) / 2) - 12) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c108 * k136 + c109
  * k139 + c2 * k142 = r := by
  subst hr hc108 hk136 hc109 hk139 hc2 hk142
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

theorem ksWY2_k0_203 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c108 k148 c109 k154 c2 k160 p163 p166 : ℝ} (hc108 : c108 = -(16 * b)) (hk148 : k148 = (d
  - 1) / 2) (hc109 : c109 = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) (hk154 : k154 = (d - 1) * (b
  * d + 7 * b - d ^ 2 - d - 6) / (16 * b - 16)) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d
  * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk160 : k160 = (d - 1) * (4
  * b ^ 2 * d ^ 2 + 28 * d * b ^ 2 + 112 * b ^ 2 - 3 * b * d ^ 3 - 41 * b * d ^ 2 - 53 * b * d
  - 191 * b + 3 * d ^ 4 + 3 * d ^ 3 + 31 * d ^ 2 + 25 * d + 82) / (288 * (b
  - 1) ^ 2)) (hp163 : p163 = -((24 * ksDT 1 d ^ 2 * b ^ 3 - 48 * ksDT 1 d ^ 2 * b ^ 2 + 40 * b
  * ksDT 1 d ^ 2 - 16 * ksDT 1 d ^ 2 - 16 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b + 8 * ksDT 1 d
  + 48) / (ksDT 1 d ^ 2 * (b - 1) ^ 2))) (hp166 : p166 = (24 * ksDT 1 d * b ^ 2 - 24 * ksDT 1 d
  * b + 16 * ksDT 1 d - 40) / (ksDT 1 d * (b - 1))) {r : ℝ} (hr : r = ((2 / 9) * ((1 - d) / 2) ^ 2
  * (-(36 * b ^ 5) - 32 * ((1 - d) / 2) * b ^ 4 + 135 * b ^ 4 - 48 * ((1 - d) / 2) ^ 2 * b ^ 3
  + 234 * ((1 - d) / 2) * b ^ 3 - 315 * b ^ 3 - 188 * ((1 - d) / 2) ^ 3 * b ^ 2 + 497 * ((1 - d)
  / 2) ^ 2 * b ^ 2 - 593 * ((1 - d) / 2) * b ^ 2 + 387 * b ^ 2 + 60 * b * ((1 - d) / 2) ^ 4 + 34
  * b * ((1 - d) / 2) ^ 3 - 322 * b * ((1 - d) / 2) ^ 2 + 402 * ((1 - d) / 2) * b - 225 * b + 156
  * ((1 - d) / 2) ^ 5 - 528 * ((1 - d) / 2) ^ 4 + 598 * ((1 - d) / 2) ^ 3 - 235 * ((1 - d)
  / 2) ^ 2 - 35 * ((1 - d) / 2) + 54) / ((b - 1) ^ 2 * (b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) :
    c108 * k148 + c109 * k154 + c2 * k160 + (1 * p163) * ((1 ^ 1 - ((1 + d) / 2) ^ 1)
  / 1) + (1 * p166) * ((1 ^ 2 - ((1 + d) / 2) ^ 2) / 2) = r := by
  subst hr hc108 hk148 hc109 hk154 hc2 hk160 hp163 hp166
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

theorem ksWY2_k0_t (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ((4
  / 9) * ((1 - d) / 2) * (9 * ((1 - d) / 2) * b ^ 3 - 16 * ((1 - d) / 2) ^ 2 * b ^ 2 + 3 * b ^ 2
  - 9 * b * ((1 - d) / 2) ^ 3 + 25 * b * ((1 - d) / 2) ^ 2 - 9 * ((1 - d) / 2) * b - 3 * b + 80
  * ((1 - d) / 2) ^ 4 - 161 * ((1 - d) / 2) ^ 3 + 98 * ((1 - d) / 2) ^ 2 - 21 * ((1 - d) / 2) - 6)
  / ((b - (1 - d) / 2) * (b - (1 + d) / 2))) + ((-4 / 9) * (b - (1 - d) / 2) * (-(22 * b ^ 3) - 22
  * ((1 - d) / 2) * b ^ 2 + 21 * b ^ 2 + 17 * b * ((1 - d) / 2) ^ 2 + 9 * ((1 - d) / 2) * b - 21
  * b - 18 * ((1 - d) / 2)) / (b)) + ((4 / 9) * (b - (1 + d) / 2) * (-(22 * b ^ 3) + 22 * ((1 - d)
  / 2) * b ^ 2 + 45 * b ^ 2 + 17 * b * ((1 - d) / 2) ^ 2 - 35 * ((1 - d) / 2) * b - 45 * b - 17
  * ((1 - d) / 2) ^ 2 + 31 * ((1 - d) / 2) + 22) / ((b - 1))) + ((4 / 9) * ((1 - d) / 2) * (-(9
  * ((1 - d) / 2) * b ^ 3) - 16 * ((1 - d) / 2) ^ 2 * b ^ 2 + 27 * ((1 - d) / 2) * b ^ 2 + 3
  * b ^ 2 + 9 * b * ((1 - d) / 2) ^ 3 + 7 * b * ((1 - d) / 2) ^ 2 - 18 * ((1 - d) / 2) * b - 3 * b
  + 80 * ((1 - d) / 2) ^ 4 - 170 * ((1 - d) / 2) ^ 3 + 107 * ((1 - d) / 2) ^ 2 - 21 * ((1 - d)
  / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d) / 2))) + (8 * ((1 + d) / 2) ^ 2 * ((1 - d)
  / 2) ^ 2 * (b - (1 - d) / 2) / (b ^ 2)) + ((-8) * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b
  - (1 + d) / 2) / ((b - 1) ^ 2)) + ((4 / 9) * ((1 - d) / 2) * (-(12 * b ^ 6) + 12 * ((1 - d) / 2)
  * b ^ 5 + 21 * b ^ 5 - 26 * ((1 - d) / 2) ^ 2 * b ^ 4 - 21 * b ^ 4 + 18 * ((1 - d) / 2) ^ 3
  * b ^ 3 - 22 * ((1 - d) / 2) ^ 2 * b ^ 3 + 30 * ((1 - d) / 2) * b ^ 3 + 18 * b ^ 3 - 104 * ((1
  - d) / 2) ^ 4 * b ^ 2 + 200 * ((1 - d) / 2) ^ 3 * b ^ 2 - 59 * ((1 - d) / 2) ^ 2 * b ^ 2 - 45
  * ((1 - d) / 2) * b ^ 2 - 30 * b * ((1 - d) / 2) ^ 5 + 171 * b * ((1 - d) / 2) ^ 4 - 264 * b
  * ((1 - d) / 2) ^ 3 + 105 * b * ((1 - d) / 2) ^ 2 + 18 * ((1 - d) / 2) * b + 78 * ((1 - d)
  / 2) ^ 6 - 234 * ((1 - d) / 2) ^ 5 + 222 * ((1 - d) / 2) ^ 4 - 54 * ((1 - d) / 2) ^ 3 - 12 * ((1
  - d) / 2) ^ 2) / (b ^ 2 * (b - (1 - d) / 2) * (b - (1 + d) / 2))) + ((-2 / 9) * ((1 - d) / 2)
  * (24 * b ^ 4 - 12 * ((1 - d) / 2) * b ^ 3 - 54 * b ^ 3 + 20 * ((1 - d) / 2) ^ 2 * b ^ 2 - 9
  * ((1 - d) / 2) * b ^ 2 + 60 * b ^ 2 - 12 * b * ((1 - d) / 2) ^ 3 + 22 * b * ((1 - d) / 2) ^ 2
  - 21 * ((1 - d) / 2) * b - 18 * b + 20 * ((1 - d) / 2) ^ 4 - 35 * ((1 - d) / 2) ^ 3 - 7 * ((1
  - d) / 2) ^ 2 + 24 * ((1 - d) / 2) - 12) / ((b - (1 - d) / 2) * (b - (1 + d) / 2))) + ((2 / 9)
  * ((1 - d) / 2) ^ 2 * (-(36 * b ^ 5) - 32 * ((1 - d) / 2) * b ^ 4 + 135 * b ^ 4 - 48 * ((1 - d)
  / 2) ^ 2 * b ^ 3 + 234 * ((1 - d) / 2) * b ^ 3 - 315 * b ^ 3 - 188 * ((1 - d) / 2) ^ 3 * b ^ 2
  + 497 * ((1 - d) / 2) ^ 2 * b ^ 2 - 593 * ((1 - d) / 2) * b ^ 2 + 387 * b ^ 2 + 60 * b * ((1
  - d) / 2) ^ 4 + 34 * b * ((1 - d) / 2) ^ 3 - 322 * b * ((1 - d) / 2) ^ 2 + 402 * ((1 - d) / 2)
  * b - 225 * b + 156 * ((1 - d) / 2) ^ 5 - 528 * ((1 - d) / 2) ^ 4 + 598 * ((1 - d) / 2) ^ 3
  - 235 * ((1 - d) / 2) ^ 2 - 35 * ((1 - d) / 2) + 54) / ((b - 1) ^ 2 * (b - (1 - d) / 2) * (b
  - (1 + d) / 2))) = ((37 * d ^ 3 - 45 * d ^ 2 + 9 * d + 87) / 9) * b ^ 0 + (-((16 * d + 16) / 3))
  * b ^ 1 + ((16 * d + 16) / 3) * b ^ 2 + (-((d + 1) * (d - 1) * (8 * d ^ 2 + d - 13) / 6)) * (b
  - 1)⁻¹ + (2 * (d - 1) ^ 2 * (d + 1) * (2 * d ^ 2 - 3) / 3) * ((b - 1) ^ 2)⁻¹ + ((d + 1) * (d
  - 1) * (8 * d ^ 2 + d - 13) / 6) * (b - 0)⁻¹ + (2 * (d - 1) ^ 2 * (d + 1) * (2 * d ^ 2 - 3) / 3)
  * ((b - 0) ^ 2)⁻¹ := by
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

theorem ksWY2_kA_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c49 k60 c48 k62 p70 : ℝ} (hc49 : c49 = -8) (hk60 : k60 = (2 * b - d + 1) * (2 * b + d
  - 1) / 8) (hc48 : c48 = 8) (hk62 : k62 = (2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b
  + d ^ 2 - 2 * d + 1) / 24) (hp70 : p70 = (16 * b - 16)) {r : ℝ} (hr : r = ((4 / 3) * (b - (1
  - d) / 2) * (8 * b ^ 2 + 8 * ((1 - d) / 2) * b - 9 * b + 2 * ((1 - d) / 2) ^ 2 - 9 * ((1 - d)
  / 2)))) :
    c49 * k60 + c48 * k62 + (1 * p70) * ((b ^ 2 - ((1 - d) / 2) ^ 2) / 2) = r := by
  subst hr hc49 hk60 hc48 hk62 hp70
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

theorem ksWY2_kA_2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c49 k88 c48 k91 p98 p101 : ℝ} (hc49 : c49 = -8) (hk88 : k88 = -((2 * b - d + 1) * (2 * b
  + d - 1) / 8)) (hc48 : c48 = 8) (hk91 : k91 = -((2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b
  + d ^ 2 - 2 * d + 1) / 24)) (hp98 : p98 = -(16 * b)) (hp101 : p101 = 16
  * b) {r : ℝ} (hr : r = ((4 / 3) * (-(8 * b ^ 3) + 15 * b ^ 2 + 6 * b * ((1 - d) / 2) ^ 2 - 6 * b
  + 2 * ((1 - d) / 2) ^ 3 - 3 * ((1 - d) / 2) ^ 2))) :
    c49 * k88 + c48 * k91 + (1 * p98)
  * ((((1 + d) / 2) ^ 1 - b ^ 1) / 1) + (1 * p101) * ((((1 + d) / 2) ^ 2 - b ^ 2) / 2) = r := by
  subst hr hc49 hk88 hc48 hk91 hp98 hp101
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

theorem ksWY2_kA_13 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c112 : ℝ} (hc112 : c112 = (8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d - 56)
  / (ksDT 1 d ^ 3 * (b - 1) ^ 3)) {r : ℝ} (hr : r = ((-8) * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2
  * (b ^ 2 - 5 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2) + 4) / ((b - 1) ^ 3))) :
    -1
  * c112 = r := by
  subst hr hc112
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
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY2_kA_100 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c4 k26 c2 k29 : ℝ} (hc4 : c4 = (16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk26 : k26 = -((2 * b - d + 1) * (2 * b + d - 1) / 8)) (hc2 : c2 = -((8 * ksDT 1 d
  * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1))) (hk29 : k29 = -((2 * b + d - 1) * (4 * b ^ 2 - 2 * b * d + 2 * b + d ^ 2 - 2 * d + 1)
  / 24)) {r : ℝ} (hr : r = ((-4 / 3) * (4 * b ^ 4 + 4 * ((1 - d) / 2) * b ^ 3 - 7 * b ^ 3 + 2
  * ((1 - d) / 2) ^ 2 * b ^ 2 - 11 * ((1 - d) / 2) * b ^ 2 + 7 * b ^ 2 + 4 * b * ((1 - d) / 2) ^ 3
  - 11 * b * ((1 - d) / 2) ^ 2 + 16 * ((1 - d) / 2) * b - 6 * b + 10 * ((1 - d) / 2) ^ 4 - 19
  * ((1 - d) / 2) ^ 3 + 13 * ((1 - d) / 2) ^ 2 - 6 * ((1 - d) / 2)) / ((b - (1 + d)
  / 2)))) :
    c4 * k26 + c2 * k29 = r := by
  subst hr hc4 hk26 hc2 hk29
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

theorem ksWY2_kA_203 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c108 k143 c109 k149 c2 k155 : ℝ} (hc108 : c108 = -(16 * b)) (hk143 : k143 = -((d - 1)
  * (2 * b + d - 1) / (4 * b - 4))) (hc109 : c109 = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2
  - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk149 : k149 = -((d - 1) * (2 * b + d - 1) * (2 * b * d + 6 * b - d ^ 2 - 2 * d - 5)
  / (32 * (b - 1) ^ 2))) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d
  + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk155 : k155 = -((d - 1) * (2 * b + d - 1) * (4
  * b ^ 2 * d ^ 2 + 16 * d * b ^ 2 + 28 * b ^ 2 - 2 * b * d ^ 3 - 18 * b * d ^ 2 - 30 * b * d - 46
  * b + d ^ 4 + 2 * d ^ 3 + 12 * d ^ 2 + 14 * d + 19) / (192 * (b
  - 1) ^ 3))) {r : ℝ} (hr : r = ((4 / 3) * ((1 - d) / 2) ^ 2 * (-(6 * b ^ 5) - 8 * ((1 - d) / 2)
  * b ^ 4 + 27 * b ^ 4 + 4 * ((1 - d) / 2) ^ 2 * b ^ 3 + 17 * ((1 - d) / 2) * b ^ 3 - 42 * b ^ 3
  + 14 * ((1 - d) / 2) ^ 3 * b ^ 2 - 41 * ((1 - d) / 2) ^ 2 * b ^ 2 + 13 * ((1 - d) / 2) * b ^ 2
  + 21 * b ^ 2 + 10 * b * ((1 - d) / 2) ^ 4 - 59 * b * ((1 - d) / 2) ^ 3 + 106 * b * ((1 - d)
  / 2) ^ 2 - 66 * ((1 - d) / 2) * b + 12 * b + 10 * ((1 - d) / 2) ^ 5 - 40 * ((1 - d) / 2) ^ 4
  + 79 * ((1 - d) / 2) ^ 3 - 87 * ((1 - d) / 2) ^ 2 + 48 * ((1 - d) / 2) - 12) / ((b - 1) ^ 3 * (b
  - (1 + d) / 2)))) :
    c108 * k143 + c109 * k149 + c2 * k155 = r := by
  subst hr hc108 hk143 hc109 hk149 hc2 hk155
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

theorem ksWY2_kA_t (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ((4
  / 3) * (b - (1 - d) / 2) * (8 * b ^ 2 + 8 * ((1 - d) / 2) * b - 9 * b + 2 * ((1 - d) / 2) ^ 2
  - 9 * ((1 - d) / 2))) + ((4 / 3) * (-(8 * b ^ 3) + 15 * b ^ 2 + 6 * b * ((1 - d) / 2) ^ 2 - 6
  * b + 2 * ((1 - d) / 2) ^ 3 - 3 * ((1 - d) / 2) ^ 2)) + ((-8) * ((1 + d) / 2) ^ 2 * ((1 - d)
  / 2) ^ 2 * (b ^ 2 - 5 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2) + 4) / ((b - 1) ^ 3))
  + ((-4 / 3) * (4 * b ^ 4 + 4 * ((1 - d) / 2) * b ^ 3 - 7 * b ^ 3 + 2 * ((1 - d) / 2) ^ 2 * b ^ 2
  - 11 * ((1 - d) / 2) * b ^ 2 + 7 * b ^ 2 + 4 * b * ((1 - d) / 2) ^ 3 - 11 * b * ((1 - d)
  / 2) ^ 2 + 16 * ((1 - d) / 2) * b - 6 * b + 10 * ((1 - d) / 2) ^ 4 - 19 * ((1 - d) / 2) ^ 3 + 13
  * ((1 - d) / 2) ^ 2 - 6 * ((1 - d) / 2)) / ((b - (1 + d) / 2))) + ((4 / 3) * ((1 - d) / 2) ^ 2
  * (-(6 * b ^ 5) - 8 * ((1 - d) / 2) * b ^ 4 + 27 * b ^ 4 + 4 * ((1 - d) / 2) ^ 2 * b ^ 3 + 17
  * ((1 - d) / 2) * b ^ 3 - 42 * b ^ 3 + 14 * ((1 - d) / 2) ^ 3 * b ^ 2 - 41 * ((1 - d) / 2) ^ 2
  * b ^ 2 + 13 * ((1 - d) / 2) * b ^ 2 + 21 * b ^ 2 + 10 * b * ((1 - d) / 2) ^ 4 - 59 * b * ((1
  - d) / 2) ^ 3 + 106 * b * ((1 - d) / 2) ^ 2 - 66 * ((1 - d) / 2) * b + 12 * b + 10 * ((1 - d)
  / 2) ^ 5 - 40 * ((1 - d) / 2) ^ 4 + 79 * ((1 - d) / 2) ^ 3 - 87 * ((1 - d) / 2) ^ 2 + 48 * ((1
  - d) / 2) - 12) / ((b - 1) ^ 3 * (b - (1 + d) / 2))) = ((2 * d ^ 3 + 4 * d ^ 2 - 6 * d + 8) / 3)
  * b ^ 0 + (-((8 * d ^ 2 + 32) / 3)) * b ^ 1 + 12 * b ^ 2 + (-16 / 3) * b ^ 3 + (2 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3) * (b - 1)⁻¹ + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 + d) / 2))⁻¹
  + ((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12) * ((b - 1) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2
  * (2 * d ^ 2 - 3) / 3)) * ((b - 1) ^ 3)⁻¹ := by
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

theorem ksWY2_kB_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c49 k64 c48 k67 p70 : ℝ} (hc49 : c49 = -8) (hk64 : k64 = (2 * b + d + 1) * (2 * b - d
  - 1) / 8) (hc48 : c48 = 8) (hk67 : k67 = (2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b
  + d ^ 2 + 2 * d + 1) / 24) (hp70 : p70 = (16 * b - 16)) {r : ℝ} (hr : r = ((4 / 3) * (8 * b ^ 3
  - 9 * b ^ 2 - 6 * b * ((1 - d) / 2) ^ 2 + 2 * ((1 - d) / 2) ^ 3 + 3 * ((1 - d) / 2) ^ 2
  + 1))) :
    c49 * k64 + c48 * k67 + (1 * p70) * ((b ^ 2 - ((1 - d) / 2) ^ 2) / 2) = r := by
  subst hr hc49 hk64 hc48 hk67 hp70
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

theorem ksWY2_kB_2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c49 k94 c48 k96 p98 p101 : ℝ} (hc49 : c49 = -8) (hk94 : k94 = -((2 * b + d + 1) * (2 * b
  - d - 1) / 8)) (hc48 : c48 = 8) (hk96 : k96 = -((2 * b - d - 1) * (4 * b ^ 2 + 2 * b * d + 2 * b
  + d ^ 2 + 2 * d + 1) / 24)) (hp98 : p98 = -(16 * b)) (hp101 : p101 = 16
  * b) {r : ℝ} (hr : r = ((-4 / 3) * (b - (1 + d) / 2) * (8 * b ^ 2 - 8 * ((1 - d) / 2) * b - 7
  * b + 2 * ((1 - d) / 2) ^ 2 - ((1 - d) / 2) - 1))) :
    c49 * k94 + c48 * k96 + (1 * p98)
  * ((((1 + d) / 2) ^ 1 - b ^ 1) / 1) + (1 * p101) * ((((1 + d) / 2) ^ 2 - b ^ 2) / 2) = r := by
  subst hr hc49 hk94 hc48 hk96 hp98 hp101
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

theorem ksWY2_kB_10 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c7 : ℝ} (hc7 : c7 = (8 * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56) / (ksDT 1 d ^ 3
  * b ^ 3)) {r : ℝ} (hr : r = (8 * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2 + 3 * b + 7
  * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2)) / (b ^ 3))) :
    1 * c7 = r := by
  subst hr hc7
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
  simp only [e1, e2, eT] at hbm hbp ⊢
  field_simp
  ring

theorem ksWY2_kB_100 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c4 k32 c2 k38 : ℝ} (hc4 : c4 = (16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk32 : k32 = (d - 1) ^ 2 * (2 * b + d + 1) * (2 * b - d - 1) / (32
  * b ^ 2)) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk38 : k38 = -((d - 1) ^ 3 * (2 * b - d - 1) * (4
  * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2 * d + 1) / (192 * b ^ 3))) {r : ℝ} (hr : r = ((4 / 3)
  * ((1 - d) / 2) ^ 2 * (6 * b ^ 5 - 8 * ((1 - d) / 2) * b ^ 4 - 3 * b ^ 4 - 4 * ((1 - d) / 2) ^ 2
  * b ^ 3 + 15 * ((1 - d) / 2) * b ^ 3 - 6 * b ^ 3 + 14 * ((1 - d) / 2) ^ 3 * b ^ 2 - 29 * ((1
  - d) / 2) ^ 2 * b ^ 2 + 16 * ((1 - d) / 2) * b ^ 2 - 3 * b ^ 2 - 10 * b * ((1 - d) / 2) ^ 4 + 31
  * b * ((1 - d) / 2) ^ 3 - 36 * b * ((1 - d) / 2) ^ 2 + 21 * ((1 - d) / 2) * b - 6 * b + 10 * ((1
  - d) / 2) ^ 5 - 30 * ((1 - d) / 2) ^ 4 + 34 * ((1 - d) / 2) ^ 3 - 18 * ((1 - d) / 2) ^ 2 + 4
  * ((1 - d) / 2)) / (b ^ 3 * (b - (1 - d) / 2)))) :
    c4 * k32 + c2 * k38 = r := by
  subst hr hc4 hk32 hc2 hk38
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

theorem ksWY2_kB_103 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c108 k134 c109 k137 c2 k140 : ℝ} (hc108 : c108 = -(16 * b)) (hk134 : k134 = (2 * b - d
  - 1) / 2) (hc109 : c109 = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) (hk137 : k137 = (2 * b + d
  + 1) * (2 * b - d - 1) / 8) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk140 : k140 = (2 * b - d - 1) * (4
  * b ^ 2 + 2 * b * d + 2 * b + d ^ 2 + 2 * d + 1) / 24) {r : ℝ} (hr : r = ((4 / 3) * (4 * b ^ 4
  - 4 * ((1 - d) / 2) * b ^ 3 - 9 * b ^ 3 + 2 * ((1 - d) / 2) ^ 2 * b ^ 2 + ((1 - d) / 2) * b ^ 2
  + 10 * b ^ 2 - 4 * b * ((1 - d) / 2) ^ 3 + 7 * b * ((1 - d) / 2) ^ 2 - 6 * ((1 - d) / 2) * b - 3
  * b + 10 * ((1 - d) / 2) ^ 4 - 15 * ((1 - d) / 2) ^ 3 + 4 * ((1 - d) / 2) ^ 2 + 3 * ((1 - d)
  / 2) - 2) / ((b - (1 - d) / 2)))) :
    c108 * k134 + c109 * k137 + c2 * k140 = r := by
  subst hr hc108 hk134 hc109 hk137 hc2 hk140
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

theorem ksWY2_kB_t (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ((4
  / 3) * (8 * b ^ 3 - 9 * b ^ 2 - 6 * b * ((1 - d) / 2) ^ 2 + 2 * ((1 - d) / 2) ^ 3 + 3 * ((1 - d)
  / 2) ^ 2 + 1)) + ((-4 / 3) * (b - (1 + d) / 2) * (8 * b ^ 2 - 8 * ((1 - d) / 2) * b - 7 * b + 2
  * ((1 - d) / 2) ^ 2 - ((1 - d) / 2) - 1)) + (8 * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2
  + 3 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2)) / (b ^ 3)) + ((4 / 3) * ((1 - d) / 2) ^ 2
  * (6 * b ^ 5 - 8 * ((1 - d) / 2) * b ^ 4 - 3 * b ^ 4 - 4 * ((1 - d) / 2) ^ 2 * b ^ 3 + 15 * ((1
  - d) / 2) * b ^ 3 - 6 * b ^ 3 + 14 * ((1 - d) / 2) ^ 3 * b ^ 2 - 29 * ((1 - d) / 2) ^ 2 * b ^ 2
  + 16 * ((1 - d) / 2) * b ^ 2 - 3 * b ^ 2 - 10 * b * ((1 - d) / 2) ^ 4 + 31 * b * ((1 - d)
  / 2) ^ 3 - 36 * b * ((1 - d) / 2) ^ 2 + 21 * ((1 - d) / 2) * b - 6 * b + 10 * ((1 - d) / 2) ^ 5
  - 30 * ((1 - d) / 2) ^ 4 + 34 * ((1 - d) / 2) ^ 3 - 18 * ((1 - d) / 2) ^ 2 + 4 * ((1 - d) / 2))
  / (b ^ 3 * (b - (1 - d) / 2))) + ((4 / 3) * (4 * b ^ 4 - 4 * ((1 - d) / 2) * b ^ 3 - 9 * b ^ 3
  + 2 * ((1 - d) / 2) ^ 2 * b ^ 2 + ((1 - d) / 2) * b ^ 2 + 10 * b ^ 2 - 4 * b * ((1 - d) / 2) ^ 3
  + 7 * b * ((1 - d) / 2) ^ 2 - 6 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 4 - 15 * ((1
  - d) / 2) ^ 3 + 4 * ((1 - d) / 2) ^ 2 + 3 * ((1 - d) / 2) - 2) / ((b - (1 - d) / 2))) = ((2
  * d ^ 3 - 4 * d ^ 2 - 6 * d - 4) / 3) * b ^ 0 + ((8 * d ^ 2 + 8) / 3) * b ^ 1 + (-4) * b ^ 2
  + (16 / 3) * b ^ 3 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - 0)⁻¹ + (4 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3) * (b - ((1 - d) / 2))⁻¹ + ((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12) * ((b
  - 0) ^ 2)⁻¹ + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) * ((b - 0) ^ 3)⁻¹ := by
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

theorem ksWY2_kC_2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c48 k80 c49 k84 p100 p104 : ℝ} (hc48 : c48 = 8) (hk80 : k80 = -((b + 1) * (b - 1)
  / 2)) (hc49 : c49 = -8) (hk84 : k84 = -((b - 1) * (b ^ 2 + b + 1)
  / 3)) (hp100 : p100 = -8) (hp104 : p104 = 8) {r : ℝ} (hr : r = ((-4 / 3) * ((1 - d) / 2) ^ 2
  * (2 * ((1 - d) / 2) - 3))) :
    c48 * k80 + c49 * k84 + (1 * p100) * ((((1 + d) / 2) ^ 2
  - b ^ 2) / 2) + (1 * p104) * ((((1 + d) / 2) ^ 3 - b ^ 3) / 3) = r := by
  subst hr hc48 hk80 hc49 hk84 hp100 hp104
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

theorem ksWY2_kC_103 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c108 k135 c109 k138 c2 k141 : ℝ} (hc108 : c108 = -(16 * b)) (hk135 : k135 = 1
  - b) (hc109 : c109 = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) (hk138 : k138 = -((b + 1)
  * (b - 1) / 2)) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk141 : k141 = -((b - 1) * (b ^ 2 + b + 1)
  / 3)) {r : ℝ} (hr : r = ((-4 / 3) * (b - 1) ^ 2 * (4 * b ^ 3 - 5 * b ^ 2 + 4 * b * ((1 - d)
  / 2) ^ 2 - 4 * ((1 - d) / 2) * b + 5 * b + 5 * ((1 - d) / 2) ^ 2 - 5 * ((1 - d) / 2) + 2) / ((b
  - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c108 * k135 + c109 * k138 + c2 * k141 = r := by
  subst hr hc108 hk135 hc109 hk138 hc2 hk141
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

theorem ksWY2_kC_203 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c108 k144 c109 k150 c2 k156 p161 p164 : ℝ} (hc108 : c108 = -(16 * b)) (hk144 : k144 = (d
  - 1) / 2) (hc109 : c109 = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)) (hk150 : k150 = (d - 1) * (d
  + 3) / 8) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk156 : k156 = (d - 1) * (d ^ 2 + 4 * d + 7)
  / 24) (hp161 : p161 = -(16 * b)) (hp164 : p164 = 16 * b) {r : ℝ} (hr : r = ((-4 / 3) * ((1 - d)
  / 2) ^ 2 * (-(2 * ((1 - d) / 2) * b ^ 2) + 3 * b ^ 2 + 2 * ((1 - d) / 2) * b - 3 * b + 10 * ((1
  - d) / 2) ^ 3 - 25 * ((1 - d) / 2) ^ 2 + 19 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1
  + d) / 2)))) :
    c108 * k144 + c109 * k150 + c2 * k156 + (1 * p161) * ((1 ^ 1 - ((1 + d)
  / 2) ^ 1) / 1) + (1 * p164) * ((1 ^ 2 - ((1 + d) / 2) ^ 2) / 2) = r := by
  subst hr hc108 hk144 hc109 hk150 hc2 hk156 hp161 hp164
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

theorem ksWY2_kC_t (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ((-4
  / 3) * ((1 - d) / 2) ^ 2 * (2 * ((1 - d) / 2) - 3)) + ((-4 / 3) * (b - 1) ^ 2 * (4 * b ^ 3 - 5
  * b ^ 2 + 4 * b * ((1 - d) / 2) ^ 2 - 4 * ((1 - d) / 2) * b + 5 * b + 5 * ((1 - d) / 2) ^ 2 - 5
  * ((1 - d) / 2) + 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2))) + ((-4 / 3) * ((1 - d) / 2) ^ 2
  * (-(2 * ((1 - d) / 2) * b ^ 2) + 3 * b ^ 2 + 2 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d)
  / 2) ^ 3 - 25 * ((1 - d) / 2) ^ 2 + 19 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d)
  / 2))) = ((4 * d ^ 2 + 8) / 3) * b ^ 0 + (-((8 * d ^ 2 + 32) / 3)) * b ^ 1 + 12 * b ^ 2 + (-16
  / 3) * b ^ 3 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ := by
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

theorem ksWY2_kM_0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c1 k9 c2 k12 c3 k15 : ℝ} (hc1 : c1 = -((16 * b - 16))) (hk9 : k9 = (d - 1) ^ 2
  / 8) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1))) (hk12 : k12 = (d - 1) ^ 2 / 8) (hc3 : c3 = (8 * ksDT 1 d * b ^ 2
  - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk15 : k15 = -((d - 1) ^ 3 / 24)) {r : ℝ} (hr : r = ((-4 / 3) * ((1 - d) / 2) ^ 2 * (6
  * b ^ 3 - 2 * ((1 - d) / 2) * b ^ 2 - 9 * b ^ 2 - 6 * b * ((1 - d) / 2) ^ 2 + 8 * ((1 - d) / 2)
  * b + 3 * b + 10 * ((1 - d) / 2) ^ 3 - 19 * ((1 - d) / 2) ^ 2 + 13 * ((1 - d) / 2) - 6) / ((b
  - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c1 * k9 + c2 * k12 + c3 * k15 = r := by
  subst hr hc1 hk9 hc2 hk12 hc3 hk15
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

theorem ksWY2_kM_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c48 k52 c49 k56 p70 p71 p74 : ℝ} (hc48 : c48 = 8) (hk52 : k52 = -((d - 1) ^ 2
  / 8)) (hc49 : c49 = -8) (hk56 : k56 = (d - 1) ^ 3 / 24) (hp70 : p70 = (16 * b
  - 16)) (hp71 : p71 = -8) (hp74 : p74 = 8) {r : ℝ} (hr : r = ((4 / 3) * (-(8 * b ^ 3) + 9 * b ^ 2
  + 6 * b * ((1 - d) / 2) ^ 2 + 4 * ((1 - d) / 2) ^ 3 - 12 * ((1 - d) / 2) ^ 2))) :
    c48 * k52
  + c49 * k56 + (-1 * p70 + -1 * p71) * ((b ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (-1 * p74) * ((b ^ 3
  - ((1 - d) / 2) ^ 3) / 3) = r := by
  subst hr hc48 hk52 hc49 hk56 hp70 hp71 hp74
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

end QED.ChainProof.SetAKS

end
