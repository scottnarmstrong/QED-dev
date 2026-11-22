/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBE2B

/-!
# Set (a), stage D: the `β`-integrand on `(σ₋, σ₊)`, rational identities II

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route, range
`β ∈ (σ₋, σ₊)`, part 3 of 4: the rational identities `ksWY2_k*_i`, `ksWY2_k*_t`, second half.
Machine-generated; every coefficient is checked by the proofs.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetAKS

variable {b d : ℝ}

theorem ksWY2_kM_2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c48 k81 c49 k85 p98 p101 p102 p105 : ℝ} (hc48 : c48 = 8) (hk81 : k81 = (d - 1) * (d + 3)
  / 8) (hc49 : c49 = -8) (hk85 : k85 = (d - 1) * (d ^ 2 + 4 * d + 7) / 24) (hp98 : p98 = -(16
  * b)) (hp101 : p101 = 16 * b) (hp102 : p102 = -8) (hp105 : p105 = 8) {r : ℝ} (hr : r = ((4 / 3)
  * (8 * b ^ 3 - 15 * b ^ 2 - 6 * b * ((1 - d) / 2) ^ 2 + 6 * b + 4 * ((1 - d) / 2) ^ 3 - 6 * ((1
  - d) / 2) ^ 2 + 1))) :
    c48 * k81 + c49 * k85 + (-1 * p98) * ((((1 + d) / 2) ^ 1 - b ^ 1)
  / 1) + (-1 * p101 + -1 * p102) * ((((1 + d) / 2) ^ 2 - b ^ 2) / 2) + (-1 * p105) * ((((1 + d)
  / 2) ^ 3 - b ^ 3) / 3) = r := by
  subst hr hc48 hk81 hc49 hk85 hp98 hp101 hp102 hp105
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

theorem ksWY2_kM_3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c107 k114 c108 k117 c2 k128 c3 k131 : ℝ} (hc107 : c107 = 16 * b) (hk114 : k114 = -((d
  - 1) / 2)) (hc108 : c108 = -(16 * b)) (hk117 : k117 = -((d - 1) * (d + 3) / 8)) (hc2 : c2 = -((8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1))) (hk128 : k128 = -((d - 1) * (d + 3) / 8)) (hc3 : c3 = (8 * ksDT 1 d * b ^ 2 - 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk131 : k131 = -((d - 1) * (d ^ 2 + 4 * d + 7) / 24)) {r : ℝ} (hr : r = ((-4 / 3) * ((1
  - d) / 2) ^ 2 * (-(6 * b ^ 3) - 2 * ((1 - d) / 2) * b ^ 2 + 9 * b ^ 2 + 6 * b * ((1 - d)
  / 2) ^ 2 - 4 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 3 - 25 * ((1 - d) / 2) ^ 2 + 19
  * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c107 * k114 + c108 * k117
  + c2 * k128 + c3 * k131 = r := by
  subst hr hc107 hk114 hc108 hk117 hc2 hk128 hc3 hk131
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

theorem ksWY2_kM_100 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c4 k33 c2 k39 p45 : ℝ} (hc4 : c4 = (16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk33 : k33 = (d - 1) ^ 2 / 8) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk39 : k39 = -((d - 1) ^ 3
  / 24)) (hp45 : p45 = (16 * b - 16)) {r : ℝ} (hr : r = ((4 / 3) * ((1 - d) / 2) ^ 2 * (-(2 * ((1
  - d) / 2) * b ^ 2) + 3 * b ^ 2 + 2 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 3 - 25
  * ((1 - d) / 2) ^ 2 + 19 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) :
    c4 * k33 + c2 * k39 + (-1 * p45) * ((((1 - d) / 2) ^ 2 - 0 ^ 2) / 2) = r := by
  subst hr hc4 hk33 hc2 hk39 hp45
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

theorem ksWY2_kM_203 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c108 k145 c109 k151 c2 k157 p162 p165 : ℝ} (hc108 : c108 = -(16
  * b)) (hk145 : k145 = -((d - 1) / 2)) (hc109 : c109 = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d
  * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk151 : k151 = -((d - 1) * (d + 3) / 8)) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1))) (hk157 : k157 = -((d - 1) * (d ^ 2 + 4 * d + 7) / 24)) (hp162 : p162 = -(16
  * b)) (hp165 : p165 = 16 * b) {r : ℝ} (hr : r = ((4 / 3) * ((1 - d) / 2) ^ 2 * (-(2 * ((1 - d)
  / 2) * b ^ 2) + 3 * b ^ 2 + 2 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 3 - 25 * ((1
  - d) / 2) ^ 2 + 19 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c108
  * k145 + c109 * k151 + c2 * k157 + (-1 * p162) * ((1 ^ 1 - ((1 + d) / 2) ^ 1) / 1) + (-1 * p165)
  * ((1 ^ 2 - ((1 + d) / 2) ^ 2) / 2) = r := by
  subst hr hc108 hk145 hc109 hk151 hc2 hk157 hp162 hp165
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

theorem ksWY2_kM_t (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ((-4
  / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 3 - 2 * ((1 - d) / 2) * b ^ 2 - 9 * b ^ 2 - 6 * b * ((1 - d)
  / 2) ^ 2 + 8 * ((1 - d) / 2) * b + 3 * b + 10 * ((1 - d) / 2) ^ 3 - 19 * ((1 - d) / 2) ^ 2 + 13
  * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d) / 2))) + ((4 / 3) * (-(8 * b ^ 3) + 9
  * b ^ 2 + 6 * b * ((1 - d) / 2) ^ 2 + 4 * ((1 - d) / 2) ^ 3 - 12 * ((1 - d) / 2) ^ 2)) + ((4
  / 3) * (8 * b ^ 3 - 15 * b ^ 2 - 6 * b * ((1 - d) / 2) ^ 2 + 6 * b + 4 * ((1 - d) / 2) ^ 3 - 6
  * ((1 - d) / 2) ^ 2 + 1)) + ((-4 / 3) * ((1 - d) / 2) ^ 2 * (-(6 * b ^ 3) - 2 * ((1 - d) / 2)
  * b ^ 2 + 9 * b ^ 2 + 6 * b * ((1 - d) / 2) ^ 2 - 4 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d)
  / 2) ^ 3 - 25 * ((1 - d) / 2) ^ 2 + 19 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d)
  / 2))) + ((4 / 3) * ((1 - d) / 2) ^ 2 * (-(2 * ((1 - d) / 2) * b ^ 2) + 3 * b ^ 2 + 2 * ((1 - d)
  / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 3 - 25 * ((1 - d) / 2) ^ 2 + 19 * ((1 - d) / 2) - 6)
  / ((b - (1 - d) / 2) * (b - (1 + d) / 2))) + ((4 / 3) * ((1 - d) / 2) ^ 2 * (-(2 * ((1 - d) / 2)
  * b ^ 2) + 3 * b ^ 2 + 2 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 3 - 25 * ((1 - d)
  / 2) ^ 2 + 19 * ((1 - d) / 2) - 6) / ((b - (1 - d) / 2) * (b - (1 + d) / 2))) = (-((4 * d ^ 3
  - 12 * d + 4) / 3)) * b ^ 0 + 8 * b ^ 1 + (-8) * b ^ 2 := by
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

theorem ksWY2_kN_0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c2 k18 c3 k22 : ℝ} (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d
  + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk18 : k18 = (d + 1) ^ 2 / 8) (hc3 : c3 = (8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk22 : k22 = (d + 1) ^ 3 / 24) {r : ℝ} (hr : r = ((4 / 3) * ((1 + d) / 2) ^ 2 * (-(2
  * ((1 - d) / 2) * b ^ 2) - b ^ 2 + 2 * ((1 - d) / 2) * b + b + 10 * ((1 - d) / 2) ^ 3 - 5 * ((1
  - d) / 2) ^ 2 - ((1 - d) / 2) + 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c2 * k18
  + c3 * k22 = r := by
  subst hr hc2 hk18 hc3 hk22
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

theorem ksWY2_kN_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {p70 p71 p74 : ℝ} (hp70 : p70 = (16 * b
  - 16)) (hp71 : p71 = -8) (hp74 : p74 = 8) {r : ℝ} (hr : r = ((-4 / 3) * (b - (1 - d) / 2) * (8
  * b ^ 2 + 8 * ((1 - d) / 2) * b - 9 * b + 2 * ((1 - d) / 2) ^ 2 - 9 * ((1 - d) / 2)))) :
    (-1
  * p70 + -1 * p71) * ((b ^ 2 - ((1 - d) / 2) ^ 2) / 2) + (-1 * p74) * ((b ^ 3 - ((1 - d)
  / 2) ^ 3) / 3) = r := by
  subst hr hp70 hp71 hp74
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

theorem ksWY2_kN_2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {p98 p101 p102 p105 : ℝ} (hp98 : p98 = -(16 * b)) (hp101 : p101 = 16
  * b) (hp102 : p102 = -8) (hp105 : p105 = 8) {r : ℝ} (hr : r = ((4 / 3) * (b - (1 + d) / 2) * (8
  * b ^ 2 - 8 * ((1 - d) / 2) * b - 7 * b + 2 * ((1 - d) / 2) ^ 2 - ((1 - d) / 2) - 1))) :
    (-1
  * p98) * ((((1 + d) / 2) ^ 1 - b ^ 1) / 1) + (-1 * p101 + -1 * p102) * ((((1 + d) / 2) ^ 2
  - b ^ 2) / 2) + (-1 * p105) * ((((1 + d) / 2) ^ 3 - b ^ 3) / 3) = r := by
  subst hr hp98 hp101 hp102 hp105
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

theorem ksWY2_kN_3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c2 k120 c3 k124 : ℝ} (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk120 : k120 = -((d + 1) * (d - 3)
  / 8)) (hc3 : c3 = (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1)) (hk124 : k124 = (d + 1) * (d ^ 2 - 4 * d + 7)
  / 24) {r : ℝ} (hr : r = ((4 / 3) * ((1 + d) / 2) ^ 2 * (-(2 * ((1 - d) / 2) * b ^ 2) - b ^ 2 + 2
  * ((1 - d) / 2) * b + b + 10 * ((1 - d) / 2) ^ 3 - 5 * ((1 - d) / 2) ^ 2 - ((1 - d) / 2) + 2)
  / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c2 * k120 + c3 * k124 = r := by
  subst hr hc2 hk120 hc3 hk124
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

theorem ksWY2_kN_10 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c7 : ℝ} (hc7 : c7 = (8 * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56) / (ksDT 1 d ^ 3
  * b ^ 3)) {r : ℝ} (hr : r = ((-8) * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2 + 3 * b + 7
  * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2)) / (b ^ 3))) :
    -1 * c7 = r := by
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

theorem ksWY2_kN_13 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c112 : ℝ} (hc112 : c112 = (8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d - 56)
  / (ksDT 1 d ^ 3 * (b - 1) ^ 3)) {r : ℝ} (hr : r = (8 * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2
  * (b ^ 2 - 5 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2) + 4) / ((b - 1) ^ 3))) :
    1
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

theorem ksWY2_kN_100 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c4 k34 c2 k40 p45 : ℝ} (hc4 : c4 = (16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk34 : k34 = (d + 1) ^ 2 * (d - 1) ^ 2 / (32 * b ^ 2)) (hc2 : c2 = -((8 * ksDT 1 d
  * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1))) (hk40 : k40 = -((d + 1) ^ 3 * (d - 1) ^ 3 / (192 * b ^ 3))) (hp45 : p45 = (16 * b
  - 16)) {r : ℝ} (hr : r = ((-4 / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 6 - 12 * b ^ 5 - 12 * ((1 - d)
  / 2) ^ 2 * b ^ 4 + 18 * ((1 - d) / 2) * b ^ 4 + 15 * ((1 - d) / 2) ^ 2 * b ^ 3 - 24 * ((1 - d)
  / 2) * b ^ 3 + 9 * b ^ 3 + 4 * ((1 - d) / 2) ^ 4 * b ^ 2 - 12 * ((1 - d) / 2) ^ 3 * b ^ 2 + 9
  * ((1 - d) / 2) ^ 2 * b ^ 2 + 2 * ((1 - d) / 2) * b ^ 2 - 3 * b ^ 2 + 11 * b * ((1 - d) / 2) ^ 4
  - 33 * b * ((1 - d) / 2) ^ 3 + 39 * b * ((1 - d) / 2) ^ 2 - 23 * ((1 - d) / 2) * b + 6 * b + 10
  * ((1 - d) / 2) ^ 6 - 40 * ((1 - d) / 2) ^ 5 + 64 * ((1 - d) / 2) ^ 4 - 52 * ((1 - d) / 2) ^ 3
  + 22 * ((1 - d) / 2) ^ 2 - 4 * ((1 - d) / 2)) / (b ^ 3 * (b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) :
    c4 * k34 + c2 * k40 + (-1 * p45) * ((((1 - d) / 2) ^ 2 - 0 ^ 2) / 2) = r := by
  subst hr hc4 hk34 hc2 hk40 hp45
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

theorem ksWY2_kN_203 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c108 k146 c109 k152 c2 k158 p162 p165 : ℝ} (hc108 : c108 = -(16 * b)) (hk146 : k146 = (d
  + 1) * (d - 1) / (4 * b - 4)) (hc109 : c109 = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk152 : k152 = (d + 1) * (d - 1) * (8 * b - d ^ 2 - 7) / (32 * (b
  - 1) ^ 2)) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk158 : k158 = (d + 1) * (d - 1) * (48 * b ^ 2 - 12
  * b * d ^ 2 - 84 * b + d ^ 4 + 10 * d ^ 2 + 37) / (192 * (b - 1) ^ 3)) (hp162 : p162 = -(16
  * b)) (hp165 : p165 = 16 * b) {r : ℝ} (hr : r = ((4 / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 6 - 24
  * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4 + 18 * ((1 - d) / 2) * b ^ 4 + 30 * b ^ 4 + 33 * ((1
  - d) / 2) ^ 2 * b ^ 3 - 48 * ((1 - d) / 2) * b ^ 3 - 9 * b ^ 3 + 4 * ((1 - d) / 2) ^ 4 * b ^ 2
  - 12 * ((1 - d) / 2) ^ 3 * b ^ 2 - 18 * ((1 - d) / 2) ^ 2 * b ^ 2 + 38 * ((1 - d) / 2) * b ^ 2
  - 6 * b ^ 2 - 19 * b * ((1 - d) / 2) ^ 4 + 57 * b * ((1 - d) / 2) ^ 3 - 54 * b * ((1 - d)
  / 2) ^ 2 + 19 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 6 - 40 * ((1 - d) / 2) ^ 5 + 79
  * ((1 - d) / 2) ^ 4 - 97 * ((1 - d) / 2) ^ 3 + 73 * ((1 - d) / 2) ^ 2 - 31 * ((1 - d) / 2) + 6)
  / ((b - 1) ^ 3 * (b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c108 * k146 + c109 * k152 + c2
  * k158 + (-1 * p162) * ((1 ^ 1 - ((1 + d) / 2) ^ 1) / 1) + (-1 * p165) * ((1 ^ 2 - ((1 + d)
  / 2) ^ 2) / 2) = r := by
  subst hr hc108 hk146 hc109 hk152 hc2 hk158 hp162 hp165
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

theorem ksWY2_kN_t (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ((4
  / 3) * ((1 + d) / 2) ^ 2 * (-(2 * ((1 - d) / 2) * b ^ 2) - b ^ 2 + 2 * ((1 - d) / 2) * b + b
  + 10 * ((1 - d) / 2) ^ 3 - 5 * ((1 - d) / 2) ^ 2 - ((1 - d) / 2) + 2) / ((b - (1 - d) / 2) * (b
  - (1 + d) / 2))) + ((-4 / 3) * (b - (1 - d) / 2) * (8 * b ^ 2 + 8 * ((1 - d) / 2) * b - 9 * b
  + 2 * ((1 - d) / 2) ^ 2 - 9 * ((1 - d) / 2))) + ((4 / 3) * (b - (1 + d) / 2) * (8 * b ^ 2 - 8
  * ((1 - d) / 2) * b - 7 * b + 2 * ((1 - d) / 2) ^ 2 - ((1 - d) / 2) - 1)) + ((4 / 3) * ((1 + d)
  / 2) ^ 2 * (-(2 * ((1 - d) / 2) * b ^ 2) - b ^ 2 + 2 * ((1 - d) / 2) * b + b + 10 * ((1 - d)
  / 2) ^ 3 - 5 * ((1 - d) / 2) ^ 2 - ((1 - d) / 2) + 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))
  + ((-8) * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2 + 3 * b + 7 * ((1 - d) / 2) ^ 2 - 7
  * ((1 - d) / 2)) / (b ^ 3)) + (8 * ((1 + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2 - 5 * b + 7
  * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2) + 4) / ((b - 1) ^ 3)) + ((-4 / 3) * ((1 - d) / 2) ^ 2
  * (6 * b ^ 6 - 12 * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4 + 18 * ((1 - d) / 2) * b ^ 4 + 15
  * ((1 - d) / 2) ^ 2 * b ^ 3 - 24 * ((1 - d) / 2) * b ^ 3 + 9 * b ^ 3 + 4 * ((1 - d) / 2) ^ 4
  * b ^ 2 - 12 * ((1 - d) / 2) ^ 3 * b ^ 2 + 9 * ((1 - d) / 2) ^ 2 * b ^ 2 + 2 * ((1 - d) / 2)
  * b ^ 2 - 3 * b ^ 2 + 11 * b * ((1 - d) / 2) ^ 4 - 33 * b * ((1 - d) / 2) ^ 3 + 39 * b * ((1
  - d) / 2) ^ 2 - 23 * ((1 - d) / 2) * b + 6 * b + 10 * ((1 - d) / 2) ^ 6 - 40 * ((1 - d) / 2) ^ 5
  + 64 * ((1 - d) / 2) ^ 4 - 52 * ((1 - d) / 2) ^ 3 + 22 * ((1 - d) / 2) ^ 2 - 4 * ((1 - d) / 2))
  / (b ^ 3 * (b - (1 - d) / 2) * (b - (1 + d) / 2))) + ((4 / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 6
  - 24 * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4 + 18 * ((1 - d) / 2) * b ^ 4 + 30 * b ^ 4 + 33
  * ((1 - d) / 2) ^ 2 * b ^ 3 - 48 * ((1 - d) / 2) * b ^ 3 - 9 * b ^ 3 + 4 * ((1 - d) / 2) ^ 4
  * b ^ 2 - 12 * ((1 - d) / 2) ^ 3 * b ^ 2 - 18 * ((1 - d) / 2) ^ 2 * b ^ 2 + 38 * ((1 - d) / 2)
  * b ^ 2 - 6 * b ^ 2 - 19 * b * ((1 - d) / 2) ^ 4 + 57 * b * ((1 - d) / 2) ^ 3 - 54 * b * ((1
  - d) / 2) ^ 2 + 19 * ((1 - d) / 2) * b - 3 * b + 10 * ((1 - d) / 2) ^ 6 - 40 * ((1 - d) / 2) ^ 5
  + 79 * ((1 - d) / 2) ^ 4 - 97 * ((1 - d) / 2) ^ 3 + 73 * ((1 - d) / 2) ^ 2 - 31 * ((1 - d) / 2)
  + 6) / ((b - 1) ^ 3 * (b - (1 - d) / 2) * (b - (1 + d) / 2))) = (-4 / 3) * b ^ 0 + 8 * b ^ 1
  + (-8) * b ^ 2 + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 + d) / 2))⁻¹ + (2 * (d ^ 2
  + 1) * (d ^ 2 - 3) / 3) * (b - ((1 - d) / 2))⁻¹ + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b
  - 1)⁻¹ + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - 0)⁻¹ + (-((d + 1) * (d - 1) * (17 * d ^ 2
  - 25) / 12)) * ((b - 1) ^ 2)⁻¹ + (-((d + 1) * (d - 1) * (17 * d ^ 2 - 25) / 12)) * ((b
  - 0) ^ 2)⁻¹ + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) * ((b - 1) ^ 3)⁻¹ + (-((d
  + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)) * ((b - 0) ^ 3)⁻¹ := by
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

theorem ksWY2_kK_0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c1 k10 c2 k13 c3 k16 k19 k23 : ℝ} (hc1 : c1 = -((16 * b - 16))) (hk10 : k10 = -((d
  - 1) ^ 2 / 8)) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk13 : k13 = -((d - 1) ^ 2 / 8)) (hc3 : c3 = (8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk16 : k16 = (d - 1) ^ 3 / 24) (hk19 : k19 = -((d + 1) ^ 2 / 8)) (hk23 : k23 = -((d
  + 1) ^ 3 / 24)) {r : ℝ} (hr : r = ((-4 / 3) * (-(6 * ((1 - d) / 2) ^ 2 * b ^ 3) + 12 * ((1 - d)
  / 2) ^ 2 * b ^ 2 - b ^ 2 + 6 * b * ((1 - d) / 2) ^ 4 - 6 * b * ((1 - d) / 2) ^ 3 - 6 * b * ((1
  - d) / 2) ^ 2 + b - 6 * ((1 - d) / 2) ^ 4 + 6 * ((1 - d) / 2) ^ 3 + 5 * ((1 - d) / 2) ^ 2 - 5
  * ((1 - d) / 2) + 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c1 * k10 + c2 * k13 + c3
  * k16 + c2 * k19 + c3 * k23 = r := by
  subst hr hc1 hk10 hc2 hk13 hc3 hk16 hk19 hk23
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

theorem ksWY2_kK_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c48 k53 c49 k57 p70 p71 p74 : ℝ} (hc48 : c48 = 8) (hk53 : k53 = (d - 1) ^ 2
  / 8) (hc49 : c49 = -8) (hk57 : k57 = -((d - 1) ^ 3 / 24)) (hp70 : p70 = (16 * b
  - 16)) (hp71 : p71 = -8) (hp74 : p74 = 8) {r : ℝ} (hr : r = ((-4 / 3) * (-(16 * b ^ 3) + 18
  * b ^ 2 + 12 * b * ((1 - d) / 2) ^ 2 + 6 * ((1 - d) / 2) ^ 3 - 21 * ((1 - d)
  / 2) ^ 2))) :
    c48 * k53 + c49 * k57 + (2 * p70 + 2 * p71) * ((b ^ 2 - ((1 - d) / 2) ^ 2)
  / 2) + (2 * p74) * ((b ^ 3 - ((1 - d) / 2) ^ 3) / 3) = r := by
  subst hr hc48 hk53 hc49 hk57 hp70 hp71 hp74
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

theorem ksWY2_kK_2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c48 k82 c49 k86 p98 p101 p102 p105 : ℝ} (hc48 : c48 = 8) (hk82 : k82 = -((d - 1) * (d
  + 3) / 8)) (hc49 : c49 = -8) (hk86 : k86 = -((d - 1) * (d ^ 2 + 4 * d + 7)
  / 24)) (hp98 : p98 = -(16 * b)) (hp101 : p101 = 16
  * b) (hp102 : p102 = -8) (hp105 : p105 = 8) {r : ℝ} (hr : r = ((-4 / 3) * (16 * b ^ 3 - 30
  * b ^ 2 - 12 * b * ((1 - d) / 2) ^ 2 + 12 * b + 6 * ((1 - d) / 2) ^ 3 - 9 * ((1 - d) / 2) ^ 2
  + 2))) :
    c48 * k82 + c49 * k86 + (2 * p98) * ((((1 + d) / 2) ^ 1 - b ^ 1) / 1) + (2 * p101
  + 2 * p102) * ((((1 + d) / 2) ^ 2 - b ^ 2) / 2) + (2 * p105) * ((((1 + d) / 2) ^ 3 - b ^ 3)
  / 3) = r := by
  subst hr hc48 hk82 hc49 hk86 hp98 hp101 hp102 hp105
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

theorem ksWY2_kK_3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c107 k115 c108 k118 c2 k121 c3 k125 k129 k132 : ℝ} (hc107 : c107 = 16
  * b) (hk115 : k115 = (d - 1) / 2) (hc108 : c108 = -(16 * b)) (hk118 : k118 = (d - 1) * (d + 3)
  / 8) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1))) (hk121 : k121 = (d + 1) * (d - 3) / 8) (hc3 : c3 = (8 * ksDT 1 d
  * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk125 : k125 = -((d + 1) * (d ^ 2 - 4 * d + 7) / 24)) (hk129 : k129 = (d - 1) * (d + 3)
  / 8) (hk132 : k132 = (d - 1) * (d ^ 2 + 4 * d + 7) / 24) {r : ℝ} (hr : r = ((4 / 3) * (-(6 * ((1
  - d) / 2) ^ 2 * b ^ 3) + 6 * ((1 - d) / 2) ^ 2 * b ^ 2 + b ^ 2 + 6 * b * ((1 - d) / 2) ^ 4 - 6
  * b * ((1 - d) / 2) ^ 3 - b - 5 * ((1 - d) / 2) ^ 2 + 5 * ((1 - d) / 2) - 2) / ((b - (1 - d)
  / 2) * (b - (1 + d) / 2)))) :
    c107 * k115 + c108 * k118 + c2 * k121 + c3 * k125 + c2 * k129
  + c3 * k132 = r := by
  subst hr hc107 hk115 hc108 hk118 hc2 hk121 hc3 hk125 hk129 hk132
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

theorem ksWY2_kK_10 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
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

theorem ksWY2_kK_13 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
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

theorem ksWY2_kK_100 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c4 k35 c2 k41 p45 : ℝ} (hc4 : c4 = (16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8
  * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk35 : k35 = -((d - 1) ^ 2 * (4 * b ^ 2 + d ^ 2 + 2 * d + 1) / (32
  * b ^ 2))) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40)
  / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk41 : k41 = (d - 1) ^ 3 * (2 * b + d + 1) * (4
  * b ^ 2 - 2 * b * d - 2 * b + d ^ 2 + 2 * d + 1) / (192 * b ^ 3)) (hp45 : p45 = (16 * b
  - 16)) {r : ℝ} (hr : r = ((4 / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 6 + 2 * ((1 - d) / 2) * b ^ 5
  - 15 * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4 + 16 * ((1 - d) / 2) * b ^ 4 + 3 * b ^ 4 - 10
  * ((1 - d) / 2) ^ 3 * b ^ 3 + 40 * ((1 - d) / 2) ^ 2 * b ^ 3 - 43 * ((1 - d) / 2) * b ^ 3 + 15
  * b ^ 3 + 4 * ((1 - d) / 2) ^ 4 * b ^ 2 - 12 * ((1 - d) / 2) ^ 3 * b ^ 2 + 9 * ((1 - d) / 2) ^ 2
  * b ^ 2 + 2 * ((1 - d) / 2) * b ^ 2 - 3 * b ^ 2 + 11 * b * ((1 - d) / 2) ^ 4 - 33 * b * ((1 - d)
  / 2) ^ 3 + 39 * b * ((1 - d) / 2) ^ 2 - 23 * ((1 - d) / 2) * b + 6 * b + 10 * ((1 - d) / 2) ^ 6
  - 40 * ((1 - d) / 2) ^ 5 + 64 * ((1 - d) / 2) ^ 4 - 52 * ((1 - d) / 2) ^ 3 + 22 * ((1 - d)
  / 2) ^ 2 - 4 * ((1 - d) / 2)) / (b ^ 3 * (b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c4 * k35
  + c2 * k41 + (2 * p45) * ((((1 - d) / 2) ^ 2 - 0 ^ 2) / 2) = r := by
  subst hr hc4 hk35 hc2 hk41 hp45
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

theorem ksWY2_kK_203 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c108 k147 c109 k153 c2 k159 p162 p165 : ℝ} (hc108 : c108 = -(16 * b)) (hk147 : k147 = (d
  - 1) * (2 * b - d - 3) / (4 * b - 4)) (hc109 : c109 = (16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d
  * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk153 : k153 = (d - 1) * (4 * d * b ^ 2 + 12 * b ^ 2 - 16 * b * d - 32 * b + d ^ 3
  + d ^ 2 + 11 * d + 19) / (32 * (b - 1) ^ 2)) (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d
  * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk159 : k159 = (d - 1) * (8
  * b ^ 3 * d ^ 2 + 32 * d * b ^ 3 + 56 * b ^ 3 - 24 * b ^ 2 * d ^ 2 - 144 * d * b ^ 2 - 216
  * b ^ 2 + 12 * b * d ^ 3 + 36 * b * d ^ 2 + 180 * b * d + 252 * b - d ^ 5 - d ^ 4 - 10 * d ^ 3
  - 18 * d ^ 2 - 69 * d - 93) / (192 * (b - 1) ^ 3)) (hp162 : p162 = -(16 * b)) (hp165 : p165 = 16
  * b) {r : ℝ} (hr : r = ((-4 / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 6 - 2 * ((1 - d) / 2) * b ^ 5
  - 21 * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4 + 26 * ((1 - d) / 2) * b ^ 4 + 18 * b ^ 4 + 10
  * ((1 - d) / 2) ^ 3 * b ^ 3 + 8 * ((1 - d) / 2) ^ 2 * b ^ 3 - 41 * ((1 - d) / 2) * b ^ 3 + 3
  * b ^ 3 + 4 * ((1 - d) / 2) ^ 4 * b ^ 2 - 42 * ((1 - d) / 2) ^ 3 * b ^ 2 + 57 * ((1 - d)
  / 2) ^ 2 * b ^ 2 - 11 * ((1 - d) / 2) * b ^ 2 - 19 * b * ((1 - d) / 2) ^ 4 + 87 * b * ((1 - d)
  / 2) ^ 3 - 129 * b * ((1 - d) / 2) ^ 2 + 74 * ((1 - d) / 2) * b - 18 * b + 10 * ((1 - d)
  / 2) ^ 6 - 40 * ((1 - d) / 2) ^ 5 + 79 * ((1 - d) / 2) ^ 4 - 107 * ((1 - d) / 2) ^ 3 + 98 * ((1
  - d) / 2) ^ 2 - 50 * ((1 - d) / 2) + 12) / ((b - 1) ^ 3 * (b - (1 - d) / 2) * (b - (1 + d)
  / 2)))) :
    c108 * k147 + c109 * k153 + c2 * k159 + (2 * p162) * ((1 ^ 1 - ((1 + d) / 2) ^ 1)
  / 1) + (2 * p165) * ((1 ^ 2 - ((1 + d) / 2) ^ 2) / 2) = r := by
  subst hr hc108 hk147 hc109 hk153 hc2 hk159 hp162 hp165
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

theorem ksWY2_kK_t (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ((-4
  / 3) * (-(6 * ((1 - d) / 2) ^ 2 * b ^ 3) + 12 * ((1 - d) / 2) ^ 2 * b ^ 2 - b ^ 2 + 6 * b * ((1
  - d) / 2) ^ 4 - 6 * b * ((1 - d) / 2) ^ 3 - 6 * b * ((1 - d) / 2) ^ 2 + b - 6 * ((1 - d)
  / 2) ^ 4 + 6 * ((1 - d) / 2) ^ 3 + 5 * ((1 - d) / 2) ^ 2 - 5 * ((1 - d) / 2) + 2) / ((b - (1
  - d) / 2) * (b - (1 + d) / 2))) + ((-4 / 3) * (-(16 * b ^ 3) + 18 * b ^ 2 + 12 * b * ((1 - d)
  / 2) ^ 2 + 6 * ((1 - d) / 2) ^ 3 - 21 * ((1 - d) / 2) ^ 2)) + ((-4 / 3) * (16 * b ^ 3 - 30
  * b ^ 2 - 12 * b * ((1 - d) / 2) ^ 2 + 12 * b + 6 * ((1 - d) / 2) ^ 3 - 9 * ((1 - d) / 2) ^ 2
  + 2)) + ((4 / 3) * (-(6 * ((1 - d) / 2) ^ 2 * b ^ 3) + 6 * ((1 - d) / 2) ^ 2 * b ^ 2 + b ^ 2 + 6
  * b * ((1 - d) / 2) ^ 4 - 6 * b * ((1 - d) / 2) ^ 3 - b - 5 * ((1 - d) / 2) ^ 2 + 5 * ((1 - d)
  / 2) - 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2))) + (8 * ((1 + d) / 2) ^ 2 * ((1 - d)
  / 2) ^ 2 * (b ^ 2 + 3 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2)) / (b ^ 3)) + ((-8) * ((1
  + d) / 2) ^ 2 * ((1 - d) / 2) ^ 2 * (b ^ 2 - 5 * b + 7 * ((1 - d) / 2) ^ 2 - 7 * ((1 - d) / 2)
  + 4) / ((b - 1) ^ 3)) + ((4 / 3) * ((1 - d) / 2) ^ 2 * (6 * b ^ 6 + 2 * ((1 - d) / 2) * b ^ 5
  - 15 * b ^ 5 - 12 * ((1 - d) / 2) ^ 2 * b ^ 4 + 16 * ((1 - d) / 2) * b ^ 4 + 3 * b ^ 4 - 10
  * ((1 - d) / 2) ^ 3 * b ^ 3 + 40 * ((1 - d) / 2) ^ 2 * b ^ 3 - 43 * ((1 - d) / 2) * b ^ 3 + 15
  * b ^ 3 + 4 * ((1 - d) / 2) ^ 4 * b ^ 2 - 12 * ((1 - d) / 2) ^ 3 * b ^ 2 + 9 * ((1 - d) / 2) ^ 2
  * b ^ 2 + 2 * ((1 - d) / 2) * b ^ 2 - 3 * b ^ 2 + 11 * b * ((1 - d) / 2) ^ 4 - 33 * b * ((1 - d)
  / 2) ^ 3 + 39 * b * ((1 - d) / 2) ^ 2 - 23 * ((1 - d) / 2) * b + 6 * b + 10 * ((1 - d) / 2) ^ 6
  - 40 * ((1 - d) / 2) ^ 5 + 64 * ((1 - d) / 2) ^ 4 - 52 * ((1 - d) / 2) ^ 3 + 22 * ((1 - d)
  / 2) ^ 2 - 4 * ((1 - d) / 2)) / (b ^ 3 * (b - (1 - d) / 2) * (b - (1 + d) / 2))) + ((-4 / 3)
  * ((1 - d) / 2) ^ 2 * (6 * b ^ 6 - 2 * ((1 - d) / 2) * b ^ 5 - 21 * b ^ 5 - 12 * ((1 - d)
  / 2) ^ 2 * b ^ 4 + 26 * ((1 - d) / 2) * b ^ 4 + 18 * b ^ 4 + 10 * ((1 - d) / 2) ^ 3 * b ^ 3 + 8
  * ((1 - d) / 2) ^ 2 * b ^ 3 - 41 * ((1 - d) / 2) * b ^ 3 + 3 * b ^ 3 + 4 * ((1 - d) / 2) ^ 4
  * b ^ 2 - 42 * ((1 - d) / 2) ^ 3 * b ^ 2 + 57 * ((1 - d) / 2) ^ 2 * b ^ 2 - 11 * ((1 - d) / 2)
  * b ^ 2 - 19 * b * ((1 - d) / 2) ^ 4 + 87 * b * ((1 - d) / 2) ^ 3 - 129 * b * ((1 - d) / 2) ^ 2
  + 74 * ((1 - d) / 2) * b - 18 * b + 10 * ((1 - d) / 2) ^ 6 - 40 * ((1 - d) / 2) ^ 5 + 79 * ((1
  - d) / 2) ^ 4 - 107 * ((1 - d) / 2) ^ 3 + 98 * ((1 - d) / 2) ^ 2 - 50 * ((1 - d) / 2) + 12)
  / ((b - 1) ^ 3 * (b - (1 - d) / 2) * (b - (1 + d) / 2))) = (4 * (d - 1) ^ 2 * (d + 2) / 3)
  * b ^ 0 + (-16) * b ^ 1 + 16 * b ^ 2 + (2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * (b - ((1 + d)
  / 2))⁻¹ + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - ((1 - d) / 2))⁻¹ + (2 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3) * (b - 1)⁻¹ + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * (b - 0)⁻¹ + ((d + 1)
  * (d - 1) * (17 * d ^ 2 - 25) / 12) * ((b - 1) ^ 2)⁻¹ + ((d + 1) * (d - 1) * (17 * d ^ 2 - 25)
  / 12) * ((b - 0) ^ 2)⁻¹ + (-((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)) * ((b - 1) ^ 3)⁻¹
  + ((d + 1) ^ 2 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) * ((b - 0) ^ 3)⁻¹ := by
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

theorem ksWY2_kD_0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c2 k20 c3 k24 : ℝ} (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d
  + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk20 : k20 = -(d / 2)) (hc3 : c3 = (8
  * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b
  + 1)) (hk24 : k24 = -(d * (d ^ 2 + 3) / 12)) {r : ℝ} (hr : r = ((4 / 3) * d * (-(2 * ((1 - d)
  / 2) ^ 2 * b ^ 2) + 2 * ((1 - d) / 2) * b ^ 2 + b ^ 2 + 2 * b * ((1 - d) / 2) ^ 2 - 2 * ((1 - d)
  / 2) * b - b + 10 * ((1 - d) / 2) ^ 4 - 20 * ((1 - d) / 2) ^ 3 + 9 * ((1 - d) / 2) ^ 2 + ((1
  - d) / 2) - 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c2 * k20 + c3 * k24 = r := by
  subst hr hc2 hk20 hc3 hk24
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

theorem ksWY2_kD_1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c49 k65 c48 k68 : ℝ} (hc49 : c49 = -8) (hk65 : k65 = d
  / 2) (hc48 : c48 = 8) (hk68 : k68 = d * (d ^ 2 + 3) / 12) {r : ℝ} (hr : r = ((4 / 3) * d * (2
  * ((1 - d) / 2) ^ 2 - 2 * ((1 - d) / 2) - 1))) :
    c49 * k65 + c48 * k68 = r := by
  subst hr hc49 hk65 hc48 hk68
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

theorem ksWY2_kD_2 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c49 k89 c48 k92 : ℝ} (hc49 : c49 = -8) (hk89 : k89 = d
  / 2) (hc48 : c48 = 8) (hk92 : k92 = d * (d ^ 2 + 3) / 12) {r : ℝ} (hr : r = ((4 / 3) * d * (2
  * ((1 - d) / 2) ^ 2 - 2 * ((1 - d) / 2) - 1))) :
    c49 * k89 + c48 * k92 = r := by
  subst hr hc49 hk89 hc48 hk92
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

theorem ksWY2_kD_3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d)
  / 2)) {c2 k122 c3 k126 : ℝ} (hc2 : c2 = -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16
  * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1))) (hk122 : k122 = -(d
  / 2)) (hc3 : c3 = (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d
  * b ^ 2 - ksDT 1 d * b + 1)) (hk126 : k126 = -(d * (d ^ 2 + 3) / 12)) {r : ℝ} (hr : r = ((4 / 3)
  * d * (-(2 * ((1 - d) / 2) ^ 2 * b ^ 2) + 2 * ((1 - d) / 2) * b ^ 2 + b ^ 2 + 2 * b * ((1 - d)
  / 2) ^ 2 - 2 * ((1 - d) / 2) * b - b + 10 * ((1 - d) / 2) ^ 4 - 20 * ((1 - d) / 2) ^ 3 + 9 * ((1
  - d) / 2) ^ 2 + ((1 - d) / 2) - 2) / ((b - (1 - d) / 2) * (b - (1 + d) / 2)))) :
    c2 * k122
  + c3 * k126 = r := by
  subst hr hc2 hk122 hc3 hk126
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
