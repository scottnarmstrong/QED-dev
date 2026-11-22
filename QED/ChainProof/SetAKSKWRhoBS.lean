/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBW
public import QED.ChainProof.SetAKSKWRhoBD

/-!
# Set (a), stage D: logarithms at the nodes of the `β`-integrand

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. The
`w`-integrated `VB` density `ksWWE β δ` contains logarithms of differences of the points `0`, `1`,
`σ± = (1 ± δ)/2`, `β` and the poles `w₀ = 1 - 1/((1-β)T)`, `w₁ = 1/(βT)` (`T = 4/(1-δ²)`). This
file rewrites them into the logarithms of `β`, `1 - β`, `β - σ±`, `δ`, `1 ± δ`, `2`, through the
factorizations `σ₊ - w₀ = σ₋(β - σ₋)/(1-β)`, `σ₋ - w₀ = σ₊(β - σ₊)/(1-β)`,
`σ₋ - w₁ = σ₋(β - σ₊)/β`, `σ₊ - w₁ = σ₊(β - σ₋)/β`.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetAKS

variable {b d : ℝ}

theorem ksWY_log_l1 (hd : d < 1) : log ((1 + d) / 2 - 1) = log (1 - d) - log 2 := by
  rw [show (1 + d) / 2 - 1 = -((1 - d) / 2) by ring, log_neg_eq_log,
    log_div (by linarith) two_ne_zero]

theorem ksWY_log_l2 (hd : -1 < d) : log ((1 - d) / 2 - 1) = log (1 + d) - log 2 := by
  rw [show (1 - d) / 2 - 1 = -((1 + d) / 2) by ring, log_neg_eq_log,
    log_div (by linarith) two_ne_zero]

theorem ksWY_log_l3 : log ((1 + d) / 2 - (1 - d) / 2) = log d := by ring_nf

theorem ksWY_log_l4 : log ((1 - d) / 2 - (1 + d) / 2) = log d := by
  rw [show (1 - d) / 2 - (1 + d) / 2 = -d by ring, log_neg_eq_log]

theorem ksWY_log_l5 (hd : -1 < d) : log (1 - (1 - d) / 2) = log (1 + d) - log 2 := by
  rw [show 1 - (1 - d) / 2 = (1 + d) / 2 by ring, log_div (by linarith) two_ne_zero]

theorem ksWY_log_l6 (hd : d < 1) : log (1 - (1 + d) / 2) = log (1 - d) - log 2 := by
  rw [show 1 - (1 + d) / 2 = (1 - d) / 2 by ring, log_div (by linarith) two_ne_zero]

theorem ksWY_log_swap (x y : ℝ) : log (x - y) = log (y - x) := by
  rw [← neg_sub, log_neg_eq_log]

theorem ksWY_ksDT_eq (d : ℝ) : ksDT 1 d = 4 / ((1 - d) * (1 + d)) := by
  unfold ksDT
  ring

theorem ksWY_sp_sub_w0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ≠ 1) :
    (1 + d) / 2 - (1 - 1 / ((1 - b) * ksDT 1 d)) = (1 - d) / 2 * (b - (1 - d) / 2) / (1 - b) := by
  have h1 : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  have h2 : 1 - d ≠ 0 := by linarith [hd.2]
  have h3 : 1 + d ≠ 0 := by linarith [hd.1]
  rw [ksWY_ksDT_eq]
  field_simp
  ring

theorem ksWY_sm_sub_w0 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ≠ 1) :
    (1 - d) / 2 - (1 - 1 / ((1 - b) * ksDT 1 d)) = (1 + d) / 2 * (b - (1 + d) / 2) / (1 - b) := by
  have h1 : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  have h2 : 1 - d ≠ 0 := by linarith [hd.2]
  have h3 : 1 + d ≠ 0 := by linarith [hd.1]
  rw [ksWY_ksDT_eq]
  field_simp
  ring

theorem ksWY_log_w0p (hd : d ∈ Ioo (0 : ℝ) 1) (hm : b ≠ (1 - d) / 2) (hb : b ≠ 1) :
    log ((1 - d) / 2 * (b - (1 - d) / 2) / (1 - b)) =
      log (1 - d) - log 2 + log (b - (1 - d) / 2) - log (1 - b) := by
  have h2 : (1 - d) / 2 ≠ 0 := by linarith [hd.2]
  rw [log_div (mul_ne_zero h2 (sub_ne_zero.2 hm)) (sub_ne_zero.2 (Ne.symm hb)),
    log_mul h2 (sub_ne_zero.2 hm), log_div (by linarith [hd.2]) two_ne_zero]

theorem ksWY_log_w0m (hd : d ∈ Ioo (0 : ℝ) 1) (hp : b ≠ (1 + d) / 2) (hb : b ≠ 1) :
    log ((1 + d) / 2 * (b - (1 + d) / 2) / (1 - b)) =
      log (1 + d) - log 2 + log (b - (1 + d) / 2) - log (1 - b) := by
  have h2 : (1 + d) / 2 ≠ 0 := by linarith [hd.1]
  rw [log_div (mul_ne_zero h2 (sub_ne_zero.2 hp)) (sub_ne_zero.2 (Ne.symm hb)),
    log_mul h2 (sub_ne_zero.2 hp), log_div (by linarith [hd.1]) two_ne_zero]

theorem ksWY_log_ksDT (hd : d ∈ Ioo (0 : ℝ) 1) :
    log (ksDT 1 d) = 2 * log 2 - log (1 - d) - log (1 + d) := by
  rw [ksWY_ksDT_eq, log_div (by norm_num) (mul_ne_zero (by linarith [hd.2]) (by linarith [hd.1])),
    log_mul (by linarith [hd.2]) (by linarith [hd.1]), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.log_pow]
  push_cast
  ring

theorem ksWY_log_ksDA (hd : d ∈ Ioo (0 : ℝ) 1) (hm : b ≠ (1 - d) / 2) (hp : b ≠ (1 + d) / 2) :
    log (ksDA 1 (-ksDT 1 d) b) =
      2 * log 2 - log (1 - d) - log (1 + d) + log (b - (1 - d) / 2) + log (b - (1 + d) / 2) := by
  have hT : ksDT 1 d ≠ 0 := (ksWW_T_pos hd).ne'
  rw [ksWW_ksDA_eq hd, log_mul hT (mul_ne_zero (sub_ne_zero.2 hm) (sub_ne_zero.2 hp)),
    log_mul (sub_ne_zero.2 hm) (sub_ne_zero.2 hp), ksWY_log_ksDT hd]
  ring

theorem ksWY_ksDT_quad (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1 = ksDT 1 d * ((b - (1 - d) / 2) * (b - (1 + d) / 2)) := by
  have h2 : 1 - d ≠ 0 := by linarith [hd.2]
  have h3 : 1 + d ≠ 0 := by linarith [hd.1]
  rw [ksWY_ksDT_eq]
  field_simp
  ring

theorem ksWY_log_sm (hd : d < 1) : log ((1 - d) / 2) = log (1 - d) - log 2 :=
  log_div (by linarith) two_ne_zero

theorem ksWY_log_sp (hd : -1 < d) : log ((1 + d) / 2) = log (1 + d) - log 2 :=
  log_div (by linarith) two_ne_zero

theorem ksWY_sm_sub_w1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ≠ 0) :
    (1 - d) / 2 - 1 / (b * ksDT 1 d) = (1 - d) / 2 * (b - (1 + d) / 2) / b := by
  have h2 : 1 - d ≠ 0 := by linarith [hd.2]
  have h3 : 1 + d ≠ 0 := by linarith [hd.1]
  rw [ksWY_ksDT_eq]
  field_simp
  ring

theorem ksWY_sp_sub_w1 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ≠ 0) :
    (1 + d) / 2 - 1 / (b * ksDT 1 d) = (1 + d) / 2 * (b - (1 - d) / 2) / b := by
  have h2 : 1 - d ≠ 0 := by linarith [hd.2]
  have h3 : 1 + d ≠ 0 := by linarith [hd.1]
  rw [ksWY_ksDT_eq]
  field_simp
  ring

theorem ksWY_log_w1m (hd : d ∈ Ioo (0 : ℝ) 1) (hp : b ≠ (1 + d) / 2) (hb : b ≠ 0) :
    log ((1 - d) / 2 * (b - (1 + d) / 2) / b) =
      log (1 - d) - log 2 + log (b - (1 + d) / 2) - log b := by
  have h2 : (1 - d) / 2 ≠ 0 := by linarith [hd.2]
  rw [log_div (mul_ne_zero h2 (sub_ne_zero.2 hp)) hb, log_mul h2 (sub_ne_zero.2 hp),
    log_div (by linarith [hd.2]) two_ne_zero]

theorem ksWY_log_w1p (hd : d ∈ Ioo (0 : ℝ) 1) (hm : b ≠ (1 - d) / 2) (hb : b ≠ 0) :
    log ((1 + d) / 2 * (b - (1 - d) / 2) / b) =
      log (1 + d) - log 2 + log (b - (1 - d) / 2) - log b := by
  have h2 : (1 + d) / 2 ≠ 0 := by linarith [hd.1]
  rw [log_div (mul_ne_zero h2 (sub_ne_zero.2 hm)) hb, log_mul h2 (sub_ne_zero.2 hm),
    log_div (by linarith [hd.1]) two_ne_zero]

end QED.ChainProof.SetAKS

end
