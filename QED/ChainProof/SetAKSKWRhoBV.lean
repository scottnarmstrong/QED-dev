/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBE1
public import QED.ChainProof.SetAKSKWRhoBE2A
public import QED.ChainProof.SetAKSKWRhoBE3
public import QED.Polylog.DilogPM
public import QED.ChainProof.SetAKSKWRhoA

/-!
# Set (a), stage D: the three primitive values of the `β`-integral of `ρ_B`

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. The
primitive values `ksWYv` of the three `ksWYe` combinations on `(0, σ₋)`, `(σ₋, σ₊)`, `(σ₊, 1)`
(`σ± = (1 ± δ)/2`) are evaluated in closed form. The dilogarithms `ksWYD` at the endpoints reduce
by the branch lemmas (`ksWY_ksWYD_of_nonpos`, `ksWY_ksWYD_of_mem`, `ksWY_ksWYD_of_one_le`) and the
functional equations of `QED.Polylog.DilogPM` to `Li₂ δ`, `Li₂ (-δ)`, `Li₂ ((1 - δ)/2)` and
elementary terms; each value is split into its logarithmic, dilogarithmic and pole components.
Their sum is `ksWRBv δ`, monomial by monomial in the logarithms `log(1 ± δ)`, `log 2`, `log δ`.

Main result:

* **`ksWYv_total`**: the three values add up to `ksWRBv δ`.
-/

@[expose] public section

open Real Set QED.Polylog QED.Chain

namespace QED.ChainProof.SetAKS

variable {d : ℝ}

theorem ksWYv_e1 : (1 + d) / 2 - 1 = -((1 - d) / 2) := by ring

theorem ksWYv_e2 : (1 - d) / 2 - 1 = -((1 + d) / 2) := by ring

theorem ksWYv_e3 : (1 + d) / 2 - (1 - d) / 2 = d := by ring

theorem ksWYv_e4 : (1 - d) / 2 - (1 + d) / 2 = -d := by ring

theorem ksWYv_e5 : 1 - (1 - d) / 2 = (1 + d) / 2 := by ring

theorem ksWYv_e6 : 1 - (1 + d) / 2 = (1 - d) / 2 := by ring

theorem ksWYv_log_a (hd : d ∈ Ioo (0 : ℝ) 1) : log (2 / (1 + d)) = log 2 - log (1 + d) :=
  log_div two_ne_zero (by linarith [hd.1])

theorem ksWYv_log_b (hd : d ∈ Ioo (0 : ℝ) 1) :
    log ((1 + d) / (1 - d)) = log (1 + d) - log (1 - d) :=
  log_div (by linarith [hd.1]) (by linarith [hd.2])

theorem ksWYv_log_c (hd : d ∈ Ioo (0 : ℝ) 1) : log (2 / (1 - d)) = log 2 - log (1 - d) :=
  log_div two_ne_zero (by linarith [hd.2])

theorem ksWYv_log_d (hd : d ∈ Ioo (0 : ℝ) 1) :
    log ((1 + d) / (2 * d)) = log (1 + d) - log 2 - log d := by
  rw [log_div (by linarith [hd.1]) (by linarith [hd.1]), log_mul two_ne_zero hd.1.ne']
  ring

theorem ksWYv_D1 :
    ksWYD ((((1 - d) / 2) - ((1 - d) / 2)) / (1 - ((1 - d) / 2))) = 0 := by
  rw [sub_self, zero_div, ksWY_ksWYD_of_mem ⟨le_rfl, zero_le_one⟩, Li₂_zero, neg_zero]

theorem ksWYv_D2 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((0 - ((1 - d) / 2)) / (1 - ((1 - d)
  / 2))) = Li₂ ((1 - d) / 2) + (log 2 - log (1 + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : 1 - ((1 - d) / 2) ≠ 0 := by
    have h : (0 : ℝ) < 1 - ((1 - d) / 2) := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (0 - ((1 - d) / 2)) / (1 - ((1 - d) / 2)) = (-(1 - d)) / (1 + d) := by
    rw [div_eq_div_iff hAP hdp.ne']
    ring
  rw [hz]
  have hz0 : (-(1 - d)) / (1 + d) ≤ 0 := by
    rw [div_le_iff₀ hdp]
    linarith only [hd.1, hd.2]
  rw [ksWY_ksWYD_of_nonpos hz0]
  have h1 : (-(1 - d)) - (1 + d) ≠ 0 := by
    have h : (-(1 - d)) - (1 + d) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have e1 : (-(1 - d)) / (1 + d) / ((-(1 - d)) / (1 + d) - 1) = ((1 - d) / 2) := by
    rw [div_sub_one hdp.ne', div_div_div_cancel_right₀ hdp.ne']
    rw [div_eq_div_iff h1 two_pos.ne']
    ring
  have e2 : 1 - (-(1 - d)) / (1 + d) = (2 / (1 + d)) := by
    rw [one_sub_div hdp.ne', div_eq_div_iff hdp.ne' hdp.ne']
    ring
  rw [e1, e2, ksWYv_log_a hd]

theorem ksWYv_D3 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 - d) / 2) - ((1 + d) / 2)) / (1 - ((1
  + d) / 2))) = log 2 ^ 2 / 2 - log 2 * log (1 - d) + Li₂ d - Li₂ (-d) + Li₂ ((1 - d) / 2)
  + log (1 - d) * log (1 + d) - log (1 + d) ^ 2 / 2 - π ^ 2 / 12 + (-log (1 - d) + log (1
  + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : 1 - ((1 + d) / 2) ≠ 0 := by
    have h : (0 : ℝ) < 1 - ((1 + d) / 2) := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (((1 - d) / 2) - ((1 + d) / 2)) / (1 - ((1 + d) / 2)) = (-(2 * d)) / (1 - d) := by
    rw [div_eq_div_iff hAP hdm.ne']
    ring
  rw [hz]
  have hz0 : (-(2 * d)) / (1 - d) ≤ 0 := by
    rw [div_le_iff₀ hdm]
    linarith only [hd.1, hd.2]
  rw [ksWY_ksWYD_of_nonpos hz0]
  have h1 : (-(2 * d)) - (1 - d) ≠ 0 := by
    have h : (-(2 * d)) - (1 - d) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have e1 : (-(2 * d)) / (1 - d) / ((-(2 * d)) / (1 - d) - 1) = (2 * d / (1 + d)) := by
    rw [div_sub_one hdm.ne', div_div_div_cancel_right₀ hdm.ne']
    rw [div_eq_div_iff h1 hdp.ne']
    ring
  have e2 : 1 - (-(2 * d)) / (1 - d) = ((1 + d) / (1 - d)) := by
    rw [one_sub_div hdm.ne', div_eq_div_iff hdm.ne' hdm.ne']
    ring
  rw [e1, e2, ksWYv_log_b hd]
  have hW := Li_two_two_mul_div hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D4 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((0 - ((1 + d) / 2)) / (1 - ((1 + d)
  / 2))) = -Li₂ ((1 - d) / 2) + π ^ 2 / 6 - (-log 2 + log (1 - d)) * (-log 2 + log (1 + d))
  + (log 2 - log (1 - d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : 1 - ((1 + d) / 2) ≠ 0 := by
    have h : (0 : ℝ) < 1 - ((1 + d) / 2) := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (0 - ((1 + d) / 2)) / (1 - ((1 + d) / 2)) = (-(1 + d)) / (1 - d) := by
    rw [div_eq_div_iff hAP hdm.ne']
    ring
  rw [hz]
  have hz0 : (-(1 + d)) / (1 - d) ≤ 0 := by
    rw [div_le_iff₀ hdm]
    linarith only [hd.1, hd.2]
  rw [ksWY_ksWYD_of_nonpos hz0]
  have h1 : (-(1 + d)) - (1 - d) ≠ 0 := by
    have h : (-(1 + d)) - (1 - d) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have e1 : (-(1 + d)) / (1 - d) / ((-(1 + d)) / (1 - d) - 1) = ((1 + d) / 2) := by
    rw [div_sub_one hdm.ne', div_div_div_cancel_right₀ hdm.ne']
    rw [div_eq_div_iff h1 two_pos.ne']
    ring
  have e2 : 1 - (-(1 + d)) / (1 - d) = (2 / (1 - d)) := by
    rw [one_sub_div hdm.ne', div_eq_div_iff hdm.ne' hdm.ne']
    ring
  rw [e1, e2, ksWYv_log_c hd]
  have hW := Li_two_one_add_div_two hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D5 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 - d) / 2) - 1) / (((1 - d) / 2)
  - 1)) = -(π ^ 2 / 6) := by
  have hAP : ((1 - d) / 2) - 1 ≠ 0 := by
    have h : ((1 - d) / 2) - 1 < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  rw [div_self hAP, ksWY_ksWYD_of_mem ⟨zero_le_one, le_rfl⟩, Li₂_one]

theorem ksWYv_D6 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((0 - 1) / (((1 - d) / 2) - 1)) = -Li₂ ((1
  - d) / 2) - π ^ 2 / 6 - (-log 2 + log (1 - d)) * (-log 2 + log (1 + d)) + (log 2 - log (1
  + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 - d) / 2) - 1 ≠ 0 := by
    have h : ((1 - d) / 2) - 1 < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (0 - 1) / (((1 - d) / 2) - 1) = 2 / (1 + d) := by
    rw [div_eq_div_iff hAP hdp.ne']
    ring
  rw [hz]
  have hz0 : 1 ≤ 2 / (1 + d) := (one_le_div hdp).2 (by linarith only [hd.1, hd.2])
  rw [ksWY_ksWYD_of_one_le hz0, one_div_div, ksWYv_log_a hd]
  have hW := Li_two_one_add_div_two hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D7 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 - d) / 2) - ((1 + d) / 2)) / (((1 - d)
  / 2) - ((1 + d) / 2))) = -(π ^ 2 / 6) := by
  have hAP : ((1 - d) / 2) - ((1 + d) / 2) ≠ 0 := by
    have h : ((1 - d) / 2) - ((1 + d) / 2) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  rw [div_self hAP, ksWY_ksWYD_of_mem ⟨zero_le_one, le_rfl⟩, Li₂_one]

theorem ksWYv_D8 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((0 - ((1 + d) / 2)) / (((1 - d) / 2) - ((1
  + d) / 2))) = log 2 ^ 2 / 2 - log 2 * log (1 - d) + Li₂ d - Li₂ (-d) + Li₂ ((1 - d) / 2)
  + log (1 - d) * log (1 + d) - log (1 + d) ^ 2 / 2 - 5 * π ^ 2 / 12 + (-log d - log 2 + log (1
  + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 - d) / 2) - ((1 + d) / 2) ≠ 0 := by
    have h : ((1 - d) / 2) - ((1 + d) / 2) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (0 - ((1 + d) / 2)) / (((1 - d) / 2) - ((1 + d) / 2)) = (1 + d) / (2 * d) := by
    rw [div_eq_div_iff hAP h2d.ne']
    ring
  rw [hz]
  have hz0 : 1 ≤ (1 + d) / (2 * d) := (one_le_div h2d).2 (by linarith only [hd.1, hd.2])
  rw [ksWY_ksWYD_of_one_le hz0, one_div_div, ksWYv_log_d hd]
  have hW := Li_two_two_mul_div hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D9 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 - d) / 2) - 1) / (((1 + d) / 2)
  - 1)) = -(log d * log (1 - d)) + log d * log (1 + d) - log 2 ^ 2 / 2 + log 2 * log (1 + d)
  - Li₂ d + Li₂ (-d) - Li₂ ((1 - d) / 2) - log (1 + d) ^ 2 / 2 - π ^ 2 / 12 + (-log (1 - d)
  + log (1 + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 + d) / 2) - 1 ≠ 0 := by
    have h : ((1 + d) / 2) - 1 < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (((1 - d) / 2) - 1) / (((1 + d) / 2) - 1) = (1 + d) / (1 - d) := by
    rw [div_eq_div_iff hAP hdm.ne']
    ring
  rw [hz]
  have hz0 : 1 ≤ (1 + d) / (1 - d) := (one_le_div hdm).2 (by linarith only [hd.1, hd.2])
  rw [ksWY_ksWYD_of_one_le hz0, one_div_div, ksWYv_log_b hd]
  have hW := Li_two_ksT hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D10 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((0 - 1) / (((1 + d) / 2) - 1)) = Li₂ ((1
  - d) / 2) - π ^ 2 / 3 + (log 2 - log (1 - d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 + d) / 2) - 1 ≠ 0 := by
    have h : ((1 + d) / 2) - 1 < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (0 - 1) / (((1 + d) / 2) - 1) = 2 / (1 - d) := by
    rw [div_eq_div_iff hAP hdm.ne']
    ring
  rw [hz]
  have hz0 : 1 ≤ 2 / (1 - d) := (one_le_div hdm).2 (by linarith only [hd.1, hd.2])
  rw [ksWY_ksWYD_of_one_le hz0, one_div_div, ksWYv_log_c hd]
  ring

theorem ksWYv_D11 :
    ksWYD ((((1 - d) / 2) - ((1 - d) / 2)) / (((1 + d) / 2) - ((1 - d)
  / 2))) = 0 := by
  rw [sub_self, zero_div, ksWY_ksWYD_of_mem ⟨le_rfl, zero_le_one⟩, Li₂_zero, neg_zero]

theorem ksWYv_D12 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((0 - ((1 - d) / 2)) / (((1 + d) / 2) - ((1
  - d) / 2))) = -(log d * log (1 - d)) + log d * log (1 + d) - log 2 ^ 2 / 2 + log 2 * log (1 + d)
  - Li₂ d + Li₂ (-d) - Li₂ ((1 - d) / 2) - log (1 + d) ^ 2 / 2 + π ^ 2 / 4 + (-log d - log 2
  + log (1 + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 + d) / 2) - ((1 - d) / 2) ≠ 0 := by
    have h : (0 : ℝ) < ((1 + d) / 2) - ((1 - d) / 2) := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (0 - ((1 - d) / 2)) / (((1 + d) / 2) - ((1 - d) / 2)) = (-(1 - d)) / (2 * d) := by
    rw [div_eq_div_iff hAP h2d.ne']
    ring
  rw [hz]
  have hz0 : (-(1 - d)) / (2 * d) ≤ 0 := by
    rw [div_le_iff₀ h2d]
    linarith only [hd.1, hd.2]
  rw [ksWY_ksWYD_of_nonpos hz0]
  have h1 : (-(1 - d)) - (2 * d) ≠ 0 := by
    have h : (-(1 - d)) - (2 * d) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have e1 : (-(1 - d)) / (2 * d) / ((-(1 - d)) / (2 * d) - 1) = ((1 - d) / (1 + d)) := by
    rw [div_sub_one h2d.ne', div_div_div_cancel_right₀ h2d.ne']
    rw [div_eq_div_iff h1 hdp.ne']
    ring
  have e2 : 1 - (-(1 - d)) / (2 * d) = ((1 + d) / (2 * d)) := by
    rw [one_sub_div h2d.ne', div_eq_div_iff h2d.ne' h2d.ne']
    ring
  rw [e1, e2, ksWYv_log_d hd]
  have hW := Li_two_ksT hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D13 :
    ksWYD ((((1 + d) / 2) - ((1 + d) / 2)) / (0 - ((1 + d) / 2))) = 0 := by
  rw [sub_self, zero_div, ksWY_ksWYD_of_mem ⟨le_rfl, zero_le_one⟩, Li₂_zero, neg_zero]

theorem ksWYv_D14 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 - d) / 2) - ((1 + d) / 2)) / (0 - ((1
  + d) / 2))) = -(log 2 ^ 2 / 2) + log 2 * log (1 - d) - Li₂ d + Li₂ (-d) - Li₂ ((1 - d) / 2)
  - log (1 - d) * log (1 + d) + log (1 + d) ^ 2 / 2 + π ^ 2 / 12 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : 0 - ((1 + d) / 2) ≠ 0 := by
    have h : 0 - ((1 + d) / 2) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (((1 - d) / 2) - ((1 + d) / 2)) / (0 - ((1 + d) / 2)) = (2 * d) / (1 + d) := by
    rw [div_eq_div_iff hAP hdp.ne']
    ring
  rw [hz]
  have hz0 : (2 * d) / (1 + d) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith only [hd.1, hd.2]) hdp.le,
      (div_le_one hdp).2 (by linarith only [hd.1, hd.2])⟩
  rw [ksWY_ksWYD_of_mem hz0]
  have hW := Li_two_two_mul_div hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D15 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 + d) / 2) - ((1 - d) / 2)) / (1 - ((1
  - d) / 2))) = -(log 2 ^ 2 / 2) + log 2 * log (1 - d) - Li₂ d + Li₂ (-d) - Li₂ ((1 - d) / 2)
  - log (1 - d) * log (1 + d) + log (1 + d) ^ 2 / 2 + π ^ 2 / 12 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : 1 - ((1 - d) / 2) ≠ 0 := by
    have h : (0 : ℝ) < 1 - ((1 - d) / 2) := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (((1 + d) / 2) - ((1 - d) / 2)) / (1 - ((1 - d) / 2)) = (2 * d) / (1 + d) := by
    rw [div_eq_div_iff hAP hdp.ne']
    ring
  rw [hz]
  have hz0 : (2 * d) / (1 + d) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith only [hd.1, hd.2]) hdp.le,
      (div_le_one hdp).2 (by linarith only [hd.1, hd.2])⟩
  rw [ksWY_ksWYD_of_mem hz0]
  have hW := Li_two_two_mul_div hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D16 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 + d) / 2) - 1) / (((1 - d) / 2)
  - 1)) = log d * log (1 - d) - log d * log (1 + d) + log 2 ^ 2 / 2 - log 2 * log (1 + d) + Li₂ d
  - Li₂ (-d) + Li₂ ((1 - d) / 2) + log (1 + d) ^ 2 / 2 - π ^ 2 / 4 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 - d) / 2) - 1 ≠ 0 := by
    have h : ((1 - d) / 2) - 1 < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (((1 + d) / 2) - 1) / (((1 - d) / 2) - 1) = (1 - d) / (1 + d) := by
    rw [div_eq_div_iff hAP hdp.ne']
    ring
  rw [hz]
  have hz0 : (1 - d) / (1 + d) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith only [hd.1, hd.2]) hdp.le,
      (div_le_one hdp).2 (by linarith only [hd.1, hd.2])⟩
  rw [ksWY_ksWYD_of_mem hz0]
  have hW := Li_two_ksT hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D17 :
    ksWYD ((((1 + d) / 2) - ((1 + d) / 2)) / (((1 - d) / 2) - ((1 + d)
  / 2))) = 0 := by
  rw [sub_self, zero_div, ksWY_ksWYD_of_mem ⟨le_rfl, zero_le_one⟩, Li₂_zero, neg_zero]

theorem ksWYv_D18 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 + d) / 2) - 0) / (((1 + d) / 2)
  - 0)) = -(π ^ 2 / 6) := by
  have hAP : ((1 + d) / 2) - 0 ≠ 0 := by
    have h : (0 : ℝ) < ((1 + d) / 2) - 0 := by linarith only [hd.1, hd.2]
    exact h.ne'
  rw [div_self hAP, ksWY_ksWYD_of_mem ⟨zero_le_one, le_rfl⟩, Li₂_one]

theorem ksWYv_D19 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 - d) / 2) - 0) / (((1 + d) / 2)
  - 0)) = log d * log (1 - d) - log d * log (1 + d) + log 2 ^ 2 / 2 - log 2 * log (1 + d) + Li₂ d
  - Li₂ (-d) + Li₂ ((1 - d) / 2) + log (1 + d) ^ 2 / 2 - π ^ 2 / 4 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 + d) / 2) - 0 ≠ 0 := by
    have h : (0 : ℝ) < ((1 + d) / 2) - 0 := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (((1 - d) / 2) - 0) / (((1 + d) / 2) - 0) = (1 - d) / (1 + d) := by
    rw [div_eq_div_iff hAP hdp.ne']
    ring
  rw [hz]
  have hz0 : (1 - d) / (1 + d) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith only [hd.1, hd.2]) hdp.le,
      (div_le_one hdp).2 (by linarith only [hd.1, hd.2])⟩
  rw [ksWY_ksWYD_of_mem hz0]
  have hW := Li_two_ksT hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D20 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 + d) / 2) - ((1 - d) / 2)) / (((1
  + d) / 2) - ((1 - d) / 2))) = -(π ^ 2 / 6) := by
  have hAP : ((1 + d) / 2) - ((1 - d) / 2) ≠ 0 := by
    have h : (0 : ℝ) < ((1 + d) / 2) - ((1 - d) / 2) := by linarith only [hd.1, hd.2]
    exact h.ne'
  rw [div_self hAP, ksWY_ksWYD_of_mem ⟨zero_le_one, le_rfl⟩, Li₂_one]

theorem ksWYv_D21 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((1 - ((1 - d) / 2)) / (0 - ((1 - d)
  / 2))) = -Li₂ ((1 - d) / 2) + π ^ 2 / 6 - (-log 2 + log (1 - d)) * (-log 2 + log (1 + d))
  + (log 2 - log (1 - d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : 0 - ((1 - d) / 2) ≠ 0 := by
    have h : 0 - ((1 - d) / 2) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (1 - ((1 - d) / 2)) / (0 - ((1 - d) / 2)) = (-(1 + d)) / (1 - d) := by
    rw [div_eq_div_iff hAP hdm.ne']
    ring
  rw [hz]
  have hz0 : (-(1 + d)) / (1 - d) ≤ 0 := by
    rw [div_le_iff₀ hdm]
    linarith only [hd.1, hd.2]
  rw [ksWY_ksWYD_of_nonpos hz0]
  have h1 : (-(1 + d)) - (1 - d) ≠ 0 := by
    have h : (-(1 + d)) - (1 - d) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have e1 : (-(1 + d)) / (1 - d) / ((-(1 + d)) / (1 - d) - 1) = ((1 + d) / 2) := by
    rw [div_sub_one hdm.ne', div_div_div_cancel_right₀ hdm.ne']
    rw [div_eq_div_iff h1 two_pos.ne']
    ring
  have e2 : 1 - (-(1 + d)) / (1 - d) = (2 / (1 - d)) := by
    rw [one_sub_div hdm.ne', div_eq_div_iff hdm.ne' hdm.ne']
    ring
  rw [e1, e2, ksWYv_log_c hd]
  have hW := Li_two_one_add_div_two hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D22 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 + d) / 2) - ((1 - d) / 2)) / (0 - ((1
  - d) / 2))) = log 2 ^ 2 / 2 - log 2 * log (1 - d) + Li₂ d - Li₂ (-d) + Li₂ ((1 - d) / 2)
  + log (1 - d) * log (1 + d) - log (1 + d) ^ 2 / 2 - π ^ 2 / 12 + (-log (1 - d) + log (1
  + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : 0 - ((1 - d) / 2) ≠ 0 := by
    have h : 0 - ((1 - d) / 2) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (((1 + d) / 2) - ((1 - d) / 2)) / (0 - ((1 - d) / 2)) = (-(2 * d)) / (1 - d) := by
    rw [div_eq_div_iff hAP hdm.ne']
    ring
  rw [hz]
  have hz0 : (-(2 * d)) / (1 - d) ≤ 0 := by
    rw [div_le_iff₀ hdm]
    linarith only [hd.1, hd.2]
  rw [ksWY_ksWYD_of_nonpos hz0]
  have h1 : (-(2 * d)) - (1 - d) ≠ 0 := by
    have h : (-(2 * d)) - (1 - d) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have e1 : (-(2 * d)) / (1 - d) / ((-(2 * d)) / (1 - d) - 1) = (2 * d / (1 + d)) := by
    rw [div_sub_one hdm.ne', div_div_div_cancel_right₀ hdm.ne']
    rw [div_eq_div_iff h1 hdp.ne']
    ring
  have e2 : 1 - (-(2 * d)) / (1 - d) = ((1 + d) / (1 - d)) := by
    rw [one_sub_div hdm.ne', div_eq_div_iff hdm.ne' hdm.ne']
    ring
  rw [e1, e2, ksWYv_log_b hd]
  have hW := Li_two_two_mul_div hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D23 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((1 - ((1 + d) / 2)) / (0 - ((1 + d)
  / 2))) = Li₂ ((1 - d) / 2) + (log 2 - log (1 + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : 0 - ((1 + d) / 2) ≠ 0 := by
    have h : 0 - ((1 + d) / 2) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (1 - ((1 + d) / 2)) / (0 - ((1 + d) / 2)) = (-(1 - d)) / (1 + d) := by
    rw [div_eq_div_iff hAP hdp.ne']
    ring
  rw [hz]
  have hz0 : (-(1 - d)) / (1 + d) ≤ 0 := by
    rw [div_le_iff₀ hdp]
    linarith only [hd.1, hd.2]
  rw [ksWY_ksWYD_of_nonpos hz0]
  have h1 : (-(1 - d)) - (1 + d) ≠ 0 := by
    have h : (-(1 - d)) - (1 + d) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have e1 : (-(1 - d)) / (1 + d) / ((-(1 - d)) / (1 + d) - 1) = ((1 - d) / 2) := by
    rw [div_sub_one hdp.ne', div_div_div_cancel_right₀ hdp.ne']
    rw [div_eq_div_iff h1 two_pos.ne']
    ring
  have e2 : 1 - (-(1 - d)) / (1 + d) = (2 / (1 + d)) := by
    rw [one_sub_div hdp.ne', div_eq_div_iff hdp.ne' hdp.ne']
    ring
  rw [e1, e2, ksWYv_log_a hd]

theorem ksWYv_D24 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((1 - 0) / (((1 - d) / 2) - 0)) = Li₂ ((1
  - d) / 2) - π ^ 2 / 3 + (log 2 - log (1 - d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 - d) / 2) - 0 ≠ 0 := by
    have h : (0 : ℝ) < ((1 - d) / 2) - 0 := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (1 - 0) / (((1 - d) / 2) - 0) = 2 / (1 - d) := by
    rw [div_eq_div_iff hAP hdm.ne']
    ring
  rw [hz]
  have hz0 : 1 ≤ 2 / (1 - d) := (one_le_div hdm).2 (by linarith only [hd.1, hd.2])
  rw [ksWY_ksWYD_of_one_le hz0, one_div_div, ksWYv_log_c hd]
  ring

theorem ksWYv_D25 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((((1 + d) / 2) - 0) / (((1 - d) / 2)
  - 0)) = -(log d * log (1 - d)) + log d * log (1 + d) - log 2 ^ 2 / 2 + log 2 * log (1 + d)
  - Li₂ d + Li₂ (-d) - Li₂ ((1 - d) / 2) - log (1 + d) ^ 2 / 2 - π ^ 2 / 12 + (-log (1 - d)
  + log (1 + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 - d) / 2) - 0 ≠ 0 := by
    have h : (0 : ℝ) < ((1 - d) / 2) - 0 := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (((1 + d) / 2) - 0) / (((1 - d) / 2) - 0) = (1 + d) / (1 - d) := by
    rw [div_eq_div_iff hAP hdm.ne']
    ring
  rw [hz]
  have hz0 : 1 ≤ (1 + d) / (1 - d) := (one_le_div hdm).2 (by linarith only [hd.1, hd.2])
  rw [ksWY_ksWYD_of_one_le hz0, one_div_div, ksWYv_log_b hd]
  have hW := Li_two_ksT hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D26 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((1 - ((1 + d) / 2)) / (((1 - d) / 2) - ((1
  + d) / 2))) = -(log d * log (1 - d)) + log d * log (1 + d) - log 2 ^ 2 / 2 + log 2 * log (1 + d)
  - Li₂ d + Li₂ (-d) - Li₂ ((1 - d) / 2) - log (1 + d) ^ 2 / 2 + π ^ 2 / 4 + (-log d - log 2
  + log (1 + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 - d) / 2) - ((1 + d) / 2) ≠ 0 := by
    have h : ((1 - d) / 2) - ((1 + d) / 2) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have hz : (1 - ((1 + d) / 2)) / (((1 - d) / 2) - ((1 + d) / 2)) = (-(1 - d)) / (2 * d) := by
    rw [div_eq_div_iff hAP h2d.ne']
    ring
  rw [hz]
  have hz0 : (-(1 - d)) / (2 * d) ≤ 0 := by
    rw [div_le_iff₀ h2d]
    linarith only [hd.1, hd.2]
  rw [ksWY_ksWYD_of_nonpos hz0]
  have h1 : (-(1 - d)) - (2 * d) ≠ 0 := by
    have h : (-(1 - d)) - (2 * d) < 0 := by linarith only [hd.1, hd.2]
    exact h.ne
  have e1 : (-(1 - d)) / (2 * d) / ((-(1 - d)) / (2 * d) - 1) = ((1 - d) / (1 + d)) := by
    rw [div_sub_one h2d.ne', div_div_div_cancel_right₀ h2d.ne']
    rw [div_eq_div_iff h1 hdp.ne']
    ring
  have e2 : 1 - (-(1 - d)) / (2 * d) = ((1 + d) / (2 * d)) := by
    rw [one_sub_div h2d.ne', div_eq_div_iff h2d.ne' h2d.ne']
    ring
  rw [e1, e2, ksWYv_log_d hd]
  have hW := Li_two_ksT hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D27 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((1 - 0) / (((1 + d) / 2) - 0)) = -Li₂ ((1
  - d) / 2) - π ^ 2 / 6 - (-log 2 + log (1 - d)) * (-log 2 + log (1 + d)) + (log 2 - log (1
  + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 + d) / 2) - 0 ≠ 0 := by
    have h : (0 : ℝ) < ((1 + d) / 2) - 0 := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (1 - 0) / (((1 + d) / 2) - 0) = 2 / (1 + d) := by
    rw [div_eq_div_iff hAP hdp.ne']
    ring
  rw [hz]
  have hz0 : 1 ≤ 2 / (1 + d) := (one_le_div hdp).2 (by linarith only [hd.1, hd.2])
  rw [ksWY_ksWYD_of_one_le hz0, one_div_div, ksWYv_log_a hd]
  have hW := Li_two_one_add_div_two hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_D28 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYD ((1 - ((1 - d) / 2)) / (((1 + d) / 2) - ((1
  - d) / 2))) = log 2 ^ 2 / 2 - log 2 * log (1 - d) + Li₂ d - Li₂ (-d) + Li₂ ((1 - d) / 2)
  + log (1 - d) * log (1 + d) - log (1 + d) ^ 2 / 2 - 5 * π ^ 2 / 12 + (-log d - log 2 + log (1
  + d)) ^ 2 / 2 := by
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hd0 : (0 : ℝ) < d := hd.1
  have h2d : (0 : ℝ) < 2 * d := by linarith [hd.1]
  have hAP : ((1 + d) / 2) - ((1 - d) / 2) ≠ 0 := by
    have h : (0 : ℝ) < ((1 + d) / 2) - ((1 - d) / 2) := by linarith only [hd.1, hd.2]
    exact h.ne'
  have hz : (1 - ((1 - d) / 2)) / (((1 + d) / 2) - ((1 - d) / 2)) = (1 + d) / (2 * d) := by
    rw [div_eq_div_iff hAP h2d.ne']
    ring
  rw [hz]
  have hz0 : 1 ≤ (1 + d) / (2 * d) := (one_le_div h2d).2 (by linarith only [hd.1, hd.2])
  rw [ksWY_ksWYD_of_one_le hz0, one_div_div, ksWYv_log_d hd]
  have hW := Li_two_two_mul_div hd
  rw [Li_two] at hW
  rw [hW]
  ring

theorem ksWYv_1L (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWPv (ksWY1L d) (ksWY1P d) 0 ((1 - d)
  / 2) =
      (-((d + 1) * (d - 1) * (5 * d ^ 2 + 2 * d + 5) / 12)) * log (1 - d) + ((13 * d ^ 4
  - 2 * d ^ 3 - 24 * d ^ 2 + 2 * d - 5) / 12) * log (1 + d) + (-(d * (2 * d ^ 3 - d ^ 2 - 6 * d
  + 1) / 3)) * log 2 + (-(d * (2 * d ^ 3 - d ^ 2 - 6 * d + 1) / 3)) * log d + (-(d * (d - 1) * (13
  * d ^ 2 + 9 * d + 30) / 18)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWPv, ksWY1L, ksWY1P, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, ksWYv_e4,
    sub_zero, zero_sub, log_neg_eq_log, ksWY_log_sm hd.2, ksWY_log_sp (by linarith [hd.1] : -1 < d),
    sub_self, log_zero, mul_zero, zero_mul, add_zero, zero_add]
  field_simp
  ring

theorem ksWYv_1D (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY1D d).map fun t => t.1 * (ksWYD ((((1 - d)
  / 2) - t.2.2) / (t.2.1 - t.2.2)) -
      ksWYD ((0 - t.2.2) / (t.2.1 - t.2.2)))).sum =
      (10
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * log (1 - d) * log (1 + d) + (-(10 * (d ^ 2 + 1) * (d ^ 2 - 3)
  / 3)) * log 2 * log (1 - d) + (2 * (d ^ 2 + 1) * (d ^ 2 - 3)) * log d * log (1 - d) + (-(10
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * log 2 * log (1 + d) + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3)))
  * log d * log (1 + d) + (10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * log 2 ^ 2 + (4 * (d ^ 2 + 1)
  * (d ^ 2 - 3)) * Li₂ d + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3))) * Li₂ (-d) + (20 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3) * Li₂ ((1 - d) / 2) + (-((d ^ 2 + 1) * (d ^ 2 - 3))) * π ^ 2 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY1D, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [ksWYv_D1, ksWYv_D2 hd, ksWYv_D3 hd, ksWYv_D4 hd, ksWYv_D5 hd, ksWYv_D6 hd, ksWYv_D7 hd,
    ksWYv_D8 hd, ksWYv_D9 hd, ksWYv_D10 hd, ksWYv_D11, ksWYv_D12 hd]
  ring

theorem ksWYv_1Q (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY1Q d).map fun t => t.1
  * (ksWYG2 t.2.1 t.2.2 ((1 - d) / 2) - ksWYG2 t.2.1 t.2.2 0)).sum =
      (-((d - 1) ^ 2 * (17
  * d ^ 2 - 25) / 12)) * log (1 - d) + ((17 * d ^ 2 - 25) * (d ^ 2 + 6 * d + 1) / 12) * log (1
  + d) + (-(2 * d * (17 * d ^ 2 - 25) / 3)) * log 2 + (-(d * (17 * d ^ 2 - 25) / 3)) * log d := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY1Q, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWYG2, ksWYv_e1, ksWYv_e2, ksWYv_e4, zero_sub, log_neg_eq_log, ksWY_log_sm hd.2,
    ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_self, log_zero, log_one, mul_zero, add_zero]
  field_simp
  ring

theorem ksWYv_1C (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY1C d).map fun t => t.1
  * (ksWYG3 t.2.1 t.2.2 ((1 - d) / 2) - ksWYG3 t.2.1 t.2.2 0)).sum =
      (-((d - 1) ^ 3 * (2
  * d ^ 2 - 3) * (d + 3) / 6)) * log (1 - d) + ((2 * d ^ 2 - 3) * (d ^ 4 - 6 * d ^ 2 - 24 * d - 3)
  / 6) * log (1 + d) + (16 * d * (2 * d ^ 2 - 3) / 3) * log 2 + (8 * d * (2 * d ^ 2 - 3) / 3)
  * log d + 2 * d * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY1C, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWYG3, one_pow, ksWYv_e1, ksWYv_e2, ksWYv_e4, zero_sub, log_neg_eq_log,
    ksWY_log_sm hd.2, ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_self, log_zero, log_one,
    mul_zero, zero_mul, add_zero, even_two, Even.neg_pow]
  field_simp
  ring

theorem ksWYv_1R (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY1R d).map fun t => ksWPQ t.1 t.2.1 t.2.2 ((1
  - d) / 2) - ksWPQ t.1 t.2.1 t.2.2 0).sum =
      (-((d - 1) ^ 2 * (17 * d ^ 2 - 25) / 12))
  * log (1 - d) + ((d - 1) * (17 * d ^ 3 - 21 * d ^ 2 - 29 * d + 25) / 12) * log (1 + d) + (d * (d
  + 1) * (d - 1) / 3) * log 2 + (-(4 * d * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY1R, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWPQ, ksWYv_e2, zero_sub, log_neg_eq_log, ksWY_log_sp (by linarith [hd.1] : -1 < d),
    log_one, mul_zero, add_zero]
  field_simp
  ring

theorem ksWYv_1S (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY1S d).map fun t => -(t.2 / (2 * (((1 - d)
  / 2) - t.1) ^ 2)) + t.2 / (2 * (0 - t.1) ^ 2)).sum =
      (-((d - 1) ^ 3 * (2 * d ^ 2 - 3) * (d
  + 3) / 6)) * log (1 - d) + ((d - 1) ^ 3 * (2 * d ^ 2 - 3) * (d + 3) / 6) * log (1 + d) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY1S, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [one_pow, ksWYv_e2, zero_sub, add_zero, even_two, Even.neg_pow]
  field_simp
  ring

theorem ksWYv_2L (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWPv (ksWY2L d) (ksWY2P d) ((1 - d) / 2) ((1 + d)
  / 2) =
      (-((13 * d ^ 4 + 2 * d ^ 3 - 24 * d ^ 2 - 2 * d - 5) / 6)) * log (1 - d) + ((d + 1)
  * (d - 1) * (5 * d ^ 2 - 2 * d + 5) / 6) * log (1 + d) + (2 * d * (2 * d ^ 3 + d ^ 2 - 6 * d
  - 1) / 3) * log 2 + (2 * d * (2 * d ^ 3 + d ^ 2 - 6 * d - 1) / 3) * log d + d * (13 * d ^ 3 - 38
  * d ^ 2 + 21 * d + 96) / 9 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWPv, ksWY2L, ksWY2P, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, ksWYv_e1,
    ksWYv_e2, ksWYv_e3, ksWYv_e4, sub_zero, zero_sub, log_neg_eq_log, ksWY_log_sm hd.2,
    ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_self, log_zero, mul_zero, add_zero, zero_add]
  field_simp
  ring

theorem ksWYv_2D (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY2D d).map fun t => t.1 * (ksWYD ((((1 + d)
  / 2) - t.2.2) / (t.2.1 - t.2.2)) -
      ksWYD ((((1 - d) / 2) - t.2.2) / (t.2.1
  - t.2.2)))).sum =
      (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * log (1 - d) * log (1 + d) + (-(4
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * log 2 * log (1 - d) + (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)
  * log d * log (1 - d) + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * log 2 * log (1 + d) + (-(4
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * log d * log (1 + d) + (4 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)
  * log 2 ^ 2 + (8 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * Li₂ d + (-(8 * (d ^ 2 + 1) * (d ^ 2 - 3)
  / 3)) * Li₂ (-d) + (8 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * Li₂ ((1 - d) / 2) + (-(2 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3)) * π ^ 2 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY2D, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [ksWYv_D13, ksWYv_D14 hd, ksWYv_D15 hd, ksWYv_D1, ksWYv_D16 hd, ksWYv_D5 hd, ksWYv_D17,
    ksWYv_D7 hd, ksWYv_D18 hd, ksWYv_D19 hd, ksWYv_D20 hd, ksWYv_D11]
  ring

theorem ksWYv_2Q (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY2Q d).map fun t => t.1
  * (ksWYG2 t.2.1 t.2.2 ((1 + d) / 2) - ksWYG2 t.2.1 t.2.2 ((1 - d) / 2))).sum =
      ((d - 1)
  * (17 * d ^ 2 - 25) / 3) * log (1 - d) + (-((d - 1) * (17 * d ^ 2 - 25) / 3)) * log (1 + d)
  + (-(2 * d * (17 * d ^ 2 - 25) / 3)) * log d := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY2Q, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWYG2, ksWYv_e1, ksWYv_e2, ksWYv_e3, ksWYv_e4, sub_zero, log_neg_eq_log,
    ksWY_log_sm hd.2, ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_self, log_zero, mul_zero,
    add_zero]
  field_simp
  ring

theorem ksWYv_2C (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY2C d).map fun t => t.1
  * (ksWYG3 t.2.1 t.2.2 ((1 + d) / 2) - ksWYG3 t.2.1 t.2.2 ((1 - d) / 2))).sum =
      (4 * (d
  - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) * log (1 - d) + (-(4 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3))
  * log (1 + d) + (16 * d * (2 * d ^ 2 - 3) / 3) * log d + 8 * d * (d - 1) * (2 * d ^ 2 - 3)
  / 3 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY2C, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWYG3, ksWYv_e1, ksWYv_e2, ksWYv_e3, ksWYv_e4, sub_zero, log_neg_eq_log,
    ksWY_log_sm hd.2, ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_self, log_zero, mul_zero,
    zero_mul, add_zero, even_two, Even.neg_pow]
  field_simp
  ring

theorem ksWYv_2R (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY2R d).map fun t => ksWPQ t.1 t.2.1 t.2.2 ((1
  + d) / 2) - ksWPQ t.1 t.2.1 t.2.2 ((1 - d) / 2)).sum =
      (-((d + 1) * (d - 1) * (8 * d ^ 2
  + d - 13) / 3)) * log (1 - d) + ((8 * d ^ 4 + 35 * d ^ 3 - 21 * d ^ 2 - 51 * d + 13) / 3)
  * log (1 + d) + (-(2 * d * (17 * d ^ 2 - 25) / 3)) * log 2 + (-(16 * d * (d - 1) * (2 * d ^ 2
  - 3) / 3)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY2R, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWPQ, ksWYv_e1, ksWYv_e2, sub_zero, log_neg_eq_log, ksWY_log_sm hd.2,
    ksWY_log_sp (by linarith [hd.1] : -1 < d), add_zero]
  field_simp
  ring

theorem ksWYv_2S (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY2S d).map fun t => -(t.2 / (2 * (((1 + d)
  / 2) - t.1) ^ 2)) + t.2 / (2 * (((1 - d) / 2) - t.1) ^ 2)).sum =
      (-(16 * d * (2 * d ^ 2
  - 3) / 3)) * log (1 + d) + (16 * d * (2 * d ^ 2 - 3) / 3) * log 2 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY2S, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWYv_e1, ksWYv_e2, sub_zero, add_zero, even_two, Even.neg_pow]
  field_simp
  ring

theorem ksWYv_3L (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWPv (ksWY3L d) (ksWY3P d) ((1 + d)
  / 2) 1 =
      (-((d + 1) * (d - 1) * (5 * d ^ 2 + 2 * d + 5) / 12)) * log (1 - d) + ((13
  * d ^ 4 - 2 * d ^ 3 - 24 * d ^ 2 + 2 * d - 5) / 12) * log (1 + d) + (-(d * (2 * d ^ 3 - d ^ 2
  - 6 * d + 1) / 3)) * log 2 + (-(d * (2 * d ^ 3 - d ^ 2 - 6 * d + 1) / 3)) * log d + (-(d * (d
  - 1) * (13 * d ^ 2 + 9 * d + 30) / 18)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWPv, ksWY3L, ksWY3P, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWPH, ksWPs, ksWPr, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_pow, ksWYv_e3,
    ksWYv_e5, ksWYv_e6, zero_sub, ksWY_log_sm hd.2, ksWY_log_sp (by linarith [hd.1] : -1 < d),
    sub_self, log_zero, mul_zero, add_zero, zero_add]
  field_simp
  ring

theorem ksWYv_3D (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY3D d).map fun t => t.1 * (ksWYD ((1 - t.2.2)
  / (t.2.1 - t.2.2)) -
      ksWYD ((((1 + d) / 2) - t.2.2) / (t.2.1 - t.2.2)))).sum =
      (10
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * log (1 - d) * log (1 + d) + (-(10 * (d ^ 2 + 1) * (d ^ 2 - 3)
  / 3)) * log 2 * log (1 - d) + (2 * (d ^ 2 + 1) * (d ^ 2 - 3)) * log d * log (1 - d) + (-(10
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) * log 2 * log (1 + d) + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3)))
  * log d * log (1 + d) + (10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) * log 2 ^ 2 + (4 * (d ^ 2 + 1)
  * (d ^ 2 - 3)) * Li₂ d + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3))) * Li₂ (-d) + (20 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3) * Li₂ ((1 - d) / 2) + (-((d ^ 2 + 1) * (d ^ 2 - 3))) * π ^ 2 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY3D, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [ksWYv_D21 hd, ksWYv_D22 hd, ksWYv_D23 hd, ksWYv_D13, ksWYv_D24 hd, ksWYv_D25 hd, ksWYv_D26 hd,
    ksWYv_D17, ksWYv_D27 hd, ksWYv_D18 hd, ksWYv_D28 hd, ksWYv_D20 hd]
  ring

theorem ksWYv_3Q (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY3Q d).map fun t => t.1
  * (ksWYG2 t.2.1 t.2.2 1 - ksWYG2 t.2.1 t.2.2 ((1 + d) / 2))).sum =
      (-((d - 1) ^ 2 * (17
  * d ^ 2 - 25) / 12)) * log (1 - d) + ((17 * d ^ 2 - 25) * (d ^ 2 + 6 * d + 1) / 12) * log (1
  + d) + (-(2 * d * (17 * d ^ 2 - 25) / 3)) * log 2 + (-(d * (17 * d ^ 2 - 25) / 3)) * log d := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY3Q, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWYG2, ksWYv_e3, ksWYv_e5, ksWYv_e6, sub_zero, ksWY_log_sm hd.2,
    ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_self, log_zero, log_one, mul_zero, add_zero]
  field_simp
  ring

theorem ksWYv_3C (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY3C d).map fun t => t.1
  * (ksWYG3 t.2.1 t.2.2 1 - ksWYG3 t.2.1 t.2.2 ((1 + d) / 2))).sum =
      (-((d - 1) ^ 3 * (2
  * d ^ 2 - 3) * (d + 3) / 6)) * log (1 - d) + ((2 * d ^ 2 - 3) * (d ^ 4 - 6 * d ^ 2 - 24 * d - 3)
  / 6) * log (1 + d) + (16 * d * (2 * d ^ 2 - 3) / 3) * log 2 + (8 * d * (2 * d ^ 2 - 3) / 3)
  * log d + 2 * d * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY3C, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWYG3, one_pow, ksWYv_e3, ksWYv_e5, ksWYv_e6, sub_zero, ksWY_log_sm hd.2,
    ksWY_log_sp (by linarith [hd.1] : -1 < d), sub_self, log_zero, log_one, mul_zero, zero_mul,
    add_zero]
  field_simp
  ring

theorem ksWYv_3R (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY3R d).map fun t => ksWPQ t.1 t.2.1 t.2.2 1
  - ksWPQ t.1 t.2.1 t.2.2 ((1 + d) / 2)).sum =
      (-((d - 1) ^ 2 * (17 * d ^ 2 - 25) / 12))
  * log (1 - d) + ((d - 1) * (17 * d ^ 3 - 21 * d ^ 2 - 29 * d + 25) / 12) * log (1 + d) + (d * (d
  + 1) * (d - 1) / 3) * log 2 + (-(4 * d * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY3R, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [ksWPQ, sub_zero, zero_sub, ksWY_log_sp (by linarith [hd.1] : -1 < d), log_one,
    mul_zero, add_zero]
  field_simp
  ring

theorem ksWYv_3S (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((ksWY3S d).map fun t => -(t.2 / (2 * (1
  - t.1) ^ 2)) + t.2 / (2 * (((1 + d) / 2) - t.1) ^ 2)).sum =
      (-((d - 1) ^ 3 * (2 * d ^ 2
  - 3) * (d + 3) / 6)) * log (1 - d) + ((d - 1) ^ 3 * (2 * d ^ 2 - 3) * (d + 3) / 6) * log (1
  + d) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  simp only [ksWY3S, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [one_pow, sub_zero, add_zero]
  field_simp
  ring

theorem ksWYv_m1 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (-(d * (d - 1) * (13 * d ^ 2 + 9 * d + 30) / 18))
  + (2 * d * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) + (-(4 * d * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3))
  + (d * (13 * d ^ 3 - 38 * d ^ 2 + 21 * d + 96) / 9) + (8 * d * (d - 1) * (2 * d ^ 2 - 3) / 3)
  + (-(16 * d * (d - 1) * (2 * d ^ 2 - 3) / 3)) + (-(d * (d - 1) * (13 * d ^ 2 + 9 * d + 30)
  / 18)) + (2 * d * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) + (-(4 * d * (d - 1) ^ 2 * (2 * d ^ 2 - 3)
  / 3)) = (-(2 * d * (12 * d ^ 4 - 13 * d ^ 2 - 45) / 9)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m2 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (-((d ^ 2 + 1) * (d ^ 2 - 3))) + (-(2 * (d ^ 2
  + 1) * (d ^ 2 - 3) / 3)) + (-((d ^ 2 + 1) * (d ^ 2 - 3))) = (-(8 * (d ^ 2 + 1) * (d ^ 2 - 3)
  / 3)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m3 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (20 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) + (8 * (d ^ 2
  + 1) * (d ^ 2 - 3) / 3) + (20 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) = 16 * (d ^ 2 + 1) * (d ^ 2
  - 3) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m4 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3))) + (-(8 * (d ^ 2
  + 1) * (d ^ 2 - 3) / 3)) + (-(4 * (d ^ 2 + 1) * (d ^ 2 - 3))) = (-(32 * (d ^ 2 + 1) * (d ^ 2
  - 3) / 3)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m5 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (4 * (d ^ 2 + 1) * (d ^ 2 - 3)) + (8 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3) + (4 * (d ^ 2 + 1) * (d ^ 2 - 3)) = 32 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m6 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (-(d * (2 * d ^ 3 - d ^ 2 - 6 * d + 1) / 3))
  + (-(d * (17 * d ^ 2 - 25) / 3)) + (8 * d * (2 * d ^ 2 - 3) / 3) + (2 * d * (2 * d ^ 3 + d ^ 2
  - 6 * d - 1) / 3) + (-(2 * d * (17 * d ^ 2 - 25) / 3)) + (16 * d * (2 * d ^ 2 - 3) / 3) + (-(d
  * (2 * d ^ 3 - d ^ 2 - 6 * d + 1) / 3)) + (-(d * (17 * d ^ 2 - 25) / 3)) + (8 * d * (2 * d ^ 2
  - 3) / 3) = 0 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m7 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (-(d * (2 * d ^ 3 - d ^ 2 - 6 * d + 1) / 3))
  + (-(2 * d * (17 * d ^ 2 - 25) / 3)) + (16 * d * (2 * d ^ 2 - 3) / 3) + (d * (d + 1) * (d - 1)
  / 3) + (2 * d * (2 * d ^ 3 + d ^ 2 - 6 * d - 1) / 3) + (-(2 * d * (17 * d ^ 2 - 25) / 3)) + (16
  * d * (2 * d ^ 2 - 3) / 3) + (-(d * (2 * d ^ 3 - d ^ 2 - 6 * d + 1) / 3)) + (-(2 * d * (17
  * d ^ 2 - 25) / 3)) + (16 * d * (2 * d ^ 2 - 3) / 3) + (d * (d + 1) * (d - 1) / 3) = 0 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m8 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) + (4 * (d ^ 2
  + 1) * (d ^ 2 - 3) / 3) + (10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) = 8 * (d ^ 2 + 1) * (d ^ 2
  - 3) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m9 (hd : d ∈ Ioo (0 : ℝ) 1) :
    ((13 * d ^ 4 - 2 * d ^ 3 - 24 * d ^ 2 + 2 * d - 5)
  / 12) + ((17 * d ^ 2 - 25) * (d ^ 2 + 6 * d + 1) / 12) + ((2 * d ^ 2 - 3) * (d ^ 4 - 6 * d ^ 2
  - 24 * d - 3) / 6) + ((d - 1) * (17 * d ^ 3 - 21 * d ^ 2 - 29 * d + 25) / 12) + ((d - 1) ^ 3
  * (2 * d ^ 2 - 3) * (d + 3) / 6) + ((d + 1) * (d - 1) * (5 * d ^ 2 - 2 * d + 5) / 6) + (-((d
  - 1) * (17 * d ^ 2 - 25) / 3)) + (-(4 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3)) + ((8 * d ^ 4 + 35
  * d ^ 3 - 21 * d ^ 2 - 51 * d + 13) / 3) + (-(16 * d * (2 * d ^ 2 - 3) / 3)) + ((13 * d ^ 4 - 2
  * d ^ 3 - 24 * d ^ 2 + 2 * d - 5) / 12) + ((17 * d ^ 2 - 25) * (d ^ 2 + 6 * d + 1) / 12) + ((2
  * d ^ 2 - 3) * (d ^ 4 - 6 * d ^ 2 - 24 * d - 3) / 6) + ((d - 1) * (17 * d ^ 3 - 21 * d ^ 2 - 29
  * d + 25) / 12) + ((d - 1) ^ 3 * (2 * d ^ 2 - 3) * (d + 3) / 6) = (4 * d ^ 6 - 4 * d ^ 4 + 4
  * d ^ 2 - 12) / 3 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m10 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3))) + (-(4
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) + (-(2 * (d ^ 2 + 1) * (d ^ 2 - 3))) = (-(16 * (d ^ 2 + 1)
  * (d ^ 2 - 3) / 3)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m11 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (-(10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) + (-(4
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) + (-(10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) = (-(8 * (d ^ 2 + 1)
  * (d ^ 2 - 3))) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m12 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (-((d + 1) * (d - 1) * (5 * d ^ 2 + 2 * d + 5)
  / 12)) + (-((d - 1) ^ 2 * (17 * d ^ 2 - 25) / 12)) + (-((d - 1) ^ 3 * (2 * d ^ 2 - 3) * (d + 3)
  / 6)) + (-((d - 1) ^ 2 * (17 * d ^ 2 - 25) / 12)) + (-((d - 1) ^ 3 * (2 * d ^ 2 - 3) * (d + 3)
  / 6)) + (-((13 * d ^ 4 + 2 * d ^ 3 - 24 * d ^ 2 - 2 * d - 5) / 6)) + ((d - 1) * (17 * d ^ 2
  - 25) / 3) + (4 * (d - 1) ^ 2 * (2 * d ^ 2 - 3) / 3) + (-((d + 1) * (d - 1) * (8 * d ^ 2 + d
  - 13) / 3)) + (-((d + 1) * (d - 1) * (5 * d ^ 2 + 2 * d + 5) / 12)) + (-((d - 1) ^ 2 * (17
  * d ^ 2 - 25) / 12)) + (-((d - 1) ^ 3 * (2 * d ^ 2 - 3) * (d + 3) / 6)) + (-((d - 1) ^ 2 * (17
  * d ^ 2 - 25) / 12)) + (-((d - 1) ^ 3 * (2 * d ^ 2 - 3) * (d + 3) / 6)) = (-((4 * d ^ 6 - 4
  * d ^ 4 + 4 * d ^ 2 - 12) / 3)) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m13 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (2 * (d ^ 2 + 1) * (d ^ 2 - 3)) + (4 * (d ^ 2
  + 1) * (d ^ 2 - 3) / 3) + (2 * (d ^ 2 + 1) * (d ^ 2 - 3)) = 16 * (d ^ 2 + 1) * (d ^ 2 - 3)
  / 3 := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m14 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (-(10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) + (-(4
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) + (-(10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3)) = (-(8 * (d ^ 2 + 1)
  * (d ^ 2 - 3))) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

theorem ksWYv_m15 (hd : d ∈ Ioo (0 : ℝ) 1) :
    (10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) + (4
  * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) + (10 * (d ^ 2 + 1) * (d ^ 2 - 3) / 3) = 8 * (d ^ 2 + 1)
  * (d ^ 2 - 3) := by
  have hdm : 1 - d ≠ 0 := (by linarith [hd.2] : (0 : ℝ) < 1 - d).ne'
  have hdp : 1 + d ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < 1 + d).ne'
  have hd0 : d ≠ 0 := hd.1.ne'
  have hdm' : d - 1 ≠ 0 := (by linarith [hd.2] : d - 1 < 0).ne
  have hdp' : d + 1 ≠ 0 := (by linarith [hd.1] : (0 : ℝ) < d + 1).ne'
  field_simp
  ring

/-- **The `β`-integral in closed form**: the three values sum to `ksWRBv δ`. -/
theorem ksWYv_total (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWYv (ksWY1L d) (ksWY1P d) (ksWY1D d) (ksWY1Q d) (ksWY1C d) (ksWY1R d) (ksWY1S d) 0
        ((1 - d) / 2) +
      ksWYv (ksWY2L d) (ksWY2P d) (ksWY2D d) (ksWY2Q d) (ksWY2C d) (ksWY2R d) (ksWY2S d)
        ((1 - d) / 2) ((1 + d) / 2) +
      ksWYv (ksWY3L d) (ksWY3P d) (ksWY3D d) (ksWY3Q d) (ksWY3C d) (ksWY3R d) (ksWY3S d)
        ((1 + d) / 2) 1 = ksWRBv d := by
  have hdp : (0 : ℝ) < 1 + d := by linarith [hd.1]
  have hdm : (0 : ℝ) < 1 - d := by linarith [hd.2]
  have hA := Li_two_ksT hd
  have hB := Li_two_neg_ksT hd
  rw [Li_two] at hA hB
  have hl1 : log ((1 + d) ^ 3 / (8 * d ^ 2)) = 3 * log (1 + d) - 3 * log 2 - 2 * log d := by
    rw [log_div (pow_pos hdp 3).ne' (mul_pos (by norm_num) (pow_pos hd.1 2)).ne', log_pow,
      log_mul (by norm_num) (pow_pos hd.1 2).ne',
      log_pow, show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
    push_cast
    ring
  have hl3 : log (64 * d ^ 4 / (1 - d ^ 2) ^ 3) =
      6 * log 2 + 4 * log d - 3 * log (1 - d) - 3 * log (1 + d) := by
    have h1 : (1 : ℝ) - d ^ 2 = (1 - d) * (1 + d) := by ring
    rw [log_div (mul_pos (by norm_num) (pow_pos hd.1 4)).ne'
      (pow_pos (by rw [h1]; exact mul_pos hdm hdp) 3).ne', log_mul (by norm_num)
      (pow_pos hd.1 4).ne', log_pow, log_pow, h1, log_mul hdm.ne' hdp.ne',
      show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow]
    push_cast
    ring
  unfold ksWYv ksWRBv ksRho ksRhoDm ksWRAv ksWRAn
  rw [hA, hB, hl1, ksWYv_log_b hd, hl3]
  have hdd : d * d⁻¹ = 1 := mul_inv_cancel₀ hd.1.ne'
  linear_combination ksWYv_1L hd + ksWYv_1D hd + ksWYv_1Q hd + ksWYv_1C hd + ksWYv_1R hd
    + ksWYv_1S hd + ksWYv_2L hd + ksWYv_2D hd + ksWYv_2Q hd + ksWYv_2C hd + ksWYv_2R hd
    + ksWYv_2S hd + ksWYv_3L hd + ksWYv_3D hd + ksWYv_3Q hd + ksWYv_3C hd + ksWYv_3R hd
    + ksWYv_3S hd + (ksWYv_m1 hd) + (π ^ 2 * ksWYv_m2 hd) + (Li₂ ((1 - d) / 2) * ksWYv_m3 hd)
    + (Li₂ (-d) * ksWYv_m4 hd) + (Li₂ d * ksWYv_m5 hd) + (log d * ksWYv_m6 hd) + (log 2
    * ksWYv_m7 hd) + (log 2 ^ 2 * ksWYv_m8 hd) + (log (1 + d) * ksWYv_m9 hd) + (log d * log (1
    + d) * ksWYv_m10 hd) + (log 2 * log (1 + d) * ksWYv_m11 hd) + (log (1 - d) * ksWYv_m12 hd)
    + (log d * log (1 - d) * ksWYv_m13 hd) + (log 2 * log (1 - d) * ksWYv_m14 hd) + (log (1 - d)
    * log (1 + d) * ksWYv_m15 hd) + (8 / 3 * d ^ 5 - 80 / 9 * d ^ 3) * hdd

end QED.ChainProof.SetAKS

end
