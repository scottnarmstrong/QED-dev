/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSIdent

/-!
# R-KS: the mass-mismatch profile, and `SetAKSScal` with every witness fixed

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function. The open
input `SetAKSScal e` asks for the per-flavour photon-regulator limit `decT₀ e μ x s` of R-Π₄ step
L9 in the form `ksG(s/x) + κ log(x/μ²) φ(s/x) + α(μ, s) + β(μ, s) x`.

The mismatch term comes from the mass counterterm, which the model fixes at the counterterm
flavour (mass `μ`) and not at the loop flavour (mass `√x`). Its profile is the one-loop mass
derivative `D(σ) = M ∂_M Π̂(s/M²) = -2σ Π̂'(σ) = -4σ ∫₀¹ t²(1-t)²/(1 + t(1-t)σ) dt` (in
`(α/π)²` units, so `/(16π⁴)` in the model's), with coefficient `κ = -3/4`. Both were checked
numerically against the model (R-Π₄ design spike, check N3: the ratio of the mismatch to
`D` tends to `-0.75`).

Main results:

* `ksDm`, `ksPhi`, `ksKappa`: the profile `D`, `φ = D/(16π⁴)` and `κ = -3/4`;
* `ksPhi_zero`, `norm_ksPhi_sub_le`: `φ` vanishes at `0` and is Lipschitz on `[-1, 1]`;
* `SetAKSFix e`: the remaining analytic statement, with `G = ksG`, `φ = ksPhi`, `κ = -3/4`
  fixed and only the affine part `α + β x` left existential;
* `setAKSScal_of_fix`: `SetAKSFix e → SetAKSScal e`.
-/

@[expose] public section

open Real MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

open QED.GradedProof.RPi4

/-- The integrand of the mismatch profile: `t²(1-t)² σ/(1 + t(1-t)σ)`. -/
noncomputable def ksDmKer (σ t : ℝ) : ℝ :=
  t ^ 2 * (1 - t) ^ 2 * (σ / (1 + t * (1 - t) * σ))

/-- **The one-loop mass derivative** `D(σ) = -4σ ∫₀¹ t²(1-t)²/(1 + t(1-t)σ) dt`, that is
`M ∂_M Π̂(s/M²)` at `σ = s/M²` (`(α/π)` units). -/
noncomputable def ksDm (σ : ℝ) : ℝ :=
  -4 * ∫ t in (0 : ℝ)..1, ksDmKer σ t

/-- **The mismatch profile** in the model's normalization, `D(σ)/(16π⁴)`. -/
noncomputable def ksPhi (σ : ℝ) : ℂ :=
  ((ksDm σ / (16 * π ^ 4) : ℝ) : ℂ)

/-- **The mismatch coefficient** `κ = -3/4`. -/
noncomputable def ksKappa : ℂ := -3 / 4

theorem ksDm_zero : ksDm 0 = 0 := by
  simp [ksDm, ksDmKer]

theorem ksPhi_zero : ksPhi 0 = 0 := by
  simp [ksPhi, ksDm_zero]

/-- The denominator `1 + t(1-t)σ` is at least `3/4` on `t ∈ [0, 1]`, `|σ| ≤ 1`. -/
theorem ksDm_den_ge {σ t : ℝ} (hσ : |σ| ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    3 / 4 ≤ 1 + t * (1 - t) * σ := by
  obtain ⟨h0, h1⟩ := ht
  obtain ⟨hl, hu⟩ := abs_le.1 hσ
  have ha : 0 ≤ t * (1 - t) := mul_nonneg h0 (by linarith)
  have ha' : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left hl ha]

theorem intervalIntegrable_ksDmKer {σ : ℝ} (hσ : |σ| ≤ 1) :
    IntervalIntegrable (ksDmKer σ) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div continuousOn_const (by fun_prop)
    fun t ht => ?_)
  have := ksDm_den_ge hσ ht
  linarith

/-- The pointwise Lipschitz bound of the integrand. -/
theorem abs_ksDmKer_sub_le {σ σ' t : ℝ} (hσ : |σ| ≤ 1) (hσ' : |σ'| ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : |ksDmKer σ t - ksDmKer σ' t| ≤ |σ - σ'| / 4 := by
  have hd := ksDm_den_ge hσ ht
  have hd' := ksDm_den_ge hσ' ht
  obtain ⟨h0, h1⟩ := ht
  set a : ℝ := t * (1 - t) with ha
  have ha0 : 0 ≤ a := mul_nonneg h0 (by linarith)
  have ha1 : a ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have hp : 0 < (1 + a * σ) * (1 + a * σ') := by positivity
  have hprod : 9 / 16 ≤ (1 + a * σ) * (1 + a * σ') := by nlinarith
  have hsq : t ^ 2 * (1 - t) ^ 2 = a ^ 2 := by rw [ha]; ring
  have e : ksDmKer σ t - ksDmKer σ' t = a ^ 2 * (σ - σ') / ((1 + a * σ) * (1 + a * σ')) := by
    simp only [ksDmKer]
    rw [hsq, ← ha]
    field_simp
    ring
  rw [e, abs_div, abs_mul, abs_of_pos hp, abs_of_nonneg (sq_nonneg a), div_le_div_iff₀ hp
    (by norm_num)]
  have ha2 : a ^ 2 ≤ 1 / 16 := by nlinarith
  have hs := abs_nonneg (σ - σ')
  nlinarith [mul_le_mul_of_nonneg_right ha2 hs, mul_le_mul_of_nonneg_left hprod hs]

/-- **`D` is Lipschitz on `[-1, 1]`**, with constant `1`. -/
theorem abs_ksDm_sub_le {σ σ' : ℝ} (hσ : |σ| ≤ 1) (hσ' : |σ'| ≤ 1) :
    |ksDm σ - ksDm σ'| ≤ |σ - σ'| := by
  have e : ksDm σ - ksDm σ' = -4 * ∫ t in (0 : ℝ)..1, (ksDmKer σ t - ksDmKer σ' t) := by
    rw [ksDm, ksDm, integral_sub (intervalIntegrable_ksDmKer hσ)
      (intervalIntegrable_ksDmKer hσ')]
    ring
  have hb : ‖∫ t in (0 : ℝ)..1, (ksDmKer σ t - ksDmKer σ' t)‖ ≤ |σ - σ'| / 4 * |1 - 0| := by
    refine norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    rw [Real.norm_eq_abs]
    exact abs_ksDmKer_sub_le hσ hσ' (Ioc_subset_Icc_self ht)
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hb
  rw [e, abs_mul]
  norm_num
  linarith

/-- The Lipschitz constant of `ksPhi` on `[-1, 1]`. -/
noncomputable def ksPhiLip : ℝ := 1 / (16 * π ^ 4)

theorem ksPhiLip_nonneg : 0 ≤ ksPhiLip := by
  rw [ksPhiLip]
  positivity

/-- **`φ` is Lipschitz on `[-1, 1]`.** -/
theorem norm_ksPhi_sub_le {σ σ' : ℝ} (hσ : |σ| ≤ 1) (hσ' : |σ'| ≤ 1) :
    ‖ksPhi σ - ksPhi σ'‖ ≤ ksPhiLip * |σ - σ'| := by
  have hp : 0 < 16 * π ^ 4 := by positivity
  rw [ksPhi, ksPhi, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← sub_div,
    abs_div, abs_of_pos hp, ksPhiLip, one_div_mul_eq_div, div_le_div_iff_of_pos_right hp]
  exact abs_ksDm_sub_le hσ hσ'

/-- **The remaining analytic input of (R-KS), with every witness fixed**: the per-flavour
photon-regulator limit of R-Π₄ step L9 is the Källén–Sabry profile plus the mass mismatch
`-(3/4) log(x/μ²) D(s/x)/(16π⁴)`, up to an affine function of `x = M²`. -/
def SetAKSFix (e : ℝ) : Prop :=
  ∃ α β : ℝ → ℝ → ℂ, ∀ μ x s : ℝ, 0 < μ → μ ^ 2 ≤ x → -(4 * μ ^ 2) < s →
    decT₀ e μ x s = decT ksG ksPhi ksKappa μ x s + (α μ s + β μ s * x)

/-- **`SetAKSFix → SetAKSScal`.** -/
theorem setAKSScal_of_fix {e : ℝ} (h : SetAKSFix e) : SetAKSScal e := by
  obtain ⟨α, β, hT⟩ := h
  exact ⟨ksPhi, ksKappa, 1, ksPhiLip, α, β, one_pos, ksPhiLip_nonneg, ksPhi_zero,
    fun σ σ' hσ hσ' => norm_ksPhi_sub_le hσ hσ', hT⟩

end QED.ChainProof.SetAKS

end
