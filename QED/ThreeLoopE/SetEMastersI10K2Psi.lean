/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10K2Factor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The first two Taylor kernels of the inner integral of `K₂`

Multiplying by an exponential shifts each exponent in the two-term
representation of the integrand. The shift accounts for the logarithmic
variation of the weights in the outer integral.
-/

@[expose] public section

open Set Complex MeasureTheory QED.ThreeLoopD

namespace QED.ThreeLoopE

/-- The positive base in the power that couples the two parameters of `ψ`. -/
def i10PsiBase (t u : ℝ) : ℝ := 1 - (1 - u) * t

/-- The coefficient of degree one in the integrand of `ψ`. -/
noncomputable def i10PsiCoeffOne (t u : ℝ) : ℝ :=
  let q := i10PsiBase t u
  let L := Real.log t - Real.log u
  (-(1 - u)) * L - 3 * q * Real.log q / t

/-- The coefficient of degree two in the integrand of `ψ`. -/
noncomputable def i10PsiCoeffTwo (t u : ℝ) : ℝ :=
  let q := i10PsiBase t u
  let L := Real.log t - Real.log u
  (-(1 - u)) * L ^ 2 / 2 - 3 * q * Real.log q * L / t +
    (9 / 2) * q * Real.log q ^ 2 / t

theorem i10PsiBase_pos {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    0 < i10PsiBase t u := by
  unfold i10PsiBase
  nlinarith only [ht.2, mul_nonneg ht.1.le hu.1]

private theorem i10PsiF_mul_exp_eq {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) (M ε : ℂ) :
    let q : ℝ := i10PsiBase t u
    let L : ℂ := (Real.log t : ℂ) - (Real.log u : ℂ) + M
    exp (M * ε) * i10PsiF ε t u =
      (q : ℂ) / t * exp ((L - 3 * (Real.log q : ℂ)) * ε) -
        (t : ℂ)⁻¹ * exp (L * ε) := by
  dsimp only
  have hq := i10PsiBase_pos ht (Ioo_subset_Icc_self hu)
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
  have hu' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
  have hq' : (i10PsiBase t u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq.ne'
  change exp (M * ε) * ((u : ℂ) ^ (-ε) * ((t : ℂ) ^ (ε - 1) *
    ((i10PsiBase t u : ℂ) ^ (1 - 3 * ε) - 1))) = _
  rw [show ε - 1 = (-1 : ℂ) + ε by ring, show 1 - 3 * ε = 1 + -(3 * ε) by ring,
    cpow_add _ _ ht', cpow_add _ _ hq', cpow_neg_one, cpow_one,
    cpow_def_of_ne_zero hu', cpow_def_of_ne_zero ht', cpow_def_of_ne_zero hq',
    ← ofReal_log hu.1.le, ← ofReal_log ht.1.le, ← ofReal_log hq.le]
  rw [show ((Real.log t : ℂ) - Real.log u + M - 3 * Real.log (i10PsiBase t u)) * ε =
      M * ε + (Real.log u : ℂ) * (-ε) + (Real.log t : ℂ) * ε +
        (Real.log (i10PsiBase t u) : ℂ) * -(3 * ε) by ring,
    show ((Real.log t : ℂ) - Real.log u + M) * ε =
      M * ε + (Real.log u : ℂ) * (-ε) + (Real.log t : ℂ) * ε by ring]
  simp only [exp_add, div_eq_mul_inv]
  ring

private theorem iteratedDeriv_i10PsiF_mul_exp {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) (M : ℂ) (n : ℕ) :
    let q : ℝ := i10PsiBase t u
    let L : ℂ := (Real.log t : ℂ) - (Real.log u : ℂ) + M
    iteratedDeriv n (fun ε => exp (M * ε) * i10PsiF ε t u) 0 =
      (q : ℂ) / t * (L - 3 * (Real.log q : ℂ)) ^ n - (t : ℂ)⁻¹ * L ^ n := by
  dsimp only
  rw [funext (i10PsiF_mul_exp_eq ht hu M)]
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul, mul_zero,
    exp_zero, mul_one]

theorem deriv_i10PsiF_mul_exp_zero {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) (M : ℂ) :
    deriv (fun ε => exp (M * ε) * i10PsiF ε t u) 0 =
      (i10PsiCoeffOne t u : ℂ) + M * ((u : ℂ) - 1) := by
  rw [← iteratedDeriv_one, iteratedDeriv_i10PsiF_mul_exp ht hu]
  simp only [pow_one, i10PsiCoeffOne, ofReal_sub, ofReal_one, ofReal_mul, ofReal_neg,
    ofReal_div, ofReal_ofNat, i10PsiBase]
  field_simp [ofReal_ne_zero.mpr ht.1.ne']
  ring

theorem iteratedDeriv_two_i10PsiF_mul_exp_zero {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) (M : ℂ) :
    iteratedDeriv 2 (fun ε => exp (M * ε) * i10PsiF ε t u) 0 =
      2 * (i10PsiCoeffTwo t u : ℂ) + 2 * M * (i10PsiCoeffOne t u : ℂ) +
        M ^ 2 * ((u : ℂ) - 1) := by
  rw [iteratedDeriv_i10PsiF_mul_exp ht hu]
  simp only [i10PsiCoeffOne, i10PsiCoeffTwo, ofReal_sub, ofReal_one, ofReal_mul,
    ofReal_neg, ofReal_div, ofReal_ofNat, ofReal_add, ofReal_pow, i10PsiBase]
  field_simp [ofReal_ne_zero.mpr ht.1.ne']
  ring

/-- The linear interpolation subtraction used in the definition of `K₂`. -/
def i10K2Interpolation (g : ℝ → ℝ) (z r s : ℝ) : ℝ :=
  g (i10Tau z r s) - (1 - z) * g s - z * g r

/-- The logarithmic slope of the bubble and joining weights. -/
noncomputable def i10K2LogWeight (z r s : ℝ) : ℝ :=
  Real.log (z * (1 - z)) - Real.log (1 - r) - Real.log (1 - s)

/-- The coefficient integrand of degree one after the interpolation subtraction. -/
noncomputable def i10K2CoeffOne (p : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  let (z, r, s) := p.1
  i10K2Interpolation (fun t => i10PsiCoeffOne t p.2) z r s / (z * (1 - z))

/-- The coefficient integrand of degree two after the interpolation subtraction. -/
noncomputable def i10K2CoeffTwo (p : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  let (z, r, s) := p.1
  (i10K2Interpolation (fun t => i10PsiCoeffTwo t p.2) z r s +
    i10K2LogWeight z r s * i10K2Interpolation (fun t => i10PsiCoeffOne t p.2) z r s) /
      (z * (1 - z))

private theorem i10K2F_eq_shifted {z r s u : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) (ε : ℂ) :
    let V := fun t => exp ((i10K2LogWeight z r s : ℂ) * ε) * i10PsiF ε t u
    i10K2F ε ((z, r, s), u) = ((z * (1 - z) : ℝ) : ℂ)⁻¹ *
      (V (i10Tau z r s) - (1 - (z : ℂ)) * V s - (z : ℂ) * V r) := by
  have hz0 := mul_pos hz.1 (sub_pos.mpr hz.2)
  have hr0 := sub_pos.mpr hr.2
  have hs0 := sub_pos.mpr hs.2
  have hw : ((z * (1 - z) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz0.ne'
  dsimp [i10K2F, i10K2B, i10A, i10W, i10K2LogWeight]
  rw [show ε - 1 = (-1 : ℂ) + ε by ring, cpow_add _ _ hw, cpow_neg_one,
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr0.ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hs0.ne'), cpow_def_of_ne_zero hw,
    ← ofReal_log hr0.le, ← ofReal_log hs0.le, ← ofReal_log hz0.le]
  push_cast
  rw [show ((Real.log (z * (1 - z)) : ℂ) - Real.log (1 - r) - Real.log (1 - s)) * ε =
    (Real.log (1 - r) : ℂ) * (-ε) + (Real.log (1 - s) : ℂ) * (-ε) +
      (Real.log (z * (1 - z)) : ℂ) * ε by ring]
  simp only [exp_add]
  ring

theorem deriv_i10K2F_zero {p : (ℝ × ℝ × ℝ) × ℝ} (hp : p ∈ i10K2Domain) :
    deriv (fun ε => i10K2F ε p) 0 = (i10K2CoeffOne p : ℂ) := by
  obtain ⟨⟨z, r, s⟩, u⟩ := p
  obtain ⟨⟨hz, hr, hs⟩, hu⟩ := hp
  dsimp only at hz hr hs hu
  have ht := i10Tau_mem_Ioo hz hr hs
  let M : ℂ := i10K2LogWeight z r s
  let V (t : ℝ) (ε : ℂ) := exp (M * ε) * i10PsiF ε t u
  have he : (fun ε => i10K2F ε ((z, r, s), u)) =
      fun ε => ((z * (1 - z) : ℝ) : ℂ)⁻¹ *
        (V (i10Tau z r s) ε - (1 - (z : ℂ)) * V s ε - (z : ℂ) * V r ε) :=
    funext (i10K2F_eq_shifted hz hr hs)
  have hd {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : Differentiable ℂ (V t) :=
    (show Differentiable ℂ (fun ε => exp (M * ε)) by fun_prop).mul
      (differentiable_i10PsiF ht hu)
  have ds := (hd hs).const_mul (1 - (z : ℂ))
  have dr := (hd hr).const_mul (z : ℂ)
  have dts : Differentiable ℂ (fun ε => V (i10Tau z r s) ε - (1 - (z : ℂ)) * V s ε) :=
    (hd ht).sub ds
  rw [he, deriv_const_mul_field,
    deriv_fun_sub dts.differentiableAt dr.differentiableAt,
    deriv_fun_sub (hd ht).differentiableAt ds.differentiableAt,
    deriv_const_mul_field, deriv_const_mul_field]
  dsimp only [V, i10K2CoeffOne, i10K2Interpolation]
  rw [deriv_i10PsiF_mul_exp_zero ht hu, deriv_i10PsiF_mul_exp_zero hs hu,
    deriv_i10PsiF_mul_exp_zero hr hu]
  push_cast
  ring

theorem iteratedDeriv_two_i10K2F_zero {p : (ℝ × ℝ × ℝ) × ℝ} (hp : p ∈ i10K2Domain) :
    iteratedDeriv 2 (fun ε => i10K2F ε p) 0 = 2 * (i10K2CoeffTwo p : ℂ) := by
  obtain ⟨⟨z, r, s⟩, u⟩ := p
  obtain ⟨⟨hz, hr, hs⟩, hu⟩ := hp
  dsimp only at hz hr hs hu
  have ht := i10Tau_mem_Ioo hz hr hs
  let M : ℂ := i10K2LogWeight z r s
  let V (t : ℝ) (ε : ℂ) := exp (M * ε) * i10PsiF ε t u
  have he : (fun ε => i10K2F ε ((z, r, s), u)) =
      fun ε => ((z * (1 - z) : ℝ) : ℂ)⁻¹ *
        (V (i10Tau z r s) ε - (1 - (z : ℂ)) * V s ε - (z : ℂ) * V r ε) :=
    funext (i10K2F_eq_shifted hz hr hs)
  have hd {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : Differentiable ℂ (V t) :=
    (show Differentiable ℂ (fun ε => exp (M * ε)) by fun_prop).mul
      (differentiable_i10PsiF ht hu)
  have ds := (hd hs).const_mul (1 - (z : ℂ))
  have dr := (hd hr).const_mul (z : ℂ)
  have dts : Differentiable ℂ (fun ε => V (i10Tau z r s) ε - (1 - (z : ℂ)) * V s ε) :=
    (hd ht).sub ds
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub dts.contDiff.contDiffAt dr.contDiff.contDiffAt,
    iteratedDeriv_fun_sub (hd ht).contDiff.contDiffAt ds.contDiff.contDiffAt,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  dsimp only [V, i10K2CoeffTwo, i10K2Interpolation]
  rw [iteratedDeriv_two_i10PsiF_mul_exp_zero ht hu,
    iteratedDeriv_two_i10PsiF_mul_exp_zero hs hu, iteratedDeriv_two_i10PsiF_mul_exp_zero hr hu]
  push_cast
  dsimp only [M]
  ring

/-- The Taylor truncation of `K₂` with real coefficient integrals. -/
theorem hasTruncLaurent_i10K2_log_integrals :
    HasTruncLaurent i10K2 (fun ε =>
      ((∫ p in i10K2Domain, i10K2CoeffOne p : ℝ) : ℂ) * ε +
        ((∫ p in i10K2Domain, i10K2CoeffTwo p : ℝ) : ℂ) * ε ^ 2) 3 := by
  have hS : MeasurableSet i10K2Domain :=
    (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)).prod measurableSet_Ioo
  have h1 : (∫ p in i10K2Domain, deriv (fun w => i10K2F w p) 0) =
      ((∫ p in i10K2Domain, i10K2CoeffOne p : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun hS fun _ hp => deriv_i10K2F_zero hp
  have h2 : (∫ p in i10K2Domain, iteratedDeriv 2 (fun w => i10K2F w p) 0) =
      2 * ((∫ p in i10K2Domain, i10K2CoeffTwo p : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    exact setIntegral_congr_fun hS fun _ hp => iteratedDeriv_two_i10K2F_zero hp
  have h := hasTruncLaurent_i10K2_integrals
  simp only [h1, h2] at h
  have hcancel (a : ℂ) : 2 * a / 2 = a := by ring
  simpa only [hcancel] using h

end QED.ThreeLoopE
