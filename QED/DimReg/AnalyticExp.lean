/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analyticity of Lee–Pomeransky integrals in one exponent

`QED.DimReg.analyticOnNhd_lpIntegral_exp`: if the integral converges absolutely when the `i`-th
exponent is the real number `a` and when it is `b`, with the other exponents and `d` fixed, then
`t ↦ lpIntegral G (update ν i t) d` is analytic on the strip `a < re t < b`. This is the
analytic-regularization counterpart of `QED.DimReg.analyticOnNhd_lpIntegral_dim`: the factor
`xᵢ ^ (t - 1) = xᵢ⁻¹ exp(t log xᵢ)` has the form required by
`QED.DimReg.differentiableOn_integral_mul_exp`.
-/

public section

open MeasureTheory Set Complex

namespace QED.DimReg

variable {N : ℕ}

/-- Splitting off the `i`-th exponent: on the orthant,
`J-integrand(update ν i t) = J-integrand(update ν i 0) · exp(t log xᵢ)`. -/
theorem lpIntegrand_update_eq (G : (Fin N → ℝ) → ℝ) (ν : Fin N → ℂ) (d : ℂ) (i : Fin N)
    (t : ℂ) {x : Fin N → ℝ} (hx : x ∈ posOrthant N) :
    lpIntegrand G (Function.update ν i t) d x =
      lpIntegrand G (Function.update ν i 0) d x * exp (t * (Real.log (x i) : ℂ)) := by
  have hxi := (mem_posOrthant.mp hx) i
  have hxi0 : (x i : ℂ) ≠ 0 := ofReal_ne_zero.mpr hxi.ne'
  simp only [lpIntegrand]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => (x j : ℂ) ^ (Function.update ν i 0 j - 1))
      (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, (x j : ℂ) ^ (Function.update ν i t j - 1) =
      ∏ j ∈ Finset.univ.erase i, (x j : ℂ) ^ (Function.update ν i 0 j - 1) :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj),
        Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hexp : exp (t * (Real.log (x i) : ℂ)) = (x i : ℂ) ^ t := by
    rw [cpow_def_of_ne_zero hxi0, ← ofReal_log hxi.le, mul_comm]
  rw [hrest, hexp, Function.update_self, Function.update_self, zero_sub,
    show t - 1 = -1 + t by ring, cpow_add _ _ hxi0]
  ring

/-- **Analyticity in one exponent** on the interior of its strip of absolute convergence. -/
theorem analyticOnNhd_lpIntegral_exp {G : (Fin N → ℝ) → ℝ} (hG : Measurable G) (ν : Fin N → ℂ)
    (d : ℂ) (i : Fin N) {a b : ℝ}
    (ha : LPConvergent G (Function.update ν i a) d)
    (hb : LPConvergent G (Function.update ν i b) d) :
    AnalyticOnNhd ℂ (fun t => lpIntegral G (Function.update ν i t) d)
      {t | a < t.re ∧ t.re < b} := by
  have hopen : IsOpen {t : ℂ | a < t.re ∧ t.re < b} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  set μ := volume.restrict (posOrthant N)
  set f := lpIntegrand G (Function.update ν i 0) d
  set φ : (Fin N → ℝ) → ℝ := fun x => Real.log (x i)
  have hrep : ∀ t : ℂ, lpIntegral G (Function.update ν i t) d =
      ∫ x, f x * exp (t * φ x) ∂μ := fun t =>
    setIntegral_congr_fun (measurableSet_posOrthant N) fun x hx =>
      lpIntegrand_update_eq G ν d i t hx
  have hf : AEStronglyMeasurable f μ := (measurable_lpIntegrand hG _ d).aestronglyMeasurable
  have hφ : AEStronglyMeasurable φ μ :=
    (Real.measurable_log.comp (measurable_pi_apply i)).aestronglyMeasurable
  have hconv : ∀ c : ℝ, LPConvergent G (Function.update ν i c) d →
      Integrable (fun x => ‖f x‖ * Real.exp (c * φ x)) μ := by
    intro c hc
    refine hc.norm.congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_posOrthant N)] with x hx
    rw [lpIntegrand_update_eq G ν d i c hx, norm_mul, norm_exp]
    simp [φ, f]
  exact (differentiableOn_integral_mul_exp hf hφ (hconv a ha) (hconv b hb)).congr
    fun t _ => hrep t

end QED.DimReg
