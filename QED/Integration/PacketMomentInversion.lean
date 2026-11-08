/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Fourier inversion at the origin on `ℝ³`

For a continuous integrable `h : (Fin 3 → ℝ) → ℂ` whose Fourier integral
`g x = ∫ d³Q h(Q) e^{i Q·x}` is integrable, the integral of `g` is `(2π)³ h(0)`.
This is the Fourier inversion formula evaluated at the origin, written in the physics
normalization on the coordinate space `Fin 3 → ℝ`.

## Main statements

* `QED.Integration.integral_integral_mul_cexp_eq`:
  `∫ d³x ∫ d³Q h(Q) e^{i Q·x} = (2π)³ h(0)`.

## Implementation notes

Mathlib's Fourier transform `𝓕` lives on real inner product spaces and uses the kernel
`e^{-2πi⟨v, w⟩}`. We transport `h` to `EuclideanSpace ℝ (Fin 3)` along the volume-preserving
equivalence `PiLp.ofLp`, identify `g` with `𝓕 h` composed with the dilation `x ↦ -(2π)⁻¹ x`,
rescale the integral, and apply `MeasureTheory.Integrable.fourierInv_fourier_eq` at `0`.
-/

public section

open MeasureTheory Complex
open scoped FourierTransform

namespace QED.Integration

private lemma fourier_ofLp_eq (h : (Fin 3 → ℝ) → ℂ) (w : EuclideanSpace ℝ (Fin 3)) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin 3) => h (WithLp.ofLp v)) w =
      ∫ Q : Fin 3 → ℝ, h Q *
        cexp (I * ((∑ j, Q j * ((-2 * Real.pi) • WithLp.ofLp w) j : ℝ) : ℂ)) := by
  rw [Real.fourier_eq']
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
  congr 1
  ext Q
  simp only [PiLp.inner_apply, smul_eq_mul, Pi.smul_apply, RCLike.inner_apply, conj_trivial]
  rw [mul_comm (cexp _), mul_comm _ I]
  congr 3
  rw [Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

/-- **Fourier inversion at the origin on `ℝ³`.** If `h` is continuous and integrable and its
Fourier integral `g x = ∫ d³Q h(Q) e^{i Q·x}` is integrable, then `∫ d³x g(x) = (2π)³ h(0)`. -/
theorem integral_integral_mul_cexp_eq {h : (Fin 3 → ℝ) → ℂ} (hc : Continuous h)
    (hi : Integrable h)
    (hg : Integrable fun x : Fin 3 → ℝ => ∫ Q, h Q * cexp (I * ((∑ j, Q j * x j : ℝ) : ℂ))) :
    ∫ x : Fin 3 → ℝ, ∫ Q, h Q * cexp (I * ((∑ j, Q j * x j : ℝ) : ℂ)) =
      (2 * Real.pi) ^ 3 * h 0 := by
  set g : (Fin 3 → ℝ) → ℂ := fun x => ∫ Q, h Q * cexp (I * ((∑ j, Q j * x j : ℝ) : ℂ))
  set h' : EuclideanSpace ℝ (Fin 3) → ℂ := fun v => h (WithLp.ofLp v) with hh'
  have hc_ne : (-2 * Real.pi : ℝ) ≠ 0 := by
    have := Real.pi_pos
    exact mul_ne_zero (by norm_num) this.ne'
  have hT := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have hF : ∀ w, 𝓕 h' w = (fun y => g ((-2 * Real.pi) • y)) (WithLp.ofLp w) :=
    fun w => fourier_ofLp_eq h w
  have hi' : Integrable h' := (hT.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi
  have hFi : Integrable (𝓕 h') := by
    have := (hT.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
      (hg.comp_smul hc_ne)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    exact (hF w).symm
  have hcont : Continuous h' := hc.comp (PiLp.continuous_ofLp 2 _)
  have hinv := hi'.fourierInv_fourier_eq hFi hcont.continuousAt (v := 0)
  rw [Real.fourierInv_eq] at hinv
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] at hinv
  have hEG : ∫ v : EuclideanSpace ℝ (Fin 3), 𝓕 h' v =
      ∫ y : Fin 3 → ℝ, g ((-2 * Real.pi) • y) := by
    rw [← hT.integral_comp' (fun y => g ((-2 * Real.pi) • y))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => hF w)
  have hscale := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Fin 3 → ℝ))
    (fun y => g ((-2 * Real.pi) • y)) (-2 * Real.pi)⁻¹
  simp only [smul_smul, mul_inv_cancel₀ hc_ne, one_smul, Module.finrank_fin_fun] at hscale
  rw [hscale, ← hEG, hinv]
  simp only [hh', WithLp.ofLp_zero, inv_pow, inv_inv, Complex.real_smul]
  rw [abs_pow, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
  push_cast
  ring

end QED.Integration
