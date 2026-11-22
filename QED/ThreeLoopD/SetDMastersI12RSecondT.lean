/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Set (d), master `I₁₂`: second derivatives of the face remainders

The second Taylor coefficient of `QED.ThreeLoopD.i12Rest` contains `(T_A''(0) + T_B''(0)) / 2`
(`QED.ThreeLoopD.iteratedDeriv_two_i12Rest_eq`). Both face integrands have the shape

  `F(ε) = θ ^ (2ε - 1) H ^ (2ε - 1) P ^ ε (Φ₀(X, Y) - (2 - 3ε) Y ^ (-3ε))`

with positive reals `θ, H, P, X, Y`. Expanding `Φ₀`, `F` is a combination of products of real
powers `c ^ (aε + b)`, each with constant logarithmic derivative `a log c`. With
`λ = 2 log θ + 2 log H + log P` and `μ_c = λ - 3 log c`,

  `F''(0) = ((X + Y)² μ_{X+Y}² - X² μ_X² - Y² μ_Y²) / (XY θH) - (2 μ_Y² - 6 μ_Y) / (θH)`

(`QED.ThreeLoopD.i12Tdd`). Differentiating twice under the integral sign
(`QED.ThreeLoopD.i12_hasDerivAt_deriv_integral`) gives `T_A''(0)` and `T_B''(0)` as integrals
of these pointwise values.

## Main results

* `QED.ThreeLoopD.deriv_deriv_i12T_integrand`.
* `QED.ThreeLoopD.deriv_deriv_i12TA_zero`, `QED.ThreeLoopD.deriv_deriv_i12TB_zero`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-! ### Functions with constant logarithmic derivative -/

theorem i12_logDeriv_cpow {c : ℝ} (hc : 0 < c) {e : ℂ → ℂ} {a : ℂ}
    (he : ∀ ε, HasDerivAt e a ε) :
    ∀ ε, HasDerivAt (fun ε => (c : ℂ) ^ e ε) (a * (Real.log c : ℂ) * (c : ℂ) ^ e ε) ε := by
  intro ε
  have := (he ε).const_cpow (c := (c : ℂ)) (Or.inl (ofReal_ne_zero.mpr hc.ne'))
  rw [ofReal_log hc.le]
  exact this.congr_deriv (by ring)

theorem i12_logDeriv_mul {f g : ℂ → ℂ} {μ ν : ℂ} (hf : ∀ ε, HasDerivAt f (μ * f ε) ε)
    (hg : ∀ ε, HasDerivAt g (ν * g ε) ε) :
    ∀ ε, HasDerivAt (fun ε => f ε * g ε) ((μ + ν) * (f ε * g ε)) ε := fun ε =>
  ((hf ε).mul (hg ε)).congr_deriv (by ring)

theorem i12_hasDerivAt_affine (a b : ℂ) : ∀ ε, HasDerivAt (fun ε : ℂ => a * ε + b) a ε :=
  fun ε => by simpa using ((hasDerivAt_id ε).const_mul a).add_const b

/-- First derivative of `(p₀ + p₁ ε) f(ε)` when `f' = μ f`. -/
theorem i12_hasDerivAt_poly_mul {f : ℂ → ℂ} {μ : ℂ} (hf : ∀ ε, HasDerivAt f (μ * f ε) ε)
    (p₀ p₁ : ℂ) :
    ∀ ε, HasDerivAt (fun ε => (p₀ + p₁ * ε) * f ε) ((p₁ + μ * (p₀ + p₁ * ε)) * f ε) ε := by
  intro ε
  have h := (i12_hasDerivAt_affine p₁ p₀ ε).mul (hf ε)
  have e : (fun ε => (p₀ + p₁ * ε) * f ε) = fun ε => (p₁ * ε + p₀) * f ε :=
    funext fun w => by ring
  rw [e]
  exact h.congr_deriv (by ring)

/-- Second derivative at `0` of `(p₀ + p₁ ε) f(ε)` when `f' = μ f`. -/
theorem i12_hasDerivAt_poly_mul_deriv {f : ℂ → ℂ} {μ : ℂ} (hf : ∀ ε, HasDerivAt f (μ * f ε) ε)
    (p₀ p₁ : ℂ) :
    HasDerivAt (fun ε => (p₁ + μ * (p₀ + p₁ * ε)) * f ε) ((2 * p₁ * μ + μ ^ 2 * p₀) * f 0) 0 := by
  have h := i12_hasDerivAt_poly_mul hf (p₁ + μ * p₀) (μ * p₁) 0
  have e : (fun ε => (p₁ + μ * (p₀ + p₁ * ε)) * f ε) =
      fun ε => (p₁ + μ * p₀ + μ * p₁ * ε) * f ε := funext fun w => by ring
  rw [e]
  exact h.congr_deriv (by ring)

/-! ### The generic face integrand -/

/-- `λ = 2 log θ + 2 log H + log P`. -/
noncomputable def i12Lam (θ H P : ℝ) : ℝ := 2 * Real.log θ + 2 * Real.log H + Real.log P

/-- The second `ε`-derivative at `0` of `θ^(2ε-1) H^(2ε-1) P^ε (Φ₀(X, Y) - (2 - 3ε) Y^(-3ε))`. -/
noncomputable def i12Tdd (θ H P X Y : ℝ) : ℝ :=
  ((X + Y) ^ 2 * (i12Lam θ H P - 3 * Real.log (X + Y)) ^ 2 -
      X ^ 2 * (i12Lam θ H P - 3 * Real.log X) ^ 2 -
      Y ^ 2 * (i12Lam θ H P - 3 * Real.log Y) ^ 2) / (X * Y) / (θ * H) -
    (2 * (i12Lam θ H P - 3 * Real.log Y) ^ 2 - 6 * (i12Lam θ H P - 3 * Real.log Y)) / (θ * H)

/-- The generic face integrand as a combination of functions with constant logarithmic
derivative. -/
theorem i12_T_integrand_eq (θ H P X Y : ℝ) (ε : ℂ) :
    (θ : ℂ) ^ (2 * ε - 1) * (H : ℂ) ^ (2 * ε - 1) * (P : ℂ) ^ ε *
        (i12Phi0 ε X Y - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε)) =
      (((θ : ℂ) ^ (2 * ε + -1) * (H : ℂ) ^ (2 * ε + -1) * (P : ℂ) ^ (1 * ε + 0)) *
          ((X + Y : ℝ) : ℂ) ^ (-3 * ε + 2) -
        ((θ : ℂ) ^ (2 * ε + -1) * (H : ℂ) ^ (2 * ε + -1) * (P : ℂ) ^ (1 * ε + 0)) *
          (X : ℂ) ^ (-3 * ε + 2) -
        ((θ : ℂ) ^ (2 * ε + -1) * (H : ℂ) ^ (2 * ε + -1) * (P : ℂ) ^ (1 * ε + 0)) *
          (Y : ℂ) ^ (-3 * ε + 2)) / ((X * Y : ℝ) : ℂ) -
        (2 + -3 * ε) * (((θ : ℂ) ^ (2 * ε + -1) * (H : ℂ) ^ (2 * ε + -1) *
          (P : ℂ) ^ (1 * ε + 0)) * (Y : ℂ) ^ (-3 * ε + 0)) := by
  simp only [i12Phi0, one_mul, add_zero, ← sub_eq_add_neg, neg_mul]
  rw [show -(3 * ε) + 2 = 2 - 3 * ε by ring, show (2 : ℂ) - 3 * ε = 2 - 3 * ε from rfl]
  ring

section Generic

variable {θ H P X Y : ℝ} (hθ : 0 < θ) (hH : 0 < H) (hP : 0 < P) (hX : 0 < X) (hY : 0 < Y)
include hθ hH hP

/-- The prefactor `q(ε) = θ^(2ε-1) H^(2ε-1) P^ε` has logarithmic derivative `λ`. -/
theorem i12_logDeriv_pref :
    ∀ ε, HasDerivAt (fun ε : ℂ => (θ : ℂ) ^ (2 * ε + -1) * (H : ℂ) ^ (2 * ε + -1) *
      (P : ℂ) ^ (1 * ε + 0)) ((i12Lam θ H P : ℝ) * ((θ : ℂ) ^ (2 * ε + -1) *
        (H : ℂ) ^ (2 * ε + -1) * (P : ℂ) ^ (1 * ε + 0))) ε := by
  intro ε
  have h := i12_logDeriv_mul (i12_logDeriv_mul (i12_logDeriv_cpow hθ (i12_hasDerivAt_affine 2 (-1)))
    (i12_logDeriv_cpow hH (i12_hasDerivAt_affine 2 (-1))))
    (i12_logDeriv_cpow hP (i12_hasDerivAt_affine 1 0)) ε
  refine h.congr_deriv ?_
  simp only [i12Lam]
  push_cast
  ring

include hX hY

/-- **The pointwise second derivative of the generic face integrand.** -/
theorem deriv_deriv_i12T_integrand :
    deriv (fun w => deriv (fun ε => (θ : ℂ) ^ (2 * ε - 1) * (H : ℂ) ^ (2 * ε - 1) *
        (P : ℂ) ^ ε * (i12Phi0 ε X Y - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε))) w) 0 =
      ((i12Tdd θ H P X Y : ℝ) : ℂ) := by
  have hq := i12_logDeriv_pref hθ hH hP
  have hS : 0 < X + Y := add_pos hX hY
  have hfS := i12_logDeriv_mul hq (i12_logDeriv_cpow hS (i12_hasDerivAt_affine (-3) 2))
  have hfX := i12_logDeriv_mul hq (i12_logDeriv_cpow hX (i12_hasDerivAt_affine (-3) 2))
  have hfY := i12_logDeriv_mul hq (i12_logDeriv_cpow hY (i12_hasDerivAt_affine (-3) 2))
  have hf0 := i12_logDeriv_mul hq (i12_logDeriv_cpow hY (i12_hasDerivAt_affine (-3) 0))
  have hp := i12_hasDerivAt_poly_mul hf0 2 (-3)
  have hd1 := fun ε =>
    ((((hfS ε).sub (hfX ε)).sub (hfY ε)).div_const ((X * Y : ℝ) : ℂ)).sub (hp ε)
  have hd1' : ∀ ε, HasDerivAt (fun ε => (θ : ℂ) ^ (2 * ε - 1) * (H : ℂ) ^ (2 * ε - 1) *
      (P : ℂ) ^ ε * (i12Phi0 ε X Y - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε))) _ ε := fun ε =>
    (hd1 ε).congr_of_eventuallyEq (Eventually.of_forall fun w => by
      exact i12_T_integrand_eq θ H P X Y w)
  rw [show (fun w => deriv (fun ε => (θ : ℂ) ^ (2 * ε - 1) * (H : ℂ) ^ (2 * ε - 1) *
      (P : ℂ) ^ ε * (i12Phi0 ε X Y - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε))) w) = _ from
    funext fun w => (hd1' w).deriv]
  have hS2 := i12_hasDerivAt_poly_mul_deriv hfS 1 0
  have hX2 := i12_hasDerivAt_poly_mul_deriv hfX 1 0
  have hY2 := i12_hasDerivAt_poly_mul_deriv hfY 1 0
  have h02 := i12_hasDerivAt_poly_mul_deriv hf0 2 (-3)
  have h2 := (((hS2.sub hX2).sub hY2).div_const ((X * Y : ℝ) : ℂ)).sub h02
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).deriv.trans ?_
  · simp only [Pi.sub_apply]
    ring
  have hθc : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ.ne'
  have hHc : (H : ℂ) ≠ 0 := ofReal_ne_zero.mpr hH.ne'
  have hXc : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hYc : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
  simp only [i12Tdd, mul_zero, zero_add, add_zero, cpow_zero, cpow_neg_one, mul_one,
    show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  push_cast
  field_simp
  ring

end Generic

/-! ### The faces `ρ = 0` of the two sectors -/

theorem i12TA_integrand_eq (θ u : ℝ) (ε : ℂ) :
    (θ : ℂ) ^ (2 * ε - 1) * (i12GA ε 0 θ u - i12GA0 ε 0 u) =
      (θ : ℂ) ^ (2 * ε - 1) * ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        (i12Phi0 ε (u * θ) ((1 - u) * i12H 0) -
          (2 - 3 * ε) * (((1 - u) * i12H 0 : ℝ) : ℂ) ^ (-3 * ε)) := by
  simp only [i12GA, i12GA0, zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]
  ring

theorem i12TB_integrand_eq (θ u : ℝ) (ε : ℂ) :
    (θ : ℂ) ^ (2 * ε - 1) * (i12GB ε 0 θ u - i12GB0 ε 0 u) =
      (θ : ℂ) ^ (2 * ε - 1) * ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        (i12Phi0 ε ((1 - u) * θ * i12H 0) u - (2 - 3 * ε) * (u : ℂ) ^ (-3 * ε)) := by
  simp only [i12GB, i12GB0, zero_mul, sub_zero, ofReal_one, one_cpow, mul_one, i12Phi0_comm ε u]
  ring

/-- The pointwise second derivative of the integrand of `T_A`. -/
theorem deriv_deriv_i12TA_integrand {θ u : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv (fun w => deriv (fun ε => (θ : ℂ) ^ (2 * ε - 1) *
        (i12GA ε 0 θ u - i12GA0 ε 0 u)) w) 0 =
      ((i12Tdd θ (i12H 0) (u * (1 - u)) (u * θ) ((1 - u) * i12H 0) : ℝ) : ℂ) := by
  simp_rw [i12TA_integrand_eq θ u]
  exact deriv_deriv_i12T_integrand hθ.1 (i12H_pos (by norm_num))
    (mul_pos hu.1 (sub_pos.mpr hu.2)) (mul_pos hu.1 hθ.1)
    (mul_pos (sub_pos.mpr hu.2) (i12H_pos (by norm_num)))

/-- The pointwise second derivative of the integrand of `T_B`. -/
theorem deriv_deriv_i12TB_integrand {θ u : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv (fun w => deriv (fun ε => (θ : ℂ) ^ (2 * ε - 1) *
        (i12GB ε 0 θ u - i12GB0 ε 0 u)) w) 0 =
      ((i12Tdd θ (i12H 0) (u * (1 - u)) ((1 - u) * θ * i12H 0) u : ℝ) : ℂ) := by
  simp_rw [i12TB_integrand_eq θ u]
  exact deriv_deriv_i12T_integrand hθ.1 (i12H_pos (by norm_num))
    (mul_pos hu.1 (sub_pos.mpr hu.2))
    (mul_pos (mul_pos (sub_pos.mpr hu.2) hθ.1) (i12H_pos (by norm_num))) hu.1

/-- **`T_A''(0)` under the integral sign.** -/
theorem deriv_deriv_i12TA_zero :
    Integrable (fun z : ℝ × ℝ =>
        ((i12Tdd z.1 (i12H 0) (z.2 * (1 - z.2)) (z.2 * z.1) ((1 - z.2) * i12H 0) : ℝ) : ℂ))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) ∧
      deriv (deriv i12TA) 0 = ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        ((i12Tdd z.1 (i12H 0) (z.2 * (1 - z.2)) (z.2 * z.1) ((1 - z.2) * i12H 0) : ℝ) : ℂ) := by
  have h0 : ‖(0 : ℂ)‖ < 1 / 200 := by norm_num
  obtain ⟨hi, hd⟩ := i12_hasDerivAt_deriv_integral (z₁ := 0)
    (F := fun ε (z : ℝ × ℝ) => (z.1 : ℂ) ^ (2 * ε - 1) * (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2))
    (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 6912 * i12Maj2 z) (integrable_i12Maj2.const_mul 6912)
    (fun ε _ => (by unfold i12GA i12GA0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ => (z.1 : ℂ) ^ (2 * ε - 1) *
        (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem i12_measurableSet2 fun z hz ε hε =>
      norm_i12TA_integrand_le (i12_ball_small h0 ε hε) hz)
    (by
      refine ae_restrict_of_forall_mem i12_measurableSet2 fun z hz => ?_
      obtain ⟨hθ, hu⟩ := hz
      have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
      have hθ0 := hθ.1
      have hd : Differentiable ℂ fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) := by
        fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
      exact (hd.mul ((differentiable_i12GA h0' hθ hu).sub
        (differentiable_i12GA0 h0' hu))).differentiableOn)
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      deriv (fun w => deriv (fun ε => (z.1 : ℂ) ^ (2 * ε - 1) *
        (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2)) w) 0 =
      ((i12Tdd z.1 (i12H 0) (z.2 * (1 - z.2)) (z.2 * z.1) ((1 - z.2) * i12H 0) : ℝ) : ℂ) :=
    fun z hz => deriv_deriv_i12TA_integrand hz.1 hz.2
  refine ⟨hi.congr (ae_restrict_of_forall_mem i12_measurableSet2 hpt), ?_⟩
  rw [← setIntegral_congr_fun i12_measurableSet2 hpt]
  exact hd.deriv

/-- **`T_B''(0)` under the integral sign.** -/
theorem deriv_deriv_i12TB_zero :
    Integrable (fun z : ℝ × ℝ =>
        ((i12Tdd z.1 (i12H 0) (z.2 * (1 - z.2)) ((1 - z.2) * z.1 * i12H 0) z.2 : ℝ) : ℂ))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) ∧
      deriv (deriv i12TB) 0 = ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        ((i12Tdd z.1 (i12H 0) (z.2 * (1 - z.2)) ((1 - z.2) * z.1 * i12H 0) z.2 : ℝ) : ℂ) := by
  have h0 : ‖(0 : ℂ)‖ < 1 / 200 := by norm_num
  obtain ⟨hi, hd⟩ := i12_hasDerivAt_deriv_integral (z₁ := 0)
    (F := fun ε (z : ℝ × ℝ) => (z.1 : ℂ) ^ (2 * ε - 1) * (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2))
    (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 1728 * i12Maj2 z) (integrable_i12Maj2.const_mul 1728)
    (fun ε _ => (by unfold i12GB i12GB0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ => (z.1 : ℂ) ^ (2 * ε - 1) *
        (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem i12_measurableSet2 fun z hz ε hε =>
      norm_i12TB_integrand_le (i12_ball_small h0 ε hε) hz)
    (by
      refine ae_restrict_of_forall_mem i12_measurableSet2 fun z hz => ?_
      obtain ⟨hθ, hu⟩ := hz
      have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
      have hθ0 := hθ.1
      have hd : Differentiable ℂ fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) := by
        fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
      exact (hd.mul ((differentiable_i12GB h0' hθ hu).sub
        (differentiable_i12GB0 h0' hu))).differentiableOn)
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      deriv (fun w => deriv (fun ε => (z.1 : ℂ) ^ (2 * ε - 1) *
        (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2)) w) 0 =
      ((i12Tdd z.1 (i12H 0) (z.2 * (1 - z.2)) ((1 - z.2) * z.1 * i12H 0) z.2 : ℝ) : ℂ) :=
    fun z hz => deriv_deriv_i12TB_integrand hz.1 hz.2
  refine ⟨hi.congr (ae_restrict_of_forall_mem i12_measurableSet2 hpt), ?_⟩
  rw [← setIntegral_congr_fun i12_measurableSet2 hpt]
  exact hd.deriv

end QED.ThreeLoopD
