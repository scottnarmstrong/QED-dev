/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RFirst
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville

/-!
# Set (d), master `I₁₂`: second derivatives under the integral sign

For the second Taylor coefficient of `QED.ThreeLoopD.i12Rest = ε S + T_A + T_B`
(`S = R₁ + R_A + R_B`),

  `i12Rest''(0) / 2 = S'(0) + (T_A''(0) + T_B''(0)) / 2`.

This file supplies the analytic plumbing: a parametric integral whose integrand is holomorphic
and dominated by an integrable function on a ball has, at the centre, a second derivative equal
to the integral of the pointwise second derivatives
(`QED.ThreeLoopD.i12_hasDerivAt_deriv_integral`), and the reduction of
`iteratedDeriv 2 i12Rest 0` to the derivatives of the five remainders
(`QED.ThreeLoopD.iteratedDeriv_two_i12Rest_eq`).

## Main results

* `QED.ThreeLoopD.i12_deriv_integral_eventuallyEq`,
  `QED.ThreeLoopD.i12_hasDerivAt_deriv_integral`.
* `QED.ThreeLoopD.iteratedDeriv_two_i12Rest_eq`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℂ → α → ℂ} {z₁ : ℂ} {R : ℝ}
  {b : α → ℝ}

/-- Near the centre, the derivative of a holomorphic parametric integral is the integral of the
pointwise derivatives. -/
theorem i12_deriv_integral_eventuallyEq (hR : 0 < R) (hb : Integrable b μ)
    (hFm : ∀ w ∈ ball z₁ R, AEStronglyMeasurable (F w) μ)
    (hFb : ∀ᵐ t ∂μ, ∀ w ∈ ball z₁ R, ‖F w t‖ ≤ b t)
    (hFd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => F w t) (ball z₁ R)) :
    ∀ w ∈ ball z₁ (R / 2), Integrable (fun t => deriv (fun w => F w t) w) μ ∧
      HasDerivAt (fun w => ∫ t, F w t ∂μ) (∫ t, deriv (fun w' => F w' t) w ∂μ) w := by
  intro w hw
  have hsub : ball w (R / 2) ⊆ ball z₁ R := by
    intro u hu
    rw [mem_ball] at hu hw ⊢
    calc dist u z₁ ≤ dist u w + dist w z₁ := dist_triangle _ _ _
      _ < R := by linarith
  exact i12_hasDerivAt_integral_of_holomorphic (half_pos hR) hb
    (fun v hv => hFm v (hsub hv))
    (by filter_upwards [hFb] with t ht v hv using ht v (hsub hv))
    (by filter_upwards [hFd] with t ht using ht.mono hsub)

/-- **Second derivative of a holomorphic parametric integral** at the centre: the derivative of
`w ↦ (∫ F w)'` is the integral of the pointwise second derivatives, which are integrable. -/
theorem i12_hasDerivAt_deriv_integral (hR : 0 < R) (hb : Integrable b μ)
    (hFm : ∀ w ∈ ball z₁ R, AEStronglyMeasurable (F w) μ)
    (hFb : ∀ᵐ t ∂μ, ∀ w ∈ ball z₁ R, ‖F w t‖ ≤ b t)
    (hFd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => F w t) (ball z₁ R)) :
    Integrable (fun t => deriv (fun w => deriv (fun w' => F w' t) w) z₁) μ ∧
      HasDerivAt (deriv fun w => ∫ t, F w t ∂μ)
        (∫ t, deriv (fun w => deriv (fun w' => F w' t) w) z₁ ∂μ) z₁ := by
  have h1 := i12_deriv_integral_eventuallyEq hR hb hFm hFb hFd
  set r := R / 4 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  -- Cauchy bound for the first derivative on `ball z₁ (R / 2)`
  have hF1b : ∀ᵐ t ∂μ, ∀ w ∈ ball z₁ (R / 2), ‖deriv (fun w' => F w' t) w‖ ≤ b t / r := by
    filter_upwards [hFb, hFd] with t hb' hd' w hw
    have hsub : closedBall w r ⊆ ball z₁ R := by
      intro u hu
      rw [mem_ball] at hw ⊢
      rw [mem_closedBall] at hu
      calc dist u z₁ ≤ dist u w + dist w z₁ := dist_triangle _ _ _
        _ < R := by rw [hr] at hu; linarith
    refine norm_deriv_le_of_forall_mem_sphere_norm_le hr0 (hd'.diffContOnCl_ball hsub) ?_
    intro u hu
    exact hb' u (hsub (sphere_subset_closedBall hu))
  have hF1d : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => deriv (fun w' => F w' t) w)
      (ball z₁ (R / 2)) := by
    filter_upwards [hFd] with t ht
    exact (ht.deriv isOpen_ball).mono (ball_subset_ball (by linarith))
  have h2 := i12_hasDerivAt_integral_of_holomorphic (F := fun w t => deriv (fun w' => F w' t) w)
    (half_pos hR) (hb.div_const r) (fun w hw => (h1 w hw).1.aestronglyMeasurable) hF1b hF1d
  refine ⟨h2.1, h2.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (half_pos hR))] with w hw
  exact (h1 w hw).2.deriv

/-- **The second Taylor coefficient of the remainder in terms of the five remainders**:
`i12Rest''(0) / 2 = S'(0) + (T_A''(0) + T_B''(0)) / 2`. -/
theorem iteratedDeriv_two_i12Rest_eq :
    iteratedDeriv 2 i12Rest 0 / (2 : ℕ).factorial =
      deriv i12R1 0 + deriv i12RA3 0 + deriv i12RB3 0 +
        (deriv (deriv i12TA) 0 + deriv (deriv i12TB) 0) / 2 := by
  have hball : ∀ {f : ℂ → ℂ}, (∀ ε₀ : ℂ, ‖ε₀‖ < 1 / 200 → DifferentiableAt ℂ f ε₀) →
      DifferentiableOn ℂ f (ball 0 (1 / 200)) := fun hf ε hε =>
    (hf ε (by simpa using hε)).differentiableWithinAt
  have hdd : ∀ {f : ℂ → ℂ}, (∀ ε₀ : ℂ, ‖ε₀‖ < 1 / 200 → DifferentiableAt ℂ f ε₀) →
      DifferentiableAt ℂ (deriv f) 0 := fun hf =>
    ((hball hf).deriv isOpen_ball).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))
  have hS : ∀ ε₀ : ℂ, ‖ε₀‖ < 1 / 200 →
      DifferentiableAt ℂ (fun ε => i12R1 ε + i12RA3 ε + i12RB3 ε) ε₀ := fun ε₀ h =>
    ((differentiableAt_i12R1 h).add (differentiableAt_i12RA3 h)).add (differentiableAt_i12RB3 h)
  have heq : deriv i12Rest =ᶠ[𝓝 0] fun ε => (i12R1 ε + i12RA3 ε + i12RB3 ε) +
      ε * deriv (fun ε => i12R1 ε + i12RA3 ε + i12RB3 ε) ε + deriv i12TA ε +
        deriv i12TB ε := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 200))]
      with ε hε
    have h : ‖ε‖ < 1 / 200 := by simpa using hε
    have hd := (((hasDerivAt_id' ε).mul (hS ε h).hasDerivAt).add
      (differentiableAt_i12TA h).hasDerivAt).add (differentiableAt_i12TB h).hasDerivAt
    have hd' : HasDerivAt i12Rest _ ε := hd
    rw [hd'.deriv]
    ring
  have hd := (((hS 0 (by norm_num)).hasDerivAt.add ((hasDerivAt_id' (0 : ℂ)).mul
    (hdd hS).hasDerivAt)).add (hdd fun _ h => differentiableAt_i12TA h).hasDerivAt).add
    (hdd fun _ h => differentiableAt_i12TB h).hasDerivAt
  have hd' : HasDerivAt (fun ε => (i12R1 ε + i12RA3 ε + i12RB3 ε) +
      ε * deriv (fun ε => i12R1 ε + i12RA3 ε + i12RB3 ε) ε + deriv i12TA ε +
        deriv i12TB ε) _ 0 := hd
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq, hd'.deriv]
  have h0 : ‖(0 : ℂ)‖ < 1 / 200 := by norm_num
  have hsum : deriv (fun ε => i12R1 ε + i12RA3 ε + i12RB3 ε) 0 =
      deriv i12R1 0 + deriv i12RA3 0 + deriv i12RB3 0 := by
    exact ((((differentiableAt_i12R1 h0).hasDerivAt.add
      (differentiableAt_i12RA3 h0).hasDerivAt).add (differentiableAt_i12RB3 h0).hasDerivAt)).deriv
  simp only [one_mul, zero_mul, add_zero, hsum]
  ring

end QED.ThreeLoopD
