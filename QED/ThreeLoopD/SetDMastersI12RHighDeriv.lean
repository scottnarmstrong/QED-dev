/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville

/-!
# Set (d), master `I₁₂`: Taylor coefficients of the remainder of every order

For every `n`, the `(n + 1)`-st derivative at `0` of
`QED.ThreeLoopD.i12Rest = ε S + T_A + T_B` (`S = R₁ + R_A + R_B`) is

  `i12Rest⁽ⁿ⁺¹⁾(0) = (n + 1) S⁽ⁿ⁾(0) + T_A⁽ⁿ⁺¹⁾(0) + T_B⁽ⁿ⁺¹⁾(0)`

(Leibniz's rule, `QED.ThreeLoopD.iteratedDeriv_succ_i12Rest`), and each derivative of each of
the five remainders is the integral of the pointwise `ε`-derivatives of its integrand at `ε = 0`.
The analytic input is one statement for all orders: a parametric integral whose integrand is
holomorphic and dominated by an integrable function on a ball has, near the centre, every
iterated derivative equal to the integral of the pointwise iterated derivatives
(`QED.ThreeLoopD.i12_iteratedDeriv_integral`; the radius halves at each order, by Cauchy's
estimate). The domination of the five integrands is the one already used for analyticity
(`QED.ThreeLoopD.SetDMastersI12RestAnalytic`).

So `r_{n+1} = i12Rest⁽ⁿ⁺¹⁾(0) / (n + 1)!` is a sum of five explicit integrals
(`QED.ThreeLoopD.iteratedDeriv_succ_i12Rest_eq_integrals`). Numerically (contour extraction on
the tanh-sinh grids of `setDI12/decomp_fast.py`) the Taylor coefficients `[εᵏ]` are

| `k` | `R₁` | `R_A` | `R_B` | `T_A` | `T_B` |
|---|---|---|---|---|---|
| 2 | -47.05453097 | 83.75570463 | 22.17220830 | 59.02060741 | 25.75524464 |
| 3 | 117.3944677 | -197.4559144 | -102.2653173 | -130.7926844 | -64.95934350 |
| 4 | | | | 157.9967245 | 90.78851534 |

and `[ε²]S + [ε³](T_A + T_B)`, `[ε³]S + [ε⁴](T_A + T_B)` reproduce `r₃`, `r₄` to `1e-8`.

## Main results

* `QED.ThreeLoopD.i12_iteratedDeriv_integral`.
* `QED.ThreeLoopD.iteratedDeriv_succ_i12Rest`.
* `QED.ThreeLoopD.iteratedDeriv_i12R1_eq`, `QED.ThreeLoopD.iteratedDeriv_i12RA3_eq`,
  `QED.ThreeLoopD.iteratedDeriv_i12RB3_eq`, `QED.ThreeLoopD.iteratedDeriv_i12TA_eq`,
  `QED.ThreeLoopD.iteratedDeriv_i12TB_eq`.
* `QED.ThreeLoopD.iteratedDeriv_succ_i12Rest_eq_integrals`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

section Generic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {z₁ : ℂ}

/-- **Iterated derivatives of a holomorphic parametric integral.** If `F w` is dominated by an
integrable `b` and holomorphic in `w` on `ball z₁ R`, then for every `n` the pointwise `n`-th
derivatives at `z₁` are integrable and, on `ball z₁ (R / 2 ^ n)`, the `n`-th derivative of the
integral is the integral of the pointwise `n`-th derivatives. -/
theorem i12_iteratedDeriv_integral (n : ℕ) :
    ∀ {R : ℝ} {b : α → ℝ} {F : ℂ → α → ℂ}, 0 < R → Integrable b μ →
      (∀ w ∈ ball z₁ R, AEStronglyMeasurable (F w) μ) →
      (∀ᵐ t ∂μ, ∀ w ∈ ball z₁ R, ‖F w t‖ ≤ b t) →
      (∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => F w t) (ball z₁ R)) →
      Integrable (fun t => iteratedDeriv n (fun w => F w t) z₁) μ ∧
        ∀ w ∈ ball z₁ (R / 2 ^ n), iteratedDeriv n (fun w => ∫ t, F w t ∂μ) w =
          ∫ t, iteratedDeriv n (fun w' => F w' t) w ∂μ := by
  induction n with
  | zero =>
    intro R b F hR hb hFm hFb _
    refine ⟨?_, fun w _ => by simp only [iteratedDeriv_zero]⟩
    simp only [iteratedDeriv_zero]
    refine hb.mono' (hFm z₁ (mem_ball_self hR)) ?_
    filter_upwards [hFb] with t ht using ht z₁ (mem_ball_self hR)
  | succ n ih =>
    intro R b F hR hb hFm hFb hFd
    have h1 := i12_deriv_integral_eventuallyEq hR hb hFm hFb hFd
    set r := R / 4 with hr
    have hr0 : 0 < r := by rw [hr]; linarith
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
    obtain ⟨hI, hE⟩ := ih (R := R / 2) (b := fun t => b t / r)
      (F := fun w t => deriv (fun w' => F w' t) w) (half_pos hR) (hb.div_const r)
      (fun w hw => (h1 w hw).1.aestronglyMeasurable) hF1b hF1d
    refine ⟨by simpa only [iteratedDeriv_succ'] using hI, fun w hw => ?_⟩
    have hw' : w ∈ ball z₁ (R / 2 / 2 ^ n) := by rwa [div_div, ← pow_succ']
    have hw2 : w ∈ ball z₁ (R / 2) :=
      ball_subset_ball (div_le_self (half_pos hR).le (one_le_pow₀ (by norm_num))) hw'
    have heq : deriv (fun w => ∫ t, F w t ∂μ) =ᶠ[𝓝 w]
        fun w => ∫ t, deriv (fun w' => F w' t) w ∂μ := by
      filter_upwards [isOpen_ball.mem_nhds hw2] with v hv using (h1 v hv).2.deriv
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq, hE w hw']
    simp only [iteratedDeriv_succ']

/-- The case `w = z₁` of `QED.ThreeLoopD.i12_iteratedDeriv_integral`. -/
theorem i12_iteratedDeriv_integral_center (n : ℕ) {R : ℝ} {b : α → ℝ} {F : ℂ → α → ℂ}
    (hR : 0 < R) (hb : Integrable b μ) (hFm : ∀ w ∈ ball z₁ R, AEStronglyMeasurable (F w) μ)
    (hFb : ∀ᵐ t ∂μ, ∀ w ∈ ball z₁ R, ‖F w t‖ ≤ b t)
    (hFd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => F w t) (ball z₁ R)) :
    Integrable (fun t => iteratedDeriv n (fun w => F w t) z₁) μ ∧
      iteratedDeriv n (fun w => ∫ t, F w t ∂μ) z₁ =
        ∫ t, iteratedDeriv n (fun w' => F w' t) z₁ ∂μ := by
  obtain ⟨hI, hE⟩ := i12_iteratedDeriv_integral n hR hb hFm hFb hFd
  exact ⟨hI, hE z₁ (mem_ball_self (by positivity))⟩

end Generic

/-! ### Leibniz's rule for `ε S + T_A + T_B` -/

theorem i12_contDiffAt_zero {f : ℂ → ℂ}
    (hf : ∀ ε₀ : ℂ, ‖ε₀‖ < 1 / 200 → DifferentiableAt ℂ f ε₀) (m : ℕ) :
    ContDiffAt ℂ m f 0 :=
  (DifferentiableOn.analyticAt (fun ε hε => (hf ε (by simpa using hε)).differentiableWithinAt)
    (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 200)))).contDiffAt

/-- **The Taylor coefficients of the remainder in terms of the five remainders**, all orders:
`i12Rest⁽ⁿ⁺¹⁾(0) = (n + 1) (R₁⁽ⁿ⁾(0) + R_A⁽ⁿ⁾(0) + R_B⁽ⁿ⁾(0)) + T_A⁽ⁿ⁺¹⁾(0) + T_B⁽ⁿ⁺¹⁾(0)`. -/
theorem iteratedDeriv_succ_i12Rest (n : ℕ) :
    iteratedDeriv (n + 1) i12Rest 0 =
      (n + 1) * (iteratedDeriv n i12R1 0 + iteratedDeriv n i12RA3 0 +
        iteratedDeriv n i12RB3 0) + iteratedDeriv (n + 1) i12TA 0 +
          iteratedDeriv (n + 1) i12TB 0 := by
  have hS : ∀ ε₀ : ℂ, ‖ε₀‖ < 1 / 200 →
      DifferentiableAt ℂ (fun ε => i12R1 ε + i12RA3 ε + i12RB3 ε) ε₀ := fun ε₀ h =>
    ((differentiableAt_i12R1 h).add (differentiableAt_i12RA3 h)).add (differentiableAt_i12RB3 h)
  have hR : ∀ ε₀ : ℂ, ‖ε₀‖ < 1 / 200 →
      DifferentiableAt ℂ (fun ε => ε * (i12R1 ε + i12RA3 ε + i12RB3 ε)) ε₀ := fun ε₀ h =>
    differentiableAt_id.mul (hS ε₀ h)
  have hrest : i12Rest = fun ε => ε * (i12R1 ε + i12RA3 ε + i12RB3 ε) + i12TA ε + i12TB ε :=
    rfl
  rw [hrest, iteratedDeriv_fun_add ((i12_contDiffAt_zero hR _).add
      (i12_contDiffAt_zero (fun _ h => differentiableAt_i12TA h) _))
      (i12_contDiffAt_zero (fun _ h => differentiableAt_i12TB h) _),
    iteratedDeriv_fun_add (i12_contDiffAt_zero hR _)
      (i12_contDiffAt_zero (fun _ h => differentiableAt_i12TA h) _),
    iteratedDeriv_fun_mul (f := fun ε => ε) contDiffAt_id (i12_contDiffAt_zero hS _)]
  rw [Finset.sum_eq_single 1 (fun i _ hi => by simp [iteratedDeriv_fun_id_zero, hi])
    (fun h => by simp at h)]
  simp only [iteratedDeriv_fun_id_zero, Nat.choose_one_right, ite_true, mul_one,
    Nat.add_sub_cancel]
  rw [iteratedDeriv_fun_add ((i12_contDiffAt_zero (fun _ h => differentiableAt_i12R1 h) _).add
      (i12_contDiffAt_zero (fun _ h => differentiableAt_i12RA3 h) _))
      (i12_contDiffAt_zero (fun _ h => differentiableAt_i12RB3 h) _),
    iteratedDeriv_fun_add (i12_contDiffAt_zero (fun _ h => differentiableAt_i12R1 h) _)
      (i12_contDiffAt_zero (fun _ h => differentiableAt_i12RA3 h) _)]
  push_cast
  ring

/-! ### The five integrands and their iterated derivatives -/

/-- The integrand of `QED.ThreeLoopD.i12R1`, over `(y, t, u) ∈ (0, 1)³`. -/
noncomputable def i12R1Ig (ε : ℂ) (z : ℝ × ℝ × ℝ) : ℂ :=
  i12Wt ε (z.1 * (1 - z.1)) z.2.1 z.2.2 *
    i12Phi1 ε (z.2.2 * z.2.1) ((1 - z.2.2) * (z.1 * (1 - z.1)))

/-- The integrand of `QED.ThreeLoopD.i12RA3`, over `(ρ, θ, u) ∈ (0, 1)³`. -/
noncomputable def i12RA3Ig (ε : ℂ) (z : ℝ × ℝ × ℝ) : ℂ :=
  i12SecWt ε z.1 z.2.1 * (i12GA ε z.1 z.2.1 z.2.2 - i12GA ε 0 z.2.1 z.2.2 -
    i12GA0 ε z.1 z.2.2 + i12GA0 ε 0 z.2.2)

/-- The integrand of `QED.ThreeLoopD.i12RB3`, over `(ρ, θ, u) ∈ (0, 1)³`. -/
noncomputable def i12RB3Ig (ε : ℂ) (z : ℝ × ℝ × ℝ) : ℂ :=
  i12SecWt ε z.1 z.2.1 * (i12GB ε z.1 z.2.1 z.2.2 - i12GB ε 0 z.2.1 z.2.2 -
    i12GB0 ε z.1 z.2.2 + i12GB0 ε 0 z.2.2)

/-- The integrand of `QED.ThreeLoopD.i12TA`, over `(θ, u) ∈ (0, 1)²`. -/
noncomputable def i12TAIg (ε : ℂ) (z : ℝ × ℝ) : ℂ :=
  (z.1 : ℂ) ^ (2 * ε - 1) * (i12GA ε 0 z.1 z.2 - i12GA0 ε 0 z.2)

/-- The integrand of `QED.ThreeLoopD.i12TB`, over `(θ, u) ∈ (0, 1)²`. -/
noncomputable def i12TBIg (ε : ℂ) (z : ℝ × ℝ) : ℂ :=
  (z.1 : ℂ) ^ (2 * ε - 1) * (i12GB ε 0 z.1 z.2 - i12GB0 ε 0 z.2)

/-- The open unit cube `(0, 1)³`. -/
abbrev i12Cube : Set (ℝ × ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)

/-- The open unit square `(0, 1)²`. -/
abbrev i12Sq : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1

theorem i12_norm_zero_lt : ‖(0 : ℂ)‖ < 1 / 200 := by norm_num

theorem iteratedDeriv_i12R1_eq (n : ℕ) :
    Integrable (fun z => iteratedDeriv n (fun ε => i12R1Ig ε z) 0)
        (volume.restrict i12Cube) ∧
      iteratedDeriv n i12R1 0 = ∫ z in i12Cube, iteratedDeriv n (fun ε => i12R1Ig ε z) 0 := by
  refine i12_iteratedDeriv_integral_center (F := i12R1Ig) n (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 27 * i12Maj3 z) (integrable_i12Maj3.const_mul 27)
    (fun ε _ => (by unfold i12R1Ig i12Wt i12Phi1; fun_prop :
      Measurable fun z : ℝ × ℝ × ℝ => i12R1Ig ε z).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet3 fun z hz ε hε =>
      norm_i12R1_integrand_le (i12_ball_small i12_norm_zero_lt ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet3 fun z hz => ?_
    obtain ⟨hy, ht, hu⟩ := hz
    have hc : 0 < z.1 * (1 - z.1) := mul_pos hy.1 (sub_pos.mpr hy.2)
    exact ((differentiable_i12Wt hc ht hu).mul (differentiable_i12Phi1 (mul_pos hu.1 ht.1)
      (mul_pos (sub_pos.mpr hu.2) hc) (by nlinarith [hu.1, hu.2, ht.1, ht.2]))).differentiableOn

theorem iteratedDeriv_i12RA3_eq (n : ℕ) :
    Integrable (fun z => iteratedDeriv n (fun ε => i12RA3Ig ε z) 0)
        (volume.restrict i12Cube) ∧
      iteratedDeriv n i12RA3 0 = ∫ z in i12Cube, iteratedDeriv n (fun ε => i12RA3Ig ε z) 0 := by
  refine i12_iteratedDeriv_integral_center (F := i12RA3Ig) n (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 20000 * i12Maj3 z) (integrable_i12Maj3.const_mul 20000)
    (fun ε _ => (by unfold i12RA3Ig i12SecWt i12GA i12GA0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ × ℝ => i12RA3Ig ε z).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet3 fun z hz ε hε =>
      norm_i12RA3_integrand_le (i12_ball_small i12_norm_zero_lt ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet3 fun z hz => ?_
    obtain ⟨hρ, hθ, hu⟩ := hz
    have hρ' : z.1 ∈ Ico (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2⟩
    have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
    exact ((differentiable_i12SecWt hρ.1 hθ.1).mul
      ((((differentiable_i12GA hρ' hθ hu).sub (differentiable_i12GA h0' hθ hu)).sub
        (differentiable_i12GA0 hρ' hu)).add (differentiable_i12GA0 h0' hu))).differentiableOn

theorem iteratedDeriv_i12RB3_eq (n : ℕ) :
    Integrable (fun z => iteratedDeriv n (fun ε => i12RB3Ig ε z) 0)
        (volume.restrict i12Cube) ∧
      iteratedDeriv n i12RB3 0 = ∫ z in i12Cube, iteratedDeriv n (fun ε => i12RB3Ig ε z) 0 := by
  refine i12_iteratedDeriv_integral_center (F := i12RB3Ig) n (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 20000 * i12Maj3 z) (integrable_i12Maj3.const_mul 20000)
    (fun ε _ => (by unfold i12RB3Ig i12SecWt i12GB i12GB0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ × ℝ => i12RB3Ig ε z).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet3 fun z hz ε hε =>
      norm_i12RB3_integrand_le (i12_ball_small i12_norm_zero_lt ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet3 fun z hz => ?_
    obtain ⟨hρ, hθ, hu⟩ := hz
    have hρ' : z.1 ∈ Ico (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2⟩
    have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
    exact ((differentiable_i12SecWt hρ.1 hθ.1).mul
      ((((differentiable_i12GB hρ' hθ hu).sub (differentiable_i12GB h0' hθ hu)).sub
        (differentiable_i12GB0 hρ' hu)).add (differentiable_i12GB0 h0' hu))).differentiableOn

theorem iteratedDeriv_i12TA_eq (n : ℕ) :
    Integrable (fun z => iteratedDeriv n (fun ε => i12TAIg ε z) 0) (volume.restrict i12Sq) ∧
      iteratedDeriv n i12TA 0 = ∫ z in i12Sq, iteratedDeriv n (fun ε => i12TAIg ε z) 0 := by
  refine i12_iteratedDeriv_integral_center (F := i12TAIg) n (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 6912 * i12Maj2 z) (integrable_i12Maj2.const_mul 6912)
    (fun ε _ => (by unfold i12TAIg i12GA i12GA0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ => i12TAIg ε z).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet2 fun z hz ε hε =>
      norm_i12TA_integrand_le (i12_ball_small i12_norm_zero_lt ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet2 fun z hz => ?_
    obtain ⟨hθ, hu⟩ := hz
    have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
    have hθ0 := hθ.1
    have hd : Differentiable ℂ fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) := by
      fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
    exact (hd.mul ((differentiable_i12GA h0' hθ hu).sub
      (differentiable_i12GA0 h0' hu))).differentiableOn

theorem iteratedDeriv_i12TB_eq (n : ℕ) :
    Integrable (fun z => iteratedDeriv n (fun ε => i12TBIg ε z) 0) (volume.restrict i12Sq) ∧
      iteratedDeriv n i12TB 0 = ∫ z in i12Sq, iteratedDeriv n (fun ε => i12TBIg ε z) 0 := by
  refine i12_iteratedDeriv_integral_center (F := i12TBIg) n (by norm_num : (0 : ℝ) < 1 / 200)
    (b := fun z => 1728 * i12Maj2 z) (integrable_i12Maj2.const_mul 1728)
    (fun ε _ => (by unfold i12TBIg i12GB i12GB0 i12Phi0 i12H; fun_prop :
      Measurable fun z : ℝ × ℝ => i12TBIg ε z).aestronglyMeasurable) ?_ ?_
  · exact ae_restrict_of_forall_mem i12_measurableSet2 fun z hz ε hε =>
      norm_i12TB_integrand_le (i12_ball_small i12_norm_zero_lt ε hε) hz
  · refine ae_restrict_of_forall_mem i12_measurableSet2 fun z hz => ?_
    obtain ⟨hθ, hu⟩ := hz
    have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
    have hθ0 := hθ.1
    have hd : Differentiable ℂ fun ε : ℂ => (z.1 : ℂ) ^ (2 * ε - 1) := by
      fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
    exact (hd.mul ((differentiable_i12GB h0' hθ hu).sub
      (differentiable_i12GB0 h0' hu))).differentiableOn

/-- **The `(n + 1)`-st Taylor coefficient of the remainder as five integrals** of pointwise
`ε`-derivatives at `ε = 0`:
`i12Rest⁽ⁿ⁺¹⁾(0) = (n + 1) (∫ ∂ⁿR₁ + ∫ ∂ⁿR_A + ∫ ∂ⁿR_B) + ∫ ∂ⁿ⁺¹T_A + ∫ ∂ⁿ⁺¹T_B`. -/
theorem iteratedDeriv_succ_i12Rest_eq_integrals (n : ℕ) :
    iteratedDeriv (n + 1) i12Rest 0 =
      (n + 1) * ((∫ z in i12Cube, iteratedDeriv n (fun ε => i12R1Ig ε z) 0) +
        (∫ z in i12Cube, iteratedDeriv n (fun ε => i12RA3Ig ε z) 0) +
        ∫ z in i12Cube, iteratedDeriv n (fun ε => i12RB3Ig ε z) 0) +
      (∫ z in i12Sq, iteratedDeriv (n + 1) (fun ε => i12TAIg ε z) 0) +
      ∫ z in i12Sq, iteratedDeriv (n + 1) (fun ε => i12TBIg ε z) 0 := by
  rw [iteratedDeriv_succ_i12Rest, (iteratedDeriv_i12R1_eq n).2, (iteratedDeriv_i12RA3_eq n).2,
    (iteratedDeriv_i12RB3_eq n).2, (iteratedDeriv_i12TA_eq (n + 1)).2,
    (iteratedDeriv_i12TB_eq (n + 1)).2]

end QED.ThreeLoopD
