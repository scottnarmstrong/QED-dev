/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSGoodAn

/-!
# Set (d), master `I₁₂`: the good part of the bulk remainder near `ε = 0`

The closed form `QED.ThreeLoopD.i12HS_integral_good_of_norm` of `∫ Good` holds for `0 < re ε`.
Multiplied by `ε`, and with `ε Γ(2ε) Γ(ε) / Γ(3ε) = (3/2) Γ(1 + 2ε) Γ(1 + ε) / Γ(1 + 3ε)`, it is

  `ε ∫ Good = R(ε) = (3/2) a (1 - 3ε) / ((1 - ε)² (1 - 2ε)) Γ(1 + 2ε) Γ(1 + ε) / Γ(1 + 3ε)
    P(ε - 1, ε) - a B_w P(-ε - 1, ε) / 2 - a B_w P(2ε - 1, ε)`

(`QED.ThreeLoopD.i12HSGoodR`, `a = 2 - 3ε`), whose every factor is holomorphic on
`‖ε‖ < 1/100`: the Gamma factors have arguments of positive real part, and
`ε ↦ P(cε - 1, ε)` is a holomorphic parametric integral, dominated by `32 x ^ (-1/100)`
(`QED.ThreeLoopD.differentiableOn_i12HSP_lin`), with Taylor coefficients
`∫₀¹ ((log x + c log h(x)) ^ n / (x h(x)) - (log x + c log h(0)) ^ n / (x h(0))) dx`
(`QED.ThreeLoopD.iteratedDeriv_i12HSP_lin`). Both sides being holomorphic on the ball, the
identity theorem extends `ε ∫ Good = R(ε)` to all of `‖ε‖ < 1/100`
(`QED.ThreeLoopD.i12HS_mul_GoodI_eq`), and Leibniz's rule gives the order-`n` coefficients of the
good part from the Taylor coefficients of `R` (`QED.ThreeLoopD.iteratedDeriv_succ_i12HSGoodR`):

  `R⁽ⁿ⁺¹⁾(0) = (n + 1) ∫ Good_n`.

## Main results

* `QED.ThreeLoopD.differentiableOn_i12HSP_lin`, `QED.ThreeLoopD.iteratedDeriv_i12HSP_lin`.
* `QED.ThreeLoopD.differentiableOn_i12HSGoodR`.
* `QED.ThreeLoopD.i12HS_mul_GoodI_eq_of_re_pos`, `QED.ThreeLoopD.i12HS_mul_GoodI_eq`.
* `QED.ThreeLoopD.iteratedDeriv_succ_i12HSGoodR`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-- Domination of the integrand of `P(cε - 1, ε)`: `32 x ^ (-1/100)`. -/
theorem i12HS_norm_P_integrand_le {ε c : ℂ} (hε : ‖ε‖ < 1 / 100) (hc : ‖c‖ ≤ 2) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖(x : ℂ) ^ (ε - 1) *
        (((i12H x : ℝ) : ℂ) ^ (c * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (c * ε - 1))‖ ≤
      32 * x ^ (-(1 / 100) : ℝ) := by
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hx0 := hx.1
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hh := i12H_mem hxI
  have hle : i12H x ≤ i12H 0 := by unfold i12H; linarith [hx.1]
  have hce : ‖c * ε‖ ≤ 2 / 100 := by
    rw [norm_mul]; nlinarith [norm_nonneg c, norm_nonneg ε]
  have hcre' := abs_le.mp ((abs_re_le_norm _).trans hce)
  have hL := i12_norm_cpow_sub_le_lip (by norm_num : (0 : ℝ) < 1 / 4) hh.1 hle
    (v := c * ε - 1) (by simp only [sub_re, one_re]; linarith)
  have hv : ‖c * ε - 1‖ ≤ 2 := by
    calc ‖c * ε - 1‖ ≤ ‖c * ε‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have h64 : (1 / 4 : ℝ) ^ ((c * ε - 1).re - 1) ≤ 64 :=
    i12_rpow_le_64 le_rfl (by simp only [sub_re, one_re]; linarith)
      (by simp only [sub_re, one_re]; linarith)
  have hd : i12H 0 - i12H x = x / 4 := by unfold i12H; ring
  have hX : ‖(x : ℂ) ^ (ε - 1)‖ ≤ x ^ (-(101 / 100) : ℝ) :=
    norm_cpow_le_rpow_of_le hx.1 hx.2.le (by simp only [sub_re, one_re]; linarith)
  have hD : ‖((i12H x : ℝ) : ℂ) ^ (c * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (c * ε - 1)‖ ≤
      32 * x := by
    rw [norm_sub_rev]
    refine hL.trans ?_
    rw [hd]
    have : 0 ≤ (1 / 4 : ℝ) ^ ((c * ε - 1).re - 1) := by positivity
    calc ‖c * ε - 1‖ * (x / 4 * (1 / 4 : ℝ) ^ ((c * ε - 1).re - 1)) ≤ 2 * (x / 4 * 64) := by
          gcongr
      _ = 32 * x := by ring
  rw [norm_mul]
  calc _ ≤ x ^ (-(101 / 100) : ℝ) * (32 * x) :=
        mul_le_mul hX hD (norm_nonneg _) (by positivity)
    _ = 32 * x ^ (-(1 / 100) : ℝ) := by
        rw [show x ^ (-(1 / 100) : ℝ) = x ^ (-(101 / 100) : ℝ) * x by
          rw [← Real.rpow_add_one hx.1.ne']; norm_num]
        ring

/-- The integrand of `P(cε - 1, ε)`. -/
noncomputable def i12HSPIg (c ε : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (ε - 1) * (((i12H x : ℝ) : ℂ) ^ (c * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (c * ε - 1))

/-- The hypotheses of the holomorphic-parametric-integral lemmas for `P(cε - 1, ε)` on a ball
inside `‖ε‖ < 1/100`. -/
theorem i12HS_P_hyps {c : ℂ} (hc : ‖c‖ ≤ 2) {w : ℂ} {r : ℝ}
    (hsub : ∀ v ∈ ball w r, ‖v‖ < 1 / 100) :
    Integrable (fun x : ℝ => 32 * x ^ (-(1 / 100) : ℝ)) (volume.restrict (Ioo 0 1)) ∧
      (∀ v ∈ ball w r, AEStronglyMeasurable (i12HSPIg c v) (volume.restrict (Ioo 0 1))) ∧
      (∀ᵐ x : ℝ ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ v ∈ ball w r,
        ‖i12HSPIg c v x‖ ≤ 32 * x ^ (-(1 / 100) : ℝ)) ∧
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        DifferentiableOn ℂ (fun v => i12HSPIg c v x) (ball w r) := by
  refine ⟨(integrableOn_rpow_Ioo (a := -(1 / 100)) (by norm_num)).const_mul 32,
    fun v _ => ?_, (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall
      fun _ hx v hv => i12HS_norm_P_integrand_le (hsub v hv) hc hx), ?_⟩
  · refine Measurable.aestronglyMeasurable ?_
    unfold i12HSPIg i12H; fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
    have h1 : 0 < x := hx.1
    have h2 : 0 < i12H x := i12HS_h_pos (by linarith [hx.2])
    have h3 : 0 < i12H 0 := i12HS_h_pos (by norm_num)
    refine Differentiable.differentiableOn ?_
    unfold i12HSPIg
    fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

/-- **`ε ↦ P(cε - 1, ε)` is holomorphic** on `‖ε‖ < 1/100` for `‖c‖ ≤ 2`. -/
theorem differentiableOn_i12HSP_lin {c : ℂ} (hc : ‖c‖ ≤ 2) :
    DifferentiableOn ℂ (fun ε => i12HSP (c * ε - 1) ε) (ball 0 (1 / 100)) := by
  intro w hw
  have hw' : ‖w‖ < 1 / 100 := by simpa using hw
  have hr : 0 < 1 / 100 - ‖w‖ := by linarith
  have hsub : ∀ v ∈ ball w (1 / 100 - ‖w‖), ‖v‖ < 1 / 100 := by
    intro v hv
    rw [mem_ball, dist_eq_norm] at hv
    calc ‖v‖ ≤ ‖v - w‖ + ‖w‖ := by simpa using norm_add_le (v - w) w
      _ < 1 / 100 := by linarith
  obtain ⟨hb, hm, hdom, hdiff⟩ := i12HS_P_hyps hc hsub
  obtain ⟨-, hd⟩ := i12_deriv_integral_eventuallyEq (z₁ := w) hr hb hm hdom hdiff w
    (mem_ball_self (half_pos hr))
  exact hd.differentiableAt.differentiableWithinAt

/-- The pointwise `n`-th `ε`-derivative at `0` of the integrand of `P(cε - 1, ε)`. -/
theorem iteratedDeriv_i12HSPIg {c : ℂ} {x : ℝ} (hx : 0 < x) (hx2 : x < 2) (n : ℕ) :
    iteratedDeriv n (fun ε => i12HSPIg c ε x) 0 =
      (Real.log x + c * Real.log (i12H x)) ^ n / ((x * i12H x : ℝ) : ℂ) -
        (Real.log x + c * Real.log (i12H 0)) ^ n / ((x * i12H 0 : ℝ) : ℂ) := by
  have hA := i12HS_h_pos hx2
  have hB := i12HS_h_pos (x := 0) (by norm_num)
  have hpow : ∀ {H : ℝ}, 0 < H → ∀ ε : ℂ, (x : ℂ) ^ (ε - 1) * (H : ℂ) ^ (c * ε - 1) =
      (1 / ((x * H : ℝ) : ℂ)) * exp ((Real.log x + c * Real.log H) * ε) := by
    intro H hH ε
    have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    have hH' : (H : ℂ) ≠ 0 := ofReal_ne_zero.mpr hH.ne'
    rw [cpow_sub _ _ hx', cpow_sub _ _ hH', cpow_one, cpow_one, i12_cpow_lin hx,
      i12_cpow_lin hH, add_mul, exp_add]
    push_cast
    field_simp
  have e : (fun ε => i12HSPIg c ε x) = fun ε =>
      (1 / ((x * i12H x : ℝ) : ℂ)) * exp ((Real.log x + c * Real.log (i12H x)) * ε) -
        (1 / ((x * i12H 0 : ℝ) : ℂ)) * exp ((Real.log x + c * Real.log (i12H 0)) * ε) := by
    funext ε
    rw [i12HSPIg, mul_sub, hpow hA, hpow hB]
  rw [e, iteratedDeriv_fun_sub (by fun_prop) (by fun_prop), i12_iteratedDeriv_exp_zero,
    i12_iteratedDeriv_exp_zero]
  ring

/-- **The Taylor coefficients of `P(cε - 1, ε)`** at `ε = 0`, as integrals over `(0, 1)` of
`(log x + c log h(x)) ^ n / (x h(x)) - (log x + c log h(0)) ^ n / (x h(0))`. -/
theorem iteratedDeriv_i12HSP_lin {c : ℂ} (hc : ‖c‖ ≤ 2) (n : ℕ) :
    iteratedDeriv n (fun ε => i12HSP (c * ε - 1) ε) 0 =
      ∫ x in Ioo (0 : ℝ) 1, ((Real.log x + c * Real.log (i12H x)) ^ n /
          ((x * i12H x : ℝ) : ℂ) -
        (Real.log x + c * Real.log (i12H 0)) ^ n / ((x * i12H 0 : ℝ) : ℂ)) := by
  have hsub : ∀ v ∈ ball (0 : ℂ) (1 / 100), ‖v‖ < 1 / 100 := fun v hv => by simpa using hv
  obtain ⟨hb, hm, hdom, hdiff⟩ := i12HS_P_hyps hc hsub
  obtain ⟨-, hE⟩ := i12_iteratedDeriv_integral_center n (z₁ := 0)
    (by norm_num : (0 : ℝ) < 1 / 100) hb hm hdom hdiff
  have hP : (fun ε => i12HSP (c * ε - 1) ε) =
      fun ε => ∫ x, i12HSPIg c ε x ∂(volume.restrict (Ioo 0 1)) := rfl
  rw [hP, hE]
  exact setIntegral_congr_fun measurableSet_Ioo fun x hx =>
    iteratedDeriv_i12HSPIg hx.1 (by linarith [hx.2]) n

/-- The analytic form of `ε ∫ Good`:
`(3/2) a (1 - 3ε) / ((1 - ε)² (1 - 2ε)) Γ(1 + 2ε) Γ(1 + ε) / Γ(1 + 3ε) P(ε - 1, ε)
  - a B_w P(-ε - 1, ε) / 2 - a B_w P(2ε - 1, ε)` (`a = 2 - 3ε`). -/
noncomputable def i12HSGoodR (ε : ℂ) : ℂ :=
  3 / 2 * ((2 - 3 * ε) * (1 - 3 * ε) / ((1 - ε) * (1 - 2 * ε) * (1 - ε))) *
      (Gamma (1 + 2 * ε) * Gamma (1 + ε) / Gamma (1 + 3 * ε)) * i12HSP (ε - 1) ε -
    (2 - 3 * ε) * i12HSBw ε / 2 * i12HSP (-ε - 1) ε -
    (2 - 3 * ε) * i12HSBw ε * i12HSP (2 * ε - 1) ε

theorem i12HS_Gamma_facts {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gamma s ∧ Gamma s ≠ 0 := by
  refine ⟨Complex.differentiableAt_Gamma _ fun m h => ?_, Complex.Gamma_ne_zero_of_re_pos hs⟩
  have := congrArg re h
  simp only [neg_re, natCast_re] at this
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- `ε ∫ Good = R(ε)` for `0 < re ε`, `‖ε‖ < 1/100` (from the closed form). -/
theorem i12HS_mul_GoodI_eq_of_re_pos {ε : ℂ} (hε : ‖ε‖ < 1 / 100) (h0 : 0 < ε.re) :
    ε * i12HSGoodI ε = i12HSGoodR ε := by
  have hre := abs_le.mp ((abs_re_le_norm ε).trans hε.le)
  have hε0 : ε ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have h1 : (1 - ε) ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have h2 : (1 - 2 * ε) ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have g1 : Gamma (1 + ε) = ε * Gamma ε := by rw [add_comm, Complex.Gamma_add_one _ hε0]
  have g2 : Gamma (1 + 2 * ε) = 2 * ε * Gamma (2 * ε) := by
    rw [add_comm, Complex.Gamma_add_one _ (mul_ne_zero two_ne_zero hε0)]
  have g3 : Gamma (1 + 3 * ε) = 3 * ε * Gamma (2 * ε + ε) := by
    rw [show 2 * ε + ε = 3 * ε by ring, add_comm,
      Complex.Gamma_add_one _ (mul_ne_zero three_ne_zero hε0)]
  have hG3 : Gamma (2 * ε + ε) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [i12HSGoodI, i12HS_integral_good_of_norm hε h0, i12HSGoodR, i12HSMphi, g1, g2, g3]
  field_simp

/-- **`R` is holomorphic** on `‖ε‖ < 1/100`. -/
theorem differentiableOn_i12HSGoodR : DifferentiableOn ℂ i12HSGoodR (ball 0 (1 / 100)) := by
  intro w hw
  have hw' : ‖w‖ < 1 / 100 := by simpa using hw
  have hre := abs_le.mp ((abs_re_le_norm w).trans hw'.le)
  have hn := isOpen_ball.mem_nhds hw
  have hP1 : DifferentiableAt ℂ (fun ε => i12HSP (ε - 1) ε) w := by
    have := (differentiableOn_i12HSP_lin (c := 1) (by simp)).differentiableAt hn
    simpa only [one_mul] using this
  have hP2 : DifferentiableAt ℂ (fun ε => i12HSP (-ε - 1) ε) w := by
    have := (differentiableOn_i12HSP_lin (c := -1) (by simp)).differentiableAt hn
    simpa only [neg_one_mul] using this
  have hP3 : DifferentiableAt ℂ (fun ε => i12HSP (2 * ε - 1) ε) w :=
    (differentiableOn_i12HSP_lin (c := 2) (by simp)).differentiableAt hn
  obtain ⟨d1, -⟩ := i12HS_Gamma_facts (s := 1 + 2 * w) (by simp; linarith)
  obtain ⟨d2, -⟩ := i12HS_Gamma_facts (s := 1 + w) (by simp; linarith)
  obtain ⟨d3, n3⟩ := i12HS_Gamma_facts (s := 1 + 3 * w) (by simp; linarith)
  obtain ⟨d4, -⟩ := i12HS_Gamma_facts (s := 1 - 2 * w) (by simp; linarith)
  obtain ⟨d5, n5⟩ := i12HS_Gamma_facts (s := 2 - w) (by simp; linarith)
  have e1 : DifferentiableAt ℂ (fun ε => Gamma (1 + 2 * ε)) w := d1.comp w (by fun_prop)
  have e2 : DifferentiableAt ℂ (fun ε => Gamma (1 + ε)) w := d2.comp w (by fun_prop)
  have e3 : DifferentiableAt ℂ (fun ε => Gamma (1 + 3 * ε)) w := d3.comp w (by fun_prop)
  have e4 : DifferentiableAt ℂ (fun ε => Gamma (1 - 2 * ε)) w := d4.comp w (by fun_prop)
  have e5 : DifferentiableAt ℂ (fun ε => Gamma (2 - ε)) w := d5.comp w (by fun_prop)
  have hden : (1 - w) * (1 - 2 * w) * (1 - w) ≠ 0 := by
    have h1 : (1 - w) ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    have h2 : (1 - 2 * w) ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    exact mul_ne_zero (mul_ne_zero h1 h2) h1
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold i12HSGoodR i12HSBw
  fun_prop (disch := assumption)

/-- **The identity theorem**: `ε ∫ Good = R(ε)` on `‖ε‖ < 1/100`. -/
theorem i12HS_mul_GoodI_eq {ε : ℂ} (hε : ε ∈ ball (0 : ℂ) (1 / 100)) :
    ε * i12HSGoodI ε = i12HSGoodR ε := by
  have hf : AnalyticOnNhd ℂ (fun ε => ε * i12HSGoodI ε) (ball 0 (1 / 100)) :=
    (differentiableOn_id.mul differentiableOn_i12HSGoodI).analyticOnNhd isOpen_ball
  have hg := differentiableOn_i12HSGoodR.analyticOnNhd isOpen_ball
  have h0 : ((1 / 200 : ℝ) : ℂ) ∈ ball (0 : ℂ) (1 / 100) := by
    rw [mem_ball_zero_iff, norm_real]; norm_num
  have hev : (fun ε => ε * i12HSGoodI ε) =ᶠ[𝓝 ((1 / 200 : ℝ) : ℂ)] i12HSGoodR := by
    filter_upwards [ball_mem_nhds ((1 / 200 : ℝ) : ℂ) (by norm_num : (0 : ℝ) < 1 / 400)]
      with v hv
    rw [mem_ball, dist_eq_norm] at hv
    have h1 := abs_le.mp ((abs_re_le_norm (v - ((1 / 200 : ℝ) : ℂ))).trans hv.le)
    simp only [sub_re, ofReal_re] at h1
    refine i12HS_mul_GoodI_eq_of_re_pos ?_ (by linarith)
    calc ‖v‖ ≤ ‖v - ((1 / 200 : ℝ) : ℂ)‖ + ‖((1 / 200 : ℝ) : ℂ)‖ := by
          simpa using norm_add_le (v - ((1 / 200 : ℝ) : ℂ)) ((1 / 200 : ℝ) : ℂ)
      _ < 1 / 100 := by rw [norm_real, Real.norm_of_nonneg (by norm_num)]; linarith
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_ball _ _).isPreconnected h0 hev hε

/-- **The Taylor coefficients of the good part from `R`**:
`R⁽ⁿ⁺¹⁾(0) = (n + 1) ∫ Good_n`. -/
theorem iteratedDeriv_succ_i12HSGoodR (n : ℕ) :
    iteratedDeriv (n + 1) i12HSGoodR 0 =
      (n + 1) * ((∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1),
        i12HSGoodDn n z.1 z.2.1 z.2.2 : ℝ) : ℂ) := by
  have hev : i12HSGoodR =ᶠ[𝓝 0] fun ε => ε * i12HSGoodI ε := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 100)] with v hv
    exact (i12HS_mul_GoodI_eq hv).symm
  have hS : ContDiffAt ℂ (n + 1) i12HSGoodI 0 :=
    (differentiableOn_i12HSGoodI.analyticAt (ball_mem_nhds _ (by norm_num))).contDiffAt
  rw [hev.iteratedDeriv_eq, iteratedDeriv_fun_mul (f := fun ε => ε) contDiffAt_id hS]
  rw [Finset.sum_eq_single 1 (fun i _ hi => by simp [iteratedDeriv_fun_id_zero, hi])
    (fun h => by simp at h)]
  simp only [iteratedDeriv_fun_id_zero, Nat.choose_one_right, ite_true, mul_one,
    Nat.add_sub_cancel]
  rw [iteratedDeriv_i12HSGoodI_eq_real]
  push_cast
  ring

end QED.ThreeLoopD
