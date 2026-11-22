/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSWire

/-!
# Set (d), master `I₁₂`: the bad part of the bulk remainder as a holomorphic function

The bad part of the bulk remainder is the function

  `Bad(ε) = R₁(ε) + R_A(ε) + R_B(ε) - ∫ Good(ε)`   (`QED.ThreeLoopD.i12HSBadF`),

holomorphic on `‖ε‖ < 1/200`. Its Taylor coefficients at `0` are exactly the left sides of the
bad-part identities of `QED.ThreeLoopD.SetDMastersI12RHighSWire`:

  `Bad⁽ⁿ⁾(0) = ∫_{(0,1)³} D₁ⁿ + rest_n`   (`QED.ThreeLoopD.iteratedDeriv_i12HSBadF`).

Hence `r₃`, `r₄` (hypotheses `h3`, `h4`) follow from `Bad⁽²⁾(0) = 2 Bad₂`, `Bad⁽³⁾(0) = 6 Bad₃`
(`QED.ThreeLoopD.i12Rest_coeff_three_of_badF`, `QED.ThreeLoopD.i12Rest_coeff_four_of_badF`), and
in particular from an identity `Bad(x) = G(x)` for real `x ∈ (0, δ)` only, with `G` analytic at
`0` (the identity theorem, `QED.ThreeLoopD.i12HSBadF_eventuallyEq_of_real`). This is the form in
which the ε-exact decomposition of the bad part (absolutely convergent integrals for small
real `ε > 0`) is to be used.

## Main results

* `QED.ThreeLoopD.analyticOnNhd_i12HSBadF`, `QED.ThreeLoopD.iteratedDeriv_i12HSBadF`.
* `QED.ThreeLoopD.i12HSBadF_eventuallyEq_of_real`.
* `QED.ThreeLoopD.i12Rest_coeff_three_of_badF`, `QED.ThreeLoopD.i12Rest_coeff_four_of_badF`,
  `QED.ThreeLoopD.i12Rest_coeff_three_of_real`, `QED.ThreeLoopD.i12Rest_coeff_four_of_real`.
-/

@[expose] public section

open Complex Set MeasureTheory Metric Filter Topology

namespace QED.ThreeLoopD

/-- The bad part of the bulk remainder, `R₁ + R_A + R_B - ∫ Good`. -/
noncomputable def i12HSBadF (ε : ℂ) : ℂ :=
  i12R1 ε + i12RA3 ε + i12RB3 ε - i12HSGoodI ε

theorem differentiableAt_i12HSBadF {ε₀ : ℂ} (h : ‖ε₀‖ < 1 / 200) :
    DifferentiableAt ℂ i12HSBadF ε₀ := by
  have hG : DifferentiableAt ℂ i12HSGoodI ε₀ :=
    differentiableOn_i12HSGoodI.differentiableAt
      (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith))
  exact (((differentiableAt_i12R1 h).add (differentiableAt_i12RA3 h)).add
    (differentiableAt_i12RB3 h)).sub hG

/-- **The bad part is holomorphic** on `‖ε‖ < 1/200`. -/
theorem analyticOnNhd_i12HSBadF : AnalyticOnNhd ℂ i12HSBadF (ball 0 (1 / 200)) := by
  have h : DifferentiableOn ℂ i12HSBadF (ball 0 (1 / 200)) := fun ε hε =>
    (differentiableAt_i12HSBadF (by simpa using hε)).differentiableWithinAt
  exact h.analyticOnNhd isOpen_ball

theorem analyticAt_i12HSBadF : AnalyticAt ℂ i12HSBadF 0 :=
  analyticOnNhd_i12HSBadF 0 (mem_ball_self (by norm_num))

/-- **The Taylor coefficients of the bad part**: `Bad⁽ⁿ⁾(0) = ∫ D₁ⁿ + rest_n`. -/
theorem iteratedDeriv_i12HSBadF (n : ℕ) :
    iteratedDeriv n i12HSBadF 0 =
      (∫ z in i12Cube, (i12R1Dn n z.1 z.2.1 z.2.2 : ℂ)) + (i12HSRest n : ℂ) := by
  have hR1 := i12_contDiffAt_zero (fun _ h => differentiableAt_i12R1 h) n
  have hRA := i12_contDiffAt_zero (fun _ h => differentiableAt_i12RA3 h) n
  have hRB := i12_contDiffAt_zero (fun _ h => differentiableAt_i12RB3 h) n
  have hG : ContDiffAt ℂ n i12HSGoodI 0 :=
    (differentiableOn_i12HSGoodI.analyticAt (ball_mem_nhds _ (by norm_num))).contDiffAt
  have e : i12HSBadF = fun ε => i12R1 ε + i12RA3 ε + i12RB3 ε - i12HSGoodI ε := rfl
  rw [e, iteratedDeriv_fun_sub ((hR1.add hRA).add hRB) hG,
    iteratedDeriv_fun_add (hR1.add hRA) hRB, iteratedDeriv_fun_add hR1 hRA,
    (iteratedDeriv_i12R1_eq_integral n).2, (iteratedDeriv_i12RA3_eq_integral n).2,
    (iteratedDeriv_i12RB3_eq_integral n).2, add_assoc (∫ z in i12Cube, (i12R1Dn n z.1 z.2.1
      z.2.2 : ℂ)), (integral_i12RA3Dn_add_i12RB3Dn n).2, iteratedDeriv_i12HSGoodI_eq_real,
    (integral_i12HSW_split n).2.2, i12HSRest]
  push_cast
  ring

/-- **The identity theorem at `0` from real `ε > 0`**: if the bad part agrees with a function
`G` analytic at `0` at every real `x ∈ (0, δ)`, then it agrees with `G` near `0`. -/
theorem i12HSBadF_eventuallyEq_of_real {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0) {δ : ℝ}
    (hδ : 0 < δ) (h : ∀ x : ℝ, 0 < x → x < δ → i12HSBadF x = G x) :
    i12HSBadF =ᶠ[𝓝 0] G := by
  refine (analyticAt_i12HSBadF.eventually_eq_or_eventually_ne hG).resolve_right fun hne => ?_
  obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hne)
  set x : ℝ := min r δ / 2 with hx
  have hm : 0 < min r δ := lt_min hr hδ
  have hx0 : 0 < x := by rw [hx]; linarith
  have hxr : x < r := by rw [hx]; linarith [min_le_left r δ]
  have hxd : x < δ := by rw [hx]; linarith [min_le_right r δ]
  refine hP (y := (x : ℂ)) ?_ ?_ (h x hx0 hxd)
  · rw [dist_zero_right, norm_real, Real.norm_of_nonneg hx0.le]; exact hxr
  · simpa using hx0.ne'

/-- **`r₃` from the bad part**: if `Bad⁽²⁾(0) = 2 Bad₂` then `i12Rest⁽³⁾(0)/3! = r₃`. -/
theorem i12Rest_coeff_three_of_badF (h : iteratedDeriv 2 i12HSBadF 0 = 2 * (i12HSBad2 : ℂ)) :
    iteratedDeriv 3 i12Rest 0 / (3 : ℕ).factorial = i12RestR3 :=
  i12Rest_coeff_three_of_bad (by rw [← iteratedDeriv_i12HSBadF]; exact h)

/-- **`r₄` from the bad part**: if `Bad⁽³⁾(0) = 6 Bad₃` then `i12Rest⁽⁴⁾(0)/4! = r₄`. -/
theorem i12Rest_coeff_four_of_badF (h : iteratedDeriv 3 i12HSBadF 0 = 6 * (i12HSBad3 : ℂ)) :
    iteratedDeriv 4 i12Rest 0 / (4 : ℕ).factorial = i12RestR4 :=
  i12Rest_coeff_four_of_bad (by rw [← iteratedDeriv_i12HSBadF]; exact h)

/-- **`r₃` from a real-`ε` identity for the bad part**: if `Bad(x) = G(x)` for real
`x ∈ (0, δ)`, `G` analytic at `0` with `G⁽²⁾(0) = 2 Bad₂`, then `i12Rest⁽³⁾(0)/3! = r₃`. -/
theorem i12Rest_coeff_three_of_real {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : ℝ, 0 < x → x < δ → i12HSBadF x = G x)
    (h2 : iteratedDeriv 2 G 0 = 2 * (i12HSBad2 : ℂ)) :
    iteratedDeriv 3 i12Rest 0 / (3 : ℕ).factorial = i12RestR3 :=
  i12Rest_coeff_three_of_badF (by rw [(i12HSBadF_eventuallyEq_of_real hG hδ h).iteratedDeriv_eq,
    h2])

/-- **`r₄` from a real-`ε` identity for the bad part**: if `Bad(x) = G(x)` for real
`x ∈ (0, δ)`, `G` analytic at `0` with `G⁽³⁾(0) = 6 Bad₃`, then `i12Rest⁽⁴⁾(0)/4! = r₄`. -/
theorem i12Rest_coeff_four_of_real {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : ℝ, 0 < x → x < δ → i12HSBadF x = G x)
    (h3 : iteratedDeriv 3 G 0 = 6 * (i12HSBad3 : ℂ)) :
    iteratedDeriv 4 i12Rest 0 / (4 : ℕ).factorial = i12RestR4 :=
  i12Rest_coeff_four_of_badF (by rw [(i12HSBadF_eventuallyEq_of_real hG hδ h).iteratedDeriv_eq,
    h3])

end QED.ThreeLoopD
