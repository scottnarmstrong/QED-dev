/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Set (d), master `I₁₂`: first derivatives of the three-dimensional remainders

The second Taylor coefficient of `QED.ThreeLoopD.i12Rest` contains `R₁'(0) + R_A'(0) + R_B'(0)`
(`QED.ThreeLoopD.iteratedDeriv_two_i12Rest_eq`). This file computes the pointwise
`ε`-derivatives at `0` of the three integrands and differentiates under the integral sign.

With `h = QED.ThreeLoopD.i12H`, `g = QED.ThreeLoopD.i12Rg` and `P = u (1 - u)`:

* the face difference `G_A - G_A⁰` of the sector `t < v` vanishes at `ε = 0` and has derivative
  `(-2 log (1 - ρθ) + g(uθ / ((1 - u) h(ρ)))) / h(ρ)` (`QED.ThreeLoopD.i12RAd`), so the
  integrand of `R_A` has derivative `(i12RAd ρ θ u - i12RAd 0 θ u) / (ρθ)`;
* the face difference `G_B - G_B⁰` of the sector `v < t` equals `2/h(ρθ) - 2/h(0)` at
  `ε = 0` and has derivative `QED.ThreeLoopD.i12RBd`; the integrand of `R_B` has derivative
  `((log ρ + 2 log θ)(2/h(ρθ) - 4) + i12RBd ρ θ u - i12RBd 0 θ u) / (ρθ)`;
* the integrand `W Φ₁(X, Y)` of `R₁` has derivative
  `((2 log (ct) - log (1 - t) + log P) X Y + Φ₁'(X, Y)) / (ct)` with
  `Φ₁' = -3 (N² log N - S² log S) / (XY) - 3 (X + Y) - 6 (X log X + Y log Y)`,
  `N = X + Y - XY`, `S = X + Y` (`QED.ThreeLoopD.i12R1d`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12RA3_zero`, `QED.ThreeLoopD.hasDerivAt_i12RB3_zero`,
  `QED.ThreeLoopD.hasDerivAt_i12R1_zero`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-! ### Differentiation under the integral sign over the cube -/

/-- Differentiation at `0` under the integral sign over `(0, 1)³`, with the majorant
`QED.ThreeLoopD.i12Maj3`. -/
theorem i12_hasDerivAt_cube_integral {F : ℂ → ℝ × ℝ × ℝ → ℂ} {f : ℝ × ℝ × ℝ → ℝ} {C : ℝ}
    (hm : ∀ ε, Measurable (F ε))
    (hb : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), ∀ ε : ℂ, ‖ε‖ < 1 / 100 →
      ‖F ε z‖ ≤ C * i12Maj3 z)
    (hd : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
      Differentiable ℂ fun ε => F ε z)
    (hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
      HasDerivAt (fun ε => F ε z) ((f z : ℝ) : ℂ) 0) :
    Integrable (fun z => ((f z : ℝ) : ℂ))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) ∧
      HasDerivAt (fun ε => ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), F ε z)
        (∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), ((f z : ℝ) : ℂ)) 0 := by
  have h0 : ‖(0 : ℂ)‖ < 1 / 200 := by norm_num
  obtain ⟨hi, hD⟩ := i12_hasDerivAt_integral_of_holomorphic (z₁ := 0) (F := F)
    (by norm_num : (0 : ℝ) < 1 / 200) (b := fun z => C * i12Maj3 z)
    (integrable_i12Maj3.const_mul C) (fun ε _ => (hm ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem i12_measurableSet3 fun z hz ε hε =>
      hb z hz ε (i12_ball_small h0 ε hε))
    (ae_restrict_of_forall_mem i12_measurableSet3 fun z hz => (hd z hz).differentiableOn)
  have hpt' : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
      deriv (fun ε => F ε z) 0 = ((f z : ℝ) : ℂ) := fun z hz => (hpt z hz).deriv
  refine ⟨hi.congr (ae_restrict_of_forall_mem i12_measurableSet3 hpt'), ?_⟩
  rw [← setIntegral_congr_fun i12_measurableSet3 hpt']
  exact hD

/-! ### Elementary derivatives -/

/-- `d/dε x ^ f(ε) = x ^ f(0) log x f'(0)` at `0`, for real `x > 0`. -/
theorem i12_hasDerivAt_ofReal_cpow {x : ℝ} (hx : 0 < x) {f : ℂ → ℂ} {f' : ℂ}
    (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun ε => (x : ℂ) ^ f ε) ((x : ℂ) ^ f 0 * ((Real.log x : ℝ) : ℂ) * f') 0 := by
  have := hf.const_cpow (c := (x : ℂ)) (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  rwa [ofReal_log hx.le]

theorem i12_hasDerivAt_lin (a b : ℂ) : HasDerivAt (fun ε : ℂ => a * ε + b) a 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).const_mul a).add_const b

/-- The derivative of the sector weight: `d/dε ρ ^ (ε - 1) θ ^ (2ε - 1) = (log ρ + 2 log θ)/(ρθ)`
at `0`. -/
theorem hasDerivAt_i12SecWt {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) :
    HasDerivAt (fun ε => i12SecWt ε ρ θ)
      (((Real.log ρ + 2 * Real.log θ) / (ρ * θ) : ℝ) : ℂ) 0 := by
  have h1 := i12_hasDerivAt_ofReal_cpow hρ (i12_hasDerivAt_lin 1 (-1))
  have h2 := i12_hasDerivAt_ofReal_cpow hθ (i12_hasDerivAt_lin 2 (-1))
  have h := h1.mul h2
  have e : (fun ε => i12SecWt ε ρ θ) =
      fun ε => (ρ : ℂ) ^ (1 * ε + -1) * (θ : ℂ) ^ (2 * ε + -1) := by
    funext ε
    simp only [i12SecWt, one_mul]
    ring_nf
  rw [e]
  convert h using 1
  have hρc : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.ne'
  have hθc : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ.ne'
  simp only [mul_zero, zero_add, cpow_neg_one]
  push_cast
  field_simp

theorem i12SecWt_zero (ρ θ : ℝ) : i12SecWt 0 ρ θ = (((ρ * θ)⁻¹ : ℝ) : ℂ) := by
  simp only [i12SecWt, mul_zero, zero_sub, cpow_neg_one]
  push_cast
  ring

/-! ### The sector `t < v` -/

/-- The `ε`-derivative at `0` of the face difference `G_A - G_A⁰`. -/
noncomputable def i12RAd (ρ θ u : ℝ) : ℝ :=
  (-2 * Real.log (1 - ρ * θ) + i12Rg (u * θ / ((1 - u) * i12H ρ))) / i12H ρ

theorem i12GA_sub_zero {ρ θ u : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) : i12GA 0 ρ θ u - i12GA0 0 ρ u = 0 := by
  have hY : 0 < (1 - u) * i12H ρ := mul_pos (by linarith [hu.2]) (i12H_pos (by linarith [hρ.2]))
  have hX : 0 < u * θ := mul_pos hu.1 hθ.1
  simp only [i12GA, i12GA0, i12Phi0_zero hX hY]
  simp

theorem hasDerivAt_i12GA_sub {ρ θ u : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε => i12GA ε ρ θ u - i12GA0 ε ρ u) ((i12RAd ρ θ u : ℝ) : ℂ) 0 := by
  have hH : 0 < i12H ρ := i12H_pos (by linarith [hρ.2])
  have hL : 0 < 1 - ρ * θ := by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]
  have hP : 0 < u * (1 - u) := mul_pos hu.1 (by linarith [hu.2])
  have hY : 0 < (1 - u) * i12H ρ := mul_pos (by linarith [hu.2]) hH
  have hX : 0 < u * θ := mul_pos hu.1 hθ.1
  have e : (fun ε => i12GA ε ρ θ u - i12GA0 ε ρ u) = fun ε =>
      (((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        ((1 - ρ * θ : ℝ) : ℂ) ^ (-ε)) * (i12Phi0 ε (u * θ) ((1 - u) * i12H ρ) -
          (2 - 3 * ε) * (((1 - u) * i12H ρ : ℝ) : ℂ) ^ (-3 * ε)) +
      (((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        ((2 - 3 * ε) * (((1 - u) * i12H ρ : ℝ) : ℂ) ^ (-3 * ε))) *
        (((1 - ρ * θ : ℝ) : ℂ) ^ (-1 * ε + 0) - 1) := by
    funext ε
    simp only [i12GA, i12GA0, neg_one_mul, add_zero]
    ring
  have hA : DifferentiableAt ℂ (fun ε : ℂ => ((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1) *
      ((u * (1 - u) : ℝ) : ℂ) ^ ε * ((1 - ρ * θ : ℝ) : ℂ) ^ (-ε)) 0 := by
    fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
  have hB : DifferentiableAt ℂ (fun ε : ℂ => ((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1) *
      ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        ((2 - 3 * ε) * (((1 - u) * i12H ρ : ℝ) : ℂ) ^ (-3 * ε))) 0 := by
    fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
  have hC := (i12_hasDerivAt_ofReal_cpow hL (i12_hasDerivAt_lin (-1) 0)).sub_const 1
  have h := (hA.hasDerivAt.mul (hasDerivAt_i12_bracket hX hY)).add (hB.hasDerivAt.mul hC)
  rw [e]
  convert h using 1
  have hHc : ((i12H ρ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hH.ne'
  simp only [i12RAd, mul_zero, zero_sub, neg_zero, add_zero, cpow_zero, cpow_neg_one, sub_zero,
    mul_one, i12Phi0_zero hX hY, sub_self]
  push_cast
  field_simp
  ring

/-- The pointwise `ε`-derivative at `0` of the integrand of `R_A`. -/
theorem hasDerivAt_i12RA3_integrand {ρ θ u : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hθ : θ ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε => i12SecWt ε ρ θ * (i12GA ε ρ θ u - i12GA ε 0 θ u -
      i12GA0 ε ρ u + i12GA0 ε 0 u)) (((i12RAd ρ θ u - i12RAd 0 θ u) / (ρ * θ) : ℝ) : ℂ) 0 := by
  have hρ' : ρ ∈ Ico (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2⟩
  have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  have h := (hasDerivAt_i12SecWt hρ.1 hθ.1).mul
    ((hasDerivAt_i12GA_sub hρ' hθ hu).sub (hasDerivAt_i12GA_sub h0' hθ hu))
  have e : (fun ε => i12SecWt ε ρ θ * (i12GA ε ρ θ u - i12GA ε 0 θ u -
      i12GA0 ε ρ u + i12GA0 ε 0 u)) = fun ε => i12SecWt ε ρ θ *
        ((i12GA ε ρ θ u - i12GA0 ε ρ u) - (i12GA ε 0 θ u - i12GA0 ε 0 u)) := by
    funext ε; ring
  rw [e]
  convert h using 1
  simp only [Pi.sub_apply]
  rw [i12GA_sub_zero hρ' hθ hu, i12GA_sub_zero h0' hθ hu, i12SecWt_zero]
  push_cast
  ring

/-- **`R_A'(0)` under the integral sign.** -/
theorem hasDerivAt_i12RA3_zero :
    Integrable (fun z : ℝ × ℝ × ℝ =>
        (((i12RAd z.1 z.2.1 z.2.2 - i12RAd 0 z.2.1 z.2.2) / (z.1 * z.2.1) : ℝ) : ℂ))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) ∧
      HasDerivAt i12RA3 (∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
        (((i12RAd z.1 z.2.1 z.2.2 - i12RAd 0 z.2.1 z.2.2) / (z.1 * z.2.1) : ℝ) : ℂ)) 0 := by
  refine i12_hasDerivAt_cube_integral (C := 20000)
    (fun ε => by unfold i12SecWt i12GA i12GA0 i12Phi0 i12H; fun_prop)
    (fun z hz ε hε => norm_i12RA3_integrand_le hε hz) (fun z hz => ?_)
    (fun z hz => hasDerivAt_i12RA3_integrand hz.1 hz.2.1 hz.2.2)
  obtain ⟨hρ, hθ, hu⟩ := hz
  have hρ' : z.1 ∈ Ico (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2⟩
  have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  exact (differentiable_i12SecWt hρ.1 hθ.1).mul
    ((((differentiable_i12GA hρ' hθ hu).sub (differentiable_i12GA h0' hθ hu)).sub
      (differentiable_i12GA0 hρ' hu)).add (differentiable_i12GA0 h0' hu))

/-! ### The sector `v < t` -/

/-- The `ε`-derivative at `0` of the face difference `G_B - G_B⁰`. -/
noncomputable def i12RBd (ρ θ u : ℝ) : ℝ :=
  i12Rg ((1 - u) * θ * i12H (ρ * θ) / u) / i12H (ρ * θ) +
    2 * (-Real.log (1 - ρ) + Real.log (u * (1 - u))) * (1 / i12H (ρ * θ) - 1 / i12H 0) +
    2 * (2 * Real.log (i12H (ρ * θ)) / i12H (ρ * θ) - 2 * Real.log (i12H 0) / i12H 0) +
    (1 / i12H (ρ * θ) - 1 / i12H 0) * (-3 - 6 * Real.log u)

theorem i12GB_sub_zero {ρ θ u : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    i12GB 0 ρ θ u - i12GB0 0 ρ u = ((2 / i12H (ρ * θ) - 2 / i12H 0 : ℝ) : ℂ) := by
  have hY : 0 < (1 - u) * θ * i12H (ρ * θ) := mul_pos (mul_pos (by linarith [hu.2]) hθ.1)
    (i12H_pos (by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]))
  simp only [i12GB, i12GB0, i12Phi0_zero hu.1 hY]
  simp only [mul_zero, zero_sub, neg_zero, cpow_zero, cpow_neg_one, mul_one, sub_zero]
  push_cast
  ring

theorem hasDerivAt_i12GB_sub {ρ θ u : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε => i12GB ε ρ θ u - i12GB0 ε ρ u) ((i12RBd ρ θ u : ℝ) : ℂ) 0 := by
  have hH : 0 < i12H (ρ * θ) := i12H_pos (by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2])
  have hH0 : 0 < i12H 0 := i12H_pos (by norm_num)
  have hL : 0 < 1 - ρ := by linarith [hρ.2]
  have hP : 0 < u * (1 - u) := mul_pos hu.1 (by linarith [hu.2])
  have hY : 0 < (1 - u) * θ * i12H (ρ * θ) := mul_pos (mul_pos (by linarith [hu.2]) hθ.1) hH
  have hX : 0 < u := hu.1
  have e : (fun ε => i12GB ε ρ θ u - i12GB0 ε ρ u) = fun ε =>
      (((1 - ρ : ℝ) : ℂ) ^ (-ε) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        ((i12H (ρ * θ) : ℝ) : ℂ) ^ (2 * ε - 1)) *
        (i12Phi0 ε ((1 - u) * θ * i12H (ρ * θ)) u - (2 - 3 * ε) * (u : ℂ) ^ (-3 * ε)) +
      (((1 - ρ : ℝ) : ℂ) ^ (-1 * ε + 0) * ((u * (1 - u) : ℝ) : ℂ) ^ (1 * ε + 0)) *
        (((i12H (ρ * θ) : ℝ) : ℂ) ^ (2 * ε + -1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε + -1)) *
        ((-3 * ε + 2) * (u : ℂ) ^ (-3 * ε + 0)) := by
    funext ε
    simp only [i12GB, i12GB0, i12Phi0_comm ε u, neg_one_mul, one_mul, add_zero,
      ← sub_eq_add_neg]
    ring
  have hA : DifferentiableAt ℂ (fun ε : ℂ => ((1 - ρ : ℝ) : ℂ) ^ (-ε) *
      ((u * (1 - u) : ℝ) : ℂ) ^ ε * ((i12H (ρ * θ) : ℝ) : ℂ) ^ (2 * ε - 1)) 0 := by
    fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))
  have hF := (i12_hasDerivAt_ofReal_cpow hL (i12_hasDerivAt_lin (-1) 0)).mul
    (i12_hasDerivAt_ofReal_cpow hP (i12_hasDerivAt_lin 1 0))
  have hB := (i12_hasDerivAt_ofReal_cpow hH (i12_hasDerivAt_lin 2 (-1))).sub
    (i12_hasDerivAt_ofReal_cpow hH0 (i12_hasDerivAt_lin 2 (-1)))
  have hC := (i12_hasDerivAt_lin (-3) 2).mul
    (i12_hasDerivAt_ofReal_cpow hX (i12_hasDerivAt_lin (-3) 0))
  have h := (hA.hasDerivAt.mul (hasDerivAt_i12_bracket hY hX)).add ((hF.mul hB).mul hC)
  rw [e]
  convert h using 1
  have hHc : ((i12H (ρ * θ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hH.ne'
  have hH0c : ((i12H 0 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hH0.ne'
  simp only [i12RBd, mul_zero, zero_sub, neg_zero, add_zero, zero_add, cpow_zero,
    cpow_neg_one, sub_zero, mul_one, i12Phi0_zero hY hX, sub_self, Pi.mul_apply, Pi.sub_apply]
  push_cast
  field_simp
  ring

/-- The pointwise `ε`-derivative at `0` of the integrand of `R_B`. -/
theorem hasDerivAt_i12RB3_integrand {ρ θ u : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hθ : θ ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε => i12SecWt ε ρ θ * (i12GB ε ρ θ u - i12GB ε 0 θ u -
      i12GB0 ε ρ u + i12GB0 ε 0 u))
      ((((Real.log ρ + 2 * Real.log θ) * (2 / i12H (ρ * θ) - 2 / i12H 0) +
        (i12RBd ρ θ u - i12RBd 0 θ u)) / (ρ * θ) : ℝ) : ℂ) 0 := by
  have hρ' : ρ ∈ Ico (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2⟩
  have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  have h := (hasDerivAt_i12SecWt hρ.1 hθ.1).mul
    ((hasDerivAt_i12GB_sub hρ' hθ hu).sub (hasDerivAt_i12GB_sub h0' hθ hu))
  have e : (fun ε => i12SecWt ε ρ θ * (i12GB ε ρ θ u - i12GB ε 0 θ u -
      i12GB0 ε ρ u + i12GB0 ε 0 u)) = fun ε => i12SecWt ε ρ θ *
        ((i12GB ε ρ θ u - i12GB0 ε ρ u) - (i12GB ε 0 θ u - i12GB0 ε 0 u)) := by
    funext ε; ring
  rw [e]
  convert h using 1
  simp only [Pi.sub_apply]
  rw [i12GB_sub_zero hρ' hθ hu, i12GB_sub_zero h0' hθ hu, i12SecWt_zero, zero_mul, sub_self]
  have hρθ : ρ * θ ≠ 0 := (mul_pos hρ.1 hθ.1).ne'
  push_cast
  field_simp
  ring

/-- **`R_B'(0)` under the integral sign.** -/
theorem hasDerivAt_i12RB3_zero :
    Integrable (fun z : ℝ × ℝ × ℝ =>
        ((((Real.log z.1 + 2 * Real.log z.2.1) * (2 / i12H (z.1 * z.2.1) - 2 / i12H 0) +
          (i12RBd z.1 z.2.1 z.2.2 - i12RBd 0 z.2.1 z.2.2)) / (z.1 * z.2.1) : ℝ) : ℂ))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) ∧
      HasDerivAt i12RB3 (∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
        ((((Real.log z.1 + 2 * Real.log z.2.1) * (2 / i12H (z.1 * z.2.1) - 2 / i12H 0) +
          (i12RBd z.1 z.2.1 z.2.2 - i12RBd 0 z.2.1 z.2.2)) / (z.1 * z.2.1) : ℝ) : ℂ)) 0 := by
  refine i12_hasDerivAt_cube_integral (C := 20000)
    (fun ε => by unfold i12SecWt i12GB i12GB0 i12Phi0 i12H; fun_prop)
    (fun z hz ε hε => norm_i12RB3_integrand_le hε hz) (fun z hz => ?_)
    (fun z hz => hasDerivAt_i12RB3_integrand hz.1 hz.2.1 hz.2.2)
  obtain ⟨hρ, hθ, hu⟩ := hz
  have hρ' : z.1 ∈ Ico (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2⟩
  have h0' : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  exact (differentiable_i12SecWt hρ.1 hθ.1).mul
    ((((differentiable_i12GB hρ' hθ hu).sub (differentiable_i12GB h0' hθ hu)).sub
      (differentiable_i12GB0 hρ' hu)).add (differentiable_i12GB0 h0' hu))

/-! ### The remainder `R₁` -/

/-- `Φ₁'(X, Y) = ∂_ε Φ₁ (ε = 0)`. -/
noncomputable def i12Phi1d (X Y : ℝ) : ℝ :=
  -3 * ((X + Y - X * Y) ^ 2 * Real.log (X + Y - X * Y) - (X + Y) ^ 2 * Real.log (X + Y)) /
    (X * Y) - 3 * (X + Y) - 6 * (X * Real.log X + Y * Real.log Y)

/-- The `ε`-derivative at `0` of the integrand `W Φ₁(ut, (1 - u)c)` of `R₁`. -/
noncomputable def i12R1d (c t u : ℝ) : ℝ :=
  ((2 * Real.log (c * t) - Real.log (1 - t) + Real.log (u * (1 - u))) * (u * t) *
    ((1 - u) * c) + i12Phi1d (u * t) ((1 - u) * c)) / (c * t)

theorem i12Phi1_zero {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) : i12Phi1 0 X Y = ((X * Y : ℝ) : ℂ) := by
  have hX0 : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hY0 : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
  simp only [i12Phi1, mul_zero, sub_zero, cpow_one,
    show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  push_cast
  field_simp
  ring

theorem i12_hasDerivAt_cpow_one_sub {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun ε : ℂ => (x : ℂ) ^ (1 - 3 * ε)) ((x : ℂ) * (Real.log x : ℂ) * (-3)) 0 := by
  have h1 : HasDerivAt (fun ε : ℂ => 1 - 3 * ε) (-3) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul 3).const_sub 1
  have := h1.const_cpow (c := (x : ℂ)) (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  convert this using 1
  rw [ofReal_log hx.le]
  norm_num

theorem hasDerivAt_i12Phi1 {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (hX1 : X < 1) :
    HasDerivAt (fun ε => i12Phi1 ε X Y) ((i12Phi1d X Y : ℝ) : ℂ) 0 := by
  have hN : 0 < X + Y - X * Y := by nlinarith [mul_pos hY (sub_pos.mpr hX1)]
  have hS : 0 < X + Y := add_pos hX hY
  have hlin : HasDerivAt (fun ε : ℂ => 2 - 3 * ε) (-3) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul 3).const_sub 2
  have h := (((i12_hasDerivAt_cpow_two_sub hN).sub (i12_hasDerivAt_cpow_two_sub hS)).div_const
    ((X * Y : ℝ) : ℂ)).add (hlin.mul ((i12_hasDerivAt_cpow_one_sub hX).add
      (i12_hasDerivAt_cpow_one_sub hY)))
  convert h using 1
  · funext ε; rfl
  have hX0 : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hY0 : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
  simp only [i12Phi1d, mul_zero, sub_zero, cpow_one, Pi.add_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_i12Wt {c t u : ℝ} (hc : 0 < c) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε => i12Wt ε c t u) (((2 * Real.log (c * t) - Real.log (1 - t) +
      Real.log (u * (1 - u))) / (c * t) : ℝ) : ℂ) 0 := by
  have h1 : 0 < c * t := mul_pos hc ht.1
  have h2 : 0 < 1 - t := sub_pos.mpr ht.2
  have h3 : 0 < u * (1 - u) := mul_pos hu.1 (sub_pos.mpr hu.2)
  have h := ((i12_hasDerivAt_ofReal_cpow h1 (i12_hasDerivAt_lin 2 (-1))).mul
    (i12_hasDerivAt_ofReal_cpow h2 (i12_hasDerivAt_lin (-1) 0))).mul
    (i12_hasDerivAt_ofReal_cpow h3 (i12_hasDerivAt_lin 1 0))
  have e : (fun ε => i12Wt ε c t u) = fun ε => ((c * t : ℝ) : ℂ) ^ (2 * ε + -1) *
      ((1 - t : ℝ) : ℂ) ^ (-1 * ε + 0) * ((u * (1 - u) : ℝ) : ℂ) ^ (1 * ε + 0) := by
    funext ε
    simp only [i12Wt, neg_one_mul, one_mul, add_zero, ← sub_eq_add_neg]
  rw [e]
  convert h using 1
  have hct : ((c * t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1.ne'
  simp only [mul_zero, zero_add, cpow_zero, cpow_neg_one, mul_one, Pi.mul_apply]
  push_cast
  field_simp
  ring

/-- The pointwise `ε`-derivative at `0` of the integrand of `R₁`. -/
theorem hasDerivAt_i12R1_integrand {c t u : ℝ} (hc : 0 < c) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ε => i12Wt ε c t u * i12Phi1 ε (u * t) ((1 - u) * c))
      ((i12R1d c t u : ℝ) : ℂ) 0 := by
  have hX : 0 < u * t := mul_pos hu.1 ht.1
  have hY : 0 < (1 - u) * c := mul_pos (sub_pos.mpr hu.2) hc
  have hX1 : u * t < 1 := by nlinarith [hu.1, hu.2, ht.1, ht.2]
  have h := (hasDerivAt_i12Wt hc ht hu).mul (hasDerivAt_i12Phi1 hX hY hX1)
  convert h using 1
  have hct : c * t ≠ 0 := (mul_pos hc ht.1).ne'
  rw [i12Phi1_zero hX hY]
  simp only [i12Wt, i12R1d, mul_zero, zero_sub, neg_zero, cpow_zero, cpow_neg_one, mul_one]
  push_cast
  field_simp

/-- **`R₁'(0)` under the integral sign.** -/
theorem hasDerivAt_i12R1_zero :
    Integrable (fun z : ℝ × ℝ × ℝ => ((i12R1d (z.1 * (1 - z.1)) z.2.1 z.2.2 : ℝ) : ℂ))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) ∧
      HasDerivAt i12R1 (∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
        ((i12R1d (z.1 * (1 - z.1)) z.2.1 z.2.2 : ℝ) : ℂ)) 0 := by
  refine i12_hasDerivAt_cube_integral (C := 27) (fun ε => by unfold i12Wt i12Phi1; fun_prop)
    (fun z hz ε hε => norm_i12R1_integrand_le hε hz) (fun z hz => ?_) (fun z hz =>
      hasDerivAt_i12R1_integrand (mul_pos hz.1.1 (sub_pos.mpr hz.1.2)) hz.2.1 hz.2.2)
  obtain ⟨hy, ht, hu⟩ := hz
  have hc : 0 < z.1 * (1 - z.1) := mul_pos hy.1 (sub_pos.mpr hy.2)
  exact (differentiable_i12Wt hc ht hu).mul (differentiable_i12Phi1 (mul_pos hu.1 ht.1)
    (mul_pos (sub_pos.mpr hu.2) hc) (by nlinarith [hu.1, hu.2, ht.1, ht.2]))

end QED.ThreeLoopD
