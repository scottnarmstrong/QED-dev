/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R1Xi

/-!
# Set (d), master `I₈`: the coefficient `c₁ = 39/4 - π²/6` of `Rem`

With `c = 1 - 2 log 2`, the first coefficients of the integrands of `Rem`
(`QED.ThreeLoopD.i8R1C_one`, `QED.ThreeLoopD.i8AsymC_one`) split as

  `D¹ h₁ = p + c (1 - ξ) + (4/π) t J₁` on `(0, 1)`,
  `D¹ h₁ - D¹ Asym = (p - a) + c (1/t - ξ) + (4/π) (t J₁ + m₀ - 4 m₂/t)` on `(1, ∞)`,

with `p, a` the bubble part (`QED.ThreeLoopD.i8_integral_P1`,
`QED.ThreeLoopD.i8_integral_P1_sub`: total `43/4 - π²/3`), the term `c (1 - ξ)` as at order zero
(total `3c/2`), and the angular part (`QED.ThreeLoopD.i8_integral_tJ1r`: total
`-5/2 + 3 log 2 + π²/6` after the factor `4/π`). Hence `c₁ = 39/4 - π²/6`.

## Main results

* `QED.ThreeLoopD.i8RemCoeff_one : i8RemCoeff 1 = -π²/6 + 39/4`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopD

/-! ### Integrability of the pointwise coefficients -/

theorem integrableOn_i8Dsl_remInt1 (k : ℕ) :
    IntegrableOn (fun t => i13Dsl (i8RemInt1 t) k 0) (Ioo (0 : ℝ) 1) := by
  obtain ⟨CN, hN⟩ := i8Nrm_bound
  exact integrable_i13Dsl_zero (μ := volume.restrict (Ioo (0 : ℝ) 1)) (h := i8RemInt1)
    (R := 1 / 5) (ρ := 1 / 10) (M := fun t => 4 * CN * t ^ (-(1 : ℝ) / 10)) (by norm_num)
    (by norm_num) ((integrableOn_rpow_Ioo (by norm_num)).const_mul (4 * CN))
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => differentiableOn_i8RemInt1 ht.1)
    (fun ε _ => (measurable_i8RemInt1 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ε hε =>
      norm_i8RemInt1_le hN ht hε.le) k

theorem integrableOn_i8Dsl_remInt2 (k : ℕ) :
    IntegrableOn (fun t => i13Dsl (i8RemInt2 t) k 0) (Ioi (1 : ℝ)) := by
  obtain ⟨K, hK⟩ := norm_i8RemInt2_le
  exact integrable_i13Dsl_zero (μ := volume.restrict (Ioi (1 : ℝ))) (h := i8RemInt2)
    (R := 1 / 5) (ρ := 1 / 10) (M := fun t => K * t ^ ((3 : ℝ) / 10 - 2))
    (by norm_num) (by norm_num)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul K)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      differentiableOn_i8RemInt2 (zero_lt_one.trans ht))
    (fun ε _ => (measurable_i8RemInt2 ε).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ε hε =>
      hK ε hε.le t (le_of_lt ht)) k

/-! ### The first coefficients as real functions -/

/-- `D¹ h₁(t) = (1 - ξ)(-log t + 2β₁ + 1 - 2 log 2) + t (4/π) J₁(t)`. -/
noncomputable def i8Q1 (t : ℝ) : ℝ :=
  (1 - i13Xi t) * (-Real.log t + 2 * i13Be1r t + (1 - 2 * Real.log 2)) +
    t * (4 / Real.pi) * i8J1r t

/-- `D¹ Asym(t) = 4 - 3 log t + (-17/2 - log t)/t`. -/
noncomputable def i8AQ1 (t : ℝ) : ℝ := 4 - 3 * Real.log t + (-17 / 2 - Real.log t) / t

theorem i8Dsl_remInt1_one {t : ℝ} (ht : 0 < t) :
    i13Dsl (i8RemInt1 t) 1 0 = (i8Q1 t : ℂ) := by
  rw [(i8Jet_remInt1 ht).dsl_eq, i8R1C_one ht, i8Q1]

theorem i8Dsl_remInt2_one {t : ℝ} (ht : 0 < t) :
    i13Dsl (i8RemInt2 t) 1 0 = ((i8Q1 t - i8AQ1 t : ℝ) : ℂ) := by
  rw [(i8Jet_remInt2 ht).dsl_eq, i8R1C_one ht, i8AsymC_one ht, i8Q1, i8AQ1]
  push_cast
  ring

theorem integrableOn_i8Q1 : IntegrableOn i8Q1 (Ioo (0 : ℝ) 1) := by
  have h := (integrableOn_i8Dsl_remInt1 1).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp [i8Dsl_remInt1_one ht.1]

theorem integrableOn_i8Q1_sub : IntegrableOn (fun t => i8Q1 t - i8AQ1 t) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_i8Dsl_remInt2 1).re
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [i8Dsl_remInt2_one (zero_lt_one.trans ht)]
  simp

/-! ### The splitting -/

theorem integrableOn_i8_inv_sub_xi : IntegrableOn (fun t => 1 / t - i13Xi t) (Ioi (1 : ℝ)) := by
  have hd : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun t => Real.log t - i8P0 t) (1 / t - i13Xi t) t :=
    fun t ht => by
      have ht' : (1 : ℝ) < t := ht
      have h := (Real.hasDerivAt_log (by linarith : t ≠ 0)).sub
        (hasDerivAt_i8P0 (by linarith : (0 : ℝ) < t))
      rw [one_div]; exact h
  exact integrableOn_Ioi_deriv_of_nonneg
    (((Real.hasDerivAt_log one_ne_zero).sub (hasDerivAt_i8P0 one_pos)).continuousAt
      |>.continuousWithinAt) hd
    (fun t (ht : 1 < t) => by linarith [i13Xi_le_inv (by linarith : (0 : ℝ) < t)])
    tendsto_i8_log_sub_P0

theorem i8Q1_eq (t : ℝ) : i8Q1 t = i8P1 t + (1 - 2 * Real.log 2) * (1 - i13Xi t) +
    4 / Real.pi * (t * i8J1r t) := by
  unfold i8Q1 i8P1; ring

theorem i8Q1_sub_eq {t : ℝ} (ht : 0 < t) : i8Q1 t - i8AQ1 t = (i8P1 t - i8A1r t) +
    (1 - 2 * Real.log 2) * (1 / t - i13Xi t) + 4 / Real.pi * (t * i8J1r t -
      (-(Real.pi / 4 * (1 - 2 * Real.log 2)) + Real.pi * (1 / 8 - Real.log 2 / 2) / t)) := by
  have hpi := Real.pi_pos.ne'
  unfold i8Q1 i8P1 i8AQ1 i8A1r
  field_simp
  ring

/-- The real form of `c₁`. -/
theorem i8_integral_Q1_total :
    (∫ t in Ioo (0 : ℝ) 1, i8Q1 t) + ∫ t in Ioi (1 : ℝ), (i8Q1 t - i8AQ1 t) =
      39 / 4 - Real.pi ^ 2 / 6 := by
  have iX0 : IntegrableOn (fun t => (1 - 2 * Real.log 2) * (1 - i13Xi t)) (Ioo (0 : ℝ) 1) :=
    (continuous_const.mul (continuous_const.sub continuous_i13Xi)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have iJ0 : IntegrableOn (fun t => 4 / Real.pi * (t * i8J1r t)) (Ioo (0 : ℝ) 1) :=
    integrableOn_i8_tJ1r.const_mul _
  have iP0 : IntegrableOn i8P1 (Ioo (0 : ℝ) 1) := by
    refine ((integrableOn_i8Q1.sub iX0).sub iJ0).congr_fun (fun t _ => ?_) measurableSet_Ioo
    simp only [Pi.sub_apply, i8Q1_eq]; ring
  have iX1 : IntegrableOn (fun t => (1 - 2 * Real.log 2) * (1 / t - i13Xi t)) (Ioi (1 : ℝ)) :=
    integrableOn_i8_inv_sub_xi.const_mul _
  have iJ1 := integrableOn_i8_tJ1r_sub.const_mul (4 / Real.pi)
  have iP1 : IntegrableOn (fun t => i8P1 t - i8A1r t) (Ioi (1 : ℝ)) := by
    refine ((integrableOn_i8Q1_sub.sub iX1).sub iJ1).congr_fun (fun t (ht : 1 < t) => ?_)
      measurableSet_Ioi
    simp only [Pi.sub_apply, i8Q1_sub_eq (zero_lt_one.trans ht)]; ring
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t _ => i8Q1_eq t),
    setIntegral_congr_fun measurableSet_Ioi (fun t (ht : 1 < t) =>
      i8Q1_sub_eq (zero_lt_one.trans ht)),
    integral_add (f := fun t => i8P1 t + (1 - 2 * Real.log 2) * (1 - i13Xi t))
      (g := fun t => 4 / Real.pi * (t * i8J1r t)) (by exact iP0.add iX0) iJ0,
    integral_add (f := i8P1) (g := fun t => (1 - 2 * Real.log 2) * (1 - i13Xi t)) iP0 iX0,
    integral_add (f := fun t => i8P1 t - i8A1r t + (1 - 2 * Real.log 2) * (1 / t - i13Xi t))
      (by exact iP1.add iX1) iJ1,
    integral_add (f := fun t => i8P1 t - i8A1r t)
      (g := fun t => (1 - 2 * Real.log 2) * (1 / t - i13Xi t)) iP1 iX1,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, i8_integral_P1 iP0, i8_integral_P1_sub iP1, integral_i8_one_sub_xi,
    integral_i8_inv_sub_xi]
  have h := i8_integral_tJ1r
  have hpi := Real.pi_pos.ne'
  calc _ = 43 / 4 - π ^ 2 / 3 + (1 - 2 * Real.log 2) * (3 / 2) +
      4 / π * ((∫ t in Ioo (0 : ℝ) 1, t * i8J1r t) +
        ∫ t in Ioi (1 : ℝ), (t * i8J1r t - (-(π / 4 * (1 - 2 * Real.log 2)) +
          π * (1 / 8 - Real.log 2 / 2) / t))) := by ring
    _ = 39 / 4 - π ^ 2 / 6 := by
        rw [h]; field_simp; ring

/-- **The coefficient `c₁ = 39/4 - π²/6`.** -/
theorem i8RemCoeff_one : i8RemCoeff 1 = -1 / 6 * (π : ℂ) ^ 2 + 39 / 4 := by
  unfold i8RemCoeff
  rw [setIntegral_congr_fun measurableSet_Ioo fun t ht => i8Dsl_remInt1_one ht.1,
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i8Dsl_remInt2_one (zero_lt_one.trans ht),
    integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_add,
    i8_integral_Q1_total]
  push_cast
  ring

end QED.ThreeLoopD
