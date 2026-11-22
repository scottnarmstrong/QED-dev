/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5Bound
public import QED.ThreeLoopD.SetDMastersI8R0

/-!
# Set (d), master `I₅`: the kernel at `ε = 0` as a real double integral

**The angular integral.** For `P, Q > 0`, `1/(P - i Q z) + 1/(P + i Q z) = 2P/(P² + Q² z²)`, so
by the symmetry `z ↦ -z` and the primitive `QED.ThreeLoopD.i8F0` (at `t = 4P²/Q²`),

  `∫₋₁¹ √(1 - z²) / (P - i Q z) dz = π / (P + √(P² + Q²))`
  (`QED.ThreeLoopD.i5_integral_ang`).

**The kernel.** At `ε = 0` the triangle integrand is `U⁻¹ X⁻¹`, `U = 1 + a + c`,
`X = X₁ + c w`, `X₁ = c² + a t`, and `X⁻¹ w⁻¹ = X₁⁻¹ (w⁻¹ - c X⁻¹)`. On shell `w = t - 2i√t z`
and `X = (X₁ + c t) - 2i c √t z`, both of the form `P - i Q z`. The integrand of `K₀` is bounded
by `t⁻¹ i5TriDom t q` (`QED.ThreeLoopD.norm_i5TriF_le`), so Fubini applies, and with
`N₀ = 2/π` (`QED.ThreeLoopD.i5Nrm_zero`)

  `K₀(t) = ∫∫ 2 / (U X₁) · (A(t, 2√t) - c A(X₁ + c t, 2c√t)) da dc`,
  `A(P, Q) = 1 / (P + √(P² + Q²))`

(`QED.ThreeLoopD.i5Ker_zero`, `QED.ThreeLoopD.i5Phi0`).

## Main results

* `QED.ThreeLoopD.i5_integral_ang`, `QED.ThreeLoopD.i5Nrm_zero`.
* `QED.ThreeLoopD.i5Ker_zero`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- `A(P, Q) = 1 / (P + √(P² + Q²))`; `π A(P, Q)` is the angular integral of `1/(P - i Q z)`. -/
noncomputable def i5Ang (P Q : ℝ) : ℝ := 1 / (P + √(P ^ 2 + Q ^ 2))

/-- The integrand of `K₀` after the angular integration:
`2 / (U X₁) · (A(t, 2√t) - c A(X₁ + c t, 2c√t))`. -/
noncomputable def i5Phi0 (t : ℝ) (q : ℝ × ℝ) : ℝ :=
  2 / ((1 + q.1 + q.2) * (q.2 ^ 2 + q.1 * t)) *
    (i5Ang t (2 * √t) - q.2 * i5Ang (q.2 ^ 2 + q.1 * t + q.2 * t) (2 * q.2 * √t))

theorem i5Nrm_zero : i5Nrm 0 = 2 / (Real.pi : ℂ) := by
  have h : i5Nrm 0 = i8Nrm 0 / 2 := by unfold i5Nrm i8Nrm; ring
  rw [h, i8Nrm_zero]
  ring

/-! ### The angular integral -/

theorem i5_ang_ne {P Q z : ℝ} (hP : 0 < P) : (P : ℂ) - ((Q * z : ℝ) : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem i5_ang_mul (P Q z : ℝ) :
    ((P : ℂ) - ((Q * z : ℝ) : ℂ) * I) * ((P : ℂ) - ((Q * -z : ℝ) : ℂ) * I) =
      ((P ^ 2 + Q ^ 2 * z ^ 2 : ℝ) : ℂ) := by
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The even part of `√(1 - z²) / (P - i Q z)`. -/
theorem i5_ang_even {P Q z : ℝ} (hP : 0 < P) :
    ((√(1 - z ^ 2) : ℝ) : ℂ) / ((P : ℂ) - ((Q * z : ℝ) : ℂ) * I) +
        ((√(1 - (-z) ^ 2) : ℝ) : ℂ) / ((P : ℂ) - ((Q * -z : ℝ) : ℂ) * I) =
      ((2 * P * √(1 - z ^ 2) / (P ^ 2 + Q ^ 2 * z ^ 2) : ℝ) : ℂ) := by
  have h1 := i5_ang_ne (Q := Q) (z := z) hP
  have h2 := i5_ang_ne (Q := Q) (z := -z) hP
  have hm := i5_ang_mul P Q z
  have hd : (0 : ℝ) < P ^ 2 + Q ^ 2 * z ^ 2 := by positivity
  rw [neg_sq, div_add_div _ _ h1 h2, hm]
  push_cast
  field_simp
  ring

theorem i8F0_neg_one (t : ℝ) : i8F0 t (-1) = -i8F0 t 1 := by
  unfold i8F0
  simp only [neg_sq, one_pow, mul_one, neg_mul, one_mul, neg_div, Real.arcsin_neg]
  ring

/-- `∫₋₁¹ 2P √(1 - z²) / (P² + Q² z²) dz = 2π / (P + √(P² + Q²))`. -/
theorem i5_integral_ang_re {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) :
    ∫ z in (-1 : ℝ)..1, 2 * P * √(1 - z ^ 2) / (P ^ 2 + Q ^ 2 * z ^ 2) =
      2 * (Real.pi * i5Ang P Q) := by
  set τ := 4 * P ^ 2 / Q ^ 2 with hτ
  have hτ0 : 0 < τ := by positivity
  have hQ2 : (0 : ℝ) < Q ^ 2 := by positivity
  have hd : ∀ z ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun z => 8 * P / Q ^ 2 * i8F0 τ z)
      (2 * P * √(1 - z ^ 2) / (P ^ 2 + Q ^ 2 * z ^ 2)) z := fun z hz => by
    refine ((hasDerivAt_i8F0 hτ0 hz).const_mul (8 * P / Q ^ 2)).congr_deriv ?_
    have : (0 : ℝ) < P ^ 2 + Q ^ 2 * z ^ 2 := by positivity
    rw [hτ]
    field_simp
    ring
  have hc : Continuous fun z : ℝ => 2 * P * √(1 - z ^ 2) / (P ^ 2 + Q ^ 2 * z ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) fun z => (by positivity : (0 : ℝ) <
      P ^ 2 + Q ^ 2 * z ^ 2).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (show Continuous (fun z => 8 * P / Q ^ 2 * i8F0 τ z) from
      continuous_const.mul (continuous_i8F0 hτ0)).continuousOn hd
    (hc.intervalIntegrable _ _)]
  show 8 * P / Q ^ 2 * i8F0 τ 1 - 8 * P / Q ^ 2 * i8F0 τ (-1) = _
  rw [i8F0_neg_one, i8F0_one hτ0]
  set S := √(P ^ 2 + Q ^ 2) with hS
  have hS2 : S ^ 2 = P ^ 2 + Q ^ 2 := Real.sq_sqrt (by positivity)
  have hS0 : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hSP : P < S := by nlinarith
  have hsq : √(τ * (τ + 4)) = 4 * P * S / Q ^ 2 := by
    rw [show τ * (τ + 4) = (4 * P * S / Q ^ 2) ^ 2 by rw [hτ]; field_simp; rw [hS2],
      Real.sqrt_sq (by positivity)]
  rw [hsq, i5Ang, ← hS]
  have hPS : 0 < P + S := by linarith
  field_simp
  rw [hτ]
  field_simp
  nlinarith [hS2]

/-- **The angular integral**: `∫₋₁¹ √(1 - z²) / (P - i Q z) dz = π / (P + √(P² + Q²))`. -/
theorem i5_integral_ang {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) :
    ∫ z in Ioo (-1 : ℝ) 1, ((√(1 - z ^ 2) : ℝ) : ℂ) / ((P : ℂ) - ((Q * z : ℝ) : ℂ) * I) =
      ((Real.pi * i5Ang P Q : ℝ) : ℂ) := by
  set f := fun z : ℝ => ((√(1 - z ^ 2) : ℝ) : ℂ) / ((P : ℂ) - ((Q * z : ℝ) : ℂ) * I) with hf
  have hfc : Continuous f := Continuous.div (by fun_prop) (by fun_prop)
    fun z => i5_ang_ne hP
  have hneg : ∫ z in (-1 : ℝ)..1, f (-z) = ∫ z in (-1 : ℝ)..1, f z := by
    rw [intervalIntegral.integral_comp_neg]; norm_num
  have hsum : (∫ z in (-1 : ℝ)..1, f z) + ∫ z in (-1 : ℝ)..1, f (-z) =
      ((2 * (Real.pi * i5Ang P Q) : ℝ) : ℂ) := by
    have hi2 : IntervalIntegrable (fun z => f (-z)) volume (-1) 1 :=
      (hfc.comp continuous_neg).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add (hfc.intervalIntegrable _ _) hi2]
    simp only [hf]
    rw [intervalIntegral.integral_congr (g := fun z : ℝ =>
      ((2 * P * √(1 - z ^ 2) / (P ^ 2 + Q ^ 2 * z ^ 2) : ℝ) : ℂ)) fun z _ => i5_ang_even hP,
      intervalIntegral.integral_ofReal, i5_integral_ang_re hP hQ]
  rw [hneg] at hsum
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  have h2 : (2 : ℂ) * ∫ z in (-1 : ℝ)..1, f z = 2 * ((Real.pi * i5Ang P Q : ℝ) : ℂ) := by
    rw [two_mul, hsum]; push_cast; ring
  exact mul_left_cancel₀ two_ne_zero h2

/-! ### The kernel at `ε = 0` -/

theorem i5_wt_zero {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - (0 : ℂ)) = ((√(1 - z ^ 2) : ℝ) : ℂ) := by
  have hw : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  rw [sub_zero, Real.sqrt_eq_rpow, ofReal_cpow hw]
  push_cast
  ring_nf

theorem i5TriF_zero (t : ℝ) (w : ℂ) (q : ℝ × ℝ) :
    i5TriF 0 t w q = ((1 + q.1 + q.2 : ℝ) : ℂ)⁻¹ * (i5X t w q)⁻¹ := by
  unfold i5TriF
  simp only [mul_zero, add_zero, sub_zero, cpow_neg_one]

/-- The integrand of `K₀`, as a function of `(z, q)`. -/
noncomputable def i5H0 (t : ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ((1 - p.1 ^ 2 : ℝ) : ℂ) ^ (1 / 2 - (0 : ℂ)) * i5TriF 0 t (i5W t p.1) p.2 / i5W t p.1

theorem measurable_i5H0 (t : ℝ) : Measurable (i5H0 t) := by
  unfold i5H0 i5TriF i5X i5W
  fun_prop

theorem norm_i5H0_le {t : ℝ} (ht : 0 < t) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) : ‖i5H0 t (z, q)‖ ≤ 1 * (1 / t * i5TriDom t q) := by
  have hU : 0 < 1 + q.1 + q.2 := by
    have := hq.1; have := hq.2; simp only [mem_Ioi] at *; linarith
  have hX : 0 < i5X0 t q := by
    have h1 : 0 < q.1 := hq.1
    have h2 : 0 < q.2 := hq.2
    unfold i5X0; positivity
  have h1 : ‖((√(1 - z ^ 2) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_sqrt (by nlinarith : 1 - z ^ 2 ≤ 1)).trans_eq Real.sqrt_one
  have h2 : ‖i5TriF 0 t (i5W t z) q‖ ≤ i5TriDom t q := by
    refine (norm_i5TriF_le (ε := 0) (by simp) ht (re_i5W t z) hq).trans ?_
    simp only [norm_zero, mul_zero, Real.exp_zero, one_mul]
    exact i5_rpow_pair_le hU hX (by simp)
  have hD : 0 ≤ i5TriDom t q := by unfold i5TriDom; positivity
  have h3 := le_norm_i5W t z
  have hw : 0 < ‖i5W t z‖ := ht.trans_le h3
  simp only [i5H0]
  rw [i5_wt_zero hz, norm_div, norm_mul, div_le_iff₀ hw]
  calc _ ≤ 1 * i5TriDom t q := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 * (1 / t * i5TriDom t q) * t := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

theorem integrable_i5H0 {t : ℝ} (ht : 0 < t) :
    Integrable (i5H0 t) ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod
    ((integrableOn_i5TriDom ht).const_mul (1 / t))) (measurable_i5H0 t).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
    (measurableSet_Ioi.prod measurableSet_Ioi))] with p hp
  exact norm_i5H0_le ht hp.1 hp.2

/-- The inner angular integral, for fixed `q = (a, c)`. -/
theorem i5Nrm_mul_integral_i5H0 {t : ℝ} (ht : 0 < t) {q : ℝ × ℝ}
    (hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    i5Nrm 0 * ∫ z in Ioo (-1 : ℝ) 1, i5H0 t (z, q) = (i5Phi0 t q : ℂ) := by
  obtain ⟨a, c⟩ := q
  have ha : 0 < a := hq.1
  have hc : 0 < c := hq.2
  have hst : 0 < √t := Real.sqrt_pos.mpr ht
  set X₁ := c ^ 2 + a * t with hX₁
  have hX₁0 : 0 < X₁ := by positivity
  have hU : 0 < 1 + a + c := by linarith
  have hP₂ : 0 < X₁ + c * t := by positivity
  have hQ₁ : 0 < 2 * √t := by positivity
  have hQ₂ : 0 < 2 * c * √t := by positivity
  set f₁ := fun z : ℝ => ((√(1 - z ^ 2) : ℝ) : ℂ) / ((t : ℂ) - ((2 * √t * z : ℝ) : ℂ) * I)
  set f₂ := fun z : ℝ => ((√(1 - z ^ 2) : ℝ) : ℂ) /
    (((X₁ + c * t : ℝ) : ℂ) - ((2 * c * √t * z : ℝ) : ℂ) * I)
  have hf₁ : Continuous f₁ := Continuous.div (by fun_prop) (by fun_prop) fun z => i5_ang_ne ht
  have hf₂ : Continuous f₂ := Continuous.div (by fun_prop) (by fun_prop) fun z => i5_ang_ne hP₂
  have hpt : ∀ z ∈ Ioo (-1 : ℝ) 1, i5H0 t (z, (a, c)) =
      ((1 + a + c : ℝ) : ℂ)⁻¹ * (X₁ : ℂ)⁻¹ * (f₁ z - c * f₂ z) := fun z hz => by
    have hw : i5W t z = (t : ℂ) - ((2 * √t * z : ℝ) : ℂ) * I := by
      unfold i5W; push_cast; ring
    have hX : i5X t (i5W t z) (a, c) =
        ((X₁ + c * t : ℝ) : ℂ) - ((2 * c * √t * z : ℝ) : ℂ) * I := by
      unfold i5X; rw [hw, hX₁]; push_cast; ring
    have hw0 := i5_ang_ne (Q := 2 * √t) (z := z) ht
    have hX0 := i5_ang_ne (Q := 2 * c * √t) (z := z) hP₂
    have hXw : ((X₁ + c * t : ℝ) : ℂ) - ((2 * c * √t * z : ℝ) : ℂ) * I =
        (X₁ : ℂ) + c * ((t : ℂ) - ((2 * √t * z : ℝ) : ℂ) * I) := by push_cast; ring
    simp only [i5H0, f₁, f₂]
    rw [i5_wt_zero hz, i5TriF_zero, hX, hw]
    rw [hXw] at hX0 ⊢
    have hX₁c : (X₁ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX₁0.ne'
    have hUc : ((1 + a + c : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hU.ne'
    generalize (t : ℂ) - ((2 * √t * z : ℝ) : ℂ) * I = w at hw0 hX0 ⊢
    field_simp
    ring
  have hi : ∀ f : ℝ → ℂ, Continuous f → IntegrableOn f (Ioo (-1 : ℝ) 1) := fun f hf =>
    (hf.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul,
    integral_sub (hi _ hf₁) ((hi _ hf₂).const_mul _), integral_const_mul]
  simp only [f₁, f₂]
  rw [i5_integral_ang ht hQ₁, i5_integral_ang hP₂ hQ₂, i5Nrm_zero]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  unfold i5Phi0
  rw [← hX₁]
  push_cast
  field_simp

/-- **The kernel at `ε = 0`** as a real double integral over `(a, c)`. -/
theorem i5Ker_zero {t : ℝ} (ht : 0 < t) :
    i5Ker 0 t = ((∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5Phi0 t q : ℝ) : ℂ) := by
  have hin : ∀ z : ℝ, ((1 - z ^ 2 : ℝ) : ℂ) ^ (1 / 2 - (0 : ℂ)) * i5Tri 0 t (i5W t z) /
      i5W t z = ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), i5H0 t (z, q) := fun z => by
    rw [i5Tri_eq, ← integral_const_mul, ← integral_div]
    rfl
  unfold i5Ker
  simp_rw [hin]
  rw [integral_integral_swap (f := fun z q => i5H0 t (z, q)) (integrable_i5H0 ht),
    ← integral_const_mul,
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi)
      fun q hq => i5Nrm_mul_integral_i5H0 ht hq, integral_complex_ofReal]

end QED.ThreeLoopD
