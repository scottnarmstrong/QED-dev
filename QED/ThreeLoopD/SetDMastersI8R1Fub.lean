/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R1Mom

/-!
# Set (d), master `I₈`: the angular part of `c₁`, by Fubini

With `φ(z) = √(1 - z²) log (1 - z²)` (`|φ| ≤ 2`), the first coefficient of `J_ε(t)` satisfies
`t J₁(t) = -∫₀¹ φ(z) t/(t + 4z²) dz`, and at large `t`, `t J₁(t) = -m₀ + 4 m₂/t + O(t⁻²)` with
`m₀ = ∫₀¹ φ`, `m₂ = ∫₀¹ φ z²`. Exchanging the order of integration,

  `∫₀¹ t/(t + 4z²) dt = 1 - 4z² (log (1 + 4z²) - log (4z²))`,
  `∫₁^∞ (t/(t + 4z²) - 1 + 4z²/t) dt = ∫₁^∞ 16z⁴/(t (t + 4z²)) dt = 4z² log (1 + 4z²)`,

so the two pieces add up to `-∫₀¹ φ(z) (1 + 4z² log (4z²)) dz = -(m₀ + 8 m₂ log 2 + 8 X)`,
`X = ∫₀¹ φ z² log z` (`QED.ThreeLoopD.i8_integral_wLz2log`):

  `∫₀¹ t J₁ + ∫₁^∞ (t J₁ + m₀ - 4 m₂/t) = -π (5/8 - 3 log 2/4) + π³/24`

(`QED.ThreeLoopD.i8_integral_tJ1r`).

## Main results

* `QED.ThreeLoopD.integrableOn_i8_tJ1r`, `QED.ThreeLoopD.integrableOn_i8_tJ1r_sub`.
* `QED.ThreeLoopD.i8_integral_tJ1r`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Function

namespace QED.ThreeLoopD

/-- `φ(z) = √(1 - z²) log (1 - z²)`. -/
noncomputable def i8Phi (z : ℝ) : ℝ := √(1 - z ^ 2) * Real.log (1 - z ^ 2)

theorem measurable_i8Phi : Measurable i8Phi := by unfold i8Phi; fun_prop

theorem abs_i8Phi_le {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : |i8Phi z| ≤ 2 :=
  i8_abs_sqrt_mul_log_le (i8_one_sub_sq_pos hz) (by nlinarith)

theorem i8_t_mul_J1r {t : ℝ} (ht : 0 < t) :
    t * i8J1r t = ∫ z in Ioo (0 : ℝ) 1, -(i8Phi z * (t / (t + 4 * z ^ 2))) := by
  unfold i8J1r
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun z _ => ?_
  have := i8_den_pos ht z
  unfold i8Phi
  field_simp

/-! ### The inner integrals -/

theorem i8_integral_t_div {z : ℝ} (hz : 0 < z) :
    ∫ t in Ioo (0 : ℝ) 1, t / (t + 4 * z ^ 2) =
      1 - 4 * z ^ 2 * (Real.log (1 + 4 * z ^ 2) - Real.log (4 * z ^ 2)) := by
  have hq : ∀ t : ℝ, 0 ≤ t → 0 < t + 4 * z ^ 2 := fun t ht => by positivity
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => t - 4 * z ^ 2 * Real.log (t + 4 * z ^ 2))
      (t / (t + 4 * z ^ 2)) t := fun t ht => by
    have h : HasDerivAt (fun t => t - 4 * z ^ 2 * Real.log (t + 4 * z ^ 2))
        (1 - 4 * z ^ 2 * (1 / (t + 4 * z ^ 2))) t :=
      (hasDerivAt_id' t).sub ((((hasDerivAt_id' t).add_const (4 * z ^ 2)).log
        (hq t ht.1.le).ne').const_mul (4 * z ^ 2))
    refine h.congr_deriv ?_
    have := hq t ht.1.le
    field_simp
    ring
  have hc : ContinuousOn (fun t => t - 4 * z ^ 2 * Real.log (t + 4 * z ^ 2)) (Icc 0 1) :=
    continuousOn_id.sub (continuousOn_const.mul
      (ContinuousOn.log (by fun_prop) fun t ht => (hq t ht.1).ne'))
  have hi : IntervalIntegrable (fun t => t / (t + 4 * z ^ 2)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one
      (ContinuousOn.div continuousOn_id (by fun_prop) fun t ht => (hq t ht.1).ne')
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hd hi]
  simp only [zero_add]
  ring_nf

theorem i8_tail_eq {z t : ℝ} (ht : 0 < t) :
    16 * z ^ 4 / (t * (t + 4 * z ^ 2)) = t / (t + 4 * z ^ 2) - 1 + 4 * z ^ 2 / t := by
  have := i8_den_pos ht z
  field_simp
  ring

theorem i8_integral_t_tail {z : ℝ} (hz : 0 < z) :
    ∫ t in Ioi (1 : ℝ), 16 * z ^ 4 / (t * (t + 4 * z ^ 2)) =
      4 * z ^ 2 * Real.log (1 + 4 * z ^ 2) := by
  have hq : ∀ t : ℝ, 0 < t → 0 < t + 4 * z ^ 2 := fun t ht => i8_den_pos ht z
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => 4 * z ^ 2 * (Real.log t -
      Real.log (t + 4 * z ^ 2))) (16 * z ^ 4 / (t * (t + 4 * z ^ 2))) t := fun t ht => by
    have h : HasDerivAt (fun t => 4 * z ^ 2 * (Real.log t - Real.log (t + 4 * z ^ 2)))
        (4 * z ^ 2 * (t⁻¹ - 1 / (t + 4 * z ^ 2))) t :=
      ((Real.hasDerivAt_log ht.ne').sub (((hasDerivAt_id' t).add_const (4 * z ^ 2)).log
        (hq t ht).ne')).const_mul (4 * z ^ 2)
    refine h.congr_deriv ?_
    have := hq t ht
    field_simp
    ring
  have hlim : Tendsto (fun t => 4 * z ^ 2 * (Real.log t - Real.log (t + 4 * z ^ 2))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 1 + 4 * z ^ 2 * t⁻¹) atTop (𝓝 1) := by
      have := (tendsto_inv_atTop_zero.const_mul (4 * z ^ 2)).const_add 1
      rwa [mul_zero, add_zero] at this
    have h2 := (h1.log one_ne_zero).const_mul (4 * z ^ 2)
    rw [Real.log_one, mul_zero] at h2
    refine (h2.neg.congr' ?_).trans (by simp)
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [show t + 4 * z ^ 2 = t * (1 + 4 * z ^ 2 * t⁻¹) by field_simp,
      Real.log_mul ht.ne' (by positivity)]
    ring
  rw [integral_Ioi_of_hasDerivAt_of_nonneg ((hd 1 one_pos).continuousAt.continuousWithinAt)
    (fun t ht => hd t (zero_lt_one.trans ht)) (fun t ht => by
      have := hq t (zero_lt_one.trans ht); have : (0 : ℝ) < t := zero_lt_one.trans ht
      positivity) hlim]
  simp

/-! ### Fubini -/

theorem i8_ae_prod_mem {s u : Set ℝ} (hs : MeasurableSet s) (hu : MeasurableSet u) :
    ∀ᵐ p ∂((volume.restrict s).prod (volume.restrict u)), p ∈ s ×ˢ u := by
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (hs.prod hu)

theorem i8_integrable_f1 : Integrable (uncurry fun t z => i8Phi z * (t / (t + 4 * z ^ 2)))
    ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  refine Integrable.mono' (integrable_const 2)
    (((measurable_i8Phi.comp measurable_snd).mul (by fun_prop) : Measurable fun p : ℝ × ℝ =>
      i8Phi p.2 * (p.1 / (p.1 + 4 * p.2 ^ 2)))).aestronglyMeasurable ?_
  filter_upwards [i8_ae_prod_mem measurableSet_Ioo measurableSet_Ioo] with p hp
  have hz := hp.2
  have ht := hp.1.1
  have hq := i8_den_pos ht p.2
  simp only [uncurry, Real.norm_eq_abs, abs_mul]
  calc |i8Phi p.2| * |p.1 / (p.1 + 4 * p.2 ^ 2)| ≤ 2 * 1 := by
        refine mul_le_mul (abs_i8Phi_le hz) ?_ (abs_nonneg _) (by norm_num)
        rw [abs_of_pos (div_pos ht hq), div_le_one hq]
        nlinarith
    _ = 2 := by norm_num

theorem i8_integrable_f2 :
    Integrable (uncurry fun t z => i8Phi z * (16 * z ^ 4 / (t * (t + 4 * z ^ 2))))
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hb : Integrable (fun p : ℝ × ℝ => 32 * p.1 ^ (-2 : ℝ) * (1 : ℝ))
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    Integrable.mul_prod (f := fun t : ℝ => 32 * t ^ (-2 : ℝ)) (g := fun _ : ℝ => (1 : ℝ))
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 32) (integrable_const 1)
  refine Integrable.mono' hb
    (((measurable_i8Phi.comp measurable_snd).mul (by fun_prop) : Measurable fun p : ℝ × ℝ =>
      i8Phi p.2 * (16 * p.2 ^ 4 / (p.1 * (p.1 + 4 * p.2 ^ 2))))).aestronglyMeasurable ?_
  filter_upwards [i8_ae_prod_mem measurableSet_Ioi measurableSet_Ioo] with p hp
  have hz := hp.2
  have ht : (1 : ℝ) < p.1 := hp.1
  have ht0 : (0 : ℝ) < p.1 := by linarith
  have hq := i8_den_pos ht0 p.2
  have hz4 : p.2 ^ 4 ≤ 1 := pow_le_one₀ hz.1.le hz.2.le
  have hp2 : p.1 ^ (-2 : ℝ) = (p.1 ^ 2)⁻¹ := by
    rw [Real.rpow_neg ht0.le]; norm_cast
  simp only [uncurry, Real.norm_eq_abs, abs_mul, mul_one, hp2]
  calc |i8Phi p.2| * |16 * p.2 ^ 4 / (p.1 * (p.1 + 4 * p.2 ^ 2))| ≤ 2 * (16 * (p.1 ^ 2)⁻¹) := by
        refine mul_le_mul (abs_i8Phi_le hz) ?_ (abs_nonneg _) (by norm_num)
        rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
        have : p.1 ^ 2 ≤ p.1 * (p.1 + 4 * p.2 ^ 2) := by nlinarith [sq_nonneg p.2]
        calc 16 * p.2 ^ 4 ≤ 16 := by linarith
          _ = 16 * (p.1 ^ 2)⁻¹ * p.1 ^ 2 := by field_simp
          _ ≤ 16 * (p.1 ^ 2)⁻¹ * (p.1 * (p.1 + 4 * p.2 ^ 2)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
    _ = 32 * (p.1 ^ 2)⁻¹ := by ring

/-! ### The angular part of `c₁` -/

theorem integrableOn_i8_tJ1r : IntegrableOn (fun t => t * i8J1r t) (Ioo (0 : ℝ) 1) := by
  refine i8_integrable_f1.integral_prod_left.neg.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simp only [Pi.neg_apply, uncurry]
  rw [i8_t_mul_J1r ht.1, integral_neg]

theorem i8_bdd_Phi_mul {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ z ∈ Ioo (0 : ℝ) 1, |g z| ≤ C) :
    IntegrableOn (fun z => i8Phi z * g z) (Ioo (0 : ℝ) 1) :=
  i8_integrableOn_bdd (measurable_i8Phi.mul hg) (C := 2 * C) fun z hz => by
    rw [abs_mul]
    exact mul_le_mul (abs_i8Phi_le hz) (hC z hz) (abs_nonneg _) (by norm_num)

theorem i8_tJ1r_sub_eq {t : ℝ} (ht : 0 < t) :
    t * i8J1r t - (-(Real.pi / 4 * (1 - 2 * Real.log 2)) +
      Real.pi * (1 / 8 - Real.log 2 / 2) / t) =
      -∫ z in Ioo (0 : ℝ) 1, i8Phi z * (16 * z ^ 4 / (t * (t + 4 * z ^ 2))) := by
  have i1 := i8_bdd_Phi_mul (g := fun z => t / (t + 4 * z ^ 2)) (by fun_prop) (C := 1)
    fun z hz => by
      have hq := i8_den_pos ht z
      rw [abs_of_pos (div_pos ht hq), div_le_one hq]; nlinarith
  have i2 := i8_bdd_Phi_mul (g := fun _ => (1 : ℝ)) measurable_const (C := 1) fun _ _ => by simp
  have i3 := i8_bdd_Phi_mul (g := fun z => z ^ 2) (by fun_prop) (C := 1) fun z hz => by
    rw [abs_of_nonneg (by positivity)]; nlinarith [hz.1, hz.2]
  have hm0 := i8_integral_wL
  have hm2 := i8_integral_wLz2
  rw [show (fun z => √(1 - z ^ 2) * Real.log (1 - z ^ 2)) = fun z => i8Phi z * 1 by
    funext z; unfold i8Phi; ring] at hm0
  rw [show (fun z => √(1 - z ^ 2) * Real.log (1 - z ^ 2) * z ^ 2) = fun z => i8Phi z * z ^ 2 by
    funext z; unfold i8Phi; ring] at hm2
  rw [i8_t_mul_J1r ht, integral_neg, setIntegral_congr_fun measurableSet_Ioo
    (f := fun z => i8Phi z * (16 * z ^ 4 / (t * (t + 4 * z ^ 2))))
    (g := fun z => i8Phi z * (t / (t + 4 * z ^ 2)) - i8Phi z * 1 + 4 / t * (i8Phi z * z ^ 2))
    fun z _ => by simp only; rw [i8_tail_eq ht]; ring,
    integral_add (f := fun z => i8Phi z * (t / (t + 4 * z ^ 2)) - i8Phi z * 1)
      (g := fun z => 4 / t * (i8Phi z * z ^ 2)) (by exact i1.sub i2) (i3.const_mul _),
    integral_sub (f := fun z => i8Phi z * (t / (t + 4 * z ^ 2))) (g := fun z => i8Phi z * 1)
      i1 i2, integral_const_mul, hm0, hm2]
  ring

theorem integrableOn_i8_tJ1r_sub : IntegrableOn (fun t => t * i8J1r t -
    (-(Real.pi / 4 * (1 - 2 * Real.log 2)) + Real.pi * (1 / 8 - Real.log 2 / 2) / t))
    (Ioi (1 : ℝ)) := by
  refine i8_integrable_f2.integral_prod_left.neg.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 1 < t)
  simp only [Pi.neg_apply, uncurry]
  rw [i8_tJ1r_sub_eq (zero_lt_one.trans ht)]

/-- **The angular part of `c₁`**. -/
theorem i8_integral_tJ1r :
    (∫ t in Ioo (0 : ℝ) 1, t * i8J1r t) + ∫ t in Ioi (1 : ℝ), (t * i8J1r t -
      (-(Real.pi / 4 * (1 - 2 * Real.log 2)) + Real.pi * (1 / 8 - Real.log 2 / 2) / t)) =
      -Real.pi * (5 / 8 - 3 * Real.log 2 / 4) + Real.pi ^ 3 / 24 := by
  have e1 : ∫ t in Ioo (0 : ℝ) 1, t * i8J1r t =
      -∫ z in Ioo (0 : ℝ) 1, i8Phi z * (1 - 4 * z ^ 2 *
        (Real.log (1 + 4 * z ^ 2) - Real.log (4 * z ^ 2))) := by
    rw [setIntegral_congr_fun measurableSet_Ioo (f := fun t => t * i8J1r t)
      (g := fun t => -∫ z in Ioo (0 : ℝ) 1, i8Phi z * (t / (t + 4 * z ^ 2)))
      (fun t ht => by beta_reduce; rw [i8_t_mul_J1r ht.1, integral_neg]), integral_neg,
      integral_integral_swap i8_integrable_f1]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
    rw [integral_const_mul, i8_integral_t_div hz.1]
  have e2 : ∫ t in Ioi (1 : ℝ), (t * i8J1r t -
      (-(Real.pi / 4 * (1 - 2 * Real.log 2)) + Real.pi * (1 / 8 - Real.log 2 / 2) / t)) =
      -∫ z in Ioo (0 : ℝ) 1, i8Phi z * (4 * z ^ 2 * Real.log (1 + 4 * z ^ 2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) =>
      i8_tJ1r_sub_eq (zero_lt_one.trans ht), integral_neg,
      integral_integral_swap i8_integrable_f2]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
    rw [integral_const_mul, i8_integral_t_tail hz.1]
  have j1 := i8_integrable_f1.integral_prod_right
  have j2 := i8_integrable_f2.integral_prod_right
  have k1 : IntegrableOn (fun z => i8Phi z * (1 - 4 * z ^ 2 *
      (Real.log (1 + 4 * z ^ 2) - Real.log (4 * z ^ 2)))) (Ioo (0 : ℝ) 1) :=
    j1.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      simp only [uncurry]; rw [integral_const_mul, i8_integral_t_div hz.1])
  have k2 : IntegrableOn (fun z => i8Phi z * (4 * z ^ 2 * Real.log (1 + 4 * z ^ 2)))
      (Ioo (0 : ℝ) 1) :=
    j2.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      simp only [uncurry]; rw [integral_const_mul, i8_integral_t_tail hz.1])
  have i2 := i8_bdd_Phi_mul (g := fun _ => (1 : ℝ)) measurable_const (C := 1) fun _ _ => by simp
  have i3 := i8_bdd_Phi_mul (g := fun z => z ^ 2) (by fun_prop) (C := 1) fun z hz => by
    rw [abs_of_nonneg (by positivity)]; nlinarith [hz.1, hz.2]
  have i4 := i8_bdd_Phi_mul (g := fun z => z ^ 2 * Real.log z) (by fun_prop) (C := 1)
    fun z hz => by
      have h := Real.abs_log_mul_self_lt z hz.1 hz.2.le
      rw [show z ^ 2 * Real.log z = z * (Real.log z * z) by ring, abs_mul,
        abs_of_pos hz.1]
      nlinarith [abs_nonneg (Real.log z * z), hz.2]
  have hm0 := i8_integral_wL
  have hm2 := i8_integral_wLz2
  have hX := i8_integral_wLz2log
  rw [show (fun z => √(1 - z ^ 2) * Real.log (1 - z ^ 2)) = fun z => i8Phi z * 1 by
    funext z; unfold i8Phi; ring] at hm0
  rw [show (fun z => √(1 - z ^ 2) * Real.log (1 - z ^ 2) * z ^ 2) = fun z => i8Phi z * z ^ 2 by
    funext z; unfold i8Phi; ring] at hm2
  rw [show (fun z => √(1 - z ^ 2) * Real.log (1 - z ^ 2) * z ^ 2 * Real.log z) =
    fun z => i8Phi z * (z ^ 2 * Real.log z) by funext z; unfold i8Phi; ring] at hX
  rw [e1, e2, ← neg_add, ← integral_add k1 k2, setIntegral_congr_fun measurableSet_Ioo
    (g := fun z => (i8Phi z * 1 + 8 * Real.log 2 * (i8Phi z * z ^ 2)) +
      8 * (i8Phi z * (z ^ 2 * Real.log z))) fun z hz => by
      have hz0 := hz.1
      simp only
      rw [show (4 : ℝ) * z ^ 2 = 2 ^ 2 * z ^ 2 by norm_num, Real.log_mul (by positivity)
        (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      ring,
    integral_add (f := fun z => i8Phi z * 1 + 8 * Real.log 2 * (i8Phi z * z ^ 2))
      (g := fun z => 8 * (i8Phi z * (z ^ 2 * Real.log z))) (by exact i2.add (i3.const_mul _))
      (i4.const_mul _),
    integral_add (f := fun z => i8Phi z * 1) (g := fun z => 8 * Real.log 2 * (i8Phi z * z ^ 2))
      i2 (i3.const_mul _),
    integral_const_mul, integral_const_mul, hm0, hm2, hX]
  ring

end QED.ThreeLoopD
