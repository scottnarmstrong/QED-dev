/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R1
public import QED.ThreeLoopD.SetDMastersI13R3

/-!
# Set (d), master `I₈`: the differential equation of the angular coefficients

The weight coefficients `wₖ(z) = √(1 - z²) (-log (1 - z²))ᵏ / k!` (`QED.ThreeLoopD.i8Wr`) obey
`(1 - z²) wₖ' = -z wₖ + 2z wₖ₋₁` (`w₋₁ = 0`). With `D = t + 4z²` and
`G(z) = z (1 - z²) wₖ(z) / D`, which vanishes at `z = 0` and `z = 1`, the pointwise identity
`-t (t + 4) wₖ / D² = -2 wₖ / D - t wₖ₋₁ / D - (wₖ - wₖ₋₁) - 2 G'` integrates to

  `t (t + 4) Jₖ' = -2 Jₖ - t Jₖ₋₁ - (mₖ - mₖ₋₁)`,

`Jₖ(t) = ∫₀¹ wₖ / D`, `mₖ = ∫₀¹ wₖ` (`QED.ThreeLoopD.hasDerivAt_i8Jr`).

## Main results

* `QED.ThreeLoopD.abs_i8Wr_le`: `|wₖ| ≤ 2ᵏ`.
* `QED.ThreeLoopD.hasDerivAt_i8Jr`: the differential equation of `Jₖ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped Nat

namespace QED.ThreeLoopD

/-- The real weight coefficient `wₖ(z) = √(1 - z²) (-log (1 - z²))ᵏ / k!`. -/
noncomputable def i8Wr (k : ℕ) (z : ℝ) : ℝ := √(1 - z ^ 2) * ((-Real.log (1 - z ^ 2)) ^ k / k !)

/-- The previous weight coefficient `wₖ₋₁`, with `w₋₁ = 0`. -/
noncomputable def i8Wp : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, z => i8Wr k z

theorem i8WC_eq (z : ℝ) (k : ℕ) : i8WC z k = (i8Wr k z : ℂ) := by
  unfold i8WC i8Wr
  push_cast
  ring

theorem measurable_i8Wr (k : ℕ) : Measurable (i8Wr k) := by
  unfold i8Wr; fun_prop

theorem measurable_i8Wp (k : ℕ) : Measurable (i8Wp k) := by
  cases k with
  | zero => exact measurable_const
  | succ k => exact measurable_i8Wr k

theorem i8_sqrt_mul_exp {u : ℝ} (hu : 0 < u) : √u * Real.exp (-Real.log u / 2) = 1 := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu, ← Real.exp_add]
  ring_nf
  exact Real.exp_zero

/-- `|wₖ(z)| ≤ 2ᵏ`, from `(L/2)ᵏ/k! ≤ e^(L/2) = (1 - z²)^(-1/2)`. -/
theorem abs_i8Wr_le (k : ℕ) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : |i8Wr k z| ≤ 2 ^ k := by
  have hu := i8_one_sub_sq_pos hz
  have hu1 : 1 - z ^ 2 ≤ 1 := by nlinarith
  unfold i8Wr
  have hL : 0 ≤ -Real.log (1 - z ^ 2) := by linarith [Real.log_nonpos hu.le hu1]
  have h1 := Real.pow_div_factorial_le_exp (x := -Real.log (1 - z ^ 2) / 2) (by linarith) k
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg (pow_nonneg hL k)
    (by positivity)))]
  calc √(1 - z ^ 2) * ((-Real.log (1 - z ^ 2)) ^ k / k !)
      = 2 ^ k * (√(1 - z ^ 2) * ((-Real.log (1 - z ^ 2) / 2) ^ k / k !)) := by
        rw [div_pow]; field_simp
    _ ≤ 2 ^ k * (√(1 - z ^ 2) * Real.exp (-Real.log (1 - z ^ 2) / 2)) := by gcongr
    _ = 2 ^ k := by rw [i8_sqrt_mul_exp hu, mul_one]

theorem abs_i8Wp_le (k : ℕ) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : |i8Wp k z| ≤ 2 ^ k := by
  cases k with
  | zero => simp [i8Wp]
  | succ k =>
    exact (abs_i8Wr_le k hz).trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k))

theorem continuousOn_i8Wr (k : ℕ) : ContinuousOn (i8Wr k) (Ioo (-1) 1) := by
  intro z hz
  have hu : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  unfold i8Wr
  refine ContinuousAt.continuousWithinAt ?_
  have : ContinuousAt (fun z : ℝ => Real.log (1 - z ^ 2)) z :=
    (continuousAt_const.sub (continuousAt_id.pow 2)).log hu.ne'
  exact (continuous_sqrt.continuousAt.comp (by fun_prop)).mul ((this.neg.pow k).div_const _)

/-- `(1 - z²) wₖ' = -z wₖ + 2z wₖ₋₁`. -/
theorem hasDerivAt_i8Wr (k : ℕ) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i8Wr k) ((-z * i8Wr k z + 2 * z * i8Wp k z) / (1 - z ^ 2)) z := by
  have hu := i8_one_sub_sq_pos hz
  have hg : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-(2 * z)) z := by
    simpa using ((hasDerivAt_pow 2 z).const_sub 1)
  have hs : HasDerivAt (fun z : ℝ => √(1 - z ^ 2)) (-(2 * z) / (2 * √(1 - z ^ 2))) z :=
    hg.sqrt hu.ne'
  have hsq := Real.sq_sqrt hu.le
  have hspos := Real.sqrt_pos.2 hu
  cases k with
  | zero =>
    have e : i8Wr 0 = fun z => √(1 - z ^ 2) := by funext z; simp [i8Wr]
    rw [e]
    refine hs.congr_deriv ?_
    simp only [i8Wp]
    field_simp
    linear_combination z * hsq
  | succ k =>
    have hp := i13_hasDerivAt_negLog_pow hg hu k
    have e : i8Wr (k + 1) = fun z => √(1 - z ^ 2) *
        ((-Real.log (1 - z ^ 2)) ^ (k + 1) / ((k + 1) ! : ℝ)) := rfl
    rw [e]
    refine (hs.mul hp).congr_deriv ?_
    simp only [i8Wp, i8Wr]
    field_simp
    linear_combination (z * (-Real.log (1 - z ^ 2)) ^ (k + 1) * ((k ! : ℝ))) * hsq

/-! ### The differential equation in `t` -/

/-- `G(z) = z (1 - z²) w(z) / (t + 4z²)`, the boundary term of the integration by parts. -/
noncomputable def i8Gb (w : ℝ → ℝ) (t z : ℝ) : ℝ := z * (1 - z ^ 2) * w z / (t + 4 * z ^ 2)

/-- The derivative of `QED.ThreeLoopD.i8Gb`. -/
noncomputable def i8Gd (w wp : ℝ → ℝ) (t z : ℝ) : ℝ :=
  (1 - 4 * z ^ 2) * w z / (t + 4 * z ^ 2) + 2 * z ^ 2 * wp z / (t + 4 * z ^ 2) -
    8 * z ^ 2 * (1 - z ^ 2) * w z / (t + 4 * z ^ 2) ^ 2

theorem hasDerivAt_i8Gb {w wp : ℝ → ℝ} {t z : ℝ} (ht : 0 < t) (hz : z ∈ Ioo (0 : ℝ) 1)
    (hd : HasDerivAt w ((-z * w z + 2 * z * wp z) / (1 - z ^ 2)) z) :
    HasDerivAt (i8Gb w t) (i8Gd w wp t z) z := by
  have hu := i8_one_sub_sq_pos hz
  have hD : 0 < t + 4 * z ^ 2 := by positivity
  have hP : HasDerivAt (fun z : ℝ => z * (1 - z ^ 2)) (1 - 3 * z ^ 2) z := by
    have := (hasDerivAt_id' z).mul ((hasDerivAt_pow 2 z).const_sub 1)
    refine this.congr_deriv ?_
    simp; ring
  have hQ : HasDerivAt (fun z : ℝ => t + 4 * z ^ 2) (8 * z) z := by
    have := ((hasDerivAt_pow 2 z).const_mul 4).const_add t
    refine this.congr_deriv ?_
    simp; ring
  have e := (hP.mul hd).div hQ hD.ne'
  unfold i8Gb
  refine e.congr_deriv ?_
  unfold i8Gd
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- The pointwise identity `-t (t + 4) w / D² = -2 w/D - t wₚ/D - (w - wₚ) - 2 G'`. -/
theorem i8_J_pointwise (w wp : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (z : ℝ) :
    -w z / (t + 4 * z ^ 2) ^ 2 = (-2 * (w z / (t + 4 * z ^ 2)) - t * (wp z / (t + 4 * z ^ 2)) -
      (w z - wp z) - 2 * i8Gd w wp t z) / (t * (t + 4)) := by
  have hD : 0 < t + 4 * z ^ 2 := by positivity
  unfold i8Gd
  field_simp
  ring

theorem i8_integral_Gd_eq_zero {w wp : ℝ → ℝ} {C : ℝ} {t : ℝ} (ht : 0 < t)
    (hb : ∀ z ∈ Ioo (0 : ℝ) 1, |w z| ≤ C) (hc : ContinuousOn w (Ioo (-1) 1))
    (hd : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt w ((-z * w z + 2 * z * wp z) / (1 - z ^ 2)) z)
    (hi : IntegrableOn (i8Gd w wp t) (Ioo (0 : ℝ) 1)) :
    ∫ z in Ioo (0 : ℝ) 1, i8Gd w wp t z = 0 := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb (1 / 2) (by norm_num))
  have hcont : ContinuousOn (i8Gb w t) (Icc 0 1) := by
    intro z hz
    rcases eq_or_lt_of_le hz.2 with h1 | h1
    · subst h1
      have h0 : i8Gb w t 1 = 0 := by simp [i8Gb]
      rw [ContinuousWithinAt, h0]
      have hlim : Tendsto (fun z : ℝ => C / t * (1 - z ^ 2)) (𝓝[Icc 0 1] 1) (𝓝 0) := by
        have : ContinuousAt (fun z : ℝ => C / t * (1 - z ^ 2)) 1 := by fun_prop
        simpa using this.tendsto.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with y hy
      rcases eq_or_lt_of_le hy.2 with h | h
      · subst h; simp [i8Gb]
      rcases eq_or_lt_of_le hy.1 with h' | h'
      · subst h'; simp [i8Gb]; positivity
      have hyI : y ∈ Ioo (0 : ℝ) 1 := ⟨h', h⟩
      have hu := i8_one_sub_sq_pos hyI
      have hD : t ≤ t + 4 * y ^ 2 := by nlinarith
      unfold i8Gb
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos h', abs_of_pos hu,
        abs_of_pos (by positivity : 0 < t + 4 * y ^ 2), div_le_iff₀ (by positivity)]
      have hw := hb y hyI
      calc y * (1 - y ^ 2) * |w y| ≤ 1 * (1 - y ^ 2) * C := by gcongr
        _ = C / t * (1 - y ^ 2) * t := by field_simp
        _ ≤ C / t * (1 - y ^ 2) * (t + 4 * y ^ 2) := by gcongr
    · have hzI : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], h1⟩
      refine ContinuousAt.continuousWithinAt ?_
      unfold i8Gb
      have hw := (hc z hzI).continuousAt (isOpen_Ioo.mem_nhds hzI)
      exact ((continuousAt_id.mul (continuousAt_const.sub (continuousAt_id.pow 2))).mul
        hw).div (by fun_prop) (by positivity)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
      (fun z hz => hasDerivAt_i8Gb ht hz (hd z hz))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact hi))]
  simp [i8Gb]

theorem i8_abs_div_D_le {w : ℝ → ℝ} {C t z : ℝ} (ht : 0 < t) (hw : |w z| ≤ C) :
    |w z / (t + 4 * z ^ 2)| ≤ C / t := by
  have hD : t ≤ t + 4 * z ^ 2 := by nlinarith
  have hC : 0 ≤ C := (abs_nonneg _).trans hw
  rw [abs_div, abs_of_pos (by positivity : 0 < t + 4 * z ^ 2)]
  calc |w z| / (t + 4 * z ^ 2) ≤ C / (t + 4 * z ^ 2) := by gcongr
    _ ≤ C / t := div_le_div_of_nonneg_left hC ht hD

/-- **The differential equation** `t (t + 4) J' = -2 J - t Jₚ - (m - mₚ)` for a weight with
`(1 - z²) w' = -z w + 2z wₚ`. -/
theorem i8_hasDerivAt_Jgen {w wp : ℝ → ℝ} {C : ℝ} (hwm : Measurable w) (hwpm : Measurable wp)
    (hb : ∀ z ∈ Ioo (0 : ℝ) 1, |w z| ≤ C) (hbp : ∀ z ∈ Ioo (0 : ℝ) 1, |wp z| ≤ C)
    (hc : ContinuousOn w (Ioo (-1) 1))
    (hd : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt w ((-z * w z + 2 * z * wp z) / (1 - z ^ 2)) z)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ z in Ioo (0 : ℝ) 1, w z / (s + 4 * z ^ 2))
      ((-2 * (∫ z in Ioo (0 : ℝ) 1, w z / (t + 4 * z ^ 2)) -
        t * (∫ z in Ioo (0 : ℝ) 1, wp z / (t + 4 * z ^ 2)) -
        ((∫ z in Ioo (0 : ℝ) 1, w z) - ∫ z in Ioo (0 : ℝ) 1, wp z)) / (t * (t + 4))) t := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb (1 / 2) (by norm_num))
  have hball : Metric.ball t (t / 2) ∈ 𝓝 t := Metric.ball_mem_nhds t (by linarith)
  have hpos_ball : ∀ s ∈ Metric.ball t (t / 2), t / 2 < s := fun s hs => by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    linarith [(abs_lt.1 hs).1]
  have mD : ∀ s : ℝ, Measurable fun z : ℝ => s + 4 * z ^ 2 := fun s => by fun_prop
  have iD : ∀ {f : ℝ → ℝ}, Measurable f → (∀ z ∈ Ioo (0 : ℝ) 1, |f z| ≤ C) →
      IntegrableOn (fun z => f z / (t + 4 * z ^ 2)) (Ioo (0 : ℝ) 1) := fun hf hfb =>
    i8_integrableOn_bdd (hf.div (mD t)) fun z hz => i8_abs_div_D_le ht (hfb z hz)
  have iGd : IntegrableOn (i8Gd w wp t) (Ioo (0 : ℝ) 1) := by
    refine i8_integrableOn_bdd (C := 3 * (C / t) + 2 * (C / t) + 8 / t * (C / t))
      (by unfold i8Gd; fun_prop) fun z hz => ?_
    have h1 := i8_abs_div_D_le ht (hb z hz)
    have h2 := i8_abs_div_D_le ht (hbp z hz)
    have hD : t ≤ t + 4 * z ^ 2 := by nlinarith
    have hD0 : 0 < t + 4 * z ^ 2 := by positivity
    have e : i8Gd w wp t z = (1 - 4 * z ^ 2) * (w z / (t + 4 * z ^ 2)) +
        2 * z ^ 2 * (wp z / (t + 4 * z ^ 2)) -
        8 * z ^ 2 * (1 - z ^ 2) / (t + 4 * z ^ 2) * (w z / (t + 4 * z ^ 2)) := by
      unfold i8Gd; field_simp
    have hz2 : z ^ 2 < 1 := by nlinarith [hz.1, hz.2]
    have a1 : |1 - 4 * z ^ 2| ≤ 3 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
    have a2 : |2 * z ^ 2| ≤ 2 := by rw [abs_of_nonneg (by positivity)]; nlinarith
    have a3 : |8 * z ^ 2 * (1 - z ^ 2) / (t + 4 * z ^ 2)| ≤ 8 / t := by
      rw [abs_of_nonneg (div_nonneg (mul_nonneg (by positivity) (by linarith)) hD0.le)]
      calc 8 * z ^ 2 * (1 - z ^ 2) / (t + 4 * z ^ 2) ≤ 8 / (t + 4 * z ^ 2) := by
            gcongr; nlinarith
        _ ≤ 8 / t := div_le_div_of_nonneg_left (by norm_num) ht hD
    rw [e]
    calc _ ≤ |(1 - 4 * z ^ 2) * (w z / (t + 4 * z ^ 2))| +
          |2 * z ^ 2 * (wp z / (t + 4 * z ^ 2))| +
          |8 * z ^ 2 * (1 - z ^ 2) / (t + 4 * z ^ 2) * (w z / (t + 4 * z ^ 2))| :=
          (abs_sub _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ _ := by
          rw [abs_mul (1 - 4 * z ^ 2), abs_mul (2 * z ^ 2),
            abs_mul (8 * z ^ 2 * (1 - z ^ 2) / (t + 4 * z ^ 2))]
          gcongr
  obtain ⟨-, hdiff⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (F := fun s z => w z / (s + 4 * z ^ 2))
    (F' := fun s z => -w z / (s + 4 * z ^ 2) ^ 2) (bound := fun _ => C / (t / 2) ^ 2) hball
    (Eventually.of_forall fun s => (hwm.div (mD s)).aestronglyMeasurable)
    (iD hwm hb) ((hwm.neg.div ((mD t).pow_const 2)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun z hz s hs => by
      have hs2 := hpos_ball s hs
      have hD1 : t / 2 ≤ s + 4 * z ^ 2 := by nlinarith
      have hD : (t / 2) ^ 2 ≤ (s + 4 * z ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hD1 2
      have hD2 : 0 < (s + 4 * z ^ 2) ^ 2 := pow_pos (by linarith) 2
      rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hD2]
      calc |w z| / (s + 4 * z ^ 2) ^ 2 ≤ C / (s + 4 * z ^ 2) ^ 2 := by gcongr; exact hb z hz
        _ ≤ C / (t / 2) ^ 2 := div_le_div_of_nonneg_left hC (by positivity) hD)
    (integrable_const _)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun z hz s hs => by
      have hs2 := hpos_ball s hs
      have hD : 0 < s + 4 * z ^ 2 := by nlinarith
      have := (hasDerivAt_const s (w z)).div ((hasDerivAt_id' s).add_const (4 * z ^ 2)) hD.ne'
      refine this.congr_deriv ?_
      simp)
  refine hdiff.congr_deriv ?_
  rw [setIntegral_congr_fun measurableSet_Ioo fun z _ => i8_J_pointwise w wp ht z,
    integral_div]
  congr 1
  have i1 := iD hwm hb
  have i2 := iD hwpm hbp
  have i3 : IntegrableOn w (Ioo (0 : ℝ) 1) := i8_integrableOn_bdd hwm hb
  have i4 : IntegrableOn wp (Ioo (0 : ℝ) 1) := i8_integrableOn_bdd hwpm hbp
  rw [integral_sub (f := fun a => -2 * (w a / (t + 4 * a ^ 2)) - t * (wp a / (t + 4 * a ^ 2)) -
      (w a - wp a)) (g := fun a => 2 * i8Gd w wp t a)
      (((i1.const_mul (-2)).sub (i2.const_mul t)).sub (i3.sub i4)) (iGd.const_mul 2),
    integral_sub (f := fun a => -2 * (w a / (t + 4 * a ^ 2)) - t * (wp a / (t + 4 * a ^ 2)))
      (g := fun a => w a - wp a) ((i1.const_mul (-2)).sub (i2.const_mul t)) (i3.sub i4),
    integral_sub (f := fun a => -2 * (w a / (t + 4 * a ^ 2)))
      (g := fun a => t * (wp a / (t + 4 * a ^ 2))) (i1.const_mul (-2)) (i2.const_mul t),
    integral_sub i3 i4, integral_const_mul, integral_const_mul, integral_const_mul,
    i8_integral_Gd_eq_zero ht hb hc hd iGd]
  ring

/-! ### The angular coefficients `Jₖ` -/

/-- The real angular coefficient `Jₖ(t) = ∫₀¹ wₖ(z) / (t + 4z²) dz`. -/
noncomputable def i8Jr (k : ℕ) (t : ℝ) : ℝ := ∫ z in Ioo (0 : ℝ) 1, i8Wr k z / (t + 4 * z ^ 2)

/-- The real moment `mₖ = ∫₀¹ wₖ`. -/
noncomputable def i8M0r (k : ℕ) : ℝ := ∫ z in Ioo (0 : ℝ) 1, i8Wr k z

/-- `Jₖ₋₁`, with `J₋₁ = 0`. -/
noncomputable def i8Jpr : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, t => i8Jr k t

/-- `mₖ₋₁`, with `m₋₁ = 0`. -/
noncomputable def i8M0pr : ℕ → ℝ
  | 0 => 0
  | k + 1 => i8M0r k

theorem i8JC_eq (t : ℝ) (k : ℕ) : i8JC t k = (i8Jr k t : ℂ) := by
  unfold i8JC i8Jr
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun z _ => ?_
  rw [i8WC_eq]
  push_cast
  ring

theorem i8M0C_eq (k : ℕ) : i8M0C k = (i8M0r k : ℂ) := by
  unfold i8M0C i8M0r
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun z _ => ?_
  rw [i8WC_eq]

theorem i8_integral_Wp_div (k : ℕ) (t : ℝ) :
    ∫ z in Ioo (0 : ℝ) 1, i8Wp k z / (t + 4 * z ^ 2) = i8Jpr k t := by
  cases k with
  | zero => simp [i8Wp, i8Jpr]
  | succ k => rfl

theorem i8_integral_Wp (k : ℕ) : ∫ z in Ioo (0 : ℝ) 1, i8Wp k z = i8M0pr k := by
  cases k with
  | zero => simp [i8Wp, i8M0pr]
  | succ k => rfl

/-- **The angular differential equation** `t (t + 4) Jₖ' = -2 Jₖ - t Jₖ₋₁ - (mₖ - mₖ₋₁)`. -/
theorem hasDerivAt_i8Jr (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (i8Jr k) ((-2 * i8Jr k t - t * i8Jpr k t - (i8M0r k - i8M0pr k)) /
      (t * (t + 4))) t := by
  have h := i8_hasDerivAt_Jgen (measurable_i8Wr k) (measurable_i8Wp k)
    (fun z hz => abs_i8Wr_le k hz) (fun z hz => abs_i8Wp_le k hz) (continuousOn_i8Wr k)
    (fun z hz => hasDerivAt_i8Wr k hz) ht
  rw [i8_integral_Wp_div, i8_integral_Wp] at h
  exact h

theorem abs_i8Jr_le (k : ℕ) {t : ℝ} (ht : 0 < t) : |i8Jr k t| ≤ 2 ^ k / t := by
  unfold i8Jr
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) 1) (C := 2 ^ k / t)
    (f := fun z => i8Wr k z / (t + 4 * z ^ 2)) measure_Ioo_lt_top fun z hz => by
      rw [Real.norm_eq_abs]; exact i8_abs_div_D_le ht (abs_i8Wr_le k hz)
  rw [Real.norm_eq_abs] at this
  simpa [Measure.real, Real.volume_Ioo] using this

end QED.ThreeLoopD
