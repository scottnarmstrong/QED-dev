/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The value of the vacuum-polarization unit (O2-18)

The limit of the vacuum-polarization (VP) unit for the electron flavour (obligation O2-18 of
`docs/TWO-LOOP-DERIVATION.md`) is the double integral
`∫₀¹ dv ρ(v) ∫₀¹ dx x²(1-x) / (x² + (1-x)·4/(1-v²)) = 119/36 - π²/3`, with spectral weight
`ρ(v) = v²(1 - v²/3)/(1 - v²)`.

The weight blows up like `1/(1-v²)` at `v = 1`, while the inner integral decays like `1 - v²`.
For `0 ≤ v < 1` the outer integrand is the integral in `x` of the kernel
`K(v, x) = v²(1 - v²/3) x²(1-x) / ((2-x)² - x²v²)`, obtained by multiplying numerator and
denominator by `1 - v²`; the kernel satisfies `0 ≤ K ≤ 1` on `[0,1]²`. At `v = 1` Lean's
division by zero makes the outer integrand `0`; this point is a null set.

## Route

1. Fubini on `(0,1]²` for the bounded kernel `K` (`integrable_vpKernel`).
2. For `0 < x < 1` the `v`-integral is elementary, because
   `(2-x)² - x²v² = (2-x+xv)(2-x-xv)` (`integral_vpKernel_v`):
   `∫₀¹ K(v,x) dv = (1-x)(4 - 4x - 5x²/3)/(3x²) - (1-x)(2-x)(x²+2x-2)/(3x³) · log(1-x)`.
3. The `x`-integral of this function has the antiderivative
   `H(x) = (13x²+22x)/36 - 2/(3x) + (1-x)log(1-x)(x³-x²+16x-4)/(6x²) - 2 Li₂(x)` on `(0,1)`,
   with `H(0⁺) = -3` and `H(1⁻) = 11/36 - π²/3` (`integral_vpX`).

## Main statements

* `QED.TwoLoop.VPUnit.integral_vpUnit`: the double integral equals `119/36 - π²/3`.
* `QED.TwoLoop.VPUnit.intervalIntegrable_vpUnit`: the outer integrand is interval integrable on
  `[0,1]`.
* `QED.TwoLoop.VPUnit.vpUnit_integrand_mem_Icc`: for `0 ≤ v < 1` the outer integrand lies in
  `[0,1]`.
* `QED.TwoLoop.VPUnit.integral_mul_log_eq_spectral`: the spectral identity of O2-18,
  `∫₀¹ dx x(1-x) log((M² + x(1-x)k²)/M²) = ½ ∫₀¹ dv ρ(v) k²/(k² + 4M²/(1-v²))` for `M ≠ 0`
  and `k² > -4M²`.
-/

public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.TwoLoop.VPUnit

/-- The kernel `K(v, x) = v²(1 - v²/3) x²(1-x) / ((2-x)² - x²v²)`: the VP-unit integrand with the
factor `1 - v²` cleared from the weight and from the inner denominator. -/
noncomputable def vpKernel (v x : ℝ) : ℝ :=
  v ^ 2 * (1 - v ^ 2 / 3) * (x ^ 2 * (1 - x)) / ((2 - x) ^ 2 - x ^ 2 * v ^ 2)

theorem vpKernel_den_eq (v x : ℝ) :
    (2 - x) ^ 2 - x ^ 2 * v ^ 2 = 4 * (1 - x) + x ^ 2 * (1 - v ^ 2) := by ring

theorem vpKernel_nonneg {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ vpKernel v x := by
  obtain ⟨hv0, hv1⟩ := hv
  obtain ⟨hx0, hx1⟩ := hx
  have hv2 : v ^ 2 ≤ 1 := by nlinarith
  unfold vpKernel
  refine div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg v) (by linarith))
    (mul_nonneg (sq_nonneg x) (by linarith))) ?_
  rw [vpKernel_den_eq]
  have := mul_nonneg (sq_nonneg x) (sub_nonneg.2 hv2)
  linarith

theorem vpKernel_le_one {v x : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    vpKernel v x ≤ 1 := by
  obtain ⟨hv0, hv1⟩ := hv
  obtain ⟨hx0, hx1⟩ := hx
  have hv2 : v ^ 2 ≤ 1 := by nlinarith
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have ha0 : 0 ≤ v ^ 2 * (1 - v ^ 2 / 3) := mul_nonneg (sq_nonneg v) (by linarith)
  have ha : v ^ 2 * (1 - v ^ 2 / 3) ≤ 1 := by nlinarith
  have hb0 : 0 ≤ x ^ 2 * (1 - x) := mul_nonneg (sq_nonneg x) (by linarith)
  have hb : x ^ 2 * (1 - x) ≤ 1 - x := mul_le_of_le_one_left (by linarith) hx2
  have hc := mul_nonneg (sq_nonneg x) (sub_nonneg.2 hv2)
  unfold vpKernel
  rw [vpKernel_den_eq]
  refine div_le_one_of_le₀ ?_ (by linarith)
  calc v ^ 2 * (1 - v ^ 2 / 3) * (x ^ 2 * (1 - x)) ≤ 1 * (x ^ 2 * (1 - x)) :=
        mul_le_mul_of_nonneg_right ha hb0
    _ ≤ 4 * (1 - x) + x ^ 2 * (1 - v ^ 2) := by linarith

/-- The denominator of the kernel is positive for `x ∈ [0,1]` and `v ∈ [0,1)`. -/
theorem vpKernel_den_pos {v x : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < (2 - x) ^ 2 - x ^ 2 * v ^ 2 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hv2 : 0 < 1 - v ^ 2 := by nlinarith
  rw [vpKernel_den_eq]
  rcases hx1.lt_or_eq with h | h
  · have := mul_nonneg (sq_nonneg x) hv2.le
    linarith
  · subst h
    linarith

theorem measurable_vpKernel : Measurable (Function.uncurry vpKernel) := by
  change Measurable fun q : ℝ × ℝ => vpKernel q.1 q.2
  unfold vpKernel
  fun_prop

/-- The kernel is integrable on `(0,1]²`, being measurable with values in `[0,1]`. -/
theorem integrable_vpKernel :
    Integrable (Function.uncurry vpKernel)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) measurable_vpKernel.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) ?_
  rintro ⟨v, x⟩ ⟨hv, hx⟩
  simp only [Function.uncurry_apply_pair]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (vpKernel_nonneg (Ioc_subset_Icc_self hv) (Ioc_subset_Icc_self hx))]
  exact vpKernel_le_one (Ioc_subset_Icc_self hv) (Ioc_subset_Icc_self hx)

/-- Almost every point of `(0,1]` lies in `(0,1)`. -/
theorem ae_mem_Ioo : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact ae_restrict_mem measurableSet_Ioo

/-- For `0 ≤ v < 1` the outer integrand is the `x`-integral of the kernel. -/
theorem vpUnit_integrand_eq {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) *
        ∫ x in (0 : ℝ)..1, x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - v ^ 2))) =
      ∫ x in (0 : ℝ)..1, vpKernel v x := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  have hs : 0 < 1 - v ^ 2 := by nlinarith
  have hD := vpKernel_den_pos hv0 hv1 hx
  have key : x ^ 2 + (1 - x) * (4 / (1 - v ^ 2)) = ((2 - x) ^ 2 - x ^ 2 * v ^ 2) / (1 - v ^ 2) := by
    field_simp
    ring
  simp only [vpKernel]
  rw [key]
  field_simp

/-! ### The `v`-integral at fixed `x` -/

/-- An antiderivative in `v` of the kernel at fixed `x ∈ (0,1)`. -/
noncomputable def vAntideriv (x v : ℝ) : ℝ :=
  (1 - x) / (3 * x ^ 2) * (x ^ 2 * v ^ 3 / 3 - (2 * x ^ 2 + 4 * x - 4) * v) +
    (1 - x) * (2 - x) * (x ^ 2 + 2 * x - 2) / (3 * x ^ 3) *
      (log (2 - x + x * v) - log (2 - x - x * v))

/-- The `v`-integral of the kernel at fixed `x`. -/
noncomputable def vpX (x : ℝ) : ℝ :=
  (1 - x) * (4 - 4 * x - 5 * x ^ 2 / 3) / (3 * x ^ 2) -
    (1 - x) * (2 - x) * (x ^ 2 + 2 * x - 2) / (3 * x ^ 3) * log (1 - x)

theorem hasDerivAt_vAntideriv {x v : ℝ} (hx0 : 0 < x) (hp : 0 < 2 - x + x * v)
    (hm : 0 < 2 - x - x * v) : HasDerivAt (vAntideriv x) (vpKernel v x) v := by
  have h1 : HasDerivAt (fun v => 2 - x + x * v) x v := by
    simpa using ((hasDerivAt_id' v).const_mul x).const_add (2 - x)
  have h2 : HasDerivAt (fun v => 2 - x - x * v) (-x) v := by
    simpa using ((hasDerivAt_id' v).const_mul x).const_sub (2 - x)
  have h3 : HasDerivAt (fun v => x ^ 2 * v ^ 3 / 3 - (2 * x ^ 2 + 4 * x - 4) * v)
      (x ^ 2 * v ^ 2 - (2 * x ^ 2 + 4 * x - 4)) v := by
    have := (((hasDerivAt_pow 3 v).const_mul (x ^ 2)).div_const 3).sub
      ((hasDerivAt_id' v).const_mul (2 * x ^ 2 + 4 * x - 4))
    convert this using 1
    push_cast
    ring
  have h := (h3.const_mul ((1 - x) / (3 * x ^ 2))).add
    (((h1.log hp.ne').sub (h2.log hm.ne')).const_mul
      ((1 - x) * (2 - x) * (x ^ 2 + 2 * x - 2) / (3 * x ^ 3)))
  refine h.congr_deriv ?_
  have hD : (2 - x) ^ 2 - x ^ 2 * v ^ 2 = (2 - x + x * v) * (2 - x - x * v) := by ring
  unfold vpKernel
  rw [hD]
  field_simp
  ring

theorem integral_vpKernel_v {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ v in (0 : ℝ)..1, vpKernel v x = vpX x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hpm : ∀ v ∈ uIcc (0 : ℝ) 1, 0 < 2 - x + x * v ∧ 0 < 2 - x - x * v := by
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    obtain ⟨hv0, hv1⟩ := hv
    constructor <;> nlinarith
  have hcont : ContinuousOn (fun v => vpKernel v x) (uIcc 0 1) := by
    unfold vpKernel
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => ?_
    have hD : (2 - x) ^ 2 - x ^ 2 * v ^ 2 = (2 - x + x * v) * (2 - x - x * v) := by ring
    rw [hD]
    exact (mul_pos (hpm v hv).1 (hpm v hv).2).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => hasDerivAt_vAntideriv hx0 (hpm v hv).1 (hpm v hv).2) hcont.intervalIntegrable]
  simp only [vAntideriv, vpX, mul_one, mul_zero, add_zero, sub_zero, sub_self]
  rw [show 2 - x + x = (2 : ℝ) by ring, show 2 - x - x = 2 * (1 - x) by ring,
    log_mul two_ne_zero (by linarith : (1 : ℝ) - x ≠ 0)]
  field_simp
  ring

/-! ### The `x`-integral -/

/-- An antiderivative of `vpX` on `(0,1)`. -/
noncomputable def xAntideriv (x : ℝ) : ℝ :=
  (13 * x ^ 2 + 22 * x) / 36 - 2 / (3 * x) +
    (1 - x) * log (1 - x) * ((x ^ 3 - x ^ 2 + 16 * x - 4) / (6 * x ^ 2)) - 2 * Li₂ x

theorem hasDerivAt_xAntideriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt xAntideriv (vpX x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hne : (1 : ℝ) - x ≠ 0 := by linarith
  have hA := (((hasDerivAt_pow 2 x).const_mul 13).add ((hasDerivAt_id' x).const_mul 22)).div_const 36
  have hB := (hasDerivAt_const x (2 : ℝ)).div ((hasDerivAt_id' x).const_mul 3) (by positivity)
  have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  have hL := hs.mul (hs.log hne)
  have hC := ((((hasDerivAt_pow 3 x).sub (hasDerivAt_pow 2 x)).add
    ((hasDerivAt_id' x).const_mul 16)).sub_const 4).div ((hasDerivAt_pow 2 x).const_mul 6)
    (by positivity)
  have hLi := (hasDerivAt_Li₂ (by rw [abs_of_pos hx0]; exact hx1) hx0.ne').const_mul 2
  have h := ((hA.sub hB).add (hL.mul hC)).sub hLi
  refine h.congr_deriv ?_
  simp only [vpX, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  push_cast
  field_simp
  ring

theorem Li₂_zero : Li₂ 0 = 0 := by simp [Li₂]

theorem tendsto_xAntideriv_zero : Tendsto xAntideriv (𝓝[>] 0) (𝓝 (-3)) := by
  -- the remainder `r(y) = log (1 - y) + y + y²/2` is `O(y³)`
  set r : ℝ → ℝ := fun y => y + y ^ 2 / 2 + log (1 - y) with hr
  have hr0 : Tendsto (fun y => r y / y ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun y : ℝ => |y| / (1 - |y|)) (𝓝[>] 0) (𝓝 0) := by
      have : ContinuousAt (fun y : ℝ => |y| / (1 - |y|)) 0 :=
        continuous_abs.continuousAt.div (continuous_const.sub continuous_abs).continuousAt
          (by simp)
      have h := this.tendsto
      simp only [abs_zero, sub_zero, zero_div] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hlog := abs_log_sub_add_sum_range_le (x := y) (by rw [abs_of_pos hy0]; exact hy1) 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlog
    norm_num at hlog
    rw [abs_of_pos hy0] at hlog ⊢
    simp only [norm_div, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : (0 : ℝ) < y ^ 2), div_le_iff₀ (by positivity)]
    have h1 : 0 < 1 - y := by linarith
    calc |r y| ≤ y ^ 3 / (1 - y) := hlog
      _ = y / (1 - y) * y ^ 2 := by field_simp
  set p : ℝ → ℝ := fun y => -3 + 16 * y / 9 + 13 * y ^ 2 / 9 + y ^ 4 / 12 with hp
  set q : ℝ → ℝ := fun y => -y ^ 4 / 6 + y ^ 3 / 3 - 17 * y ^ 2 / 6 + 10 * y / 3 - 2 / 3 with hq
  have hLi : Tendsto Li₂ (𝓝[>] 0) (𝓝 0) := by
    have := (continuousOn_Li₂.continuousAt (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))).tendsto
    rw [Li₂_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hpq : Tendsto (fun y => p y + q y * (r y / y ^ 2) - 2 * Li₂ y) (𝓝[>] 0)
      (𝓝 (p 0 + q 0 * 0 - 2 * 0)) := by
    have hp' : Tendsto p (𝓝[>] 0) (𝓝 (p 0)) :=
      ((by fun_prop : Continuous p).tendsto 0).mono_left nhdsWithin_le_nhds
    have hq' : Tendsto q (𝓝[>] 0) (𝓝 (q 0)) :=
      ((by fun_prop : Continuous q).tendsto 0).mono_left nhdsWithin_le_nhds
    exact (hp'.add (hq'.mul hr0)).sub (hLi.const_mul 2)
  have hval : p 0 + q 0 * 0 - 2 * 0 = -3 := by simp [hp]
  rw [hval] at hpq
  refine hpq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  simp only [xAntideriv, hp, hq, hr]
  field_simp
  ring

theorem tendsto_xAntideriv_one :
    Tendsto xAntideriv (𝓝[<] 1) (𝓝 (11 / 36 - π ^ 2 / 3)) := by
  have hL : Continuous fun y : ℝ => (1 - y) * log (1 - y) :=
    continuous_mul_log.comp (continuous_const.sub continuous_id)
  have hA : ContinuousAt (fun y : ℝ => (13 * y ^ 2 + 22 * y) / 36) 1 := by fun_prop
  have hB : ContinuousAt (fun y : ℝ => 2 / (3 * y)) 1 := by fun_prop (disch := norm_num)
  have hC : ContinuousAt (fun y : ℝ => (y ^ 3 - y ^ 2 + 16 * y - 4) / (6 * y ^ 2)) 1 := by
    fun_prop (disch := norm_num)
  have hLi : ContinuousWithinAt Li₂ (Iio 1) 1 :=
    (continuousOn_Li₂ 1 (by norm_num)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)) Ioo_subset_Icc_self)
  have h : ContinuousWithinAt xAntideriv (Iio 1) 1 :=
    ((hA.sub hB).add (hL.continuousAt.mul hC)).continuousWithinAt.sub
      (continuousWithinAt_const.mul hLi)
  have hval : xAntideriv 1 = 11 / 36 - π ^ 2 / 3 := by
    simp only [xAntideriv, sub_self, zero_mul, Li₂_one]
    norm_num
    ring
  rw [← hval]
  exact h.tendsto

/-- The `v`-integral of the kernel, as a function of `x`, is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_vpX : IntervalIntegrable vpX volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine integrable_vpKernel.integral_prod_right.congr ?_
  filter_upwards [ae_mem_Ioo] with x hx
  simp only [Function.uncurry_apply_pair]
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_vpKernel_v hx]

theorem integral_vpX : ∫ x in (0 : ℝ)..1, vpX x = 119 / 36 - π ^ 2 / 3 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun x hx => hasDerivAt_xAntideriv hx) intervalIntegrable_vpX tendsto_xAntideriv_zero
    tendsto_xAntideriv_one]
  ring

/-! ### Main statements -/

/-- The outer integrand of the VP-unit double integral is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_vpUnit :
    IntervalIntegrable (fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) *
      ∫ x in (0 : ℝ)..1, x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - v ^ 2)))) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine integrable_vpKernel.integral_prod_left.congr ?_
  filter_upwards [ae_mem_Ioo] with v hv
  simp only [Function.uncurry_apply_pair]
  rw [vpUnit_integrand_eq hv.1.le hv.2, intervalIntegral.integral_of_le zero_le_one]

/-- For `0 ≤ v < 1` the outer integrand of the VP-unit double integral lies in `[0,1]`. -/
theorem vpUnit_integrand_mem_Icc {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) *
        ∫ x in (0 : ℝ)..1, x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - v ^ 2))) ∈
      Icc (0 : ℝ) 1 := by
  rw [vpUnit_integrand_eq hv0 hv1]
  have hv : v ∈ Icc (0 : ℝ) 1 := ⟨hv0, hv1.le⟩
  have hcont : ContinuousOn (fun x => vpKernel v x) (uIcc 0 1) := by
    unfold vpKernel
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    exact (vpKernel_den_pos hv0 hv1 hx).ne'
  constructor
  · refine intervalIntegral.integral_nonneg zero_le_one fun x hx => vpKernel_nonneg hv hx
  · calc ∫ x in (0 : ℝ)..1, vpKernel v x ≤ ∫ _ in (0 : ℝ)..1, (1 : ℝ) :=
          intervalIntegral.integral_mono_on zero_le_one hcont.intervalIntegrable
            intervalIntegrable_const fun x hx => vpKernel_le_one hv hx
      _ = 1 := by simp

/-- **The VP-unit value (O2-18).**
`∫₀¹ dv v²(1 - v²/3)/(1 - v²) ∫₀¹ dx x²(1-x) / (x² + (1-x)·4/(1-v²)) = 119/36 - π²/3`. -/
theorem integral_vpUnit :
    ∫ v in (0 : ℝ)..1, v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) *
      ∫ x in (0 : ℝ)..1, x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - v ^ 2))) =
      119 / 36 - π ^ 2 / 3 := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    integral_congr_ae (g := fun v => ∫ x, vpKernel v x ∂(volume.restrict (Ioc (0 : ℝ) 1))) ?_]
  · rw [integral_integral_swap integrable_vpKernel,
      integral_congr_ae (g := vpX) ?_, ← intervalIntegral.integral_of_le zero_le_one,
      integral_vpX]
    filter_upwards [ae_mem_Ioo] with x hx
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_vpKernel_v hx]
  · filter_upwards [ae_mem_Ioo] with v hv
    rw [vpUnit_integrand_eq hv.1.le hv.2, intervalIntegral.integral_of_le zero_le_one]

/-! ### The spectral identity -/

/-- **The spectral form of the one-loop VP function (O2-18).** For `M ≠ 0` and `k² > -4M²`,
`∫₀¹ dx x(1-x) log((M² + x(1-x)k²)/M²) = ½ ∫₀¹ dv ρ(v) k²/(k² + 4M²/(1-v²))` with
`ρ(v) = v²(1 - v²/3)/(1 - v²)`. Proof: the substitution `x = (1-v)/2` (so
`x(1-x) = (1-v²)/4`), evenness in `v`, and an integration by parts in `v`. -/
theorem integral_mul_log_eq_spectral {M K : ℝ} (hM : M ≠ 0) (hK : -(4 * M ^ 2) < K) :
    ∫ x in (0 : ℝ)..1, x * (1 - x) * log ((M ^ 2 + x * (1 - x) * K) / M ^ 2) =
      1 / 2 * ∫ v in (0 : ℝ)..1,
        v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) * (K / (K + 4 * M ^ 2 / (1 - v ^ 2))) := by
  have hM2 : 0 < M ^ 2 := by positivity
  have hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < M ^ 2 + (1 - v ^ 2) * K / 4 := by
    intro v hv
    obtain ⟨hv0, hv1⟩ := hv
    have hv2 : v ^ 2 ≤ 1 := by nlinarith
    rcases le_or_gt 0 K with hK0 | hK0
    · have := mul_nonneg (sub_nonneg.2 hv2) hK0
      linarith
    · nlinarith [mul_nonneg (sq_nonneg v) (neg_nonneg.2 hK0.le)]
  set g : ℝ → ℝ := fun v => (1 - v ^ 2) / 4 * log ((M ^ 2 + (1 - v ^ 2) * K / 4) / M ^ 2) with hg
  have hgc : ContinuousOn g (Icc (-1) 1) :=
    (by fun_prop : Continuous fun v : ℝ => (1 - v ^ 2) / 4).continuousOn.mul
      (ContinuousOn.log (by fun_prop) fun v hv => (div_pos (hpos v hv) hM2).ne')
  have hgi : ∀ a b : ℝ, a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → IntervalIntegrable g volume a b :=
    fun a b ha hb => (hgc.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  -- Step 1: the substitution `x = 1/2 - v/2`, `v ∈ [-1, 1]`.
  have h1 : ∫ x in (0 : ℝ)..1, x * (1 - x) * log ((M ^ 2 + x * (1 - x) * K) / M ^ 2) =
      1 / 2 * ∫ v in (-1 : ℝ)..1, g v := by
    have h := intervalIntegral.integral_comp_sub_div (a := -1) (b := 1)
      (fun x => x * (1 - x) * log ((M ^ 2 + x * (1 - x) * K) / M ^ 2)) two_ne_zero (1 / 2)
    rw [show (1 : ℝ) / 2 - 1 / 2 = 0 by norm_num, show (1 : ℝ) / 2 - -1 / 2 = 1 by norm_num,
      smul_eq_mul] at h
    have hfg : ∀ v : ℝ, (1 / 2 - v / 2) * (1 - (1 / 2 - v / 2)) = (1 - v ^ 2) / 4 := fun v => by
      ring
    simp only [hfg] at h
    have hg' : ∫ v in (-1 : ℝ)..1, g v =
        ∫ v in (-1 : ℝ)..1, (1 - v ^ 2) / 4 * log ((M ^ 2 + (1 - v ^ 2) / 4 * K) / M ^ 2) :=
      intervalIntegral.integral_congr fun v _ => by
        simp only [hg]
        rw [div_mul_eq_mul_div (1 - v ^ 2) 4 K]
    rw [hg', h]
    ring
  -- Step 2: `g` is even.
  have h2 : ∫ v in (-1 : ℝ)..1, g v = 2 * ∫ v in (0 : ℝ)..1, g v := by
    have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have h11 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgi _ _ hm1 h0) (hgi _ _ h0 h11)]
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1) g
    simp only [neg_zero, hg, neg_sq] at h
    rw [← h]
    ring
  -- Step 3: integration by parts on `[0, 1]`.
  set R : ℝ → ℝ := fun v => v ^ 2 * (1 - v ^ 2 / 3) * K / (K * (1 - v ^ 2) + 4 * M ^ 2) with hR
  have hRden : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < K * (1 - v ^ 2) + 4 * M ^ 2 := fun v hv => by
    have := hpos v hv
    linarith
  have hRc : ContinuousOn R (Icc (-1) 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => (hRden v hv).ne'
  have h01 : uIcc (0 : ℝ) 1 ⊆ Icc (-1) 1 := by
    rw [uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have h3 : ∫ v in (0 : ℝ)..1, g v = 1 / 2 * ∫ v in (0 : ℝ)..1, R v := by
    have hderiv : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt
        (fun v => (v - v ^ 3 / 3) * log ((M ^ 2 + (1 - v ^ 2) * K / 4) / M ^ 2))
        (4 * g v - 2 * R v) v := by
      intro v hv
      have hs := hpos v (h01 hv)
      have hd := hRden v (h01 hv)
      have hq : HasDerivAt (fun v : ℝ => (M ^ 2 + (1 - v ^ 2) * K / 4) / M ^ 2)
          (-(2 * v) * K / 4 / M ^ 2) v := by
        have := (((((hasDerivAt_pow 2 v).const_sub 1).mul_const K).div_const 4).const_add
          (M ^ 2)).div_const (M ^ 2)
        convert this using 1
        push_cast
        ring
      have hp : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3) (1 - v ^ 2) v := by
        have := (hasDerivAt_id' v).sub ((hasDerivAt_pow 3 v).div_const 3)
        convert this using 1
        push_cast
        ring
      refine (hp.mul (hq.log (div_pos hs hM2).ne')).congr_deriv ?_
      simp only [hg, hR]
      field_simp
      ring
    have hgI : IntervalIntegrable (fun v => 4 * g v) volume 0 1 :=
      (hgc.mono h01).intervalIntegrable.const_mul 4
    have hRI : IntervalIntegrable (fun v => 2 * R v) volume 0 1 :=
      (hRc.mono h01).intervalIntegrable.const_mul 2
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hgI.sub hRI)
    rw [intervalIntegral.integral_sub hgI hRI, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hFTC
    norm_num [div_self hM2.ne'] at hFTC
    linarith
  -- Step 4: the spectral integrand equals `R` off `v = 1`.
  have h4 : ∫ v in (0 : ℝ)..1,
      v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2) * (K / (K + 4 * M ^ 2 / (1 - v ^ 2))) =
        ∫ v in (0 : ℝ)..1, R v := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Ioo] with v hv
    obtain ⟨hv0, hv1⟩ := hv
    have hs : 0 < 1 - v ^ 2 := by nlinarith
    have hd := hRden v ⟨by linarith, hv1.le⟩
    have key : K + 4 * M ^ 2 / (1 - v ^ 2) = (K * (1 - v ^ 2) + 4 * M ^ 2) / (1 - v ^ 2) := by
      field_simp
    simp only [hR]
    rw [key]
    field_simp
  rw [h1, h2, h3, h4]
  ring

end QED.TwoLoop.VPUnit
