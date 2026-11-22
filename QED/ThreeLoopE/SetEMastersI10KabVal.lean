/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10KabAn
public import QED.ThreeLoopD.SetDMastersLaurent
public import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (e), master `I₁₀`: the expansion `K_ab = (2π²/3 - π⁴/18 - 2ζ₃) ε² + O(ε³)`

By `QED.ThreeLoopE.i10Kab_eq`, `K_ab = ε² h` with `h = ∫ H` analytic near `0`, so
`HasTruncLaurent K_ab (h(0) ε²) 3` (`QED.ThreeLoopE.hasTruncLaurent_i10Kab`), and

  `h(0) = ∫_{(0,1)³} log (1 - ρ) log (1 - σ) (τ⁻¹ - (1 - z) σ⁻¹ - z ρ⁻¹) / (z(1 - z))`.

The `z`-integrand is `-(ρ - σ)² / (ρ σ τ)` times the logarithms, and `∫₀¹ dz / τ =
(log ρ - log σ) / (ρ - σ)`, so the inner integral is
`log (1 - ρ) log (1 - σ) (1/ρ - 1/σ)(log ρ - log σ)`. Expanding, the outer integral is a sum of
products of `∫ log (1 - x) log x / x = ζ₃`, `∫ log (1 - x) = -1`, `∫ log (1 - x) / x = -ζ₂` and
`∫ log x log (1 - x) = 2 - ζ₂`
(`QED.ThreeLoopE.intervalIntegrable_and_integral_log_mul_log_one_sub`,
primitive `(x log x - x + 1) log (1 - x) - x log x + 2x + Li₂(1 - x)`):
`h(0) = -2ζ₃ + 2ζ₂(2 - ζ₂)` (`QED.ThreeLoopE.integral_i10KabH_zero`). This agrees with the direct
Taylor coefficient of `scripts/numerics/three_loop_masters/i10taylor.py`, `-1.2359937074…`.

## Main results

* `QED.ThreeLoopE.intervalIntegrable_and_integral_log_mul_log_one_sub`.
* `QED.ThreeLoopE.integral_i10KabH_zero`, `QED.ThreeLoopE.hasTruncLaurent_i10Kab`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.ThreeLoopD

namespace QED.ThreeLoopE

/-! ### One-dimensional integrals -/

theorem i10_integrableOn_log_one_sub : IntegrableOn (fun u : ℝ => log (1 - u)) (Ioo 0 1) := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 1) (b := 0)).comp_sub_left 1
  simp only [sub_self, sub_zero] at h
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h

theorem i10_integral_log_one_sub : ∫ u in Ioo (0 : ℝ) 1, log (1 - u) = -1 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left (fun u => log u) 1, integral_log]
  simp

/-- `0 ≤ x log x - x + 1 ≤ (1 - x)²` for `x > 0`. -/
theorem i10_xlogx_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ x * log x - x + 1 ∧ x * log x - x + 1 ≤ (1 - x) ^ 2 := by
  have h1 := Real.log_le_sub_one_of_pos hx
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h2
  constructor
  · have : x * (1 - x⁻¹) ≤ x * log x := mul_le_mul_of_nonneg_left (by linarith) hx.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hx.ne'] at this
    linarith
  · nlinarith

theorem i10_tendsto_xlogx_log_one_sub :
    Tendsto (fun x => (x * log x - x + 1) * log (1 - x)) (𝓝[<] 1) (𝓝 0) := by
  have hy : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 0) := by
    have := ((by fun_prop : Continuous fun x : ℝ => 1 - x).tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hm : Tendsto (fun x : ℝ => (1 - x) * ((1 - x) * log (1 - x))) (𝓝[<] 1) (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => (1 - x) * log (1 - x)) (𝓝[<] 1) (𝓝 0) := by
      have := (Real.continuous_mul_log.tendsto 0).comp hy
      simpa [Function.comp_def] using this
    simpa using hy.mul h2
  refine squeeze_zero_norm' ?_ (by simpa using hm.norm)
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
  obtain ⟨b0, b1⟩ := i10_xlogx_bounds hx.1
  have hl : log (1 - x) ≤ 0 := Real.log_nonpos (by linarith [hx.2]) (by linarith [hx.1])
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg b0, abs_of_nonpos hl,
    abs_of_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x)]
  nlinarith [mul_le_mul_of_nonneg_right b1 (neg_nonneg.mpr hl)]

/-- `∫₀¹ log x log (1 - x) = 2 - ζ₂`. -/
theorem intervalIntegrable_and_integral_log_mul_log_one_sub :
    IntervalIntegrable (fun x => log x * log (1 - x)) MeasureTheory.volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, log x * log (1 - x) = 2 - π ^ 2 / 6 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg
    (F := fun x => (x * log x - x + 1) * log (1 - x) - x * log x + 2 * x + Li₂ (1 - x))
    (f := fun x => log x * log (1 - x)) (A := π ^ 2 / 6) (B := 2) ?_ ?_ ?_ ?_
  · exact h
  · intro x hx
    have hx1 : 1 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hL := ((hasDerivAt_Li₂' hx1).comp x ((hasDerivAt_id x).const_sub 1))
    have hl := Real.hasDerivAt_log hx.1.ne'
    have hl1 := ((hasDerivAt_id x).const_sub 1).log (by linarith [hx.2] : (1 : ℝ) - x ≠ 0)
    have hm := (hasDerivAt_id x).mul hl
    have h := ((((hm.sub (hasDerivAt_id x)).add_const 1).mul hl1).sub hm).add
      ((hasDerivAt_id x).const_mul 2) |>.add hL
    convert h using 1
    · funext y; simp
    · have h1 : 1 - x ≠ 0 := by linarith [hx.2]
      have h0 := hx.1.ne'
      simp only [id, sub_sub_cancel, Pi.mul_apply, Pi.sub_apply]
      field_simp
      ring
  · intro x hx
    exact mul_nonneg_of_nonpos_of_nonpos (Real.log_nonpos hx.1.le hx.2.le)
      (Real.log_nonpos (by linarith [hx.2]) (by linarith [hx.1]))
  · have hc : ContinuousAt (fun x : ℝ => (x * log x - x + 1) * log (1 - x) - x * log x + 2 * x)
        0 := by
      have hm := Real.continuous_mul_log.continuousAt (x := (0 : ℝ))
      have hl : ContinuousAt (fun x : ℝ => log (1 - x)) 0 :=
        (Real.continuousAt_log (by norm_num)).comp
          (by fun_prop : Continuous fun x : ℝ => 1 - x).continuousAt
      exact (((hm.sub continuousAt_id).add continuousAt_const).mul hl).sub hm |>.add
        (continuousAt_const.mul continuousAt_id)
    have h1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [zero_mul, sub_zero, zero_add, sub_self, Real.log_one, mul_zero, add_zero] at h1
    have hy : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝[<] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := ((by fun_prop : Continuous fun x : ℝ => 1 - x).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_Iio]; linarith [mem_Ioi.mp hx]
    simpa using h1.add (tendsto_Li₂_one_left.comp hy)
  · have hm : Tendsto (fun x : ℝ => x * log x) (𝓝[<] 1) (𝓝 0) := by
      have := (Real.continuous_mul_log.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 1))
      simpa using this
    have h2 : Tendsto (fun x : ℝ => 2 * x) (𝓝[<] 1) (𝓝 2) := by
      have := ((by fun_prop : Continuous fun x : ℝ => 2 * x).tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using this
    have hy : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := ((by fun_prop : Continuous fun x : ℝ => 1 - x).tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_Ioi]; linarith [mem_Iio.mp hx]
    have := ((i10_tendsto_xlogx_log_one_sub.sub hm).add h2).add (tendsto_Li₂_zero_right.comp hy)
    simpa using this

theorem i10_ioo_of_interval {f : ℝ → ℝ} {c : ℝ} (h : IntervalIntegrable f volume 0 1 ∧
    ∫ x in (0 : ℝ)..1, f x = c) : IntegrableOn f (Ioo 0 1) ∧ ∫ x in Ioo (0 : ℝ) 1, f x = c := by
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h.1, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, h.2]

/-! ### The value of `h(0)` -/

/-- The integrand of `h(0)`: `-log (1 - ρ) log (1 - σ) (ρ - σ)² / (ρ σ τ)` on `(z, ρ, σ)`. -/
noncomputable def i10KabF0 (q : ℝ × ℝ × ℝ) : ℝ :=
  -(log (1 - q.2.1) * log (1 - q.2.2)) * (q.2.1 - q.2.2) ^ 2 /
    (q.2.1 * q.2.2 * i10Tau q.1 q.2.1 q.2.2)

theorem i10KabH_zero_eq {q : ℝ × ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    i10KabH 0 q = (i10KabF0 q : ℂ) := by
  obtain ⟨hz, hρ, hσ⟩ := hq
  have hτ : 0 < i10Tau q.1 q.2.1 q.2.2 := by unfold i10Tau; nlinarith [hz.1, hz.2, hρ.1, hσ.1]
  have hz0 : (q.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have hz1 : (1 : ℂ) - q.1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (by linarith [hz.2])
  have hρ0 : (q.2.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.1.ne'
  have hσ0 : (q.2.2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.1.ne'
  have hτ0 : (q.1 : ℂ) * q.2.1 + (1 - q.1) * q.2.2 ≠ 0 := by
    have := Complex.ofReal_ne_zero.mpr hτ.ne'
    unfold i10Tau at this; push_cast at this; exact this
  rw [i10KabH, i10D_zero hρ.2, i10D_zero hσ.2]
  simp only [i10W, i10Br, zero_sub, Complex.cpow_neg_one, i10KabF0, i10Tau]
  push_cast
  field_simp
  ring

theorem integral_inv_i10Tau {ρ σ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (hne : ρ ≠ σ) : ∫ z in Ioo (0 : ℝ) 1, 1 / i10Tau z ρ σ = (log ρ - log σ) / (ρ - σ) := by
  have hpos : ∀ z ∈ Icc (0 : ℝ) 1, 0 < i10Tau z ρ σ := fun z hz => by
    unfold i10Tau
    rcases le_total ρ σ with h | h
    · nlinarith [mul_nonneg (sub_nonneg.2 hz.2) (sub_nonneg.2 h), hρ.1]
    · nlinarith [mul_nonneg hz.1 (sub_nonneg.2 h), hσ.1]
  have hd : ∀ z ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun z => log (i10Tau z ρ σ) / (ρ - σ))
      (1 / i10Tau z ρ σ) z := by
    intro z hz
    rw [uIcc_of_le zero_le_one] at hz
    have hT : HasDerivAt (fun z => i10Tau z ρ σ) (ρ - σ) z := by
      unfold i10Tau
      have := ((hasDerivAt_id' z).mul_const ρ).add
        (((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id' z)).mul_const σ)
      convert this using 1; ring
    convert (hT.log (hpos z hz).ne').div_const (ρ - σ) using 1
    field_simp [sub_ne_zero.mpr hne]
  have hc : ContinuousOn (fun z => 1 / i10Tau z ρ σ) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.div continuousOn_const (by unfold i10Tau; fun_prop) fun z hz =>
      (hpos z hz).ne'
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  rw [show i10Tau 1 ρ σ = ρ by unfold i10Tau; ring, show i10Tau 0 ρ σ = σ by unfold i10Tau; ring]
  ring

/-- The `z`-integral of the integrand of `h(0)`. -/
theorem integral_i10KabF0_inner {ρ σ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ∫ z in Ioo (0 : ℝ) 1, i10KabF0 (z, (ρ, σ)) =
      log (1 - ρ) * log (1 - σ) * ((1 / ρ - 1 / σ) * (log ρ - log σ)) := by
  have e : ∀ z, i10KabF0 (z, (ρ, σ)) =
      (-(log (1 - ρ) * log (1 - σ)) * (ρ - σ) ^ 2 / (ρ * σ)) * (1 / i10Tau z ρ σ) := by
    intro z; simp only [i10KabF0]; rw [mul_one_div, div_div]
  have hρ0 := hρ.1.ne'
  have hσ0 := hσ.1.ne'
  simp only [e]
  rw [integral_const_mul]
  by_cases hne : ρ = σ
  · subst hne; simp
  · rw [integral_inv_i10Tau hρ hσ hne]
    have h1 : ρ - σ ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring

theorem integrableOn_i10KabF0 :
    IntegrableOn i10KabF0 (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have hC : IntegrableOn (fun q => (i10KabF0 q : ℂ))
      (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    (integrableOn_i10KabH (by simp)).congr_fun (fun q hq => i10KabH_zero_eq hq) hS
  simpa using hC.re

/-- The value of the outer double integral. -/
theorem integral_i10KabG :
    ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, log (1 - p.1) * log (1 - p.2) *
      ((1 / p.1 - 1 / p.2) * (log p.1 - log p.2)) =
      2 / 3 * π ^ 2 - π ^ 4 / 18 - 2 * zeta3 := by
  obtain ⟨i1, v1⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_log_mul_log_one_sub_div
  obtain ⟨i3, v3⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_log_one_sub_div
  obtain ⟨i4, v4⟩ := i10_ioo_of_interval intervalIntegrable_and_integral_log_mul_log_one_sub
  have i2 := i10_integrableOn_log_one_sub
  have v2 := i10_integral_log_one_sub
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have e : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, log (1 - p.1) * log (1 - p.2) *
      ((1 / p.1 - 1 / p.2) * (log p.1 - log p.2)) =
      (log p.1 * log (1 - p.1) / p.1) * log (1 - p.2) -
        (log (1 - p.1) / p.1) * (log p.2 * log (1 - p.2)) -
        (log p.1 * log (1 - p.1)) * (log (1 - p.2) / p.2) +
        log (1 - p.1) * (log p.2 * log (1 - p.2) / p.2) := by
    intro p hp
    have := hp.1.1.ne'
    have := hp.2.1.ne'
    field_simp
    ring
  rw [setIntegral_congr_fun hS e]
  rw [IntegrableOn] at i1 i2 i3 i4
  have j1 := i1.mul_prod i2
  have j2 := i3.mul_prod i4
  have j3 := i4.mul_prod i3
  have j4 := i2.mul_prod i1
  rw [volume_restrict_prod2, integral_add, integral_sub, integral_sub]
  rotate_left
  · exact j1
  · exact j2
  · exact j1.sub j2
  · exact j3
  · exact (j1.sub j2).sub j3
  · exact j4
  rw [integral_prod_mul (fun x : ℝ => log x * log (1 - x) / x) (fun y : ℝ => log (1 - y)),
    integral_prod_mul (fun x : ℝ => log (1 - x) / x) (fun y : ℝ => log y * log (1 - y)),
    integral_prod_mul (fun x : ℝ => log x * log (1 - x)) (fun y : ℝ => log (1 - y) / y),
    integral_prod_mul (fun x : ℝ => log (1 - x)) (fun y : ℝ => log y * log (1 - y) / y),
    v1, v2, v3, v4]
  ring

/-- **The value** `h(0) = 2π²/3 - π⁴/18 - 2ζ₃`. -/
theorem integral_i10KabH_zero :
    ∫ q in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i10KabH 0 q =
      ((2 / 3 * π ^ 2 - π ^ 4 / 18 - 2 * zeta3 : ℝ) : ℂ) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  rw [setIntegral_congr_fun hS fun q hq => i10KabH_zero_eq hq, integral_complex_ofReal]
  congr 1
  have hF := integrableOn_i10KabF0
  have hR : (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
      Measure (ℝ × ℝ × ℝ)) = (volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [IntegrableOn, hR] at hF
  rw [hR, ← integral_prod_swap, integral_prod (fun z => i10KabF0 z.swap) hF.swap]
  rw [← integral_i10KabG]
  refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp => ?_
  exact integral_i10KabF0_inner hp.1 hp.2

/-! ### The expansion -/

/-- **The target expansion of `K_ab`** through `ε²`. -/
noncomputable def i10KabLaurent (ε : ℂ) : ℂ :=
  (2 / 3 * (π : ℂ) ^ 2 - (π : ℂ) ^ 4 / 18 - 2 * (zeta3 : ℂ)) * ε ^ 2

/-- **The expansion of `K_ab`**: `K_ab = (2π²/3 - π⁴/18 - 2ζ₃) ε² + ε³ R`, `R` analytic. -/
theorem hasTruncLaurent_i10Kab : HasTruncLaurent i10Kab i10KabLaurent 3 := by
  set h := fun ε => ∫ q in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i10KabH ε q
    with hh
  have hd : DifferentiableOn ℂ h (Metric.ball 0 (1 / 40)) := fun ε hε =>
    (analyticOnNhd_i10KabH ε hε).differentiableAt.differentiableWithinAt
  have hds : DifferentiableOn ℂ (dslope h 0) (Metric.ball 0 (1 / 40)) :=
    (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 (by norm_num))).2 hd
  refine ⟨dslope h 0, hds.analyticAt (Metric.ball_mem_nhds 0 (by norm_num)), ?_⟩
  refine Eventually.of_forall fun ε => ?_
  have e := sub_smul_dslope h 0 ε
  rw [sub_zero, smul_eq_mul] at e
  have h0 : h 0 = ((2 / 3 * π ^ 2 - π ^ 4 / 18 - 2 * zeta3 : ℝ) : ℂ) := integral_i10KabH_zero
  rw [i10Kab_eq, i10KabLaurent]
  show ε ^ 2 * h ε = _
  rw [h0] at e
  push_cast at e
  linear_combination (-ε ^ 2) * e

end QED.ThreeLoopE
