/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetASpectral
public import QED.Chain.VPChainPiHat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (a): from the photon-line integral to the dispersive form

Helper analysis for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md`. It is **not** frozen.

With `Π̂⁽⁴⁾ = QED.Chain.piHat4`, the set (a) coefficient of `(α/π)³` is, in the normalization of
set (b) (`QED.Chain.integral_setB`, one-loop vertex with the inserted photon at the Euclidean
point `s = x²/(1-x)`), `∫₀¹ (1-x) Π̂⁽⁴⁾(x²/(1-x)) dx` (Kaptari et al. 2025, arXiv:2508.05119,
eq. (4) with `Π̃ = -Π̂⁽⁴⁾`). Exchanging the `x`- and `δ`-integrals gives eq. (25) at `r = 1`:
`∫₀¹ 2δ/(1-δ²) ρ⁽⁴⁾(δ) K̃(δ) dδ` with `K̃(δ) = ∫₀¹ x²(1-x)/(x² + (1-x)·4/(1-δ²)) dx` (eq. (3)).

## Route

On `(0,1)²` the integrand `F(δ,x) = 2δ/(1-δ²) ρ⁽⁴⁾(δ) x²(1-x)/(x² + (1-x)·4/(1-δ²))` satisfies
`|F(δ,x)| ≤ |ρ⁽⁴⁾(δ)|/2`, and `ρ⁽⁴⁾` is integrable (`QED.Chain.integrableOn_ksRho`), so Fubini
applies. For fixed `x`, `(1-x)·s/(s+c) = x²(1-x)/(x² + (1-x)c)`
(`QED.Chain.one_sub_mul_photonVar_div`).

## Main statements

* `intervalIntegrable_setA`: `x ↦ (1-x) Π̂⁽⁴⁾(x²/(1-x))` is interval integrable on `[0,1]`.
* `intervalIntegrable_setADispersive`: so is the dispersive integrand in `δ`.
* `integral_setA_eq_dispersive`: the two integrals agree.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.Chain

/-- The one-loop vertex kernel at photon mass² `4/(1-δ²)`. -/
noncomputable def setAKer (δ x : ℝ) : ℝ := x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2)))

/-- The double integrand of set (a) on `(0,1)²`. -/
noncomputable def setAF (δ x : ℝ) : ℝ := 2 * δ / (1 - δ ^ 2) * ksRho δ * setAKer δ x

/-- For `δ, x ∈ (0,1)` the weight `2δ/(1-δ²) · K(δ,x)` lies in `[0, 1/2]`. -/
theorem setAWeight_mem {δ x : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ 2 * δ / (1 - δ ^ 2) * setAKer δ x ∧ 2 * δ / (1 - δ ^ 2) * setAKer δ x ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := hδ
  obtain ⟨hx0, hx1⟩ := hx
  have hq : 0 < 1 - δ ^ 2 := by nlinarith
  have hm : 0 < 1 - x := by linarith
  have he : 2 * δ / (1 - δ ^ 2) * setAKer δ x =
      2 * δ * (x ^ 2 * (1 - x)) / ((1 - δ ^ 2) * x ^ 2 + 4 * (1 - x)) := by
    unfold setAKer
    field_simp
  rw [he]
  have hd : 0 < (1 - δ ^ 2) * x ^ 2 + 4 * (1 - x) := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ hd (by norm_num)]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hq.le (sq_nonneg x), mul_pos h0 hm, mul_nonneg (mul_pos h0 hm).le
    (sub_nonneg.2 hx2)]

theorem setAKer_den_pos {δ x : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2)) := by
  have hq : 0 < 1 - δ ^ 2 := by nlinarith [hδ.1, hδ.2]
  have : 0 < 1 - x := by linarith [hx.2]
  have := hx.1
  positivity

theorem continuousOn_setAF : ContinuousOn (Function.uncurry setAF) (Ioo 0 1 ×ˢ Ioo 0 1) := by
  have hρ : ContinuousOn (fun p : ℝ × ℝ => ksRho p.1) (Ioo 0 1 ×ˢ Ioo 0 1) :=
    continuousOn_ksRho.comp continuousOn_fst fun p hp => hp.1
  have hq : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, (1 : ℝ) - p.1 ^ 2 ≠ 0 := fun p hp => by
    nlinarith [hp.1.1, hp.1.2]
  have hw : ContinuousOn (fun p : ℝ × ℝ => 2 * p.1 / (1 - p.1 ^ 2)) (Ioo 0 1 ×ˢ Ioo 0 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) hq
  have hk : ContinuousOn (fun p : ℝ × ℝ => setAKer p.1 p.2) (Ioo 0 1 ×ˢ Ioo 0 1) := by
    unfold setAKer
    refine ContinuousOn.div (by fun_prop) ?_ fun p hp => (setAKer_den_pos hp.1 hp.2).ne'
    exact (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ 2) _).add
      ((by fun_prop : ContinuousOn (fun p : ℝ × ℝ => 1 - p.2) _).mul
        (ContinuousOn.div continuousOn_const (by fun_prop) hq))
  exact (hw.mul hρ).mul hk

/-- The double integrand is integrable on `(0,1)²`. -/
theorem integrable_setAF :
    Integrable (Function.uncurry setAF)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hρ : Integrable (fun δ => ‖ksRho δ‖ / 2) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have h := (integrableOn_ksRho.mono_set Ioo_subset_Ioc_self).norm.div_const 2
    exact h
  refine Integrable.mono' (hρ.comp_fst _) ?_ ?_
  · rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact continuousOn_setAF.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)
  · rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo) ?_
    rintro ⟨δ, x⟩ ⟨hδ, hx⟩
    obtain ⟨hw0, hw1⟩ := setAWeight_mem hδ hx
    simp only [Function.uncurry_apply_pair, setAF]
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      show 2 * δ / (1 - δ ^ 2) * ksRho δ * setAKer δ x =
        (2 * δ / (1 - δ ^ 2) * setAKer δ x) * ksRho δ by ring, abs_mul, abs_of_nonneg hw0]
    calc (2 * δ / (1 - δ ^ 2) * setAKer δ x) * |ksRho δ| ≤ 1 / 2 * |ksRho δ| :=
          mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)
      _ = |ksRho δ| / 2 := by ring

/-- For `0 < x < 1`, `(1-x) Π̂⁽⁴⁾(x²/(1-x)) = ∫₀¹ F(δ,x) dδ`. -/
theorem one_sub_mul_piHat4_photonVar {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) * piHat4 (x ^ 2 / (1 - x)) = ∫ δ in (0 : ℝ)..1, setAF δ x := by
  unfold piHat4
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_Ioo_Ioc] with δ hδ
  have hc : 0 ≤ 4 / (1 - δ ^ 2) := div_nonneg (by norm_num) (by nlinarith [hδ.1, hδ.2])
  unfold setAF setAKer
  rw [← one_sub_mul_photonVar_div hx hc]
  ring

/-- For `0 < δ < 1`, `∫₀¹ F(δ,x) dx = 2δ/(1-δ²) ρ⁽⁴⁾(δ) K̃(δ)`. -/
theorem integral_setAF_x (δ : ℝ) :
    ∫ x in (0 : ℝ)..1, setAF δ x = 2 * δ / (1 - δ ^ 2) * ksRho δ * ∫ x in (0 : ℝ)..1,
      x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2))) := by
  unfold setAF setAKer
  rw [intervalIntegral.integral_const_mul]

theorem interval_eq_Ioo (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, f x = ∫ x in Ioo (0 : ℝ) 1, f x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- The set (a) photon-line integrand is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_setA :
    IntervalIntegrable (fun x => (1 - x) * piHat4 (x ^ 2 / (1 - x))) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one, IntegrableOn,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  refine integrable_setAF.integral_prod_right.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simp only [Function.uncurry_apply_pair]
  rw [one_sub_mul_piHat4_photonVar hx, interval_eq_Ioo]

/-- The dispersive integrand of eq. (25) is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_setADispersive :
    IntervalIntegrable (fun δ => 2 * δ / (1 - δ ^ 2) * ksRho δ * ∫ x in (0 : ℝ)..1,
      x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2)))) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one, IntegrableOn,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  refine integrable_setAF.integral_prod_left.congr (Eventually.of_forall fun δ => ?_)
  simp only [Function.uncurry_apply_pair]
  rw [← integral_setAF_x, interval_eq_Ioo]

/-- **Fubini for set (a).** `∫₀¹ (1-x) Π̂⁽⁴⁾(x²/(1-x)) dx = ∫₀¹ 2δ/(1-δ²) ρ⁽⁴⁾(δ) K̃(δ) dδ`
(Kaptari et al. 2025, eq. (25) at `r = 1`). -/
theorem integral_setA_eq_dispersive :
    ∫ x in (0 : ℝ)..1, (1 - x) * piHat4 (x ^ 2 / (1 - x)) =
      ∫ δ in (0 : ℝ)..1, 2 * δ / (1 - δ ^ 2) * ksRho δ * ∫ x in (0 : ℝ)..1,
        x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2))) := by
  rw [interval_eq_Ioo, interval_eq_Ioo]
  have h1 : ∫ x in Ioo (0 : ℝ) 1, (1 - x) * piHat4 (x ^ 2 / (1 - x)) =
      ∫ x in Ioo (0 : ℝ) 1, ∫ δ in Ioo (0 : ℝ) 1, setAF δ x := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [one_sub_mul_piHat4_photonVar hx, interval_eq_Ioo]
  have h2 : ∫ δ in Ioo (0 : ℝ) 1, 2 * δ / (1 - δ ^ 2) * ksRho δ * (∫ x in (0 : ℝ)..1,
        x ^ 2 * (1 - x) / (x ^ 2 + (1 - x) * (4 / (1 - δ ^ 2)))) =
      ∫ δ in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, setAF δ x := by
    refine setIntegral_congr_fun measurableSet_Ioo fun δ _ => ?_
    rw [← integral_setAF_x, interval_eq_Ioo]
  rw [h1, h2]
  exact (integral_integral_swap integrable_setAF).symm

end QED.Chain
