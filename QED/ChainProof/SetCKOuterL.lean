/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKOuterInt
public import QED.ChainProof.SetCKLPair
public import QED.TwoLoop.UnitLCloseLimit
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Set (c), Stage K: the outer placement as a single integral

Helper level (no frozen statement). For `t > 0`,

`lOuter t = ∫₀¹ Φ_out(x, h_t(x)) dx - (3/2) F₂(t)`, `h_t(x) = (x² + (1-x) t)/x`

(`lOuter_eq`). The integrand of the outer placement is bounded on the unit square by
`4 (1 + 1/h₀)²`, `h₀ = (3/4) min(1, t)` (`abs_outerG_le`, `hOut_ge`), so the order of integration
can be exchanged, and for every `x ∈ (0, 1)` other than `x = t` (where `h_t(x) = 1`) the
`Y`-integral is `Φ_out` (`integral_outerG`).
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set MeasureTheory Function QED.TwoLoop.UnitLLink

/-- The outer mass function `h_t(x) = (x² + (1-x) t)/x`. -/
noncomputable def hOut (t x : ℝ) : ℝ := ladderInnerMass 1 (√t) x / x

theorem hOut_eq {t x : ℝ} (ht : 0 ≤ t) : hOut t x = (x ^ 2 + (1 - x) * t) / x := by
  unfold hOut ladderInnerMass
  rw [sq_sqrt ht]
  ring

theorem hOut_ge {t x : ℝ} (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    3 / 4 * min 1 t ≤ hOut t x := by
  rw [hOut_eq ht.le]
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hm0 : 0 < min 1 t := lt_min one_pos ht
  have hm1 : min 1 t ≤ 1 := min_le_left _ _
  have hmt : min 1 t ≤ t := min_le_right _ _
  have hnum : 3 / 4 * min 1 t ≤ x ^ 2 + (1 - x) * t := by
    have : (1 - x) * min 1 t ≤ (1 - x) * t := mul_le_mul_of_nonneg_left hmt hx1.le
    have : x ^ 2 * min 1 t ≤ x ^ 2 := by nlinarith
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hpos : 0 ≤ x ^ 2 + (1 - x) * t := by positivity
  calc 3 / 4 * min 1 t ≤ x ^ 2 + (1 - x) * t := hnum
    _ ≤ (x ^ 2 + (1 - x) * t) / x := by
      rw [le_div_iff₀ hx0]
      nlinarith [hx.2]

theorem hOut_ne_one {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ≠ t) :
    hOut t x ≠ 1 := by
  rw [hOut_eq ht]
  intro h
  have hx0 := hx.1.ne'
  rw [div_eq_one_iff_eq hx0] at h
  have : (x - 1) * (x - t) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith [hx.2]
  · exact hxt (by linarith)

/-- The uniform bound on the outer-placement integrand at photon mass² `t`. -/
theorem abs_ladderGm_zero_le {t Y x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    |ladderGm (√t) 0 Y x| ≤ 4 * (1 + 1 / (3 / 4 * min 1 t)) ^ 2 := by
  have hh0 : 0 < 3 / 4 * min 1 t := by have := lt_min one_pos ht; positivity
  have hge := hOut_ge ht hx
  have hh : 0 < hOut t x := lt_of_lt_of_le hh0 hge
  rw [ladderGm_zero_eq_outerG]
  refine (abs_outerG_le hx hh hY).trans ?_
  have : 1 / hOut t x ≤ 1 / (3 / 4 * min 1 t) := one_div_le_one_div_of_le hh0 hge
  have h1 : 0 ≤ 1 + 1 / hOut t x := by positivity
  gcongr

theorem integrable_ladderGm_zero {t : ℝ} (ht : 0 < t) :
    Integrable (uncurry fun Y x => ladderGm (√t) 0 Y x)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  refine Integrable.mono' (g := fun _ => 4 * (1 + 1 / (3 / 4 * min 1 t)) ^ 2)
    (integrable_const _) (measurable_ladderGm_uncurry _ _).aestronglyMeasurable ?_
  rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
  refine Filter.Eventually.of_forall fun p hp => ?_
  rw [Real.norm_eq_abs]
  exact abs_ladderGm_zero_le ht hp.1 hp.2

/-- For `x ∈ (0, 1)`, `x ≠ t`, the `Y`-integral of the outer placement is `Φ_out`. -/
theorem integral_ladderGm_zero_Y {t x : ℝ} (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ≠ t) :
    ∫ Y in (0 : ℝ)..1, ladderGm (√t) 0 Y x = phiOut x (hOut t x) := by
  have hh0 : 0 < 3 / 4 * min 1 t := by have := lt_min one_pos ht; positivity
  have hh : 0 < hOut t x := lt_of_lt_of_le hh0 (hOut_ge ht hx)
  have hmeas : Measurable fun Y => ladderGm (√t) 0 Y x :=
    (measurable_ladderGm_uncurry _ _).comp (measurable_id.prodMk measurable_const)
  have hint := (intervalIntegrable_of_abs_le hmeas
    (intervalIntegrable_const (c := 4 * (1 + 1 / (3 / 4 * min 1 t)) ^ 2))
    fun Y hY => abs_ladderGm_zero_le ht hY hx).1
  simp only [ladderGm_zero_eq_outerG] at hint ⊢
  exact integral_outerG hx.1.ne' hh (hOut_ne_one ht.le hx hxt) hint

/-- **The outer placement as a single integral.** -/
theorem lOuter_eq {t : ℝ} (ht : 0 < t) :
    lOuter t = (∫ x in (0 : ℝ)..1, phiOut x (hOut t x)) - 3 / 2 * oneLoopF2 1 (√t) := by
  unfold lOuter
  congr 1
  have hswap := integral_integral_swap (integrable_ladderGm_zero ht)
  simp only [← setIntegral_Ioo_eq_intervalIntegral]
  rw [hswap]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [Measure.ae_ne volume t] with x hxt hx
  rw [setIntegral_Ioo_eq_intervalIntegral]
  exact integral_ladderGm_zero_Y ht hx hxt

end QED.ChainProof.SetCK
