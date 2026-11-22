/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R2

/-!
# Set (d), master `I₁₃`: the differential equation of the bubble coefficients

The bubble coefficients `βₖ(t) = ∫₀¹ gₖ(x, t) dx`, `gₖ = (-L)ᵏ/k!`,
`L = log (1 + x(1 - x) t)` (`QED.ThreeLoopD.i13BubR`), satisfy for `t > 0`

  `t (t + 4) βₖ₊₁'(t) = -2 βₖ₊₁(t) - t βₖ(t)`

(`QED.ThreeLoopD.hasDerivAt_i13BubR`). Differentiating under the integral sign,
`βₖ₊₁' = ∫₀¹ D`, `D = -x(1 - x)/f · gₖ`, `f = 1 + x(1 - x) t`, and with
`G(x) = (x - 1/2) gₖ₊₁(x, t)`, which vanishes at both ends, the integrands satisfy the pointwise
identity `t (t + 4) D = -t gₖ - 2 gₖ₊₁ + 2 G'`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i13BubR`: the differential equation.
* `QED.ThreeLoopD.i13BubC_eq_bubR`: `βₖ` is the coefficient `QED.ThreeLoopD.i13BubC`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped Nat

namespace QED.ThreeLoopD

/-- The integrand `gₖ(x, t) = (-log (1 + x(1 - x) t))ᵏ / k!` of the bubble coefficients. -/
noncomputable def i13Bg (k : ℕ) (t x : ℝ) : ℝ := (-Real.log (1 + x * (1 - x) * t)) ^ k / k !

/-- The real bubble coefficient `βₖ(t) = ∫₀¹ gₖ(x, t) dx`. -/
noncomputable def i13BubR (k : ℕ) (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, i13Bg k t x

theorem i13BubC_eq_bubR (t : ℝ) (k : ℕ) : i13BubC t k = (i13BubR k t : ℂ) := by
  unfold i13BubC i13BubR i13Bg
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_complex_ofReal]
  push_cast
  rfl

/-- `d/dy (-log g)ᵏ⁺¹/(k + 1)! = (-log g)ᵏ/k! · (-g'/g)`. -/
theorem i13_hasDerivAt_negLog_pow {g : ℝ → ℝ} {g' y : ℝ} (hg : HasDerivAt g g' y)
    (hpos : 0 < g y) (k : ℕ) :
    HasDerivAt (fun y => (-Real.log (g y)) ^ (k + 1) / ((k + 1) ! : ℝ))
      ((-Real.log (g y)) ^ k / (k ! : ℝ) * (-(g' / g y))) y := by
  have h := ((hg.log hpos.ne').neg.pow (k + 1)).div_const ((k + 1) ! : ℝ)
  convert h using 1
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  field_simp
  simp only [Pi.neg_apply]
  ring

theorem i13Bg_succ_hasDerivAt_x {t x : ℝ} (hpos : 0 < 1 + x * (1 - x) * t) (k : ℕ) :
    HasDerivAt (i13Bg (k + 1) t)
      (i13Bg k t x * (-((1 - 2 * x) * t / (1 + x * (1 - x) * t)))) x := by
  have hg : HasDerivAt (fun x : ℝ => 1 + x * (1 - x) * t) ((1 - 2 * x) * t) x := by
    have := (((hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub 1)).mul_const t).const_add 1
    convert this using 1
    ring
  exact i13_hasDerivAt_negLog_pow hg hpos k

theorem i13Bg_succ_hasDerivAt_t {s x : ℝ} (hpos : 0 < 1 + x * (1 - x) * s) (k : ℕ) :
    HasDerivAt (fun s => i13Bg (k + 1) s x)
      (i13Bg k s x * (-(x * (1 - x) / (1 + x * (1 - x) * s)))) s := by
  have hg : HasDerivAt (fun s : ℝ => 1 + x * (1 - x) * s) (x * (1 - x)) s := by
    simpa using ((hasDerivAt_id' s).const_mul (x * (1 - x))).const_add 1
  exact i13_hasDerivAt_negLog_pow hg hpos k

theorem i13_continuousOn_Bg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (i13Bg k t) (uIcc 0 1) := by
  rw [uIcc_of_le zero_le_one]
  unfold i13Bg
  exact (((ContinuousOn.log (by fun_prop) fun x hx => (i13_base_pos hx ht).ne').neg).pow
    k).div_const _

theorem i13_log_base_nonneg {x t : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) :
    0 ≤ Real.log (1 + x * (1 - x) * t) := by
  have : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
  exact Real.log_nonneg (by nlinarith)

theorem i13_log_base_le {x t : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) :
    Real.log (1 + x * (1 - x) * t) ≤ t := by
  have h1 : x * (1 - x) ≤ 1 := by nlinarith [hx.1, hx.2]
  have h0 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
  calc Real.log (1 + x * (1 - x) * t) ≤ x * (1 - x) * t := by
        have := Real.log_le_sub_one_of_pos (i13_base_pos hx ht)
        linarith
    _ ≤ t := by nlinarith

theorem i13_abs_Bg_le (k : ℕ) {x t : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) :
    |i13Bg k t x| ≤ t ^ k := by
  unfold i13Bg
  rw [abs_div, abs_pow, abs_neg, abs_of_nonneg (i13_log_base_nonneg hx ht), Nat.abs_cast]
  calc Real.log (1 + x * (1 - x) * t) ^ k / (k ! : ℝ) ≤ Real.log (1 + x * (1 - x) * t) ^ k :=
        div_le_self (pow_nonneg (i13_log_base_nonneg hx ht) _)
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k))
    _ ≤ t ^ k := pow_le_pow_left₀ (i13_log_base_nonneg hx ht) (i13_log_base_le hx ht) k

theorem i13_Bg_zero_endpoints (k : ℕ) (t : ℝ) : i13Bg (k + 1) t 0 = 0 ∧ i13Bg (k + 1) t 1 = 0 := by
  unfold i13Bg
  constructor <;> simp

/-- The pointwise identity `t (t + 4) D = -t gₖ - 2 gₖ₊₁ + 2 G'`. -/
theorem i13_bub_pointwise (k : ℕ) {t x : ℝ} (ht : 0 < t) (hpos : 0 < 1 + x * (1 - x) * t) :
    i13Bg k t x * (-(x * (1 - x) / (1 + x * (1 - x) * t))) =
      (-t * i13Bg k t x - 2 * i13Bg (k + 1) t x + 2 * (i13Bg (k + 1) t x +
        (x - 1 / 2) * (i13Bg k t x * (-((1 - 2 * x) * t / (1 + x * (1 - x) * t)))))) /
        (t * (t + 4)) := by
  have h1 : 1 + x * (1 - x) * t ≠ 0 := hpos.ne'
  field_simp
  ring

/-- **The bubble differential equation** `t (t + 4) βₖ₊₁' = -2 βₖ₊₁ - t βₖ`, `t > 0`. -/
theorem hasDerivAt_i13BubR (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (i13BubR (k + 1)) ((-2 * i13BubR (k + 1) t - t * i13BubR k t) / (t * (t + 4)))
      t := by
  set D : ℝ → ℝ → ℝ := fun s x => i13Bg k s x * (-(x * (1 - x) / (1 + x * (1 - x) * s)))
  have hball : Metric.ball t (t / 2) ∈ 𝓝 t := Metric.ball_mem_nhds t (by linarith)
  have hpos_ball : ∀ s ∈ Metric.ball t (t / 2), 0 < s := fun s hs => by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    linarith [(abs_lt.1 hs).1]
  have hle_ball : ∀ s ∈ Metric.ball t (t / 2), s ≤ 2 * t := fun s hs => by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    linarith [(abs_lt.1 hs).2]
  have hIoc : ∀ x ∈ uIoc (0 : ℝ) 1, x ∈ Icc (0 : ℝ) 1 := fun x hx => by
    rw [uIoc_of_le zero_le_one] at hx
    exact Ioc_subset_Icc_self hx
  have hcontD : ∀ s, 0 ≤ s → ContinuousOn (D s) (uIcc 0 1) := fun s hs => by
    refine (i13_continuousOn_Bg k hs).mul (ContinuousOn.neg (ContinuousOn.div (by fun_prop)
      (by fun_prop) fun x hx => (i13_base_pos ?_ hs).ne'))
    rwa [uIcc_of_le zero_le_one] at hx
  have hF'm : AEStronglyMeasurable (D t) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    ((hcontD t ht.le).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hbd : ∀ᵐ x ∂volume, x ∈ uIoc (0 : ℝ) 1 → ∀ s ∈ Metric.ball t (t / 2),
      ‖D s x‖ ≤ (2 * t) ^ k := by
    refine Eventually.of_forall fun x hx s hs => ?_
    have hx' := hIoc x hx
    have hs0 := hpos_ball s hs
    have hf := i13_base_pos hx' hs0.le
    have h0 : 0 ≤ x * (1 - x) := mul_nonneg hx'.1 (by linarith [hx'.2])
    have hq : x * (1 - x) / (1 + x * (1 - x) * s) ≤ 1 := by
      rw [div_le_one hf]; nlinarith [hx'.2, hx'.1]
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (div_nonneg h0 hf.le)]
    calc |i13Bg k s x| * (x * (1 - x) / (1 + x * (1 - x) * s)) ≤ s ^ k * 1 :=
          mul_le_mul (i13_abs_Bg_le k hx' hs0.le) hq (by positivity) (by positivity)
      _ ≤ (2 * t) ^ k := by rw [mul_one]; exact pow_le_pow_left₀ hs0.le (hle_ball s hs) k
  have hdf : ∀ᵐ x ∂volume, x ∈ uIoc (0 : ℝ) 1 → ∀ s ∈ Metric.ball t (t / 2),
      HasDerivAt (fun s => i13Bg (k + 1) s x) (D s x) s := by
    refine Eventually.of_forall fun x hx s hs => ?_
    exact i13Bg_succ_hasDerivAt_t (i13_base_pos (hIoc x hx) (hpos_ball s hs).le) k
  obtain ⟨-, hd⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := fun s x => i13Bg (k + 1) s x) (F' := D)
    (bound := fun _ => (2 * t) ^ k) hball
    (Eventually.of_forall fun s =>
      (by unfold i13Bg; fun_prop : Measurable (i13Bg (k + 1) s)).aestronglyMeasurable)
    ((i13_continuousOn_Bg (k + 1) ht.le).intervalIntegrable) hF'm hbd intervalIntegrable_const
    hdf
  have e : ∫ x in (0 : ℝ)..1, D t x = ∫ x in (0 : ℝ)..1,
      (-t * i13Bg k t x - 2 * i13Bg (k + 1) t x + 2 * (i13Bg (k + 1) t x +
        (x - 1 / 2) * (i13Bg k t x * (-((1 - 2 * x) * t / (1 + x * (1 - x) * t)))))) /
        (t * (t + 4)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    exact i13_bub_pointwise k ht (i13_base_pos hx ht.le)
  have hG : ∫ x in (0 : ℝ)..1, (i13Bg (k + 1) t x +
      (x - 1 / 2) * (i13Bg k t x * (-((1 - 2 * x) * t / (1 + x * (1 - x) * t))))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => (x - 1 / 2) *
      i13Bg (k + 1) t x)]
    · simp [(i13_Bg_zero_endpoints k t).1, (i13_Bg_zero_endpoints k t).2]
    · intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      have := ((hasDerivAt_id' x).sub_const (1 / 2)).mul
        (i13Bg_succ_hasDerivAt_x (i13_base_pos hx ht.le) k)
      convert this using 1
      ring
    · refine ContinuousOn.intervalIntegrable ?_
      refine (i13_continuousOn_Bg (k + 1) ht.le).add (ContinuousOn.mul (by fun_prop)
        ((i13_continuousOn_Bg k ht.le).mul (ContinuousOn.neg (ContinuousOn.div (by fun_prop)
        (by fun_prop) fun x hx => (i13_base_pos ?_ ht.le).ne'))))
      rwa [uIcc_of_le zero_le_one] at hx
  have hi : ∀ j, IntervalIntegrable (i13Bg j t) volume 0 1 := fun j =>
    (i13_continuousOn_Bg j ht.le).intervalIntegrable
  have hiG : IntervalIntegrable (fun x => i13Bg (k + 1) t x +
      (x - 1 / 2) * (i13Bg k t x * (-((1 - 2 * x) * t / (1 + x * (1 - x) * t)))))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (i13_continuousOn_Bg (k + 1) ht.le).add (ContinuousOn.mul (by fun_prop)
      ((i13_continuousOn_Bg k ht.le).mul (ContinuousOn.neg (ContinuousOn.div (by fun_prop)
      (by fun_prop) fun x hx => (i13_base_pos ?_ ht.le).ne'))))
    rwa [uIcc_of_le zero_le_one] at hx
  rw [e, intervalIntegral.integral_div, intervalIntegral.integral_add
    (((hi k).const_mul (-t)).sub ((hi (k + 1)).const_mul 2)) (hiG.const_mul 2),
    intervalIntegral.integral_sub ((hi k).const_mul (-t)) ((hi (k + 1)).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hG] at hd
  unfold i13BubR
  convert hd using 2
  ring

theorem abs_i13BubR_le (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : |i13BubR k t| ≤ t ^ k := by
  unfold i13BubR
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := t ^ k)
    (f := i13Bg k t) fun x hx => by
      rw [uIoc_of_le zero_le_one] at hx
      rw [Real.norm_eq_abs]
      exact i13_abs_Bg_le k (Ioc_subset_Icc_self hx) ht
  simpa using this

theorem i13BubR_one {t : ℝ} (ht : 0 < t) : i13BubR 1 t = i13Be1r t := by
  have h := i13BubC_one ht
  rw [i13BubC_eq_bubR] at h
  exact_mod_cast h

theorem i13BubR_two {t : ℝ} (ht : 0 < t) : i13BubR 2 t = i13Be2r t := by
  have h := i13BubC_two ht
  rw [i13BubC_eq_bubR] at h
  exact_mod_cast h

end QED.ThreeLoopD
