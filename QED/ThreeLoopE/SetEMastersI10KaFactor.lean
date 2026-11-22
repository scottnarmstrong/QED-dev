/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI10KabAn
public import QED.ThreeLoopD.SetDMastersLaurent
import Mathlib.Analysis.Complex.Liouville
import QED.Polylog.ExtraIntegralsC
import QED.ThreeLoopD.SetDMastersI9KValB
import QED.ThreeLoopE.SetEMastersI10KabVal

/-!
# Difference quotient for the once-weighted remainder of the master `I₁₀`

The two vanishing factors in the defining integrand of `K_a` give an exact
factorization by `ε²`. The divided integrand is defined pointwise at zero
using the same continued difference quotient as for `K_ab`. A power bound
at each joining endpoint gives a uniform integrable majorant. Cauchy's
estimate then justifies differentiation under the integral. The quadratic
coefficient is evaluated by integrating the joining variable first.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric QED.ThreeLoopD QED.DimReg
open Complex hiding log log_one log_inv log_mul

namespace QED.ThreeLoopE

/-- The divided difference `((1 - x) ^ ε - 1) / ε`, continued to zero. -/
noncomputable def i10KaD (ε : ℂ) (x : ℝ) : ℂ := -i10D (-ε) x

/-- The bracket of `K_a` divided by `ε`, with its pointwise continuation. -/
noncomputable def i10KaB (ε : ℂ) (z r : ℝ) : ℂ :=
  (i10KaD ε (z * (1 - r)) - i10KaD ε (1 - z * r)) / (1 - z : ℂ) +
    (1 - z : ℂ) * i10KaD ε (1 - z * r) - (z : ℂ) * (r : ℂ) ^ (ε - 1)

/-- The integrand of `K_a / ε²`, continued pointwise to zero. -/
noncomputable def i10KaH (ε : ℂ) (q : ℝ × ℝ) : ℂ :=
  i10D ε q.2 * i10W ε q.1 * i10KaB ε q.1 q.2

theorem i10Ka_eq (ε : ℂ) :
    i10Ka ε =
      ε ^ 2 * ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10KaH ε q := by
  rw [i10Ka, ← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro q _
  dsimp only
  rw [i10A_sub_one, i10KaH, i10KaB]
  have h (x : ℝ) : (((1 - x : ℝ) : ℂ) ^ ε) - 1 = ε * i10KaD ε x := by
    simpa only [i10A, neg_neg, i10KaD, mul_neg, neg_mul] using i10A_sub_one (-ε) x
  have h₁ := h (q.1 * (1 - q.2))
  have h₂ := h (1 - q.1 * q.2)
  rw [sub_sub_cancel] at h₂
  rw [show (((1 - q.1 * (1 - q.2) : ℝ) : ℂ) ^ ε) -
      (((q.1 * q.2 : ℝ) : ℂ) ^ ε) =
      ε * (i10KaD ε (q.1 * (1 - q.2)) - i10KaD ε (1 - q.1 * q.2)) by
    rw [mul_sub ε, ← h₁, ← h₂]
    ring]
  rw [show 1 - (((q.1 * q.2 : ℝ) : ℂ) ^ ε) = -(ε * i10KaD ε (1 - q.1 * q.2)) by
    rw [← h₂]
    ring]
  ring

theorem measurable_i10KaH (ε : ℂ) : Measurable (i10KaH ε) := by
  unfold i10KaH i10KaB i10KaD i10W
  have h := measurable_i10D ε
  have h' := measurable_i10D (-ε)
  fun_prop (disch := assumption)

theorem differentiable_i10KaH {q : ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    Differentiable ℂ fun ε => i10KaH ε q := by
  obtain ⟨hz, hr⟩ := hq
  have h₁ : q.1 * (1 - q.2) < 1 := by nlinarith [hz.1, hz.2, hr.1]
  have h₂ : 1 - q.1 * q.2 < 1 := by nlinarith [mul_pos hz.1 hr.1]
  have hc (x : ℝ) (hx : x ≠ 0) (ε : ℂ) :
      DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ (w - 1)) ε :=
    (differentiableAt_id.sub_const _).const_cpow (Or.inl (ofReal_ne_zero.mpr hx))
  have hd (x : ℝ) (hx : x < 1) :
      Differentiable ℂ fun w => i10KaD w x :=
    ((differentiable_i10D hx).comp differentiable_neg).neg
  intro ε
  unfold i10KaH i10KaB i10W
  exact ((differentiable_i10D hr.2 ε).mul (hc _ (i9_c_pos hz).ne' ε)).mul
    ((((hd _ h₁ ε).sub (hd _ h₂ ε)).div_const _).add
      ((hd _ h₂ ε).const_mul _) |>.sub ((hc _ hr.1.ne' ε).const_mul _))

theorem i10KaB_zero {z r : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    i10KaB 0 z r =
      ((Real.log (1 - z * (1 - r)) : ℂ) - (Real.log (z * r) : ℂ)) / (1 - z : ℂ) +
        (1 - z : ℂ) * (Real.log (z * r) : ℂ) - (z : ℂ) / r := by
  have h₁ : z * (1 - r) < 1 := by nlinarith [hz.1, hz.2, hr.1]
  have h₂ : 1 - z * r < 1 := by nlinarith [mul_pos hz.1 hr.1]
  rw [i10KaB, i10KaD, i10KaD, neg_zero, i10D_zero h₁, i10D_zero h₂, sub_sub_cancel,
    zero_sub, cpow_neg_one]
  ring

/-- Exact average of the power derivative between the two arguments in the divided bracket. -/
theorem i10KaB_eq_average {ε : ℂ} {z r : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    i10KaB ε z r =
      ((∫ t in z * r..1 - z * (1 - r), (t : ℂ) ^ (ε - 1)) / (1 - z : ℂ) -
        (r : ℂ) ^ (ε - 1)) +
      (1 - z : ℂ) * (i10KaD ε (1 - z * r) + (r : ℂ) ^ (ε - 1)) := by
  have hp := mul_pos hz.1 hr.1
  have hq : z * r ≤ 1 - z * (1 - r) := by nlinarith [hz.2]
  have hc (e : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ e)
      (uIcc (z * r) (1 - z * (1 - r))) := by
    rw [uIcc_of_le hq]
    intro t ht
    have ht' : 0 < t := hp.trans_le ht.1
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr ht'.ne')).continuousWithinAt
  have heq : (∫ t in z * r..1 - z * (1 - r), (t : ℂ) ^ (ε - 1)) =
      i10KaD ε (z * (1 - r)) - i10KaD ε (1 - z * r) := by
    by_cases he : ε = 0
    · subst ε
      have ha : z * (1 - r) < 1 := by nlinarith [hz.2, hp]
      have hb : 1 - z * r < 1 := by linarith
      rw [i10KaD, i10KaD, neg_zero, i10D_zero ha, i10D_zero hb, sub_sub_cancel]
      have hd : ∀ t ∈ uIcc (z * r) (1 - z * (1 - r)),
          HasDerivAt (fun x : ℝ => (Real.log x : ℂ)) ((t : ℂ) ^ ((0 : ℂ) - 1)) t := by
        rw [uIcc_of_le hq]
        intro t ht
        have hn := (hp.trans_le ht.1).ne'
        have hh := ofRealCLM.hasFDerivAt.comp_hasDerivAt t (Real.hasDerivAt_log hn)
        change HasDerivAt (fun x : ℝ => (Real.log x : ℂ)) ((t⁻¹ : ℝ) : ℂ) t at hh
        simpa only [zero_sub, cpow_neg_one, ofReal_inv] using hh
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc _).intervalIntegrable]
      ring
    · have hd : ∀ t ∈ uIcc (z * r) (1 - z * (1 - r)),
          HasDerivAt (fun x : ℝ => (x : ℂ) ^ ε / ε) ((t : ℂ) ^ (ε - 1)) t := by
        rw [uIcc_of_le hq]
        intro t ht
        convert (hasDerivAt_ofReal_cpow_const (hp.trans_le ht.1).ne' he).div_const ε using 1
        field_simp [he]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc _).intervalIntegrable]
      have hh (x : ℝ) : i10KaD ε x = ((((1 - x : ℝ) : ℂ) ^ ε) - 1) / ε := by
        rw [i10KaD, i10D_of_ne (neg_ne_zero.mpr he), neg_neg, div_neg, neg_neg]
      rw [hh, hh, sub_sub_cancel]
      ring
  rw [i10KaB, heq]
  ring

private theorem norm_i10KaPower_sub_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {r t d : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Icc (r / 2) 1) (hd : |t - r| ≤ d) :
    ‖(t : ℂ) ^ (ε - 1) - (r : ℂ) ^ (ε - 1)‖ ≤
      9 * (d ^ (1 / 2 : ℝ) * r ^ (-(31 / 20) : ℝ)) := by
  have hp : 0 < r / 2 := by linarith [hr.1]
  have ht' := hp.trans_le ht.1
  have hd' := (abs_nonneg _).trans hd
  have hre := (i9_eps_facts hε).2.2.1
  have hα : -(21 / 20 : ℝ) ≤ (ε - 1).re := by simp; linarith
  have hr0 := Real.rpow_nonneg hr.1.le (-(21 / 20) : ℝ)
  have ht0 : ‖(t : ℂ) ^ (ε - 1)‖ ≤ 4 * r ^ (-(21 / 20) : ℝ) := calc
    _ ≤ t ^ (-(21 / 20) : ℝ) := norm_cpow_le_rpow_of_le ht' ht.2 hα
    _ ≤ (r / 2) ^ (-(21 / 20) : ℝ) := Real.rpow_le_rpow_of_nonpos hp ht.1 (by norm_num)
    _ ≤ 4 * r ^ (-(21 / 20) : ℝ) := by
      rw [Real.div_rpow hr.1.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
        neg_neg, mul_comm]
      exact mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (21 / 20 : ℝ) ≤ 2)).trans
          (by norm_num)) hr0
  set X := ‖(t : ℂ) ^ (ε - 1) - (r : ℂ) ^ (ε - 1)‖
  have ha : X ≤ 5 * r ^ (-(21 / 20) : ℝ) := by
    have hb := norm_cpow_le_rpow_of_le hr.1 hr.2.le hα
    exact (norm_sub_le _ _).trans (by linarith [ht0, hb])
  have hb : X ≤ 16 * r ^ (-(41 / 20) : ℝ) * d :=
    (norm_cpow_sub_cpow_mvt hε hr ht).trans
      (mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num) (Real.rpow_nonneg hr.1.le _)))
  have hs : X ^ 2 ≤ 80 * (d * (r ^ (-(31 / 20) : ℝ)) ^ 2) := calc
    X ^ 2 ≤ (5 * r ^ (-(21 / 20) : ℝ)) * (16 * r ^ (-(41 / 20) : ℝ) * d) := by
      rw [sq]
      exact mul_le_mul ha hb (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show (r ^ (-(31 / 20) : ℝ)) ^ 2 =
          r ^ (-(21 / 20) : ℝ) * r ^ (-(41 / 20) : ℝ) by
        rw [sq, rpow_mul_rpow_eq (c := -(31 / 10)) hr.1 (by norm_num),
          rpow_mul_rpow_eq (c := -(31 / 10)) hr.1 (by norm_num)]]
      ring
  have hd2 : (d ^ (1 / 2 : ℝ)) ^ 2 = d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd']
    norm_num
  have hnonneg : 0 ≤ 9 * (d ^ (1 / 2 : ℝ) * r ^ (-(31 / 20) : ℝ)) :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hd' _) (Real.rpow_nonneg hr.1.le _))
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) hnonneg two_ne_zero).mp
  calc
    _ ≤ 80 * (d * (r ^ (-(31 / 20) : ℝ)) ^ 2) := hs
    _ ≤ 81 * (d * (r ^ (-(31 / 20) : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hd' (sq_nonneg _))
    _ = _ := by rw [mul_pow, mul_pow, hd2]; norm_num

private theorem norm_i10KaAverage_sub_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z r : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hz' : 1 / 2 ≤ z) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ‖(∫ t in z * r..1 - z * (1 - r), (t : ℂ) ^ (ε - 1)) / (1 - z : ℂ) -
      (r : ℂ) ^ (ε - 1)‖ ≤
      9 * ((1 - z) ^ (1 / 2 : ℝ) * r ^ (-(31 / 20) : ℝ)) := by
  set a := z * r
  set b := 1 - z * (1 - r)
  have hab : b - a = 1 - z := by dsimp [a, b]; ring
  have hza : a ≤ b := by linarith [hz.2]
  have ha : r / 2 ≤ a := by dsimp [a]; nlinarith [hr.1]
  have hb : b ≤ 1 := by dsimp [b]; nlinarith [hz.1, hr.2]
  have hza' : 0 < 1 - z := sub_pos.mpr hz.2
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (ε - 1)) (uIcc a b) := by
    rw [uIcc_of_le hza]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [hr.1, ht.1]
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr ht0)).continuousWithinAt
  have heq :
      (∫ t in a..b, (t : ℂ) ^ (ε - 1)) / (1 - z : ℂ) - (r : ℂ) ^ (ε - 1) =
        (∫ t in a..b, (t : ℂ) ^ (ε - 1) - (r : ℂ) ^ (ε - 1)) / (1 - z : ℂ) := by
    rw [intervalIntegral.integral_sub hc.intervalIntegrable intervalIntegrable_const,
      intervalIntegral.integral_const, Complex.real_smul, hab, ofReal_sub, ofReal_one]
    have hzC : (1 - z : ℂ) ≠ 0 := by exact_mod_cast hza'.ne'
    field_simp
  rw [heq, norm_div, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
    abs_of_pos hza', div_le_iff₀ hza']
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun t => (t : ℂ) ^ (ε - 1) - (r : ℂ) ^ (ε - 1))
    (C := 9 * ((1 - z) ^ (1 / 2 : ℝ) * r ^ (-(31 / 20) : ℝ))) (by
      rw [uIoc_of_le hza]
      intro t ht
      apply norm_i10KaPower_sub_le hε hr ⟨ha.trans ht.1.le, ht.2.trans hb⟩
      apply abs_le.mpr
      constructor
      · have h : (1 - z) * r ≤ 1 - z := mul_le_of_le_one_right hza'.le hr.2.le
        dsimp [a] at ht
        nlinarith only [ht.1, h]
      · have h : (1 - z) * (1 - r) ≤ 1 - z :=
          mul_le_of_le_one_right hza'.le (by linarith [hr.1])
        dsimp [b] at ht
        nlinarith only [ht.2, h])
  rwa [abs_of_nonneg (sub_nonneg.mpr hza), hab] at hnorm

private theorem i10Ka_rpow_ge_one {x p : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hp : p ≤ 0) :
    1 ≤ x ^ p := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx.1 hx.2.le hp

private theorem i10Ka_rpow_lower {x y p : ℝ} (hy : 0 < y) (hxy : y / 2 ≤ x)
    (hp : p ∈ Icc (-1 : ℝ) 0) : x ^ p ≤ 2 * y ^ p := by
  calc
    _ ≤ (y / 2) ^ p := Real.rpow_le_rpow_of_nonpos (by positivity) hxy hp.2
    _ = (2 : ℝ) ^ (-p) * y ^ p := by
      rw [Real.div_rpow hy.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
        mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (show -p ≤ 1 by linarith [hp.1])).trans_eq
        (Real.rpow_one _)) (Real.rpow_nonneg hy.le _)

private theorem i10Ka_rpow_compare {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ 2 * y) (hy : 0 ≤ y) :
    x ^ (9 / 20 : ℝ) ≤ 2 * y ^ (9 / 20 : ℝ) := calc
  _ ≤ (2 * y) ^ (9 / 20 : ℝ) := Real.rpow_le_rpow hx hxy (by norm_num)
  _ = _ * y ^ (9 / 20 : ℝ) := Real.mul_rpow (by norm_num) hy
  _ ≤ _ := mul_le_mul_of_nonneg_right
    ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (9 / 20 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one _)) (Real.rpow_nonneg hy _)

private theorem norm_i10KaD_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : ‖i10KaD ε x‖ ≤ 2 * x * (1 - x) ^ (-(11 / 20) : ℝ) := by
  rw [i10KaD, norm_neg]
  exact norm_i10D_le (by rwa [norm_neg]) hx

private theorem norm_i10KaD_join_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z r : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ‖i10KaD ε (1 - z * r)‖ ≤ 2 * (z * r) ^ (-(11 / 20) : ℝ) := by
  have hzr₀ := mul_pos hz.1 hr.1
  have hzr₁ := (mul_lt_of_lt_one_right hz.1 hr.2).trans hz.2
  have h := norm_i10KaD_le hε (show 1 - z * r ∈ Ioo (0 : ℝ) 1 from
    ⟨sub_pos.mpr hzr₁, sub_lt_self _ hzr₀⟩)
  rw [sub_sub_cancel] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hzr₀.le _))

private theorem norm_i10KaB_le_low {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z r : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hz' : z ≤ 1 / 2) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ‖i10KaB ε z r‖ ≤ 17 * (z ^ (9 / 20 : ℝ) * r ^ (-(31 / 20) : ℝ)) := by
  have hz₁ := sub_pos.mpr hz.2
  have hz₀ := hz.1.le
  have hr₀ := hr.1.le
  have hzr₀ := mul_pos hz.1 (sub_pos.mpr hr.2)
  have hzr₁ : z * (1 - r) ≤ z := mul_le_of_le_one_right hz.1.le (by linarith [hr.1])
  have h₁ : ‖i10KaD ε (z * (1 - r))‖ ≤ 4 * z := by
    have h := norm_i10KaD_le hε ⟨hzr₀, hzr₁.trans_lt hz.2⟩
    have hpow : (1 - z * (1 - r)) ^ (-(11 / 20) : ℝ) ≤ 2 := by
      simpa only [Real.one_rpow, mul_one] using i10Ka_rpow_lower
        (y := 1) (p := -(11 / 20)) (by norm_num) (by linarith) (by norm_num)
    exact h.trans ((mul_le_mul (by linarith : 2 * (z * (1 - r)) ≤ 2 * z) hpow
      (Real.rpow_nonneg (by linarith : 0 ≤ 1 - z * (1 - r)) _) (by positivity)).trans_eq (by ring))
  have h₂ := norm_i10KaD_join_le hε hz hr
  rw [Real.mul_rpow hz.1.le hr.1.le] at h₂
  have h₃ : ‖(r : ℂ) ^ (ε - 1)‖ ≤ r ^ (-(21 / 20) : ℝ) := by
    apply norm_cpow_le_rpow_of_le hr.1 hr.2.le
    have := (i9_eps_facts hε).2.2.1
    simp
    linarith
  have hzCast : (1 - (z : ℂ)) ≠ 0 := by exact_mod_cast hz₁.ne'
  have heq : i10KaB ε z r =
      (i10KaD ε (z * (1 - r)) - (z : ℂ) * (2 - z) * i10KaD ε (1 - z * r)) /
        (1 - z : ℂ) - (z : ℂ) * (r : ℂ) ^ (ε - 1) := by
    rw [i10KaB]
    field_simp
    ring
  have hden : ‖1 - (z : ℂ)‖ = 1 - z := by
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos hz₁]
  have hzne : ‖(z : ℂ)‖ = z := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hz.1]
  have hz2 : ‖2 - (z : ℂ)‖ ≤ 2 := by
    rw [← ofReal_ofNat, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hz.2])]
    linarith [hz.1]
  have hzm : z ≤ z ^ (9 / 20 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hz.1 hz.2.le (by norm_num : (9 / 20 : ℝ) ≤ 1)
  have hmul : z * z ^ (-(11 / 20) : ℝ) = z ^ (9 / 20 : ℝ) := by
    nth_rw 1 [← Real.rpow_one z]
    exact rpow_mul_rpow_eq hz.1 (by norm_num)
  have hrM := i10Ka_rpow_ge_one hr (show -(31 / 20 : ℝ) ≤ 0 by norm_num)
  have hc₁ : r ^ (-(11 / 20) : ℝ) ≤ r ^ (-(31 / 20) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2.le (by norm_num)
  have hc₂ : r ^ (-(21 / 20) : ℝ) ≤ r ^ (-(31 / 20) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2.le (by norm_num)
  have ht : ‖(z : ℂ) * (2 - z) * i10KaD ε (1 - z * r)‖ ≤
      4 * (z ^ (9 / 20 : ℝ) * r ^ (-(31 / 20) : ℝ)) := by
    rw [norm_mul, norm_mul, hzne]
    calc
      _ ≤ z * 2 * (2 * (z ^ (-(11 / 20) : ℝ) * r ^ (-(11 / 20) : ℝ))) := by gcongr
      _ = 4 * (z ^ (9 / 20 : ℝ) * r ^ (-(11 / 20) : ℝ)) := by
        rw [← hmul]; ring
      _ ≤ _ := by gcongr
  have hd : 1 / (1 - z) ≤ 2 := by
    apply (div_le_iff₀ hz₁).mpr
    linarith
  rw [heq]
  calc
    _ ≤ ‖(i10KaD ε (z * (1 - r)) - (z : ℂ) * (2 - z) * i10KaD ε (1 - z * r)) /
        (1 - z : ℂ)‖ + ‖(z : ℂ) * (r : ℂ) ^ (ε - 1)‖ := norm_sub_le _ _
    _ ≤ (4 * z + 4 * (z ^ (9 / 20 : ℝ) * r ^ (-(31 / 20) : ℝ))) * 2 +
        z * r ^ (-(21 / 20) : ℝ) := by
      rw [norm_div, hden, div_eq_mul_one_div, norm_mul, hzne]
      have h := (norm_sub_le _ _).trans (add_le_add h₁ ht)
      exact add_le_add (mul_le_mul h hd (one_div_nonneg.mpr hz₁.le) ((norm_nonneg _).trans h))
        (mul_le_mul_of_nonneg_left h₃ hz₀)
    _ ≤ _ := by
      have hmul₁ := hzm.trans (le_mul_of_one_le_right
        (Real.rpow_nonneg hz.1.le _) hrM)
      have hmul₂ := mul_le_mul hzm hc₂ (Real.rpow_nonneg hr.1.le _) (Real.rpow_nonneg hz.1.le _)
      linarith only [hmul₁, hmul₂]

private theorem norm_i10KaB_le_high {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z r : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hz' : 1 / 2 ≤ z) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ‖i10KaB ε z r‖ ≤ 14 * ((1 - z) ^ (9 / 20 : ℝ) * r ^ (-(31 / 20) : ℝ)) := by
  have hz₁ := sub_pos.mpr hz.2
  have h₁ := norm_i10KaAverage_sub_le hε hz hz' hr
  have h₂ := (norm_i10KaD_join_le hε hz hr).trans
    (mul_le_mul_of_nonneg_left (i10Ka_rpow_lower hr.1 (by nlinarith [hr.1]) (by norm_num))
      (by norm_num))
  have h₃ : ‖(r : ℂ) ^ (ε - 1)‖ ≤ r ^ (-(31 / 20) : ℝ) := by
    apply norm_cpow_le_rpow_of_le hr.1 hr.2.le
    have := (i9_eps_facts hε).2.2.1
    simp
    linarith
  have hc : r ^ (-(11 / 20) : ℝ) ≤ r ^ (-(31 / 20) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2.le (by norm_num)
  have hzc : 1 - z ≤ 1 := by linarith [hz.1]
  have hzM : 1 - z ≤ (1 - z) ^ (9 / 20 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hz₁ hzc (by norm_num : (9 / 20 : ℝ) ≤ 1)
  have hzM' := Real.rpow_le_rpow_of_exponent_ge hz₁ hzc (by norm_num : (9 / 20 : ℝ) ≤ 1 / 2)
  have hzN : ‖1 - (z : ℂ)‖ = 1 - z := by
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos hz₁]
  rw [i10KaB_eq_average hz hr]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hzN]
  calc
    _ ≤ 9 * ((1 - z) ^ (9 / 20 : ℝ) * r ^ (-(31 / 20) : ℝ)) +
        (1 - z) ^ (9 / 20 : ℝ) * (4 * r ^ (-(31 / 20) : ℝ) + r ^ (-(31 / 20) : ℝ)) := by
      gcongr
      · exact h₁.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hzM' (Real.rpow_nonneg hr.1.le _)) (by norm_num))
      · exact (norm_add_le _ _).trans (add_le_add (h₂.trans (by linarith only [hc])) h₃)
    _ = _ := by ring

private theorem norm_i10KaB_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {z r : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ‖i10KaB ε z r‖ ≤ 34 * ((z * (1 - z)) ^ (9 / 20 : ℝ) * r ^ (-(31 / 20) : ℝ)) := by
  have hc := (i9_c_pos hz).le
  rcases le_or_gt z (1 / 2) with h | h
  · have h' := i10Ka_rpow_compare hz.1.le (by nlinarith [hz.1]) hc
    refine (norm_i10KaB_le_low hε hz h hr).trans ?_
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h' (by norm_num : (0 : ℝ) ≤ 17))
      (Real.rpow_nonneg hr.1.le (-(31 / 20)))
    convert hh using 1 <;> ring
  · have h' := i10Ka_rpow_compare (sub_pos.mpr hz.2).le (by nlinarith [hz.2]) hc
    refine (norm_i10KaB_le_high hε hz h.le hr).trans ?_
    have hc' := Real.rpow_nonneg hc (9 / 20 : ℝ)
    have hh : 14 * (1 - z) ^ (9 / 20 : ℝ) ≤ 34 * (z * (1 - z)) ^ (9 / 20 : ℝ) := by
      linarith only [h', hc']
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh
      (Real.rpow_nonneg hr.1.le (-(31 / 20)))

theorem norm_i10KaH_le {ε : ℂ} (hε : ‖ε‖ < 1 / 20) {q : ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    ‖i10KaH ε q‖ ≤ 68 * ((q.1 * (1 - q.1)) ^ (-(3 / 5) : ℝ) *
      (q.2 * (1 - q.2)) ^ (-(11 / 20) : ℝ)) := by
  obtain ⟨hz, hr⟩ := hq
  set z := q.1
  set r := q.2
  have hc := i9_c_pos hz
  have hr' := sub_pos.mpr hr.2
  have hr₀ : 0 ≤ r := hr.1.le
  have hc₀ : 0 ≤ z * (1 - z) := hc.le
  have hr₁ : 0 ≤ 1 - r := hr'.le
  rw [i10KaH, norm_mul, norm_mul]
  calc
    _ ≤ (2 * r * (1 - r) ^ (-(11 / 20) : ℝ)) * (z * (1 - z)) ^ (-(21 / 20) : ℝ) *
        (34 * ((z * (1 - z)) ^ (9 / 20 : ℝ) * r ^ (-(31 / 20) : ℝ))) :=
      mul_le_mul (mul_le_mul (norm_i10D_le hε hr) (norm_i10W_le hε hz) (norm_nonneg _)
        (by positivity)) (norm_i10KaB_le hε hz hr) (norm_nonneg _) (by positivity)
    _ = 68 * (((z * (1 - z)) ^ (-(21 / 20) : ℝ) * (z * (1 - z)) ^ (9 / 20 : ℝ)) *
        ((r * r ^ (-(31 / 20) : ℝ)) * (1 - r) ^ (-(11 / 20) : ℝ))) := by ring
    _ = _ := by
      rw [rpow_mul_rpow_eq (c := -(3 / 5)) hc (by norm_num),
        show r * r ^ (-(31 / 20) : ℝ) = r ^ (-(11 / 20) : ℝ) by
          nth_rw 1 [← Real.rpow_one r]
          exact rpow_mul_rpow_eq hr.1 (by norm_num),
        ← Real.mul_rpow hr.1.le hr'.le]

private theorem integrable_i10KaBound :
    IntegrableOn (fun q : ℝ × ℝ => 68 * ((q.1 * (1 - q.1)) ^ (-(3 / 5) : ℝ) *
      (q.2 * (1 - q.2)) ^ (-(11 / 20) : ℝ))) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rw [IntegrableOn, volume_restrict_prod2]
  exact ((integrableOn_mul_one_sub_rpow_Ioo (by norm_num)).mul_prod
    (integrableOn_mul_one_sub_rpow_Ioo (by norm_num))).const_mul 68

theorem analyticOnNhd_i10KaH : AnalyticOnNhd ℂ (fun ε =>
    ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10KaH ε q) (Metric.ball 0 (1 / 40)) := by
  have hd : DifferentiableOn ℂ (fun ε =>
      ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10KaH ε q) (Metric.ball 0 (1 / 40)) := by
    intro ε₀ hε₀
    apply DifferentiableAt.differentiableWithinAt
    have hball : ∀ ε ∈ Metric.ball ε₀ (1 / 40), ‖ε‖ < 1 / 20 := fun ε hε => by
      have hh := norm_sub_norm_le ε ε₀
      rw [Metric.mem_ball, dist_eq_norm] at hε
      rw [Metric.mem_ball, dist_zero_right] at hε₀
      linarith
    have hs : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
      measurableSet_Ioo.prod measurableSet_Ioo
    refine differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 40)
      integrable_i10KaBound (fun ε _ => (measurable_i10KaH ε).aestronglyMeasurable) ?_ ?_
    · exact ae_restrict_of_forall_mem hs fun q hq ε hε => norm_i10KaH_le (hball ε hε) hq
    · exact ae_restrict_of_forall_mem hs fun q hq ε _ =>
        (differentiable_i10KaH hq ε).differentiableWithinAt
  exact fun ε hε => hd.analyticAt (Metric.isOpen_ball.mem_nhds hε)

/-- The first derivative of the divided integral is obtained under the integral sign. -/
theorem hasDerivAt_i10KaH_integral_zero :
    HasDerivAt (fun ε => ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10KaH ε q)
      (∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, deriv (fun ε => i10KaH ε q) 0) 0 := by
  let S := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
  let μ := volume.restrict S
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hq : ∀ᵐ q ∂μ, q ∈ S := ae_restrict_mem hS
  let b : ℝ × ℝ → ℝ := fun q => 68 * ((q.1 * (1 - q.1)) ^ (-(3 / 5) : ℝ) *
    (q.2 * (1 - q.2)) ^ (-(11 / 20) : ℝ))
  have hb : Integrable b μ := integrable_i10KaBound
  have hm (ε : ℂ) : AEStronglyMeasurable (i10KaH ε) μ :=
    (measurable_i10KaH ε).aestronglyMeasurable
  have h0 : Integrable (i10KaH 0) μ := hb.mono' (hm _) (by
    filter_upwards [hq] with q hq using norm_i10KaH_le (by norm_num) hq)
  have hδpos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  let δ : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hδ : Tendsto δ atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa only [δ, Function.comp_def, ofReal_zero] using (continuous_ofReal.tendsto 0).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
    · exact ofReal_ne_zero.mpr (hδpos n).ne'
  have hm' : AEStronglyMeasurable (fun q => deriv (fun ε => i10KaH ε q) 0) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n q => (δ n)⁻¹ • (i10KaH (δ n) q - i10KaH 0 q))
      (fun n => ?_) ?_
    · exact (((hm (δ n)).sub (hm 0)).const_smul (δ n)⁻¹ :
        AEStronglyMeasurable ((δ n)⁻¹ • (i10KaH (δ n) - i10KaH 0)) μ)
    · filter_upwards [hq] with q hq
      have h := (differentiable_i10KaH hq 0).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope_zero] at h
      simpa only [Function.comp_def, zero_add] using h.comp hδ
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := i10KaH) (F' := fun ε q => deriv (fun w => i10KaH w q) ε)
    (s := ball (0 : ℂ) (1 / 80)) (bound := fun q => b q / (1 / 80))
    (ball_mem_nhds _ (by norm_num)) (Eventually.of_forall hm) h0 hm' ?_
    (hb.div_const _) ?_).2
  · filter_upwards [hq] with q hq ε hε
    have hd : DifferentiableOn ℂ (fun w => i10KaH w q) (closedBall ε (1 / 80)) :=
      (differentiable_i10KaH hq).differentiableOn
    refine norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) ?_ ?_
    · exact hd.diffContOnCl_ball (Subset.rfl)
    · intro w hw
      apply norm_i10KaH_le _ hq
      rw [mem_sphere] at hw
      rw [mem_ball] at hε
      have hh := dist_triangle w ε 0
      simp only [dist_zero_right, hw] at hh
      rw [dist_zero_right] at hε
      linarith
  · filter_upwards [hq] with q hq ε _
    exact (differentiable_i10KaH hq ε).hasDerivAt

/-- The expansion of `K_a` with its coefficients given by convergent integrals. -/
theorem hasTruncLaurent_i10Ka_integrals :
    HasTruncLaurent i10Ka
      (fun ε => (∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10KaH 0 q) * ε ^ 2 +
        (∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, deriv (fun w => i10KaH w q) 0) * ε ^ 3) 4 := by
  let H := fun ε => ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10KaH ε q
  have hH : AnalyticAt ℂ H 0 := analyticOnNhd_i10KaH 0 (mem_ball_self (by norm_num))
  have hd : deriv H 0 =
      ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, deriv (fun w => i10KaH w q) 0 :=
    hasDerivAt_i10KaH_integral_zero.deriv
  obtain ⟨F, hF, he⟩ := hH.exists_eventuallyEq_sum_add_pow_mul 2
  refine ⟨F, hF, ?_⟩
  filter_upwards [nhdsWithin_le_nhds he] with ε hε
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, div_one, pow_zero, pow_one, smul_eq_mul,
    iteratedDeriv_zero, iteratedDeriv_one] at hε
  rw [i10Ka_eq]
  change ε ^ 2 * H ε = H 0 * ε ^ 2 + _ * ε ^ 3 + ε ^ 4 * F ε
  rw [hε, hd]
  ring

private theorem hasDerivAt_i10_dslope_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    HasDerivAt (dslope f 0) (iteratedDeriv 2 f 0 / 2) 0 := by
  obtain ⟨F, hF, he⟩ := hf.exists_eq_sum_add_pow_mul 3
  let c := iteratedDeriv 2 f 0 / 2
  have hd : HasDerivAt (fun ε => deriv f 0 + ε * c + ε ^ 2 * F ε) c 0 := by
    have h₁ := (hasDerivAt_id (0 : ℂ)).mul_const c
    have h₂ : HasDerivAt (fun ε : ℂ => ε ^ 2 * F ε) 0 0 := by
      have hh := ((hasDerivAt_id (0 : ℂ)).pow 2).mul hF.differentiableAt.hasDerivAt
      change HasDerivAt (fun ε : ℂ => ε ^ 2 * F ε) _ 0 at hh
      convert hh using 1
      norm_num [Pi.pow_apply]
    have hh := (h₁.const_add (deriv f 0)).add h₂
    change HasDerivAt (fun ε => deriv f 0 + ε * c + ε ^ 2 * F ε) _ _ at hh
    simpa only [one_mul, add_zero] using hh
  suffices (fun ε => deriv f 0 + ε * c + ε ^ 2 * F ε) = dslope f 0 by rwa [this] at hd
  funext ε
  by_cases hε : ε = 0
  · subst ε
    simp only [dslope_same, zero_mul, add_zero, zero_pow (by decide : 2 ≠ 0)]
  · have h := he ε
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
      smul_eq_mul] at h
    have e := sub_smul_dslope f 0 ε
    rw [sub_zero, smul_eq_mul, h] at e
    apply (mul_left_cancel₀ hε)
    rw [e]
    dsimp only [c]
    ring

private theorem hasDerivAt_i10KaD_zero {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun ε => i10KaD ε x) ((Real.log (1 - x) : ℂ) ^ 2 / 2) 0 := by
  let L : ℂ := (Real.log (1 - x) : ℂ)
  have hp : 0 < 1 - x := sub_pos.mpr hx
  have he : (fun ε => i10KaD ε x) = dslope (fun ε : ℂ => exp (L * ε)) 0 := by
    funext ε
    by_cases hε : ε = 0
    · subst ε
      rw [i10KaD, neg_zero, i10D_zero hx, neg_neg, dslope_same]
      have h := ((hasDerivAt_id (0 : ℂ)).const_mul L).cexp
      simpa only [id_eq, mul_zero, exp_zero, one_mul, mul_one] using h.deriv.symm
    · rw [i10KaD, i10D_of_ne (neg_ne_zero.mpr hε), neg_neg, div_neg, neg_neg,
        dslope_of_ne _ hε, slope_def_field, sub_zero, mul_zero, exp_zero,
        cpow_def_of_ne_zero (ofReal_ne_zero.mpr hp.ne'), ← ofReal_log hp.le]
  rw [he]
  have h := hasDerivAt_i10_dslope_zero
    (f := fun ε : ℂ => exp (L * ε)) (by fun_prop)
  rw [iteratedDeriv_cexp_const_mul] at h
  simpa only [mul_zero, exp_zero, mul_one] using h

/-- The derivative of the divided integrand, in terms of the two log brackets. -/
theorem hasDerivAt_i10KaH_zero {q : ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    let z := q.1
    let r := q.2
    let A : ℂ := Real.log (1 - z * (1 - r))
    let B : ℂ := Real.log (z * r)
    let D : ℂ := - (Real.log (1 - r) : ℂ)
    let W : ℂ := ((z * (1 - z) : ℝ) : ℂ)⁻¹
    HasDerivAt (fun ε => i10KaH ε q)
      (D * W * ((A ^ 2 - B ^ 2) / (2 * (1 - z)) + (1 - z) * B ^ 2 / 2 -
        (z : ℂ) / r * (Real.log r : ℂ) +
        ((Real.log (z * (1 - z)) : ℂ) + D / 2) * i10KaB 0 z r)) 0 := by
  dsimp only
  obtain ⟨hz, hr⟩ := hq
  have h₁ : q.1 * (1 - q.2) < 1 := by nlinarith [hz.1, hz.2, hr.1]
  have h₂ : 1 - q.1 * q.2 < 1 := by nlinarith [mul_pos hz.1 hr.1]
  have hc (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun w : ℂ => (x : ℂ) ^ (w - 1))
        ((x : ℂ)⁻¹ * (Real.log x : ℂ)) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).sub_const (1 : ℂ)
    simpa only [id_eq, zero_sub, cpow_neg_one, mul_one, ofReal_log hx.le] using
      h.const_cpow (c := (x : ℂ)) (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have hD : HasDerivAt (fun w => i10D w q.2)
      ((Real.log (1 - q.2) : ℂ) ^ 2 / 2) 0 := by
    have hh : HasDerivAt (fun ε => i10KaD ε q.2)
        ((Real.log (1 - q.2) : ℂ) ^ 2 / 2) (-(0 : ℂ)) := by
      rw [neg_zero]
      exact hasDerivAt_i10KaD_zero hr.2
    have h := hh.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
    have hn := h.neg
    change HasDerivAt (fun w => -(-i10D (-(-w)) q.2)) _ _ at hn
    simpa only [neg_neg, mul_neg, mul_one] using hn
  have hB := ((((hasDerivAt_i10KaD_zero h₁).sub
    (hasDerivAt_i10KaD_zero h₂)).div_const (1 - (q.1 : ℂ))).add
    ((hasDerivAt_i10KaD_zero h₂).const_mul (1 - (q.1 : ℂ)))).sub
    ((hc q.2 hr.1).const_mul (q.1 : ℂ))
  rw [sub_sub_cancel] at hB
  have hW := hc _ (i9_c_pos hz)
  have hh := (hD.mul hW).mul hB
  change HasDerivAt (fun ε => i10KaH ε q) _ _ at hh
  refine hh.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, zero_sub, cpow_neg_one, i10D_zero hr.2]
  rw [i10KaB_zero hz hr]
  simp only [i10KaD, neg_zero, i10D_zero h₁, i10D_zero h₂, neg_neg, sub_sub_cancel,
    div_eq_mul_inv, mul_inv_rev]
  ring

section LeadingCoefficient

open Real QED.Polylog

theorem integral_i10Ka_leading_reduced :
    ∫ r in Ioo (0 : ℝ) 1, -log (1 - r) * (π ^ 2 / 6 + log r ^ 2 / 2 + (1 + log r) / r) =
      3 + π ^ 2 / 6 - 2 * zeta3 := by
  let S := Ioo (0 : ℝ) 1
  let a := fun r : ℝ => log (1 - r)
  let b := fun r : ℝ => log r * log r * log (1 - r)
  let c := fun r : ℝ => log (1 - r) / r
  let d := fun r : ℝ => log r * log (1 - r) / r
  have ha : IntegrableOn a S := i10_integrableOn_log_one_sub
  have hb : IntegrableOn b S :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      i9_integral_log_sq_mul_log_one_sub.1
  have hc : IntegrableOn c S :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      intervalIntegrable_and_integral_log_one_sub_div.1
  have hd : IntegrableOn d S :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      intervalIntegrable_and_integral_log_mul_log_one_sub_div.1
  let A := fun r : ℝ => -(π ^ 2 / 6) * a r
  let B := fun r : ℝ => -(1 / 2) * b r
  have hA : IntegrableOn A S := ha.const_mul _
  have hB : IntegrableOn B S := hb.const_mul _
  have hb' : (∫ r in S, b r) = 2 * zeta3 - 6 + π ^ 2 / 3 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact i9_integral_log_sq_mul_log_one_sub.2
  have hc' : (∫ r in S, c r) = -(π ^ 2 / 6) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegrable_and_integral_log_one_sub_div.2
  have hd' : (∫ r in S, d r) = zeta3 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact integral_log_mul_log_one_sub_div
  calc
    _ = ∫ r in S, A r + B r - c r - d r := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r _
      dsimp [A, B, a, b, c, d]
      ring
    _ = _ := by
      calc
        _ = ((∫ r in S, A r) + ∫ r in S, B r) - (∫ r in S, c r) - ∫ r in S, d r := by
          have h := integral_sub ((hA.add hB).sub hc) hd
          change (∫ r in S, A r + B r - c r - d r) =
            (∫ r in S, A r + B r - c r) - ∫ r in S, d r at h
          rw [h]
          rw [show (∫ r in S, A r + B r - c r) =
            (∫ r in S, A r + B r) - ∫ r in S, c r from integral_sub (hA.add hB) hc]
          rw [integral_add hA hB]
        _ = _ := by
          dsimp only [A, B]
          rw [integral_const_mul, integral_const_mul, hb', hc', hd']
          change (-(π ^ 2 / 6) * (∫ r in Ioo (0 : ℝ) 1, log (1 - r)) +
            -(1 / 2) * (2 * zeta3 - 6 + π ^ 2 / 3)) - -(π ^ 2 / 6) - zeta3 = _
          rw [i10_integral_log_one_sub]
          ring

private theorem i10KaLogPosMoment {k : ℝ} (hk : 0 < k) :
    IntervalIntegrable (fun y : ℝ => log (1 + k * y) / y) volume 0 1 ∧
      ∫ y in (0 : ℝ)..1, log (1 + k * y) / y =
        Li₂ (k / (1 + k)) + log (1 + k) ^ 2 / 2 := by
  let P := fun y : ℝ => Li₂ (k * y / (1 + k * y)) + log (1 + k * y) ^ 2 / 2
  have hcont : ContinuousOn P (Icc 0 1) := by
    have ha : ContinuousOn (fun y : ℝ => 1 + k * y) (Icc 0 1) := by fun_prop
    have hb : ∀ y ∈ Icc (0 : ℝ) 1, 0 < 1 + k * y := fun y hy =>
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hk.le hy.1)
    have hd : ContinuousOn (fun y : ℝ => k * y / (1 + k * y)) (Icc 0 1) :=
      (continuousOn_const.mul continuousOn_id).div ha fun y hy => (hb y hy).ne'
    have hm : MapsTo (fun y : ℝ => k * y / (1 + k * y)) (Icc 0 1) (Icc (-1) 1) :=
      fun y hy => ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans
        (div_nonneg (mul_nonneg hk.le hy.1) (hb y hy).le),
        (div_le_one (hb y hy)).mpr (by linarith)⟩
    exact (continuousOn_Li₂.comp hd hm).add
      ((ha.log fun y hy => (hb y hy).ne').pow 2 |>.div_const 2)
  have hd : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt P (log (1 + k * y) / y) y := by
    intro y hy
    have hp : 0 < 1 + k * y := add_pos zero_lt_one (mul_pos hk hy.1)
    have hu : k * y / (1 + k * y) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos (mul_pos hk hy.1) hp, (div_lt_one hp).mpr (by linarith)⟩
    have hA := (hasDerivAt_id' y).const_mul k
    have hB := hA.const_add 1
    have h := ((hasDerivAt_Li₂' hu).comp y (hA.div hB hp.ne')).add
      (((hB.log hp.ne').pow 2).div_const 2)
    refine h.congr_deriv ?_
    simp only [mul_one]
    rw [show 1 - k * y / (1 + k * y) = (1 + k * y)⁻¹ by field_simp; ring]
    rw [log_inv]
    field_simp [hy.1.ne', hk.ne', hp.ne']
    ring
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd
    (fun y hy => div_nonneg (log_nonneg (by linarith [mul_nonneg hk.le hy.1.le])) hy.1.le)
    ((hcont 0 ⟨le_rfl, zero_le_one⟩).mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1))))
    ((hcont 1 ⟨zero_le_one, le_rfl⟩).mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1))))
  simpa only [P, mul_zero, zero_div, Li₂_zero, add_zero, log_one, zero_pow (by decide : 2 ≠ 0),
    zero_add, mul_one, sub_zero] using h

private theorem i10KaLogPosRemMoment {k : ℝ} (hk : 0 < k) :
    IntervalIntegrable (fun y : ℝ => (log (1 + k * y) - k * y) / y ^ 2) volume 0 1 ∧
      ∫ y in (0 : ℝ)..1, (log (1 + k * y) - k * y) / y ^ 2 =
        k - (1 + k) * log (1 + k) := by
  let P := fun y : ℝ => k - (y⁻¹ + k) * log (1 + k * y)
  have hd : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt P ((log (1 + k * y) - k * y) / y ^ 2) y := by
    intro y hy
    have hp : 0 < 1 + k * y := add_pos zero_lt_one (mul_pos hk hy.1)
    have hA := ((hasDerivAt_id' y).const_mul k).const_add 1
    have h := (((hasDerivAt_inv hy.1.ne').add_const k).mul (hA.log hp.ne')).const_sub k
    refine h.congr_deriv ?_
    simp only [mul_one]
    rw [show (y⁻¹ + k) * (k / (1 + k * y)) = k / y by
      rw [show y⁻¹ + k = (1 + k * y) / y by field_simp [hy.1.ne']]
      field_simp [hy.1.ne', hp.ne']]
    field_simp [hy.1.ne']
    ring
  have ha : Tendsto (fun y : ℝ => log (1 + k * y)) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun y : ℝ => log (1 + k * y)) 0 := by
      fun_prop (disch := norm_num)
    simpa only [mul_zero, add_zero, log_one] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun y : ℝ => y⁻¹ * log (1 + k * y)) (𝓝[>] 0) (𝓝 k) := by
    have h := (((hasDerivAt_id' (0 : ℝ)).const_mul k).const_add 1).log (by norm_num)
    simp only [mul_zero, add_zero, mul_one, div_one] at h
    rw [hasDerivAt_iff_tendsto_slope_zero] at h
    have hh := h.mono_left (nhdsWithin_mono _ (show Ioi (0 : ℝ) ⊆ {0}ᶜ
      from fun y hy => ne_of_gt hy))
    simpa only [zero_add, mul_zero, add_zero, log_one, sub_zero, smul_eq_mul] using hh
  have h0 : Tendsto P (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_const_nhds (x := k)).sub (hb.add (ha.const_mul k))
    rw [mul_zero, add_zero, sub_self] at h
    apply h.congr
    intro y
    dsimp [P]
    ring
  have h1 : Tendsto P (𝓝[<] 1) (𝓝 (k - (1 + k) * log (1 + k))) := by
    have h : ContinuousAt P 1 := by
      dsimp [P]
      fun_prop (disch := first | linarith | norm_num)
    simpa only [P, inv_one, mul_one] using h.tendsto.mono_left nhdsWithin_le_nhds
  have h := intervalIntegrable_and_integral_eq_of_nonpos hd (fun y hy => by
    have hp := log_le_sub_one_of_pos (add_pos zero_lt_one (mul_pos hk hy.1))
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg y)) h0 h1
  simpa only [sub_zero] using h

private theorem i10KaLogNegMoment {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun z : ℝ => log (1 - x * z) / z) volume 0 1 ∧
      ∫ z in (0 : ℝ)..1, log (1 - x * z) / z = -Li₂ x := by
  let P := fun z : ℝ => -Li₂ (x * z)
  have hd : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt P (log (1 - x * z) / z) z := by
    intro z hz
    have hxz : x * z ∈ Ioo (0 : ℝ) 1 :=
      ⟨mul_pos hx.1 hz.1, (mul_lt_of_lt_one_right hx.1 hz.2).trans hx.2⟩
    refine (((hasDerivAt_Li₂' hxz).comp z ((hasDerivAt_id' z).const_mul x)).neg).congr_deriv ?_
    simp only [mul_one]
    field_simp [hx.1.ne', hz.1.ne']
  have hcont : ContinuousOn P (Icc 0 1) :=
    (continuousOn_Li₂.comp (continuousOn_const.mul continuousOn_id)
      (fun z hz => ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (mul_nonneg hx.1.le hz.1),
        (mul_le_of_le_one_right hx.1.le hz.2).trans hx.2.le⟩)).neg
  have h := intervalIntegrable_and_integral_eq_of_nonpos hd
    (fun z hz => div_nonpos_of_nonpos_of_nonneg (log_nonpos
      (by linarith [(mul_le_of_le_one_right hx.1.le hz.2.le).trans hx.2.le])
      (by linarith [mul_pos hx.1 hz.1])) hz.1.le)
    ((hcont 0 ⟨le_rfl, zero_le_one⟩).mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1))))
    ((hcont 1 ⟨zero_le_one, le_rfl⟩).mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1))))
  simpa only [P, mul_zero, Li₂_zero, neg_zero, mul_one, sub_zero] using h

private theorem i10Ka_reflect {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    IntervalIntegrable (fun z : ℝ => f (1 - z)) volume 0 1 ∧
      (∫ z in (0 : ℝ)..1, f (1 - z)) = ∫ z in (0 : ℝ)..1, f z := by
  refine ⟨?_, ?_⟩
  · simpa only [sub_self, sub_zero] using hf.symm.comp_sub_left 1
  · simpa only [sub_zero, sub_self] using
      intervalIntegral.integral_comp_sub_left f (a := 0) (b := 1) 1

/-- The joining integral of the linear term in the divided `K_a` bracket. -/
theorem integral_i10Ka_leading_join {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∫ z in Ioo (0 : ℝ) 1, (((log (1 - z * (1 - r)) - log (z * r)) / (1 - z) +
      (1 - z) * log (z * r) - z / r) / (z * (1 - z))) =
        π ^ 2 / 6 + log r ^ 2 / 2 + (1 + log r) / r := by
  let x := 1 - r
  let k := x / r
  have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [x]; linarith [hr.2], by dsimp [x]; linarith [hr.1]⟩
  have hk : 0 < k := div_pos hx.1 hr.1
  have hk₁ : 1 + k = r⁻¹ := by dsimp [k, x]; field_simp [hr.1.ne']; ring
  have hk₂ : k / (1 + k) = x := by rw [hk₁]; dsimp [k]; field_simp [hr.1.ne']
  let A := fun z : ℝ => log (1 - x * z) / z
  let B := fun z : ℝ => log (1 + k * (1 - z)) / (1 - z)
  let C := fun z : ℝ => -(log (1 - (1 - z)) / (1 - z))
  let D := fun z : ℝ => (log (1 + k * (1 - z)) - k * (1 - z)) / (1 - z) ^ 2
  let E := fun z : ℝ => -((log (1 - (1 - z)) + (1 - z)) / (1 - z) ^ 2)
  have ha := i10KaLogNegMoment hx
  have hb := i10Ka_reflect (i10KaLogPosMoment hk).1
  have hc := i10Ka_reflect intervalIntegrable_and_integral_log_one_sub_div.1
  have hd := i10Ka_reflect (i10KaLogPosRemMoment hk).1
  have he := i10Ka_reflect intervalIntegrable_and_integral_log_one_sub_add_div_sq.1
  have hC : IntervalIntegrable C volume 0 1 := hc.1.neg
  have hE : IntervalIntegrable E volume 0 1 := he.1.neg
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ z in (0 : ℝ)..1, A z + B z + C z + D z + E z := by
      apply intervalIntegral.integral_congr_uIoo
      intro z hz
      rw [uIoo_of_le zero_le_one] at hz
      have hzc : 1 - z ≠ 0 := sub_ne_zero.mpr hz.2.ne'
      have hmul : 1 - z * (1 - r) = r * (1 + k * (1 - z)) := by
        dsimp [k, x]
        field_simp [hr.1.ne']
        ring
      have hne : 1 + k * (1 - z) ≠ 0 :=
        (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hk.le (sub_nonneg.mpr hz.2.le))).ne'
      have hl : log (1 - z * (1 - r)) = log r + log (1 + k * (1 - z)) := by
        rw [hmul, log_mul hr.1.ne' hne]
      dsimp [A, B, C, D, E, x]
      rw [log_mul hz.1.ne' hr.1.ne']
      rw [mul_comm (1 - r) z, hl, sub_sub_cancel]
      dsimp [k, x]
      field_simp [hz.1.ne', hzc, hr.1.ne']
      ring
    _ = _ := by
      have hA : IntervalIntegrable A volume 0 1 := ha.1
      have hB : IntervalIntegrable B volume 0 1 := hb.1
      have hD : IntervalIntegrable D volume 0 1 := hd.1
      rw [intervalIntegral.integral_add (((hA.add hB).add hC).add hD) hE,
        intervalIntegral.integral_add ((hA.add hB).add hC) hD,
        intervalIntegral.integral_add (hA.add hB) hC, intervalIntegral.integral_add hA hB]
      dsimp only [A, B, C, D, E]
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_neg, ha.2, hb.2, hc.2, hd.2,
        he.2, (i10KaLogPosMoment hk).2, (i10KaLogPosRemMoment hk).2,
        intervalIntegrable_and_integral_log_one_sub_div.2,
        intervalIntegrable_and_integral_log_one_sub_add_div_sq.2, hk₂, hk₁, log_inv]
      dsimp [k, x]
      field_simp [hr.1.ne']
      ring

end LeadingCoefficient

/-- The coefficient of `ε²` in the once-weighted remainder. -/
theorem integral_i10KaH_zero :
    ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, i10KaH 0 q =
      ((3 + Real.pi ^ 2 / 6 - 2 * QED.Polylog.zeta3 : ℝ) : ℂ) := by
  let S := Ioo (0 : ℝ) 1
  let F := i10KaH 0
  have hS : MeasurableSet S := measurableSet_Ioo
  have hi : IntegrableOn F (S ×ˢ S) :=
    integrable_i10KaBound.mono' (measurable_i10KaH 0).aestronglyMeasurable
      (ae_restrict_of_forall_mem (hS.prod hS) fun q hq => norm_i10KaH_le (by norm_num) hq)
  rw [IntegrableOn, volume_restrict_prod2] at hi
  change (∫ q in S ×ˢ S, F q) = _
  rw [volume_restrict_prod2, ← integral_prod_swap, integral_prod (fun z => F z.swap) hi.swap]
  have he : (∫ r in S, ∫ z in S, F (z, r)) =
      ∫ r in S, ((-Real.log (1 - r) *
        (Real.pi ^ 2 / 6 + Real.log r ^ 2 / 2 + (1 + Real.log r) / r) : ℝ) : ℂ) := by
    apply setIntegral_congr_fun hS
    intro r hr
    let g := fun z : ℝ => ((Real.log (1 - z * (1 - r)) - Real.log (z * r)) / (1 - z) +
      (1 - z) * Real.log (z * r) - z / r) / (z * (1 - z))
    have eg : (∫ z in S, F (z, r)) =
        ∫ z in S, ((-Real.log (1 - r) * g z : ℝ) : ℂ) := by
      apply setIntegral_congr_fun hS
      intro z hz
      dsimp only [F, g, i10KaH]
      rw [i10D_zero hr.2, i10W, zero_sub, cpow_neg_one, i10KaB_zero hz hr]
      push_cast
      ring
    dsimp only
    rw [eg, integral_complex_ofReal, integral_const_mul]
    rw [show (∫ z in S, g z) = _ from integral_i10Ka_leading_join hr]
  change (∫ r in S, ∫ z in S, F (z, r)) = _
  rw [he, integral_complex_ofReal, integral_i10Ka_leading_reduced]

/-- The quadratic coefficient of `K_a` in closed form, with a cubic coefficient integral. -/
theorem hasTruncLaurent_i10Ka_leading :
    HasTruncLaurent i10Ka
      (fun ε => ((3 + Real.pi ^ 2 / 6 - 2 * QED.Polylog.zeta3 : ℝ) : ℂ) * ε ^ 2 +
        (∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, deriv (fun w => i10KaH w q) 0) * ε ^ 3) 4 := by
  simpa only [integral_i10KaH_zero] using hasTruncLaurent_i10Ka_integrals

end QED.ThreeLoopE
