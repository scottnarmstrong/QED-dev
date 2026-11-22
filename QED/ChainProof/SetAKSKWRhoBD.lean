/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBP
public import QED.Polylog.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (a), stage D: logarithms over linear factors, integrated

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. After the
`ρ`- and `w`-integrals the `VB` density is, on each `β`-range, a combination of logarithms
`log (β - a)` (with `Real.log`, i.e. `log |β - a|`) with rational coefficients. This file
integrates the terms that are not covered by `ksWPe`:

* the difference quotient `(log (β - a) - log (p - a))/(β - p)`, over any interval: its primitive
  is `ksWYD ((β - p)/(a - p))`, where `ksWYD z = -Re Li₂ z` is written with the power-series
  `Li₂` at an argument in `[0, 1]` on each of `z ≤ 0`, `0 ≤ z ≤ 1`, `1 ≤ z`;
* `log (β - a)/(β - p)²` and `log (β - a)/(β - p)³` over intervals not containing `p`.

Main results:

* **`ksWY_hasDerivAt_ksWYD`**, `ksWY_continuous_ksWYD`: `ksWYD' z = log (1 - z)/z`;
* **`ksWY_integral_dq`**: `∫_l^u (log (β - a) - log (p - a))/(β - p) dβ` for any `l, u`;
* `ksWY_integral_q2`, `ksWY_integral_q3`: the double and triple poles;
* **`ksWY_piece`**: a function agreeing on `(l, u)` with a combination `ksWYe` of all these terms
  and those of `ksWPe`, `ksWPq` has the integral `ksWYv`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral QED.Polylog

namespace QED.ChainProof.SetAKS

/-- `-Re Li₂ z` on the real line, through the power-series `Li₂` at an argument in `[0, 1]`:
Landen's form for `z ≤ 0`, `-Li₂ z` on `[0, 1]`, the inversion form for `z ≥ 1`. -/
noncomputable def ksWYD (z : ℝ) : ℝ :=
  if z ≤ 0 then Li₂ (z / (z - 1)) + log (1 - z) ^ 2 / 2
  else if z ≤ 1 then -Li₂ z else Li₂ (1 / z) + log z ^ 2 / 2 - π ^ 2 / 3

theorem ksWY_ksWYD_of_nonpos {z : ℝ} (hz : z ≤ 0) :
    ksWYD z = Li₂ (z / (z - 1)) + log (1 - z) ^ 2 / 2 := by
  simp only [ksWYD, hz, ↓reduceIte]

theorem ksWY_ksWYD_of_mem {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) : ksWYD z = -Li₂ z := by
  unfold ksWYD
  rcases eq_or_lt_of_le hz.1 with h | h
  · subst h
    simp
  · simp only [not_le.2 h, hz.2, ↓reduceIte]

theorem ksWY_ksWYD_of_one_le {z : ℝ} (hz : 1 ≤ z) :
    ksWYD z = Li₂ (1 / z) + log z ^ 2 / 2 - π ^ 2 / 3 := by
  unfold ksWYD
  rcases eq_or_lt_of_le hz with h | h
  · subst h
    simp only [show ¬ ((1 : ℝ) ≤ 0) by norm_num, le_refl, ↓reduceIte, div_one, Real.log_one,
      Li₂_one]
    ring
  · simp only [show ¬ z ≤ 0 by linarith, not_le.2 h, ↓reduceIte]

theorem ksWY_landen_mem {z : ℝ} (hz : z ≤ 0) : z / (z - 1) ∈ Icc (-1 : ℝ) 1 := by
  have h1 : z - 1 < 0 := by linarith
  exact ⟨by linarith [div_nonneg_of_nonpos hz h1.le], (div_le_one_of_neg h1).2 (by linarith)⟩

theorem ksWY_inv_mem {z : ℝ} (hz : 1 ≤ z) : 1 / z ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith [one_div_pos.2 (by linarith : (0 : ℝ) < z)], (div_le_one (by linarith)).2 hz⟩

theorem ksWY_abs_lt_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : |x| < 1 :=
  abs_lt.2 ⟨by linarith [hx.1], hx.2⟩

theorem ksWY_continuous_ksWYD : Continuous ksWYD := by
  have c1 : ContinuousOn ksWYD (Iic 0) := by
    refine ContinuousOn.congr (f := fun z => Li₂ (z / (z - 1)) + log (1 - z) ^ 2 / 2) ?_
      fun z hz => ksWY_ksWYD_of_nonpos hz
    refine ContinuousOn.add (continuousOn_Li₂.comp ?_ fun z hz => ksWY_landen_mem hz) ?_
    · exact continuousOn_id.div (continuousOn_id.sub continuousOn_const)
        fun z hz => by simp only [mem_Iic] at hz; linarith
    · exact ((continuousOn_const.sub continuousOn_id).log
        fun z hz => by simp only [mem_Iic] at hz; simp only [Pi.sub_apply, id]; linarith).pow 2
        |>.div_const _
  have c2 : ContinuousOn ksWYD (Icc 0 1) :=
    (continuousOn_Li₂.mono fun z hz => ⟨by linarith [hz.1], hz.2⟩).neg.congr
      fun z hz => ksWY_ksWYD_of_mem hz
  have c3 : ContinuousOn ksWYD (Ici 1) := by
    refine ContinuousOn.congr (f := fun z => Li₂ (1 / z) + log z ^ 2 / 2 - π ^ 2 / 3) ?_
      fun z hz => ksWY_ksWYD_of_one_le hz
    refine ContinuousOn.sub (ContinuousOn.add (continuousOn_Li₂.comp ?_
      fun z hz => ksWY_inv_mem hz) ?_) continuousOn_const
    · exact continuousOn_const.div continuousOn_id
        fun z hz => by simp only [mem_Ici] at hz; linarith
    · exact (continuousOn_id.log fun z hz => by
        simp only [mem_Ici] at hz; simp only [id]; linarith).pow 2 |>.div_const _
  have h := (c1.union_of_isClosed c2 isClosed_Iic isClosed_Icc).union_of_isClosed c3
    (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  have e : Iic (0 : ℝ) ∪ Icc 0 1 ∪ Ici 1 = univ := by
    ext z
    simp only [mem_union, mem_Iic, mem_Icc, mem_Ici, mem_univ, iff_true]
    rcases le_total z 0 with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total z 1 with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr h'
  rw [e] at h
  exact continuousOn_univ.1 h

/-- **The derivative of `ksWYD`**: `log (1 - z)/z` (i.e. `log |1 - z|/z`) off `{0, 1}`. -/
theorem ksWY_hasDerivAt_ksWYD {z : ℝ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    HasDerivAt ksWYD (log (1 - z) / z) z := by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · -- Landen branch
    have hz1 : z - 1 < 0 := by linarith
    have hw : z / (z - 1) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos_of_neg_of_neg hn hz1, (div_lt_one_of_neg hz1).2 (by linarith)⟩
    have hL := (hasDerivAt_Li₂ (ksWY_abs_lt_one hw) hw.1.ne').comp z
      ((hasDerivAt_id z).div ((hasDerivAt_id z).sub_const 1) hz1.ne)
    have hl := (((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)).log
      (by simp; linarith)).pow 2 |>.div_const 2
    have e : ∀ᶠ y in 𝓝 z, Li₂ (y / (y - 1)) + log (1 - y) ^ 2 / 2 = ksWYD y :=
      (eventually_lt_nhds hn).mono fun y hy => (ksWY_ksWYD_of_nonpos hy.le).symm
    · refine (hL.add hl).congr_of_eventuallyEq (e.mono fun y hy => hy.symm) |>.congr_deriv ?_
      have e1 : 1 - z / (z - 1) = (1 - z)⁻¹ := by field_simp; ring
      simp only [id, e1, Real.log_inv, Pi.sub_apply]
      have : (1 : ℝ) - z ≠ 0 := by linarith
      field_simp
      ring
  · rcases lt_or_gt_of_ne h1 with h1' | h1'
    · have hw : z ∈ Ioo (0 : ℝ) 1 := ⟨hp, h1'⟩
      have hL := (hasDerivAt_Li₂ (ksWY_abs_lt_one hw) h0).neg
      have e : ∀ᶠ y in 𝓝 z, -Li₂ y = ksWYD y :=
        Filter.mem_of_superset (Ioo_mem_nhds hp h1') fun y hy =>
          (ksWY_ksWYD_of_mem ⟨hy.1.le, hy.2.le⟩).symm
      refine hL.congr_of_eventuallyEq (e.mono fun y hy => hy.symm) |>.congr_deriv ?_
      ring
    · have hz : (0 : ℝ) < z := by linarith
      have hw : 1 / z ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, (div_lt_one hz).2 h1'⟩
      have hL := (hasDerivAt_Li₂ (ksWY_abs_lt_one hw) hw.1.ne').comp z
        ((hasDerivAt_const z (1 : ℝ)).div (hasDerivAt_id z) hz.ne')
      have hl := ((hasDerivAt_id z).log hz.ne').pow 2 |>.div_const 2
      have e : ∀ᶠ y in 𝓝 z, Li₂ (1 / y) + log y ^ 2 / 2 - π ^ 2 / 3 = ksWYD y :=
        (eventually_gt_nhds h1').mono fun y hy => (ksWY_ksWYD_of_one_le hy.le).symm
      refine ((hL.add hl).sub_const (π ^ 2 / 3)).congr_of_eventuallyEq
        (e.mono fun y hy => hy.symm) |>.congr_deriv ?_
      have e1 : 1 - 1 / z = (z - 1) / z := by field_simp
      have e2 : log (1 - z) = log (z - 1) := by
        rw [show 1 - z = -(z - 1) by ring, Real.log_neg_eq_log]
      have e3 : log ((z - 1) / z) = log (z - 1) - log z :=
        Real.log_div (by linarith) hz.ne'
      simp only [id, e1, e2, e3]
      field_simp
      ring

/-! ### The difference quotient `(log (β - a) - log (p - a))/(β - p)` -/

/-- The difference quotient of `β ↦ log (β - a)` at `p`. -/
noncomputable def ksWYq (a p b : ℝ) : ℝ := (log (b - a) - log (p - a)) / (b - p)

theorem ksWY_ksWYq_eq_dslope {a p b : ℝ} (h : b ≠ p) :
    ksWYq a p b = dslope (fun x => log (x - a)) p b := by
  rw [dslope_of_ne _ h, slope_def_field, ksWYq]

theorem ksWY_ii_dslope {a p x y : ℝ} (ha : a ∉ uIcc x y) :
    IntervalIntegrable (dslope (fun t => log (t - a)) p) volume x y := by
  refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
  have hta : t - a ≠ 0 := sub_ne_zero.2 fun h => ha (h ▸ ht)
  by_cases htp : t = p
  · subst htp
    exact continuousAt_dslope_same.2 (((hasDerivAt_id t).sub_const a).log hta).differentiableAt
  · exact (continuousAt_dslope_of_ne htp).2
      ((continuous_id.sub continuous_const).continuousAt.log hta)

theorem ksWY_ii_log_mul {a l u : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc l u)) :
    IntervalIntegrable (fun t => g t * log (t - a)) volume l u := by
  have h := (intervalIntegrable_log' (a := l - a) (b := u - a)).comp_sub_right a
  simp only [sub_add_cancel] at h
  exact h.continuousOn_mul hg

theorem ksWY_ii_ksWYq_of_not_mem {a p x y : ℝ} (hp : p ∉ uIcc x y) :
    IntervalIntegrable (ksWYq a p) volume x y := by
  have hne : ∀ t ∈ uIcc x y, t - p ≠ 0 := fun t ht h => hp (sub_eq_zero.1 h ▸ ht)
  have hc : ContinuousOn (fun t => (t - p)⁻¹) (uIcc x y) := ContinuousOn.inv₀ (by fun_prop) hne
  have h1 := ksWY_ii_log_mul (a := a) hc
  have h3 : IntervalIntegrable (fun t => (t - p)⁻¹ * log (p - a)) volume x y :=
    (hc.mul continuousOn_const).intervalIntegrable
  convert h1.sub h3 using 1
  funext t
  simp only [ksWYq]
  ring

/-- The difference quotient is integrable over every interval. -/
theorem ksWY_intervalIntegrable_ksWYq {a p : ℝ} (hap : a ≠ p) (l u : ℝ) :
    IntervalIntegrable (ksWYq a p) volume l u := by
  have key : ∀ x, IntervalIntegrable (ksWYq a p) volume x ((a + p) / 2) := by
    intro x
    by_cases ha : a ∈ uIcc x ((a + p) / 2)
    · refine ksWY_ii_ksWYq_of_not_mem fun hp => hap ?_
      rcases le_total x ((a + p) / 2) with h | h
      · rw [uIcc_of_le h] at ha hp
        linarith [ha.2, hp.2]
      · rw [uIcc_of_ge h] at ha hp
        linarith [ha.1, hp.1]
    · refine (ksWY_ii_dslope (p := p) ha).congr_ae ?_
      exact (ae_restrict_of_ae (Measure.ae_ne volume p)).mono fun t ht =>
        (ksWY_ksWYq_eq_dslope ht).symm
  exact (key l).trans (key u).symm

/-- **The integral of the difference quotient**, over any interval:
`∫_l^u (log (β - a) - log (p - a))/(β - p) dβ = ksWYD ((u-p)/(a-p)) - ksWYD ((l-p)/(a-p))`. -/
theorem ksWY_integral_ksWYq {a p : ℝ} (hap : a ≠ p) (l u : ℝ) :
    ∫ b in l..u, ksWYq a p b = ksWYD ((u - p) / (a - p)) - ksWYD ((l - p) / (a - p)) := by
  have hap' : a - p ≠ 0 := sub_ne_zero.2 hap
  refine integral_eq_of_hasDerivAt_off_countable (fun b => ksWYD ((b - p) / (a - p))) _
    ((countable_singleton a).insert p)
    ((ksWY_continuous_ksWYD.comp (by fun_prop)).continuousOn) (fun b hb => ?_)
    (ksWY_intervalIntegrable_ksWYq hap l u)
  simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or] at hb
  obtain ⟨-, hbp, hba⟩ := hb
  have hbp' : b - p ≠ 0 := sub_ne_zero.2 hbp
  have hz0 : (b - p) / (a - p) ≠ 0 := div_ne_zero hbp' hap'
  have hz1 : (b - p) / (a - p) ≠ 1 := fun h => hba (by
    rw [div_eq_one_iff_eq hap'] at h
    linarith)
  have h := (ksWY_hasDerivAt_ksWYD hz0 hz1).comp b
    (((hasDerivAt_id b).sub_const p).div_const (a - p))
  refine h.congr_deriv ?_
  have e1 : 1 - (b - p) / (a - p) = (a - b) / (a - p) := by field_simp; ring
  have e2 : log ((a - b) / (a - p)) = log (b - a) - log (p - a) := by
    rw [Real.log_div (sub_ne_zero.2 (Ne.symm hba)) hap', show a - b = -(b - a) by ring,
      show a - p = -(p - a) by ring, Real.log_neg_eq_log, Real.log_neg_eq_log]
  rw [e1, e2, ksWYq]
  field_simp

/-! ### Double and triple poles off the interval -/

/-- A primitive of `log (β - a)/(β - p)²` (`a ≠ p`). -/
noncomputable def ksWYG2 (a p b : ℝ) : ℝ :=
  (b - a) * log (b - a) / ((a - p) * (b - p)) - log (b - p) / (a - p)

/-- A primitive of `log (β - a)/(β - p)³` (`a ≠ p`). -/
noncomputable def ksWYG3 (a p b : ℝ) : ℝ :=
  (b - a) * log (b - a) * ((b - p) + (a - p)) / (2 * (a - p) ^ 2 * (b - p) ^ 2) -
    (log (b - p) / (2 * (a - p) ^ 2) - 1 / (2 * (a - p) * (b - p)))

theorem ksWY_continuous_mul_log (a : ℝ) : Continuous fun b : ℝ => (b - a) * log (b - a) :=
  continuous_mul_log.comp (continuous_id.sub continuous_const)

theorem ksWY_hasDerivAt_mul_log {a b : ℝ} (h : b ≠ a) :
    HasDerivAt (fun b : ℝ => (b - a) * log (b - a)) (log (b - a) + 1) b := by
  have hba : b - a ≠ 0 := sub_ne_zero.2 h
  have := ((hasDerivAt_id b).sub_const a).mul (((hasDerivAt_id b).sub_const a).log hba)
  refine this.congr_deriv ?_
  simp only [id_eq]
  field_simp

theorem ksWY_integral_q2 {a p l u : ℝ} (hap : a ≠ p) (hp : p ∉ uIcc l u) :
    IntervalIntegrable (fun b => log (b - a) / (b - p) ^ 2) volume l u ∧
      ∫ b in l..u, log (b - a) / (b - p) ^ 2 = ksWYG2 a p u - ksWYG2 a p l := by
  have hap' : a - p ≠ 0 := sub_ne_zero.2 hap
  have hne : ∀ t ∈ uIcc l u, t - p ≠ 0 := fun t ht h => hp (sub_eq_zero.1 h ▸ ht)
  have hi : IntervalIntegrable (fun b => log (b - a) / (b - p) ^ 2) volume l u := by
    have hc : ContinuousOn (fun t => ((t - p) ^ 2)⁻¹) (uIcc l u) :=
      ContinuousOn.inv₀ (by fun_prop) fun t ht => pow_ne_zero 2 (hne t ht)
    convert ksWY_ii_log_mul (a := a) hc using 1
    funext t
    ring
  refine ⟨hi, integral_eq_of_hasDerivAt_off_countable (ksWYG2 a p) _ (countable_singleton a)
    ?_ (fun b hb => ?_) hi⟩
  · unfold ksWYG2
    refine ContinuousOn.sub ?_ ?_
    · exact (ksWY_continuous_mul_log a).continuousOn.div (by fun_prop)
        fun t ht => mul_ne_zero hap' (hne t ht)
    · exact ((continuousOn_id.sub continuousOn_const).log hne).div_const _
  · have hbp : b - p ≠ 0 := hne b (Ioo_subset_Icc_self hb.1)
    have hba : b ≠ a := hb.2
    have h := (((ksWY_hasDerivAt_mul_log hba).div (((hasDerivAt_id b).sub_const p).const_mul
      (a - p)) (mul_ne_zero hap' hbp)).sub
      ((((hasDerivAt_id b).sub_const p).log hbp).div_const (a - p)))
    refine h.congr_deriv ?_
    simp only [id_eq] at h ⊢
    field_simp
    ring

theorem ksWY_integral_q3 {a p l u : ℝ} (hap : a ≠ p) (hp : p ∉ uIcc l u) :
    IntervalIntegrable (fun b => log (b - a) / (b - p) ^ 3) volume l u ∧
      ∫ b in l..u, log (b - a) / (b - p) ^ 3 = ksWYG3 a p u - ksWYG3 a p l := by
  have hap' : a - p ≠ 0 := sub_ne_zero.2 hap
  have hne : ∀ t ∈ uIcc l u, t - p ≠ 0 := fun t ht h => hp (sub_eq_zero.1 h ▸ ht)
  have hi : IntervalIntegrable (fun b => log (b - a) / (b - p) ^ 3) volume l u := by
    have hc : ContinuousOn (fun t => ((t - p) ^ 3)⁻¹) (uIcc l u) :=
      ContinuousOn.inv₀ (by fun_prop) fun t ht => pow_ne_zero 3 (hne t ht)
    convert ksWY_ii_log_mul (a := a) hc using 1
    funext t
    ring
  refine ⟨hi, integral_eq_of_hasDerivAt_off_countable (ksWYG3 a p) _ (countable_singleton a)
    ?_ (fun b hb => ?_) hi⟩
  · unfold ksWYG3
    refine ContinuousOn.sub ?_ (ContinuousOn.sub ?_ ?_)
    · exact ((ksWY_continuous_mul_log a).continuousOn.mul (by fun_prop)).div (by fun_prop)
        fun t ht => mul_ne_zero (by positivity) (pow_ne_zero 2 (hne t ht))
    · exact ((continuousOn_id.sub continuousOn_const).log hne).div_const _
    · exact continuousOn_const.div (by fun_prop) fun t ht => mul_ne_zero (by positivity) (hne t ht)
  · have hbp : b - p ≠ 0 := hne b (Ioo_subset_Icc_self hb.1)
    have hba : b ≠ a := hb.2
    have h1 := (ksWY_hasDerivAt_mul_log hba).mul (((hasDerivAt_id b).sub_const p).add_const
      (a - p))
    have h2 := ((((hasDerivAt_id b).sub_const p).pow 2).const_mul (2 * (a - p) ^ 2))
    have h3 := (((hasDerivAt_id b).sub_const p).log hbp).div_const (2 * (a - p) ^ 2)
    have h4 := (((hasDerivAt_id b).sub_const p).const_mul (2 * (a - p))).inv
      (mul_ne_zero (by positivity) hbp)
    have h := (h1.div h2 (mul_ne_zero (by positivity) (pow_ne_zero 2 hbp))).sub (h3.sub h4)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
    · simp only [ksWYG3, one_div, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.inv_apply,
        Pi.pow_apply, id_eq]
    · simp only [id_eq, Pi.mul_apply, Pi.pow_apply]
      field_simp
      ring

theorem ksWY_integral_r3 {p c l u : ℝ} (hp : p ∉ uIcc l u) :
    IntervalIntegrable (fun b => c / (b - p) ^ 3) volume l u ∧
      ∫ b in l..u, c / (b - p) ^ 3 = -(c / (2 * (u - p) ^ 2)) + c / (2 * (l - p) ^ 2) := by
  have hne : ∀ t ∈ uIcc l u, t - p ≠ 0 := fun t ht h => hp (sub_eq_zero.1 h ▸ ht)
  have hc : ContinuousOn (fun b => c / (b - p) ^ 3) (uIcc l u) :=
    continuousOn_const.div (by fun_prop) fun t ht => pow_ne_zero 3 (hne t ht)
  refine ⟨hc.intervalIntegrable, ?_⟩
  rw [integral_eq_sub_of_hasDerivAt (f := fun b => -(c / (2 * (b - p) ^ 2))) (fun b hb => ?_)
    hc.intervalIntegrable]
  · ring
  · have hbp := hne b hb
    have h := ((((hasDerivAt_id b).sub_const p).pow 2).const_mul 2).inv
      (mul_ne_zero two_ne_zero (pow_ne_zero 2 hbp)) |>.const_mul c |>.neg
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
    · simp only [div_eq_mul_inv, Pi.neg_apply, Pi.inv_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq, Pi.pow_apply]
      field_simp
      ring

/-! ### Finite combinations -/

theorem ksWY_list {α : Type*} (D : List α) (f : α → ℝ → ℝ) (v : α → ℝ) {l u : ℝ}
    (h : ∀ t ∈ D, IntervalIntegrable (f t) volume l u ∧ ∫ b in l..u, f t b = v t) :
    IntervalIntegrable (fun b => (D.map fun t => f t b).sum) volume l u ∧
      ∫ b in l..u, (D.map fun t => f t b).sum = (D.map v).sum := by
  induction D with
  | nil => simp
  | cons t D ih =>
    obtain ⟨i1, v1⟩ := h t List.mem_cons_self
    obtain ⟨i2, v2⟩ := ih fun s hs => h s (List.mem_cons_of_mem t hs)
    simp only [List.map_cons, List.sum_cons]
    exact ⟨i1.add i2, by rw [integral_add i1 i2, v1, v2]⟩

/-- A finite combination of the terms `ksWPe L P`, `c · ksWYq a p` (list `D` of `(c, a, p)`),
`c log (β - a)/(β - p)²`, `c log (β - a)/(β - p)³` (lists `Q₂`, `Q₃` of `(c, a, p)`), the
pole terms `ksWPq p c₁ c₂` (list `R` of `(p, c₁, c₂)`) and `c/(β - p)³` (list `S` of `(p, c)`). -/
noncomputable def ksWYe (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ)) (D Q₂ Q₃ R : List (ℝ × ℝ × ℝ))
    (S : List (ℝ × ℝ)) (b : ℝ) : ℝ :=
  ksWPe L P b + (D.map fun t => t.1 * ksWYq t.2.1 t.2.2 b).sum +
    (Q₂.map fun t => t.1 * (log (b - t.2.1) / (b - t.2.2) ^ 2)).sum +
    (Q₃.map fun t => t.1 * (log (b - t.2.1) / (b - t.2.2) ^ 3)).sum +
    (R.map fun t => ksWPq t.1 t.2.1 t.2.2 b).sum + (S.map fun t => t.2 / (b - t.1) ^ 3).sum

/-- The integral of `ksWYe` over `[l, u]`. -/
noncomputable def ksWYv (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ)) (D Q₂ Q₃ R : List (ℝ × ℝ × ℝ))
    (S : List (ℝ × ℝ)) (l u : ℝ) : ℝ :=
  ksWPv L P l u +
    (D.map fun t => t.1 * (ksWYD ((u - t.2.2) / (t.2.1 - t.2.2)) -
      ksWYD ((l - t.2.2) / (t.2.1 - t.2.2)))).sum +
    (Q₂.map fun t => t.1 * (ksWYG2 t.2.1 t.2.2 u - ksWYG2 t.2.1 t.2.2 l)).sum +
    (Q₃.map fun t => t.1 * (ksWYG3 t.2.1 t.2.2 u - ksWYG3 t.2.1 t.2.2 l)).sum +
    (R.map fun t => ksWPQ t.1 t.2.1 t.2.2 u - ksWPQ t.1 t.2.1 t.2.2 l).sum +
    (S.map fun t => -(t.2 / (2 * (u - t.1) ^ 2)) + t.2 / (2 * (l - t.1) ^ 2)).sum

/-- **The integral of a combination `ksWYe`**: all difference quotients have `a ≠ p`, the double
and triple poles have `a ≠ p ∉ [l, u]`, the pole terms `p ∉ [l, u]`. -/
theorem ksWY_integral_ksWYe (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ))
    (D Q₂ Q₃ R : List (ℝ × ℝ × ℝ)) (S : List (ℝ × ℝ)) {l u : ℝ} (hD : ∀ t ∈ D, t.2.1 ≠ t.2.2)
    (h₂ : ∀ t ∈ Q₂, t.2.1 ≠ t.2.2 ∧ t.2.2 ∉ uIcc l u)
    (h₃ : ∀ t ∈ Q₃, t.2.1 ≠ t.2.2 ∧ t.2.2 ∉ uIcc l u) (hR : ∀ t ∈ R, t.1 ∉ uIcc l u)
    (hS : ∀ t ∈ S, t.1 ∉ uIcc l u) :
    IntervalIntegrable (ksWYe L P D Q₂ Q₃ R S) volume l u ∧
      ∫ b in l..u, ksWYe L P D Q₂ Q₃ R S b = ksWYv L P D Q₂ Q₃ R S l u := by
  have i0 := ksWP_intervalIntegrable_ksWPe L P l u
  obtain ⟨i1, v1⟩ := ksWY_list D (fun t b => t.1 * ksWYq t.2.1 t.2.2 b)
    (fun t => t.1 * (ksWYD ((u - t.2.2) / (t.2.1 - t.2.2)) -
      ksWYD ((l - t.2.2) / (t.2.1 - t.2.2)))) (l := l) (u := u) fun t ht =>
    ⟨(ksWY_intervalIntegrable_ksWYq (hD t ht) l u).const_mul _, by
      rw [intervalIntegral.integral_const_mul, ksWY_integral_ksWYq (hD t ht)]⟩
  obtain ⟨i2, v2⟩ := ksWY_list Q₂ (fun t b => t.1 * (log (b - t.2.1) / (b - t.2.2) ^ 2))
    (fun t => t.1 * (ksWYG2 t.2.1 t.2.2 u - ksWYG2 t.2.1 t.2.2 l)) fun t ht =>
    ⟨(ksWY_integral_q2 (h₂ t ht).1 (h₂ t ht).2).1.const_mul _, by
      rw [intervalIntegral.integral_const_mul, (ksWY_integral_q2 (h₂ t ht).1 (h₂ t ht).2).2]⟩
  obtain ⟨i3, v3⟩ := ksWY_list Q₃ (fun t b => t.1 * (log (b - t.2.1) / (b - t.2.2) ^ 3))
    (fun t => t.1 * (ksWYG3 t.2.1 t.2.2 u - ksWYG3 t.2.1 t.2.2 l)) fun t ht =>
    ⟨(ksWY_integral_q3 (h₃ t ht).1 (h₃ t ht).2).1.const_mul _, by
      rw [intervalIntegral.integral_const_mul, (ksWY_integral_q3 (h₃ t ht).1 (h₃ t ht).2).2]⟩
  obtain ⟨i4, v4⟩ := ksWY_list R (fun t b => ksWPq t.1 t.2.1 t.2.2 b)
    (fun t => ksWPQ t.1 t.2.1 t.2.2 u - ksWPQ t.1 t.2.1 t.2.2 l) fun t ht =>
    ksWP_integral_ksWPq t.1 t.2.1 t.2.2 (hR t ht)
  obtain ⟨i5, v5⟩ := ksWY_list S (fun t b => t.2 / (b - t.1) ^ 3)
    (fun t => -(t.2 / (2 * (u - t.1) ^ 2)) + t.2 / (2 * (l - t.1) ^ 2)) fun t ht =>
    ksWY_integral_r3 (hS t ht)
  refine ⟨((((i0.add i1).add i2).add i3).add i4).add i5, ?_⟩
  unfold ksWYe ksWYv
  rw [integral_add ((((i0.add i1).add i2).add i3).add i4) i5,
    integral_add (((i0.add i1).add i2).add i3) i4, integral_add ((i0.add i1).add i2) i3,
    integral_add (i0.add i1) i2, integral_add i0 i1, ksWP_integral_ksWPe, v1, v2, v3, v4, v5]

/-- **A function agreeing with `ksWYe` on `(l, u)`** has the integral `ksWYv` over `[l, u]`. -/
theorem ksWY_piece {f : ℝ → ℝ} (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ))
    (D Q₂ Q₃ R : List (ℝ × ℝ × ℝ)) (S : List (ℝ × ℝ)) {l u : ℝ} (hlu : l ≤ u)
    (hD : ∀ t ∈ D, t.2.1 ≠ t.2.2) (h₂ : ∀ t ∈ Q₂, t.2.1 ≠ t.2.2 ∧ t.2.2 ∉ uIcc l u)
    (h₃ : ∀ t ∈ Q₃, t.2.1 ≠ t.2.2 ∧ t.2.2 ∉ uIcc l u) (hR : ∀ t ∈ R, t.1 ∉ uIcc l u)
    (hS : ∀ t ∈ S, t.1 ∉ uIcc l u) (h : EqOn (ksWYe L P D Q₂ Q₃ R S) f (Ioo l u)) :
    IntervalIntegrable f volume l u ∧ ∫ b in l..u, f b = ksWYv L P D Q₂ Q₃ R S l u := by
  obtain ⟨i, v⟩ := ksWY_integral_ksWYe L P D Q₂ Q₃ R S hD h₂ h₃ hR hS
  exact ⟨i.congr_uIoo (uIoo_of_le hlu ▸ h), by rw [← integral_congr_Ioo_of_le hlu h, v]⟩

end QED.ChainProof.SetAKS

end
