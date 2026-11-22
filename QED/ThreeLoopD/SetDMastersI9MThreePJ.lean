/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import QED.Polylog.HPLBasic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.ThreeLoopD.SetDMastersI9MInner
import QED.Polylog.ExtraIntegrals
import QED.Polylog.HPLCalculus
import QED.Polylog.HPLLowWeight
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Set (d), master `I₉`: tools for the weight-three `x`-integrals of `M₃`

Fix `w ∈ (0, 1)` and write `u = 1 - w`, `A = w + u x`, `B = 1 - u x`. The weight-three pieces
`P₆, P₇, P₈, P₉` of `M₃` (`QED.ThreeLoopD.SetDMastersI9MThreePA`, `...MThreePB`) are computed
as functions of `w`: we differentiate under the integral sign, evaluate the derivative
`x`-integrals (weight two) by explicit dilogarithm antiderivatives, and fix the constant by
dominated convergence as `w → 0⁺`.

This file contains

* generic tools: differentiation under `∫₀¹` with a local domination
  (`QED.ThreeLoopD.i9M3P_hasDerivAt_integral`), dominated convergence as `w → 0⁺`
  (`QED.ThreeLoopD.i9M3P_tendsto_integral`), and uniqueness of a function with given
  derivative and limit at `0⁺` (`QED.ThreeLoopD.i9M3P_eq_of_deriv`);
* `∫₀¹ log² x / (1 - x) = 2ζ(3)` (`QED.ThreeLoopD.i9M3P_logSq_div`);
* the weight-two derivative integrals `QED.ThreeLoopD.i9M3P_h6`, `QED.ThreeLoopD.i9M3P_logX_divA`,
  `QED.ThreeLoopD.i9M3P_h9` and `QED.ThreeLoopD.i9M3P_h8`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### Generic tools -/

theorem i9M3P_iff {f : ℝ → ℝ} :
    IntervalIntegrable f volume 0 1 ↔ IntegrableOn f (Ioo (0 : ℝ) 1) :=
  intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one

theorem i9M3P_integral_eq (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, f x = ∫ x in Ioo (0 : ℝ) 1, f x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

theorem i9M3P_intervalIntegrable {f bnd : ℝ → ℝ} (hf : ContinuousOn f (Ioo 0 1))
    (hb : IntervalIntegrable bnd volume 0 1) (hbd : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ bnd x) :
    IntervalIntegrable f volume 0 1 :=
  i9M3P_iff.2 (Integrable.mono' (i9M3P_iff.1 hb) (hf.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => by
      rw [Real.norm_eq_abs]; exact hbd x hx)))

theorem i9M3P_hasDerivAt_integral {g g' : ℝ → ℝ → ℝ} {bnd : ℝ → ℝ} {s : Set ℝ} {w₀ : ℝ}
    (hs : s ∈ 𝓝 w₀) (hg : ∀ w ∈ s, ContinuousOn (g w) (Ioo 0 1))
    (hg' : ContinuousOn (g' w₀) (Ioo 0 1)) (hint : IntervalIntegrable (g w₀) volume 0 1)
    (hb : IntervalIntegrable bnd volume 0 1)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w ∈ s, HasDerivAt (fun w => g w x) (g' w x) w)
    (hbd : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w ∈ s, |g' w x| ≤ bnd x) :
    IntervalIntegrable (g' w₀) volume 0 1 ∧
      HasDerivAt (fun w => ∫ x in (0 : ℝ)..1, g w x) (∫ x in (0 : ℝ)..1, g' w₀ x) w₀ := by
  obtain ⟨h1, h2⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (F := g) (F' := g') (bound := bnd) hs
    (Filter.mem_of_superset hs fun w hw => (hg w hw).aestronglyMeasurable measurableSet_Ioo)
    (i9M3P_iff.1 hint) (hg'.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx w hw => by
      rw [Real.norm_eq_abs]; exact hbd x hx w hw))
    (i9M3P_iff.1 hb)
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx w hw => hd x hx w hw))
  refine ⟨i9M3P_iff.2 h1, ?_⟩
  simp only [i9M3P_integral_eq]
  exact h2

theorem i9M3P_tendsto_integral {g : ℝ → ℝ → ℝ} {g₀ bnd : ℝ → ℝ}
    (hg : ∀ w ∈ Ioo (0 : ℝ) 1, ContinuousOn (g w) (Ioo 0 1))
    (hb : IntervalIntegrable bnd volume 0 1)
    (hbd : ∀ w ∈ Ioo (0 : ℝ) 1, ∀ x ∈ Ioo (0 : ℝ) 1, |g w x| ≤ bnd x)
    (hlim : ∀ x ∈ Ioo (0 : ℝ) 1, Tendsto (fun w => g w x) (𝓝[>] 0) (𝓝 (g₀ x))) :
    Tendsto (fun w => ∫ x in (0 : ℝ)..1, g w x) (𝓝[>] 0) (𝓝 (∫ x in (0 : ℝ)..1, g₀ x)) := by
  simp only [i9M3P_integral_eq]
  have hev : ∀ᶠ w in 𝓝[>] (0 : ℝ), w ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  refine tendsto_integral_filter_of_dominated_convergence bnd
    (hev.mono fun w hw => (hg w hw).aestronglyMeasurable measurableSet_Ioo)
    (hev.mono fun w hw => (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => by
      rw [Real.norm_eq_abs]; exact hbd w hw x hx))
    (i9M3P_iff.1 hb) ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ hlim))

theorem i9M3P_eq_of_deriv {V T D : ℝ → ℝ} {c : ℝ}
    (hV : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivAt V (D w) w)
    (hT : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivAt T (D w) w)
    (hV0 : Tendsto V (𝓝[>] 0) (𝓝 c)) (hT0 : Tendsto T (𝓝[>] 0) (𝓝 c)) :
    ∀ w ∈ Ioo (0 : ℝ) 1, V w = T w := by
  have h := HPL.eq_of_hasDerivAt_zero_of_tendsto_right (F := fun w => V w - T w) (c := c - c)
    zero_lt_one (fun w hw => by
      have := (hV w hw).sub (hT w hw); rwa [sub_self] at this) (hV0.sub hT0)
  intro w hw
  have := h w hw
  simp only [sub_self] at this
  linarith

theorem i9M3P_nhds {w₀ : ℝ} (hw : w₀ ∈ Ioo (0 : ℝ) 1) :
    Ioo (w₀ / 2) ((1 + w₀) / 2) ∈ 𝓝 w₀ :=
  Ioo_mem_nhds (by linarith [hw.1]) (by linarith [hw.2])

theorem i9M3P_mem {w₀ w : ℝ} (hw₀ : w₀ ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (w₀ / 2) ((1 + w₀) / 2)) :
    w ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith [hw.1, hw₀.1], by linarith [hw.2, hw₀.2]⟩

theorem i9M3P_hasDerivAt_Aw (w x : ℝ) : HasDerivAt (fun w => w + (1 - w) * x) (1 - x) w := by
  have := (hasDerivAt_id w).add (((hasDerivAt_id w).const_sub 1).mul_const x)
  refine this.congr_deriv ?_
  ring

theorem i9M3P_hasDerivAt_Bw (w x : ℝ) : HasDerivAt (fun w => 1 - (1 - w) * x) x w := by
  have := (((hasDerivAt_id w).const_sub 1).mul_const x).const_sub 1
  refine this.congr_deriv ?_
  ring

/-- `-log y ≤ (1 - y)/y` for `y > 0`. -/
theorem i9M3P_neg_log_le {y : ℝ} (hy : 0 < y) : -Real.log y ≤ (1 - y) / y := by
  have := Real.log_le_sub_one_of_pos (inv_pos.2 hy)
  rw [Real.log_inv] at this
  have e : y⁻¹ - 1 = (1 - y) / y := by field_simp
  linarith

theorem i9M3P_tendsto_log_mul {v : List Letter} (hv : ¬AllZero v) :
    Tendsto (fun w => Real.log w * hpl v w) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_hpl_mul_hpl_zero (u := [zero]) (v := v) (by simp [hv])
  simpa only [hpl_zero] using h

theorem i9M3P_tendsto_log_sq_mul {v : List Letter} (hv : ¬AllZero v) :
    Tendsto (fun w => Real.log w ^ 2 * hpl v w) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_hpl_mul_hpl_zero (u := [zero, zero]) (v := v) (by simp [hv])).const_mul 2
  rw [mul_zero] at h
  refine h.congr fun w => ?_
  rw [hpl_zero_zero]
  ring

theorem i9M3P_hpl_tendsto {v : List Letter} (hv : ¬AllZero v) :
    Tendsto (hpl v) (𝓝[>] 0) (𝓝 0) := tendsto_hpl_zero hv

/-! ### Elementary bounds on `A` and `B` -/

theorem i9M3P_le_A {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ≤ 1) : x ≤ w + (1 - w) * x := by
  have := mul_nonneg hw.1.le (sub_nonneg.2 hx)
  linarith

theorem i9M3P_le_B {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : 0 ≤ x) :
    1 - x ≤ 1 - (1 - w) * x := by
  have := mul_nonneg hw.1.le hx
  linarith

theorem i9M3P_w_le_A {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : 0 ≤ x) : w ≤ w + (1 - w) * x := by
  have := mul_nonneg (sub_nonneg.2 hw.2.le) hx
  linarith

theorem i9M3P_w_le_B {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ≤ 1) :
    w ≤ 1 - (1 - w) * x := by
  have := mul_le_mul_of_nonneg_left hx (sub_nonneg.2 hw.2.le)
  linarith


/-! ### Weight-two `x`-integrals -/

theorem i9M3P_logSq_div :
    IntervalIntegrable (fun x => Real.log x ^ 2 / (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x ^ 2 / (1 - x) = 2 * zeta3 := by
  obtain ⟨h1, h2⟩ := intervalIntegrable_and_integral_log_one_sub_sq_div
  have hi := (h1.comp_sub_left 1).symm
  simp only [sub_sub_cancel, sub_self, sub_zero] at hi
  refine ⟨hi, ?_⟩
  have := intervalIntegral.integral_comp_sub_left (fun x => Real.log (1 - x) ^ 2 / x)
    (a := 0) (b := 1) 1
  simp only [sub_sub_cancel, sub_self, sub_zero] at this
  rw [this, h2]


/-- `log (1 - x) log A → 0` as `x → 1⁻`. -/
theorem i9M3P_tendsto_logOneSub_mul_logA {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Real.log (1 - x) * Real.log (w + (1 - w) * x)) (𝓝[<] 1) (𝓝 0) := by
  have h := (i9M2_tendsto_log_mul_log_one_sub (t := 1 - w) (by linarith [hw.2])
    (by linarith [hw.1])).comp tendsto_one_sub_nhdsLT_one
  refine h.congr fun x => ?_
  simp only [Function.comp_apply]
  ring_nf

/-- The antiderivative of `(1 - x) log (1 - x) / (x A)`. -/
noncomputable def i9M3P_F6 (w x : ℝ) : ℝ :=
  (-Li₂ x - (Li₂ ((1 - w) * (1 - x)) + Real.log (1 - x) * Real.log (w + (1 - w) * x)) /
    (1 - w)) / w

/-- `∫₀¹ (1 - x) log (1 - x) / (x A) = (-π²/6 + Li₂ (1 - w)/(1 - w))/w`. -/
theorem i9M3P_h6 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - x) / (w + (1 - w) * x) * Real.log (1 - x) / x)
      volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - x) / (w + (1 - w) * x) * Real.log (1 - x) / x =
        (-(π ^ 2 / 6) + Li₂ (1 - w) / (1 - w)) / w := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (i9M3P_F6 w)
      ((1 - x) / (w + (1 - w) * x) * Real.log (1 - x) / x) x := by
    intro x hx
    have hx0 := hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx0.le
    have h1 := i9M2_hasDerivAt_A w x
    have hlA := h1.log hAx.ne'
    have hs := (hasDerivAt_id x).const_sub 1
    have hlq := hs.log hx1.ne'
    have hz1 : (1 - w) * (1 - id x) ∈ Ioo (0 : ℝ) 1 :=
      ⟨by simp only [id]; positivity, by simp only [id]; nlinarith⟩
    have hLi := (hasDerivAt_Li₂' hz1).comp x (hs.const_mul (1 - w))
    have hLx := hasDerivAt_Li₂' hx
    have hG := ((hLx.neg.sub ((hLi.add (hlq.mul hlA)).div_const (1 - w))).div_const w)
    refine hG.congr_deriv ?_
    simp only [id]
    have e1 : 1 - (1 - w) * (1 - x) = w + (1 - w) * x := by ring
    rw [e1]
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, (1 - x) / (w + (1 - w) * x) * Real.log (1 - x) / x ≤ 0 :=
    fun x hx => div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (by linarith [hx.2]) (i9M2_A_pos hw hx.1.le).le)
      (Real.log_nonpos (by linarith [hx.2]) (by linarith [hx.1]))) hx.1.le
  -- limits at `0⁺`
  have hlA0 : Tendsto (fun x => Real.log (w + (1 - w) * x)) (𝓝[>] 0)
      (𝓝 (Real.log (w + (1 - w) * 0))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => w + (1 - w) * x) 0).log (by simp; exact hw0.ne'))
  have hlq0 : Tendsto (fun x => Real.log (1 - x)) (𝓝[>] 0) (𝓝 (Real.log (1 - 0))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (1 - x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => 1 - x) 0).log (by simp))
  have hLi0 : Tendsto (fun x => Li₂ ((1 - w) * (1 - x))) (𝓝[>] 0)
      (𝓝 (Li₂ ((1 - w) * (1 - 0)))) := by
    refine tendsto_Li₂_comp ⟨by simp; linarith, by simp; linarith⟩
      (i9M2_tendsto_of_continuousAt (by fun_prop)) ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by nlinarith [hx.2], by nlinarith [hx.1, hx.2]⟩
  have hA := ((tendsto_Li₂_zero_right.neg.sub ((hLi0.add (hlq0.mul hlA0)).div_const
    (1 - w))).div_const w)
  -- limits at `1⁻`
  have hLi1 : Tendsto (fun x => Li₂ ((1 - w) * (1 - x))) (𝓝[<] 1)
      (𝓝 (Li₂ ((1 - w) * (1 - 1)))) := by
    refine tendsto_Li₂_comp ⟨by simp, by simp⟩
      (i9M2_tendsto_of_continuousAt (by fun_prop)) ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by nlinarith [hx.2], by nlinarith [hx.1, hx.2]⟩
  have hB := ((tendsto_Li₂_one_left.neg.sub ((hLi1.add
    (i9M3P_tendsto_logOneSub_mul_logA hw)).div_const (1 - w))).div_const w)
  have h := intervalIntegrable_and_integral_eq_of_nonpos (F := fun x => i9M3P_F6 w x) hd hf
    (by simpa only [i9M3P_F6] using hA) (by simpa only [i9M3P_F6] using hB)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [mul_one, mul_zero, sub_zero, sub_self, Li₂_zero, Real.log_one, zero_mul,
    add_zero, neg_zero]
  field_simp
  ring

/-- The antiderivative of `((1 - x) log B / A + x log A / B)/x`. -/
noncomputable def i9M3P_F9 (w x : ℝ) : ℝ :=
  -Li₂ ((1 - w) * x) / w + (Li₂ ((w + (1 - w) * x) / (1 + w)) -
    Real.log (w + (1 - w) * x) * Real.log (1 + w)) / w -
    Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / (1 - w)

/-- The `w`-derivative integral of `P₉`. -/
theorem i9M3P_h9 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => ((1 - x) / (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) +
        Real.log (w + (1 - w) * x) * (x / (1 - (1 - w) * x))) / x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, ((1 - x) / (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) +
        Real.log (w + (1 - w) * x) * (x / (1 - (1 - w) * x))) / x =
        (-Li₂ (1 - w) + Li₂ (1 / (1 + w)) - Li₂ (w / (1 + w)) +
          Real.log w * Real.log (1 + w)) / w := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hp : 0 < 1 + w := by linarith
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (i9M3P_F9 w)
      (((1 - x) / (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) +
        Real.log (w + (1 - w) * x) * (x / (1 - (1 - w) * x))) / x) x := by
    intro x hx
    have hx0 := hx.1
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx0.le
    have hBx : 0 < 1 - (1 - w) * x := i9M2_B_pos hw hx.2.le
    have h1 := i9M2_hasDerivAt_A w x
    have h2 := i9M2_hasDerivAt_B w x
    have hlA := h1.log hAx.ne'
    have hlB := h2.log hBx.ne'
    have hz1 : (1 - w) * id x ∈ Ioo (0 : ℝ) 1 :=
      ⟨by simp only [id]; positivity, by simp only [id]; nlinarith [hx.2]⟩
    have hL1 := (hasDerivAt_Li₂' hz1).comp x ((hasDerivAt_id x).const_mul (1 - w))
    have hAa : (w + (1 - w) * x) / (1 + w) ∈ Ioo (0 : ℝ) 1 :=
      ⟨by positivity, by rw [div_lt_one hp]; nlinarith [hx.2]⟩
    have hL2 := (hasDerivAt_Li₂' hAa).comp x (h1.div_const (1 + w))
    have hG := ((hL1.neg.div_const w).add ((hL2.sub (hlA.mul_const (Real.log (1 + w)))).div_const
      w)).sub ((hlA.mul hlB).div_const (1 - w))
    refine hG.congr_deriv ?_
    simp only [id]
    have e2 : 1 - (w + (1 - w) * x) / (1 + w) = (1 - (1 - w) * x) / (1 + w) := by
      field_simp; ring
    rw [e2, Real.log_div hBx.ne' hp.ne']
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, ((1 - x) / (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) +
        Real.log (w + (1 - w) * x) * (x / (1 - (1 - w) * x))) / x ≤ 0 := by
    intro x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    have hBx : 0 < 1 - (1 - w) * x := i9M2_B_pos hw hx.2.le
    refine div_nonpos_of_nonpos_of_nonneg (add_nonpos (mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (by linarith [hx.2]) hAx.le) (Real.log_nonpos hBx.le (i9M2_B_le hw hx.1.le)))
      (mul_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hAx.le (i9M2_A_le hw hx.2.le))
      (div_nonneg hx.1.le hBx.le))) hx.1.le
  have hc : ContinuousOn (i9M3P_F9 w) (Icc 0 1) := by
    have hA : ∀ x ∈ Icc (0 : ℝ) 1, 0 < w + (1 - w) * x := fun x hx => i9M2_A_pos hw hx.1
    have hB : ∀ x ∈ Icc (0 : ℝ) 1, 0 < 1 - (1 - w) * x := fun x hx => i9M2_B_pos hw hx.2
    have hL1 : ContinuousOn (fun x => Li₂ ((1 - w) * x)) (Icc 0 1) :=
      continuousOn_Li₂.comp (by fun_prop) fun x hx =>
        ⟨by nlinarith [hx.1], by nlinarith [hx.1, hx.2]⟩
    have hL2 : ContinuousOn (fun x => Li₂ ((w + (1 - w) * x) / (1 + w))) (Icc 0 1) :=
      continuousOn_Li₂.comp (by fun_prop) fun x hx => by
        have := hA x hx
        exact ⟨by have : 0 ≤ (w + (1 - w) * x) / (1 + w) := by positivity
                  linarith, by rw [div_le_one hp]; nlinarith [hx.2]⟩
    have hlA : ContinuousOn (fun x => Real.log (w + (1 - w) * x)) (Icc 0 1) :=
      ContinuousOn.log (by fun_prop) fun x hx => (hA x hx).ne'
    have hlB : ContinuousOn (fun x => Real.log (1 - (1 - w) * x)) (Icc 0 1) :=
      ContinuousOn.log (by fun_prop) fun x hx => (hB x hx).ne'
    unfold i9M3P_F9
    exact ((hL1.neg.div_const w).add ((hL2.sub (hlA.mul continuousOn_const)).div_const w)).sub
      ((hlA.mul hlB).div_const (1 - w))
  have h0 : Tendsto (i9M3P_F9 w) (𝓝[>] 0) (𝓝 (i9M3P_F9 w 0)) :=
    ((hc 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)))
  have h1 : Tendsto (i9M3P_F9 w) (𝓝[<] 1) (𝓝 (i9M3P_F9 w 1)) :=
    ((hc 1 ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)))
  have h := intervalIntegrable_and_integral_eq_of_nonpos hd hf h0 h1
  refine ⟨h.1, ?_⟩
  rw [h.2]
  unfold i9M3P_F9
  simp only [mul_one, mul_zero, sub_zero, add_zero, Li₂_zero, Real.log_one,
    neg_zero, zero_div, sub_sub_cancel]
  rw [show w + (1 - w) = 1 by ring]
  simp only [Real.log_one, zero_mul, sub_zero]
  field_simp
  ring

/-- The antiderivative of `log x / A`. -/
noncomputable def i9M3P_FpA (w x : ℝ) : ℝ :=
  -Li₂ ((1 - w) * x / (w + (1 - w) * x)) + Real.log x * Real.log ((w + (1 - w) * x) / w) -
    Real.log (w + (1 - w) * x) ^ 2 / 2 + Real.log (w + (1 - w) * x) * Real.log w

theorem i9M3P_hasDerivAt_FpA {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i9M3P_FpA w) ((1 - w) * (Real.log x / (w + (1 - w) * x))) x := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hx0 := hx.1
  have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx0.le
  have h1 := i9M2_hasDerivAt_A w x
  have hlA := h1.log hAx.ne'
  have hlx := Real.hasDerivAt_log hx0.ne'
  have hlq := (h1.div_const w).log (div_pos hAx hw0).ne'
  have hz := ((hasDerivAt_id x).const_mul (1 - w)).div h1 hAx.ne'
  have hz1 : (1 - w) * id x / (w + (1 - w) * x) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (mul_pos hu hx0) hAx, by rw [div_lt_one hAx]; simp only [id]; linarith⟩
  have hLi := (hasDerivAt_Li₂' hz1).comp x hz
  have hG := ((hLi.neg.add (hlx.mul hlq)).sub ((hlA.pow 2).div_const 2)).add
    (hlA.mul_const (Real.log w))
  refine hG.congr_deriv ?_
  simp only [id]
  have e1 : 1 - (1 - w) * x / (w + (1 - w) * x) = w / (w + (1 - w) * x) := by
    field_simp; ring
  rw [e1, Real.log_div hw0.ne' hAx.ne', Real.log_div hAx.ne' hw0.ne']
  field_simp
  ring

theorem i9M3P_FpA_zero {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i9M3P_FpA w) (𝓝[>] 0) (𝓝 (Real.log w ^ 2 / 2)) := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hlA0 : Tendsto (fun x => Real.log (w + (1 - w) * x)) (𝓝[>] 0)
      (𝓝 (Real.log (w + (1 - w) * 0))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => w + (1 - w) * x) 0).log (by simp; exact hw0.ne'))
  have hq : ∀ x, (w + (1 - w) * x) / w = 1 + (1 - w) / w * x := fun x => by
    field_simp
  have hxq0 : Tendsto (fun x => Real.log x * Real.log ((w + (1 - w) * x) / w)) (𝓝[>] 0)
      (𝓝 0) := by
    simpa only [hq] using i9M2_tendsto_log_mul_log_one_add (t := (1 - w) / w) (by positivity)
  have hz0 : Tendsto (fun x => (1 - w) * x / (w + (1 - w) * x)) (𝓝[>] 0)
      (𝓝 ((1 - w) * 0 / (w + (1 - w) * 0))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => (1 - w) * x / (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => (1 - w) * x) 0).div (by fun_prop)
        (by simp; exact hw0.ne'))
  have hLi0 : Tendsto (fun x => Li₂ ((1 - w) * x / (w + (1 - w) * x))) (𝓝[>] 0)
      (𝓝 (Li₂ ((1 - w) * 0 / (w + (1 - w) * 0)))) := by
    refine tendsto_Li₂_comp (by simp) hz0 ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    exact ⟨by have : 0 ≤ (1 - w) * x / (w + (1 - w) * x) :=
                div_nonneg (mul_nonneg hu.le hx.1.le) hAx.le
              linarith,
      by rw [div_le_one hAx]; linarith⟩
  have h := ((hLi0.neg.add hxq0).sub ((hlA0.pow 2).div_const 2)).add
    (hlA0.mul_const (Real.log w))
  have e : -Li₂ ((1 - w) * 0 / (w + (1 - w) * 0)) + 0 - Real.log (w + (1 - w) * 0) ^ 2 / 2 +
      Real.log (w + (1 - w) * 0) * Real.log w = Real.log w ^ 2 / 2 := by
    simp only [mul_zero, add_zero, zero_div, Li₂_zero]
    ring
  rw [e] at h
  exact h

theorem i9M3P_FpA_one {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i9M3P_FpA w) (𝓝[<] 1) (𝓝 (-Li₂ (1 - w))) := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hl1 : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    i9M2_tendsto_of_continuousAt (Real.continuousAt_log one_ne_zero)
  have hlA1 : Tendsto (fun x => Real.log (w + (1 - w) * x)) (𝓝[<] 1)
      (𝓝 (Real.log (w + (1 - w) * 1))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => w + (1 - w) * x) 1).log (by simp))
  have hlq1 : Tendsto (fun x => Real.log ((w + (1 - w) * x) / w)) (𝓝[<] 1)
      (𝓝 (Real.log ((w + (1 - w) * 1) / w))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log ((w + (1 - w) * x) / w))
      ((by fun_prop : ContinuousAt (fun x : ℝ => (w + (1 - w) * x) / w) 1).log
        (by simp; exact hw0.ne'))
  have hz1 : Tendsto (fun x => (1 - w) * x / (w + (1 - w) * x)) (𝓝[<] 1)
      (𝓝 ((1 - w) * 1 / (w + (1 - w) * 1))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => (1 - w) * x / (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => (1 - w) * x) 1).div (by fun_prop)
        (by simp))
  have hLi1 : Tendsto (fun x => Li₂ ((1 - w) * x / (w + (1 - w) * x))) (𝓝[<] 1)
      (𝓝 (Li₂ ((1 - w) * 1 / (w + (1 - w) * 1)))) := by
    refine tendsto_Li₂_comp ⟨by simp; linarith, by simp; linarith⟩ hz1 ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    exact ⟨by have : 0 ≤ (1 - w) * x / (w + (1 - w) * x) :=
                div_nonneg (mul_nonneg hu.le hx.1.le) hAx.le
              linarith,
      by rw [div_le_one hAx]; linarith⟩
  have h := ((hLi1.neg.add (hl1.mul hlq1)).sub ((hlA1.pow 2).div_const 2)).add
    (hlA1.mul_const (Real.log w))
  have e : -Li₂ ((1 - w) * 1 / (w + (1 - w) * 1)) +
      Real.log 1 * Real.log ((w + (1 - w) * 1) / w) - Real.log (w + (1 - w) * 1) ^ 2 / 2 +
      Real.log (w + (1 - w) * 1) * Real.log w = -Li₂ (1 - w) := by
    rw [show w + (1 - w) * 1 = 1 by ring]
    simp
  rw [e] at h
  exact h

/-- `∫₀¹ log x / A = -(Li₂ (1 - w) + log² w / 2)/(1 - w)`. -/
theorem i9M3P_logX_divA {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log x / (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x / (w + (1 - w) * x) =
        -(Li₂ (1 - w) + Real.log w ^ 2 / 2) / (1 - w) := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => i9M3P_FpA w x / (1 - w))
      (Real.log x / (w + (1 - w) * x)) x := fun x hx => by
    refine ((i9M3P_hasDerivAt_FpA hw hx).div_const (1 - w)).congr_deriv ?_
    field_simp
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, Real.log x / (w + (1 - w) * x) ≤ 0 := fun x hx =>
    div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hx.1.le hx.2.le)
      (i9M2_A_pos hw hx.1.le).le
  have h := intervalIntegrable_and_integral_eq_of_nonpos hd hf
    ((i9M3P_FpA_zero hw).div_const (1 - w)) ((i9M3P_FpA_one hw).div_const (1 - w))
  refine ⟨h.1, ?_⟩
  rw [h.2]
  field_simp
  ring

/-- The antiderivative of `log x / B`. -/
noncomputable def i9M3P_FpB (w x : ℝ) : ℝ :=
  -Li₂ ((1 - w) * x) - Real.log x * Real.log (1 - (1 - w) * x)

theorem i9M3P_hasDerivAt_FpB {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i9M3P_FpB w) ((1 - w) * (Real.log x / (1 - (1 - w) * x))) x := by
  have hx0 := hx.1
  have hu : (1 - w) ≠ 0 := by linarith [hw.2]
  have hBx : 0 < 1 - (1 - w) * x := i9M2_B_pos hw hx.2.le
  have hlB := (i9M2_hasDerivAt_B w x).log hBx.ne'
  have hlx := Real.hasDerivAt_log hx0.ne'
  have hz1 : (1 - w) * id x ∈ Ioo (0 : ℝ) 1 :=
    ⟨by simp only [id]; nlinarith [hw.2], by simp only [id]; nlinarith [hx.2, hw.1]⟩
  have hLi := (hasDerivAt_Li₂' hz1).comp x ((hasDerivAt_id x).const_mul (1 - w))
  refine (hLi.neg.sub (hlx.mul hlB)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem i9M3P_FpB_zero {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i9M3P_FpB w) (𝓝[>] 0) (𝓝 0) := by
  have hLi0 : Tendsto (fun x => Li₂ ((1 - w) * x)) (𝓝[>] 0) (𝓝 (Li₂ ((1 - w) * 0))) := by
    refine tendsto_Li₂_comp (by simp) (i9M2_tendsto_of_continuousAt (by fun_prop)) ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by nlinarith [hx.1, hw.2], by nlinarith [hx.2, hx.1, hw.1]⟩
  have h := hLi0.neg.sub (i9M2_tendsto_log_mul_log_one_sub (t := 1 - w) (by linarith [hw.2])
    (by linarith [hw.1]))
  unfold i9M3P_FpB
  simpa using h

theorem i9M3P_FpB_one {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i9M3P_FpB w) (𝓝[<] 1) (𝓝 (-Li₂ (1 - w))) := by
  have hLi1 : Tendsto (fun x => Li₂ ((1 - w) * x)) (𝓝[<] 1) (𝓝 (Li₂ ((1 - w) * 1))) := by
    refine tendsto_Li₂_comp ⟨by simp; linarith [hw.2], by simp; linarith [hw.1]⟩
      (i9M2_tendsto_of_continuousAt (by fun_prop)) ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by nlinarith [hx.1, hw.2], by nlinarith [hx.2, hx.1, hw.1]⟩
  have hl1 : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    i9M2_tendsto_of_continuousAt (Real.continuousAt_log one_ne_zero)
  have hlB1 : Tendsto (fun x => Real.log (1 - (1 - w) * x)) (𝓝[<] 1)
      (𝓝 (Real.log (1 - (1 - w) * 1))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (1 - (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => 1 - (1 - w) * x) 1).log
        (by simp; exact hw.1.ne'))
  have h := hLi1.neg.sub (hl1.mul hlB1)
  unfold i9M3P_FpB
  simpa using h

/-- The antiderivative of `log A / B` (times `1 - w`). -/
noncomputable def i9M3P_FaB (w x : ℝ) : ℝ :=
  -Li₂ ((w + (1 - w) * x) / (1 + w)) - Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) +
    Real.log (w + (1 - w) * x) * Real.log (1 + w)

theorem i9M3P_hasDerivAt_FaB {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i9M3P_FaB w)
      ((1 - w) * (Real.log (w + (1 - w) * x) / (1 - (1 - w) * x))) x := by
  have hw0 : 0 < w := hw.1
  have hp : 0 < 1 + w := by linarith
  have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
  have hBx : 0 < 1 - (1 - w) * x := i9M2_B_pos hw hx.2.le
  have h1 := i9M2_hasDerivAt_A w x
  have hlA := h1.log hAx.ne'
  have hlB := (i9M2_hasDerivAt_B w x).log hBx.ne'
  have hAa : (w + (1 - w) * x) / (1 + w) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one hp]; nlinarith [hx.2]⟩
  have hL2 := (hasDerivAt_Li₂' hAa).comp x (h1.div_const (1 + w))
  refine ((hL2.neg.sub (hlA.mul hlB)).add (hlA.mul_const (Real.log (1 + w)))).congr_deriv ?_
  have e2 : 1 - (w + (1 - w) * x) / (1 + w) = (1 - (1 - w) * x) / (1 + w) := by
    field_simp; ring
  rw [e2, Real.log_div hBx.ne' hp.ne']
  field_simp
  ring

theorem i9M3P_continuousOn_FaB {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (i9M3P_FaB w) (Icc 0 1) := by
  have hp : 0 < 1 + w := by linarith [hw.1]
  have hA : ∀ x ∈ Icc (0 : ℝ) 1, 0 < w + (1 - w) * x := fun x hx => i9M2_A_pos hw hx.1
  have hB : ∀ x ∈ Icc (0 : ℝ) 1, 0 < 1 - (1 - w) * x := fun x hx => i9M2_B_pos hw hx.2
  have hL2 : ContinuousOn (fun x => Li₂ ((w + (1 - w) * x) / (1 + w))) (Icc 0 1) :=
    continuousOn_Li₂.comp (by fun_prop) fun x hx => by
      have := hA x hx
      exact ⟨by have : 0 ≤ (w + (1 - w) * x) / (1 + w) := by positivity
                linarith, by rw [div_le_one hp]; linarith [i9M2_A_le hw hx.2, hw.1]⟩
  have hlA : ContinuousOn (fun x => Real.log (w + (1 - w) * x)) (Icc 0 1) :=
    ContinuousOn.log (by fun_prop) fun x hx => (hA x hx).ne'
  have hlB : ContinuousOn (fun x => Real.log (1 - (1 - w) * x)) (Icc 0 1) :=
    ContinuousOn.log (by fun_prop) fun x hx => (hB x hx).ne'
  exact (hL2.neg.sub (hlA.mul hlB)).add (hlA.mul continuousOn_const)

/-- The `x`-integral behind the `w`-derivative of `P₈`. -/
theorem i9M3P_h8 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - w) * Real.log x /
        ((w + (1 - w) * x) * (1 - (1 - w) * x)) +
        Real.log (w + (1 - w) * x) / (1 - (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, ((1 - w) * Real.log x / ((w + (1 - w) * x) * (1 - (1 - w) * x)) +
        Real.log (w + (1 - w) * x) / (1 - (1 - w) * x)) =
        (-2 * Li₂ (1 - w) - Real.log w ^ 2 / 2) / (1 + w) +
          (-Li₂ (1 / (1 + w)) + Li₂ (w / (1 + w)) - Real.log w * Real.log (1 + w)) / (1 - w) := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hp : 0 < 1 + w := by linarith
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun x => (i9M3P_FpA w x + i9M3P_FpB w x) / (1 + w) + i9M3P_FaB w x / (1 - w))
      ((1 - w) * Real.log x / ((w + (1 - w) * x) * (1 - (1 - w) * x)) +
        Real.log (w + (1 - w) * x) / (1 - (1 - w) * x)) x := by
    intro x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    have hBx : 0 < 1 - (1 - w) * x := i9M2_B_pos hw hx.2.le
    refine ((((i9M3P_hasDerivAt_FpA hw hx).add (i9M3P_hasDerivAt_FpB hw hx)).div_const
      (1 + w)).add ((i9M3P_hasDerivAt_FaB hw hx).div_const (1 - w))).congr_deriv ?_
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, (1 - w) * Real.log x /
      ((w + (1 - w) * x) * (1 - (1 - w) * x)) +
        Real.log (w + (1 - w) * x) / (1 - (1 - w) * x) ≤ 0 := by
    intro x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    have hBx : 0 < 1 - (1 - w) * x := i9M2_B_pos hw hx.2.le
    exact add_nonpos (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hu.le
      (Real.log_nonpos hx.1.le hx.2.le)) (mul_pos hAx hBx).le)
      (div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hAx.le (i9M2_A_le hw hx.2.le)) hBx.le)
  have hc := i9M3P_continuousOn_FaB hw
  have h0 : Tendsto (i9M3P_FaB w) (𝓝[>] 0) (𝓝 (i9M3P_FaB w 0)) :=
    ((hc 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)))
  have h1 : Tendsto (i9M3P_FaB w) (𝓝[<] 1) (𝓝 (i9M3P_FaB w 1)) :=
    ((hc 1 ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)))
  have h := intervalIntegrable_and_integral_eq_of_nonpos hd hf
    ((((i9M3P_FpA_zero hw).add (i9M3P_FpB_zero hw)).div_const (1 + w)).add
      (h0.div_const (1 - w)))
    ((((i9M3P_FpA_one hw).add (i9M3P_FpB_one hw)).div_const (1 + w)).add
      (h1.div_const (1 - w)))
  refine ⟨h.1, ?_⟩
  rw [h.2]
  unfold i9M3P_FaB
  simp only [mul_one, mul_zero, sub_zero, add_zero, sub_sub_cancel]
  rw [show w + (1 - w) = 1 by ring]
  simp only [Real.log_one, zero_mul, sub_zero]
  field_simp
  ring

end QED.ThreeLoopD
