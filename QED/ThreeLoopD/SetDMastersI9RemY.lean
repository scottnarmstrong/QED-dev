/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemTaylor
public import QED.Polylog.Deriv

/-!
# Set (d), master `I₉`: the `y`-integral of the first Taylor coefficient of `Rem`

At fixed `x, w ∈ (0, 1)`, with `a = P₀ = c (1 - w)²`, `P₁ = a + w` and `P = a + w y`, the
first Taylor coefficient `F₁ = -3 S₁ / D` of `QED.ThreeLoopD.SetDMastersI9RemTaylor` has the
`y`-integral

  `∫₀¹ S₁ / (y (1 - y)) dy = w (π²/6 - Li₂ (w / P₁)) + a/2 · log² (P₁ / a)`.

The antiderivative is
`H(y) = a Li₂ (w y / P) + a/2 · log² (P / a) + P₁ Li₂ (w (1 - y) / P₁) - w Li₂ (1 - y)`,
whose dilogarithms have arguments in `[0, 1]` on `[0, 1]`. Integrability is a hypothesis: it
holds for almost every `(x, w)` by Fubini, which is all the reduction of `∫ F₁` needs.

## Main results

* `QED.ThreeLoopD.integral_i9RemS1_div`.
* `QED.ThreeLoopD.integral_i9RemF1_eq`: `∫ F₁` as an iterated `(x, w)`-integral (Fubini).
-/

@[expose] public section

open MeasureTheory Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- The `y`-antiderivative of `S₁ / (y (1 - y))`. -/
noncomputable def i9RemH1 (x w y : ℝ) : ℝ :=
  i9Poly x w 0 * Li₂ (w * y / i9Poly x w y) +
    i9Poly x w 0 / 2 * Real.log (i9Poly x w y / i9Poly x w 0) ^ 2 +
    i9Poly x w 1 * Li₂ (w * (1 - y) / i9Poly x w 1) - w * Li₂ (1 - y)

theorem i9Poly_eq_add (x w y : ℝ) : i9Poly x w y = i9Poly x w 0 + w * y := by
  unfold i9Poly; ring

theorem hasDerivAt_i9RemH1 {x w y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => i9RemH1 x w y) (i9RemS 1 x w y / (y * (1 - y))) y := by
  have hc : 0 < x * (1 - x) := i9_c_pos hx
  have hw0 : 0 < w := hw.1
  have hy0 : 0 < y := hy.1
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  have hw1 : 0 < 1 - w := by linarith [hw.2]
  set a := i9Poly x w 0 with ha_def
  have ha : 0 < a := by
    rw [ha_def]; unfold i9Poly; rw [mul_zero, add_zero]; exact mul_pos hc (pow_pos hw1 2)
  have hPe : ∀ t, i9Poly x w t = a + w * t := fun t => i9Poly_eq_add x w t
  have hP : 0 < a + w * y := by positivity
  have hP1 : 0 < a + w := by positivity
  -- the first dilogarithm, argument `v = w y / P`
  have hv : HasDerivAt (fun y => w * y / (a + w * y)) (w * a / (a + w * y) ^ 2) y := by
    have h1 : HasDerivAt (fun y => w * y) w y := by simpa using (hasDerivAt_id y).const_mul w
    have h2 : HasDerivAt (fun y => a + w * y) w y := h1.const_add a
    convert h1.div h2 hP.ne' using 1
    field_simp
    ring
  have hv0 : 0 < w * y / (a + w * y) := by positivity
  have hv1 : w * y / (a + w * y) < 1 := by rw [div_lt_one hP]; linarith
  have hL1 := (hasDerivAt_Li₂ (by rw [abs_of_pos hv0]; exact hv1) hv0.ne').comp y hv
  -- the log square
  have hl : HasDerivAt (fun y => Real.log ((a + w * y) / a)) (w / (a + w * y)) y := by
    have h2 : HasDerivAt (fun y => (a + w * y) / a) (w / a) y := by
      simpa using (((hasDerivAt_id y).const_mul w).const_add a).div_const a
    convert h2.log (by positivity) using 1
    field_simp
  have hl2 := hl.pow 2
  -- the second dilogarithm, argument `w (1 - y) / P₁`
  have hu : HasDerivAt (fun y => w * (1 - y) / (a + w)) (-w / (a + w)) y := by
    simpa using (((hasDerivAt_id y).const_sub 1).const_mul w).div_const (a + w)
  have hu0 : 0 < w * (1 - y) / (a + w) := by positivity
  have hu1 : w * (1 - y) / (a + w) < 1 := by
    rw [div_lt_one hP1]; nlinarith
  have hL2 := (hasDerivAt_Li₂ (by rw [abs_of_pos hu0]; exact hu1) hu0.ne').comp y hu
  -- the third dilogarithm, argument `1 - y`
  have hL3 := (hasDerivAt_Li₂ (by rw [abs_of_pos hy1]; linarith) hy1.ne').comp y
    ((hasDerivAt_id y).const_sub 1)
  have hH : (fun y => i9RemH1 x w y) = fun y =>
      a * Li₂ (w * y / (a + w * y)) + a / 2 * Real.log ((a + w * y) / a) ^ 2 +
        (a + w) * Li₂ (w * (1 - y) / (a + w)) - w * Li₂ (1 - y) := by
    funext t
    unfold i9RemH1
    rw [hPe t, hPe 1, mul_one]
  rw [hH]
  convert (((hL1.const_mul a).add (hl2.const_mul (a / 2))).add (hL2.const_mul (a + w))).sub
    (hL3.const_mul w) using 1
  · funext t
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Function.comp]
  -- the derivative identity
  have e1 : 1 - w * y / (a + w * y) = a / (a + w * y) := by field_simp; ring
  have e2 : 1 - w * (1 - y) / (a + w) = (a + w * y) / (a + w) := by field_simp; ring
  have e3 : (1 : ℝ) - (1 - y) = y := by ring
  rw [e1, e2, e3, Real.log_div ha.ne' hP.ne', Real.log_div hP.ne' hP1.ne',
    Real.log_div hP.ne' ha.ne']
  unfold i9RemS
  rw [hPe y, hPe 1, mul_one, Real.log_mul hw0.ne' hy0.ne']
  field_simp
  ring

theorem continuousOn_i9RemH1 {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun y => i9RemH1 x w y) (Icc 0 1) := by
  have hc : 0 < x * (1 - x) := i9_c_pos hx
  have hw0 : 0 < w := hw.1
  have hw1 : 0 < 1 - w := by linarith [hw.2]
  have ha : 0 < i9Poly x w 0 := by
    unfold i9Poly; rw [mul_zero, add_zero]; exact mul_pos hc (pow_pos hw1 2)
  have hPe : ∀ t, i9Poly x w t = i9Poly x w 0 + w * t := fun t => i9Poly_eq_add x w t
  have hP : ∀ t ∈ Icc (0 : ℝ) 1, 0 < i9Poly x w t := fun t ht => by
    rw [hPe t]; nlinarith [ht.1]
  have hP1 := hP 1 ⟨zero_le_one, le_rfl⟩
  have hcP : ContinuousOn (fun t => i9Poly x w t) (Icc 0 1) := by
    unfold i9Poly; fun_prop
  have hLi : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc 0 1) → (∀ t ∈ Icc (0 : ℝ) 1, g t ∈ Icc (-1) 1) →
      ContinuousOn (fun t => Li₂ (g t)) (Icc 0 1) := fun hg hm =>
    continuousOn_Li₂.comp hg (fun t ht => hm t ht)
  unfold i9RemH1
  refine (((continuousOn_const.mul (hLi ?_ ?_)).add (continuousOn_const.mul ?_)).add
    (continuousOn_const.mul (hLi ?_ ?_))).sub (continuousOn_const.mul (hLi ?_ ?_))
  · exact (continuousOn_const.mul continuousOn_id).div hcP (fun t ht => (hP t ht).ne')
  · intro t ht
    have := hP t ht
    rw [hPe t] at this ⊢
    constructor
    · rw [le_div_iff₀ this]; nlinarith [ht.1]
    · rw [div_le_one this]; linarith
  · exact ((hcP.div_const _).log fun t ht => (div_pos (hP t ht) ha).ne').pow 2
  · exact (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).div_const _
  · intro t ht
    rw [hPe 1]
    constructor
    · rw [le_div_iff₀ (by rw [← hPe 1]; exact hP1)]; nlinarith [ht.2]
    · rw [div_le_one (by rw [← hPe 1]; exact hP1)]; nlinarith [ht.1]
  · exact continuousOn_const.sub continuousOn_id
  · intro t ht; constructor <;> linarith [ht.1, ht.2]

/-- **The `y`-integral of `S₁ / (y (1 - y))`.** -/
theorem integral_i9RemS1_div {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
    (hint : IntegrableOn (fun y => i9RemS 1 x w y / (y * (1 - y))) (Ioo 0 1)) :
    ∫ y in Ioo (0 : ℝ) 1, i9RemS 1 x w y / (y * (1 - y)) =
      w * (π ^ 2 / 6 - Li₂ (w / i9Poly x w 1)) +
        i9Poly x w 0 / 2 * Real.log (i9Poly x w 1 / i9Poly x w 0) ^ 2 := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_i9RemH1 hx hw) (fun y hy => hasDerivAt_i9RemH1 hx hw hy)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hint)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hFTC
  rw [hFTC]
  unfold i9RemH1
  have hPe : ∀ t, i9Poly x w t = i9Poly x w 0 + w * t := fun t => i9Poly_eq_add x w t
  have hw1 : 0 < 1 - w := by linarith [hw.2]
  have ha : 0 < i9Poly x w 0 := by
    unfold i9Poly; rw [mul_zero, add_zero]; exact mul_pos (i9_c_pos hx) (pow_pos hw1 2)
  simp only [mul_zero, zero_div, Li₂_zero, sub_self, sub_zero, mul_one, div_self ha.ne',
    Real.log_one, Li₂_one]
  rw [hPe 1]
  ring

/-- `F₁` is integrable on the cube. -/
theorem integrable_i9RemF1 :
    Integrable i9RemF1 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
  Integrable.mono' (integrable_i9RemBound.const_mul 25) measurable_i9RemF1.aestronglyMeasurable
    (ae_restrict_of_forall_mem (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo))
      fun z hz => by rw [Real.norm_eq_abs]; exact (i9Rem_coeff_bounds hz).1)

/-- **`∫ F₁` as an iterated `(x, w)`-integral**, the `y`-integral done in closed form. -/
theorem integral_i9RemF1_eq :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemF1 z =
      ∫ x in Ioo (0 : ℝ) 1, ∫ w in Ioo (0 : ℝ) 1, -3 / (x * (1 - x) * w) *
        (w * (π ^ 2 / 6 - Li₂ (w / i9Poly x w 1)) +
          i9Poly x w 0 / 2 * Real.log (i9Poly x w 1 / i9Poly x w 0) ^ 2) := by
  have hF := integrable_i9RemF1
  rw [volume_restrict_prod3] at hF ⊢
  rw [integral_prod _ hF]
  refine integral_congr_ae ?_
  filter_upwards [hF.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  rw [integral_prod _ hx]
  refine integral_congr_ae ?_
  filter_upwards [hx.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with w hw hwm
  have hc : x * (1 - x) * w ≠ 0 := (mul_pos (i9_c_pos hxm) hwm.1).ne'
  have e : ∀ y, i9RemF1 (x, w, y) = -3 / (x * (1 - x) * w) * (i9RemS 1 x w y / (y * (1 - y))) :=
    fun y => by
      simp only [i9RemF1, i9RemD]
      rw [div_mul_div_comm, mul_assoc (x * (1 - x)) w]
  simp only [e] at hw ⊢
  rw [integral_const_mul, integral_i9RemS1_div hxm hwm]
  have := hw.const_mul ((x * (1 - x) * w) / -3)
  refine this.congr (ae_of_all _ fun y => ?_)
  simp only
  field_simp
  rw [mul_assoc (x * (1 - x) * w) y, mul_div_mul_left _ _ hc]

end QED.ThreeLoopD
