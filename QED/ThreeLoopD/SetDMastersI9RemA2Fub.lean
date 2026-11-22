/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemY
public import QED.ThreeLoopD.SetDMastersI9RemA2L

/-!
# Set (d), master `I₉`: the `y`-integral of the second Taylor coefficient of `Rem`

At fixed `x, w ∈ (0, 1)`, with `c = x (1 - x)`, `a = P₀ = c (1 - w)²`, `P₁ = a + w` and
`Λ = 2 log c + 2 log w + log y + log (1 - y)`, the second Taylor coefficient
`F₂ = (Λ (-3 S₁) + 9/2 S₂) / (c w y (1 - y))` of `QED.ThreeLoopD.SetDMastersI9RemTaylor` has
the `y`-integral

  `(-6 (log c + log w) Y₁ - 3 Y_L + 9/2 Y₂) / (c w)`,

with `Y₁` from `QED.ThreeLoopD.integral_i9RemS1_div`, `Y_L = QED.ThreeLoopD.i9A2YL a w` and
`Y₂ = QED.ThreeLoopD.i9A2Y2 a w`. No integrability hypothesis is needed at fixed `(x, w)`
beyond that of `F₂` itself: `S₁ / (y (1 - y)) ≥ 0` (concavity of `log`), so the `S₁` and the
log-weighted `S₁` integrands have signs and are integrable by the fundamental theorem of
calculus, and the `S₂` integrand is then a combination of integrable functions.

## Main results

* `QED.ThreeLoopD.integral_i9RemF2_slice`: the `y`-integral at fixed `(x, w)`.
* `QED.ThreeLoopD.integral_i9RemF2_eq`: `∫ F₂` as an iterated `(x, w)`-integral (Fubini).
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-! ### Connectors -/

theorem i9RemS_one_eq (x w y : ℝ) : i9RemS 1 x w y = i9A2S1 (i9Poly x w 0) w y := by
  unfold i9RemS i9A2S1
  rw [i9Poly_eq_add x w y, i9Poly_eq_add x w 1]
  ring

theorem i9RemS_two_eq (x w y : ℝ) : i9RemS 2 x w y = i9A2S2 (i9Poly x w 0) w y := by
  unfold i9RemS i9A2S2
  rw [i9Poly_eq_add x w y, i9Poly_eq_add x w 1]
  ring

theorem i9Poly_zero_pos {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 < i9Poly x w 0 := by
  have hw1 : 0 < 1 - w := by linarith [hw.2]
  unfold i9Poly; rw [mul_zero, add_zero]; exact mul_pos (i9_c_pos hx) (pow_pos hw1 2)

/-! ### Signs -/

/-- **`S₁ / (y (1 - y)) ≥ 0`**: it is `a ℓ / y + (b m - w log y) / (1 - y)` with `ℓ ≥ 0` and
`b m ≥ w log y` by concavity of `log` (`P / b = (a/b) · 1 + (w/b) · y`). -/
theorem i9A2S1_div_nonneg {a w y : ℝ} (ha : 0 < a) (hw : 0 < w) (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 ≤ i9A2S1 a w y / (y * (1 - y)) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hy1' : 0 < 1 - y := by linarith
  have hP : 0 < a + w * y := by positivity
  have hb : 0 < a + w := by positivity
  have e : i9A2S1 a w y / (y * (1 - y)) = a * Real.log ((a + w * y) / a) / y +
      ((a + w) * Real.log ((a + w * y) / (a + w)) - w * Real.log y) / (1 - y) := by
    unfold i9A2S1
    rw [Real.log_mul hw.ne' hy0.ne', Real.log_div hP.ne' ha.ne', Real.log_div hP.ne' hb.ne']
    field_simp
    ring
  rw [e]
  have h1 : 0 ≤ Real.log ((a + w * y) / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; nlinarith)
  have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (mem_Ioi.2 one_pos) (mem_Ioi.2 hy0)
    (show 0 ≤ a / (a + w) by positivity) (show 0 ≤ w / (a + w) by positivity)
    (show a / (a + w) + w / (a + w) = 1 by field_simp)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hc
  have e2 : a / (a + w) + w / (a + w) * y = (a + w * y) / (a + w) := by field_simp
  rw [e2] at hc
  have h2 : 0 ≤ (a + w) * Real.log ((a + w * y) / (a + w)) - w * Real.log y := by
    have := mul_le_mul_of_nonneg_left hc hb.le
    rw [← mul_assoc, mul_div_cancel₀ _ hb.ne'] at this
    linarith
  positivity

/-! ### Integrability and values at fixed `(x, w)` -/

/-- The log-weighted `S₁` integrand: integrable, with integral `i9A2YL`. -/
theorem integrableOn_and_integral_i9A2YL {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    IntegrableOn (fun y => (Real.log y + Real.log (1 - y)) * i9A2S1 a w y / (y * (1 - y)))
        (Ioo 0 1) ∧
      ∫ y in Ioo (0 : ℝ) 1, (Real.log y + Real.log (1 - y)) * i9A2S1 a w y / (y * (1 - y)) =
        i9A2YL a w := by
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_eq_of_nonpos
    (fun y hy => hasDerivAt_i9A2HL ha hw hy) (fun y hy => by
      have h := i9A2S1_div_nonneg ha hw hy
      have hl : Real.log y + Real.log (1 - y) ≤ 0 := by
        have := Real.log_nonpos hy.1.le hy.2.le
        have := Real.log_nonpos (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y) (by linarith [hy.1])
        linarith
      rw [mul_div_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg hl h)
    (tendsto_i9A2HL_zero ha hw) (tendsto_i9A2HL_one ha hw)
  have hI := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hi
  refine ⟨hI, ?_⟩
  rw [← integral_i9A2YL_div ha hw hI]

/-- The `S₁` integrand is integrable at fixed `(x, w)`. -/
theorem integrableOn_i9RemS1_div {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun y => i9RemS 1 x w y / (y * (1 - y))) (Ioo 0 1) := by
  have hc := continuousOn_i9RemH1 hx hw
  have ha := i9Poly_zero_pos hx hw
  have h0 := ((hc 0 ⟨le_rfl, zero_le_one⟩).tendsto).mono_left
    (nhdsWithin_le_of_mem (Icc_mem_nhdsGT zero_lt_one))
  have h1 := ((hc 1 ⟨zero_le_one, le_rfl⟩).tendsto).mono_left
    (nhdsWithin_le_of_mem (Icc_mem_nhdsLT zero_lt_one))
  obtain ⟨hi, -⟩ := intervalIntegrable_and_integral_eq_of_nonneg
    (fun y hy => hasDerivAt_i9RemH1 hx hw hy)
    (fun y hy => by rw [i9RemS_one_eq]; exact i9A2S1_div_nonneg ha hw.1 hy) h0 h1
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hi

/-- The `(x, w)`-density of `∫ F₂`: `(-6 (log c + log w) Y₁ - 3 Y_L + 9/2 Y₂) / (c w)`. -/
noncomputable def i9A2Dens (x w : ℝ) : ℝ :=
  (-6 * (Real.log (x * (1 - x)) + Real.log w) *
      (w * (π ^ 2 / 6 - Li₂ (w / i9Poly x w 1)) +
        i9Poly x w 0 / 2 * Real.log (i9Poly x w 1 / i9Poly x w 0) ^ 2) -
    3 * i9A2YL (i9Poly x w 0) w + 9 / 2 * i9A2Y2 (i9Poly x w 0) w) / (x * (1 - x) * w)

/-- **The `y`-integral of `F₂`** at fixed `(x, w)`. -/
theorem integral_i9RemF2_slice {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
    (hint : IntegrableOn (fun y => i9RemF2 (x, w, y)) (Ioo 0 1)) :
    ∫ y in Ioo (0 : ℝ) 1, i9RemF2 (x, w, y) = i9A2Dens x w := by
  have ha := i9Poly_zero_pos hx hw
  have hc : 0 < x * (1 - x) * w := mul_pos (i9_c_pos hx) hw.1
  set a := i9Poly x w 0 with ha_def
  set α := -6 * (Real.log (x * (1 - x)) + Real.log w) / (x * (1 - x) * w) with hα
  set β := -3 / (x * (1 - x) * w) with hβ
  set γ := 9 / 2 / (x * (1 - x) * w) with hγ
  have hI1 : IntegrableOn (fun y => i9A2S1 a w y / (y * (1 - y))) (Ioo 0 1) := by
    refine (integrableOn_i9RemS1_div hx hw).congr_fun (fun y _ => ?_) measurableSet_Ioo
    simp only [i9RemS_one_eq, ha_def]
  obtain ⟨hI2, hv2⟩ := integrableOn_and_integral_i9A2YL ha hw.1
  have hpt : ∀ y ∈ Ioo (0 : ℝ) 1, i9RemF2 (x, w, y) =
      α * (i9A2S1 a w y / (y * (1 - y))) +
        β * ((Real.log y + Real.log (1 - y)) * i9A2S1 a w y / (y * (1 - y))) +
        γ * (i9A2S2 a w y / (y * (1 - y))) := by
    intro y hy
    have hy0 : y ≠ 0 := hy.1.ne'
    have hy1 : 1 - y ≠ 0 := by linarith [hy.2]
    simp only [i9RemF2, i9RemD, i9RemLam, i9RemS_one_eq, i9RemS_two_eq, ← ha_def, hα, hβ, hγ]
    field_simp
    ring
  have hI3 : IntegrableOn (fun y => i9A2S2 a w y / (y * (1 - y))) (Ioo 0 1) := by
    have h := ((hint.sub (hI1.const_mul α)).sub (hI2.const_mul β)).const_mul γ⁻¹
    refine IntegrableOn.congr_fun h (fun y hy => ?_) measurableSet_Ioo
    simp only [Pi.sub_apply]
    rw [hpt y hy]
    have hγ0 : γ ≠ 0 := by rw [hγ]; positivity
    field_simp
    ring
  have h12 : IntegrableOn (fun y => α * (i9A2S1 a w y / (y * (1 - y))) +
      β * ((Real.log y + Real.log (1 - y)) * i9A2S1 a w y / (y * (1 - y)))) (Ioo 0 1) :=
    (hI1.const_mul α).add (hI2.const_mul β)
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_add h12 (hI3.const_mul γ),
    integral_add (hI1.const_mul α) (hI2.const_mul β), integral_const_mul, integral_const_mul,
    integral_const_mul, hv2, integral_i9A2S2_div ha hw.1 hI3]
  have hY1 := integral_i9RemS1_div hx hw (integrableOn_i9RemS1_div hx hw)
  simp only [i9RemS_one_eq, ← ha_def] at hY1
  rw [hY1, i9A2Dens, ← ha_def, hα, hβ, hγ]
  field_simp
  ring

/-! ### Fubini -/

/-- `F₂` is integrable on the cube. -/
theorem integrable_i9RemF2 :
    Integrable i9RemF2 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))) :=
  Integrable.mono' (integrable_i9RemBound.const_mul 1250) measurable_i9RemF2.aestronglyMeasurable
    (ae_restrict_of_forall_mem (measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo))
      fun z hz => by rw [Real.norm_eq_abs]; exact (i9Rem_coeff_bounds hz).2.1)

/-- **`∫ F₂` as an iterated `(x, w)`-integral**, the `y`-integral done in closed form. -/
theorem integral_i9RemF2_eq :
    ∫ z in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), i9RemF2 z =
      ∫ x in Ioo (0 : ℝ) 1, ∫ w in Ioo (0 : ℝ) 1, i9A2Dens x w := by
  have hF := integrable_i9RemF2
  rw [volume_restrict_prod3] at hF ⊢
  rw [integral_prod _ hF]
  refine integral_congr_ae ?_
  filter_upwards [hF.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  rw [integral_prod _ hx]
  refine integral_congr_ae ?_
  filter_upwards [hx.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with w hw hwm
  exact integral_i9RemF2_slice hxm hwm hw

/-- `i9A2Dens` is integrable on the `(x, w)`-square: it is a.e. the `y`-integral of the
integrable `F₂`. -/
theorem integrableOn_i9A2Dens :
    IntegrableOn (fun z : ℝ × ℝ => i9A2Dens z.1 z.2) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hF := integrable_i9RemF2
  rw [volume_restrict_prod3] at hF
  set μ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  have hP := measurePreserving_prodAssoc μ μ μ
  have hG : Integrable (i9RemF2 ∘ MeasurableEquiv.prodAssoc) ((μ.prod μ).prod μ) :=
    (hP.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).2 hF
  have hmem : ∀ᵐ z ∂(μ.prod μ), z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    rw [hμ, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine hG.integral_prod_left.congr ?_
  filter_upwards [hG.prod_right_ae, hmem] with z hz hzm
  exact integral_i9RemF2_slice hzm.1 hzm.2 hz

end QED.ThreeLoopD
