/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCKSec
public import QED.ChainProof.SetCKFormOCSwap
public import QED.ChainProof.SetCKScOutCH

/-!
# Set (c), Stage K, closed forms: the `K`-part of the outer-massive corner, Fubini

Helper level (no frozen statement). Step 2 of the `ρ_oC` route (Stage K notes, Session 29+).
On `(((a, x), Y), X') ∈ (0, 1)⁴` the kernel (**`formOCKF`**)

`F = Y · 1{x < X' < X} Q'(X') k(Y, a Y, x, Q(X') - Q(x))`

has the `X'`-sections `Y K(Y, a Y, x, Q(X) - Q(x))` (`formOC_KF_section`, by the node
substitution of `SetCKFormOCKSec`) and is integrable (**`formOC_integrable_KF`**): the
`L¹`-norms of the sections are at most `Y (Q(X) + 1) D(Y, a Y, x)` with the dominating function
`D = scOutCDom 1` of the corner (`formOC_abs_k_le_dom`), integrable after `y₃ = a Y`
(`formOC_integral_cov`). Fubini then moves the node variable outside
(**`formOC_K_part`**): with `g_k = formOCgk` the closed-form `Y`-integral of `Y k`
(`formOC_integral_k`),

`∫_{(a, x)} 1{x < X} ∫_Y Y K = ∫_{X'} 1{X' < X} Q'(X') ∫_{(a, x)} 1{x < X'} g_k(x, a, v(x, X'))`,

`v(x, X') = Q(X') - Q(x)`,

with the integrability of both inner functions.
-/

@[expose] public section

open Real Set Filter MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The closed-form `Y`-integral of `Y k`** at `y₃ = a Y` (`formOC_integral_k`). -/
noncomputable def formOCgk (x a v : ℝ) : ℝ :=
  formOCLaurI (formOCkn3 x a v (formOCD a x v)) (formOCkn2 x a v (formOCD a x v))
      (formOCkn1 x a v (formOCD a x v)) (formOCkp0 x a v (formOCD a x v))
      (formOCkp1 x a v (formOCD a x v)) (formOCYc a x v) -
    x ^ 2 * formOCYc a x v ^ 2 / (4 * v)

/-- **The `K`-part kernel** on `(((a, x), Y), X')`. -/
noncomputable def formOCKF (X : ℝ) (r : ((ℝ × ℝ) × ℝ) × ℝ) : ℝ :=
  r.1.2 * (if r.1.1.2 < r.2 ∧ r.2 < X then
    setCKdQ r.2 * formOCkY r.1.2 r.1.1.1 r.1.1.2 (scOutVX r.1.1.2 r.2) else 0)

theorem measurable_formOCKF (X : ℝ) : Measurable (formOCKF X) := by
  have hk : Measurable fun r : ((ℝ × ℝ) × ℝ) × ℝ =>
      formOCkY r.1.2 r.1.1.1 r.1.1.2 (scOutVX r.1.1.2 r.2) := by
    unfold formOCkY scOutCk scOutCs betaG cornerC0 cornerC1 cornerC2 cornerC3
      QED.TwoLoop.UnitSCReduce.cornerP2 cornerG cornerR scOutCm scOutRho scOutVX setCKQ
    exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)
      (by fun_prop)
  have hdQ : Measurable setCKdQ := by unfold setCKdQ; fun_prop
  have hs : MeasurableSet {r : ((ℝ × ℝ) × ℝ) × ℝ | r.1.1.2 < r.2 ∧ r.2 < X} :=
    (measurableSet_lt measurable_fst.fst.snd measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)
  have h2 : Measurable fun r : ((ℝ × ℝ) × ℝ) × ℝ => setCKdQ r.2 *
      formOCkY r.1.2 r.1.1.1 r.1.1.2 (scOutVX r.1.1.2 r.2) := (hdQ.comp measurable_snd).mul hk
  have h3 : Measurable fun r : ((ℝ × ℝ) × ℝ) × ℝ => if r.1.1.2 < r.2 ∧ r.2 < X then
      setCKdQ r.2 * formOCkY r.1.2 r.1.1.1 r.1.1.2 (scOutVX r.1.1.2 r.2) else 0 :=
    Measurable.ite hs h2 measurable_const
  exact measurable_fst.snd.mul h3

/-- The `Y`-integral of the `K`-part at the node `X`, as a function of `(a, x)`. -/
noncomputable def formOCGK (X : ℝ) (q : ℝ × ℝ) : ℝ :=
  if q.2 < X then ∫ Y in Ioo (0 : ℝ) 1, Y * scOutCK (cornerC0 q.2)
    (cornerC1 q.2 (q.1 * Y) (Y - q.1 * Y)) (cornerC2 q.2 (q.1 * Y) (Y - q.1 * Y))
    (cornerC3 q.2 (q.1 * Y) (Y - q.1 * Y)) (scOutCm Y (q.1 * Y) q.2)
    (q.1 * Y * (Y - q.1 * Y)) (scOutRho q.2) (scOutCs Y (q.1 * Y) q.2) (scOutVX q.2 X) else 0

/-- The closed-form `Y`-integral of `Y k` at the node `X'`, as a function of `(a, x)`. -/
noncomputable def formOCIK (X' : ℝ) (q : ℝ × ℝ) : ℝ :=
  if q.2 < X' then formOCgk q.2 q.1 (scOutVX q.2 X') else 0

theorem formOC_ae_mem2 : ∀ᵐ q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
    (volume.restrict (Ioo (0 : ℝ) 1))), q.1 ∈ Ioo (0 : ℝ) 1 ∧ q.2 ∈ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
  exact hq

theorem formOC_ae_mem3 : ∀ᵐ p ∂(((volume.restrict (Ioo (0 : ℝ) 1)).prod
    (volume.restrict (Ioo (0 : ℝ) 1))).prod (volume.restrict (Ioo (0 : ℝ) 1))),
    p.1.1 ∈ Ioo (0 : ℝ) 1 ∧ p.1.2 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem ((measurableSet_Ioo.prod measurableSet_Ioo).prod
    measurableSet_Ioo)] with p hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

section

variable {X X' Y a x : ℝ}

/-- The mass condition of the corner bound at `t = 1`, `y₃ = a Y`. -/
theorem formOC_mass_pos (hY : 0 < Y) (ha : a ∈ Ioo (0 : ℝ) 1) :
    0 < Y ^ 2 - 1 * (a * Y * (Y - a * Y)) := by
  have : Y ^ 2 - 1 * (a * Y * (Y - a * Y)) = Y ^ 2 * (1 - a + a ^ 2) := by ring
  rw [this]
  have : 0 < 1 - a + a ^ 2 := by nlinarith [ha.1, ha.2]
  positivity

/-- **The `X'`-section of the `K`-part kernel.** -/
theorem formOC_KF_section (hX : X ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun X' => formOCKF X (((a, x), Y), X')) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X' in Ioo (0 : ℝ) 1, formOCKF X (((a, x), Y), X') =
        (if x < X then Y * scOutCK (cornerC0 x) (cornerC1 x (a * Y) (Y - a * Y))
          (cornerC2 x (a * Y) (Y - a * Y)) (cornerC3 x (a * Y) (Y - a * Y))
          (scOutCm Y (a * Y) x) (a * Y * (Y - a * Y)) (scOutRho x) (scOutCs Y (a * Y) x)
          (scOutVX x X) else 0) ∧
      ∫ X' in Ioo (0 : ℝ) 1, ‖formOCKF X (((a, x), Y), X')‖ ≤
        Y * ((setCKQ X + 1) * scOutCDom 1 Y (a * Y) x) := by
  have hY0 := hY.1
  have hdom0 : 0 ≤ scOutCDom 1 Y (a * Y) x := by
    have h1 : 0 < √(1 - Y) := sqrt_pos.2 (by linarith [hY.2])
    have h2 := rpow_pos_of_pos hY.1 ((1 : ℝ) / 12)
    have h3 := rpow_pos_of_pos (mul_pos ha.1 hY.1) ((1 : ℝ) / 12)
    have h4 := rpow_pos_of_pos hx.1 ((1 : ℝ) / 12)
    unfold scOutCDom
    positivity
  by_cases hxX : x < X
  · have hx' : x ∈ Ioo (0 : ℝ) X := ⟨hx.1, hxX⟩
    have h3 : a * Y ∈ Ioo (0 : ℝ) Y := ⟨mul_pos ha.1 hY.1, by nlinarith [ha.2]⟩
    have hm := scOutCm_pos hY h3 hx
    have he : 0 < a * Y * (Y - a * Y) := mul_pos h3.1 (by linarith [h3.2])
    have hw := scOutRho_pos hx
    have hQ0 := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    have hu : 0 < setCKQ x + 1 := by linarith
    have hs : 0 ≤ scOutCs Y (a * Y) x := scOutCs_nonneg hx
    have hM : scOutCm Y (a * Y) x - a * Y * (Y - a * Y) * (setCKQ x + 1) ≠ 0 := by
      have := formOC_mass_pos hY.1 ha
      unfold scOutCm
      intro h
      nlinarith
    have hki := (scOutC_k_int hm he hw hu hs hM (cornerC0 x) (cornerC1 x (a * Y) (Y - a * Y))
      (cornerC2 x (a * Y) (Y - a * Y)) (cornerC3 x (a * Y) (Y - a * Y))).1
    have hkm : Measurable (formOCkY Y a x) := measurable_scOutCk _ _ _ _ _ _ _ _
    obtain ⟨hIoc, hbd⟩ := formOC_k_Ioc hX.2 hx' hkm hki
    obtain ⟨hi1, hv1⟩ := formOC_k_section hX.2 hx' hIoc
    obtain ⟨hi2, hv2⟩ := formOC_k_section hX.2 hx' hIoc.abs
    have hdom := formOC_abs_k_le_dom one_pos hY h3 hx (formOC_mass_pos hY.1 ha).ne'
    have habs : ∀ X', ‖formOCKF X (((a, x), Y), X')‖ = Y * (if x < X' ∧ X' < X then
        setCKdQ X' * |formOCkY Y a x (scOutVX x X')| else 0) := by
      intro X'
      simp only [formOCKF, Real.norm_eq_abs, abs_mul, abs_of_pos hY0]
      congr 1
      split_ifs with h
      · rw [abs_mul, abs_of_pos (setCKdQ_pos ⟨hx.1.trans h.1, h.2.trans hX.2⟩)]
      · exact abs_zero
    refine ⟨hi1.const_mul Y, ?_, ?_⟩
    · simp only [hxX, ↓reduceIte, formOCKF]
      rw [integral_const_mul, hv1]
      rfl
    · simp only [habs]
      rw [integral_const_mul, hv2]
      refine mul_le_mul_of_nonneg_left (hbd.trans ?_) hY0.le
      exact mul_le_mul_of_nonneg_left hdom (by linarith [setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩])
  · have h0 : ∀ X', formOCKF X (((a, x), Y), X') = 0 := fun X' => by
      simp only [formOCKF]
      rw [ite_eq_right_iff.2 fun h => absurd (h.1.trans h.2) hxX, mul_zero]
    have hQX := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
    simp only [h0, hxX, ↓reduceIte, norm_zero, integral_zero]
    exact ⟨integrable_zero _ _ _, trivial, by positivity⟩

/-- **The `K`-part kernel is integrable** on `(0, 1)⁴`. -/
theorem formOC_integrable_KF (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (formOCKF X) ((((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))).prod (volume.restrict (Ioo (0 : ℝ) 1))).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set f : ℝ × ℝ × ℝ → ℝ := fun q =>
    if q.2.1 < q.1 then (setCKQ X + 1) * scOutCDom 1 q.1 q.2.1 q.2.2 else 0 with hf
  have hs : MeasurableSet {q : ℝ × ℝ × ℝ | q.2.1 < q.1} :=
    measurableSet_lt measurable_snd.fst measurable_fst
  have hdm : Measurable fun q : ℝ × ℝ × ℝ => scOutCDom 1 q.1 q.2.1 q.2.2 := by
    unfold scOutCDom
    fun_prop
  have hfm : Measurable f := Measurable.ite hs (hdm.const_mul _) measurable_const
  have hfI : Integrable f ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
    refine (((integrable_scOutCDom 1).const_mul (setCKQ X + 1)).indicator hs).congr
      (Eventually.of_forall fun q => ?_)
    by_cases h : q.2.1 < q.1
    · simp only [hf, h, ↓reduceIte, indicator_of_mem (show q ∈ {q : ℝ × ℝ × ℝ | q.2.1 < q.1}
        from h)]
    · simp only [hf, h, ↓reduceIte, indicator_of_notMem (show q ∉ {q : ℝ × ℝ × ℝ | q.2.1 < q.1}
        from h)]
  have hz : ∀ q : ℝ × ℝ × ℝ, q.1 ≤ q.2.1 → f q = 0 := fun q hq => by
    simp only [hf, not_lt.2 hq, ↓reduceIte]
  have hI2 := (formOC_integral_cov hfm hz hfI).1.swap
  refine (integrable_prod_iff (measurable_formOCKF X).aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [formOC_ae_mem3] with p hp
    exact (formOC_KF_section hX hp.1 hp.2.1 hp.2.2).1
  · refine Integrable.mono' hI2
      ((measurable_formOCKF X).aestronglyMeasurable.norm.integral_prod_right') ?_
    filter_upwards [formOC_ae_mem3] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hb := (formOC_KF_section hX hp.1 hp.2.1 hp.2.2).2.2
    have hlt : p.1.1 * p.2 < p.2 := by nlinarith [hp.1.2, hp.2.2.1]
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, hf, hlt, ↓reduceIte]
    exact hb

/-- The inner `Y`-integral of the `K`-part kernel at a node `X'`. -/
theorem formOC_KF_Y (hX' : X' ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ Y in Ioo (0 : ℝ) 1, formOCKF X (((a, x), Y), X') =
      if X' < X then setCKdQ X' * formOCIK X' (a, x) else 0 := by
  by_cases h : x < X' ∧ X' < X
  · have hv : 0 < scOutVX x X' := sub_pos.2 (setCKQ_lt hx.1.le h.1 hX'.2)
    have e : ∀ Y, formOCKF X (((a, x), Y), X') = setCKdQ X' * (Y * scOutCk (cornerC0 x)
        (cornerC1 x (a * Y) (Y - a * Y)) (cornerC2 x (a * Y) (Y - a * Y))
        (cornerC3 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x) (a * Y * (Y - a * Y))
        (scOutRho x) (scOutCs Y (a * Y) x) (scOutVX x X')) := fun Y => by
      simp only [formOCKF, h, and_self, ↓reduceIte, formOCkY]
      ring
    simp only [e, h.2, ↓reduceIte, formOCIK, h.1]
    rw [integral_const_mul, (formOC_integral_k ha hx hv).2]
    rfl
  · have e : ∀ Y, formOCKF X (((a, x), Y), X') = 0 := fun Y => by
      simp only [formOCKF, h, ↓reduceIte, mul_zero]
    simp only [e, integral_zero]
    split_ifs with h2
    · have : ¬ x < X' := fun h1 => h ⟨h1, h2⟩
      simp only [formOCIK, this, ↓reduceIte, mul_zero]
    · rfl

/-- **The `K`-part at the node**: Fubini moves the node variable `X'` outside. -/
theorem formOC_K_part (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (formOCGK X) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) ∧
      (∀ᵐ X' ∂(volume.restrict (Ioo (0 : ℝ) 1)), X' < X →
        Integrable (formOCIK X') ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)))) ∧
      ∫ q, formOCGK X q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1))) =
        ∫ X' in Ioo (0 : ℝ) 1, if X' < X then setCKdQ X' * ∫ q, formOCIK X' q
          ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))
          else 0 := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  have hF := formOC_integrable_KF hX
  set G3 : (ℝ × ℝ) × ℝ → ℝ := fun p => ∫ X', formOCKF X (p, X') ∂μ with hG3d
  have hG3 : Integrable G3 ((μ.prod μ).prod μ) := hF.integral_prod_left
  have hG2 : Integrable (fun q => ∫ Y, G3 (q, Y) ∂μ) (μ.prod μ) := hG3.integral_prod_left
  have hae : (fun q => ∫ Y, G3 (q, Y) ∂μ) =ᵐ[μ.prod μ] formOCGK X := by
    filter_upwards [formOC_ae_mem2] with q hq
    have e : ∀ Y ∈ Ioo (0 : ℝ) 1, G3 (q, Y) = if q.2 < X then Y * scOutCK (cornerC0 q.2)
        (cornerC1 q.2 (q.1 * Y) (Y - q.1 * Y)) (cornerC2 q.2 (q.1 * Y) (Y - q.1 * Y))
        (cornerC3 q.2 (q.1 * Y) (Y - q.1 * Y)) (scOutCm Y (q.1 * Y) q.2)
        (q.1 * Y * (Y - q.1 * Y)) (scOutRho q.2) (scOutCs Y (q.1 * Y) q.2)
        (scOutVX q.2 X) else 0 := fun Y hY =>
      (formOC_KF_section hX hq.1 hq.2 hY).2.1
    simp only [hμ]
    rw [setIntegral_congr_fun measurableSet_Ioo e]
    unfold formOCGK
    split_ifs
    · rfl
    · exact integral_zero _ _
  have hsec : ∀ᵐ X' ∂μ, X' ∈ Ioo (0 : ℝ) 1 ∧ Integrable (fun p => formOCKF X (p, X'))
      ((μ.prod μ).prod μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hF.prod_left_ae] with X' h1 h2
    exact ⟨h1, h2⟩
  have hsec2 : ∀ X' ∈ Ioo (0 : ℝ) 1, (fun q => ∫ Y, formOCKF X ((q, Y), X') ∂μ) =ᵐ[μ.prod μ]
      fun q => if X' < X then setCKdQ X' * formOCIK X' q else 0 := by
    intro X' hX'
    filter_upwards [formOC_ae_mem2] with q hq
    exact formOC_KF_Y hX' hq.1 hq.2
  refine ⟨hG2.congr hae, ?_, ?_⟩
  · filter_upwards [hsec] with X' hX' hlt
    have hi := (hX'.2.integral_prod_left).congr (hsec2 X' hX'.1)
    simp only [hlt, ↓reduceIte] at hi
    have hd := setCKdQ_pos hX'.1
    refine (hi.const_mul (setCKdQ X')⁻¹).congr (Eventually.of_forall fun q => ?_)
    simp only
    field_simp
  · rw [← integral_congr_ae hae, ← integral_prod _ hG3, ← integral_prod _ hF,
      integral_prod_symm _ hF]
    refine integral_congr_ae ?_
    filter_upwards [hsec] with X' hX'
    rw [integral_prod _ hX'.2, integral_congr_ae (hsec2 X' hX'.1)]
    split_ifs
    · exact integral_const_mul _ _
    · exact integral_zero _ _

end

end QED.ChainProof.SetCK

end
