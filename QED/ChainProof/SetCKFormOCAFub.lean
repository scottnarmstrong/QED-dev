/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCAhBd
public import QED.ChainProof.SetCKFormOCKFub

/-!
# Set (c), Stage K, closed forms: the `Â`-increment moved to the node variable

Helper level (no frozen statement). Step 3 of the `ρ_oC` route (Stage K notes, Session 29+).
With `μ = volume|(0, 1)`, `v(x, X) = Q(X) - Q(x)` and `S_A = ∂_v Â` (`formOCSA`), the kernel
`1{x < X' < X} Q'(X') S_A(a, x, v(x, X'))` (**`formOCAF`**) is integrable on `(0, 1)³`
(**`formOC_integrable_AF`**, by `formOC_SA_bound` and the node substitution
`formOC_k_section`), and Fubini gives (**`formOC_A_part`**), for `X ∈ (0, 1)`:

`∫_{(a, x)} 1{x < X} (Â(v(x, X)) - Â(0)) = ∫_{X'} 1{X' < X} Q'(X') ∫_{(a, x)} 1{x < X'} S_A`,

in the scaled form `formOCAhR` of `Â`, with integrability of both sides.
-/

@[expose] public section

open Real Set Filter MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

theorem measurable_formOCSA {α : Type*} [MeasurableSpace α] {f g h : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable fun r => formOCSA (f r) (g r) (h r) := by
  unfold formOCSA formOCdR0 formOCdP0x formOCP0x formOCdP1x formOCP1x formOCdN1x formOCN1x
    formOCm1 formOCdm1 formOCRat formOCRatD formXPol formXPolD formOCYc formOCdc formOClam
    formOCE formOCD formOCD0 setCKQ formOCR0N formOCP0xN formOCP1xN formOCN1xN formOCm1N
  fun_prop

/-- The `A`-part kernel in `((a, x), X')`. -/
noncomputable def formOCAF (X : ℝ) (r : (ℝ × ℝ) × ℝ) : ℝ :=
  if r.1.2 < r.2 ∧ r.2 < X then setCKdQ r.2 * formOCSA r.1.1 r.1.2 (scOutVX r.1.2 r.2) else 0

theorem measurable_formOCAF (X : ℝ) : Measurable (formOCAF X) := by
  have hdQ : Measurable setCKdQ := by unfold setCKdQ; fun_prop
  have hv : Measurable fun r : (ℝ × ℝ) × ℝ => scOutVX r.1.2 r.2 := by
    unfold scOutVX setCKQ; fun_prop
  have hs : MeasurableSet {r : (ℝ × ℝ) × ℝ | r.1.2 < r.2 ∧ r.2 < X} :=
    (measurableSet_lt measurable_fst.snd measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)
  have h2 : Measurable fun r : (ℝ × ℝ) × ℝ =>
      setCKdQ r.2 * formOCSA r.1.1 r.1.2 (scOutVX r.1.2 r.2) :=
    (hdQ.comp measurable_snd).mul (measurable_formOCSA measurable_fst.fst measurable_fst.snd hv)
  have h3 : Measurable fun r : (ℝ × ℝ) × ℝ => if r.1.2 < r.2 ∧ r.2 < X then
      setCKdQ r.2 * formOCSA r.1.1 r.1.2 (scOutVX r.1.2 r.2) else 0 :=
    Measurable.ite hs h2 measurable_const
  unfold formOCAF
  exact h3

/-- The `Â`-increment at the node `X`, as a function of `(a, x)`. -/
noncomputable def formOCGA (X : ℝ) (q : ℝ × ℝ) : ℝ :=
  if q.2 < X then formOCAhR q.1 q.2 (scOutVX q.2 X) - formOCAhR q.1 q.2 0 else 0

/-- `S_A` at the node `X'`, as a function of `(a, x)`. -/
noncomputable def formOCIA (X' : ℝ) (q : ℝ × ℝ) : ℝ :=
  if q.2 < X' then formOCSA q.1 q.2 (scOutVX q.2 X') else 0

/-- The majorant `C (Q(X)(1 + |log a| + |log x|) + ∫₀^{Q(X)} |log|)` of the sections. -/
noncomputable def formOCAMaj (X C : ℝ) (q : ℝ × ℝ) : ℝ :=
  C * (setCKQ X * (1 + |log q.1| + |log q.2|) + ∫ v in Ioc 0 (setCKQ X), |log v|)

section

variable {X X' a x C : ℝ}

theorem formOC_integrableOn_abs_log (V : ℝ) : IntegrableOn (fun v => |log v|) (Ioc 0 V) := by
  rcases le_or_gt V 0 with h | h
  · rw [Ioc_eq_empty (not_lt.2 h)]
    exact integrableOn_empty
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le h.le).1
      intervalIntegral.intervalIntegrable_log').abs

/-- **The `X'`-section of the `A`-part kernel.** -/
theorem formOC_AF_section (hX : X ∈ Ioo (0 : ℝ) 1) (hC : ∀ a ∈ Ioo (0 : ℝ) 1,
      ∀ x ∈ Ioc (0 : ℝ) X, ∀ v ∈ Ioc (0 : ℝ) (setCKQ X),
        |formOCSA a x v| ≤ C * (1 + |log a| + |log x| + |log v|)) (hC0 : 0 ≤ C)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun X' => formOCAF X ((a, x), X')) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X' in Ioo (0 : ℝ) 1, formOCAF X ((a, x), X') = formOCGA X (a, x) ∧
      ∫ X' in Ioo (0 : ℝ) 1, ‖formOCAF X ((a, x), X')‖ ≤ formOCAMaj X C (a, x) := by
  have hQ0 := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hmaj : 0 ≤ formOCAMaj X C (a, x) := by
    unfold formOCAMaj
    have := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
    have := setIntegral_nonneg (μ := volume) (s := Ioc 0 (setCKQ X)) measurableSet_Ioc
      fun v _ => abs_nonneg (log v)
    positivity
  by_cases h : x < X
  · have hV : 0 < scOutVX x X := sub_pos.2 (setCKQ_lt hx.1.le h hX.2)
    have hVQ : scOutVX x X ≤ setCKQ X := by unfold scOutVX; linarith
    have hk := formOC_integrableOn_SA ha hx hV
    obtain ⟨hi, hv⟩ := formOC_k_section hX.2 ⟨hx.1, h⟩ hk
    obtain ⟨hia, hva⟩ := formOC_k_section hX.2 ⟨hx.1, h⟩ hk.abs
    have e : ∀ X', formOCAF X ((a, x), X') =
        if x < X' ∧ X' < X then setCKdQ X' * formOCSA a x (scOutVX x X') else 0 := fun _ => rfl
    have en : ∀ X' ∈ Ioo (0 : ℝ) 1, ‖formOCAF X ((a, x), X')‖ =
        if x < X' ∧ X' < X then setCKdQ X' * |formOCSA a x (scOutVX x X')| else 0 := by
      intro X' hX'
      rw [e, Real.norm_eq_abs]
      split_ifs
      · rw [abs_mul, abs_of_pos (setCKdQ_pos hX')]
      · exact abs_zero
    refine ⟨?_, ?_, ?_⟩
    · simp only [e]
      exact hi
    · simp only [e]
      rw [hv, formOC_AhR_ftc ha hx hV]
      simp only [formOCGA, h, ↓reduceIte]
    · rw [setIntegral_congr_fun measurableSet_Ioo en, hva]
      have hb : ∀ v ∈ Ioc 0 (scOutVX x X), |formOCSA a x v| ≤
          C * (1 + |log a| + |log x|) + C * |log v| := fun v hv' => by
        have := hC a ha x ⟨hx.1, h.le⟩ v ⟨hv'.1, hv'.2.trans hVQ⟩
        linarith
      have hgi : IntegrableOn (fun v => C * (1 + |log a| + |log x|) + C * |log v|)
          (Ioc 0 (setCKQ X)) :=
        (integrableOn_const (by simp)).add ((formOC_integrableOn_abs_log _).const_mul C)
      calc ∫ v in Ioc 0 (scOutVX x X), |formOCSA a x v|
          ≤ ∫ v in Ioc 0 (scOutVX x X), C * (1 + |log a| + |log x|) + C * |log v| :=
            setIntegral_mono_on hk.abs (hgi.mono_set (Ioc_subset_Ioc_right hVQ))
              measurableSet_Ioc hb
        _ ≤ ∫ v in Ioc 0 (setCKQ X), C * (1 + |log a| + |log x|) + C * |log v| := by
            refine setIntegral_mono_set hgi (Eventually.of_forall fun v => ?_)
              (Ioc_subset_Ioc_right hVQ).eventuallyLE
            have := abs_nonneg (log v)
            simp only [Pi.zero_apply]
            positivity
        _ = formOCAMaj X C (a, x) := by
            rw [integral_add (integrableOn_const (by simp))
              ((formOC_integrableOn_abs_log _).const_mul C), setIntegral_const,
              integral_const_mul, Real.volume_real_Ioc_of_le (setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩)]
            unfold formOCAMaj
            simp only [smul_eq_mul]
            ring
  · have e : ∀ X', formOCAF X ((a, x), X') = 0 := fun X' => by
      simp only [formOCAF]
      exact ite_eq_right_iff.2 fun h' => absurd (h'.1.trans h'.2) h
    simp only [e, norm_zero, integral_zero]
    refine ⟨integrable_zero _ _ _, ?_, hmaj⟩
    simp only [formOCGA, h, ↓reduceIte]

theorem formOC_integrable_AMaj (X C : ℝ) :
    Integrable (formOCAMaj X C) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hl : Integrable (fun v => |log v|) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (formOC_integrableOn_abs_log 1).mono_set Ioo_subset_Ioc_self
  have h1 := hl.comp_fst (volume.restrict (Ioo (0 : ℝ) 1))
  have h2 := hl.comp_snd (volume.restrict (Ioo (0 : ℝ) 1))
  unfold formOCAMaj
  exact ((((integrable_const 1).add h1).add h2).const_mul _ |>.add (integrable_const _)).const_mul C

/-- **The `A`-part kernel is integrable** on `(0, 1)³`. -/
theorem formOC_integrable_AF (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (formOCAF X) (((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨C, hC0, hC⟩ := formOC_SA_bound (V := setCKQ X) hX.2
    (by simpa [setCKQ] using setCKQ_lt le_rfl hX.1 hX.2)
  refine (integrable_prod_iff (measurable_formOCAF X).aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [formOC_ae_mem2] with q hq
    exact (formOC_AF_section hX hC hC0 hq.1 hq.2).1
  · refine Integrable.mono' (formOC_integrable_AMaj X C)
      ((measurable_formOCAF X).aestronglyMeasurable.norm.integral_prod_right') ?_
    filter_upwards [formOC_ae_mem2] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact (formOC_AF_section hX hC hC0 hq.1 hq.2).2.2

/-- **The `A`-part at the node**: Fubini moves the node variable `X'` outside. -/
theorem formOC_A_part (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (formOCGA X) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) ∧
      (∀ᵐ X' ∂(volume.restrict (Ioo (0 : ℝ) 1)), X' < X →
        Integrable (formOCIA X') ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)))) ∧
      ∫ q, formOCGA X q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1))) =
        ∫ X' in Ioo (0 : ℝ) 1, if X' < X then setCKdQ X' * ∫ q, formOCIA X' q
          ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))
          else 0 := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  obtain ⟨C, hC0, hC⟩ := formOC_SA_bound (V := setCKQ X) hX.2
    (by simpa [setCKQ] using setCKQ_lt le_rfl hX.1 hX.2)
  have hF := formOC_integrable_AF hX
  have hG : Integrable (fun q => ∫ X', formOCAF X (q, X') ∂μ) (μ.prod μ) :=
    hF.integral_prod_left
  have hae : (fun q => ∫ X', formOCAF X (q, X') ∂μ) =ᵐ[μ.prod μ] formOCGA X := by
    filter_upwards [formOC_ae_mem2] with q hq
    exact (formOC_AF_section hX hC hC0 hq.1 hq.2).2.1
  have e : ∀ q X', formOCAF X (q, X') = if X' < X then setCKdQ X' * formOCIA X' q else 0 := by
    intro q X'
    unfold formOCAF formOCIA
    by_cases h1 : q.2 < X' <;> by_cases h2 : X' < X <;> simp [h1, h2]
  refine ⟨hG.congr hae, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo, hF.prod_left_ae] with X' h1 h2 hlt
    have hd := setCKdQ_pos h1
    simp only [e, hlt, ↓reduceIte] at h2
    refine (h2.const_mul (setCKdQ X')⁻¹).congr (Eventually.of_forall fun q => ?_)
    simp only
    field_simp
  · rw [← integral_congr_ae hae, ← integral_prod _ hF, integral_prod_symm _ hF]
    refine integral_congr_ae (Eventually.of_forall fun X' => ?_)
    simp only [e]
    split_ifs
    · exact integral_const_mul _ _
    · exact integral_zero _ _

end

end QED.ChainProof.SetCK

end
