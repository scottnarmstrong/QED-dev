/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCLCF
public import QED.ChainProof.SetCKAsmLam
public import QED.ChainProof.SetCKAsmRho

/-!
# Set (c), Stage K, closed forms: `H_oC = ∫₀^X ρ_oC Q` (conditional on items 3–5)

Helper level (no frozen statement). Item 6 (OCE) of the `ρ_oC` route (Stage K notes,
Session 30+). From the node form `formOC_scOutCH_node`,

`H_oC(X) = 2 (∫_{X' < X} Q'(X') (J_K + J_A)(X') + ∫_a (∫_{(0,X)} f(a, x) dx - 𝓛(a, X)))`,

and the per-`X'` identity `ρ_oC Q/2 = ∫_a (f + Q' N - ℓ_a)` (items 3–5), Fubini in `(a, X')`
together with `𝓛(a, X) = ∫₀^X ℓ_a` (`formOCLL_eq_integral`) gives
(**`scOutCH_ae_eq_setCKRhoH_of_formOCG`**)

`∀ᵐ X ∈ (0, 1), scOutCH X = setCKRhoH rhoScOutC X`,

the only hypothesis of `setCKDisp_eq_aSetC_of_scOutCH`. The theorem takes as hypotheses exactly
the statements of items 4 and 5 with the function `N` (`formOCN`) and `G` (the integrand of `𝒢`)
as parameters:
* `hN`: the shape of `formOC_JK_add_JA`;
* `hG`: `f + Q' N - ℓ_a = G` off `a = 1/2`, with `ℓ_a` in letters (`formOCellC`);
* `hGi`: `∫₀¹ G(a, X) da = ρ_oC(X) Q(X)/2` on `(0, 1)`.
Integrability: `1{x < X} f` from `φ_X` and the bounded `β_c` times `log v`
(`formOCE_integrable_f`); `1{x < X} ℓ_a` from the uniform bound (`formOCE_integrable_ell`);
the `X'`-integrands of the node form from the kernels `formOCKF`, `formOCAF`
(`formOCE_integrable_uK`, `formOCE_integrable_uA`).
-/

@[expose] public section

open Real Set Filter MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

section

variable {X : ℝ}

/-- `∫_{(0,1)} 1{x < X} g = ∫_{(0,X)} g` for `X ≤ 1`. -/
theorem formOCE_ite_integral (hX : X ≤ 1) (g : ℝ → ℝ) :
    ∫ x in Ioo (0 : ℝ) 1, (if x < X then g x else 0) = ∫ x in Ioo (0 : ℝ) X, g x := by
  have hset : Ioo (0 : ℝ) 1 ∩ Iio X = Ioo 0 X := by
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨⟨h0, _⟩, h⟩
      exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨h0, lt_of_lt_of_le h hX⟩, h⟩
  have e : (fun x => if x < X then g x else 0) = (Iio X).indicator g := by
    funext x
    by_cases h : x < X
    · simp [h]
    · simp [h]
  rw [e, setIntegral_indicator measurableSet_Iio, hset]

theorem formOCE_integrableOn_ite (hX : X ≤ 1) {g : ℝ → ℝ}
    (hg : Integrable (fun x => if x < X then g x else 0) (volume.restrict (Ioo (0 : ℝ) 1))) :
    IntegrableOn g (Ioo 0 X) := by
  have h : IntegrableOn (fun x => if x < X then g x else 0) (Ioo 0 X) :=
    hg.mono_measure (Measure.restrict_mono (Ioo_subset_Ioo_right hX) le_rfl)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioo
  simp only [hx.2, ↓reduceIte]

theorem formOCE_abs_beta_le (hX : X < 1) {a x : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) X) : |formOCbeta a x| ≤ 1 / (4 * (1 - X) ^ 2) := by
  have hx1 : x < 1 := hx.2.trans hX
  have hL : 1 - X ≤ 1 - a * x := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have hM : 1 - X ≤ 1 - x + a * x := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have h1X : 0 < 1 - X := by linarith
  rw [formOCbeta_eq hx1.ne, abs_div, abs_neg, abs_of_nonneg (by positivity),
    abs_of_pos (by have := lt_of_lt_of_le h1X hL; have := lt_of_lt_of_le h1X hM; positivity)]
  have hx4 : x ^ 4 ≤ 1 := pow_le_one₀ hx.1.le hx1.le
  have hLM : (1 - X) ^ 2 ≤ (1 - a * x) * (1 - x + a * x) := by
    rw [sq]
    exact mul_le_mul hL hM h1X.le (by linarith)
  have hpos : 0 < 4 * ((1 - a * x) * (1 - x + a * x)) := by
    have := lt_of_lt_of_le h1X hL
    have := lt_of_lt_of_le h1X hM
    positivity
  calc x ^ 4 / (4 * ((1 - a * x) * (1 - x + a * x))) ≤ 1 / (4 * ((1 - a * x) * (1 - x + a * x)))
        := by gcongr
    _ ≤ 1 / (4 * (1 - X) ^ 2) := by gcongr

/-- The `β_c log v` part of `φ_X`, on `(0, 1)²`. -/
theorem formOCE_integrable_blog (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun q : ℝ × ℝ => if q.2 < X then formOCbeta q.1 q.2 * log (scOutVX q.2 X)
      else 0) ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  have hl : Integrable (fun x => if x < X then log (scOutVX x X) else 0) μ := by
    have h1 := (formOC_integrableOn_logv hX).integrable_indicator measurableSet_Ioo
    have h2 : Integrable ((Ioo 0 X).indicator fun x => log (scOutVX x X)) μ :=
      h1.mono_measure Measure.restrict_le_self
    refine h2.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    by_cases h : x < X
    · simp [h, indicator_of_mem (show x ∈ Ioo 0 X from ⟨hx.1, h⟩)]
    · simp [h]
  have hg := (hl.abs.comp_snd μ).const_mul (1 / (4 * (1 - X) ^ 2))
  have hm : Measurable fun q : ℝ × ℝ => if q.2 < X then
      formOCbeta q.1 q.2 * log (scOutVX q.2 X) else 0 := by
    have h1 : Measurable fun q : ℝ × ℝ => formOCbeta q.1 q.2 * log (scOutVX q.2 X) := by
      unfold formOCbeta formOCD0 scOutVX setCKQ
      fun_prop
    exact Measurable.ite (measurableSet_lt measurable_snd measurable_const) h1 measurable_const
  refine hg.mono' hm.aestronglyMeasurable ?_
  filter_upwards [formOC_ae_mem2] with q hq
  by_cases h : q.2 < X
  · simp only [h, ↓reduceIte, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (formOCE_abs_beta_le hX.2 hq.1 ⟨hq.2.1, h⟩)
      (abs_nonneg _)
  · simp only [h, ↓reduceIte, norm_zero, abs_zero, mul_zero, le_refl]

/-- **`1{x < X} f` is integrable on `(0, 1)²`** when `φ_X` is. -/
theorem formOCE_integrable_f (hX : X ∈ Ioo (0 : ℝ) 1)
    (hPhi : Integrable (formOCPhi X) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)))) :
    Integrable (fun q : ℝ × ℝ => if q.2 < X then formOCf q.1 q.2 else 0)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  refine (hPhi.add (formOCE_integrable_blog hX)).congr (Eventually.of_forall fun q => ?_)
  by_cases h : q.2 < X
  · simp only [Pi.add_apply, formOCPhi, h, ↓reduceIte, formOCf]
    ring
  · simp only [Pi.add_apply, formOCPhi, h, ↓reduceIte, add_zero]

/-- **`1{x < X} ℓ_a(x)` is integrable on `(0, 1)²`.** -/
theorem formOCE_integrable_ell (hX : X < 1) :
    Integrable (fun q : ℝ × ℝ => if q.2 < X then formOCell q.1 q.2 else 0)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨M, hM⟩ := formOCell_bound hX
  have hm : AEStronglyMeasurable (fun q : ℝ × ℝ => if q.2 < X then formOCell q.1 q.2 else 0)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    (stronglyMeasurable_formOCell.ite (measurableSet_lt measurable_snd measurable_const)
      stronglyMeasurable_const).aestronglyMeasurable
  refine (integrable_const (max M 0)).mono' hm ?_
  filter_upwards [formOC_ae_mem2] with q hq
  by_cases h : q.2 < X
  · simp only [h, ↓reduceIte, Real.norm_eq_abs]
    exact (hM q.1 ⟨hq.1.1.le, hq.1.2.le⟩ q.2 ⟨hq.2.1.le, h.le⟩).trans (le_max_left _ _)
  · simp only [h, ↓reduceIte, norm_zero]
    exact le_max_right _ _

/-- The `X'`-integrand of the `K`-part of the node form is integrable. -/
theorem formOCE_integrable_uK (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun X' => if X' < X then setCKdQ X' * ∫ q, formOCIK X' q
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) else 0)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  have hF := formOC_integrable_KF hX
  refine hF.integral_prod_right.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hF.prod_left_ae] with X' hX' hsec
  rw [integral_prod _ hsec]
  have e : (fun q => ∫ Y, formOCKF X ((q, Y), X') ∂μ) =ᵐ[μ.prod μ]
      fun q => if X' < X then setCKdQ X' * formOCIK X' q else 0 := by
    filter_upwards [formOC_ae_mem2] with q hq
    exact formOC_KF_Y hX' hq.1 hq.2
  rw [integral_congr_ae e]
  split_ifs
  · exact integral_const_mul _ _
  · exact integral_zero _ _

/-- The `X'`-integrand of the `A`-part of the node form is integrable. -/
theorem formOCE_integrable_uA (hX : X ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun X' => if X' < X then setCKdQ X' * ∫ q, formOCIA X' q
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) else 0)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hF := formOC_integrable_AF hX
  have e : ∀ q X', formOCAF X (q, X') = if X' < X then setCKdQ X' * formOCIA X' q else 0 := by
    intro q X'
    unfold formOCAF formOCIA
    by_cases h1 : q.2 < X' <;> by_cases h2 : X' < X <;> simp [h1, h2]
  refine hF.integral_prod_right.congr (Eventually.of_forall fun X' => ?_)
  simp only [e]
  split_ifs
  · exact integral_const_mul _ _
  · exact integral_zero _ _

theorem formOCE_ae_ne_half :
    ∀ᵐ a ∂(volume.restrict (Ioo (0 : ℝ) 1)), a ≠ 1 / 2 :=
  Measure.ae_ne _ _

/-- **`H_oC = ∫₀^X ρ_oC Q`, conditional on items 3–5** (`N`: the `x`-integral of
`g_k + S_A`, item 4; `G`: the integrand of `𝒢`, item 5). -/
theorem scOutCH_ae_eq_setCKRhoH_of_formOCG {N G : ℝ → ℝ → ℝ}
    (hN : ∀ X' : ℝ, X' < 1 →
      Integrable (formOCIK X') ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) →
      Integrable (formOCIA X') ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) →
      IntegrableOn (fun a => N a X') (Ioo 0 1) ∧
        (∫ q, formOCIK X' q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
            (volume.restrict (Ioo (0 : ℝ) 1)))) +
          ∫ q, formOCIA X' q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
            (volume.restrict (Ioo (0 : ℝ) 1))) = ∫ a in Ioo (0 : ℝ) 1, N a X')
    (hG : ∀ a ∈ Ioo (0 : ℝ) 1, a ≠ 1 / 2 → ∀ X ∈ Ioo (0 : ℝ) 1,
      formOCf a X + setCKdQ X * N a X - formOCellC a X = G a X)
    (hGi : ∀ X ∈ Ioo (0 : ℝ) 1, ∫ a in Ioo (0 : ℝ) 1, G a X = rhoScOutC X * setCKQ X / 2) :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)), scOutCH X = setCKRhoH rhoScOutC X := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  filter_upwards [formOC_scOutCH_node, ae_restrict_mem measurableSet_Ioo] with X hnode hX
  obtain ⟨hPhi, hIKA, hH⟩ := hnode
  have hf := formOCE_integrable_f hX hPhi
  have hl := formOCE_integrable_ell (X := X) hX.2
  have huK := formOCE_integrable_uK hX
  have huA := formOCE_integrable_uA hX
  -- the density at a.e. node `X' < X`
  have hpt : ∀ᵐ X' ∂μ, X' < X → rhoScOutC X' * setCKQ X' =
      2 * ((∫ a, formOCf a X' ∂μ) + setCKdQ X' * ((∫ q, formOCIK X' q ∂(μ.prod μ)) +
        ∫ q, formOCIA X' q ∂(μ.prod μ)) - ∫ a, formOCell a X' ∂μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hIKA, hf.prod_left_ae, hl.prod_left_ae]
      with X' hX' hia hfs hls hlt
    obtain ⟨hNi, hNe⟩ := hN X' hX'.2 (hia hlt).1 (hia hlt).2
    simp only [hlt, ↓reduceIte] at hfs hls
    have hGa := hGi X' hX'
    have e1 : ∫ a in Ioo (0 : ℝ) 1, G a X' =
        ∫ a, (formOCf a X' + setCKdQ X' * N a X' - formOCell a X') ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo, formOCE_ae_ne_half] with a ha ha2
      rw [← hG a ha ha2 X' hX', formOCell_eq ha ha2 hX']
    have hNi' : Integrable (fun a => setCKdQ X' * N a X') μ := hNi.const_mul _
    have e2 : ∫ a, (formOCf a X' + setCKdQ X' * N a X' - formOCell a X') ∂μ =
        (∫ a, formOCf a X' ∂μ) + setCKdQ X' * (∫ a, N a X' ∂μ) - ∫ a, formOCell a X' ∂μ := by
      rw [integral_sub (f := fun a => formOCf a X' + setCKdQ X' * N a X') (hfs.add hNi') hls,
        integral_add (f := fun a => formOCf a X') (g := fun a => setCKdQ X' * N a X') hfs hNi',
        integral_const_mul]
    rw [e1, e2, ← hNe] at hGa
    linarith
  -- integrability on `(0, X)` of the three parts
  have hF1 : IntegrableOn (fun X' => ∫ a, formOCf a X' ∂μ) (Ioo 0 X) := by
    refine formOCE_integrableOn_ite hX.2.le (hf.integral_prod_right.congr
      (Eventually.of_forall fun x => ?_))
    by_cases h : x < X
    · simp only [h, ↓reduceIte]
      rfl
    · simp [h]
  have hF3 : IntegrableOn (fun X' => ∫ a, formOCell a X' ∂μ) (Ioo 0 X) := by
    refine formOCE_integrableOn_ite hX.2.le (hl.integral_prod_right.congr
      (Eventually.of_forall fun x => ?_))
    by_cases h : x < X
    · simp only [h, ↓reduceIte]
      rfl
    · simp [h]
  have hQJ : IntegrableOn (fun X' => setCKdQ X' * ((∫ q, formOCIK X' q ∂(μ.prod μ)) +
      ∫ q, formOCIA X' q ∂(μ.prod μ))) (Ioo 0 X) := by
    refine formOCE_integrableOn_ite hX.2.le ((huK.add huA).congr
      (Eventually.of_forall fun x => ?_))
    by_cases h : x < X
    · simp only [Pi.add_apply, h, ↓reduceIte]
      ring
    · simp [h]
  -- `∫₀^X ρ Q`
  have hRho : setCKRhoH rhoScOutC X = ∫ X' in Ioo (0 : ℝ) X,
      2 * ((∫ a, formOCf a X' ∂μ) + setCKdQ X' * ((∫ q, formOCIK X' q ∂(μ.prod μ)) +
        ∫ q, formOCIA X' q ∂(μ.prod μ)) - ∫ a, formOCell a X' ∂μ) := by
    unfold setCKRhoH
    rw [intervalIntegral.integral_of_le hX.1.le, integral_Ioc_eq_integral_Ioo]
    refine integral_congr_ae ?_
    have h := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hX.2.le) hpt
    filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with X' h1 h2
    exact h1 h2.2
  -- Fubini for the `f`-part
  have hV1 : ∫ X' in Ioo (0 : ℝ) X, (∫ a, formOCf a X' ∂μ) =
      ∫ a, (∫ x in Ioo (0 : ℝ) X, formOCf a x) ∂μ := by
    rw [← formOCE_ite_integral hX.2.le]
    have e : (fun x => if x < X then ∫ a, formOCf a x ∂μ else 0) =
        fun x => ∫ a, (if x < X then formOCf a x else 0) ∂μ := by
      funext x
      by_cases h : x < X <;> simp [h]
    rw [e, ← integral_prod_symm _ hf, integral_prod _ hf]
    exact integral_congr_ae (Eventually.of_forall fun a => formOCE_ite_integral hX.2.le _)
  -- Fubini and FTC for the `ℓ`-part
  have hV3 : ∫ X' in Ioo (0 : ℝ) X, (∫ a, formOCell a X' ∂μ) = ∫ a, formOCLL a X ∂μ := by
    rw [← formOCE_ite_integral hX.2.le]
    have e : (fun x => if x < X then ∫ a, formOCell a x ∂μ else 0) =
        fun x => ∫ a, (if x < X then formOCell a x else 0) ∂μ := by
      funext x
      by_cases h : x < X <;> simp [h]
    rw [e, ← integral_prod_symm _ hl, integral_prod _ hl]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    rw [formOCE_ite_integral hX.2.le, formOCLL_eq_integral ⟨ha.1.le, ha.2.le⟩ hX,
      intervalIntegral.integral_of_le hX.1.le, integral_Ioc_eq_integral_Ioo]
  -- the node part
  have hV2 : ∫ X' in Ioo (0 : ℝ) X, setCKdQ X' * ((∫ q, formOCIK X' q ∂(μ.prod μ)) +
      ∫ q, formOCIA X' q ∂(μ.prod μ)) =
      (∫ X' in Ioo (0 : ℝ) 1, if X' < X then setCKdQ X' * ∫ q, formOCIK X' q ∂(μ.prod μ)
        else 0) +
      ∫ X' in Ioo (0 : ℝ) 1, if X' < X then setCKdQ X' * ∫ q, formOCIA X' q ∂(μ.prod μ)
        else 0 := by
    rw [← integral_add huK huA, ← formOCE_ite_integral hX.2.le]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases h : x < X
    · simp only [h, ↓reduceIte]
      ring
    · simp [h]
  -- `∫ φ_X`
  have hfa : Integrable (fun a => ∫ x in Ioo (0 : ℝ) X, formOCf a x) μ := by
    refine hf.integral_prod_left.congr (Eventually.of_forall fun a => ?_)
    exact formOCE_ite_integral hX.2.le (formOCf a)
  have hLa : Integrable (fun a => formOCLL a X) μ := by
    refine hl.integral_prod_left.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    rw [formOCE_ite_integral hX.2.le, formOCLL_eq_integral ⟨ha.1.le, ha.2.le⟩ hX,
      intervalIntegral.integral_of_le hX.1.le, integral_Ioc_eq_integral_Ioo]
  have hPhiV : ∫ q, formOCPhi X q ∂(μ.prod μ) =
      (∫ a, (∫ x in Ioo (0 : ℝ) X, formOCf a x) ∂μ) - ∫ a, formOCLL a X ∂μ := by
    rw [← integral_sub hfa hLa]
    exact formOC_integral_phi hX hPhi
  have hsplit : ∫ X' in Ioo (0 : ℝ) X,
      ((∫ a, formOCf a X' ∂μ) + setCKdQ X' * ((∫ q, formOCIK X' q ∂(μ.prod μ)) +
        ∫ q, formOCIA X' q ∂(μ.prod μ)) - ∫ a, formOCell a X' ∂μ) =
      (∫ X' in Ioo (0 : ℝ) X, (∫ a, formOCf a X' ∂μ)) +
        (∫ X' in Ioo (0 : ℝ) X, setCKdQ X' * ((∫ q, formOCIK X' q ∂(μ.prod μ)) +
          ∫ q, formOCIA X' q ∂(μ.prod μ))) -
        ∫ X' in Ioo (0 : ℝ) X, (∫ a, formOCell a X' ∂μ) := by
    rw [integral_sub (f := fun X' => (∫ a, formOCf a X' ∂μ) + setCKdQ X' *
      ((∫ q, formOCIK X' q ∂(μ.prod μ)) + ∫ q, formOCIA X' q ∂(μ.prod μ))) (hF1.add hQJ) hF3,
      integral_add (f := fun X' => ∫ a, formOCf a X' ∂μ) hF1 hQJ]
  rw [← hμ] at hH
  rw [hH, hRho, integral_const_mul, hsplit, hV1, hV2, hV3, hPhiV]
  ring

end

end QED.ChainProof.SetCK

end
