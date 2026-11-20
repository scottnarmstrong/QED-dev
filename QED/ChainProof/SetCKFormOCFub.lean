/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCH
public import QED.ChainProof.SetCKFormOCThr
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Set (c), Stage K, closed forms: the outer-massive corner weight in the coordinates `y₃ = a Y`

Helper level (no frozen statement). Step 1 of the `ρ_oC` route (Session 27+/28+ of the Stage K
notes). On the cube `(0, 1)³` with `μ = volume|(0, 1)` the substitution `y₃ = a Y` (Jacobian
`Y`) maps `(Y, (a, x))` onto the region `y₃ < Y` of the coordinates `(Y, (y₃, x))`:

* **`formOC_lintegral_cov`**: for a measurable `g ≥ 0` vanishing where `Y ≤ y₃`,
  `∫⁻ Y g(Y, a Y, x) = ∫⁻ g` (lower integrals over the cube);
* **`formOC_integral_cov`**: the same for an integrable real `f`, with the integrability of the
  transformed function.

Applied to the kernel of `H_oC = scOutCH` (**`formOCKer`**,
`(Y, (a, x)) ↦ Y · 1{x < X} T(Y, a Y, x, Q(X) - Q(x))`):

**`formOC_scOutCH_ae_eq`**: for almost every `X ∈ (0, 1)`, `formOCKer X` is integrable on the
cube and `H_oC(X) = 2 ∫ formOCKer X`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory
open scoped ENNReal

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The outer-massive corner kernel in the coordinates `y₃ = a Y`**, on `(Y, (a, x))`. -/
noncomputable def formOCKer (X : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  p.1 * scOutCKer p.1 (p.2.1 * p.1) p.2.2 X

/-- The substitution `y₃ = a Y` at fixed `Y ∈ (0, 1)`, for a function vanishing on `y₃ ≥ Y`. -/
theorem formOC_lintegral_sub {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) {h : ℝ → ℝ≥0∞}
    (hz : ∀ y3, Y ≤ y3 → h y3 = 0) :
    ∫⁻ a in Ioo (0 : ℝ) 1, ENNReal.ofReal Y * h (a * Y) = ∫⁻ y3 in Ioo (0 : ℝ) 1, h y3 := by
  have hd : ∀ a ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun a => a * Y) Y (Ioo 0 1) a :=
    fun a _ => ((hasDerivAt_id a).mul_const Y).hasDerivWithinAt.congr_deriv (one_mul Y)
  have hinj : InjOn (fun a : ℝ => a * Y) (Ioo 0 1) :=
    fun a _ b _ hab => mul_right_cancel₀ hY.1.ne' hab
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj h
  rw [image_mul_right_Ioo _ _ hY.1, zero_mul, one_mul, abs_of_pos hY.1] at himg
  rw [← himg]
  have hU : Ioo (0 : ℝ) 1 = Ioo 0 Y ∪ Ico Y 1 := (Ioo_union_Ico_eq_Ioo hY.1 hY.2.le).symm
  rw [hU, lintegral_union measurableSet_Ico
    (Set.disjoint_left.2 fun _ h1 h2 => (not_le.2 h1.2) h2.1)]
  have h0 : ∫⁻ y3 in Ico Y 1, h y3 = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ico (g := fun _ => 0) fun y3 hy3 => hz y3 hy3.1]
    exact lintegral_zero
  rw [h0, add_zero]

/-- **The substitution `y₃ = a Y` on the cube**, for lower integrals. -/
theorem formOC_lintegral_cov {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g)
    (hz : ∀ q : ℝ × ℝ × ℝ, q.1 ≤ q.2.1 → g q = 0) :
    ∫⁻ p, ENNReal.ofReal p.1 * g (p.1, p.2.1 * p.1, p.2.2)
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) =
      ∫⁻ q, g q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  have hm : Measurable fun p : ℝ × ℝ × ℝ => ENNReal.ofReal p.1 * g (p.1, p.2.1 * p.1, p.2.2) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hg.comp (measurable_fst.prodMk ((measurable_snd.fst.mul measurable_fst).prodMk
        measurable_snd.snd)))
  rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hg.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioo fun Y hY => ?_
  have hmY : ∀ Y : ℝ, Measurable fun q : ℝ × ℝ => g (Y, q) :=
    fun Y => hg.comp (measurable_const.prodMk measurable_id)
  have hmY' : Measurable fun q : ℝ × ℝ => ENNReal.ofReal Y * g (Y, q.1 * Y, q.2) :=
    measurable_const.mul (hg.comp (measurable_const.prodMk
      ((measurable_fst.mul measurable_const).prodMk measurable_snd)))
  rw [lintegral_prod _ hmY'.aemeasurable, lintegral_prod _ (hmY Y).aemeasurable]
  have hx : ∀ y3, Measurable fun x => g (Y, y3, x) :=
    fun y3 => (hmY Y).comp (measurable_const.prodMk measurable_id)
  simp only [lintegral_const_mul _ (hx _)]
  refine formOC_lintegral_sub (h := fun y3 => ∫⁻ x in Ioo (0 : ℝ) 1, g (Y, y3, x)) hY
    fun y3 hy => ?_
  have e : ∀ x, g (Y, y3, x) = 0 := fun x => hz (Y, y3, x) hy
  simp only [e, lintegral_zero]

/-- **The substitution `y₃ = a Y` on the cube**, for an integrable real function. -/
theorem formOC_integral_cov {f : ℝ × ℝ × ℝ → ℝ} (hf : Measurable f)
    (hz : ∀ q : ℝ × ℝ × ℝ, q.1 ≤ q.2.1 → f q = 0)
    (hI : Integrable f ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))))) :
    Integrable (fun p : ℝ × ℝ × ℝ => p.1 * f (p.1, p.2.1 * p.1, p.2.2))
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) ∧
      ∫ p, p.1 * f (p.1, p.2.1 * p.1, p.2.2)
          ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
            ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) =
        ∫ q, f q ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
            ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  set ν := (volume.restrict (Ioo (0 : ℝ) 1)).prod
    ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))
  have hT : Measurable fun p : ℝ × ℝ × ℝ => (p.1, p.2.1 * p.1, p.2.2) :=
    measurable_fst.prodMk ((measurable_snd.fst.mul measurable_fst).prodMk measurable_snd.snd)
  have hFm : Measurable fun p : ℝ × ℝ × ℝ => p.1 * f (p.1, p.2.1 * p.1, p.2.2) :=
    measurable_fst.mul (hf.comp hT)
  have hpos : ∀ᵐ p ∂ν, 0 ≤ p.1 := by
    filter_upwards [ae_mem_cube] with p hp
    exact hp.1.1.le
  have key : ∀ φ : ℝ → ℝ, Measurable φ → φ 0 = 0 →
      ∫⁻ p, ENNReal.ofReal (p.1 * φ (f (p.1, p.2.1 * p.1, p.2.2))) ∂ν =
        ∫⁻ q, ENNReal.ofReal (φ (f q)) ∂ν := by
    intro φ hφ h0
    have hc := formOC_lintegral_cov (g := fun q => ENNReal.ofReal (φ (f q)))
      (ENNReal.measurable_ofReal.comp (hφ.comp hf))
      fun q hq => by simp only [hz q hq, h0, ENNReal.ofReal_zero]
    rw [← hc]
    refine lintegral_congr_ae ?_
    filter_upwards [hpos] with p hp
    simp only [ENNReal.ofReal_mul hp]
  have hfin : ∫⁻ p, ‖p.1 * f (p.1, p.2.1 * p.1, p.2.2)‖ₑ ∂ν < ⊤ := by
    have e : ∫⁻ p, ‖p.1 * f (p.1, p.2.1 * p.1, p.2.2)‖ₑ ∂ν = ∫⁻ q, ‖f q‖ₑ ∂ν := by
      simp only [← ofReal_norm, Real.norm_eq_abs]
      rw [← key (fun t => |t|) continuous_abs.measurable abs_zero]
      refine lintegral_congr_ae ?_
      filter_upwards [hpos] with p hp
      rw [abs_mul, abs_of_nonneg hp]
    rw [e]
    exact hI.2
  have hI' : Integrable (fun p : ℝ × ℝ × ℝ => p.1 * f (p.1, p.2.1 * p.1, p.2.2)) ν :=
    ⟨hFm.aestronglyMeasurable, hfin⟩
  refine ⟨hI', ?_⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI',
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
  have k1 := key id measurable_id rfl
  have k2 := key (fun t => -t) measurable_neg neg_zero
  simp only [id, mul_neg] at k1 k2
  rw [k1, k2]

/-- The kernel section of `H_oC` at `X` is integrable on the cube for almost every `X`. -/
theorem formOC_ae_integrable_scOutCKer :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Integrable (fun p : ℝ × ℝ × ℝ => scOutCKer p.1 p.2.1 p.2.2 X)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  filter_upwards [(integrable_scOutCKerT one_pos (scOutC_bound one_pos)).prod_left_ae,
    ae_restrict_mem measurableSet_Ioo] with X hI hX
  have hd := setCKdQ_pos hX
  have hq : 0 < setCKQ X + 1 := by linarith [setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩]
  have hw : 0 < setCKdQ X / (setCKQ X + 1) ^ 2 := by positivity
  refine (hI.div_const (setCKdQ X / (setCKQ X + 1) ^ 2)).congr
    (Eventually.of_forall fun p => ?_)
  simp only [scOutCKerT]
  field_simp

/-- `(Y, y₃, x) ↦ 1{y₃ < Y, x < X} T(Y, y₃, x, Q(X) - Q(x))` is measurable. -/
theorem formOC_measurable_scOutCKer (X : ℝ) :
    Measurable fun q : ℝ × ℝ × ℝ => scOutCKer q.1 q.2.1 q.2.2 X := by
  have hv : Measurable fun q : ℝ × ℝ × ℝ => scOutVX q.2.2 X := by
    unfold scOutVX
    exact measurable_const.sub (measurable_setCKQ.comp measurable_snd.snd)
  have hK : Measurable fun q : ℝ × ℝ × ℝ => scOutCT q.1 q.2.1 q.2.2 (scOutVX q.2.2 X) :=
    measurable_scOutCT.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
      (measurable_snd.snd.prodMk hv)))
  have hs : MeasurableSet {q : ℝ × ℝ × ℝ | q.2.1 < q.1 ∧ q.2.2 < X} :=
    (measurableSet_lt measurable_snd.fst measurable_fst).inter
      (measurableSet_lt measurable_snd.snd measurable_const)
  unfold scOutCKer
  exact Measurable.ite hs hK measurable_const

/-- **`H_oC` in the coordinates `y₃ = a Y`**: for almost every `X ∈ (0, 1)` the kernel
`formOCKer X` is integrable on the cube and `H_oC(X) = 2 ∫ formOCKer X`. -/
theorem formOC_scOutCH_ae_eq :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Integrable (formOCKer X) ((volume.restrict (Ioo (0 : ℝ) 1)).prod
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) ∧
        scOutCH X = 2 * ∫ p, formOCKer X p ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
          ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  filter_upwards [formOC_ae_integrable_scOutCKer] with X hI
  have hz : ∀ q : ℝ × ℝ × ℝ, q.1 ≤ q.2.1 → scOutCKer q.1 q.2.1 q.2.2 X = 0 := by
    intro q hq
    unfold scOutCKer
    exact ite_eq_right_iff.2 fun h => absurd h.1 (not_lt.2 hq)
  obtain ⟨h1, h2⟩ := formOC_integral_cov (formOC_measurable_scOutCKer X) hz hI
  exact ⟨h1, by rw [scOutCH, ← h2]; rfl⟩

end QED.ChainProof.SetCK

end
