/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI4Def
import QED.TwoLoop.UnitXGraphChengWuSet
import QED.Integration.ChengWu
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Set (e), master I₄: the Cheng–Wu gauge shared with I₂, for general integrands

`QED.ThreeLoopE.i4PInt_zero_eq` moves the period `∫ U⁻²` of I₄ from the simplex chart
`QED.ThreeLoopE.i4Dom` to the domain `QED.ThreeLoopD.i2Dom` of the set (d) master I₂, with the
Cheng–Wu gauge `a + b + l = 1`,

  `(a, b, c, l, m, n) = ((1 - w) x, w, y₈, (1 - w)(1 - x), y₄, y₇)`,

Jacobian `1 - w`. Here the same change of variables is proved for every function
`g(a, b, c, l, m, n)` homogeneous of degree `-6` on the positive orthant, both for the integral
and for integrability (`QED.ThreeLoopE.i4Gauge_integral`,
`QED.ThreeLoopE.i4Gauge_integrableOn_iff`). The logarithmic moments
`∫ (4 log U - 3 log F)ᵏ / U²` are of this form, since `U` and `F` are homogeneous of degrees
3 and 4. The steps are those of `QED.ThreeLoopE.SetEMastersI4Def`: a measure-preserving
relabelling of the simplex, the Cheng–Wu theorem
`QED.TwoLoop.UnitXGraph.integral_simplex_chengWuSet` with gauge set `{0, 1}`, and the triangle
chart scaling the first coordinate by `1 - w`.

## Main definitions

* `QED.ThreeLoopE.i4GaugeIntegrand`: `(1 - w) g((1 - w) x, w, y₈, (1 - w)(1 - x), y₄, y₇)`.

## Main results

* `QED.ThreeLoopE.i4Gauge_integral`, `QED.ThreeLoopE.i4Gauge_integrableOn_iff`.
-/

@[expose] public section

open MeasureTheory Set Function

namespace QED.ThreeLoopE

/-- The integrand of the shared Cheng–Wu gauge on `QED.ThreeLoopD.i2Dom`. -/
def i4GaugeIntegrand (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (z : I4Coords) : ℝ :=
  (1 - z.2.1) * g ((1 - z.2.1) * z.1) z.2.1 z.2.2.2.2 ((1 - z.2.1) * (1 - z.1)) z.2.2.1
    z.2.2.2.1

/-- The integrand on the simplex chart `QED.ThreeLoopE.i4Dom`. -/
def i4SimplexIntegrand (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x : I4Coords) : ℝ :=
  g x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 (i4Last x)

private def gaugeCoordsEquiv : (Fin 5 → ℝ) ≃ᵐ I4Coords :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
        ((MeasurableEquiv.refl ℝ).prodCongr
          ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
            ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ => ℝ)))))))

private theorem measurePreserving_gaugeCoordsEquiv : MeasurePreserving gaugeCoordsEquiv := by
  unfold gaugeCoordsEquiv
  exact ((((MeasurePreserving.id volume).prod
    ((((MeasurePreserving.id volume).prod
      ((((MeasurePreserving.id volume).prod (volume_preserving_piFinTwo (fun _ => ℝ)))).comp
        (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0)))).comp
      (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0)))).comp
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0))

private theorem gaugeCoordsEquiv_apply (x : Fin 5 → ℝ) :
    gaugeCoordsEquiv x = (x 0, x 1, x 2, x 3, x 4) := by
  rfl

private theorem preimage_gauge_i4Dom :
    gaugeCoordsEquiv ⁻¹' i4Dom = QED.Integration.ChengWu.openSimplex 5 := by
  ext x
  simp [gaugeCoordsEquiv_apply, i4Dom, QED.Integration.ChengWu.mem_openSimplex,
    Fin.forall_fin_succ, Fin.sum_univ_succ, add_assoc, and_assoc]

/-- The relabelled six-coordinate form of `g` used on the simplex. -/
private def gaugeForm (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (z : Fin 6 → ℝ) : ℝ :=
  g (z 0) (z 1) (z 4) (z 5) (z 2) (z 3)

private def gaugePerm : Equiv.Perm (Fin 5) := Equiv.swap 2 4

private def gaugePermEquiv : (Fin 5 → ℝ) ≃ᵐ (Fin 5 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 5 => ℝ) gaugePerm

private theorem gaugePermEquiv_apply (x : Fin 5 → ℝ) (i : Fin 5) :
    gaugePermEquiv x i = x (gaugePerm.symm i) := by
  simpa [gaugePermEquiv] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) gaugePerm x (gaugePerm.symm i)

private theorem measurePreserving_gaugePermEquiv : MeasurePreserving gaugePermEquiv :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin 5 => ℝ) gaugePerm

open QED.Integration Feynman TwoLoop ChengWu in
private theorem preimage_gaugePerm :
    gaugePermEquiv ⁻¹' simplexSet 5 = simplexSet 5 := by
  ext x
  simp only [mem_preimage]
  rw [mem_simplexSet_iff (by decide), mem_simplexSet_iff (by decide)]
  have hlast : simplexPoint (gaugePermEquiv x) (Fin.last 5) = simplexPoint x (Fin.last 5) := by
    simp only [simplexPoint_last, gaugePermEquiv_apply, Equiv.sum_comp]
  constructor
  · intro h i
    induction i using Fin.lastCases with
    | last => rw [← hlast]; exact h _
    | cast j =>
      simpa only [simplexPoint_castSucc, gaugePermEquiv_apply, Equiv.symm_apply_apply] using
        h (gaugePerm j).castSucc
  · intro h i
    induction i using Fin.lastCases with
    | last => rw [hlast]; exact h _
    | cast j =>
      simpa only [simplexPoint_castSucc, gaugePermEquiv_apply] using h (gaugePerm.symm j).castSucc

/-- The composite chart from the simplex to `i4Dom`. -/
private def gaugeChart (x : Fin 5 → ℝ) : I4Coords :=
  gaugeCoordsEquiv (QED.Integration.TwoLoop.simplexSwap 3 (gaugePermEquiv x))

open QED.Integration Feynman TwoLoop ChengWu in
private theorem gaugeChart_apply (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (x : Fin 5 → ℝ) :
    i4SimplexIntegrand g (gaugeChart x) = gaugeForm g (simplexPoint x) := by
  have hu (z : Fin 5 → ℝ) : i4SimplexIntegrand g (gaugeCoordsEquiv z) =
      g (simplexPoint z 0) (simplexPoint z 1) (simplexPoint z 2)
        (simplexPoint z 3) (simplexPoint z 4) (simplexPoint z 5) := by
    have hsum : ∑ i, z i = z 0 + (z 1 + (z 2 + (z 3 + z 4))) := by
      simp [Fin.sum_univ_succ]
    simp only [i4SimplexIntegrand, i4Last, gaugeCoordsEquiv_apply,
      show (0 : Fin 6) = (0 : Fin 5).castSucc from rfl,
      show (1 : Fin 6) = (1 : Fin 5).castSucc from rfl,
      show (2 : Fin 6) = (2 : Fin 5).castSucc from rfl,
      show (3 : Fin 6) = (3 : Fin 5).castSucc from rfl,
      show (4 : Fin 6) = (4 : Fin 5).castSucc from rfl,
      show (5 : Fin 6) = Fin.last 5 from rfl,
      simplexPoint_castSucc, simplexPoint_last, hsum, add_assoc]
  rw [gaugeChart, hu]
  unfold gaugeForm
  simp only [simplexPoint_simplexSwap]
  have hlast : simplexPoint (gaugePermEquiv x) 5 = simplexPoint x 5 := by
    change simplexPoint (gaugePermEquiv x) (Fin.last 5) = simplexPoint x (Fin.last 5)
    simp only [simplexPoint_last, gaugePermEquiv_apply, Equiv.sum_comp]
  have shift :
      ∀ i : Fin 6, simplexPoint (gaugePermEquiv x) i =
        simplexPoint x (Equiv.swap (2 : Fin 6) 4 i) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [show Equiv.swap (2 : Fin 6) 4 (Fin.last 5) = Fin.last 5 from by decide]
      exact hlast
    | cast j =>
      have hj : Equiv.swap (2 : Fin 6) 4 j.castSucc = (gaugePerm.symm j).castSucc := by
        fin_cases j <;> decide
      rw [hj, simplexPoint_castSucc, simplexPoint_castSucc, gaugePermEquiv_apply]
  simp only [shift]
  rfl

open QED.Integration Feynman TwoLoop ChengWu in
private theorem gauge_simplex_integral (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) :
    ∫ x in i4Dom, i4SimplexIntegrand g x = ∫ x in simplexSet 5, gaugeForm g (simplexPoint x) := by
  rw [← measurePreserving_gaugeCoordsEquiv.setIntegral_preimage_emb
    gaugeCoordsEquiv.measurableEmbedding, preimage_gauge_i4Dom,
    ← setIntegral_congr_set (simplexSet_ae_eq_openSimplex (0 : Fin 5)),
    ← (measurePreserving_simplexSwap (3 : Fin 5)).setIntegral_preimage_emb
      (simplexSwapEquiv 3).measurableEmbedding, preimage_simplexSwap,
    ← measurePreserving_gaugePermEquiv.setIntegral_preimage_emb
      gaugePermEquiv.measurableEmbedding, preimage_gaugePerm]
  exact setIntegral_congr_fun (measurableSet_simplexSet _) fun x _ => gaugeChart_apply g x

open QED.Integration Feynman TwoLoop ChengWu in
private theorem gauge_simplex_integrableOn (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) :
    IntegrableOn (i4SimplexIntegrand g) i4Dom ↔
      IntegrableOn (fun x => gaugeForm g (simplexPoint x)) (simplexSet 5) := by
  rw [← measurePreserving_gaugeCoordsEquiv.integrableOn_comp_preimage
    gaugeCoordsEquiv.measurableEmbedding, preimage_gauge_i4Dom, IntegrableOn,
    ← Measure.restrict_congr_set (simplexSet_ae_eq_openSimplex (0 : Fin 5)), ← IntegrableOn,
    ← (measurePreserving_simplexSwap (3 : Fin 5)).integrableOn_comp_preimage
      (simplexSwapEquiv 3).measurableEmbedding, preimage_simplexSwap,
    ← measurePreserving_gaugePermEquiv.integrableOn_comp_preimage
      gaugePermEquiv.measurableEmbedding, preimage_gaugePerm]
  exact integrableOn_congr_fun (fun x _ => gaugeChart_apply g x) (measurableSet_simplexSet _)

/-! ### The triangle chart -/

private def gaugeBox : Set (Fin 5 → ℝ) :=
  {z | (∀ i, 0 < z i) ∧ z 0 < 1 ∧ z 1 < 1}

private def gaugeTri (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  z - (z 1 * z 0) • Pi.single 0 1

private theorem gaugeTri_apply (z : Fin 5 → ℝ) (i : Fin 5) :
    gaugeTri z i = if i = 0 then (1 - z 1) * z 0 else z i := by
  by_cases h : i = 0
  · subst i
    simp [gaugeTri]; ring
  · simp [gaugeTri, h]

private noncomputable def gaugeTriDeriv (z : Fin 5 → ℝ) :
    (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  ContinuousLinearMap.id ℝ _ -
    (z 1 • (ContinuousLinearMap.proj 0 : (Fin 5 → ℝ) →L[ℝ] ℝ) +
      z 0 • (ContinuousLinearMap.proj 1 : (Fin 5 → ℝ) →L[ℝ] ℝ)).smulRight
      (Pi.single 0 1)

private theorem hasFDerivAt_gaugeTri (z : Fin 5 → ℝ) :
    HasFDerivAt gaugeTri (gaugeTriDeriv z) z := by
  have h₁ := (ContinuousLinearMap.proj 1 : (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h₀ := (ContinuousLinearMap.proj 0 : (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h := (hasFDerivAt_id z).sub ((h₁.mul h₀).smul_const
    (Pi.single (M := fun _ : Fin 5 => ℝ) 0 1))
  have he : gaugeTri = id -
      fun y : Fin 5 → ℝ => (y 1 * y 0) • Pi.single (M := fun _ : Fin 5 => ℝ) 0 1 := by
    funext x i
    rfl
  rw [he]
  simpa only [gaugeTriDeriv, ContinuousLinearMap.proj_apply, Pi.mul_apply] using h

private theorem det_gaugeTriDeriv (z : Fin 5 → ℝ) :
    (gaugeTriDeriv z).det = 1 - z 1 := by
  let u : Fin 5 → ℝ := Pi.single 0 1
  let v : Fin 5 → ℝ := fun j => -(z 1 * u j + z 0 * Pi.single (M := fun _ : Fin 5 => ℝ) 1 1 j)
  have hM : LinearMap.toMatrix' (gaugeTriDeriv z : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ)) =
      1 + Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) v := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    simp only [gaugeTriDeriv, ContinuousLinearMap.coe_coe]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> by_cases hj' : j = 1 <;>
      simp_all [u, v, Pi.single_apply, Matrix.mul_apply, Matrix.one_apply, eq_comm, sub_eq_add_neg]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', hM,
    Matrix.det_one_add_mul_comm, Matrix.det_fin_one]
  simp [u, v, Matrix.replicateRow_mul_replicateCol_apply, sub_eq_add_neg]

private theorem preimage_gaugeBox :
    gaugeCoordsEquiv ⁻¹' QED.ThreeLoopD.i2Dom = gaugeBox := by
  ext z
  simp [gaugeCoordsEquiv_apply, QED.ThreeLoopD.i2Dom, gaugeBox, Fin.forall_fin_succ]
  tauto

private theorem measurableSet_gaugeBox : MeasurableSet gaugeBox :=
  preimage_gaugeBox ▸ gaugeCoordsEquiv.measurable (measurableSet_Ioo.prod
    (measurableSet_Ioo.prod (measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi))))

open QED.TwoLoop.UnitXGraph in
private theorem image_gaugeTri :
    gaugeTri '' gaugeBox = cwSet ({0, 1} : Finset (Fin 5)) := by
  ext z
  simp only [mem_cwSet, Finset.sum_insert (by decide : (0 : Fin 5) ∉ ({1} : Finset (Fin 5))),
    Finset.sum_singleton]
  constructor
  · rintro ⟨w, ⟨hw, hx, hy⟩, rfl⟩
    have hy' := sub_pos.mpr hy
    refine ⟨fun i => ?_, ?_⟩
    · rw [gaugeTri_apply]
      split
      · exact mul_pos hy' (hw 0)
      · exact hw i
    · simp only [gaugeTri_apply, ite_true, ite_eq_right (by decide : (1 : Fin 5) ≠ 0)]
      linarith [mul_pos hy' (sub_pos.mpr hx)]
  · rintro ⟨hz, hs⟩
    have hz1 : z 1 < 1 := by linarith [hz 0]
    have hpos := sub_pos.mpr hz1
    refine ⟨Function.update z 0 (z 0 / (1 - z 1)), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i
      by_cases hi : i = 0
      · subst i; simpa using div_pos (hz 0) hpos
      · simpa [Function.update_of_ne hi] using hz i
    · rw [Function.update_self, div_lt_one hpos]
      linarith
    · simpa using hz1
    · ext i
      by_cases hi : i = 0
      · subst i
        simp [gaugeTri_apply, hpos.ne', mul_div_cancel₀]
      · simp [gaugeTri_apply, hi]

private theorem injOn_gaugeTri : InjOn gaugeTri gaugeBox := by
  intro x hx y _ h
  have hn (i : Fin 5) (hi : i ≠ 0) : x i = y i := by
    simpa only [gaugeTri_apply, ite_eq_right hi] using congrFun h i
  ext i
  by_cases hi : i = 0
  · subst i
    have h1 := hn 1 (by decide)
    have h0 := congrFun h 0
    simp only [gaugeTri_apply, ite_true, ← h1] at h0
    exact mul_left_cancel₀ (sub_pos.mpr hx.2.2).ne' h0
  · exact hn i hi

/-- On the box, the Jacobian-weighted Cheng–Wu integrand is the gauge integrand. -/
private theorem gaugeTri_eq (g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) {x : Fin 5 → ℝ}
    (hx : x ∈ gaugeBox) :
    |(gaugeTriDeriv x).det| • gaugeForm g (Fin.snoc (gaugeTri x)
      (1 - ∑ i ∈ ({0, 1} : Finset (Fin 5)), gaugeTri x i)) =
      i4GaugeIntegrand g (gaugeCoordsEquiv x) := by
  rw [det_gaugeTriDeriv, abs_of_pos (sub_pos.mpr hx.2.2), smul_eq_mul, gaugeCoordsEquiv_apply]
  simp only [i4GaugeIntegrand]
  congr 1
  simp only [gaugeForm]
  have hsnoc (w : Fin 5 → ℝ) (t : ℝ) (i : Fin 5) :
      Fin.snoc (α := fun _ : Fin 6 => ℝ) w t i.castSucc = w i :=
    Fin.snoc_castSucc (α := fun _ : Fin 6 => ℝ) t w i
  simp only [show (5 : Fin 6) = Fin.last 5 from rfl, Fin.snoc_last,
    show (0 : Fin 6) = (0 : Fin 5).castSucc from rfl,
    show (1 : Fin 6) = (1 : Fin 5).castSucc from rfl,
    show (2 : Fin 6) = (2 : Fin 5).castSucc from rfl,
    show (3 : Fin 6) = (3 : Fin 5).castSucc from rfl,
    show (4 : Fin 6) = (4 : Fin 5).castSucc from rfl, hsnoc,
    Finset.sum_insert (by decide : (0 : Fin 5) ∉ ({1} : Finset (Fin 5))), Finset.sum_singleton]
  simp only [gaugeTri_apply, ite_true, ite_eq_right (by decide : (1 : Fin 5) ≠ 0),
    ite_eq_right (by decide : (2 : Fin 5) ≠ 0), ite_eq_right (by decide : (3 : Fin 5) ≠ 0),
    ite_eq_right (by decide : (4 : Fin 5) ≠ 0)]
  congr 1
  ring

private theorem gaugeForm_smul {g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ∀ a b c l m n t : ℝ, 0 < a → 0 < b → 0 < c → 0 < l → 0 < m → 0 < n → 0 < t →
      g (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) = (t ^ 6)⁻¹ * g a b c l m n)
    (z : Fin 6 → ℝ) (hz : ∀ i, 0 < z i) (t : ℝ) (ht : 0 < t) :
    gaugeForm g (t • z) = (t ^ 6)⁻¹ • gaugeForm g z := by
  simp only [gaugeForm, Pi.smul_apply, smul_eq_mul]
  exact hg _ _ _ _ _ _ _ (hz 0) (hz 1) (hz 4) (hz 5) (hz 2) (hz 3) ht

open QED.Integration.Feynman QED.TwoLoop.UnitXGraph in
/-- **The shared Cheng–Wu gauge, integrals.** For `g` homogeneous of degree `-6` on the positive
orthant, the integral over the simplex chart equals the integral over the domain of I₂ with the
gauge `a + b + l = 1` and Jacobian `1 - w`. -/
theorem i4Gauge_integral {g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ∀ a b c l m n t : ℝ, 0 < a → 0 < b → 0 < c → 0 < l → 0 < m → 0 < n → 0 < t →
      g (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) = (t ^ 6)⁻¹ * g a b c l m n) :
    ∫ x in i4Dom, i4SimplexIntegrand g x =
      ∫ z in QED.ThreeLoopD.i2Dom, i4GaugeIntegrand g z := by
  rw [gauge_simplex_integral, integral_simplex_chengWuSet (by decide : 0 < 5)
    ({0, 1} : Finset (Fin 5)) (gaugeForm g) (gaugeForm_smul hg), ← image_gaugeTri,
    integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_gaugeBox
      (fun z _ => (hasFDerivAt_gaugeTri z).hasFDerivWithinAt) injOn_gaugeTri,
    ← measurePreserving_gaugeCoordsEquiv.setIntegral_preimage_emb
      gaugeCoordsEquiv.measurableEmbedding, preimage_gaugeBox]
  exact setIntegral_congr_fun measurableSet_gaugeBox fun x hx => gaugeTri_eq g hx

open QED.Integration.Feynman QED.TwoLoop.UnitXGraph in
/-- **The shared Cheng–Wu gauge, integrability.** -/
theorem i4Gauge_integrableOn_iff {g : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ∀ a b c l m n t : ℝ, 0 < a → 0 < b → 0 < c → 0 < l → 0 < m → 0 < n → 0 < t →
      g (t * a) (t * b) (t * c) (t * l) (t * m) (t * n) = (t ^ 6)⁻¹ * g a b c l m n) :
    IntegrableOn (i4SimplexIntegrand g) i4Dom ↔
      IntegrableOn (i4GaugeIntegrand g) QED.ThreeLoopD.i2Dom := by
  rw [gauge_simplex_integrableOn, integrableOn_simplex_chengWuSet_iff (by decide : 0 < 5)
    ({0, 1} : Finset (Fin 5)) (gaugeForm g) (gaugeForm_smul hg), ← image_gaugeTri,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_gaugeBox
      (fun z _ => (hasFDerivAt_gaugeTri z).hasFDerivWithinAt) injOn_gaugeTri,
    ← measurePreserving_gaugeCoordsEquiv.integrableOn_comp_preimage
      gaugeCoordsEquiv.measurableEmbedding, preimage_gaugeBox]
  exact integrableOn_congr_fun (fun x hx => gaugeTri_eq g hx) measurableSet_gaugeBox

end QED.ThreeLoopE

end
