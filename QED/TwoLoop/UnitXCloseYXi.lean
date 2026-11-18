/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXCloseOuterInt
public import QED.TwoLoop.UnitXKernel
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The crossed-ladder unit in the variables `(Y, ξ)`

The substitution `z₂ = Y ξ`, `z₃ = Y (1 - ξ)` of section 4.5.1 of `docs/TWO-LOOP-UNITS.md`
(`yxiMap`, Jacobian `Y`) maps `(0, 1)²` onto the open triangle. With
`QED.TwoLoop.UnitXClose.integral_crossedZero_eq_phi`:

* `integrableOn_crossedPhi`: `Φ_X` is integrable on the triangle;
* `integral_triangle_eq_yxi`: `∫_{triangle} f = ∫₀¹ ∫₀¹ Y f(Y ξ, Y (1 - ξ)) dξ dY` for `f`
  integrable on the triangle;
* `xUnitLimit_of_kernel`: **the X link reduces to the `ξ`-integration** (step 4.5.2): if for almost
  every `Y ∈ (0, 1)`, `∫₀¹ Y Φ_X(Y ξ, Y (1 - ξ)) dξ = K_X(Y)` (`crossedKernel`, eq. (4.7)), then
  `XUnitLimit`, by `QED.TwoLoop.Units.crossedUnit_value`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.TwoLoop.UnitXClose

open QED.TwoLoop.UnitXGraph
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The substitution -/

/-- `(Y, ξ) ↦ (Y ξ, Y - Y ξ)`. -/
def yxiMap (x : ℝ × ℝ) : ℝ × ℝ := (x.1 * x.2, x.1 - x.1 * x.2)

/-- The derivative of `yxiMap`. -/
noncomputable def yxiDeriv (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (x.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + x.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ -
      (x.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + x.2 • ContinuousLinearMap.fst ℝ ℝ ℝ))

theorem hasFDerivAt_yxiMap (x : ℝ × ℝ) : HasFDerivAt yxiMap (yxiDeriv x) x := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).mul (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
  have h2 := (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).sub h1
  exact h1.prodMk h2

theorem det_yxiDeriv (x : ℝ × ℝ) : (yxiDeriv x).det = -x.1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, yxiDeriv]
  ring

/-- The unit square `(0, 1)²`. -/
def unitSquare : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1

theorem measurableSet_unitSquare : MeasurableSet unitSquare :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem image_yxiMap : yxiMap '' unitSquare = innerTriangle := by
  ext p
  simp only [mem_image, unitSquare, mem_prod, mem_Ioo, innerTriangle, mem_ofPred_eq, yxiMap,
    Prod.ext_iff]
  constructor
  · rintro ⟨x, ⟨⟨h1, h2⟩, h3, h4⟩, e1, e2⟩
    rw [← e1, ← e2]
    refine ⟨by positivity, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(p.1 + p.2, p.1 / (p.1 + p.2)), ⟨⟨by positivity, h3⟩, by positivity, ?_⟩, ?_, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · field_simp
    · field_simp; ring

theorem injOn_yxiMap : InjOn yxiMap unitSquare := by
  rintro ⟨Y, ξ⟩ ⟨⟨hY, -⟩, -⟩ ⟨Y', ξ'⟩ ⟨⟨hY', -⟩, -⟩ h
  simp only [yxiMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hYY : Y = Y' := by linarith
  subst hYY
  exact Prod.ext rfl (mul_left_cancel₀ hY.ne' h1)

theorem abs_det_yxiDeriv {x : ℝ × ℝ} (hx : x ∈ unitSquare) : |(yxiDeriv x).det| = x.1 := by
  rw [det_yxiDeriv, abs_neg, abs_of_pos hx.1.1]

/-- **Integrability in `(Y, ξ)`.** -/
theorem integrableOn_triangle_iff (f : ℝ × ℝ → ℝ) :
    IntegrableOn f innerTriangle ↔ IntegrableOn (fun x => x.1 * f (yxiMap x)) unitSquare := by
  rw [← image_yxiMap, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    measurableSet_unitSquare (fun x _ => (hasFDerivAt_yxiMap x).hasFDerivWithinAt)
    injOn_yxiMap f]
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_unitSquare
  rw [abs_det_yxiDeriv hx, smul_eq_mul]

/-- **The substitution `(z₂, z₃) = (Y ξ, Y (1 - ξ))`.** -/
theorem integral_triangle_eq_yxi {f : ℝ × ℝ → ℝ} (hf : IntegrableOn f innerTriangle) :
    ∫ p in innerTriangle, f p =
      ∫ Y in Ioo (0 : ℝ) 1, ∫ ξ in Ioo (0 : ℝ) 1, Y * f (Y * ξ, Y * (1 - ξ)) := by
  have hint := (integrableOn_triangle_iff f).mp hf
  rw [← image_yxiMap, integral_image_eq_integral_abs_det_fderiv_smul volume
    measurableSet_unitSquare (fun x _ => (hasFDerivAt_yxiMap x).hasFDerivWithinAt)
    injOn_yxiMap f]
  rw [setIntegral_congr_fun measurableSet_unitSquare (g := fun x => x.1 * f (yxiMap x))
    (fun x hx => by rw [abs_det_yxiDeriv hx, smul_eq_mul])]
  rw [unitSquare, Measure.volume_eq_prod] at *
  rw [setIntegral_prod _ hint]
  refine setIntegral_congr_fun measurableSet_Ioo fun Y _ => ?_
  refine setIntegral_congr_fun measurableSet_Ioo fun ξ _ => ?_
  simp only [yxiMap]
  ring_nf

/-! ### `Φ_X` is integrable on the triangle -/

theorem ae_iterated_eq_crossedPhi
    (hI : IntegrableOn (fun y => crossedZero (simplexPoint y)) (simplexSet 4)) :
    (fun p : ℝ × ℝ => ∫ A in Ioi (0 : ℝ), ∫ a in Ioi (0 : ℝ),
        crossedTerm 0 0 A p.1 p.2 a (1 - (p.1 + p.2))) =ᵐ[volume.restrict innerTriangle]
      fun p => crossedPhi p.1 p.2 := by
  filter_upwards [ae_integrableOn_inner hI, ae_ne_diag,
    ae_restrict_mem measurableSet_innerTriangle] with p hp hne hmem
  obtain ⟨h1, h2, h3⟩ := hmem
  have e : 1 - (p.1 + p.2) = 1 - p.1 - p.2 := by ring
  simp only [e] at hp ⊢
  exact iterated_crossedTerm_zero_eq h1 h2 (by linarith) hne hp.1 hp.2

/-- **`Φ_X` is integrable on the triangle.** -/
theorem integrableOn_crossedPhi :
    IntegrableOn (fun p : ℝ × ℝ => crossedPhi p.1 p.2) innerTriangle := by
  have hI := (tendsto_integral_crossedFour crossedDom).1
  have hH := integrableOn_crossedZeroH hI
  have hL := hH.integral_prod_left
  refine (hL.congr ?_).congr (ae_iterated_eq_crossedPhi hI)
  filter_upwards [hH.prod_right_ae] with p hp
  rw [← Measure.prod_restrict] at hp
  rw [← Measure.prod_restrict, integral_prod _ hp]
  rfl

/-! ### The reduction to the `ξ`-integration -/

/-- **The X link reduces to the `ξ`-integration of section 4.5.2**: if for almost every
`Y ∈ (0, 1)`, `∫₀¹ Y Φ_X(Y ξ, Y (1 - ξ)) dξ = K_X(Y)`, then `XUnitLimit`. -/
theorem xUnitLimit_of_kernel
    (hK : ∀ᵐ Y ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ ξ in Ioo (0 : ℝ) 1, Y * crossedPhi (Y * ξ) (Y * (1 - ξ)) =
        QED.TwoLoop.Units.crossedKernel Y) :
    QED.TwoLoop.HeadlineAssembly.XUnitLimit := by
  refine xUnitLimit_of_phi ?_
  rw [integral_triangle_eq_yxi (f := fun p => crossedPhi p.1 p.2) integrableOn_crossedPhi,
    integral_congr_ae hK, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
    zero_le_one, QED.TwoLoop.Units.crossedUnit_value, xValue]

end QED.TwoLoop.UnitXClose

end
