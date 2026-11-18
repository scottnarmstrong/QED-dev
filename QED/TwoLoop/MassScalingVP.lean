/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.MassScalingOpen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Mass scaling of the vacuum-polarization class value

For `s > 0`, `vpZero (massScale s P) = s⁵ · vpZero P` (`vpZero_massScale`). Each of the five
piece numerators `K (E₀ + m² E₂)`, `-K E₂ D⁰` of `VP` is homogeneous of degree `12` in the masses,
the external and the loop momenta (`vpPieceM_massScale`): the bubble coefficient
`K = (M₁² - m²)(M₂² - m²)` has degree `4`, the chain with the loop trace `E₀` degree `8`, and the
chain without it `E₂` degree `6`, compensated by `m²` or by a line denominator `D⁰`. With the
Pauli weights the projected numerator scales by `s¹⁷`, `V` by `s²`, and `s¹⁷ / (s²)⁶ = s⁵`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real

namespace QED.TwoLoop.MassScaling

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic castLoopMatrix lineDenom classVPMomenta)

/-! ### The chain of `VP` -/

theorem electronNumerator_zero_smul (s : ℝ) (k : Fin 4 → ℝ) :
    electronNumerator 0 (s • k) = (s : ℂ) • electronNumerator 0 k := by
  simpa using electronNumerator_smul s 0 k

theorem traceT_smul (a b : ℂ) (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    traceT (a • A) (b • B) = fun x y => a * b * traceT A B x y := by
  funext x y
  simp only [traceT, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem pvG_massScale (s : ℝ) (P : Params) (x y : Fin 4) :
    pvG (massScale s P) x y = (s : ℂ) ^ 2 * pvG P x y := by
  simp only [pvG, massScale_Λ, massScale_mγ]
  push_cast
  ring

theorem lowered_massScale (s : ℝ) (P : Params) (a : ℂ) (X : Fin 4 → Fin 4 → ℂ) :
    lowered (massScale s P) (fun x y => a * X x y) =
      fun ν ρ => (s : ℂ) ^ 4 * a * lowered P X ν ρ := by
  funext ν ρ
  simp only [lowered, pvG_massScale, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem chain_smul (D : Fin 4 → Fin 4 → ℂ) (c a b : ℂ) (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) :
    IsSpinLift.chain (fun ν ρ => c * D ν ρ) (a • A) (b • B) μ =
      (c * a * b) • IsSpinLift.chain D A B μ := by
  simp only [IsSpinLift.chain, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by congr 1; ring

theorem vpChainM_massScale (s : ℝ) (P : Params) (p kext k : Fin 4 → ℝ) (a : ℂ)
    (X : Fin 4 → Fin 4 → ℂ) (μ : Fin 4) :
    vpChainM (massScale s P) (s • p) (s • kext) (s • k) (fun x y => a * X x y) μ =
      ((s : ℂ) ^ 6 * a) • vpChainM P p kext k X μ := by
  have e1 : s • p + s • kext - s • k = s • (p + kext - k) := by
    rw [smul_sub, smul_add]
  have e2 : s • p - s • k = s • (p - k) := (smul_sub s p k).symm
  simp only [vpChainM, lowered_massScale, massScale_m, e1, e2, electronNumerator_smul,
    chain_smul]
  congr 1
  ring

theorem vpE0M_massScale (s : ℝ) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpE0M (massScale s P) (s • p) (s • p') μ (s • ℓ) = (s : ℂ) ^ 8 • vpE0M P p p' μ ℓ := by
  have e1 : (s • ℓ) 0 = s • ℓ 0 := rfl
  have e2 : -(s • ℓ) 1 = s • -ℓ 1 := by simp
  have e3 : s • ℓ 0 + s • -ℓ 1 = s • (ℓ 0 + -ℓ 1) := (smul_add s _ _).symm
  have e4 : s • p' - s • p = s • (p' - p) := (smul_sub s p' p).symm
  rw [vpE0M_eq, vpE0M_eq, e1, e2, e3, e4, electronNumerator_zero_smul, electronNumerator_zero_smul,
    traceT_smul, vpChainM_massScale, massScale_e, smul_smul, smul_smul]
  congr 1
  ring

theorem vpE2M_massScale (s : ℝ) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpE2M (massScale s P) (s • p) (s • p') μ (s • ℓ) = (s : ℂ) ^ 6 • vpE2M P p p' μ ℓ := by
  have e2 : -(s • ℓ) 1 = s • -ℓ 1 := by simp
  have e4 : s • p' - s • p = s • (p' - p) := (smul_sub s p' p).symm
  have h := vpChainM_massScale s P p (p' - p) (-ℓ 1) 1 (traceT 1 1) μ
  simp only [one_mul, mul_one] at h
  rw [vpE2M_eq, vpE2M_eq, e2, e4, h, massScale_e, smul_smul, smul_smul]
  congr 1
  ring

/-! ### The coefficients -/

theorem vpBubbleCoeff_massScale (s : ℝ) (P : Params) :
    vpBubbleCoeff (massScale s P) = (s : ℂ) ^ 4 * vpBubbleCoeff P := by
  simp only [vpBubbleCoeff, massScale_M₁, massScale_M₂, massScale_m]
  push_cast
  ring

theorem vpShapeMomenta_smul (t : Fin 4) (s : ℝ) (p p' : Fin 4 → ℝ) :
    vpShapeMomenta t (s • p) (s • p') = s • vpShapeMomenta t p p' := by
  funext i
  simp only [vpShapeMomenta, Pi.smul_apply]
  generalize vpShapeLines t i = j
  fin_cases j <;> simp [classVPMomenta]

theorem vpShapeMasses_massScale (s : ℝ) (P : Params) (t : Fin 4) :
    vpShapeMasses (massScale s P) t = s • vpShapeMasses P t := by
  funext i
  fin_cases t <;> fin_cases i <;> simp [vpShapeMasses]

theorem lineDenom_zero_smul {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (i : Fin (m + 1)) {s : ℝ} (hs : s ≠ 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom α (s • q) (s • M) 0 i (s • ℓ) = (s : ℂ) ^ 2 * lineDenom α q M 0 i ℓ := by
  have h := lineMomentum_smul α q i hs (s • ℓ)
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at h
  simp only [lineDenom, show (s • q) = fun k => s • q k from rfl, h, dot_smul, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  ring

theorem vpCoeff0_massScale (s : ℝ) (P : Params) (j : Fin 5) :
    vpCoeff0 (massScale s P) j = (s : ℂ) ^ 4 * vpCoeff0 P j := by
  simp only [vpCoeff0, vpBubbleCoeff_massScale]
  split_ifs <;> ring

theorem vpCoeff2_massScale {s : ℝ} (hs : s ≠ 0) (P : Params) (p p' : Fin 4 → ℝ) (j : Fin 5)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpCoeff2 (massScale s P) (s • p) (s • p') j (s • ℓ) = (s : ℂ) ^ 6 * vpCoeff2 P p p' j ℓ := by
  simp only [vpCoeff2, vpBubbleCoeff_massScale, vpShapeMomenta_smul, vpShapeMasses_massScale,
    lineDenom_zero_smul _ _ _ _ hs, massScale_m]
  split_ifs <;> push_cast <;> ring

/-- **The piece numerators of `VP` are homogeneous of degree `12`.** -/
theorem vpPieceM_massScale {s : ℝ} (hs : s ≠ 0) (P : Params) (p p' : Fin 4 → ℝ) (j : Fin 5)
    (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpPieceM (massScale s P) (s • p) (s • p') j μ ℓ =
      (s : ℂ) ^ 12 • vpPieceM P p p' j μ (s⁻¹ • ℓ) := by
  have hℓ : ℓ = s • (s⁻¹ • ℓ) := by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
  conv_lhs => rw [hℓ]
  rw [vpPieceM_eq, vpPieceM_eq, vpCoeff0_massScale, vpCoeff2_massScale hs, vpE0M_massScale,
    vpE2M_massScale, smul_smul, smul_smul, smul_add, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> ring

/-! ### The class value -/

theorem vpF_massScale {s : ℝ} (hs : s ≠ 0) (P : Params) (p' : Fin 4 → ℝ) (k : Fin 5) (j : Idx) :
    vpF (massScale s P) (s • p') k j = fun ℓ => (s : ℂ) ^ 12 * vpF P p' k j (s⁻¹ • ℓ) := by
  funext ℓ
  simp only [vpF, massScale_m, restMomentum_smul, vpPieceM_massScale hs, Matrix.smul_apply,
    smul_eq_mul]

theorem exists_quartic_vpF (P : Params) (p' : Fin 4 → ℝ) (k : Fin 5) (j : Idx) :
    ∃ Q : LoopQuartic, Q.eval = vpF P p' k j := by
  have hF : vpF P p' k j = vpPieceNumer P (fun _ => p') (fun _ => restMomentum P.m)
      (fun _ => p' - restMomentum P.m) (fun _ => j.2.1) (fun _ => j.2.2) (fun _ => j.1) k :=
    funext fun ℓ => by simp only [vpF, vpPieceM, Matrix.of_apply]
  rw [hF]
  exact (isLoopPoly_vpPieceNumer P _ _ _ _ _ _ k).exists_loopQuartic

theorem vpNum_massScale {s : ℝ} (hs : s ≠ 0) (P : Params) (k : Fin 5) (x : Fin 9 → ℝ) (u : ℝ) :
    vpNum (massScale s P) k x u = (s : ℂ) ^ 17 * vpNum P k x u := by
  simp only [vpNum, massScale_m, curveMomentum_smul, restMomentum_smul, pauliWt_smul,
    vpShapeMomenta_smul, vpShapeMasses_massScale, vpF_massScale hs]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [paramNumOf_smul (exists_quartic_vpF P _ k j) _ hs]
  ring

theorem vpV_massScale (s : ℝ) (P : Params) (k : Fin 5) (x : Fin 9 → ℝ) :
    vpV (massScale s P) k x = s ^ 2 * vpV P k x := by
  simp only [vpV, massScale_m, restMomentum_smul, vpShapeMomenta_smul, vpShapeMasses_massScale,
    symanzikV_smul]

theorem secondCoeff_const_mul_vpNum (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (k : Fin 5) (x : Fin 9 → ℝ) (a : ℂ) :
    secondCoeff (fun u => a * vpNum P k x u) = a * secondCoeff (vpNum P k x) := by
  have hpn : vpNum P k x = projNum (vpCurve P hm hmγ hΛ hM₁ hM₂ k)
      (fun u (j : Idx) ℓ => vpPieceM P (restMomentum P.m) (curveMomentum P.m u) k j.1 ℓ
        j.2.1 j.2.2)
      (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
      x := rfl
  rw [hpn]
  exact secondCoeff_const_mul_projNum (vpCurve P hm hmγ hΛ hM₁ hM₂ k) (D := 8) (n := 4) (r := 4)
    (Dω := 8)
    (fun u (j : Idx) ℓ => vpPieceM P (restMomentum P.m) (curveMomentum P.m u) k j.1 ℓ j.2.1 j.2.2)
    (fun j => by
      have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
        (G := fun ℓ y => vpPieceNumer P (fun _ => y 0) (fun _ => restMomentum P.m)
          (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1) (fun _ => j.2.2) (fun _ => j.1)
          k ℓ)
        (fun ℓ => isLoopPoly_vpPieceNumer_out P _ _ _ _ k ℓ)
        (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
      refine h.congr fun ℓ u _ => ?_
      simp only [vpPieceM, Matrix.of_apply])
    (fun u _ j => exists_quartic_vpF P _ k j)
    (fun u (j : Idx) => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
    (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m) x a

/-- **Mass scaling of the `VP` class value**: `vpZero (massScale s P) = s⁵ vpZero P` for
`s > 0`. -/
theorem vpZero_massScale (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) {s : ℝ} (hs : 0 < s) :
    vpZero (massScale s P) = (s : ℂ) ^ 5 * vpZero P := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  unfold vpZero
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hN : vpNum (massScale s P) k x = fun u => (s : ℂ) ^ 17 * vpNum P k x u :=
    funext (vpNum_massScale hs.ne' P k x)
  simp only [hN, vpV_massScale]
  rw [secondCoeff_const_mul_vpNum P hm hmγ hΛ hM₁ hM₂ k x]
  have hV : ((s ^ 2 * vpV P k x : ℝ) : ℂ) ^ 6 = (s : ℂ) ^ 12 * ((vpV P k x : ℝ) : ℂ) ^ 6 := by
    push_cast
    ring
  rw [hV, show (s : ℂ) ^ 17 = (s : ℂ) ^ 12 * (s : ℂ) ^ 5 by ring, mul_assoc,
    mul_div_mul_left _ _ (pow_ne_zero 12 hs0), mul_div_assoc]

end QED.TwoLoop.MassScaling

end
