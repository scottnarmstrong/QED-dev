/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXScale
public import QED.ChainProof.SetCRegXIntegrand

/-!
# Mass dilation of the extended Pauli value

The dilation from `QED/ChainProof/SetCRegXScale.lean` passes through the
convergent second-coefficient quotient and through the simplex integral.
-/

public section

open Complex MeasureTheory

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.PauliZero QED.TwoLoop.ClassLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.MassScaling
open QED.ChainProof.SetCUnit QED.TwoLoop.LimitCovariance

variable {r : ℕ}

private theorem secondCoeff_const_mul_unitMPauliNum {c : Class5} (hc : c ∈ openClasses)
    (P : Params) (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) (x : Fin (r + 7) → ℝ) (d : ℂ) :
    let g := unitMPauliNum c P s κ (unitMMasses P.m a A b B cs) x
    secondCoeff (fun u => d * g u) = d * secondCoeff g := by
  let C := unitMCurve hc P hm hs hμ₀ hM hX
  let F := fun u (j : Idx) => openF c P (curveMomentum P.m u) j
  let ω := fun u (j : Idx) =>
    pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2
  change secondCoeff (fun u => d * projNum C F ω x u) = d * secondCoeff (projNum C F ω x)
  apply secondCoeff_const_mul_projNum C (D := 8) (n := 4) (r := 4) (Dω := 8)
  · intro j
    have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
      (G := fun ℓ y => twoLoopNorm * classNumeratorE c P (fun _ => y 0)
        (fun _ => restMomentum P.m) (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1)
        (fun _ => j.2.2) (fun _ => j.1) ℓ)
      (fun ℓ => (isLoopPoly_classNumeratorE_out hc P _ _ _ _ ℓ).const_mul _)
      (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
    refine h.congr fun ℓ u _ => ?_
    simp only [F, openF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]
  · exact fun u _ j => exists_quartic_openF hc P _ j
  · exact fun j => isUPoly_pauliWt P.m j
  · exact sum_pauliWt_zero P.m

/-- The projected Pauli value scales with the numerator degree less twice the
power of the second Symanzik function. -/
theorem unitMPauliZero_massScale {c : Class5} (hc : c ∈ openClasses)
    (P : Params) (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) {t : ℝ} (ht : t ≠ 0) :
    unitMPauliZero c (massScale t P) s κ (t • unitMMasses P.m a A b B cs) =
      ((t : ℂ) ^ 13 / ((t : ℂ) ^ 2) ^ (r + 4)) *
        unitMPauliZero c P s κ (unitMMasses P.m a A b B cs) := by
  unfold unitMPauliZero
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hN : unitMPauliNum c (massScale t P) s κ (t • unitMMasses P.m a A b B cs) x =
      fun u => (t : ℂ) ^ 13 * unitMPauliNum c P s κ (unitMMasses P.m a A b B cs) x u :=
    funext fun u => unitMPauliNum_massScale hc P s κ _ x u ht
  dsimp only
  rw [hN, secondCoeff_const_mul_unitMPauliNum hc P hm hs hμ₀ hM hX x, unitMV0_massScale]
  push_cast
  simp only [mul_pow, div_eq_mul_inv, mul_inv]
  ring

section Charge

open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitLGraph

private theorem unitMPauliNum_X_chargeOne (P : Params) (s : Fin 8)
    (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ) (u : ℝ) :
    unitMPauliNum .X P s (fun _ => 1) M x u =
      (P.e : ℂ) ^ 5 * unitMPauliNum .X { P with e := 1 } s (fun _ => 1) M x u := by
  let P' := { P with e := 1 }
  have hc : ladderConst P = (P.e : ℂ) ^ 5 * ladderConst P' := by
    simp only [ladderConst, P', ofReal_one, mul_one]
    ring
  have hW (μ : Fin 4) (l : Fin 5 → Fin 4) : crossedWeight P' μ l = crossedWeight P μ l := rfl
  have hE (w : Fin 8 → ℝ) : crossedE P' w u = crossedE P w u := rfl
  have ht₁ (w : Fin 8 → ℝ) : crossedT1 P w u = (P.e : ℂ) ^ 5 * crossedT1 P' w u := by
    simp only [crossedT1, hc, hW, hE, P']
    ring
  have ht₂ (w : Fin 8 → ℝ) : crossedT2 P w u = (P.e : ℂ) ^ 5 * crossedT2 P' w u := by
    simp only [crossedT2, hc, hW, hE, P']
    ring
  have ht₃ (w : Fin 8 → ℝ) : crossedT3 P w u = (P.e : ℂ) ^ 5 * crossedT3 P' w u := by
    simp only [crossedT3, hc, hW, P']
    ring
  change _ = (P.e : ℂ) ^ 5 * unitMPauliNum .X P' s (fun _ => 1) M x u
  simp only [unitMPauliNum_X_eq_T, ht₁, ht₂, ht₃]
  have e : P'.m = P.m := rfl
  simp only [e]
  ring

/-- The crossed Pauli value carries the fifth power of the vertex charge. -/
theorem unitMPauliZero_X_chargeOne (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ}
    (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) :
    unitMPauliZero .X P s (fun _ => 1) (unitMMasses P.m a A b B cs) =
      (P.e : ℂ) ^ 5 *
        unitMPauliZero .X { P with e := 1 } s (fun _ => 1) (unitMMasses P.m a A b B cs) := by
  let P' := { P with e := 1 }
  have hc : Class5.X ∈ openClasses := by decide
  have hX : ExtraGe μ₀ (fun _ : Fin r => 1) cs := fun j => ⟨one_pos, le_rfl, hcs j⟩
  change _ = (P.e : ℂ) ^ 5 *
    unitMPauliZero .X P' s (fun _ => 1) (unitMMasses P'.m a A b B cs)
  unfold unitMPauliZero
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have hN : unitMPauliNum .X P s (fun _ => 1) (unitMMasses P.m a A b B cs) x =
      fun u => (P.e : ℂ) ^ 5 *
        unitMPauliNum .X P' s (fun _ => 1) (unitMMasses P'.m a A b B cs) x u :=
    funext (unitMPauliNum_X_chargeOne P s _ x)
  rw [hN, secondCoeff_const_mul_unitMPauliNum hc P' hm hs hμ₀ hM hX x]
  rw [show unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B cs) x =
    unitMV0 .X P' s (fun _ => 1) (unitMMasses P'.m a A b B cs) x from rfl, mul_div_assoc]

end Charge

end QED.ChainProof.SetCUnitM

end
