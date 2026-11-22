/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndCoincidence
public import QED.ChainProof.SetCRegKKScl
public import QED.TwoLoop.UnitLLinkCt
import QED.TwoLoop.MassScalingCounterterm

/-!
# The fixed on-shell terms of the real kernel

The charge term has the Phase 4 ladder subtraction coefficient of
`QED/TwoLoop/UnitLLinkCt.lean`. The exact photon partial fractions
identify its Pauli integral away from the two coincident masses.
Above threshold the longitudinal terms cancel by
`QED/ChainProof/SetCRegKKScl.lean`.
-/

@[expose] public section

open Complex
open scoped Real
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.OneLoop.VertexLimit (chargeA0 chargeZ isChargeNormalized_chargeZ)
open QED.TwoLoop.UnitLLink (ladderDeltaOne four_pi_sq_mul_eq_ladderDeltaOne)
open QED.TwoLoop.VPUnit (vpInsert_eq_integral regKernel)

private theorem chargeA0_eq_ladderDeltaOne {P : Params} (hm : 0 < P.m)
    {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    4 * π ^ 2 * (-chargeA0 P.e P.m mγ Λ) =
      P.e ^ 2 * ladderDeltaOne 1 (mγ / P.m) (Λ / P.m) := by
  have hγ' := div_pos hmγ hm
  have hΛ' := div_pos hΛ hm
  have hch : QED.OneLoop.IsChargeNormalized 1
      (1 + -chargeA0 1 1 (mγ / P.m) (Λ / P.m)) 1 (mγ / P.m) (Λ / P.m)
      one_pos hγ' hΛ' := by
    simpa only [chargeZ, sub_eq_add_neg] using
      (isChargeNormalized_chargeZ (e := 1) one_pos hγ' hΛ')
  have hδ := four_pi_sq_mul_eq_ladderDeltaOne one_pos hγ' hΛ' hch
  have hs := QED.TwoLoop.MassScaling.chargeA0_mul (s := P.m⁻¹)
    (inv_ne_zero hm.ne') 1 P.m mγ Λ
  rw [inv_mul_cancel₀ hm.ne', ← div_eq_inv_mul, ← div_eq_inv_mul] at hs
  rw [QED.TwoLoop.Scaling.chargeA0_eq P.e, ← hs, ← hδ]
  ring

/-- The normalized charge term has the ordinary ladder on-shell coefficient
times the integral of the dressed one-loop Pauli kernel. -/
theorem normalized_cbVPKer_eq_ladderDeltaOne {P : Params} (he : P.e ≠ 0)
    (hm : 0 < P.m) {mγ Λ T : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ) (hT : 0 < T)
    (hγT : (mγ / P.m) ^ 2 ≠ T) (hΛT : (Λ / P.m) ^ 2 ≠ T) :
    64 * π ^ 6 / P.e ^ 6 * ((1 / I) * cbVPKer P mγ Λ T).re =
      ladderDeltaOne 1 (mγ / P.m) (Λ / P.m) *
        ∫ x in (0 : ℝ)..1, regKernel T ((mγ / P.m) ^ 2) ((Λ / P.m) ^ 2) x := by
  have hg : 0 < mγ / P.m := div_pos hmγ hm
  have hL : 0 < Λ / P.m := div_pos (hmγ.trans hΛ) hm
  have hsq : (mγ / P.m) ^ 2 ≠ (Λ / P.m) ^ 2 :=
    (pow_lt_pow_left₀ (div_lt_div_of_pos_right hΛ hm) hg.le two_ne_zero).ne
  have hA := chargeA0_eq_ladderDeltaOne (P := P) hm hmγ (hmγ.trans hΛ)
  unfold cbVPKer
  rw [vpInsert_eq_integral (pow_pos hg _) (pow_pos hL _) hT hγT.symm hΛT.symm hsq]
  have er (A F : ℝ) : ((1 / I) * (-(A : ℂ) * I * (F : ℂ))).re = -A * F := by
    rw [show (1 / I) * (-(A : ℂ) * I * (F : ℂ)) = -(A : ℂ) * (F : ℂ) by
      rw [one_div, inv_I]
      linear_combination (A : ℂ) * (F : ℂ) * I_mul_I]
    simp only [← ofReal_neg, ← ofReal_mul, ofReal_re]
  rw [er]
  calc
    _ = (4 * π ^ 2 * -chargeA0 P.e P.m mγ Λ / P.e ^ 2) *
          ∫ x in (0 : ℝ)..1, regKernel T ((mγ / P.m) ^ 2) ((Λ / P.m) ^ 2) x := by
      field_simp [he, Real.pi_ne_zero]
      ring
    _ = _ := by rw [hA, mul_div_cancel_left₀ _ (pow_ne_zero _ he)]

/-- The actual above-threshold real kernel with its two fixed on-shell
counterterm terms written explicitly. -/
theorem setCKerRe_eq_feyn_ladderDeltaOne {P : Params} (he : P.e ≠ 0)
    (hm : 0 < P.m) {mγ Λ T : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ) (hT : 4 ≤ T)
    (hγT : (mγ / P.m) ^ 2 ≠ T) (hΛT : (Λ / P.m) ^ 2 ≠ T) :
    setCKerRe P (uBD P) mγ Λ T =
      kerRe P (uBDT P) (fun _ _ _ _ => 0) (uSF P) mγ Λ T +
        ladderDeltaOne 1 (mγ / P.m) (Λ / P.m) *
          (∫ x in (0 : ℝ)..1, regKernel T ((mγ / P.m) ^ 2) ((Λ / P.m) ^ 2) x) -
        8 * π ^ 2 / P.e ^ 2 * cb01B P mγ Λ *
          vpInsertW T ((mγ / P.m) ^ 2) ((Λ / P.m) ^ 2) := by
  rw [setCKerRe_eq_feyn_ge he hm (isKKCancelGe P he hm) hmγ hΛ hT]
  rw [← normalized_cbVPKer_eq_ladderDeltaOne he hm hmγ hΛ (by linarith) hγT hΛT]
  unfold kerRe
  rw [sum_uCBC_eq]
  simp only [Finset.sum_const_zero, add_zero, mul_add, mul_sub, add_re, sub_re]
  have er (F : ℝ) : ((1 / I) * (2 * I * (F : ℂ))).re = 2 * F := by
    rw [show (1 / I) * (2 * I * (F : ℂ)) = 2 * (F : ℂ) by
      rw [one_div, inv_I]
      linear_combination (-2 : ℂ) * (F : ℂ) * I_mul_I]
    simp only [← ofReal_ofNat, ← ofReal_mul, ofReal_re]
  rw [er]
  field_simp [he, Real.pi_ne_zero]
  ring

end QED.ChainProof.SetCRegDisp

end
