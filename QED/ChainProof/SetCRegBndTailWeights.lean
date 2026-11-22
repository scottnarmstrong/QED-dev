/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitSMasters
public import QED.TwoLoop.UnitSCLimitCMasters
public import QED.TwoLoop.UnitSCCloseIR

/-!
# Tail coefficients of the self-energy and corner masters

The radial logarithmic masters in QED/TwoLoop/UnitSCLimitSMasters.lean and
QED/TwoLoop/UnitSCLimitCMasters.lean give the weights computed here. Both
include the factor of two for the mirrored placements.
-/

@[expose] public section

open Set MeasureTheory
open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitSCClose

namespace QED.ChainProof.SetCRegDisp

private theorem integral_selfTail_weight_y (μ x : ℝ) (hM : 0 < ladderInnerMass 1 μ x) :
    (∫ Y in (0 : ℝ)..1, 2 *
      (selfK1 Y x * (x / ladderInnerMass 1 μ x) +
        selfK2 Y x * (x / ladderInnerMass 1 μ x) ^ 2)) =
      2 * vmIntegrand μ x + vkIntegrand μ x / 2 := by
  let w := x / ladderInnerMass 1 μ x
  let A := -(x * (x - 1)) * (2 * x + 1) * w +
    x ^ 2 * (x - 1) * (x - 1) * w ^ 2 / 2
  let B := -(x * (x - 1)) * (2 - 2 * x) * w +
    x ^ 2 * (x - 1) * (3 - x) * w ^ 2 / 2
  have hlin (Y : ℝ) : 2 * (selfK1 Y x * w + selfK2 Y x * w ^ 2) = A * Y + B := by
    dsimp [A, B, selfK1, selfK2]
    ring
  change (∫ Y in (0 : ℝ)..1, 2 * (selfK1 Y x * w + selfK2 Y x * w ^ 2)) = _
  simp_rw [hlin]
  have hi : IntervalIntegrable (fun Y : ℝ => A * Y) volume 0 1 :=
    (continuous_id.const_mul A).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const]
  dsimp [A, B, w, vmIntegrand, vkIntegrand]
  field_simp
  unfold ladderInnerMass
  ring

/-- In the inner self-energy masters, the two logarithmic weights sum to the
on-shell coefficient `-F₂/2 + 3 V_m/2`. -/
theorem integral_selfTail_weight {μ : ℝ} (hμ : 0 < μ) :
    (∫ x in (0 : ℝ)..1, ∫ Y in (0 : ℝ)..1, 2 *
      (selfK1 Y x * (x / ladderInnerMass 1 μ x) +
        selfK2 Y x * (x / ladderInnerMass 1 μ x) ^ 2)) =
      -oneLoopF2 1 μ / 2 + 3 * selfVm μ / 2 := by
  calc
    _ = ∫ x in (0 : ℝ)..1, 2 * vmIntegrand μ x + vkIntegrand μ x / 2 := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le zero_le_one] at hx
      exact integral_selfTail_weight_y μ x (ladderInnerMass_pos zero_lt_one hμ hx)
    _ = 2 * selfVm μ + selfVk μ / 2 := by
      rw [intervalIntegral.integral_add ((intervalIntegrable_vmIntegrand hμ).const_mul 2)
        ((intervalIntegrable_vkIntegrand hμ).div_const 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_div, selfVm, selfVk]
    _ = _ := by linarith [selfVk_add_selfVm_add_oneLoopF2 hμ]

/-- The constant corner weight integrated over the triangle and both reflections. -/
theorem integral_cornerTail_weight (μ : ℝ) :
    (2 * ∫ Y in (0 : ℝ)..1, ∫ _ in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1,
      cornerC0 x * (x / ladderInnerMass 1 μ x)) = oneLoopF2 1 μ / 2 := by
  have hl (x : ℝ) : cornerC0 x * (x / ladderInnerMass 1 μ x) =
      (x ^ 2 * (1 - x) * 1 ^ 2 / ladderInnerMass 1 μ x) / 2 := by
    unfold cornerC0
    ring
  unfold oneLoopF2
  simp_rw [hl, intervalIntegral.integral_div, intervalIntegral.integral_const]
  simp_rw [sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_mul_const, integral_id]
  ring

end QED.ChainProof.SetCRegDisp

end
