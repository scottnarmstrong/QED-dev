/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEQTail
public import QED.ChainProof.SetCRegDispShellSlope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c): the closed tails `∫_w^∞ R` and `∫_w^∞ R(t)/t dt` of the dressed photon

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b4. With `A, B, U > 0` distinct
(the squared masses `m_γ², Λ², T m²`), `R(w) = w² D(w)²/(w + U)` and `Q(w) = w D(w)²/(w + U)`,
`D(w) = 1/(w + A) - 1/(w + B)`, so that `R = w Q`:

* `hasDerivAt_quadTailVP`: `∂_w quadTailVP = -Q(w)` where `w + A, w + B, w + U > 0`;
* `tendsto_quadTailVP_atTop`, `tendsto_bubTailVP_atTop`: both closed tails tend to `0`;
* `quadTailVP_nonneg`, `quadTailVP_le_at_zero`: `0 ≤ quadTailVP w ≤ quadTailVP 0` for `w ≥ 0`;
* `tendsto_photonTail_vp_atTop`: `∫_a^∞ R_T → 0`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitVPLink (photonD)

/-- The photon function divided by its argument: `Q(w) = w D(w)²/(w + U)`. -/
noncomputable def bubQ (A B U w : ℝ) : ℝ := w / (w + U) * (1 / (w + A) - 1 / (w + B)) ^ 2

theorem vpPhotonT_eq_mul_bubQ (m mγ Λ T w : ℝ) :
    vpPhotonT m mγ Λ T w = w * bubQ (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) w := by
  simp only [vpPhotonT, bubQ, photonD]
  ring

theorem bubQ_nonneg {A B U w : ℝ} (hU : 0 < U) (hw : 0 ≤ w) : 0 ≤ bubQ A B U w := by
  unfold bubQ
  have : 0 < w + U := by linarith
  positivity

section Closed

variable {A B U w : ℝ} (hAB : A ≠ B) (hAU : A ≠ U) (hBU : B ≠ U)

include hAB hAU hBU in
/-- The logarithms of `quadTailVP` have coefficients summing to `0`. -/
theorem quadCoef_sum :
    U * (A - B) ^ 2 / ((A - U) ^ 2 * (B - U) ^ 2) -
      (2 * A ^ 2 - A * U - B * U) / ((A - B) * (A - U) ^ 2) -
      (A * U - 2 * B ^ 2 + B * U) / ((A - B) * (B - U) ^ 2) = 0 := by
  have h1 : A - B ≠ 0 := sub_ne_zero.2 hAB
  have h2 : A - U ≠ 0 := sub_ne_zero.2 hAU
  have h3 : B - U ≠ 0 := sub_ne_zero.2 hBU
  field_simp
  ring

include hAB hAU hBU in
/-- **The derivative of the closed tail of `Q`.** -/
theorem hasDerivAt_quadTailVP (hA : 0 < w + A) (hB : 0 < w + B) (hU : 0 < w + U) :
    HasDerivAt (quadTailVP A B U) (-bubQ A B U w) w := by
  have h1 : A - B ≠ 0 := sub_ne_zero.2 hAB
  have h2 : A - U ≠ 0 := sub_ne_zero.2 hAU
  have h3 : B - U ≠ 0 := sub_ne_zero.2 hBU
  have lU := ((hasDerivAt_id w).add_const U).log hU.ne'
  have lA := ((hasDerivAt_id w).add_const A).log hA.ne'
  have lB := ((hasDerivAt_id w).add_const B).log hB.ne'
  have iA := ((hasDerivAt_id w).add_const A).inv hA.ne'
  have iB := ((hasDerivAt_id w).add_const B).inv hB.ne'
  have h := ((((lU.const_mul (U * (A - B) ^ 2 / ((A - U) ^ 2 * (B - U) ^ 2))).sub
    (lA.const_mul ((2 * A ^ 2 - A * U - B * U) / ((A - B) * (A - U) ^ 2)))).sub
    (lB.const_mul ((A * U - 2 * B ^ 2 + B * U) / ((A - B) * (B - U) ^ 2)))).add
    (iA.const_mul (A / (A - U)))).add (iB.const_mul (B / (B - U)))
  convert h using 1
  · funext v
    simp only [quadTailVP, id, Pi.add_apply, Pi.sub_apply, Pi.inv_apply, div_eq_mul_inv]
  · simp only [bubQ, id]
    field_simp
    ring

include hAB hAU hBU in
/-- **The closed tail of `Q` tends to `0`.** -/
theorem tendsto_quadTailVP_atTop : Tendsto (quadTailVP A B U) atTop (𝓝 0) := by
  have hs := quadCoef_sum hAB hAU hBU
  have e1 := (tendsto_log_sub_log 0 U B).const_mul
    (U * (A - B) ^ 2 / ((A - U) ^ 2 * (B - U) ^ 2))
  have e2 := (tendsto_log_sub_log 0 A B).const_mul
    ((2 * A ^ 2 - A * U - B * U) / ((A - B) * (A - U) ^ 2))
  have e3 := (tendsto_inv_add 0 A).const_mul (A / (A - U))
  have e4 := (tendsto_inv_add 0 B).const_mul (B / (B - U))
  have h := ((e1.sub e2).add e3).add e4
  simp only [mul_zero, sub_zero, add_zero, zero_add] at h
  refine h.congr' (Eventually.of_forall fun u => ?_)
  simp only [quadTailVP]
  linear_combination (-Real.log (u + B)) * hs

include hAB hAU hBU in
/-- **The closed tail of `R` tends to `0`.** -/
theorem tendsto_bubTailVP_atTop : Tendsto (bubTailVP A B U) atTop (𝓝 0) := by
  have hs := QED.ChainProof.SetCRegBubble.bubCoef_simple_sum hAB hAU hBU
  have e1 := (tendsto_log_sub_log 0 U B).const_mul
    (QED.ChainProof.SetCRegBubble.bubCoefC A B U)
  have e2 := (tendsto_log_sub_log 0 A B).const_mul
    (QED.ChainProof.SetCRegBubble.bubCoefA A B U)
  have e3 := (tendsto_inv_add 0 A).const_mul (QED.ChainProof.SetCRegBubble.bubCoefA2 A U)
  have e4 := (tendsto_inv_add 0 B).const_mul (QED.ChainProof.SetCRegBubble.bubCoefB2 B U)
  have h := (((e1.add e2).neg).add e3).add e4
  simp only [mul_zero, add_zero, neg_zero, zero_add] at h
  refine h.congr' (Eventually.of_forall fun u => ?_)
  simp only [bubTailVP, div_eq_mul_inv]
  linear_combination (Real.log (u + B)) * hs

include hAB hAU hBU in
/-- `quadTailVP` is antitone on `[0, ∞)`. -/
theorem antitoneOn_quadTailVP (hA : 0 < A) (hB : 0 < B) (hU : 0 < U) :
    AntitoneOn (quadTailVP A B U) (Ici 0) := by
  have hd : ∀ v ∈ Ici (0 : ℝ), HasDerivAt (quadTailVP A B U) (-bubQ A B U v) v :=
    fun v hv => hasDerivAt_quadTailVP hAB hAU hBU (by linarith [mem_Ici.1 hv])
      (by linarith [mem_Ici.1 hv]) (by linarith [mem_Ici.1 hv])
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
    (fun v hv => (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt)
    fun v hv => ?_
  rw [(hd v (interior_subset hv)).deriv]
  exact neg_nonpos.2 (bubQ_nonneg hU (interior_subset hv))

include hAB hAU hBU in
theorem quadTailVP_nonneg (hA : 0 < A) (hB : 0 < B) (hU : 0 < U) (hw : 0 ≤ w) :
    0 ≤ quadTailVP A B U w := by
  have hanti := antitoneOn_quadTailVP hAB hAU hBU hA hB hU
  refine le_of_tendsto (tendsto_quadTailVP_atTop hAB hAU hBU) ?_
  filter_upwards [eventually_ge_atTop w] with v hv
  exact hanti (mem_Ici.2 hw) (mem_Ici.2 (hw.trans hv)) hv

include hAB hAU hBU in
theorem quadTailVP_le_at_zero (hA : 0 < A) (hB : 0 < B) (hU : 0 < U) (hw : 0 ≤ w) :
    quadTailVP A B U w ≤ quadTailVP A B U 0 :=
  antitoneOn_quadTailVP hAB hAU hBU hA hB hU (mem_Ici.2 le_rfl) (mem_Ici.2 hw) hw

end Closed

/-- **The tail of the dressed photon tends to `0`.** -/
theorem tendsto_photonTail_vp_atTop {m mγ Λ T : ℝ} (hab : mγ ^ 2 ≠ Λ ^ 2)
    (hac : mγ ^ 2 ≠ T * m ^ 2) (hbc : Λ ^ 2 ≠ T * m ^ 2) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (hU : 0 < T * m ^ 2) :
    Tendsto (photonTail (vpPhotonT m mγ Λ T)) atTop (𝓝 0) := by
  refine (tendsto_bubTailVP_atTop hab hac hbc).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with w hw
  rw [photonTail_vpPhotonT_eq hab hac hbc (by positivity) (by positivity) (by positivity)]
  rfl

end QED.ChainProof.SetCRegDisp

end
