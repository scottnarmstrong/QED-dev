/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndShell
public import QED.ChainProof.SetCRegBubblePF

/-!
# A uniform derivative bound for the dressed photon

The derivative of the merged rational function is controlled at all
positive spectral masses, including the heavy coincidence. This also
records two explicit coefficient bounds for the separated-pole regime.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace QED.ChainProof.SetCRegDisp

/-- The derivative of the merged photon, written without dividing by the photon value. -/
theorem hasDerivAt_vpPhotonT {m mγ Λ T s : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hs : 0 < s) :
    HasDerivAt (vpPhotonT m mγ Λ T)
      (vpPhotonT m mγ Λ T s *
        (2 * (mγ ^ 2 / (s + mγ ^ 2)) - 2 * (s / (s + Λ ^ 2)) -
          s / (s + T * m ^ 2)) / s) s := by
  let a := mγ ^ 2
  let b := Λ ^ 2
  let c := T * m ^ 2
  have ha : 0 < s + a := add_pos_of_pos_of_nonneg hs (sq_nonneg _)
  have hb : 0 < s + b := add_pos_of_pos_of_nonneg hs (sq_nonneg _)
  have hc : 0 < s + c := add_pos hs (mul_pos hT (sq_pos_of_pos hm))
  have ha' := (hasDerivAt_id s).div ((hasDerivAt_id s).add_const a) ha.ne'
  have hb' := ((hasDerivAt_id s).add_const b).pow 2
  have hc' := (hasDerivAt_id s).add_const c
  have hd := (hasDerivAt_const s ((b - a) ^ 2)).div (hc'.mul hb')
    (mul_ne_zero hc.ne' (pow_ne_zero 2 hb.ne'))
  have h := (ha'.pow 2).mul hd
  have h' := h.congr_of_eventuallyEq (f₁ := vpPhotonT m mγ Λ T) (by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    exact vpPhotonT_eq hmγ hΛ hT hm (le_of_lt hu))
  convert h' using 1
  rw [vpPhotonT_eq hmγ hΛ hT hm hs.le]
  change
    (s / (s + a)) ^ 2 * ((b - a) ^ 2 / ((s + c) * (s + b) ^ 2)) *
        (2 * (a / (s + a)) - 2 * (s / (s + b)) - s / (s + c)) / s =
      ((2 : ℕ) : ℝ) * (s / (s + a)) ^ (2 - 1 : ℕ) *
          ((1 * (s + a) - s * 1) / (s + a) ^ 2) *
          ((b - a) ^ 2 / ((s + c) * (s + b) ^ 2)) +
        (s / (s + a)) ^ 2 *
          ((0 * ((s + c) * (s + b) ^ 2) -
            (b - a) ^ 2 * (1 * (s + b) ^ 2 +
              (s + c) * (((2 : ℕ) : ℝ) * (s + b) ^ (2 - 1 : ℕ) * 1))) /
            ((s + c) * (s + b) ^ 2) ^ 2)
  simp only [show (2 - 1 : ℕ) = 1 by decide, pow_one, Nat.cast_ofNat]
  field_simp [ha.ne', hb.ne', hc.ne', hs.ne']
  ring

/-- The radial derivative costs at most three copies of the spectral propagator after
multiplying by the radial variable. -/
theorem mul_abs_deriv_vpPhotonT_le {m mγ Λ T s : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hs : 0 < s) :
    s * |deriv (vpPhotonT m mγ Λ T) s| ≤ 3 / (s + T * m ^ 2) := by
  have hΛ := hmγ.trans_le hreg
  have hR := vpPhotonT_nonneg hmγ hΛ hT hm hs.le
  let x := mγ ^ 2 / (s + mγ ^ 2)
  let y := s / (s + Λ ^ 2)
  let z := s / (s + T * m ^ 2)
  have hx : 0 ≤ x ∧ x ≤ 1 := ⟨by positivity,
    (div_le_one (by positivity)).2 (le_add_of_nonneg_left hs.le)⟩
  have hy : 0 ≤ y ∧ y ≤ 1 := ⟨by positivity,
    (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg Λ))⟩
  have hz : 0 ≤ z ∧ z ≤ 1 := ⟨by positivity,
    (div_le_one (by positivity)).2 (le_add_of_nonneg_right (by positivity))⟩
  have hk : |2 * x - 2 * y - z| ≤ 3 := abs_le.2 ⟨by linarith [hx.1, hy.2, hz.2],
    by linarith [hx.2, hy.1, hz.1]⟩
  rw [(hasDerivAt_vpPhotonT hm hmγ hΛ hT hs).deriv]
  change s * |vpPhotonT m mγ Λ T s * (2 * x - 2 * y - z) / s| ≤ _
  rw [abs_div, abs_mul, abs_of_pos hs, abs_of_nonneg hR, mul_div_cancel₀ _ hs.ne']
  calc
    vpPhotonT m mγ Λ T s * |2 * x - 2 * y - z| ≤ vpPhotonT m mγ Λ T s * 3 :=
      mul_le_mul_of_nonneg_left hk hR
    _ ≤ (1 / (s + T * m ^ 2)) * 3 :=
      mul_le_mul_of_nonneg_right (vpPhotonT_le_single hm hmγ hreg hT hs.le) (by norm_num)
    _ = _ := by ring

/-- Shifting a positive radial endpoint is bounded by the shift times the derivative bound
at the lower endpoint. -/
theorem abs_vpPhotonT_sub_le {m mγ Λ T u v : ℝ}
    (hm : 0 < m) (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T)
    (hu : 0 < u) (huv : u ≤ v) :
    |vpPhotonT m mγ Λ T v - vpPhotonT m mγ Λ T u| ≤
      3 / (u * (u + T * m ^ 2)) * (v - u) := by
  have hx₀ {x : ℝ} (hx : x ∈ Icc u v) : 0 < x := hu.trans_le hx.1
  have hd : ∀ x ∈ Icc u v, DifferentiableAt ℝ (vpPhotonT m mγ Λ T) x := fun x hx =>
    (hasDerivAt_vpPhotonT hm hmγ (hmγ.trans_le hreg) hT (hx₀ hx)).differentiableAt
  have hb : ∀ x ∈ Icc u v, ‖deriv (vpPhotonT m mγ Λ T) x‖ ≤ 3 / (u * (u + T * m ^ 2)) := by
    intro x hx
    have h := mul_abs_deriv_vpPhotonT_le hm hmγ hreg hT (hx₀ hx)
    have hx' : u + T * m ^ 2 ≤ x + T * m ^ 2 := add_le_add_left hx.1 _
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (3 / (x + T * m ^ 2)) / x := (le_div_iff₀ (hx₀ hx)).2 (by rwa [mul_comm])
      _ = 3 / (x * (x + T * m ^ 2)) := by rw [div_div, mul_comm x]
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul hx.1 hx' (by positivity) (hx₀ hx).le)
  have h := (convex_Icc (𝕜 := ℝ) u v).norm_image_sub_le_of_norm_deriv_le hd hb
    (left_mem_Icc.2 huv) (right_mem_Icc.2 huv)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] using h

/-- In the singular part of the inner ladder, the endpoint shift cancels the factor `1/h`.
The bound is uniform even as the mass on the undressed line tends to zero. -/
theorem abs_ladderSoft_endpoint_shift_le {mγ Λ T Y h : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hh : 0 < h) :
    |Y ^ 2 / h * (vpPhotonT 1 mγ Λ T (shellArg 1 Y + Y * h) -
      vpPhotonT 1 mγ Λ T (shellArg 1 Y))| ≤ 3 / T := by
  let A := shellArg 1 Y
  have hY' := sub_pos.2 hY.2
  have e : A = Y ^ 2 / (1 - Y) := by simp [A, shellArg, QED.TwoLoop.UnitVPLink.photonVar]
  have hA : 0 < A := e.symm ▸ div_pos (sq_pos_of_pos hY.1) hY'
  have hYh : 0 ≤ Y * h := mul_nonneg hY.1.le hh.le
  have hb := abs_vpPhotonT_sub_le one_pos hmγ hreg hT hA (le_add_of_nonneg_right hYh)
  simp only [one_pow, mul_one, add_sub_cancel_left] at hb
  rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg Y) hh.le)]
  calc
    _ ≤ Y ^ 2 / h * (3 / (A * (A + T)) * (Y * h)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 3 * (Y * (1 - Y)) / (A + T) := by
      have hEq := (eq_div_iff hY'.ne').1 e
      field_simp
      linear_combination -Y * hEq
    _ ≤ 3 / T := by
      have hw : Y * (1 - Y) ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul hY.2.le (by linarith [hY.1]) hY'.le zero_le_one
          _ = _ := one_mul _
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num))
        (by positivity)).trans (by
          rw [mul_one]
          exact div_le_div_of_nonneg_left (by norm_num) hT (le_add_of_nonneg_left hA.le))

/-- The scalar soft coefficient of the inner ladder is the same dressed Pauli integral
that occurs in the fixed vertex counterterm. -/
theorem integral_ladderSoft_coefficient_eq (mγ Λ T : ℝ) :
    (∫ Y in (0 : ℝ)..1, Y ^ 2 * vpPhotonT 1 mγ Λ T (shellArg 1 Y)) =
      ∫ Y in (0 : ℝ)..1, QED.TwoLoop.VPUnit.regKernel T (mγ ^ 2) (Λ ^ 2) Y := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [QED.TwoLoop.UnitVPLink.ae_ne_one] with Y hY _
  rw [QED.TwoLoop.UnitVPLink.regKernel_eq_photon hY]
  simp only [vpPhotonT, shellArg, one_pow, mul_one, QED.TwoLoop.UnitVPLink.photonD]
  ring

end QED.ChainProof.SetCRegDisp

namespace QED.ChainProof.SetCRegBubble

/-- In the separated regime the spectral coefficient of the simple pole is at most sixteen. -/
theorem bubCoefC_le_sixteen {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hac : a ≤ c / 2) (hcb : 2 * c ≤ b) : bubCoefC a b c ≤ 16 := by
  have hac' : 0 < c - a := by linarith
  have hbc' : 0 < b - c := by linarith
  have hx : 0 ≤ c / (c - a) := div_nonneg hc.le hac'.le
  have hy : 0 ≤ (b - a) / (b - c) := div_nonneg (by linarith) hbc'.le
  have hx' : c / (c - a) ≤ 2 := (div_le_iff₀ hac').2 (by linarith)
  have hy' : (b - a) / (b - c) ≤ 2 := (div_le_iff₀ hbc').2 (by linarith)
  have e : bubCoefC a b c = (c / (c - a)) ^ 2 * ((b - a) / (b - c)) ^ 2 := by
    unfold bubCoefC
    have hca : a - c ≠ 0 := sub_ne_zero.2 (by linarith : a < c).ne
    field_simp
    ring
  rw [e]
  exact (mul_le_mul (pow_le_pow_left₀ hx hx' 2) (pow_le_pow_left₀ hy hy' 2) (sq_nonneg _)
    (by positivity)).trans_eq (by norm_num)

/-- In the separated regime the heavy double pole has coefficient of magnitude at most `2b`. -/
theorem abs_bubCoefB2_le {b c : ℝ} (hc : 0 < c) (hcb : 2 * c ≤ b) :
    |bubCoefB2 b c| ≤ 2 * b := by
  have hb : 0 < b := by linarith
  have hbc : 0 < b - c := by linarith
  rw [bubCoefB2, abs_div, abs_neg, abs_of_nonneg (sq_nonneg b), abs_of_pos hbc,
    div_le_iff₀ hbc]
  nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr hcb)]

end QED.ChainProof.SetCRegBubble

end
