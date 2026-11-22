/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDYA

/-!
# Set (a), stage D: the photon-mass integral of the elementary `VA` function

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). At a fixed node the photon
mass² `u` enters the inner `VA` function `ksDLin A b Y a₀ a₁` only through the slope `b`, which is
affine in `u`. This file integrates `ksDLin` in `b` in closed form, with the one transcendental
function

  `K(z) = ∫₀^z log(1 + t)/t dt`  (`= -Li₂(-z)`),

and records the inversion `K(z) + K(1/z) = log² z / 2 + 2 K(1)` that gives the large-`b`
behaviour (`K(1/z) ∈ [0, 1/z]`).

Main results:

* `ksUK`, `ksU_hasDerivAt_ksUK`, `ksU_ksUK_nonneg`, `ksU_ksUK_le`;
* `ksU_ksUK_inv`: `K z + K z⁻¹ = log z ^ 2 / 2 + 2 K 1` for `z > 0`;
* `ksUPhi`, `ksU_hasDerivAt_ksUPhi`: `∂_b ksUPhi A b Y a₀ a₁ = ksDLin A b Y a₀ a₁`;
* **`ksU_integral_ksDLin`**: `∫_{b₀}^{B} ksDLin A b Y a₀ a₁ db = ksUPhi(B) - ksUPhi(b₀)`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral Filter Topology

namespace QED.ChainProof.SetAKS

/-! ### The function `K` -/

/-- The integrand `log(1 + t)/t` of `K` (the value `0` at `t = 0` is irrelevant). -/
noncomputable def ksUKer (t : ℝ) : ℝ := Real.log (1 + t) / t

/-- `K(z) = ∫₀^z log(1 + t)/t dt`, i.e. `-Li₂(-z)`. -/
noncomputable def ksUK (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, ksUKer t

theorem ksU_measurable_ksUKer : Measurable ksUKer := by
  unfold ksUKer
  fun_prop

theorem ksU_ksUKer_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ksUKer t :=
  div_nonneg (Real.log_nonneg (by linarith)) ht

theorem ksU_ksUKer_le_one {t : ℝ} (ht : 0 ≤ t) : ksUKer t ≤ 1 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [ksUKer]
  rw [ksUKer, div_le_one ht]
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + t)
  linarith

theorem ksU_intervalIntegrable_ksUKer {z : ℝ} (hz : 0 ≤ z) :
    IntervalIntegrable ksUKer volume 0 z := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    ksU_measurable_ksUKer.aestronglyMeasurable ?_
  rw [uIoc_of_le hz]
  refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
  show ‖ksUKer t‖ ≤ 1
  rw [Real.norm_of_nonneg (ksU_ksUKer_nonneg ht.1.le)]
  exact ksU_ksUKer_le_one ht.1.le

theorem ksU_continuousAt_ksUKer {t : ℝ} (ht : 0 < t) : ContinuousAt ksUKer t := by
  unfold ksUKer
  exact ((continuousAt_const.add continuousAt_id).log
    (by change (1 : ℝ) + t ≠ 0; linarith)).div continuousAt_id ht.ne'

theorem ksU_hasDerivAt_ksUK {z : ℝ} (hz : 0 < z) : HasDerivAt ksUK (ksUKer z) z :=
  integral_hasDerivAt_right (ksU_intervalIntegrable_ksUKer hz.le)
    ksU_measurable_ksUKer.stronglyMeasurable.stronglyMeasurableAtFilter (ksU_continuousAt_ksUKer hz)

theorem ksU_ksUK_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ ksUK z :=
  intervalIntegral.integral_nonneg hz fun _ ht => ksU_ksUKer_nonneg ht.1

theorem ksU_ksUK_le {z : ℝ} (hz : 0 ≤ z) : ksUK z ≤ z := by
  have h := intervalIntegral.integral_mono_on hz (ksU_intervalIntegrable_ksUKer hz)
    (intervalIntegrable_const (c := (1 : ℝ))) fun t ht => ksU_ksUKer_le_one ht.1
  simpa [ksUK] using h

/-- **The inversion of `K`**: `K z + K z⁻¹ = log z ^ 2 / 2 + 2 K 1` for `z > 0`. -/
theorem ksU_ksUK_inv {z : ℝ} (hz : 0 < z) :
    ksUK z + ksUK z⁻¹ = Real.log z ^ 2 / 2 + 2 * ksUK 1 := by
  set f : ℝ → ℝ := fun z => ksUK z + ksUK z⁻¹ - Real.log z ^ 2 / 2 with hf
  have hd : ∀ z ∈ Ioi (0 : ℝ), HasDerivAt f 0 z := fun z hz => by
    have hz : (0 : ℝ) < z := hz
    have h1 := ksU_hasDerivAt_ksUK hz
    have h2 := (ksU_hasDerivAt_ksUK (inv_pos.2 hz)).comp z (hasDerivAt_inv hz.ne')
    have h3 := ((Real.hasDerivAt_log hz.ne').pow 2).div_const 2
    refine ((h1.add h2).sub h3).congr_deriv ?_
    simp only [ksUKer, Nat.cast_ofNat]
    have h1z : 0 < 1 + z := by linarith
    rw [show 1 + z⁻¹ = (1 + z) / z by field_simp; ring, Real.log_div h1z.ne' hz.ne']
    field_simp
    ring
  have hc := (isOpen_Ioi (a := (0 : ℝ))).is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) (x := z) (y := 1) hz one_pos
  simp only [hf, inv_one, Real.log_one] at hc
  linarith

/-! ### The `b`-antiderivative of `ksDLin` -/

/-- **The `b`-antiderivative of `ksDLin`**, with `L = log((A + bY)/A)`:
`a₀ (L/b + (Y/A) log(A + bY)) + 2a₁ (-A L/b - Y log(A + bY) + Y K(bY/A))`. -/
noncomputable def ksUPhi (A b Y a₀ a₁ : ℝ) : ℝ :=
  a₀ * (Real.log ((A + b * Y) / A) / b + Y / A * Real.log (A + b * Y)) +
    2 * a₁ * (-(A * Real.log ((A + b * Y) / A) / b) - Y * Real.log (A + b * Y) +
      Y * ksUK (b * Y / A))

theorem ksU_hasDerivAt_ksUPhi {A b Y : ℝ} (a₀ a₁ : ℝ) (hA : 0 < A) (hb : 0 < b)
    (hY : 0 < Y) : HasDerivAt (fun b => ksUPhi A b Y a₀ a₁) (ksDLin A b Y a₀ a₁) b := by
  have hP : 0 < A + b * Y := by positivity
  have hlin : HasDerivAt (fun b : ℝ => A + b * Y) Y b := by
    simpa using ((hasDerivAt_id b).mul_const Y).const_add A
  have hL : HasDerivAt (fun b : ℝ => Real.log ((A + b * Y) / A)) (Y / (A + b * Y)) b := by
    have h := (hlin.div_const A).log (div_pos hP hA).ne'
    refine h.congr_deriv ?_
    field_simp
  have hlog : HasDerivAt (fun b : ℝ => Real.log (A + b * Y)) (Y / (A + b * Y)) b := hlin.log hP.ne'
  have hK : HasDerivAt (fun b : ℝ => ksUK (b * Y / A)) (ksUKer (b * Y / A) * (Y / A)) b := by
    have h := ((hasDerivAt_id b).mul_const Y).div_const A
    simp only [id, one_mul] at h
    exact (ksU_hasDerivAt_ksUK (by positivity)).comp b h
  have hb' : HasDerivAt (fun b : ℝ => b) 1 b := hasDerivAt_id' b
  have h := ((((hL.div hb' hb.ne').add (hlog.const_mul (Y / A))).const_mul a₀).add
    ((((((hL.const_mul A).div hb' hb.ne').neg).sub (hlog.const_mul Y)).add
      (hK.const_mul Y)).const_mul (2 * a₁)))
  refine h.congr_deriv ?_
  have h1 : 1 + b * Y / A = (A + b * Y) / A := by field_simp
  simp only [ksDLin, ksUKer, h1]
  field_simp
  ring

/-- **The `b`-integral of `ksDLin`** in closed form. -/
theorem ksU_integral_ksDLin {A b₀ B Y : ℝ} (a₀ a₁ : ℝ) (hA : 0 < A) (hb₀ : 0 < b₀)
    (hB : b₀ ≤ B) (hY : 0 < Y) :
    ∫ b in b₀..B, ksDLin A b Y a₀ a₁ = ksUPhi A B Y a₀ a₁ - ksUPhi A b₀ Y a₀ a₁ := by
  have hpos : ∀ b ∈ uIcc b₀ B, 0 < b := fun b hb => by
    rw [uIcc_of_le hB] at hb
    exact hb₀.trans_le hb.1
  have hcont : ContinuousOn (fun b => ksDLin A b Y a₀ a₁) (uIcc b₀ B) := fun b hb => by
    have hb0 := hpos b hb
    have hP : 0 < A + b * Y := by positivity
    refine ContinuousAt.continuousWithinAt ?_
    have cL : ContinuousAt (fun b : ℝ => Real.log ((A + b * Y) / A)) b :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).div_const A).log
        (div_pos hP hA).ne'
    simp only [ksDLin]
    refine (continuousAt_const.mul ((continuousAt_const.div
      (continuousAt_id.mul continuousAt_const) (mul_pos hb0 hA).ne').sub
        (cL.div (continuousAt_id.pow 2) (pow_pos hb0 2).ne'))).add
      (continuousAt_const.mul ((((continuousAt_const.add (continuousAt_id.mul
        continuousAt_const)).mul cL).sub (continuousAt_id.mul continuousAt_const)).div
          (continuousAt_id.pow 2) (pow_pos hb0 2).ne'))
  exact integral_eq_sub_of_hasDerivAt
    (fun b hb => ksU_hasDerivAt_ksUPhi a₀ a₁ hA (hpos b hb) hY) hcont.intervalIntegrable

end QED.ChainProof.SetAKS

end
