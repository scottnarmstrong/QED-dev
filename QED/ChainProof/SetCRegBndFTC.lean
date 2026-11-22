/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndDeriv
public import QED.ChainProof.SetCRegBndEndpoints
import QED.ChainProof.SetCRegBndRadial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Affine radial integration of the dressed photon derivative

The inner ladder derivative term and the linear radial weight in the
self-energy master need an endpoint evaluation and integration by parts,
respectively. The starting photon and derivative are those in
`QED/ChainProof/SetCRegBndDeriv.lean`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace QED.ChainProof.SetCRegDisp

private theorem abs_deriv_le_mul_vpPhotonT {mγ Λ T s : ℝ}
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hs : 0 < s) :
    |deriv (vpPhotonT 1 mγ Λ T) s| ≤ (3 / s) * vpPhotonT 1 mγ Λ T s := by
  rw [(hasDerivAt_vpPhotonT one_pos hmγ hΛ hT hs).deriv, abs_div, abs_mul,
    abs_of_pos hs, abs_of_nonneg (vpPhotonT_nonneg hmγ hΛ hT one_pos hs.le)]
  rw [mul_comm (3 / s), mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (vpPhotonT_nonneg hmγ hΛ hT one_pos hs.le)
  apply div_le_div_of_nonneg_right _ hs.le
  have h₁ : 0 ≤ mγ ^ 2 / (s + mγ ^ 2) ∧ mγ ^ 2 / (s + mγ ^ 2) ≤ 1 :=
    ⟨by positivity, (div_le_one (by positivity)).2 (le_add_of_nonneg_left hs.le)⟩
  have h₂ : 0 ≤ s / (s + Λ ^ 2) ∧ s / (s + Λ ^ 2) ≤ 1 :=
    ⟨by positivity, (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg Λ))⟩
  have h₃ : 0 ≤ s / (s + T * 1 ^ 2) ∧ s / (s + T * 1 ^ 2) ≤ 1 :=
    ⟨by positivity, (div_le_one (by positivity)).2 (le_add_of_nonneg_right (by positivity))⟩
  exact abs_le.2 ⟨by linarith only [h₁.1, h₂.2, h₃.2], by linarith only [h₁.2, h₂.1, h₃.1]⟩

private theorem hasDerivAt_affine_vpPhotonT {mγ Λ T A k z : ℝ}
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hs : 0 < A + k * z) :
    HasDerivAt (fun u => vpPhotonT 1 mγ Λ T (A + k * u))
      (deriv (vpPhotonT 1 mγ Λ T) (A + k * z) * k) z := by
  have h := hasDerivAt_vpPhotonT one_pos hmγ hΛ hT hs
  have ha : HasDerivAt (fun u : ℝ => A + k * u) k z := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id z).const_mul k).const_add A
  rw [h.deriv]
  exact h.comp z ha

private theorem integrableOn_affine_vpPhotonT {mγ Λ T A k : ℝ}
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hA : 0 < A) (hk : 0 < k) :
    IntegrableOn (fun z => vpPhotonT 1 mγ Λ T (A + k * z)) (Ioi 0) :=
  (integrableOn_Ioi_comp_mul_left_iff
    (fun z => vpPhotonT 1 mγ Λ T (A + z)) 0 hk).2
      (by simpa only [mul_zero] using integrableOn_vpPhotonT_shift hmγ hΛ hT one_pos hA.le)

private theorem integrableOn_mul_deriv_affine_vpPhotonT {mγ Λ T A k C : ℝ}
    (hmγ : 0 < mγ) (hΛ : 0 < Λ) (hT : 0 < T) (hA : 0 < A) (hk : 0 < k)
    {w : ℝ → ℝ} (hw : Measurable w)
    (hB : ∀ z ∈ Ioi (0 : ℝ), |w z| * (3 / (A + k * z)) ≤ C) :
    IntegrableOn (fun z => w z * deriv (vpPhotonT 1 mγ Λ T) (A + k * z)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_affine_vpPhotonT hmγ hΛ hT hA hk).const_mul C)
    ((hw.mul ((measurable_deriv _).comp
      (measurable_const.add (measurable_const.mul measurable_id)))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hs : 0 < A + k * z := add_pos hA (mul_pos hk hz)
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |w z| * (3 / (A + k * z) * vpPhotonT 1 mγ Λ T (A + k * z)) :=
      mul_le_mul_of_nonneg_left (abs_deriv_le_mul_vpPhotonT hmγ hΛ hT hs) (abs_nonneg _)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hB z hz) (vpPhotonT_nonneg hmγ hΛ hT one_pos hs.le)

private theorem tendsto_affine_vpPhotonT {mγ Λ T A k : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hA : 0 < A) (hk : 0 < k) :
    Tendsto (fun z => vpPhotonT 1 mγ Λ T (A + k * z)) atTop (𝓝 0) := by
  have ht := tendsto_atTop_add_const_left atTop (A + T * 1 ^ 2)
    ((tendsto_mul_const_atTop_of_pos hk).2 tendsto_id)
  have ht' : Tendsto (fun z : ℝ => 1 / (A + k * z + T * 1 ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, add_right_comm A, one_div, mul_comm k]
      using tendsto_inv_atTop_zero.comp ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht' ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact vpPhotonT_nonneg hmγ (hmγ.trans_le hreg) hT one_pos
      (add_nonneg hA.le (mul_nonneg hk.le hz))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact vpPhotonT_le_single one_pos hmγ hreg hT (add_nonneg hA.le (mul_nonneg hk.le hz))

/-- The integral of the affine radial derivative equals the negative endpoint value. -/
theorem integral_Ioi_deriv_vpPhotonT {mγ Λ T A k : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hA : 0 < A) (hk : 0 < k) :
    IntegrableOn (fun z => deriv (vpPhotonT 1 mγ Λ T) (A + k * z)) (Ioi 0) ∧
    (∫ z in Ioi (0 : ℝ), deriv (vpPhotonT 1 mγ Λ T) (A + k * z)) =
      -vpPhotonT 1 mγ Λ T A / k := by
  have hI := integrableOn_mul_deriv_affine_vpPhotonT hmγ (hmγ.trans_le hreg) hT hA hk
    (w := fun _ => 1) (C := 3 / A) measurable_const (by
      intro z hz
      rw [abs_one, one_mul]
      exact div_le_div_of_nonneg_left (by norm_num) hA
        (le_add_of_nonneg_right (mul_nonneg hk.le (le_of_lt hz))))
  simp only [one_mul] at hI
  refine ⟨hI, (eq_div_iff hk.ne').2 ?_⟩
  rw [← integral_mul_const]
  have hd (z : ℝ) (hz : z ∈ Ici 0) := hasDerivAt_affine_vpPhotonT
    hmγ (hmγ.trans_le hreg) hT (add_pos_of_pos_of_nonneg hA (mul_nonneg hk.le hz))
  simpa only [mul_zero, add_zero, zero_sub] using
    integral_Ioi_of_hasDerivAt_of_tendsto' hd (hI.mul_const k)
      (tendsto_affine_vpPhotonT hmγ hreg hT hA hk)

/-- A linear radial weight integrates by parts to the negative affine photon tail. -/
theorem integral_Ioi_mul_deriv_vpPhotonT {mγ Λ T A k : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hA : 0 < A) (hk : 0 < k) :
    IntegrableOn (fun z => z * deriv (vpPhotonT 1 mγ Λ T) (A + k * z)) (Ioi 0) ∧
    (∫ z in Ioi (0 : ℝ), z * deriv (vpPhotonT 1 mγ Λ T) (A + k * z)) =
      -photonTail (vpPhotonT 1 mγ Λ T) A / k ^ 2 := by
  have hΛ := hmγ.trans_le hreg
  let R := vpPhotonT 1 mγ Λ T
  let F := fun z => R (A + k * z)
  let C := photonK mγ Λ / (T * (1 : ℝ) ^ 2)
  have hI := integrableOn_mul_deriv_affine_vpPhotonT hmγ hΛ hT hA hk
    (w := id) (C := 3 / k) measurable_id (by
      intro z (hz : 0 < z)
      rw [id_eq, abs_of_pos hz]
      apply (le_div_iff₀ hk).2
      rw [show z * (3 / (A + k * z)) * k = 3 * (k * z) / (A + k * z) by ring]
      exact (div_le_iff₀ (by positivity)).2 (by linarith only [hA]))
  have hF := integrableOn_affine_vpPhotonT hmγ hΛ hT hA hk
  have hZero : Tendsto (fun z => z * F z) (𝓝[>] 0) (𝓝 0) := by
    have hd := hasDerivAt_affine_vpPhotonT (z := 0) hmγ hΛ hT
      (show 0 < A + k * 0 by simpa only [mul_zero, add_zero] using hA)
    have hC : ContinuousAt (fun z => z * F z) 0 := continuousAt_id.mul hd.continuousAt
    simpa only [zero_mul] using hC.tendsto.mono_left nhdsWithin_le_nhds
  have hTop : Tendsto (fun z => z * F z) atTop (𝓝 0) := by
    have ht := tendsto_atTop_add_const_left atTop A
      ((tendsto_mul_const_atTop_of_pos hk).2 tendsto_id)
    have ht' : Tendsto (fun z : ℝ => (C / k) * (A + k * z)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, mul_zero, mul_comm k]
        using (tendsto_inv_atTop_zero.comp ht).const_mul (C / k)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht' ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
      exact mul_nonneg hz (vpPhotonT_nonneg hmγ hΛ hT one_pos
        (add_nonneg hA.le (mul_nonneg hk.le hz)))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
      let s := A + k * z
      have hs : 0 < s := add_pos_of_pos_of_nonneg hA (mul_nonneg hk.le hz)
      have hC : 0 ≤ C := div_nonneg (photonK_nonneg _ _) (by positivity)
      calc
        z * F z ≤ z * (C * (1 + s ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (vpPhotonT_le hmγ hΛ hT one_pos hs.le) hz
        _ ≤ (s / k) * (C * (s ^ 2)⁻¹) := by
          apply mul_le_mul
          · exact (le_div_iff₀ hk).2 (by dsimp [s]; linarith only [hA])
          · exact mul_le_mul_of_nonneg_left
              (inv_anti₀ (sq_pos_of_pos hs) (le_add_of_nonneg_left zero_le_one)) hC
          · positivity
          · positivity
        _ = _ := by change _ = C / k * s⁻¹; field_simp
  have e := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (u := id) (u' := fun _ => 1)
    (v := F) (v' := fun z => deriv R (A + k * z) * k)
    (fun z _ => hasDerivAt_id z)
    (fun z hz => hasDerivAt_affine_vpPhotonT hmγ hΛ hT (add_pos hA (mul_pos hk hz)))
    (by
      change Integrable (fun z => z * (deriv R (A + k * z) * k)) (volume.restrict (Ioi 0))
      simpa only [← mul_assoc, id_eq, R] using hI.mul_const k)
    (by
      change IntegrableOn (fun z => 1 * F z) (Ioi 0)
      simpa only [one_mul] using hF) hZero hTop
  simp only [id_eq, ← mul_assoc, integral_mul_const, sub_self, one_mul, zero_sub] at e
  have et := integral_affine_photon_tail R 1 A 0 hk one_pos
  simp only [div_one, one_div, one_mul, add_zero, mul_zero, mul_comm _ k] at et
  refine ⟨hI, (eq_div_iff (pow_ne_zero 2 hk.ne')).2 ?_⟩
  change (∫ z in Ioi (0 : ℝ), z * deriv R (A + k * z)) * k ^ 2 = -photonTail R A
  rw [pow_two, ← mul_assoc, e]
  change -(∫ z in Ioi (0 : ℝ), R (A + k * z)) * k = -photonTail R A
  rw [et]
  field_simp

/-- The derivative weighted by the original self-energy radial coordinate. -/
theorem integral_Ioi_add_mul_deriv_vpPhotonT {mγ Λ T A k : ℝ} (c : ℝ)
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hA : 0 < A) (hk : 0 < k) :
    IntegrableOn (fun z => (z + c) * deriv (vpPhotonT 1 mγ Λ T) (A + k * z)) (Ioi 0) ∧
    (∫ z in Ioi (0 : ℝ), (z + c) * deriv (vpPhotonT 1 mγ Λ T) (A + k * z)) =
      -photonTail (vpPhotonT 1 mγ Λ T) A / k ^ 2 - c * vpPhotonT 1 mγ Λ T A / k := by
  obtain ⟨hi, ei⟩ := integral_Ioi_deriv_vpPhotonT hmγ hreg hT hA hk
  obtain ⟨hj, ej⟩ := integral_Ioi_mul_deriv_vpPhotonT hmγ hreg hT hA hk
  have hci := hi.const_mul c
  simp only [add_mul]
  refine ⟨hj.add hci, ?_⟩
  rw [integral_add hj hci, integral_const_mul, ei, ej]
  ring

/-- The constant part of the singular ladder derivative, centered at the shell argument. -/
theorem abs_integral_ladderSoft_sub_endpoint_le {mγ Λ T Y x h : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T)
    (hY : Y ∈ Ioo 0 1) (hx : x ∈ Ioo 0 1) (hh : 0 < h) :
    let d := 1 - Y
    let U := shellArg 1 Y
    let A := U + Y * h
    let R := vpPhotonT 1 mγ Λ T
    let w := Y ^ 2 * (1 - x) ^ 3
    IntegrableOn (fun z => w / d * deriv R (A + (h / d) * z)) (Ioi 0) ∧
      |(∫ z in Ioi (0 : ℝ), w / d * deriv R (A + (h / d) * z)) + w / h * R U| ≤ 3 / T := by
  intro d U A R w
  have hd : 0 < d := sub_pos.2 hY.2
  have hU : 0 < U := by
    simpa only [U, shellArg, one_pow, one_mul, QED.TwoLoop.UnitVPLink.photonVar] using
      div_pos (sq_pos_of_pos hY.1) hd
  have hA : 0 < A := add_pos hU (mul_pos hY.1 hh)
  obtain ⟨hi, ei⟩ := integral_Ioi_deriv_vpPhotonT hmγ hreg hT hA (div_pos hh hd)
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, ei]
  have e : w / d * (-R A / (h / d)) + w / h * R U =
      -(1 - x) ^ 3 * (Y ^ 2 / h * (R A - R U)) := by
    dsimp only [w]
    field_simp
    ring
  rw [e, abs_mul, abs_neg]
  have hpow : 0 ≤ (1 - x) ^ 3 := pow_nonneg (sub_nonneg.mpr hx.2.le) _
  rw [abs_of_nonneg hpow]
  exact (mul_le_mul_of_nonneg_left (abs_ladderSoft_endpoint_shift_le hmγ hreg hT hY hh)
    hpow).trans
      (mul_le_of_le_one_left (by positivity)
        (pow_le_one₀ (sub_nonneg.mpr hx.2.le) (sub_le_self _ hx.1.le)))

open QED.TwoLoop.UnitLLink (ladderInnerMass)
open QED.TwoLoop.UnitSCLimit

/-- The leading self-energy pair after radial integration and subtraction of the zero tail. -/
theorem abs_integral_self_radial_leading_sub_le {mγ Λ T Y x : ℝ} (la : ℝ)
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T)
    (hY : Y ∈ Ioo 0 1) (hx : x ∈ Ioo 0 1) :
    let d := 1 - Y
    let c := Y * d
    let h := ladderInnerMass 1 la x / x
    let A := (Y ^ 2 + c * h) / d
    let W := (selfK1 Y x + selfK2 Y x / h) / h
    let R := vpPhotonT 1 mγ Λ T
    |(∫ z in Ioi (0 : ℝ), (selfK1 Y x / d) * R (A + (h / d) * z) -
      (selfK2 Y x / d ^ 2) * ((z + c) * deriv R (A + (h / d) * z))) -
      W * photonTail R 0| ≤ 15 / (√d * √T) := by
  intro d c h A W R
  have hd : 0 < d := sub_pos.mpr hY.2
  have hd₁ : d ≤ 1 := sub_le_self _ hY.1.le
  have hc : 0 < c := mul_pos hY.1 hd
  have hhx : x ≤ h := by
    apply (le_div_iff₀ hx.1).2
    unfold ladderInnerMass
    rw [one_pow, mul_one, ← sq]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hx.2.le) (sq_nonneg _))
  have hh := hx.1.trans_le hhx
  have hAY : Y ^ 2 ≤ A := by
    apply (le_div_iff₀ hd).2
    exact (mul_le_of_le_one_right (sq_nonneg Y) hd₁).trans
      (le_add_of_nonneg_right (mul_nonneg hc.le hh.le))
  have hA := (sq_pos_of_pos hY.1).trans_le hAY
  have hk := div_pos hh hd
  have hIR := integrableOn_affine_vpPhotonT hmγ (hmγ.trans_le hreg) hT hA hk
  obtain ⟨hID, eD⟩ := integral_Ioi_add_mul_deriv_vpPhotonT c hmγ hreg hT hA hk
  have eR :
      (∫ z in Ioi (0 : ℝ), selfK1 Y x / d * R (A + h / d * z)) =
        selfK1 Y x / h * photonTail R A := by
    have e (z : ℝ) : (Y ^ 2 + (z + c) * h) / d = A + h / d * z := by
      dsimp only [A]
      ring
    change _ = selfK1 Y x / h * photonTail R ((Y ^ 2 + c * h) / d)
    rw [← integral_affine_photon_tail R (selfK1 Y x) (Y ^ 2) c hh hd]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only [e])
  have eInt :
      (∫ z in Ioi (0 : ℝ), selfK1 Y x / d * R (A + h / d * z) -
        selfK2 Y x / d ^ 2 * ((z + c) * deriv R (A + h / d * z))) - W * photonTail R 0 =
      W * (photonTail R A - photonTail R 0) + selfK2 Y x * Y / h * R A := by
    rw [integral_sub (hIR.const_mul _) (hID.const_mul _), eR, integral_const_mul, eD]
    dsimp only [W, c]
    field_simp
    ring
  rw [eInt]
  have hK : |selfK2 Y x| ≤ h := by
    have hyx : 0 ≤ Y * x := mul_nonneg hY.1.le hx.1.le
    have hyx' : Y * x ≤ 1 :=
      (mul_le_of_le_one_right hY.1.le hx.2.le).trans hY.2.le
    have hb : |Y * x - Y - x + 3| ≤ 4 := abs_le.2
      ⟨by linarith only [hyx, hY.2, hx.2], by linarith only [hyx', hY.1, hx.1]⟩
    unfold selfK2
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x),
      abs_of_neg (sub_neg.mpr hx.2), abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc
      _ ≤ x ^ 2 * -(x - 1) * 4 / 4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb
          (mul_nonneg (sq_nonneg _) (neg_nonneg.mpr (sub_nonpos.mpr hx.2.le)))) (by norm_num)
      _ = x ^ 2 * (1 - x) := by ring
      _ ≤ x ^ 2 := mul_le_of_le_one_right (sq_nonneg _) (sub_le_self _ hx.1.le)
      _ ≤ x := by simpa only [sq, mul_one] using
        mul_le_mul_of_nonneg_left hx.2.le hx.1.le
      _ ≤ h := hhx
  have hRY : Y * R A ≤ 1 / (2 * √T) := by
    have H := Real.le_sqrt_of_sq_le hAY
    calc
      _ ≤ Y * (1 / (2 * √A * √T)) :=
        mul_le_mul_of_nonneg_left (vpPhotonT_le_geom hmγ hreg hT hA) hY.1.le
      _ ≤ √A * (1 / (2 * √A * √T)) := mul_le_mul_of_nonneg_right H (by positivity)
      _ = _ := by field_simp
  have hb : |selfK2 Y x * Y / h * R A| ≤ 1 / (2 * √T) := by
    rw [abs_mul, abs_div, abs_mul, abs_of_pos hY.1, abs_of_pos hh,
      abs_of_nonneg (vpPhotonT_nonneg hmγ (hmγ.trans_le hreg) hT one_pos hA.le)]
    change |selfK2 Y x| * Y / h * R A ≤ _
    rw [show |selfK2 Y x| * Y / h * R A = (Y * R A) * (|selfK2 Y x| / h) by ring]
    exact (mul_le_of_le_one_right (mul_nonneg hY.1.le
      (vpPhotonT_nonneg hmγ (hmγ.trans_le hreg) hT one_pos hA.le))
      ((div_le_one hh).2 hK)).trans hRY
  have hdT : √d * √T ≤ 2 * √T := by
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
    exact (Real.sqrt_le_sqrt hd₁).trans_eq Real.sqrt_one |>.trans (by norm_num)
  calc
    _ ≤ 14 / (√d * √T) + 1 / (2 * √T) :=
      (abs_add_le _ _).trans (add_le_add (abs_self_radial_tail_sub_le la hmγ hreg hT hY hx) hb)
    _ ≤ 14 / (√d * √T) + 1 / (√d * √T) :=
      add_le_add_right (div_le_div_of_nonneg_left one_pos.le (by positivity) hdT) _
    _ = _ := by ring

end QED.ChainProof.SetCRegDisp

end
