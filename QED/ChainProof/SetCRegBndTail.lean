/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndShell
public import QED.TwoLoop.UnitLCloseMasters

/-!
# The leading radial term of the inner dressed ladder

The first master of `ladderAX_eq` in QED/TwoLoop/UnitLCloseMasters.lean
gives a photon tail with a shifted lower endpoint. Centering it at zero
extracts the one-loop Pauli coefficient and leaves a uniform bound.
-/

@[expose] public section

open Set MeasureTheory Filter Real
open QED.TwoLoop.UnitLLink

namespace QED.ChainProof.SetCRegDisp

/-- The prefactor of the radial tail in the first ladder master. -/
noncomputable def ladderLeadingWeight (la Y x : ℝ) : ℝ :=
  Y / 2 * (x ^ 2 * (1 - x) / ladderInnerMass 1 la x)

/-- The lower endpoint after the radial change of variable. -/
noncomputable def ladderLeadingShift (la Y x : ℝ) : ℝ :=
  shellArg 1 Y + Y * (ladderInnerMass 1 la x / x)

/-- The integrated first master for the inner ladder with photon function `R`. -/
noncomputable def ladderInnerLeading (R : ℝ → ℝ) (la : ℝ) : ℝ :=
  ∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
    ladderLeadingWeight la Y x * photonTail R (ladderLeadingShift la Y x)

private theorem ladderH_ge_x (la : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x ≤ ladderInnerMass 1 la x / x := by
  rw [le_div_iff₀ hx.1, ladderInnerMass]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hx.2.le) (sq_nonneg la)]

private theorem ladderLeadingWeight_eq (la Y : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ladderLeadingWeight la Y x = (Y * x * (1 - x) / 2) / (ladderInnerMass 1 la x / x) := by
  have hh := hx.1.trans_le (ladderH_ge_x la hx)
  have hM : 0 < ladderInnerMass 1 la x := by
    simpa only [zero_mul] using (lt_div_iff₀ hx.1).1 hh
  unfold ladderLeadingWeight
  field_simp [hx.1.ne', hM.ne']

/-- Integrating the first dressed ladder master in the shifted radial variable gives the tail. -/
theorem integral_ladderLeading_radial (R : ℝ → ℝ) (la : ℝ) {Y x : ℝ}
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∫ z in Ioi (0 : ℝ), (Y * x * (1 - x) / 2) / (1 - Y) *
      R ((Y ^ 2 + (z + Y * (1 - Y)) * (ladderInnerMass 1 la x / x)) / (1 - Y))) =
      ladderLeadingWeight la Y x * photonTail R (ladderLeadingShift la Y x) := by
  let h := ladderInnerMass 1 la x / x
  have hh : 0 < h := hx.1.trans_le (ladderH_ge_x la hx)
  have hY' : 0 < 1 - Y := sub_pos.mpr hY.2
  let A := ladderLeadingShift la Y x
  have he (z : ℝ) : (Y ^ 2 + (z + Y * (1 - Y)) * h) / (1 - Y) =
      A + (h / (1 - Y)) * z := by
    dsimp [A, ladderLeadingShift, shellArg, QED.TwoLoop.UnitVPLink.photonVar, h]
    field_simp
    ring
  change (∫ z in Ioi (0 : ℝ), (Y * x * (1 - x) / 2) / (1 - Y) *
    R ((Y ^ 2 + (z + Y * (1 - Y)) * h) / (1 - Y))) = _
  simp_rw [he]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun u => R (A + u)) 0 (div_pos hh hY'),
    mul_zero, smul_eq_mul, ← photonTail, ladderLeadingWeight_eq la Y hx]
  change _ = (Y * x * (1 - x) / 2) / h * photonTail R A
  field_simp

private theorem ladderLeadingWeight_bounds (la : ℝ) {Y x : ℝ}
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ ladderLeadingWeight la Y x ∧ ladderLeadingWeight la Y x ≤ 1 / 2 := by
  have hh := hx.1.trans_le (ladderH_ge_x la hx)
  have hx' : 0 ≤ 1 - x := sub_nonneg.mpr hx.2.le
  rw [ladderLeadingWeight_eq la Y hx]
  refine ⟨div_nonneg (by positivity [hY.1, hx.1, hx']) hh.le, (div_le_iff₀ hh).2 ?_⟩
  have hp : Y * (1 - x) ≤ 1 := by
    simpa using mul_le_mul hY.2.le (show 1 - x ≤ 1 by linarith [hx.1]) hx' zero_le_one
  nlinarith only [mul_le_mul_of_nonneg_right hp hx.1.le, ladderH_ge_x la hx]

private theorem ladderLeadingShift_nonneg (la : ℝ) {Y x : ℝ}
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ ladderLeadingShift la Y x :=
  add_nonneg (shellArg_nonneg 1 (Ioo_subset_Icc_self hY))
    (mul_nonneg hY.1.le (hx.1.le.trans (ladderH_ge_x la hx)))

private theorem ladderLeading_sqrt_le (la : ℝ) {Y x : ℝ}
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ladderLeadingWeight la Y x * √(ladderLeadingShift la Y x) ≤
      (1 / 2) * ((1 - Y) ^ (-(1 / 2) : ℝ) + 1) := by
  let h := ladderInnerMass 1 la x / x
  let w := ladderLeadingWeight la Y x
  have hh : 0 < h := hx.1.trans_le (ladderH_ge_x la hx)
  have h1Y : 0 < 1 - Y := sub_pos.mpr hY.2
  have ⟨hw0, hw⟩ := ladderLeadingWeight_bounds la hY hx
  have hA : √(shellArg 1 Y) ≤ (1 - Y) ^ (-(1 / 2) : ℝ) := by
    simp only [shellArg, one_pow, one_mul, QED.TwoLoop.UnitVPLink.photonVar]
    rw [sqrt_div (sq_nonneg Y), sqrt_sq hY.1.le, rpow_neg h1Y.le, ← sqrt_eq_rpow]
    simpa only [one_div] using div_le_div_of_nonneg_right hY.2.le (sqrt_nonneg (1 - Y))
  have hB : w * √(Y * h) ≤ 1 / 2 := by
    have hxh : x ≤ √h := (le_sqrt hx.1.le hh.le).2 (by
      nlinarith only [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le), ladderH_ge_x la hx])
    have hYx : Y * (1 - x) ≤ 1 := by
      simpa using mul_le_mul hY.2.le (show 1 - x ≤ 1 by linarith [hx.1])
        (sub_nonneg.mpr hx.2.le) zero_le_one
    calc
      w * √(Y * h) ≤ w * √h :=
        mul_le_mul_of_nonneg_left (sqrt_le_sqrt (mul_le_of_le_one_left hh.le hY.2.le)) hw0
      _ = (Y * (1 - x) * x) / (2 * √h) := by
        rw [show w = (Y * x * (1 - x) / 2) / h from ladderLeadingWeight_eq la Y hx]
        have hs : 0 < √h := sqrt_pos.2 hh
        field_simp
        rw [sq_sqrt hh.le]
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_right hYx hx.1.le
        linarith
  have hA₀ : 0 ≤ shellArg 1 Y := shellArg_nonneg 1 (Ioo_subset_Icc_self hY)
  have hB₀ : 0 ≤ Y * h := mul_nonneg hY.1.le hh.le
  have hS : √(shellArg 1 Y + Y * h) ≤ √(shellArg 1 Y) + √(Y * h) := by
    apply (sqrt_le_left (by positivity)).2
    nlinarith only [sq_sqrt hA₀, sq_sqrt hB₀, mul_nonneg (sqrt_nonneg (shellArg 1 Y))
      (sqrt_nonneg (Y * h))]
  calc
    _ ≤ w * (√(shellArg 1 Y) + √(Y * h)) := mul_le_mul_of_nonneg_left hS hw0
    _ ≤ (1 / 2) * (1 - Y) ^ (-(1 / 2) : ℝ) + 1 / 2 := by
      rw [mul_add]
      exact add_le_add (mul_le_mul hw hA (sqrt_nonneg _) (by norm_num)) hB
    _ = _ := by ring

private theorem ladderTail_pointwise {mγ Λ T : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (la : ℝ) {Y x : ℝ}
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖ladderLeadingWeight la Y x * (photonTail (vpPhotonT 1 mγ Λ T) (ladderLeadingShift la Y x) -
      photonTail (vpPhotonT 1 mγ Λ T) 0)‖ ≤
      (1 / √T) * ((1 - Y) ^ (-(1 / 2) : ℝ) + 1) := by
  let A := ladderLeadingShift la Y x
  have hA := ladderLeadingShift_nonneg la hY hx
  have hw := (ladderLeadingWeight_bounds la hY hx).1
  obtain ⟨h0, h1⟩ := photonTail_sub_le_log one_pos hmγ hreg hT hA
  simp only [one_pow, mul_one] at h1
  have hlog : log (1 + A / T) ≤ 2 * (√A / √T) := by
    have hs : 0 ≤ A / T := div_nonneg hA hT.le
    have he : 1 + A / T ≤ (1 + √(A / T)) ^ 2 := by
      nlinarith only [sqrt_nonneg (A / T), sq_sqrt hs]
    rw [← sqrt_div hA]
    calc
      _ ≤ log ((1 + √(A / T)) ^ 2) := log_le_log (by positivity) he
      _ = 2 * log (1 + √(A / T)) := by rw [log_pow]; norm_cast
      _ ≤ _ := by linarith only [log_le_sub_one_of_pos (show 0 < 1 + √(A / T) by positivity)]
  rw [norm_mul, Real.norm_of_nonneg hw, norm_sub_rev, Real.norm_of_nonneg h0]
  calc
    _ ≤ ladderLeadingWeight la Y x * (2 * (√A / √T)) :=
      mul_le_mul_of_nonneg_left (h1.trans hlog) hw
    _ = (2 / √T) * (ladderLeadingWeight la Y x * √A) := by ring
    _ ≤ (2 / √T) * ((1 / 2) * ((1 - Y) ^ (-(1 / 2) : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (ladderLeading_sqrt_le la hY hx) (by positivity)
    _ = _ := by ring

private theorem measurable_ladderLeadingWeight (la : ℝ) :
    Measurable fun p : ℝ × ℝ => ladderLeadingWeight la p.1 p.2 := by
  unfold ladderLeadingWeight ladderInnerMass
  fun_prop

private theorem measurable_ladderLeadingTail (mγ Λ T la : ℝ) :
    Measurable fun p : ℝ × ℝ =>
      photonTail (vpPhotonT 1 mγ Λ T) (ladderLeadingShift la p.1 p.2) := by
  have ha := measurable_shellArg 1
  have hs : Measurable fun p : ℝ × ℝ => ladderLeadingShift la p.1 p.2 := by
    unfold ladderLeadingShift ladderInnerMass
    fun_prop
  exact (measurable_photonTail_vp 1 mγ Λ).comp (measurable_const.prodMk hs)

private theorem integral_ladderLeadingWeight (la Y : ℝ) :
    (∫ x in (0 : ℝ)..1, ladderLeadingWeight la Y x) = Y / 2 * oneLoopF2 1 la := by
  unfold ladderLeadingWeight oneLoopF2
  simp only [one_pow, mul_one, intervalIntegral.integral_const_mul]

/-- The leading inner ladder term centered at zero decays uniformly in both photon regulators
and in the mass on the other line. -/
theorem abs_ladderInnerLeading_sub_tail_le {mγ Λ T la : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) :
    |ladderInnerLeading (vpPhotonT 1 mγ Λ T) la -
      oneLoopF2 1 la / 4 * photonTail (vpPhotonT 1 mγ Λ T) 0| ≤ 3 / √T := by
  let R := vpPhotonT 1 mγ Λ T
  let q := photonTail R 0
  let w : ℝ → ℝ → ℝ := ladderLeadingWeight la
  let f : ℝ → ℝ → ℝ := fun Y x => w Y x * photonTail R (ladderLeadingShift la Y x)
  let g : ℝ → ℝ → ℝ := fun Y x => w Y x * q
  let B := photonK mγ Λ / T * π
  have hΛ : 0 < Λ := hmγ.trans_le hreg
  have hq0 : 0 ≤ q := photonTail_nonneg hmγ hΛ hT one_pos le_rfl
  have hqB : q ≤ B := by
    simpa only [one_pow, mul_one] using photonTail_le hmγ hΛ hT one_pos (a := 0) le_rfl
  have hw := measurable_ladderLeadingWeight la
  have hf : Measurable fun p : ℝ × ℝ => f p.1 p.2 := hw.mul (measurable_ladderLeadingTail mγ Λ T la)
  have hg : Measurable fun p : ℝ × ℝ => g p.1 p.2 := hw.mul measurable_const
  have hfB {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
      ‖f Y x‖ ≤ B / 2 := by
    have ⟨hw0, hw1⟩ := ladderLeadingWeight_bounds la hY hx
    have hA := ladderLeadingShift_nonneg la hY hx
    have h0 := photonTail_nonneg hmγ hΛ hT one_pos hA
    have hB : photonTail R (ladderLeadingShift la Y x) ≤ B := by
      simpa only [one_pow, mul_one] using photonTail_le hmγ hΛ hT one_pos hA
    rw [Real.norm_of_nonneg (mul_nonneg hw0 h0)]
    exact (mul_le_mul hw1 hB h0 (by norm_num)).trans_eq (by ring)
  have hgB {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
      ‖g Y x‖ ≤ B / 2 := by
    have ⟨hw0, hw1⟩ := ladderLeadingWeight_bounds la hY hx
    rw [Real.norm_of_nonneg (mul_nonneg hw0 hq0)]
    exact (mul_le_mul hw1 hqB hq0 (by norm_num)).trans_eq (by ring)
  have hi (F : ℝ → ℝ → ℝ) (hF : Measurable fun p : ℝ × ℝ => F p.1 p.2)
      (hFB : ∀ Y ∈ Ioo (0 : ℝ) 1, ∀ x ∈ Ioo (0 : ℝ) 1, ‖F Y x‖ ≤ B / 2) :
      (∀ Y ∈ Ioo (0 : ℝ) 1, IntegrableOn (F Y) (Ioo 0 1)) ∧
        IntegrableOn (fun Y => ∫ x in Ioo (0 : ℝ) 1, F Y x) (Ioo 0 1) := by
    have hI : ∀ Y ∈ Ioo (0 : ℝ) 1, IntegrableOn (F Y) (Ioo 0 1) := by
      intro Y hY
      refine Measure.integrableOn_of_bounded (M := B / 2) (by simp)
        (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hFB Y hY x hx
    refine ⟨hI, Measure.integrableOn_of_bounded (M := B / 2) (by simp)
      (hF.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Ioo (0 : ℝ) 1))).aestronglyMeasurable ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with Y hY
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (f := F Y) (a := 0) (b := 1) (C := B / 2) ?_
    · simpa using h
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (1 : ℝ))] with x hx hx'
    rw [uIoc_of_le zero_le_one] at hx'
    exact hFB Y hY x ⟨hx'.1, lt_of_le_of_ne hx'.2 hx⟩
  obtain ⟨hif, hIf⟩ := hi f hf fun _ hY _ hx => hfB hY hx
  obtain ⟨hig, hIg⟩ := hi g hg fun _ hY _ hx => hgB hY hx
  have eqI (F : ℝ → ℝ → ℝ) :
      (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F Y x) =
        ∫ Y in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, F Y x := by
    simp_rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have heqg : (∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, g Y x) =
      oneLoopF2 1 la / 4 * q := by
    simp only [g, w, intervalIntegral.integral_mul_const, integral_ladderLeadingWeight]
    simp_rw [div_mul_eq_mul_div, mul_div_assoc]
    rw [intervalIntegral.integral_div, integral_id]
    ring
  change |(∫ Y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f Y x) -
    oneLoopF2 1 la / 4 * q| ≤ _
  rw [← heqg, eqI, eqI, ← integral_sub hIf hIg]
  let D := fun Y : ℝ => (1 / √T) * ((1 - Y) ^ (-(1 / 2) : ℝ) + 1)
  have hD₀ : IntegrableOn (fun Y : ℝ => (1 - Y) ^ (-(1 / 2) : ℝ)) (Ioo 0 1) := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := 0)
      (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left 1
    rw [sub_self, sub_zero] at h
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h
  have hD : IntegrableOn D (Ioo 0 1) :=
    (hD₀.add (integrableOn_const (by simp))).const_mul _
  have hInt : (∫ Y in Ioo (0 : ℝ) 1, D Y) = 3 / √T := by
    have e : (∫ Y in Ioo (0 : ℝ) 1, (1 - Y) ^ (-(1 / 2) : ℝ)) = 2 := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2) : ℝ))]
      norm_num [integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]
    rw [show D = fun Y => (1 / √T) * ((1 - Y) ^ (-(1 / 2) : ℝ) + 1) from rfl,
      integral_const_mul, integral_add hD₀ (integrableOn_const (by simp)), e]
    simp
    ring
  rw [← hInt, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hD
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with Y hY
  rw [← integral_sub (hif Y hY) (hig Y hY), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (f := fun x => f Y x - g Y x) (a := 0) (b := 1) (C := D Y) ?_
  · simpa using h
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (1 : ℝ))] with x hx hx'
  rw [uIoc_of_le zero_le_one] at hx'
  simpa only [f, g, w, R, q, ← mul_sub, D] using
    ladderTail_pointwise hmγ hreg hT la hY ⟨hx'.1, lt_of_le_of_ne hx'.2 hx⟩

/-- The ordinary PV difference of the leading ladder terms has tail coefficient
`(F₂(mγ) - F₂(Λ)) / 4`. -/
theorem abs_ladderInnerLeading_pv_sub_tail_le {mγ Λ T : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) :
    |ladderInnerLeading (vpPhotonT 1 mγ Λ T) mγ -
      ladderInnerLeading (vpPhotonT 1 mγ Λ T) Λ -
      (oneLoopF2 1 mγ - oneLoopF2 1 Λ) / 4 * photonTail (vpPhotonT 1 mγ Λ T) 0| ≤ 6 / √T := by
  have h₁ := abs_ladderInnerLeading_sub_tail_le (la := mγ) hmγ hreg hT
  have h₂ := abs_ladderInnerLeading_sub_tail_le (la := Λ) hmγ hreg hT
  generalize ladderInnerLeading (vpPhotonT 1 mγ Λ T) mγ = l at *
  generalize ladderInnerLeading (vpPhotonT 1 mγ Λ T) Λ = L at *
  generalize photonTail (vpPhotonT 1 mγ Λ T) 0 = q at *
  rw [show l - L - (oneLoopF2 1 mγ - oneLoopF2 1 Λ) / 4 * q =
    (l - oneLoopF2 1 mγ / 4 * q) - (L - oneLoopF2 1 Λ / 4 * q) by ring]
  exact (abs_sub _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

end QED.ChainProof.SetCRegDisp

end
