/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndFTC
public import QED.ChainProof.SetCRegBndSoft
public import QED.ChainProof.SetCRegBndRadial

/-!
# Centering the inner ladder radial remainder

The ratio and derivative terms of the radial masters in
`QED/TwoLoop/UnitLCloseMasters.lean` yield a bound after subtracting
the photon evaluated at the shell argument.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitLLink

/-- The inner dressed ladder radial integrand with its first master removed. -/
noncomputable def ladderInnerRadialRemainder (mγ Λ T la Y x z : ℝ) : ℝ :=
  let d := 1 - Y
  let c := Y * d
  let h := ladderInnerMass 1 la x / x
  let P := Y * x * (1 - x) / 2
  let q := x * (3 * Y - 2) + (1 - x) * (4 * Y - Y ^ 2 - 2) - 2 * c * (1 - x) ^ 2 / x
  let r := c / (z + c)
  let s := (Y ^ 2 + (z + c) * h) / d
  let R := vpPhotonT 1 mγ Λ T
  P / d * (8 * r - 9 * r ^ 2) * R s - P / d ^ 2 * (q * (1 - r)) * deriv R s

/-- The inner ladder radial remainder is integrable at fixed positive
regulators. After adding its shell endpoint it has a uniform bound. -/
theorem abs_integral_ladderInnerRadialRemainder_add_shell_le {mγ Λ T Y x : ℝ} (la : ℝ)
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T)
    (hY : Y ∈ Ioo 0 1) (hx : x ∈ Ioo 0 1) :
    let d := 1 - Y
    let c := Y * d
    let h := ladderInnerMass 1 la x / x
    let f := ladderInnerRadialRemainder mγ Λ T la Y x
    IntegrableOn f (Ioi 0) ∧
      |(∫ z in Ioi (0 : ℝ), f z) +
        Y ^ 2 * (1 - x) ^ 3 / h * vpPhotonT 1 mγ Λ T (shellArg 1 Y)| ≤
        17 / (2 * √T) + 6 / (√d * √T) + 3 / T * (1 + c * (-Real.log x - Real.log d)) := by
  intro d c h f
  let P := Y * x * (1 - x) / 2
  let Q := x * (3 * Y - 2) + (1 - x) * (4 * Y - Y ^ 2 - 2)
  let W := Y ^ 2 * (1 - x) ^ 3
  let U := shellArg 1 Y
  let R := vpPhotonT 1 mγ Λ T
  let A := U + Y * h
  let s := fun z : ℝ => (Y ^ 2 + (z + c) * h) / d
  let r := fun z : ℝ => c / (z + c)
  let f₁ := fun z => P / d * (8 * r z - 9 * r z ^ 2) * R (s z)
  let f₂ := fun z => P / d ^ 2 * (-Q * (1 - r z)) * deriv R (s z)
  let f₃ := fun z => W / d * deriv R (s z)
  let f₄ := fun z => Y * c ^ 2 * (1 - x) ^ 3 / (d ^ 2 * (z + c)) * deriv R (s z)
  have hd : 0 < d := sub_pos.mpr hY.2
  have hc : 0 < c := mul_pos hY.1 hd
  have hh : 0 < h := by
    apply div_pos _ hx.1
    exact add_pos_of_pos_of_nonneg (by simpa using sq_pos_of_pos hx.1)
      (mul_nonneg (sub_nonneg.mpr hx.2.le) (sq_nonneg _))
  have hU : 0 < U := by
    simpa only [U, shellArg, one_pow, one_mul, QED.TwoLoop.UnitVPLink.photonVar] using
      div_pos (sq_pos_of_pos hY.1) hd
  have hA : 0 < A := add_pos hU (mul_pos hY.1 hh)
  have eU : U = Y ^ 2 / d := by
    simp only [U, shellArg, one_pow, one_mul, QED.TwoLoop.UnitVPLink.photonVar, d]
  have es (z : ℝ) : s z = A + (h / d) * z := by
    dsimp only [s, A, c]
    rw [eU]
    field_simp
    ring
  have hR : IntegrableOn (R ∘ s) (Ioi 0) := by
    simp only [Function.comp_def, es]
    exact (integrableOn_Ioi_comp_mul_left_iff (fun z => R (A + z)) 0 (div_pos hh hd)).2
      (by simpa only [mul_zero] using
        integrableOn_vpPhotonT_shift hmγ (hmγ.trans_le hreg) hT one_pos hA.le)
  have hD : IntegrableOn (deriv R ∘ s) (Ioi 0) := by
    simp only [Function.comp_def, es]
    exact (integral_Ioi_deriv_vpPhotonT hmγ hreg hT hA (div_pos hh hd)).1
  have hr (z : ℝ) (hz : z ∈ Ioi (0 : ℝ)) : 0 ≤ r z ∧ r z ≤ 1 := by
    have hs : 0 < z + c := add_pos hz hc
    exact ⟨div_nonneg hc.le hs.le, (div_le_one hs).2 (le_add_of_nonneg_left hz.le)⟩
  have hI₁ : IntegrableOn f₁ (Ioi 0) := by
    apply hR.bdd_mul (c := |P / d| * 17) (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    obtain ⟨h0, h1⟩ := hr z hz
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (mul_nonneg (by norm_num) h0), abs_of_nonneg (by positivity)]
    have h2 := pow_le_one₀ h0 h1 (n := 2)
    linarith only [h1, h2]
  have hI₂ : IntegrableOn f₂ (Ioi 0) := by
    apply hD.bdd_mul (c := |P / d ^ 2| * |-Q|) (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    obtain ⟨h0, h1⟩ := hr z hz
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr h1)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (abs_nonneg _) (sub_le_self 1 h0)) (abs_nonneg _)
  have hI₃ : IntegrableOn f₃ (Ioi 0) := hD.const_mul _
  have hI₄ : IntegrableOn f₄ (Ioi 0) := by
    have hm : Measurable (fun z : ℝ => Y * c ^ 2 * (1 - x) ^ 3 / (d ^ 2 * (z + c))) :=
      measurable_const.div (measurable_const.mul (measurable_id.add measurable_const))
    apply hD.bdd_mul (c := (Y * c ^ 2 * (1 - x) ^ 3) / (d ^ 2 * c)) hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hzc : c ≤ z + c := le_add_of_nonneg_left hz.le
    have hn : 0 ≤ Y * c ^ 2 * (1 - x) ^ 3 :=
      mul_nonneg (mul_nonneg hY.1.le (sq_nonneg _)) (pow_nonneg (sub_nonneg.mpr hx.2.le) _)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg hn (mul_nonneg (sq_nonneg _) (hc.le.trans hzc)))]
    exact div_le_div_of_nonneg_left hn (mul_pos (pow_pos hd 2) hc)
      (mul_le_mul_of_nonneg_left hzc (sq_nonneg _))
  have e : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] (f₁ + f₂ + f₃ - f₄) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    change f₁ z - P / d ^ 2 *
        ((Q - 2 * c * (1 - x) ^ 2 / x) * (1 - r z)) * deriv R (s z) =
      f₁ z + f₂ z + f₃ z - f₄ z
    dsimp only [f₂, f₃, f₄, r, P, W, c]
    have hz' : z + Y * d ≠ 0 := (add_pos hz hc).ne'
    field_simp [hd.ne', hx.1.ne', hz']
    ring
  have h₁ : |∫ z in Ioi (0 : ℝ), f₁ z| ≤ 17 / (2 * √T) := by
    let g := fun z : ℝ => P / d * (8 * (c / z) - 9 * (c / z) ^ 2) *
      R ((Y ^ 2 + z * h) / d)
    have eg (z : ℝ) : f₁ z = g (c + z) := by
      simp only [f₁, g, r, s, add_comm c z]
    simp_rw [eg]
    change |photonTail g c| ≤ _
    rw [photonTail_eq_Ioi]
    exact abs_integral_ladderInner_radial_ratio_le la hmγ hreg hT hY hx
  have h₂ : |∫ z in Ioi (0 : ℝ), f₂ z| ≤ 6 / (√d * √T) := by
    let g := fun z : ℝ => P / d ^ 2 * (-Q * (1 - c / z)) * deriv R ((Y ^ 2 + z * h) / d)
    have eg (z : ℝ) : f₂ z = g (c + z) := by
      simp only [f₂, g, r, s, add_comm c z]
    simp_rw [eg]
    change |photonTail g c| ≤ _
    rw [photonTail_eq_Ioi]
    apply abs_integral_ladderInner_radial_regular_le la hmγ hreg hT hY hx
    rw [abs_neg]
    exact (abs_ladderInner_radial_regularCoeff_le hY hx).trans (by norm_num)
  have h₃ : |(∫ z in Ioi (0 : ℝ), f₃ z) + W / h * R U| ≤ 3 / T := by
    simp only [f₃, es]
    exact (abs_integral_ladderSoft_sub_endpoint_le hmγ hreg hT hY hx hh).2
  have h₄ : |∫ z in Ioi (0 : ℝ), f₄ z| ≤ 3 * c / T * (-Real.log x - Real.log d) :=
    abs_integral_ladderInner_radial_singular_le la hmγ hreg hT hY hx
  constructor
  · exact (((hI₁.add hI₂).add hI₃).sub hI₄).congr e.symm
  rw [integral_congr_ae e]
  rw [integral_sub' ((hI₁.add hI₂).add hI₃) hI₄, integral_add' (hI₁.add hI₂) hI₃,
    integral_add' hI₁ hI₂]
  calc
    _ ≤ |∫ z in Ioi (0 : ℝ), f₁ z| + |∫ z in Ioi (0 : ℝ), f₂ z| +
        |(∫ z in Ioi (0 : ℝ), f₃ z) + W / h * R U| + |∫ z in Ioi (0 : ℝ), f₄ z| := by
      generalize (∫ z in Ioi (0 : ℝ), f₁ z) = v₁
      generalize (∫ z in Ioi (0 : ℝ), f₂ z) = v₂
      generalize (∫ z in Ioi (0 : ℝ), f₃ z) = v₃
      generalize (∫ z in Ioi (0 : ℝ), f₄ z) = v₄
      change |v₁ + v₂ + v₃ - v₄ + W / h * R U| ≤ _
      rw [show v₁ + v₂ + v₃ - v₄ + W / h * R U =
        (v₁ + v₂) + (v₃ + W / h * R U) - v₄ by ring]
      have hsum : |v₁ + v₂ + (v₃ + W / h * R U)| ≤ |v₁| + |v₂| + |v₃ + W / h * R U| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      exact (abs_sub _ _).trans (add_le_add hsum le_rfl)
    _ ≤ _ := (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄).trans_eq (by ring)

end QED.ChainProof.SetCRegDisp

end
