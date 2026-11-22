/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndDeriv
public import QED.TwoLoop.UnitLCloseMasters

/-!
# The inverse-radial part of the inner ladder soft term

The (c/z) part of the singular derivative coefficient in
`QED/TwoLoop/UnitLCloseMasters.lean` has a radial estimate with only logarithmic
growth in the remaining parameters. It uses the exact integral of the second
ladder master.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitLLink

/-- Bound the inverse-radial soft correction after the radial integration. -/
theorem abs_integral_ladderInner_radial_singular_le {mγ Λ T Y x : ℝ} (la : ℝ)
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T)
    (hY : Y ∈ Ioo 0 1) (hx : x ∈ Ioo 0 1) :
    let d := 1 - Y
    let c := Y * d
    let h := ladderInnerMass 1 la x / x
    |∫ z in Ioi (0 : ℝ),
      (Y * c ^ 2 * (1 - x) ^ 3 / (d ^ 2 * (z + c))) *
        deriv (vpPhotonT 1 mγ Λ T) ((Y ^ 2 + (z + c) * h) / d)| ≤
      3 * c / T * (-Real.log x - Real.log d) := by
  intro d c h
  have hYpos := hY.1
  have hxpos := hx.1
  have hd : 0 < d := sub_pos.mpr hY.2
  have hc : 0 < c := mul_pos hY.1 hd
  have hhx : x ≤ h := by
    apply (le_div_iff₀ hx.1).2
    unfold ladderInnerMass
    rw [one_pow, mul_one, ← sq]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hx.2.le) (sq_nonneg _))
  have hh := hx.1.trans_le hhx
  have hx' := sub_pos.mpr hx.2
  let C := 3 * Y ^ 2 * c / T
  obtain ⟨hI, hInt⟩ := hasIoiInt_master2 (pow_pos hY.1 2) hh hc
  calc
    _ ≤ ∫ z in Ioi (0 : ℝ), C * masterK2 (Y ^ 2) h (z + c) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hI.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have hz' : 0 < z + c := add_pos hz hc
      let A := Y ^ 2 + (z + c) * h
      let s := A / d
      have hA : 0 < A := by dsimp only [A]; positivity
      have hs : 0 < s := div_pos hA hd
      have hD := mul_abs_deriv_vpPhotonT_le one_pos hmγ hreg hT hs
      rw [one_pow, mul_one] at hD
      have hB : |deriv (vpPhotonT 1 mγ Λ T) s| ≤ (3 / T) / s := by
        apply (le_div_iff₀ hs).2
        rw [mul_comm]
        exact hD.trans (div_le_div_of_nonneg_left (by norm_num) hT (le_add_of_nonneg_left hs.le))
      have hcoef : 0 ≤ Y * c ^ 2 * (1 - x) ^ 3 / (d ^ 2 * (z + c)) :=
        div_nonneg (mul_nonneg (mul_nonneg hY.1.le (sq_nonneg _)) (pow_nonneg hx'.le _))
          (by positivity)
      change ‖(Y * c ^ 2 * (1 - x) ^ 3 / (d ^ 2 * (z + c))) *
        deriv (vpPhotonT 1 mγ Λ T) s‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoef]
      have hpow : (1 - x) ^ 3 ≤ 1 :=
        pow_le_one₀ hx'.le (sub_le_self _ hx.1.le)
      calc
        _ ≤ (Y * c ^ 2 / (d ^ 2 * (z + c))) * ((3 / T) / s) :=
          mul_le_mul (div_le_div_of_nonneg_right
            (mul_le_of_le_one_right (by positivity) hpow) (by positivity)) hB
            (abs_nonneg _) (by positivity)
        _ = _ := by
          dsimp only [C, s, masterK2]
          rw [show Y ^ 2 + (z + c) * h = A from rfl]
          field_simp [hd.ne', hz'.ne', hA.ne', hT.ne']
          dsimp only [c]
    _ = 3 * c / T * Real.log (1 + Y ^ 2 / (c * h)) := by
      rw [integral_const_mul, hInt]
      dsimp only [C]
      field_simp [hY.1.ne', hT.ne']
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hlogarg : 1 + Y ^ 2 / (c * h) ≤ 1 / (d * x) := by
        have hfrac : Y ^ 2 / (c * h) ≤ Y / (d * x) := calc
          _ = Y / (d * h) := by
            dsimp only [c]
            field_simp [hY.1.ne', hd.ne', hh.ne']
          _ ≤ _ := div_le_div_of_nonneg_left hY.1.le (mul_pos hd hx.1)
            (mul_le_mul_of_nonneg_left hhx hd.le)
        apply (le_div_iff₀ (mul_pos hd hx.1)).2
        have hdx : d * x ≤ d := mul_le_of_le_one_right hd.le hx.2.le
        have e : d + Y = 1 := by dsimp only [d]; ring
        calc
          _ ≤ (1 + Y / (d * x)) * (d * x) :=
            mul_le_mul_of_nonneg_right (add_le_add_right hfrac 1) (by positivity)
          _ = d * x + Y := by field_simp [hxpos.ne', hd.ne']
          _ ≤ 1 := (add_le_add_left hdx Y).trans_eq (by linarith only [e])
      have hlog := Real.log_le_log (by positivity) hlogarg
      rwa [Real.log_div one_ne_zero (mul_ne_zero hd.ne' hx.1.ne'), Real.log_one,
        Real.log_mul hd.ne' hx.1.ne', show 0 - (Real.log d + Real.log x) =
          -Real.log x - Real.log d by ring] at hlog

end QED.ChainProof.SetCRegDisp

end
