/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndDeriv
public import QED.TwoLoop.UnitLCloseMasters
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Radial bounds for the inner ladder remainder

The masters in `QED/TwoLoop/UnitLCloseMasters.lean` contain a (c/z) and a
((c/z)^2) correction to the leading propagator. Their combined radial
integral against the merged positive photon is uniformly bounded, including
at coincidence of the heavy regulator and the spectral mass.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitLLink (ladderInnerMass)

/-- The geometric-mean bound for a unit-mass spectral propagator. -/
theorem one_div_add_le_inv_geometric {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    1 / (s + T) ≤ 1 / (2 * √s * √T) := by
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith only [sq_nonneg (√s - √T), Real.sq_sqrt hs.le, Real.sq_sqrt hT.le]

/-- The merged photon inherits the geometric-mean bound at unit mass. -/
theorem vpPhotonT_le_geom {mγ Λ T s : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hs : 0 < s) :
    vpPhotonT 1 mγ Λ T s ≤ 1 / (2 * √s * √T) := by
  have h := vpPhotonT_le_single one_pos hmγ hreg hT hs.le
  rw [one_pow, mul_one] at h
  exact h.trans (one_div_add_le_inv_geometric hs hT)

private theorem rpow_neg_three_halves {z : ℝ} (hz : 0 < z) :
    z ^ (-(3 / 2) : ℝ) = 1 / (z * √z) := by
  rw [show -(3 / 2 : ℝ) = -(1 + 1 / 2) by norm_num, Real.rpow_neg hz.le,
    Real.rpow_add hz, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]

private theorem integral_Ioi_rpow_neg_three_halves {c : ℝ} (hc : 0 < c) :
    (∫ z in Ioi c, z ^ (-(3 / 2) : ℝ)) = 2 / √c := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hc,
    show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num, Real.rpow_neg hc.le,
    ← Real.sqrt_eq_rpow]
  ring

private theorem abs_ladder_pv_ratio_le {u : ℝ} (hu : 0 ≤ u) (hu₁ : u ≤ 1) :
    |8 * u - 9 * u ^ 2| ≤ 17 * u := by
  have hu₂ := mul_le_mul_of_nonneg_left hu₁ hu
  exact abs_le.mpr ⟨by nlinarith only [hu, hu₂], by nlinarith only [hu, sq_nonneg u]⟩

private theorem ladderInnerMass_div_ge {x : ℝ} (la : ℝ) (hx : x ∈ Ioo 0 1) :
    x ≤ ladderInnerMass 1 la x / x := by
  apply (le_div_iff₀ hx.1).2
  unfold ladderInnerMass
  rw [one_pow, mul_one, ← sq]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hx.2.le) (sq_nonneg _))

/-- The two inverse-radial ladder corrections are uniformly bounded after radial integration. -/
theorem abs_integral_ladderInner_radial_ratio_le {mγ Λ T Y x : ℝ} (la : ℝ)
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hY : Y ∈ Ioo 0 1) (hx : x ∈ Ioo 0 1) :
    let d := 1 - Y
    let c := Y * d
    let h := ladderInnerMass 1 la x / x
    let P := Y * x * (1 - x) / 2
    |∫ z in Ioi c, P / d * (8 * (c / z) - 9 * (c / z) ^ 2) *
      vpPhotonT 1 mγ Λ T ((Y ^ 2 + z * h) / d)| ≤ 17 / (2 * √T) := by
  intro d c h P
  have hd : 0 < d := sub_pos.mpr hY.2
  have hc : 0 < c := mul_pos hY.1 hd
  have hhx : x ≤ h := ladderInnerMass_div_ge la hx
  have hh := hx.1.trans_le hhx
  have hp : 0 < P := div_pos (mul_pos (mul_pos hY.1 hx.1) (sub_pos.mpr hx.2)) two_pos
  have hT' := Real.sqrt_pos.2 hT
  have hh' := Real.sqrt_pos.2 hh
  have hd' := Real.sqrt_pos.2 hd
  have hc' := Real.sqrt_pos.2 hc
  let C := 17 * P * c / (2 * √d * √h * √T)
  have hI : IntegrableOn (fun z => C * z ^ (-(3 / 2) : ℝ)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hc).const_mul C
  have hB : |∫ z in Ioi c, P / d * (8 * (c / z) - 9 * (c / z) ^ 2) *
      vpPhotonT 1 mγ Λ T ((Y ^ 2 + z * h) / d)| ≤ C * (2 / √c) := by
    rw [← integral_Ioi_rpow_neg_three_halves hc, ← integral_const_mul, ← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hI
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz' := hc.trans hz
    have hzs := Real.sqrt_pos.2 hz'
    let s := (Y ^ 2 + z * h) / d
    have hs : 0 < s := by dsimp [s]; positivity
    have hlow : z * h / d ≤ s := by
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) hd.le
    have hroot : √z * √h / √d ≤ √s := by
      simpa only [Real.sqrt_div (by positivity : 0 ≤ z * h), Real.sqrt_mul hz'.le] using
        Real.sqrt_le_sqrt hlow
    have hR := vpPhotonT_le_geom hmγ hreg hT hs
    have hR₀ := vpPhotonT_nonneg hmγ (hmγ.trans_le hreg) hT one_pos hs.le
    change ‖P / d * (8 * (c / z) - 9 * (c / z) ^ 2) * vpPhotonT 1 mγ Λ T s‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (div_pos hp hd), abs_of_nonneg hR₀]
    calc
      P / d * |8 * (c / z) - 9 * (c / z) ^ 2| * vpPhotonT 1 mγ Λ T s ≤
          P / d * (17 * (c / z)) * (1 / (2 * √s * √T)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (abs_ladder_pv_ratio_le (div_nonneg hc.le hz'.le) ((div_le_one hz').2 hz.le))
          (by positivity)) hR hR₀ (by positivity)
      _ ≤ P / d * (17 * (c / z)) * (1 / (2 * (√z * √h / √d) * √T)) :=
        mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by norm_num)) hT'.le))
          (by positivity)
      _ = _ := by
        rw [rpow_neg_three_halves hz']
        dsimp only [C]
        field_simp [hd.ne', hz'.ne', hd'.ne', hh'.ne', hzs.ne', hT'.ne']
        linear_combination Real.sq_sqrt hd.le
  refine hB.trans ?_
  have hPc : P * √c ≤ √d * √h / 2 := by
    rw [show √c = √Y * √d by exact Real.sqrt_mul hY.1.le d]
    have hYsqrt : √Y ≤ 1 := by simpa using Real.sqrt_le_sqrt hY.2.le
    have hxsqrt : x ≤ √h := calc
      x ≤ √x := Real.le_sqrt_of_sq_le
        (by nlinarith only [mul_le_mul_of_nonneg_left hx.2.le hx.1.le])
      _ ≤ √h := Real.sqrt_le_sqrt hhx
    have hp₁ : P ≤ x / 2 := by
      dsimp only [P]
      have h₁ : Y * x ≤ x := mul_le_of_le_one_left hx.1.le hY.2.le
      have h₂ : Y * x * (1 - x) ≤ Y * x :=
        mul_le_of_le_one_right (mul_nonneg hY.1.le hx.1.le) (by linarith only [hx.1])
      linarith only [h₁, h₂]
    calc
      P * (√Y * √d) ≤ (√h / 2) * (1 * √d) :=
        mul_le_mul (hp₁.trans (div_le_div_of_nonneg_right hxsqrt two_pos.le))
          (mul_le_mul_of_nonneg_right hYsqrt hd'.le) (by positivity) (by positivity)
      _ = _ := by ring
  have he : C * (2 / √c) = 17 * (P * √c) / (√d * √h * √T) := by
    dsimp only [C]
    field_simp [hc'.ne', hd'.ne', hh'.ne', hT'.ne']
    exact (Real.sq_sqrt hc.le).symm
  rw [he]
  calc
    _ ≤ 17 * (√d * √h / 2) / (√d * √h * √T) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPc (by norm_num)) (by positivity)
    _ = _ := by field_simp

private theorem affine_rpow_radial {a h c : ℝ} (hh : 0 < h) (hc : 0 < a + c * h) :
    IntegrableOn (fun z => (a + z * h) ^ (-(3 / 2) : ℝ)) (Ioi c) ∧
      (∫ z in Ioi c, (a + z * h) ^ (-(3 / 2) : ℝ)) = 2 / (h * √(a + c * h)) := by
  let F := fun z : ℝ => (-2 / h) * (a + z * h) ^ (-(1 / 2) : ℝ)
  have hF : ∀ z ∈ Ici c, HasDerivAt F ((a + z * h) ^ (-(3 / 2) : ℝ)) z := by
    intro z hz
    have hp : 0 < a + z * h := hc.trans_le (add_le_add_right
      (mul_le_mul_of_nonneg_right hz hh.le) a)
    have hA : HasDerivAt (fun z : ℝ => a + z * h) h z := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id z).mul_const h).const_add a
    have H := (hA.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hp.ne')).const_mul (-2 / h)
    convert H using 1
    rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num]
    field_simp
  have htop : Tendsto F atTop (𝓝 0) := by
    have hA := tendsto_atTop_add_const_left atTop a
      ((tendsto_mul_const_atTop_of_pos hh).2 tendsto_id)
    have H := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp hA
    simpa only [F, Function.comp_def, id_eq, mul_zero] using H.const_mul (-2 / h)
  have hpos : ∀ z ∈ Ioi c, 0 ≤ (a + z * h) ^ (-(3 / 2) : ℝ) := fun z hz =>
    Real.rpow_nonneg (hc.le.trans (add_le_add_right
      (mul_le_mul_of_nonneg_right hz.le hh.le) a)) _
  have hI := integrableOn_Ioi_deriv_of_nonneg' hF hpos htop
  refine ⟨hI, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hF hI htop]
  dsimp only [F]
  rw [Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow]
  ring

/-- The regular part of the derivative coefficient in the inner ladder master. -/
theorem abs_ladderInner_radial_regularCoeff_le {Y x : ℝ} (hY : Y ∈ Ioo 0 1) (hx : x ∈ Ioo 0 1) :
    |x * (3 * Y - 2) + (1 - x) * (4 * Y - Y ^ 2 - 2)| ≤ 2 := by
  have h₁ : |3 * Y - 2| ≤ 2 := abs_le.2
    ⟨by linarith only [hY.1], by linarith only [hY.2]⟩
  have hyy : Y ^ 2 ≤ Y := by
    simpa only [sq, mul_one] using mul_le_mul_of_nonneg_left hY.2.le hY.1.le
  have h₂ : |4 * Y - Y ^ 2 - 2| ≤ 2 := abs_le.2
    ⟨by linarith only [hY.1, hyy], by linarith only [hY.2, sq_nonneg Y]⟩
  have hx' := sub_nonneg.mpr hx.2.le
  calc
    _ ≤ |x * (3 * Y - 2)| + |(1 - x) * (4 * Y - Y ^ 2 - 2)| := abs_add_le _ _
    _ ≤ x * 2 + (1 - x) * 2 := by
      rw [abs_mul, abs_mul, abs_of_pos hx.1, abs_of_nonneg hx']
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ hx.1.le) (mul_le_mul_of_nonneg_left h₂ hx')
    _ = 2 := by ring

/-- The regular derivative term from the inner ladder radial masters. -/
theorem abs_integral_ladderInner_radial_regular_le {mγ Λ T Y x q : ℝ} (la : ℝ)
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hY : Y ∈ Ioo 0 1) (hx : x ∈ Ioo 0 1)
    (hq : |q| ≤ 4) :
    let D := deriv (vpPhotonT 1 mγ Λ T)
    let d := 1 - Y
    let c := Y * d
    let h := ladderInnerMass 1 la x / x
    let P := Y * x * (1 - x) / 2
    |∫ z in Ioi c, P / d ^ 2 * (q * (1 - c / z)) *
      D ((Y ^ 2 + z * h) / d)| ≤ 6 / (√d * √T) := by
  intro D d c h P
  have hD (s : ℝ) (hs : 0 < s) : s * |D s| ≤ 3 / (s + T) := by
    simpa only [one_pow, mul_one] using mul_abs_deriv_vpPhotonT_le one_pos hmγ hreg hT hs
  have hd : 0 < d := sub_pos.mpr hY.2
  have hc : 0 < c := mul_pos hY.1 hd
  have hhx : x ≤ h := ladderInnerMass_div_ge la hx
  have hh := hx.1.trans_le hhx
  have hp : 0 < P := div_pos (mul_pos (mul_pos hY.1 hx.1) (sub_pos.mpr hx.2)) two_pos
  have hA : 0 < Y ^ 2 + c * h := by positivity
  let C := 6 * P / (√d * √T)
  obtain ⟨hI, hInt⟩ := affine_rpow_radial hh hA
  calc
    _ ≤ ∫ z in Ioi c, C * (Y ^ 2 + z * h) ^ (-(3 / 2) : ℝ) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hI.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have hz' := hc.trans hz
      let A := Y ^ 2 + z * h
      let s := A / d
      have hA' : 0 < A := by dsimp [A]; positivity
      have hs : 0 < s := div_pos hA' hd
      have hzq : |1 - c / z| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_one hz').2 hz.le))]
        exact sub_le_self _ (div_nonneg hc.le hz'.le)
      have hDb : |D s| ≤ (3 * (1 / (2 * √s * √T))) / s :=
        (le_div_iff₀ hs).2 (by
          rw [mul_comm]
          exact (hD s hs).trans (by
            simpa only [div_eq_mul_inv, one_mul] using
              mul_le_mul_of_nonneg_left (one_div_add_le_inv_geometric hs hT)
                (by norm_num : 0 ≤ (3 : ℝ))))
      change ‖P / d ^ 2 * (q * (1 - c / z)) * D s‖ ≤ C * A ^ (-(3 / 2) : ℝ)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < P / d ^ 2)]
      calc
        _ ≤ P / d ^ 2 * (4 * 1) * ((3 * (1 / (2 * √s * √T))) / s) :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (mul_le_mul hq hzq (abs_nonneg _) (by norm_num)) (by positivity))
            hDb (abs_nonneg _) (by positivity)
        _ = _ := by
          rw [rpow_neg_three_halves hA']
          dsimp only [s, C]
          rw [Real.sqrt_div hA'.le]
          have hd' := Real.sqrt_pos.2 hd
          have hA'' := Real.sqrt_pos.2 hA'
          have hT' := Real.sqrt_pos.2 hT
          field_simp [hd.ne', hd'.ne', hA'.ne', hA''.ne', hT'.ne']
          rw [Real.sq_sqrt hd.le]
          ring
    _ = C * (2 / (h * √(Y ^ 2 + c * h))) := by rw [integral_const_mul, hInt]
    _ ≤ 6 / (√d * √T) := by
      have hPY : 2 * P ≤ h * Y := by
        dsimp only [P]
        have h₁ : Y * x * (1 - x) ≤ Y * x :=
          mul_le_of_le_one_right (mul_nonneg hY.1.le hx.1.le) (by linarith only [hx.1])
        have h₂ := mul_le_mul_of_nonneg_left hhx hY.1.le
        linarith only [h₁, h₂]
      have hYr : Y ≤ √(Y ^ 2 + c * h) :=
        Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (mul_nonneg hc.le hh.le))
      have hP : 2 * P ≤ h * √(Y ^ 2 + c * h) :=
        hPY.trans (mul_le_mul_of_nonneg_left hYr hh.le)
      calc
        C * (2 / (h * √(Y ^ 2 + c * h))) =
            (6 / (√d * √T)) * ((2 * P) / (h * √(Y ^ 2 + c * h))) := by
          dsimp only [C]
          ring
        _ ≤ (6 / (√d * √T)) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 hP) (by positivity)
        _ = _ := mul_one _

end QED.ChainProof.SetCRegDisp

end
