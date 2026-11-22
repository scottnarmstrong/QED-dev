/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndShell
public import QED.TwoLoop.UnitSCLimitSMasters
public import QED.TwoLoop.UnitSCLimitCMasters
public import QED.TwoLoop.UnitSCCornerErrCoeff

/-!
# Centered leading radial masters for the self-energy and corner graphs

The leading terms in `QED/TwoLoop/UnitSCLimitSMasters.lean` and
`QED/TwoLoop/UnitSCLimitCMasters.lean` become a weighted photon tail when the
inner photon is dressed. The corner endpoint retains the mass-dependent cut
in the radial variable, which keeps its shifted photon argument positive.
-/

@[expose] public section

open Set MeasureTheory
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitLLink (ladderInnerMass)
open QED.TwoLoop.UnitSCLimit

/-- Substitute the affine photon argument into a leading radial master. -/
theorem integral_affine_photon_tail (R : ℝ → ℝ) (N M c : ℝ) {h d : ℝ}
    (hh : 0 < h) (hd : 0 < d) :
    (∫ z in Ioi (0 : ℝ), N / d * R ((M + (z + c) * h) / d)) =
      N / h * photonTail R ((M + c * h) / d) := by
  have e (z : ℝ) : (M + (z + c) * h) / d = (M + c * h) / d + (h / d) * z := by ring
  simp_rw [e]
  rw [integral_const_mul, integral_comp_mul_left_Ioi
    (fun u => R ((M + c * h) / d + u)) 0 (div_pos hh hd), mul_zero, smul_eq_mul, ← photonTail]
  field_simp

/-- The corner cut cancels the negative outer-mass contribution at the endpoint. -/
theorem corner_radial_endpoint_nonneg {la y3 y4 x : ℝ}
    (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) (hx : x ∈ Ioo 0 1) :
    let h := ladderInnerMass 1 la x / x
    let β := betaG (cornerG y3 y4) (y3 * y4) x
    0 ≤ cornerMass la 0 y3 y4 + β * h := by
  intro h β
  have hxpos := hx.1
  have hx' := sub_pos.mpr hx.2
  have hb : 0 ≤ β := (mul_pos h3 (by linarith : 0 < 1 - y3 - y4)).le.trans (le_max_left _ _)
  have hh : (1 - x) * la ^ 2 / x ≤ h := by
    apply (div_le_div_iff_of_pos_right hx.1).2
    unfold ladderInnerMass
    exact le_add_of_nonneg_left (by positivity)
  have hβ : y3 * y4 * x / (1 - x) ≤ β := le_max_right _ _
  have he : y3 * y4 * la ^ 2 ≤ β * h := by
    calc
      _ = (y3 * y4 * x / (1 - x)) * ((1 - x) * la ^ 2 / x) := by
        field_simp [hx.1.ne', hx'.ne']
      _ ≤ _ := mul_le_mul hβ hh (by positivity) hb
  dsimp only [cornerMass]
  nlinarith only [he, sq_nonneg (y3 + y4)]

private theorem abs_mul_photonTail_sub_le {mγ Λ T A w : ℝ}
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hA : 0 ≤ A) :
    |w * (photonTail (vpPhotonT 1 mγ Λ T) A - photonTail (vpPhotonT 1 mγ Λ T) 0)| ≤
      2 * (|w| * √A) / √T := by
  obtain ⟨h0, hb⟩ := photonTail_sub_le_log one_pos hmγ hreg hT hA
  rw [one_pow, mul_one] at hb
  rw [abs_mul, abs_sub_comm, abs_of_nonneg h0]
  calc
    _ ≤ |w| * (2 * √(A / T)) := mul_le_mul_of_nonneg_left
      (hb.trans (QED.TwoLoop.UnitSCCorner.log_one_add_le_two_sqrt (div_nonneg hA hT.le)))
      (abs_nonneg _)
    _ = _ := by rw [Real.sqrt_div hA]; ring

private theorem sqrt_sq_add_mul_le {Y c h : ℝ} (hY : 0 ≤ Y) (hc : 0 ≤ c) (hh : 0 ≤ h) :
    √(Y ^ 2 + c * h) ≤ Y + √c * √h := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  have hcross : 0 ≤ Y * (√c * √h) := by positivity
  calc
    _ = Y ^ 2 + (√c * √h) ^ 2 := by rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hh]
    _ ≤ _ := by nlinarith only [hcross]

private theorem ladderMass_bounds (la : ℝ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    let h := ladderInnerMass 1 la x / x
    x ≤ h ∧ x ≤ √h := by
  intro h
  have hh : x ≤ h := by
    apply (le_div_iff₀ hx.1).2
    unfold ladderInnerMass
    rw [one_pow, mul_one, ← sq]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hx.2.le) (sq_nonneg _))
  exact ⟨hh, (Real.le_sqrt_of_sq_le
    (by nlinarith only [mul_le_mul_of_nonneg_left hx.2.le hx.1.le])).trans
      (Real.sqrt_le_sqrt hh)⟩

private theorem selfK_coeff_bounds {Y x : ℝ} (hY : Y ∈ Ioo 0 1) (hx : x ∈ Ioo 0 1) :
    |selfK1 Y x| ≤ 5 / 2 * x * (1 - x) ∧ |selfK2 Y x| ≤ x ^ 2 * (1 - x) := by
  have hYx : 0 ≤ Y * x := mul_nonneg hY.1.le hx.1.le
  have hYx' : Y * x ≤ 1 :=
    (mul_le_of_le_one_right hY.1.le hx.2.le).trans hY.2.le
  have hs : ∀ A : ℝ, |x * (x - 1) * A| = x * (1 - x) * |A| := by
    intro A
    rw [abs_mul, abs_mul, abs_of_pos hx.1, abs_of_neg (sub_neg.mpr hx.2)]
    ring
  constructor
  · unfold selfK1
    rw [abs_div, abs_neg, hs, abs_of_pos (two_pos : (0 : ℝ) < 2)]
    have hA : |2 * Y * x + Y - 2 * x + 2| ≤ 5 :=
      abs_le.2 ⟨by nlinarith only [hYx, hY.1, hx.2],
        by nlinarith only [hYx', hY.2, hx.1]⟩
    calc
      _ ≤ x * (1 - x) * 5 / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA
          (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))) two_pos.le
      _ = _ := by ring
  · unfold selfK2
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x),
      abs_of_neg (sub_neg.mpr hx.2), abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hA : |Y * x - Y - x + 3| ≤ 4 :=
      abs_le.2 ⟨by linarith only [hYx, hY.2, hx.2], by linarith only [hYx', hY.1, hx.1]⟩
    calc
      _ ≤ x ^ 2 * -(x - 1) * 4 / 4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA
          (mul_nonneg (sq_nonneg _) (by linarith only [hx.2]))) (by norm_num)
      _ = _ := by ring

/-- After removing the common tail, the leading self-energy master has an integrable
threshold majorant in the remaining parameters. -/
theorem abs_self_radial_tail_sub_le {mγ Λ T Y x : ℝ} (la : ℝ)
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T) (hY : Y ∈ Ioo 0 1) (hx : x ∈ Ioo 0 1) :
    let d := 1 - Y
    let c := Y * d
    let h := ladderInnerMass 1 la x / x
    let A := (Y ^ 2 + c * h) / d
    let W := (selfK1 Y x + selfK2 Y x / h) / h
    |W * (photonTail (vpPhotonT 1 mγ Λ T) A - photonTail (vpPhotonT 1 mγ Λ T) 0)| ≤
      14 / (√d * √T) := by
  intro d c h A W
  have hd : 0 < d := sub_pos.mpr hY.2
  have hd' := Real.sqrt_pos.2 hd
  have hc : 0 < c := mul_pos hY.1 hd
  obtain ⟨hhx, hroot⟩ := ladderMass_bounds la hx
  change x ≤ h at hhx
  change x ≤ √h at hroot
  have hh := hx.1.trans_le hhx
  have hh' := Real.sqrt_pos.2 hh
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨hk₁, hk₂⟩ := selfK_coeff_bounds hY hx
  have hx' := sub_nonneg.mpr hx.2.le
  have hW : |W| ≤ 7 / 2 * (x / h) := by
    dsimp only [W]
    rw [abs_div, abs_of_pos hh]
    apply (div_le_iff₀ hh).2
    have h2 : |selfK2 Y x / h| ≤ x * (1 - x) := by
      rw [abs_div, abs_of_pos hh]
      apply (div_le_iff₀ hh).2
      refine hk₂.trans ?_
      calc
        x ^ 2 * (1 - x) = (x * (1 - x)) * x := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hhx (mul_nonneg hx.1.le hx')
    have hsum := (abs_add_le (selfK1 Y x) (selfK2 Y x / h)).trans (add_le_add hk₁ h2)
    have hs : x * (1 - x) ≤ x := mul_le_of_le_one_right hx.1.le (by linarith only [hx.1])
    rw [mul_assoc, div_mul_cancel₀ _ hh.ne']
    linarith only [hsum, hs, show 5 / 2 * x * (1 - x) = 5 / 2 * (x * (1 - x)) by ring]
  have hA' : √A ≤ (Y + √c * √h) / √d := by
    rw [show √A = √(Y ^ 2 + c * h) / √d by exact Real.sqrt_div (by positivity) d]
    exact div_le_div_of_nonneg_right (sqrt_sq_add_mul_le hY.1.le hc.le hh.le) hd'.le
  have hc' : √c ≤ 1 := by
    have hd₁ : d ≤ 1 := sub_le_self _ hY.1.le
    have hle : c ≤ 1 := by
      change Y * d ≤ 1
      exact (mul_le_of_le_one_right hY.1.le hd₁).trans hY.2.le
    simpa using Real.sqrt_le_sqrt hle
  have hterm : x / h * (Y + √c * √h) ≤ 2 := by
    have e : x / h * (Y + √c * √h) = (x / h) * Y + (x / √h) * √c := by
      field_simp [hh.ne', hh'.ne']
      linear_combination x * √c * Real.sq_sqrt hh.le
    rw [e]
    have h₁ : x / h * Y ≤ 1 :=
      (mul_le_of_le_one_left hY.1.le ((div_le_one hh).2 hhx)).trans hY.2.le
    have h₂ : x / √h * √c ≤ 1 :=
      (mul_le_of_le_one_left (Real.sqrt_nonneg _) ((div_le_one hh').2 hroot)).trans hc'
    linarith only [h₁, h₂]
  refine (abs_mul_photonTail_sub_le hmγ hreg hT hA).trans ?_
  have hprod : |W| * √A ≤ 7 / √d := calc
    _ ≤ (7 / 2 * (x / h)) * ((Y + √c * √h) / √d) :=
      mul_le_mul hW hA' (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) (div_nonneg hx.1.le hh.le))
    _ = (7 / 2 * (x / h * (Y + √c * √h))) / √d := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (by
        have H := mul_le_mul_of_nonneg_left hterm (by norm_num : 0 ≤ (7 / 2 : ℝ))
        exact H.trans_eq (by norm_num)) hd'.le
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num))
    (Real.sqrt_nonneg T)).trans_eq (by ring)

/-- The centered leading corner master, with a bound uniform in the outer photon mass. -/
theorem abs_corner_radial_tail_sub_le {mγ Λ T y3 y4 x : ℝ} (la : ℝ)
    (hmγ : 0 < mγ) (hreg : mγ ≤ Λ) (hT : 0 < T)
    (h3 : 0 < y3) (h4 : 0 < y4) (hY : y3 + y4 < 1) (hx : x ∈ Ioo 0 1) :
    let d := 1 - (y3 + y4)
    let h := ladderInnerMass 1 la x / x
    let β := betaG (cornerG y3 y4) (y3 * y4) x
    let A := (cornerMass la 0 y3 y4 + β * h) / d
    let W := cornerC0 x / h
    |W * (photonTail (vpPhotonT 1 mγ Λ T) A - photonTail (vpPhotonT 1 mγ Λ T) 0)| ≤
      2 / (√d * √T) := by
  intro d h β A W
  have hd : 0 < d := sub_pos.mpr hY
  have hd' := Real.sqrt_pos.2 hd
  have hxpos := hx.1
  have hx' := sub_pos.mpr hx.2
  obtain ⟨hhx, hroot⟩ := ladderMass_bounds la hx
  change x ≤ h at hhx
  change x ≤ √h at hroot
  have hh := hx.1.trans_le hhx
  have hh' := Real.sqrt_pos.2 hh
  have hb : 0 ≤ β := (mul_pos h3 (by linarith : 0 < 1 - y3 - y4)).le.trans (le_max_left _ _)
  have hA0 : 0 ≤ cornerMass la 0 y3 y4 + β * h := corner_radial_endpoint_nonneg h3 h4 hY hx
  have hA : 0 ≤ A := div_nonneg hA0 hd.le
  have hW : 0 ≤ W := by
    dsimp only [W, cornerC0]
    positivity
  have hA' : √A ≤ (y3 + y4 + √β * √h) / √d := by
    rw [show √A = √(cornerMass la 0 y3 y4 + β * h) / √d by exact Real.sqrt_div hA0 d]
    apply div_le_div_of_nonneg_right _ hd'.le
    refine (Real.sqrt_le_sqrt ?_).trans (sqrt_sq_add_mul_le (by positivity) hb hh.le)
    simp only [cornerMass, zero_pow two_ne_zero, mul_zero, add_zero]
    exact add_le_add_left (sub_le_self ((y3 + y4) ^ 2)
      (mul_nonneg (sq_nonneg la) (mul_nonneg h3.le h4.le))) (β * h)
  have h₃ : y3 ≤ 1 := by linarith only [hY, h4]
  have h₄ : y4 ≤ 1 := by linarith only [hY, h3]
  have hβ : β ≤ 1 / (1 - x) := by
    apply max_le
    · have hg : cornerG y3 y4 ≤ 1 := by
        unfold cornerG
        exact (mul_le_of_le_one_right h3.le (by linarith only [h3, h4])).trans h₃
      exact hg.trans ((le_div_iff₀ hx').2 (by linarith only [hx.1]))
    · apply div_le_div_of_nonneg_right _ hx'.le
      exact (mul_le_of_le_one_right (mul_nonneg h3.le h4.le) hx.2.le).trans
        ((mul_le_of_le_one_right h3.le h₄).trans h₃)
  have hxβ : (1 - x) * √β ≤ 1 := by
    have h := Real.sqrt_le_sqrt hβ
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one] at h
    refine (mul_le_mul_of_nonneg_left h hx'.le).trans ?_
    have hxroot := Real.sqrt_pos.2 hx'
    have e : (1 - x) * (1 / √(1 - x)) = √(1 - x) := by
      field_simp [hxroot.ne']
      exact (Real.sq_sqrt hx'.le).symm
    rw [e]
    simpa using Real.sqrt_le_sqrt (sub_le_self 1 hx.1.le)
  have hprod : W * √A ≤ 1 / √d := calc
    _ ≤ W * ((y3 + y4 + √β * √h) / √d) := mul_le_mul_of_nonneg_left hA' hW
    _ = (x / h * ((1 - x) * (y3 + y4)) +
        x / √h * ((1 - x) * √β)) / (2 * √d) := by
      dsimp only [W, cornerC0]
      field_simp [hh.ne', hh'.ne', hd'.ne']
      linear_combination √β * Real.sq_sqrt hh.le
    _ ≤ _ := by
      have hleft : x / h * ((1 - x) * (y3 + y4)) ≤ 1 := by
        have hxy : (1 - x) * (y3 + y4) ≤ 1 :=
          (mul_le_of_le_one_left (by positivity) (sub_le_self 1 hx.1.le)).trans hY.le
        exact (mul_le_of_le_one_left (by positivity) ((div_le_one hh).2 hhx)).trans hxy
      have hright : x / √h * ((1 - x) * √β) ≤ 1 :=
        (mul_le_of_le_one_left (by positivity) ((div_le_one hh').2 hroot)).trans hxβ
      apply (div_le_iff₀ (mul_pos two_pos hd')).2
      rw [show 1 / √d * (2 * √d) = 2 by field_simp]
      exact (add_le_add hleft hright).trans_eq (by norm_num)
  exact (abs_mul_photonTail_sub_le hmγ hreg hT hA).trans (by
    rw [abs_of_nonneg hW]
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num))
      (Real.sqrt_nonneg T)).trans_eq (by ring))

end QED.ChainProof.SetCRegDisp

end
