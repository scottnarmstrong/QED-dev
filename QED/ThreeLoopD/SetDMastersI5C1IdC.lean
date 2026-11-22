/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Bas

/-!
# Set (d), master `I₅`: two-variable dilogarithm identities

For `0 < ξ < 1`, `y = 1 - ξ` and `0 < x < y`, each dilogarithm `Li₂(h)` appearing in the derivative
of the trilogarithmic primitive of `I(x)` reduces to the fourteen-element dilogarithm basis of
`QED.ThreeLoopD.SetDMastersI5C1Bas` plus products of logarithms of the letters and a multiple of
`π²`. Each identity is proved by the constancy principle `QED.ThreeLoopD.i5C1_eq_of_deriv`: both
sides have the same derivative in `x` (a polynomial identity in the logarithms and the letter
derivatives) and the same value at `x = 0` (by the reflection, Landen and duplication formulas
in `ξ`).

## Main results

* `QED.ThreeLoopD.i5C1_id15`, `QED.ThreeLoopD.i5C1_id16`, `QED.ThreeLoopD.i5C1_id17`,
  `QED.ThreeLoopD.i5C1_id18`.
-/

@[expose] public section

open Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- The dilogarithm of the argument of identity 15. -/
theorem i5C1B_dG15 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))))) (-(-log (1 -
        ξ) - log (ξ * x + (1 - ξ)) + log (ξ * x ^ 2 + (1 - ξ) ^ 2)) *
        ((1 / x) + (-1 / (1 - ξ - x)) - (ξ / (ξ * x + (1 - ξ))))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have e1 : 1 - (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) =
      (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ))) := by field_simp; ring
  have eA : log (1 - (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))))) = -log (1 - ξ) -
      log (ξ * x + (1 - ξ)) + log (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]; ring
  have hlt : |ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  have hne : ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => ξ * x * (1 - ξ - x) / ((1 - ξ) *
      (ξ * x + (1 - ξ)))) ((((hasDerivAt_const x (ξ)).mul hid).mul d1).div
      ((hasDerivAt_const x ((1 - ξ))).mul d2) (mul_pos hy l2).ne') hne hlt eA ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1B_cG15 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))))) (Ico 0 (1 -
        ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (1 - ξ) * (ξ * x + (1 - ξ)) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) (Ico 0 (1 -
      ξ)) := ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))) ∧ ξ * x *
      (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ ξ * x * (1 - ξ - x) / ((1 - ξ) *
      (ξ * x + (1 - ξ))))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination 2 * (by positivity : (0 : ℝ) ≤ ξ * x ^ 2) + 2 *
      (by positivity : (0 : ℝ) ≤ ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ ξ *
      (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) ≤ x ^ 3) + 3 * (by positivity : (0 : ℝ) ≤ x ^ 2 *
      (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x) ^ 2) +
      (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 3)

theorem i5C1B_zG15 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (ξ * 0 *
    (1 - ξ - 0) / ((1 - ξ) * (ξ * 0 + (1 - ξ)))) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : ξ * 0 * (1 - ξ - 0) / ((1 - ξ) * (ξ * 0 + (1 - ξ))) = 0 := by simp
  rw [e, Li₂_zero]

/-- The right side of the dilogarithm identity 15. -/
noncomputable def i5C1R15 (ξ x : ℝ) : ℝ :=
  -(1 / 2) * Li₂ (x / (1 - ξ)) - (1 / 2) * Li₂ (-(ξ * x / (1 - ξ))) + (1 / 2) *
      Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) + (1 / 2) * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) -
      (1 / 2) * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) + (1 / 2) *
      Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) - (1 / 2) * log (1 - ξ - x) *
      log (ξ * x + (1 - ξ)) + (1 / 2) * log (1 - ξ - x) * log (1 - ξ) + (1 / 2) * log (1 - ξ - x) *
      log (1 + ξ) + (1 / 2) * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) - (1 / 2) *
      log (ξ * x + (1 - ξ)) * log (1 - ξ) - (1 / 2) * log (ξ * x + (1 - ξ)) * log (1 + ξ)

/-- **Dilogarithm identity 15** for `0 < x < 1 - ξ`. -/
theorem i5C1_id15 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) = i5C1R15 ξ x := by
  have hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt (fun x => Li₂ (ξ * x *
      (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) - i5C1R15 ξ x) 0 z := by
    intro z hz
    have e := (i5C1B_dG15 hξ hz.1 hz.2).sub (((((((((((((i5C1B_d1 hξ hz.1 hz.2).const_mul
        (-1 / 2)).add ((i5C1B_d4 hξ hz.1 hz.2).const_mul (-1 / 2))).add
        ((i5C1B_d6 hξ hz.1 hz.2).const_mul (1 / 2))).add ((i5C1B_d8 hξ hz.1 hz.2).const_mul
        (1 / 2))).add ((i5C1B_d11 hξ hz.1 hz.2).const_mul (-1 / 2))).add
        ((i5C1B_d12 hξ hz.1 hz.2).const_mul (1 / 2))).add (((i5C1L_d1 hz.2).mul
        (i5C1L_d2 hξ hz.1)).const_mul (-1 / 2))).add ((i5C1L_d1 hz.2).const_mul ((1 / 2) *
        log (1 - ξ)))).add ((i5C1L_d1 hz.2).const_mul ((1 / 2) * log (1 + ξ)))).add
        (((i5C1L_d2 hξ hz.1).mul (i5C1L_d2 hξ hz.1)).const_mul (1 / 2))).add
        ((i5C1L_d2 hξ hz.1).const_mul ((-1 / 2) * log (1 - ξ)))).add
        ((i5C1L_d2 hξ hz.1).const_mul ((-1 / 2) * log (1 + ξ))))
    convert e using 1
    · funext x
      simp only [i5C1R15, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  have hc : ContinuousOn (fun x => Li₂ (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) -
      i5C1R15 ξ x) (Ico 0 (1 - ξ)) := by
    refine ((i5C1B_cG15 hξ).sub (((((((((((((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul (i5C1B_c1 hξ)).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul (i5C1B_c4 hξ))).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c6 hξ))).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c8 hξ))).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul (i5C1B_c11 hξ))).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c12 hξ))).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul (i5C1L_c1.mul (i5C1L_c2 hξ)))).add ((continuousOn_const (c :=
        (1 / 2) * log (1 - ξ))).mul i5C1L_c1)).add ((continuousOn_const (c := (1 / 2) *
        log (1 + ξ))).mul i5C1L_c1)).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul ((i5C1L_c2 hξ).mul (i5C1L_c2 hξ)))).add ((continuousOn_const (c :=
        (-1 / 2) * log (1 - ξ))).mul (i5C1L_c2 hξ))).add ((continuousOn_const (c := (-1 / 2) *
        log (1 + ξ))).mul (i5C1L_c2 hξ)))).congr fun x _ => ?_
    simp only [i5C1R15, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h0 : Li₂ (ξ * 0 * (1 - ξ - 0) / ((1 - ξ) * (ξ * 0 + (1 - ξ)))) - i5C1R15 ξ 0 = 0 := by
    simp only [i5C1R15]
    rw [i5C1B_zG15 hξ, i5C1B_z1 hξ, i5C1B_z4 hξ, i5C1B_z6 hξ, i5C1B_z8 hξ, i5C1B_z11 hξ,
        i5C1B_z12 hξ, i5C1L_z1, i5C1L_z2]
    ring
  exact sub_eq_zero.mp (i5C1_eq_of_deriv hc hd h0 hx hxy)

/-- The dilogarithm of the argument of identity 16. -/
theorem i5C1B_dG16 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)))) (-(-log (1 -
        ξ) - log (1 + ξ) + log (1 - ξ - x) - log (1 - x)) * ((ξ / (ξ * x + (1 - ξ))) -
        (-1 / (1 - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have e1 : 1 - (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))) =
      (1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x)) := by field_simp; ring
  have eA : log (1 - (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)))) = -log (1 - ξ) -
      log (1 + ξ) + log (1 - ξ - x) - log (1 - x) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity)]; ring
  have hlt : |ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) *
      (1 - x))) (((hasDerivAt_const x (ξ)).mul d2).div (((hasDerivAt_const x ((1 - ξ))).mul
      (hasDerivAt_const x ((1 + ξ)))).mul d3) (mul_pos (mul_pos hy h1p) l3).ne') hne hlt eA ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1B_cG16 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)))) (Ico 0 (1 -
        ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (1 - ξ) * (1 + ξ) * (1 - x) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) *
      (1 - x))) (Ico 0 (1 - ξ)) := ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)) ∧ ξ *
      (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) *
      (1 - x)))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ (1 - ξ - x))

theorem i5C1B_zG16 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (ξ * (ξ * 0 + (1 - ξ)) / ((1 - ξ) *
    (1 + ξ) * (1 - 0))) = -Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : ξ * (ξ * 0 + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - 0)) = ξ / (1 + ξ) :=
      by simp; field_simp
  rw [e, i5C1N_div ⟨h0, h1⟩]

/-- The right side of the dilogarithm identity 16. -/
noncomputable def i5C1R16 (ξ x : ℝ) : ℝ :=
  -2 * Li₂ (x) + 2 * Li₂ (x / (1 - ξ)) + Li₂ (ξ / (1 - x)) - Li₂ (ξ * (1 - x)) + 2 *
      Li₂ (x / (ξ * x + (1 - ξ))) - 2 * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) -
      Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) + log (1 - ξ - x) * log (ξ * x + (1 - ξ)) -
      log (1 - ξ - x) * log (1 - ξ) - log (1 - ξ - x) * log (1 + ξ) - (1 / 2) *
      log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) - log (ξ * x + (1 - ξ)) * log (1 - x) + 2 *
      log (ξ * x + (1 - ξ)) * log (1 + ξ) - log (1 - x) * log (1 - ξ) - log (1 - x) * log (1 + ξ) +
      (1 / 2) * log (1 - ξ) * log (1 - ξ) - log (1 - ξ) * log (1 + ξ) - (1 / 2) * log (1 + ξ) *
      log (1 + ξ)

/-- **Dilogarithm identity 16** for `0 < x < 1 - ξ`. -/
theorem i5C1_id16 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))) = i5C1R16 ξ x := by
  have hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt (fun x => Li₂ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) *
      (1 + ξ) * (1 - x))) - i5C1R16 ξ x) 0 z := by
    intro z hz
    have e := (i5C1B_dG16 hξ hz.1 hz.2).sub (((((((((((((((((((i5C1B_d0 hξ hz.1 hz.2).const_mul
        (-2)).add ((i5C1B_d1 hξ hz.1 hz.2).const_mul 2)).add ((i5C1B_d2 hξ hz.1 hz.2).const_mul
        1)).add ((i5C1B_d3 hξ hz.1 hz.2).const_mul (-1))).add ((i5C1B_d5 hξ hz.1 hz.2).const_mul
        2)).add ((i5C1B_d8 hξ hz.1 hz.2).const_mul (-2))).add ((i5C1B_d11 hξ hz.1 hz.2).const_mul
        (-1))).add (((i5C1L_d1 hz.2).mul (i5C1L_d2 hξ hz.1)).const_mul 1)).add
        ((i5C1L_d1 hz.2).const_mul ((-1) * log (1 - ξ)))).add ((i5C1L_d1 hz.2).const_mul ((-1) *
        log (1 + ξ)))).add (((i5C1L_d2 hξ hz.1).mul (i5C1L_d2 hξ hz.1)).const_mul (-1 / 2))).add
        (((i5C1L_d2 hξ hz.1).mul (i5C1L_d3 hξ hz.2)).const_mul (-1))).add
        ((i5C1L_d2 hξ hz.1).const_mul (2 * log (1 + ξ)))).add ((i5C1L_d3 hξ hz.2).const_mul ((-1) *
        log (1 - ξ)))).add ((i5C1L_d3 hξ hz.2).const_mul ((-1) * log (1 + ξ)))).add
        (hasDerivAt_const z ((1 / 2) * log (1 - ξ) * log (1 - ξ)))).add (hasDerivAt_const z ((-1) *
        log (1 - ξ) * log (1 + ξ)))).add (hasDerivAt_const z ((-1 / 2) * log (1 + ξ) *
        log (1 + ξ))))
    convert e using 1
    · funext x
      simp only [i5C1R16, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  have hc : ContinuousOn (fun x => Li₂ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))) -
      i5C1R16 ξ x) (Ico 0 (1 - ξ)) := by
    refine ((i5C1B_cG16 hξ).sub (((((((((((((((((((continuousOn_const (c :=
        ((-2) : ℝ))).mul (i5C1B_c0 hξ)).add ((continuousOn_const (c :=
        (2 : ℝ))).mul (i5C1B_c1 hξ))).add ((continuousOn_const (c :=
        (1 : ℝ))).mul (i5C1B_c2 hξ))).add ((continuousOn_const (c :=
        ((-1) : ℝ))).mul (i5C1B_c3 hξ))).add ((continuousOn_const (c :=
        (2 : ℝ))).mul (i5C1B_c5 hξ))).add ((continuousOn_const (c :=
        ((-2) : ℝ))).mul (i5C1B_c8 hξ))).add ((continuousOn_const (c :=
        ((-1) : ℝ))).mul (i5C1B_c11 hξ))).add ((continuousOn_const (c :=
        (1 : ℝ))).mul (i5C1L_c1.mul (i5C1L_c2 hξ)))).add ((continuousOn_const (c := (-1) *
        log (1 - ξ))).mul i5C1L_c1)).add ((continuousOn_const (c := (-1) *
        log (1 + ξ))).mul i5C1L_c1)).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul ((i5C1L_c2 hξ).mul (i5C1L_c2 hξ)))).add ((continuousOn_const (c :=
        ((-1) : ℝ))).mul ((i5C1L_c2 hξ).mul (i5C1L_c3 hξ)))).add ((continuousOn_const (c := 2 *
        log (1 + ξ))).mul (i5C1L_c2 hξ))).add ((continuousOn_const (c := (-1) *
        log (1 - ξ))).mul (i5C1L_c3 hξ))).add ((continuousOn_const (c := (-1) *
        log (1 + ξ))).mul (i5C1L_c3 hξ))).add (continuousOn_const (c := (1 / 2) * log (1 - ξ) *
        log (1 - ξ)))).add (continuousOn_const (c := (-1) * log (1 - ξ) * log (1 + ξ)))).add
        (continuousOn_const (c := (-1 / 2) * log (1 + ξ) * log (1 + ξ))))).congr fun x _ => ?_
    simp only [i5C1R16, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h0 : Li₂ (ξ * (ξ * 0 + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - 0))) - i5C1R16 ξ 0 = 0 := by
    simp only [i5C1R16]
    rw [i5C1B_zG16 hξ, i5C1B_z0 hξ, i5C1B_z1 hξ, i5C1B_z2 hξ, i5C1B_z3 hξ, i5C1B_z5 hξ,
        i5C1B_z8 hξ, i5C1B_z11 hξ, i5C1L_z1, i5C1L_z2, i5C1L_z3]
    ring
  exact sub_eq_zero.mp (i5C1_eq_of_deriv hc hd h0 hx hxy)

/-- The dilogarithm of the argument of identity 17. -/
theorem i5C1B_dG17 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (-(log (1 - ξ) +
        log (1 - ξ - x) - log (ξ * x ^ 2 + (1 - ξ) ^ 2)) * ((1 / x) + (ξ / (ξ * x + (1 - ξ))) -
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have e1 : 1 - (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) = (1 - ξ) *
      (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2) := by field_simp; ring
  have eA : log (1 - (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) = log (1 - ξ) +
      log (1 - ξ - x) - log (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  have hlt : |x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 +
      (1 - ξ) ^ 2)) ((hid.mul d2).div d5 l5.ne') hne hlt eA ?_
  simp only [Pi.mul_apply]; field_simp

theorem i5C1B_cG17 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (Ico 0 (1 -
        ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (ξ * x ^ 2 + (1 - ξ) ^ 2) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) (Ico 0 (1 -
      ξ)) := ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2) ∧ x *
      (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 +
      (1 - ξ) ^ 2))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x)) +
      (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 2)

theorem i5C1B_zG17 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (0 * (ξ * 0 + (1 - ξ)) / (ξ * 0 ^ 2 +
    (1 - ξ) ^ 2)) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : 0 * (ξ * 0 + (1 - ξ)) / (ξ * 0 ^ 2 + (1 - ξ) ^ 2) = 0 := by simp
  rw [e, Li₂_zero]

/-- The right side of the dilogarithm identity 17. -/
noncomputable def i5C1R17 (ξ x : ℝ) : ℝ :=
  (1 / 2) * Li₂ (x / (1 - ξ)) + (1 / 2) * Li₂ (-(ξ * x / (1 - ξ))) - (1 / 2) *
      Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) + (1 / 2) * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) -
      (1 / 2) * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) + (1 / 2) *
      Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) - (3 / 2) * log (1 - ξ - x) *
      log (ξ * x + (1 - ξ)) + log (1 - ξ - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) - (1 / 2) *
      log (1 - ξ - x) * log (1 - ξ) + (1 / 2) * log (1 - ξ - x) * log (1 + ξ) +
      log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) - (1 / 2) * log (ξ * x + (1 - ξ)) *
      log (1 - ξ) - (1 / 2) * log (ξ * x + (1 - ξ)) * log (1 + ξ) - (1 / 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) +
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) - (1 / 2) * log (1 - ξ) * log (1 - ξ)

/-- **Dilogarithm identity 17** for `0 < x < 1 - ξ`. -/
theorem i5C1_id17 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) = i5C1R17 ξ x := by
  have hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt (fun x => Li₂ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 +
      (1 - ξ) ^ 2)) - i5C1R17 ξ x) 0 z := by
    intro z hz
    have e := (i5C1B_dG17 hξ hz.1 hz.2).sub (((((((((((((((((i5C1B_d1 hξ hz.1 hz.2).const_mul
        (1 / 2)).add ((i5C1B_d4 hξ hz.1 hz.2).const_mul (1 / 2))).add
        ((i5C1B_d6 hξ hz.1 hz.2).const_mul (-1 / 2))).add ((i5C1B_d8 hξ hz.1 hz.2).const_mul
        (1 / 2))).add ((i5C1B_d11 hξ hz.1 hz.2).const_mul (-1 / 2))).add
        ((i5C1B_d12 hξ hz.1 hz.2).const_mul (1 / 2))).add (((i5C1L_d1 hz.2).mul
        (i5C1L_d2 hξ hz.1)).const_mul (-3 / 2))).add (((i5C1L_d1 hz.2).mul (i5C1L_d5 hξ)).const_mul
        1)).add ((i5C1L_d1 hz.2).const_mul ((-1 / 2) * log (1 - ξ)))).add
        ((i5C1L_d1 hz.2).const_mul ((1 / 2) * log (1 + ξ)))).add (((i5C1L_d2 hξ hz.1).mul
        (i5C1L_d2 hξ hz.1)).const_mul 1)).add ((i5C1L_d2 hξ hz.1).const_mul ((-1 / 2) *
        log (1 - ξ)))).add ((i5C1L_d2 hξ hz.1).const_mul ((-1 / 2) * log (1 + ξ)))).add
        (((i5C1L_d5 hξ).mul (i5C1L_d5 hξ)).const_mul (-1 / 2))).add ((i5C1L_d5 hξ).const_mul (1 *
        log (1 - ξ)))).add (hasDerivAt_const z ((-1 / 2) * log (1 - ξ) * log (1 - ξ))))
    convert e using 1
    · funext x
      simp only [i5C1R17, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  have hc : ContinuousOn (fun x => Li₂ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) -
      i5C1R17 ξ x) (Ico 0 (1 - ξ)) := by
    refine ((i5C1B_cG17 hξ).sub (((((((((((((((((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c1 hξ)).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c4 hξ))).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul (i5C1B_c6 hξ))).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c8 hξ))).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul (i5C1B_c11 hξ))).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c12 hξ))).add ((continuousOn_const (c :=
        ((-3 / 2) : ℝ))).mul (i5C1L_c1.mul (i5C1L_c2 hξ)))).add ((continuousOn_const (c :=
        (1 : ℝ))).mul (i5C1L_c1.mul (i5C1L_c5 hξ)))).add ((continuousOn_const (c := (-1 / 2) *
        log (1 - ξ))).mul i5C1L_c1)).add ((continuousOn_const (c := (1 / 2) *
        log (1 + ξ))).mul i5C1L_c1)).add ((continuousOn_const (c :=
        (1 : ℝ))).mul ((i5C1L_c2 hξ).mul (i5C1L_c2 hξ)))).add ((continuousOn_const (c := (-1 / 2) *
        log (1 - ξ))).mul (i5C1L_c2 hξ))).add ((continuousOn_const (c := (-1 / 2) *
        log (1 + ξ))).mul (i5C1L_c2 hξ))).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul ((i5C1L_c5 hξ).mul (i5C1L_c5 hξ)))).add ((continuousOn_const (c := 1 *
        log (1 - ξ))).mul (i5C1L_c5 hξ))).add (continuousOn_const (c := (-1 / 2) * log (1 - ξ) *
        log (1 - ξ))))).congr fun x _ => ?_
    simp only [i5C1R17, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h0 : Li₂ (0 * (ξ * 0 + (1 - ξ)) / (ξ * 0 ^ 2 + (1 - ξ) ^ 2)) - i5C1R17 ξ 0 = 0 := by
    simp only [i5C1R17]
    rw [i5C1B_zG17 hξ, i5C1B_z1 hξ, i5C1B_z4 hξ, i5C1B_z6 hξ, i5C1B_z8 hξ, i5C1B_z11 hξ,
        i5C1B_z12 hξ, i5C1L_z1, i5C1L_z2, i5C1L_z5]
    ring
  exact sub_eq_zero.mp (i5C1_eq_of_deriv hc hd h0 hx hxy)

/-- The dilogarithm of the argument of identity 18. -/
theorem i5C1B_dG18 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) (-(log (1 - ξ) +
        log (ξ * x + (1 - ξ)) - log (ξ * x ^ 2 + (1 - ξ) ^ 2)) * ((1 / x) + (-1 / (1 - ξ - x)) -
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have e1 : 1 - (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) = (1 - ξ) *
      (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2) := by field_simp; ring
  have eA : log (1 - (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) = log (1 - ξ) +
      log (ξ * x + (1 - ξ)) - log (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  have hlt : |-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x ^ 2) +
        (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  have hne : -(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) ≠ 0 :=
      neg_ne_zero.mpr (by positivity)
  refine i5C1_hasDerivAt_Li₂ (f := fun x => -(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))
      (((((hasDerivAt_const x (ξ)).mul hid).mul d1).div d5 l5.ne').neg) hne hlt eA ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1B_cG18 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) (Ico 0 (1 -
        ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (ξ * x ^ 2 + (1 - ξ) ^ 2) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => -(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (Ico 0 (1 -
      ξ)) := (ContinuousOn.div (by fun_prop) (by fun_prop) hD).neg
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ -(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) ∧ -(ξ * x *
      (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) ≤ 1
  refine ⟨neg_le_neg ?_, by linarith [(by positivity : (0 : ℝ) ≤ ξ * x *
      (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))]⟩
  rw [div_le_one (by positivity)]
  linear_combination 2 * (by positivity : (0 : ℝ) ≤ ξ * x ^ 2) + (by positivity : (0 : ℝ) ≤ ξ * x *
      (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ ξ * (1 - ξ - x) ^ 2) +
      (by positivity : (0 : ℝ) ≤ x ^ 3) + 3 * (by positivity : (0 : ℝ) ≤ x ^ 2 * (1 - ξ - x)) + 3 *
      (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 3)

theorem i5C1B_zG18 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (-(ξ * 0 *
    (1 - ξ - 0) / (ξ * 0 ^ 2 + (1 - ξ) ^ 2))) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : -(ξ * 0 * (1 - ξ - 0) / (ξ * 0 ^ 2 + (1 - ξ) ^ 2)) = 0 := by simp
  rw [e, Li₂_zero]

/-- The right side of the dilogarithm identity 18. -/
noncomputable def i5C1R18 (ξ x : ℝ) : ℝ :=
  (1 / 2) * Li₂ (x / (1 - ξ)) + (1 / 2) * Li₂ (-(ξ * x / (1 - ξ))) - (1 / 2) *
      Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) - (1 / 2) * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) +
      (1 / 2) * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) - (1 / 2) *
      Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) + (1 / 2) * log (1 - ξ - x) *
      log (ξ * x + (1 - ξ)) - (1 / 2) * log (1 - ξ - x) * log (1 - ξ) - (1 / 2) * log (1 - ξ - x) *
      log (1 + ξ) - log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) + log (ξ * x + (1 - ξ)) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) - (1 / 2) * log (ξ * x + (1 - ξ)) * log (1 - ξ) + (1 / 2) *
      log (ξ * x + (1 - ξ)) * log (1 + ξ) - (1 / 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) + log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) - (1 / 2) *
      log (1 - ξ) * log (1 - ξ)

/-- **Dilogarithm identity 18** for `0 < x < 1 - ξ`. -/
theorem i5C1_id18 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) = i5C1R18 ξ x := by
  have hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt (fun x => Li₂ (-(ξ * x *
      (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) - i5C1R18 ξ x) 0 z := by
    intro z hz
    have e := (i5C1B_dG18 hξ hz.1 hz.2).sub (((((((((((((((((i5C1B_d1 hξ hz.1 hz.2).const_mul
        (1 / 2)).add ((i5C1B_d4 hξ hz.1 hz.2).const_mul (1 / 2))).add
        ((i5C1B_d6 hξ hz.1 hz.2).const_mul (-1 / 2))).add ((i5C1B_d8 hξ hz.1 hz.2).const_mul
        (-1 / 2))).add ((i5C1B_d11 hξ hz.1 hz.2).const_mul (1 / 2))).add
        ((i5C1B_d12 hξ hz.1 hz.2).const_mul (-1 / 2))).add (((i5C1L_d1 hz.2).mul
        (i5C1L_d2 hξ hz.1)).const_mul (1 / 2))).add ((i5C1L_d1 hz.2).const_mul ((-1 / 2) *
        log (1 - ξ)))).add ((i5C1L_d1 hz.2).const_mul ((-1 / 2) * log (1 + ξ)))).add
        (((i5C1L_d2 hξ hz.1).mul (i5C1L_d2 hξ hz.1)).const_mul (-1))).add
        (((i5C1L_d2 hξ hz.1).mul (i5C1L_d5 hξ)).const_mul 1)).add
        ((i5C1L_d2 hξ hz.1).const_mul ((-1 / 2) * log (1 - ξ)))).add
        ((i5C1L_d2 hξ hz.1).const_mul ((1 / 2) * log (1 + ξ)))).add
        (((i5C1L_d5 hξ).mul (i5C1L_d5 hξ)).const_mul (-1 / 2))).add ((i5C1L_d5 hξ).const_mul (1 *
        log (1 - ξ)))).add (hasDerivAt_const z ((-1 / 2) * log (1 - ξ) * log (1 - ξ))))
    convert e using 1
    · funext x
      simp only [i5C1R18, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  have hc : ContinuousOn (fun x => Li₂ (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) -
      i5C1R18 ξ x) (Ico 0 (1 - ξ)) := by
    refine ((i5C1B_cG18 hξ).sub (((((((((((((((((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c1 hξ)).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c4 hξ))).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul (i5C1B_c6 hξ))).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul (i5C1B_c8 hξ))).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1B_c11 hξ))).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul (i5C1B_c12 hξ))).add ((continuousOn_const (c :=
        ((1 / 2) : ℝ))).mul (i5C1L_c1.mul (i5C1L_c2 hξ)))).add ((continuousOn_const (c :=
        (-1 / 2) * log (1 - ξ))).mul i5C1L_c1)).add ((continuousOn_const (c := (-1 / 2) *
        log (1 + ξ))).mul i5C1L_c1)).add ((continuousOn_const (c :=
        ((-1) : ℝ))).mul ((i5C1L_c2 hξ).mul (i5C1L_c2 hξ)))).add ((continuousOn_const (c :=
        (1 : ℝ))).mul ((i5C1L_c2 hξ).mul (i5C1L_c5 hξ)))).add ((continuousOn_const (c := (-1 / 2) *
        log (1 - ξ))).mul (i5C1L_c2 hξ))).add ((continuousOn_const (c := (1 / 2) *
        log (1 + ξ))).mul (i5C1L_c2 hξ))).add ((continuousOn_const (c :=
        ((-1 / 2) : ℝ))).mul ((i5C1L_c5 hξ).mul (i5C1L_c5 hξ)))).add ((continuousOn_const (c := 1 *
        log (1 - ξ))).mul (i5C1L_c5 hξ))).add (continuousOn_const (c := (-1 / 2) * log (1 - ξ) *
        log (1 - ξ))))).congr fun x _ => ?_
    simp only [i5C1R18, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h0 : Li₂ (-(ξ * 0 * (1 - ξ - 0) / (ξ * 0 ^ 2 + (1 - ξ) ^ 2))) - i5C1R18 ξ 0 = 0 := by
    simp only [i5C1R18]
    rw [i5C1B_zG18 hξ, i5C1B_z1 hξ, i5C1B_z4 hξ, i5C1B_z6 hξ, i5C1B_z8 hξ, i5C1B_z11 hξ,
        i5C1B_z12 hξ, i5C1L_z1, i5C1L_z2, i5C1L_z5]
    ring
  exact sub_eq_zero.mp (i5C1_eq_of_deriv hc hd h0 hx hxy)

end QED.ThreeLoopD
