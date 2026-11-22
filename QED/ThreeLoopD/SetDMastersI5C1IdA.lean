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

* `QED.ThreeLoopD.i5C1_id1`, `QED.ThreeLoopD.i5C1_id2`, `QED.ThreeLoopD.i5C1_id6`,
  `QED.ThreeLoopD.i5C1_id7`, `QED.ThreeLoopD.i5C1_id9`.
-/

@[expose] public section

open Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- The dilogarithm of the argument of identity 1. -/
theorem i5C1B_dG1 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ ((ξ * x + (1 - ξ)))) (-(log ξ + log (1 - x)) *
        ((ξ / (ξ * x + (1 - ξ))))) x := by
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
  have e1 : 1 - ((ξ * x + (1 - ξ))) = ξ * (1 - x) := by field_simp; ring
  have eA : log (1 - ((ξ * x + (1 - ξ)))) = log ξ + log (1 - x) := by
    rw [e1, log_mul (by positivity) (by positivity)]
  have hlt : |(ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ ^ 2) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x))
  have hne : (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => (ξ * x + (1 - ξ))) d2 hne hlt eA ?_
  field_simp

theorem i5C1B_cG1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ ((ξ * x + (1 - ξ)))) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hf : ContinuousOn (fun x => (ξ * x + (1 - ξ))) (Ico 0 (1 - ξ)) := by fun_prop
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ (ξ * x + (1 - ξ)) ∧ (ξ * x + (1 - ξ)) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ (ξ * x + (1 - ξ)))], ?_⟩
  linear_combination (by positivity : (0 : ℝ) ≤ ξ ^ 2) + (by positivity : (0 : ℝ) ≤ ξ * (1 - ξ - x))

theorem i5C1B_zG1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ ((ξ * 0 + (1 - ξ))) = π ^ 2 / 6 - Li₂ ξ -
    log ξ * log (1 - ξ) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : (ξ * 0 + (1 - ξ)) = 1 - ξ := by simp
  rw [e, i5C1N_oneSub ⟨h0, h1⟩]

/-- The right side of the dilogarithm identity 1. -/
noncomputable def i5C1R1 (ξ x : ℝ) : ℝ :=
  -Li₂ (ξ * (1 - x)) - log (ξ * x + (1 - ξ)) * log (1 - x) - log (ξ * x + (1 - ξ)) * log ξ +
      (1 / 6) * π ^ 2

/-- **Dilogarithm identity 1** for `0 < x < 1 - ξ`. -/
theorem i5C1_id1 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((ξ * x + (1 - ξ))) = i5C1R1 ξ x := by
  have hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt (fun x => Li₂ ((ξ * x + (1 - ξ))) -
      i5C1R1 ξ x) 0 z := by
    intro z hz
    have e := (i5C1B_dG1 hξ hz.1 hz.2).sub (((((i5C1B_d3 hξ hz.1 hz.2).const_mul (-1)).add
        (((i5C1L_d2 hξ hz.1).mul (i5C1L_d3 hξ hz.2)).const_mul (-1))).add
        ((i5C1L_d2 hξ hz.1).const_mul ((-1) * log ξ))).add (hasDerivAt_const z ((1 / 6) * π ^ 2)))
    convert e using 1
    · funext x
      simp only [i5C1R1, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  have hc : ContinuousOn (fun x => Li₂ ((ξ * x + (1 - ξ))) - i5C1R1 ξ x) (Ico 0 (1 - ξ)) := by
    refine ((i5C1B_cG1 hξ).sub (((((continuousOn_const (c := ((-1) : ℝ))).mul (i5C1B_c3 hξ)).add
        ((continuousOn_const (c := ((-1) : ℝ))).mul ((i5C1L_c2 hξ).mul (i5C1L_c3 hξ)))).add
        ((continuousOn_const (c := (-1) * log ξ)).mul (i5C1L_c2 hξ))).add (continuousOn_const (c :=
        (1 / 6) * π ^ 2)))).congr fun x _ => ?_
    simp only [i5C1R1, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h0 : Li₂ ((ξ * 0 + (1 - ξ))) - i5C1R1 ξ 0 = 0 := by
    simp only [i5C1R1]
    rw [i5C1B_zG1 hξ, i5C1B_z3 hξ, i5C1L_z2, i5C1L_z3]
    ring
  exact sub_eq_zero.mp (i5C1_eq_of_deriv hc hd h0 hx hxy)

/-- The dilogarithm of the argument of identity 2. -/
theorem i5C1B_dG2 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ ((1 - ξ - x) / (1 - x))) (-(log ξ - log (1 - x)) *
        ((-1 / (1 - ξ - x)) - (-1 / (1 - x)))) x := by
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
  have e1 : 1 - ((1 - ξ - x) / (1 - x)) = ξ / (1 - x) := by field_simp; ring
  have eA : log (1 - ((1 - ξ - x) / (1 - x))) = log ξ - log (1 - x) := by
    rw [e1, log_div (by positivity) (by positivity)]
  have hlt : |(1 - ξ - x) / (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ)
  have hne : (1 - ξ - x) / (1 - x) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => (1 - ξ - x) / (1 - x)) (d1.div d3 l3.ne') hne hlt eA ?_
  field_simp

theorem i5C1B_cG2 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ ((1 - ξ - x) / (1 - x))) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (1 - x) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => (1 - ξ - x) / (1 - x)) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ (1 - ξ - x) / (1 - x) ∧ (1 - ξ - x) / (1 - x) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ (1 - ξ - x) / (1 - x))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ ξ)

theorem i5C1B_zG2 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ ((1 - ξ - 0) / (1 - 0)) = π ^ 2 / 6 -
    Li₂ ξ - log ξ * log (1 - ξ) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : (1 - ξ - 0) / (1 - 0) = 1 - ξ := by simp
  rw [e, i5C1N_oneSub ⟨h0, h1⟩]

/-- The right side of the dilogarithm identity 2. -/
noncomputable def i5C1R2 (ξ x : ℝ) : ℝ :=
  -Li₂ (ξ / (1 - x)) + log (1 - ξ - x) * log (1 - x) - log (1 - ξ - x) * log ξ - log (1 - x) *
      log (1 - x) + log (1 - x) * log ξ + (1 / 6) * π ^ 2

/-- **Dilogarithm identity 2** for `0 < x < 1 - ξ`. -/
theorem i5C1_id2 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((1 - ξ - x) / (1 - x)) = i5C1R2 ξ x := by
  have hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt (fun x => Li₂ ((1 - ξ - x) / (1 - x)) -
      i5C1R2 ξ x) 0 z := by
    intro z hz
    have e := (i5C1B_dG2 hξ hz.1 hz.2).sub (((((((i5C1B_d2 hξ hz.1 hz.2).const_mul (-1)).add
        (((i5C1L_d1 hz.2).mul (i5C1L_d3 hξ hz.2)).const_mul 1)).add
        ((i5C1L_d1 hz.2).const_mul ((-1) * log ξ))).add (((i5C1L_d3 hξ hz.2).mul
        (i5C1L_d3 hξ hz.2)).const_mul (-1))).add ((i5C1L_d3 hξ hz.2).const_mul (1 * log ξ))).add
        (hasDerivAt_const z ((1 / 6) * π ^ 2)))
    convert e using 1
    · funext x
      simp only [i5C1R2, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  have hc : ContinuousOn (fun x => Li₂ ((1 - ξ - x) / (1 - x)) - i5C1R2 ξ x) (Ico 0 (1 - ξ)) := by
    refine ((i5C1B_cG2 hξ).sub (((((((continuousOn_const (c := ((-1) : ℝ))).mul (i5C1B_c2 hξ)).add
        ((continuousOn_const (c := (1 : ℝ))).mul (i5C1L_c1.mul (i5C1L_c3 hξ)))).add
        ((continuousOn_const (c := (-1) * log ξ)).mul i5C1L_c1)).add ((continuousOn_const (c :=
        ((-1) : ℝ))).mul ((i5C1L_c3 hξ).mul (i5C1L_c3 hξ)))).add ((continuousOn_const (c := 1 *
        log ξ)).mul (i5C1L_c3 hξ))).add (continuousOn_const (c := (1 / 6) * π ^ 2)))).congr fun x _
        => ?_
    simp only [i5C1R2, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h0 : Li₂ ((1 - ξ - 0) / (1 - 0)) - i5C1R2 ξ 0 = 0 := by
    simp only [i5C1R2]
    rw [i5C1B_zG2 hξ, i5C1B_z2 hξ, i5C1L_z1, i5C1L_z3]
    ring
  exact sub_eq_zero.mp (i5C1_eq_of_deriv hc hd h0 hx hxy)

/-- The dilogarithm of the argument of identity 6. -/
theorem i5C1B_dG6 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ))) (-(log ξ - log (1 - ξ) +
        log (1 - ξ - x)) * ((ξ / (ξ * x + (1 - ξ) ^ 2)))) x := by
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
  have e1 : 1 - ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ)) = ξ * (1 - ξ - x) / (1 - ξ) := by field_simp; ring
  have eA : log (1 - ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ))) = log ξ - log (1 - ξ) +
      log (1 - ξ - x) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]; ring
  have hlt : |(ξ * x + (1 - ξ) ^ 2) / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * (1 - ξ - x))
  have hne : (ξ * x + (1 - ξ) ^ 2) / (1 - ξ) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => (ξ * x + (1 - ξ) ^ 2) / (1 -
      ξ)) (d4.div (hasDerivAt_const x ((1 - ξ))) hy.ne') hne hlt eA ?_
  field_simp; ring

theorem i5C1B_cG6 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ))) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (1 - ξ) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => (ξ * x + (1 - ξ) ^ 2) / (1 - ξ)) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ (ξ * x + (1 - ξ) ^ 2) / (1 - ξ) ∧ (ξ * x + (1 - ξ) ^ 2) / (1 - ξ) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ (ξ * x + (1 - ξ) ^ 2) / (1 - ξ))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ ξ * (1 - ξ - x))

theorem i5C1B_zG6 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ ((ξ * 0 + (1 - ξ) ^ 2) / (1 - ξ)) =
    π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : (ξ * 0 + (1 - ξ) ^ 2) / (1 - ξ) = 1 - ξ := by simp; field_simp
  rw [e, i5C1N_oneSub ⟨h0, h1⟩]

/-- The right side of the dilogarithm identity 6. -/
noncomputable def i5C1R6 (ξ x : ℝ) : ℝ :=
  -Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) - log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2) +
      log (1 - ξ - x) * log (1 - ξ) - log (ξ * x + (1 - ξ) ^ 2) * log ξ +
      log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) + log ξ * log (1 - ξ) - log (1 - ξ) * log (1 - ξ) +
      (1 / 6) * π ^ 2

/-- **Dilogarithm identity 6** for `0 < x < 1 - ξ`. -/
theorem i5C1_id6 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ)) = i5C1R6 ξ x := by
  have hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt (fun x => Li₂ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ)) -
      i5C1R6 ξ x) 0 z := by
    intro z hz
    have e := (i5C1B_dG6 hξ hz.1 hz.2).sub (((((((((i5C1B_d7 hξ hz.1 hz.2).const_mul (-1)).add
        (((i5C1L_d1 hz.2).mul (i5C1L_d4 hξ hz.1)).const_mul (-1))).add
        ((i5C1L_d1 hz.2).const_mul (1 * log (1 - ξ)))).add ((i5C1L_d4 hξ hz.1).const_mul ((-1) *
        log ξ))).add ((i5C1L_d4 hξ hz.1).const_mul (1 * log (1 - ξ)))).add (hasDerivAt_const z (1 *
        log ξ * log (1 - ξ)))).add (hasDerivAt_const z ((-1) * log (1 - ξ) * log (1 - ξ)))).add
        (hasDerivAt_const z ((1 / 6) * π ^ 2)))
    convert e using 1
    · funext x
      simp only [i5C1R6, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  have hc : ContinuousOn (fun x => Li₂ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ)) -
      i5C1R6 ξ x) (Ico 0 (1 - ξ)) := by
    refine ((i5C1B_cG6 hξ).sub (((((((((continuousOn_const (c := ((-1) : ℝ))).mul
        (i5C1B_c7 hξ)).add ((continuousOn_const (c := ((-1) : ℝ))).mul
        (i5C1L_c1.mul (i5C1L_c4 hξ)))).add ((continuousOn_const (c := 1 *
        log (1 - ξ))).mul i5C1L_c1)).add ((continuousOn_const (c := (-1) *
        log ξ)).mul (i5C1L_c4 hξ))).add ((continuousOn_const (c := 1 *
        log (1 - ξ))).mul (i5C1L_c4 hξ))).add (continuousOn_const (c := 1 * log ξ *
        log (1 - ξ)))).add (continuousOn_const (c := (-1) * log (1 - ξ) * log (1 - ξ)))).add
        (continuousOn_const (c := (1 / 6) * π ^ 2)))).congr fun x _ => ?_
    simp only [i5C1R6, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h0 : Li₂ ((ξ * 0 + (1 - ξ) ^ 2) / (1 - ξ)) - i5C1R6 ξ 0 = 0 := by
    simp only [i5C1R6]
    rw [i5C1B_zG6 hξ, i5C1B_z7 hξ, i5C1L_z1, i5C1L_z4]
    ring
  exact sub_eq_zero.mp (i5C1_eq_of_deriv hc hd h0 hx hxy)

/-- The dilogarithm of the argument of identity 7. -/
theorem i5C1B_dG7 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) (-(log ξ + log (1 - ξ) -
        log (ξ * x + (1 - ξ))) * (-(ξ / (ξ * x + (1 - ξ))) + (ξ / (ξ * x + (1 - ξ) ^ 2)))) x := by
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
  have e1 : 1 - ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) = ξ * (1 - ξ) / (ξ * x + (1 - ξ)) :=
      by field_simp; ring
  have eA : log (1 - ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) = log ξ + log (1 - ξ) -
      log (ξ * x + (1 - ξ)) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  have hlt : |(ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x))
  have hne : (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => (ξ * x + (1 - ξ) ^ 2) / (ξ * x +
      (1 - ξ))) (d4.div d2 l2.ne') hne hlt eA ?_
  field_simp; ring

theorem i5C1B_cG7 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (ξ * x + (1 - ξ)) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)) ∧ (ξ * x + (1 - ξ) ^ 2) / (ξ * x +
      (1 - ξ)) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ ξ * x) + (by positivity : (0 : ℝ) ≤ ξ * (1 - ξ - x))

theorem i5C1B_zG7 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ ((ξ * 0 + (1 - ξ) ^ 2) / (ξ * 0 +
    (1 - ξ))) = π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : (ξ * 0 + (1 - ξ) ^ 2) / (ξ * 0 + (1 - ξ)) = 1 - ξ := by simp; field_simp
  rw [e, i5C1N_oneSub ⟨h0, h1⟩]

/-- The right side of the dilogarithm identity 7. -/
noncomputable def i5C1R7 (ξ x : ℝ) : ℝ :=
  -Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) - log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) +
      log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) + log (ξ * x + (1 - ξ)) * log ξ +
      log (ξ * x + (1 - ξ)) * log (1 - ξ) - log (ξ * x + (1 - ξ) ^ 2) * log ξ -
      log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) + (1 / 6) * π ^ 2

/-- **Dilogarithm identity 7** for `0 < x < 1 - ξ`. -/
theorem i5C1_id7 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) = i5C1R7 ξ x := by
  have hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt (fun x => Li₂ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x +
      (1 - ξ))) - i5C1R7 ξ x) 0 z := by
    intro z hz
    have e := (i5C1B_dG7 hξ hz.1 hz.2).sub (((((((((i5C1B_d10 hξ hz.1 hz.2).const_mul (-1)).add
        (((i5C1L_d2 hξ hz.1).mul (i5C1L_d2 hξ hz.1)).const_mul (-1))).add
        (((i5C1L_d2 hξ hz.1).mul (i5C1L_d4 hξ hz.1)).const_mul 1)).add
        ((i5C1L_d2 hξ hz.1).const_mul (1 * log ξ))).add ((i5C1L_d2 hξ hz.1).const_mul (1 *
        log (1 - ξ)))).add ((i5C1L_d4 hξ hz.1).const_mul ((-1) * log ξ))).add
        ((i5C1L_d4 hξ hz.1).const_mul ((-1) * log (1 - ξ)))).add (hasDerivAt_const z ((1 / 6) *
        π ^ 2)))
    convert e using 1
    · funext x
      simp only [i5C1R7, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  have hc : ContinuousOn (fun x => Li₂ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) -
      i5C1R7 ξ x) (Ico 0 (1 - ξ)) := by
    refine ((i5C1B_cG7 hξ).sub (((((((((continuousOn_const (c := ((-1) : ℝ))).mul
        (i5C1B_c10 hξ)).add ((continuousOn_const (c := ((-1) : ℝ))).mul
        ((i5C1L_c2 hξ).mul (i5C1L_c2 hξ)))).add ((continuousOn_const (c :=
        (1 : ℝ))).mul ((i5C1L_c2 hξ).mul (i5C1L_c4 hξ)))).add ((continuousOn_const (c := 1 *
        log ξ)).mul (i5C1L_c2 hξ))).add ((continuousOn_const (c := 1 *
        log (1 - ξ))).mul (i5C1L_c2 hξ))).add ((continuousOn_const (c := (-1) *
        log ξ)).mul (i5C1L_c4 hξ))).add ((continuousOn_const (c := (-1) *
        log (1 - ξ))).mul (i5C1L_c4 hξ))).add (continuousOn_const (c := (1 / 6) * π ^ 2)))).congr
        fun x _ => ?_
    simp only [i5C1R7, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h0 : Li₂ ((ξ * 0 + (1 - ξ) ^ 2) / (ξ * 0 + (1 - ξ))) - i5C1R7 ξ 0 = 0 := by
    simp only [i5C1R7]
    rw [i5C1B_zG7 hξ, i5C1B_z10 hξ, i5C1L_z2, i5C1L_z4]
    ring
  exact sub_eq_zero.mp (i5C1_eq_of_deriv hc hd h0 hx hxy)

/-- The dilogarithm of the argument of identity 9. -/
theorem i5C1B_dG9 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (ξ * x / (ξ * x + (1 - ξ)))) (-(log (1 - ξ) - log (ξ * x + (1 - ξ))) *
        ((1 / x) - (ξ / (ξ * x + (1 - ξ))))) x := by
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
  have e1 : 1 - (ξ * x / (ξ * x + (1 - ξ))) = (1 - ξ) / (ξ * x + (1 - ξ)) := by field_simp; ring
  have eA : log (1 - (ξ * x / (ξ * x + (1 - ξ)))) = log (1 - ξ) - log (ξ * x + (1 - ξ)) := by
    rw [e1, log_div (by positivity) (by positivity)]
  have hlt : |ξ * x / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x) + (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : ξ * x / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => ξ * x / (ξ * x + (1 - ξ)))
      (((hasDerivAt_const x (ξ)).mul hid).div d2 l2.ne') hne hlt eA ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1B_cG9 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (ξ * x / (ξ * x + (1 - ξ)))) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (ξ * x + (1 - ξ)) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => ξ * x / (ξ * x + (1 - ξ))) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ ξ * x / (ξ * x + (1 - ξ)) ∧ ξ * x / (ξ * x + (1 - ξ)) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ ξ * x / (ξ * x + (1 - ξ)))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ x) + (by positivity : (0 : ℝ) ≤ (1 - ξ - x))

theorem i5C1B_zG9 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (ξ * 0 / (ξ * 0 + (1 - ξ))) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : ξ * 0 / (ξ * 0 + (1 - ξ)) = 0 := by simp
  rw [e, Li₂_zero]

/-- The right side of the dilogarithm identity 9. -/
noncomputable def i5C1R9 (ξ x : ℝ) : ℝ :=
  -Li₂ (-(ξ * x / (1 - ξ))) - (1 / 2) * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) +
      log (ξ * x + (1 - ξ)) * log (1 - ξ) - (1 / 2) * log (1 - ξ) * log (1 - ξ)

/-- **Dilogarithm identity 9** for `0 < x < 1 - ξ`. -/
theorem i5C1_id9 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ (ξ * x / (ξ * x + (1 - ξ))) = i5C1R9 ξ x := by
  have hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt (fun x => Li₂ (ξ * x / (ξ * x + (1 - ξ))) -
      i5C1R9 ξ x) 0 z := by
    intro z hz
    have e := (i5C1B_dG9 hξ hz.1 hz.2).sub (((((i5C1B_d4 hξ hz.1 hz.2).const_mul (-1)).add
        (((i5C1L_d2 hξ hz.1).mul (i5C1L_d2 hξ hz.1)).const_mul (-1 / 2))).add
        ((i5C1L_d2 hξ hz.1).const_mul (1 * log (1 - ξ)))).add (hasDerivAt_const z ((-1 / 2) *
        log (1 - ξ) * log (1 - ξ))))
    convert e using 1
    · funext x
      simp only [i5C1R9, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  have hc : ContinuousOn (fun x => Li₂ (ξ * x / (ξ * x + (1 - ξ))) -
      i5C1R9 ξ x) (Ico 0 (1 - ξ)) := by
    refine ((i5C1B_cG9 hξ).sub (((((continuousOn_const (c := ((-1) : ℝ))).mul (i5C1B_c4 hξ)).add
        ((continuousOn_const (c := ((-1 / 2) : ℝ))).mul ((i5C1L_c2 hξ).mul (i5C1L_c2 hξ)))).add
        ((continuousOn_const (c := 1 * log (1 - ξ))).mul (i5C1L_c2 hξ))).add
        (continuousOn_const (c := (-1 / 2) * log (1 - ξ) * log (1 - ξ))))).congr fun x _ => ?_
    simp only [i5C1R9, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h0 : Li₂ (ξ * 0 / (ξ * 0 + (1 - ξ))) - i5C1R9 ξ 0 = 0 := by
    simp only [i5C1R9]
    rw [i5C1B_zG9 hξ, i5C1B_z4 hξ, i5C1L_z2]
    ring
  exact sub_eq_zero.mp (i5C1_eq_of_deriv hc hd h0 hx hxy)

end QED.ThreeLoopD
