/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Deriv
public import QED.Polylog.Reflection
public import QED.Polylog.Landen
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Set (d), master `I₅`: the dilogarithm basis of the primitive of `I(x)`

For `0 < ξ < 1`, `y = 1 - ξ`, the letters `x, y - x, ξ x + y, 1 - x, ξ x + y², ξ x² + y²` and
the constants `ξ, y, 1 + ξ` are positive on `0 < x < y`. For each of the fourteen dilogarithm
arguments `b_j` of the basis of the primitive of `I(x)` this file proves the derivative of
`Li₂ (b_j x)` in letter form (`log (1 - b_j)` is a sum of logarithms of letters and `b_j'/b_j` a
combination of the letter derivatives), and the continuity of `Li₂ (b_j x)` on `[0, y)`
(`b_j ∈ [-1, 1]` there, proved by a certificate with nonnegative coefficients in the
barycentric coordinates `ξ, x, y - x`). It also proves the constancy principle used for the
two-variable dilogarithm identities (`QED.ThreeLoopD.i5C1_eq_of_deriv`).

## Main results

* `QED.ThreeLoopD.i5C1_eq_of_deriv`.
* `QED.ThreeLoopD.i5C1B_d0`, ..., `QED.ThreeLoopD.i5C1B_d13` and
  `QED.ThreeLoopD.i5C1B_c0`, ..., `QED.ThreeLoopD.i5C1B_c13`.
-/

@[expose] public section

open Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- The chain rule for `Li₂ ∘ f` with `log (1 - f x)` and `f' / f x` named. -/
theorem i5C1_hasDerivAt_Li₂ {f : ℝ → ℝ} {f' x A D : ℝ} (hf : HasDerivAt f f' x)
    (h0 : f x ≠ 0) (h1 : |f x| < 1) (hA : log (1 - f x) = A) (hD : f' / f x = D) :
    HasDerivAt (fun x => Li₂ (f x)) (-A * D) x := by
  have := (hasDerivAt_Li₂ h1 h0).comp x hf
  rw [hA] at this
  refine this.congr_deriv ?_
  rw [← hD]
  ring

/-- Continuity of `Li₂ ∘ f` where `f` takes values in `[-1, 1]`. -/
theorem i5C1_contLi₂ {f : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (h : ∀ x ∈ s, -1 ≤ f x ∧ f x ≤ 1) : ContinuousOn (fun x => Li₂ (f x)) s :=
  continuousOn_Li₂.comp hf fun x hx => h x hx

/-- **Constancy principle**: a function continuous on `[0, y)` with zero derivative on `(0, y)`
and value `0` at `0` vanishes on `(0, y)`. -/
theorem i5C1_eq_of_deriv {ξ : ℝ} {G : ℝ → ℝ} (hc : ContinuousOn G (Ico 0 (1 - ξ)))
    (hd : ∀ z ∈ Ioo 0 (1 - ξ), HasDerivAt G 0 z) (h0 : G 0 = 0) {x : ℝ} (hx : 0 < x)
    (hxy : x < 1 - ξ) : G x = 0 := by
  obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope G (fun _ => 0) hx
    (hc.mono (Icc_subset_Ico_right hxy)) fun z hz => hd z ⟨hz.1, hz.2.trans hxy⟩
  have := hc2.symm
  rw [div_eq_zero_iff, sub_eq_zero, h0] at this
  rcases this with h | h
  · exact h
  · linarith

/-! ### Logarithms of the letters -/

section Letters

variable {ξ x : ℝ}

theorem i5C1L_d0 (hx : 0 < x) : HasDerivAt (fun x => log x) (1 / x) x := by
  simpa [one_div] using hasDerivAt_log hx.ne'

theorem i5C1L_d1 (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => log (1 - ξ - x)) (-1 / (1 - ξ - x)) x := by
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub (1 - ξ)
  exact d1.log (by linarith)

theorem i5C1L_d2 (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    HasDerivAt (fun x => log (ξ * x + (1 - ξ))) (ξ / (ξ * x + (1 - ξ))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using ((hasDerivAt_id' x).const_mul ξ).add_const (1 - ξ)
  exact d2.log (by positivity)

theorem i5C1L_d3 (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => log (1 - x)) (-1 / (1 - x)) x := by
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  exact d3.log (by linarith [hξ.1])

theorem i5C1L_d4 (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    HasDerivAt (fun x => log (ξ * x + (1 - ξ) ^ 2)) (ξ / (ξ * x + (1 - ξ) ^ 2)) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using ((hasDerivAt_id' x).const_mul ξ).add_const ((1 - ξ) ^ 2)
  exact d4.log (by positivity)

theorem i5C1L_d5 (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => log (ξ * x ^ 2 + (1 - ξ) ^ 2))
      (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using (((hasDerivAt_id' x).pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  exact d5.log (by positivity)

theorem i5C1L_c1 : ContinuousOn (fun x => log (1 - ξ - x)) (Ico 0 (1 - ξ)) :=
  ContinuousOn.log (by fun_prop) fun x hx => by linarith [hx.2]

theorem i5C1L_c2 (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => log (ξ * x + (1 - ξ))) (Ico 0 (1 - ξ)) :=
  ContinuousOn.log (by fun_prop) fun x hx => by
    nlinarith [hx.1, hx.2, hξ.1, hξ.2, mul_nonneg hξ.1.le hx.1]

theorem i5C1L_c3 (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => log (1 - x)) (Ico 0 (1 - ξ)) :=
  ContinuousOn.log (by fun_prop) fun x hx => by linarith [hx.2, hξ.1]

theorem i5C1L_c4 (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => log (ξ * x + (1 - ξ) ^ 2)) (Ico 0 (1 - ξ)) :=
  ContinuousOn.log (by fun_prop) fun x hx => by
    have := mul_nonneg hξ.1.le hx.1
    have := pow_pos (sub_pos.mpr hξ.2) 2
    linarith

theorem i5C1L_c5 (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => log (ξ * x ^ 2 + (1 - ξ) ^ 2)) (Ico 0 (1 - ξ)) :=
  ContinuousOn.log (by fun_prop) fun x _ => by
    have := mul_nonneg hξ.1.le (sq_nonneg x)
    have := pow_pos (sub_pos.mpr hξ.2) 2
    linarith

theorem i5C1L_z1 : log (1 - ξ - 0) = log (1 - ξ) := by rw [sub_zero]

theorem i5C1L_z2 : log (ξ * 0 + (1 - ξ)) = log (1 - ξ) := by rw [mul_zero, zero_add]

theorem i5C1L_z3 : log (1 - 0) = 0 := by rw [sub_zero, log_one]

theorem i5C1L_z4 : log (ξ * 0 + (1 - ξ) ^ 2) = 2 * log (1 - ξ) := by
  rw [mul_zero, zero_add, log_pow]
  push_cast
  ring

theorem i5C1L_z5 : log (ξ * 0 ^ 2 + (1 - ξ) ^ 2) = 2 * log (1 - ξ) := by
  rw [zero_pow two_ne_zero, mul_zero, zero_add, log_pow]
  push_cast
  ring

end Letters

/-! ### One-variable values at `x = 0` -/

theorem i5C1N_oneSub {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Li₂ (1 - ξ) = π ^ 2 / 6 - Li₂ ξ - log ξ * log (1 - ξ) := by
  have := Li₂_add_Li₂_one_sub hξ.1.le hξ.2.le
  linarith

theorem i5C1N_div {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Li₂ (ξ / (1 + ξ)) = -Li₂ (-ξ) - log (1 + ξ) ^ 2 / 2 := by
  obtain ⟨h0, h1⟩ := hξ
  have h := Li₂_one_sub_inv_add_Li₂_one_sub (x := 1 / (1 + ξ))
    (by rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith)
    (by rw [div_le_one (by linarith)]; linarith)
  rw [show 1 - (1 / (1 + ξ))⁻¹ = -ξ by field_simp; ring,
    show 1 - 1 / (1 + ξ) = ξ / (1 + ξ) by field_simp; ring, one_div, log_inv] at h
  linarith

theorem i5C1N_sq {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Li₂ (ξ ^ 2) = 2 * Li₂ ξ + 2 * Li₂ (-ξ) := by
  have := Li₂_add_Li₂_neg (x := ξ) (by rw [abs_of_pos hξ.1]; exact hξ.2.le)
  linarith

theorem i5C1N_inv {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Li₂ (1 / (1 + ξ)) =
      π ^ 2 / 6 + Li₂ (-ξ) + log (1 + ξ) ^ 2 / 2 + log (1 + ξ) * (log ξ - log (1 + ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have h := Li₂_add_Li₂_one_sub (x := ξ / (1 + ξ)) (by positivity)
    (by rw [div_le_one (by linarith)]; linarith)
  rw [show 1 - ξ / (1 + ξ) = 1 / (1 + ξ) by field_simp; ring, i5C1N_div ⟨h0, h1⟩,
    log_div h0.ne' (by linarith)] at h
  rw [one_div, log_inv] at h
  rw [one_div]
  linarith

theorem i5C1N_oneSubSq {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    Li₂ (1 - ξ ^ 2) =
      π ^ 2 / 6 - 2 * Li₂ ξ - 2 * Li₂ (-ξ) - 2 * log ξ * (log (1 - ξ) + log (1 + ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have h := Li₂_add_Li₂_one_sub (x := ξ ^ 2) (by positivity) (by nlinarith)
  rw [i5C1N_sq ⟨h0, h1⟩, show 1 - ξ ^ 2 = (1 - ξ) * (1 + ξ) by ring,
    log_mul (by linarith) (by linarith), log_pow] at h
  rw [show 1 - ξ ^ 2 = (1 - ξ) * (1 + ξ) by ring]
  push_cast at h
  linarith
/-! ### The basis dilogarithms -/

/-- The dilogarithm of the basis argument `b0`. -/
theorem i5C1B_d0 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (x)) (-(log (1 - x)) * ((1 / x))) x := by
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
  have e1 : 1 - (x) = (1 - x) := by field_simp
  have eA : log (1 - (x)) = log (1 - x) := by
    rw [e1]
  have hlt : |x| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ) + (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : x ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => x) hid hne hlt eA ?_
  field_simp

theorem i5C1B_c0 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (x)) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hf : ContinuousOn (fun x => x) (Ico 0 (1 - ξ)) := by fun_prop
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ x ∧ x ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ x)], ?_⟩
  linear_combination (by positivity : (0 : ℝ) ≤ ξ) + (by positivity : (0 : ℝ) ≤ (1 - ξ - x))

theorem i5C1B_z0 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (0) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  rw [Li₂_zero]

/-- The dilogarithm of the basis argument `b1`. -/
theorem i5C1B_d1 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (x / (1 - ξ))) (-(-log (1 - ξ) + log (1 - ξ - x)) * ((1 / x))) x := by
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
  have e1 : 1 - (x / (1 - ξ)) = (1 - ξ - x) / (1 - ξ) := by field_simp
  have eA : log (1 - (x / (1 - ξ))) = -log (1 - ξ) + log (1 - ξ - x) := by
    rw [e1, log_div (by positivity) (by positivity)]; ring
  have hlt : |x / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : x / (1 - ξ) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => x / (1 - ξ)) (hid.div (hasDerivAt_const x ((1 - ξ)))
      hy.ne') hne hlt eA ?_
  field_simp; ring

theorem i5C1B_c1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (x / (1 - ξ))) (Ico 0 (1 - ξ)) := by
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
  have hf : ContinuousOn (fun x => x / (1 - ξ)) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ x / (1 - ξ) ∧ x / (1 - ξ) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ x / (1 - ξ))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ (1 - ξ - x))

theorem i5C1B_z1 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (0 / (1 - ξ)) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : 0 / (1 - ξ) = 0 := by simp
  rw [e, Li₂_zero]

/-- The dilogarithm of the basis argument `b2`. -/
theorem i5C1B_d2 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (ξ / (1 - x))) (-(log (1 - ξ - x) - log (1 - x)) *
        (-(-1 / (1 - x)))) x := by
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
  have e1 : 1 - (ξ / (1 - x)) = (1 - ξ - x) / (1 - x) := by field_simp; ring
  have eA : log (1 - (ξ / (1 - x))) = log (1 - ξ - x) - log (1 - x) := by
    rw [e1, log_div (by positivity) (by positivity)]
  have hlt : |ξ / (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : ξ / (1 - x) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => ξ / (1 - x)) ((hasDerivAt_const x (ξ)).div d3 l3.ne')
      hne hlt eA ?_
  field_simp; ring

theorem i5C1B_c2 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (ξ / (1 - x))) (Ico 0 (1 - ξ)) := by
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
  have hf : ContinuousOn (fun x => ξ / (1 - x)) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ ξ / (1 - x) ∧ ξ / (1 - x) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ ξ / (1 - x))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ (1 - ξ - x))

theorem i5C1B_z2 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (ξ / (1 - 0)) = Li₂ ξ := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : ξ / (1 - 0) = ξ := by simp
  rw [e]

/-- The dilogarithm of the basis argument `b3`. -/
theorem i5C1B_d3 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (ξ * (1 - x))) (-(log (ξ * x + (1 - ξ))) * ((-1 / (1 - x)))) x := by
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
  have e1 : 1 - (ξ * (1 - x)) = (ξ * x + (1 - ξ)) := by field_simp; ring
  have eA : log (1 - (ξ * (1 - x))) = log (ξ * x + (1 - ξ)) := by
    rw [e1]
  have hlt : |ξ * (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : ξ * (1 - x) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => ξ * (1 - x)) ((hasDerivAt_const x (ξ)).mul d3) hne hlt
      eA ?_
  field_simp; ring

theorem i5C1B_c3 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (ξ * (1 - x))) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hf : ContinuousOn (fun x => ξ * (1 - x)) (Ico 0 (1 - ξ)) := by fun_prop
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ ξ * (1 - x) ∧ ξ * (1 - x) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ ξ * (1 - x))], ?_⟩
  linear_combination 2 * (by positivity : (0 : ℝ) ≤ ξ * x) + (by positivity : (0 : ℝ) ≤ ξ *
      (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ x ^ 2) + 2 * (by positivity : (0 : ℝ) ≤ x *
      (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 2)

theorem i5C1B_z3 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (ξ * (1 - 0)) = Li₂ ξ := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : ξ * (1 - 0) = ξ := by simp
  rw [e]

/-- The dilogarithm of the basis argument `b4`. -/
theorem i5C1B_d4 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (-(ξ * x / (1 - ξ)))) (-(-log (1 - ξ) + log (ξ * x + (1 - ξ))) *
        ((1 / x))) x := by
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
  have e1 : 1 - (-(ξ * x / (1 - ξ))) = (ξ * x + (1 - ξ)) / (1 - ξ) := by field_simp; ring
  have eA : log (1 - (-(ξ * x / (1 - ξ)))) = -log (1 - ξ) + log (ξ * x + (1 - ξ)) := by
    rw [e1, log_div (by positivity) (by positivity)]; ring
  have hlt : |-(ξ * x / (1 - ξ))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : -(ξ * x / (1 - ξ)) ≠ 0 := neg_ne_zero.mpr (by positivity)
  refine i5C1_hasDerivAt_Li₂ (f := fun x => -(ξ * x / (1 - ξ))) ((((hasDerivAt_const x (ξ)).mul
      hid).div (hasDerivAt_const x ((1 - ξ))) hy.ne').neg) hne hlt eA ?_
  field_simp; ring

theorem i5C1B_c4 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (-(ξ * x / (1 - ξ)))) (Ico 0 (1 - ξ)) := by
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
  have hf : ContinuousOn (fun x => -(ξ * x / (1 - ξ))) (Ico 0 (1 - ξ)) :=
      (ContinuousOn.div (by fun_prop) (by fun_prop) hD).neg
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ -(ξ * x / (1 - ξ)) ∧ -(ξ * x / (1 - ξ)) ≤ 1
  refine ⟨neg_le_neg ?_, by linarith [(by positivity : (0 : ℝ) ≤ ξ * x / (1 - ξ))]⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ ξ * (1 - ξ - x)) +
      (by positivity : (0 : ℝ) ≤ x ^ 2) + 2 * (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x)) +
      (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 2)

theorem i5C1B_z4 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (-(ξ * 0 / (1 - ξ))) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : -(ξ * 0 / (1 - ξ)) = 0 := by simp
  rw [e, Li₂_zero]

/-- The dilogarithm of the basis argument `b5`. -/
theorem i5C1B_d5 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (x / (ξ * x + (1 - ξ)))) (-(log (1 - ξ) - log (ξ * x + (1 - ξ)) +
        log (1 - x)) * ((1 / x) - (ξ / (ξ * x + (1 - ξ))))) x := by
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
  have e1 : 1 - (x / (ξ * x + (1 - ξ))) = (1 - ξ) * (1 - x) / (ξ * x + (1 - ξ)) :=
      by field_simp; ring
  have eA : log (1 - (x / (ξ * x + (1 - ξ)))) = log (1 - ξ) - log (ξ * x + (1 - ξ)) +
      log (1 - x) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]; ring
  have hlt : |x / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : x / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => x / (ξ * x + (1 - ξ))) (hid.div d2 l2.ne') hne hlt eA ?_
  field_simp

theorem i5C1B_c5 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (x / (ξ * x + (1 - ξ)))) (Ico 0 (1 - ξ)) := by
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
  have hf : ContinuousOn (fun x => x / (ξ * x + (1 - ξ))) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ x / (ξ * x + (1 - ξ)) ∧ x / (ξ * x + (1 - ξ)) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ x / (ξ * x + (1 - ξ)))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ ξ * x) + (by positivity : (0 : ℝ) ≤ ξ *
      (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x)) +
      (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 2)

theorem i5C1B_z5 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (0 / (ξ * 0 + (1 - ξ))) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : 0 / (ξ * 0 + (1 - ξ)) = 0 := by simp
  rw [e, Li₂_zero]

/-- The dilogarithm of the basis argument `b6`. -/
theorem i5C1B_d6 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) (-(-2 * log (1 - ξ) +
        log (ξ * x ^ 2 + (1 - ξ) ^ 2)) * (2 * (1 / x))) x := by
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
  have e1 : 1 - (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) = (ξ * x ^ 2 + (1 - ξ) ^ 2) / (1 - ξ) ^ 2 :=
      by field_simp; ring
  have eA : log (1 - (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) = -2 * log (1 - ξ) +
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
    rw [e1, log_div (by positivity) (by positivity), log_pow]; ring
  have hlt : |-(ξ * x ^ 2 / (1 - ξ) ^ 2)| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  have hne : -(ξ * x ^ 2 / (1 - ξ) ^ 2) ≠ 0 := neg_ne_zero.mpr (by positivity)
  refine i5C1_hasDerivAt_Li₂ (f := fun x => -(ξ * x ^ 2 / (1 - ξ) ^ 2))
      ((((hasDerivAt_const x (ξ)).mul (hid.pow 2)).div (hasDerivAt_const x ((1 - ξ) ^ 2))
      (pow_pos hy 2).ne').neg) hne hlt eA ?_
  field_simp; ring

theorem i5C1B_c6 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (1 - ξ) ^ 2 ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => -(ξ * x ^ 2 / (1 - ξ) ^ 2)) (Ico 0 (1 - ξ)) :=
      (ContinuousOn.div (by fun_prop) (by fun_prop) hD).neg
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ -(ξ * x ^ 2 / (1 - ξ) ^ 2) ∧ -(ξ * x ^ 2 / (1 - ξ) ^ 2) ≤ 1
  refine ⟨neg_le_neg ?_, by linarith [(by positivity : (0 : ℝ) ≤ ξ * x ^ 2 / (1 - ξ) ^ 2)]⟩
  rw [div_le_one (by positivity)]
  linear_combination 2 * (by positivity : (0 : ℝ) ≤ ξ * x * (1 - ξ - x)) +
      (by positivity : (0 : ℝ) ≤ ξ * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) ≤ x ^ 3) + 3 *
      (by positivity : (0 : ℝ) ≤ x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) ≤ x *
      (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 3)

theorem i5C1B_z6 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (-(ξ * 0 ^ 2 / (1 - ξ) ^ 2)) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : -(ξ * 0 ^ 2 / (1 - ξ) ^ 2) = 0 := by simp
  rw [e, Li₂_zero]

/-- The dilogarithm of the basis argument `b7`. -/
theorem i5C1B_d7 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) (-(-log (1 - ξ) +
        log (ξ * x + (1 - ξ) ^ 2)) * ((-1 / (1 - ξ - x)))) x := by
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
  have e1 : 1 - (ξ * (1 - ξ - x) / (1 - ξ)) = (ξ * x + (1 - ξ) ^ 2) / (1 - ξ) := by field_simp; ring
  have eA : log (1 - (ξ * (1 - ξ - x) / (1 - ξ))) = -log (1 - ξ) + log (ξ * x + (1 - ξ) ^ 2) := by
    rw [e1, log_div (by positivity) (by positivity)]; ring
  have hlt : |ξ * (1 - ξ - x) / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : ξ * (1 - ξ - x) / (1 - ξ) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => ξ * (1 - ξ - x) / (1 -
      ξ)) (((hasDerivAt_const x (ξ)).mul d1).div (hasDerivAt_const x ((1 - ξ))) hy.ne') hne hlt eA
      ?_
  field_simp; ring

theorem i5C1B_c7 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (ξ * (1 - ξ - x) / (1 - ξ))) (Ico 0 (1 - ξ)) := by
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
  have hf : ContinuousOn (fun x => ξ * (1 - ξ - x) / (1 - ξ)) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ ξ * (1 - ξ - x) / (1 - ξ) ∧ ξ * (1 - ξ - x) / (1 - ξ) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ ξ * (1 - ξ - x) / (1 - ξ))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ ξ * x) + (by positivity : (0 : ℝ) ≤ x ^ 2) + 2 *
      (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 2)

theorem i5C1B_z7 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (ξ * (1 - ξ - 0) / (1 - ξ)) = Li₂ ξ := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : ξ * (1 - ξ - 0) / (1 - ξ) = ξ := by simp; field_simp
  rw [e]

/-- The dilogarithm of the basis argument `b8`. -/
theorem i5C1B_d8 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) (-(log (1 - ξ - x) -
        log (ξ * x + (1 - ξ))) * ((1 / x) - (ξ / (ξ * x + (1 - ξ))))) x := by
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
  have e1 : 1 - ((1 + ξ) * x / (ξ * x + (1 - ξ))) = (1 - ξ - x) / (ξ * x + (1 - ξ)) :=
      by field_simp; ring
  have eA : log (1 - ((1 + ξ) * x / (ξ * x + (1 - ξ)))) = log (1 - ξ - x) -
      log (ξ * x + (1 - ξ)) := by
    rw [e1, log_div (by positivity) (by positivity)]
  have hlt : |(1 + ξ) * x / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : (1 + ξ) * x / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => (1 + ξ) * x / (ξ * x +
      (1 - ξ))) (((hasDerivAt_const x ((1 + ξ))).mul hid).div d2 l2.ne') hne hlt eA ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1B_c8 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) (Ico 0 (1 - ξ)) := by
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
  have hf : ContinuousOn (fun x => (1 + ξ) * x / (ξ * x + (1 - ξ))) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ (1 + ξ) * x / (ξ * x + (1 - ξ)) ∧ (1 + ξ) * x / (ξ * x + (1 - ξ)) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ (1 + ξ) * x / (ξ * x + (1 - ξ)))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ (1 - ξ - x))

theorem i5C1B_z8 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ ((1 + ξ) * 0 / (ξ * 0 + (1 - ξ))) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : (1 + ξ) * 0 / (ξ * 0 + (1 - ξ)) = 0 := by simp
  rw [e, Li₂_zero]

/-- The dilogarithm of the basis argument `b9`. -/
theorem i5C1B_d9 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (x / (ξ * x + (1 - ξ) ^ 2))) (-(log (1 - ξ) + log (1 - ξ - x) -
        log (ξ * x + (1 - ξ) ^ 2)) * ((1 / x) - (ξ / (ξ * x + (1 - ξ) ^ 2)))) x := by
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
  have e1 : 1 - (x / (ξ * x + (1 - ξ) ^ 2)) = (1 - ξ) * (1 - ξ - x) / (ξ * x + (1 - ξ) ^ 2) :=
      by field_simp; ring
  have eA : log (1 - (x / (ξ * x + (1 - ξ) ^ 2))) = log (1 - ξ) + log (1 - ξ - x) -
      log (ξ * x + (1 - ξ) ^ 2) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  have hlt : |x / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : x / (ξ * x + (1 - ξ) ^ 2) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => x / (ξ * x + (1 - ξ) ^ 2)) (hid.div d4 l4.ne') hne hlt
      eA ?_
  field_simp

theorem i5C1B_c9 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (x / (ξ * x + (1 - ξ) ^ 2))) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (ξ * x + (1 - ξ) ^ 2) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => x / (ξ * x + (1 - ξ) ^ 2)) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ x / (ξ * x + (1 - ξ) ^ 2) ∧ x / (ξ * x + (1 - ξ) ^ 2) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ x / (ξ * x + (1 - ξ) ^ 2))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x)) +
      (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 2)

theorem i5C1B_z9 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (0 / (ξ * 0 + (1 - ξ) ^ 2)) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : 0 / (ξ * 0 + (1 - ξ) ^ 2) = 0 := by simp
  rw [e, Li₂_zero]

/-- The dilogarithm of the basis argument `b10`. -/
theorem i5C1B_d10 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) (-(-log (ξ * x + (1 - ξ)) +
        log (ξ * x + (1 - ξ) ^ 2)) * (-(ξ / (ξ * x + (1 - ξ))))) x := by
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
  have e1 : 1 - (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) = (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)) :=
      by field_simp; ring
  have eA : log (1 - (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) = -log (ξ * x + (1 - ξ)) +
      log (ξ * x + (1 - ξ) ^ 2) := by
    rw [e1, log_div (by positivity) (by positivity)]; ring
  have hlt : |ξ * (1 - ξ) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : ξ * (1 - ξ) / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => ξ * (1 - ξ) / (ξ * x +
      (1 - ξ))) (((hasDerivAt_const x (ξ)).mul (hasDerivAt_const x ((1 - ξ)))).div d2 l2.ne') hne
      hlt eA ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1B_c10 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) (Ico 0 (1 - ξ)) := by
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
  have hf : ContinuousOn (fun x => ξ * (1 - ξ) / (ξ * x + (1 - ξ))) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ ξ * (1 - ξ) / (ξ * x + (1 - ξ)) ∧ ξ * (1 - ξ) / (ξ * x + (1 - ξ)) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ ξ * (1 - ξ) / (ξ * x + (1 - ξ)))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination (by positivity : (0 : ℝ) ≤ ξ * x) + (by positivity : (0 : ℝ) ≤ x ^ 2) + 2 *
      (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 2)

theorem i5C1B_z10 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (ξ * (1 - ξ) / (ξ * 0 + (1 - ξ))) =
    Li₂ ξ := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : ξ * (1 - ξ) / (ξ * 0 + (1 - ξ)) = ξ := by simp; field_simp
  rw [e]

/-- The dilogarithm of the basis argument `b11`. -/
theorem i5C1B_d11 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) (-(log (1 - ξ) +
        log (1 + ξ) - log (ξ * x + (1 - ξ))) * ((-1 / (1 - ξ - x)) - (ξ / (ξ * x + (1 - ξ))))) x :=
        by
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
  have e1 : 1 - (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) = (1 - ξ) * (1 + ξ) / (ξ * x + (1 - ξ)) :=
      by field_simp; ring
  have eA : log (1 - (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) = log (1 - ξ) + log (1 + ξ) -
      log (ξ * x + (1 - ξ)) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  have hlt : |-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) +
        2 * (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) <
        (1 - ξ - x) ^ 2)
  have hne : -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))) ≠ 0 := neg_ne_zero.mpr (by positivity)
  refine i5C1_hasDerivAt_Li₂ (f := fun x => -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))
      ((((hasDerivAt_const x (ξ)).mul d1).div d2 l2.ne').neg) hne hlt eA ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1B_c11 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) (Ico 0 (1 - ξ)) := by
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
  have hf : ContinuousOn (fun x => -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) (Ico 0 (1 - ξ)) :=
      (ContinuousOn.div (by fun_prop) (by fun_prop) hD).neg
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))) ∧ -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))) ≤ 1
  refine ⟨neg_le_neg ?_, by linarith [(by positivity : (0 : ℝ) ≤ ξ *
      (1 - ξ - x) / (ξ * x + (1 - ξ)))]⟩
  rw [div_le_one (by positivity)]
  linear_combination 2 * (by positivity : (0 : ℝ) ≤ ξ * x) + (by positivity : (0 : ℝ) ≤ x ^ 2) +
      2 * (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 2)

theorem i5C1B_z11 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (-(ξ * (1 - ξ - 0) / (ξ * 0 + (1 - ξ)))) =
    Li₂ (-ξ) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : -(ξ * (1 - ξ - 0) / (ξ * 0 + (1 - ξ))) = -ξ := by simp; field_simp
  rw [e]

/-- The dilogarithm of the basis argument `b12`. -/
theorem i5C1B_d12 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) (-(log (1 + ξ) - 2 *
        log (ξ * x + (1 - ξ)) + log (ξ * x ^ 2 + (1 - ξ) ^ 2)) * (2 * (-1 / (1 - ξ - x)) - 2 *
        (ξ / (ξ * x + (1 - ξ))))) x := by
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
  have e1 : 1 - (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) = (1 + ξ) *
      (ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)) ^ 2 := by field_simp; ring
  have eA : log (1 - (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) = log (1 + ξ) - 2 *
      log (ξ * x + (1 - ξ)) + log (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
    rw [e1, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_pow]; ring
  have hlt : |-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 4 * (by positivity : (0 : ℝ) < ξ ^ 2 * x ^ 2) + 4 *
        (by positivity : (0 : ℝ) < ξ ^ 2 * x * (1 - ξ - x)) + 4 *
        (by positivity : (0 : ℝ) < ξ * x ^ 3) + 10 * (by positivity : (0 : ℝ) < ξ * x ^ 2 *
        (1 - ξ - x)) + 7 * (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x) ^ 2) +
        (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 3) + (by positivity : (0 : ℝ) < x ^ 4) + 4 *
        (by positivity : (0 : ℝ) < x ^ 3 * (1 - ξ - x)) + 6 * (by positivity : (0 : ℝ) < x ^ 2 *
        (1 - ξ - x) ^ 2) + 4 * (by positivity : (0 : ℝ) < x * (1 - ξ - x) ^ 3) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 4)
  have hne : -(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2) ≠ 0 := neg_ne_zero.mpr (by positivity)
  refine i5C1_hasDerivAt_Li₂ (f := fun x => -(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))
      ((((hasDerivAt_const x (ξ)).mul (d1.pow 2)).div (d2.pow 2) (pow_pos l2 2).ne').neg) hne hlt
      eA ?_
  simp only [Pi.mul_apply, Pi.pow_apply]; field_simp; ring

theorem i5C1B_c12 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2))) (Ico 0 (1 - ξ)) :=
        by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (ξ * x + (1 - ξ)) ^ 2 ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => -(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) (Ico 0 (1 -
      ξ)) := (ContinuousOn.div (by fun_prop) (by fun_prop) hD).neg
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ -(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2) ∧ -(ξ *
      (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2) ≤ 1
  refine ⟨neg_le_neg ?_, by linarith [(by positivity : (0 : ℝ) ≤ ξ *
      (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)]⟩
  rw [div_le_one (by positivity)]
  linear_combination 4 * (by positivity : (0 : ℝ) ≤ ξ ^ 2 * x ^ 2) + 4 *
      (by positivity : (0 : ℝ) ≤ ξ ^ 2 * x * (1 - ξ - x)) + 4 * (by positivity : (0 : ℝ) ≤ ξ *
      x ^ 3) + 10 * (by positivity : (0 : ℝ) ≤ ξ * x ^ 2 * (1 - ξ - x)) + 7 *
      (by positivity : (0 : ℝ) ≤ ξ * x * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) ≤ ξ *
      (1 - ξ - x) ^ 3) + (by positivity : (0 : ℝ) ≤ x ^ 4) + 4 * (by positivity : (0 : ℝ) ≤ x ^ 3 *
      (1 - ξ - x)) + 6 * (by positivity : (0 : ℝ) ≤ x ^ 2 * (1 - ξ - x) ^ 2) + 4 *
      (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x) ^ 3) + (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 4)

theorem i5C1B_z12 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (-(ξ * (1 - ξ - 0) ^ 2 / (ξ * 0 +
    (1 - ξ)) ^ 2)) = Li₂ (-ξ) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : -(ξ * (1 - ξ - 0) ^ 2 / (ξ * 0 + (1 - ξ)) ^ 2) = -ξ := by simp; field_simp
  rw [e]

/-- The dilogarithm of the basis argument `b13`. -/
theorem i5C1B_d13 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2))) (-(-log (ξ * x +
        (1 - ξ) ^ 2) + log (ξ * x ^ 2 + (1 - ξ) ^ 2)) * ((1 / x) + (-1 / (1 - x)) -
        (ξ / (ξ * x + (1 - ξ) ^ 2)))) x := by
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
  have e1 : 1 - (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) = (ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x +
      (1 - ξ) ^ 2) := by field_simp; ring
  have eA : log (1 - (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2))) = -log (ξ * x + (1 - ξ) ^ 2) +
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
    rw [e1, log_div (by positivity) (by positivity)]; ring
  have hlt : |ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  have hne : ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2) ≠ 0 := by positivity
  refine i5C1_hasDerivAt_Li₂ (f := fun x => ξ * x * (1 - x) / (ξ * x +
      (1 - ξ) ^ 2)) ((((hasDerivAt_const x (ξ)).mul hid).mul d3).div d4 l4.ne') hne hlt eA ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1B_c13 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x => Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2))) (Ico 0 (1 - ξ)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have hD : ∀ x ∈ Ico 0 (1 - ξ), (ξ * x + (1 - ξ) ^ 2) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hxy⟩ := hx
    have l1 : 0 < 1 - ξ - x := by linarith
    have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
    have l3 : 0 < 1 - x := by linarith
    have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
      have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
    have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
    positivity
  have hf : ContinuousOn (fun x => ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) (Ico 0 (1 - ξ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hD
  refine i5C1_contLi₂ hf fun x hx => ?_
  obtain ⟨hx0, hxy⟩ := hx
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by have := mul_nonneg h0.le hx0; linarith
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by
    have := mul_nonneg h0.le hx0; have := pow_pos hy 2; linarith
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  show -1 ≤ ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2) ∧ ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2) ≤ 1
  refine ⟨by linarith [(by positivity : (0 : ℝ) ≤ ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2))], ?_⟩
  rw [div_le_one (by positivity)]
  linear_combination 2 * (by positivity : (0 : ℝ) ≤ ξ * x ^ 2) + 2 *
      (by positivity : (0 : ℝ) ≤ ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ ξ *
      (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) ≤ x ^ 3) + 3 * (by positivity : (0 : ℝ) ≤ x ^ 2 *
      (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x) ^ 2) +
      (by positivity : (0 : ℝ) ≤ (1 - ξ - x) ^ 3)

theorem i5C1B_z13 {ξ : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) : Li₂ (ξ * 0 *
    (1 - 0) / (ξ * 0 + (1 - ξ) ^ 2)) = 0 := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have e : ξ * 0 * (1 - 0) / (ξ * 0 + (1 - ξ) ^ 2) = 0 := by simp
  rw [e, Li₂_zero]

end QED.ThreeLoopD
