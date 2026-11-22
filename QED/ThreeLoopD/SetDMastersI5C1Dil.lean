/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Set (d), master `I₅`: a two-variable dilogarithm identity

For `0 < ξ < 1`, `y = 1 - ξ` and `0 < x < y`, the dilogarithm of the argument
`ρ₀/ρ₁ = ξ x³ (ξ x + y²)/(y⁴ (1 - x))` of the integrand `I(x)` of `t K₁(t)` reduces to the
dilogarithm basis `x, x/y, ξ/(1 - x), -ξx/y, x/(ξx + y), -ξx²/y², ξ(y - x)/y, x/(ξx + y²),
ξy/(ξx + y), ξx(1 - x)/(ξx + y²)` of the primitive, plus products of logarithms of the letters
(`QED.ThreeLoopD.i5C1_dilogD3`). Both sides have the same derivative in `x`
(`QED.ThreeLoopD.hasDerivAt_i5C1D3`: every derivative is a combination of the letter
derivatives `1/x, -1/(y - x), ξ/(ξx + y), -1/(1 - x), ξ/(ξx + y²)`), and agree at `x = 0`.

## Main results

* `QED.ThreeLoopD.i5C1_dilogD3`.
-/

@[expose] public section

open MeasureTheory Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- The chain rule for `Li₂ ∘ f` with `log (1 - f x)` named. -/
theorem i5Li₂_hasDerivAt_comp {f : ℝ → ℝ} {f' x A : ℝ} (hf : HasDerivAt f f' x)
    (h0 : f x ≠ 0) (h1 : |f x| < 1) (hA : log (1 - f x) = A) :
    HasDerivAt (fun x => Li₂ (f x)) (-A / f x * f') x := by
  have := (hasDerivAt_Li₂ h1 h0).comp x hf
  rw [hA] at this
  exact this

/-- `i5Li₂_hasDerivAt_comp` with the logarithmic derivative `f'/f` named. -/
theorem i5Li₂_hasDerivAt_comp' {f : ℝ → ℝ} {f' x A D : ℝ} (hf : HasDerivAt f f' x)
    (h0 : f x ≠ 0) (h1 : |f x| < 1) (hA : log (1 - f x) = A) (hD : f' / f x = D) :
    HasDerivAt (fun x => Li₂ (f x)) (-A * D) x := by
  refine (i5Li₂_hasDerivAt_comp hf h0 h1 hA).congr_deriv ?_
  rw [← hD]
  ring

/-- The right side of the dilogarithm identity for `Li₂(ξ x³ (ξ x + y²)/(y⁴ (1 - x)))`. -/
noncomputable def i5C1D3R (ξ x : ℝ) : ℝ :=
  -2 * Li₂ x + 2 * Li₂ (x / (1 - ξ)) + Li₂ (ξ / (1 - x)) + 2 * Li₂ (-(ξ * x / (1 - ξ))) -
    Li₂ (x / (ξ * x + (1 - ξ))) + 2 * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) -
    2 * Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) + Li₂ (x / (ξ * x + (1 - ξ) ^ 2)) +
    Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) - Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) -
    2 * log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2) + 2 * log (1 - ξ - x) * log (1 - ξ) +
    log (ξ * x + (1 - ξ)) * log (1 - x) - log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) +
    log (ξ * x + (1 - ξ)) * log (1 - ξ) + log (1 - x) * log (ξ * x + (1 - ξ) ^ 2) -
    4 * log (1 - x) * log (1 - ξ) + 3 * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) -
    3 * log (1 - ξ) ^ 2

theorem hasDerivAt_i5C1D3 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₂ (ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - x))) -
      i5C1D3R ξ x) 0 x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
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
  -- the dilogarithm terms
  have t0 := i5Li₂_hasDerivAt_comp' hid hx.ne' (by rw [abs_of_pos hx]; linarith) rfl
    (show _ = 1 / x by field_simp)
  have t1 := i5Li₂_hasDerivAt_comp' (f := fun x => x / (1 - ξ))
    (hid.div_const (1 - ξ)) (by positivity)
    (by rw [abs_of_pos (by positivity), div_lt_one hy]; exact hxy)
    (show log (1 - x / (1 - ξ)) = log (1 - ξ - x) - log (1 - ξ) by
      rw [show 1 - x / (1 - ξ) = (1 - ξ - x) / (1 - ξ) by field_simp, log_div l1.ne' hy.ne'])
    (show _ = 1 / x by field_simp)
  have t2 := i5Li₂_hasDerivAt_comp' (f := fun x => ξ / (1 - x))
    ((hasDerivAt_const x ξ).div d3 l3.ne') (by positivity)
    (by rw [abs_of_pos (by positivity), div_lt_one l3]; linarith)
    (show log (1 - ξ / (1 - x)) = log (1 - ξ - x) - log (1 - x) by
      rw [show 1 - ξ / (1 - x) = (1 - ξ - x) / (1 - x) by field_simp; ring,
        log_div l1.ne' l3.ne'])
    (show _ = -(-1 / (1 - x)) by field_simp; ring)
  have t4 := i5Li₂_hasDerivAt_comp' (f := fun x => -(ξ * x / (1 - ξ)))
    (((hid.const_mul ξ).div_const (1 - ξ)).neg)
    (neg_ne_zero.mpr (by positivity))
    (by rw [abs_neg, abs_of_pos (by positivity), div_lt_one hy]; nlinarith)
    (show log (1 - -(ξ * x / (1 - ξ))) = log (ξ * x + (1 - ξ)) - log (1 - ξ) by
      rw [show 1 - -(ξ * x / (1 - ξ)) = (ξ * x + (1 - ξ)) / (1 - ξ) by field_simp; ring,
        log_div l2.ne' hy.ne'])
    (show _ = 1 / x by field_simp)
  have t5 := i5Li₂_hasDerivAt_comp' (f := fun x => x / (ξ * x + (1 - ξ)))
    (hid.div d2 l2.ne') (by positivity)
    (by rw [abs_of_pos (by positivity), div_lt_one l2]; nlinarith)
    (show log (1 - x / (ξ * x + (1 - ξ))) = log (1 - ξ) + log (1 - x) - log (ξ * x + (1 - ξ)) by
      rw [show 1 - x / (ξ * x + (1 - ξ)) = (1 - ξ) * (1 - x) / (ξ * x + (1 - ξ)) by
        field_simp; ring, log_div (by positivity) l2.ne', log_mul hy.ne' l3.ne'])
    (show _ = 1 / x - ξ / (ξ * x + (1 - ξ)) by field_simp)
  have t6 := i5Li₂_hasDerivAt_comp' (f := fun x => -(ξ * x ^ 2 / (1 - ξ) ^ 2))
    ((((hid.pow 2).const_mul ξ).div_const ((1 - ξ) ^ 2)).neg)
    (neg_ne_zero.mpr (by positivity))
    (by rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]; nlinarith)
    (show log (1 - -(ξ * x ^ 2 / (1 - ξ) ^ 2)) = log (ξ * x ^ 2 + (1 - ξ) ^ 2) -
        2 * log (1 - ξ) by
      rw [show 1 - -(ξ * x ^ 2 / (1 - ξ) ^ 2) = (ξ * x ^ 2 + (1 - ξ) ^ 2) / (1 - ξ) ^ 2 by
        field_simp; ring, log_div l5.ne' (by positivity), log_pow]
      push_cast; ring)
    (show _ = 2 * (1 / x) by field_simp; ring)
  have t7 := i5Li₂_hasDerivAt_comp' (f := fun x => ξ * (1 - ξ - x) / (1 - ξ))
    ((d1.const_mul ξ).div_const (1 - ξ)) (by positivity)
    (by rw [abs_of_pos (by positivity), div_lt_one hy]; nlinarith)
    (show log (1 - ξ * (1 - ξ - x) / (1 - ξ)) = log (ξ * x + (1 - ξ) ^ 2) - log (1 - ξ) by
      rw [show 1 - ξ * (1 - ξ - x) / (1 - ξ) = (ξ * x + (1 - ξ) ^ 2) / (1 - ξ) by
        field_simp; ring, log_div l4.ne' hy.ne'])
    (show _ = -1 / (1 - ξ - x) by field_simp)
  have t9 := i5Li₂_hasDerivAt_comp' (f := fun x => x / (ξ * x + (1 - ξ) ^ 2))
    (hid.div d4 l4.ne') (by positivity)
    (by rw [abs_of_pos (by positivity), div_lt_one l4]; nlinarith)
    (show log (1 - x / (ξ * x + (1 - ξ) ^ 2)) = log (1 - ξ) + log (1 - ξ - x) -
        log (ξ * x + (1 - ξ) ^ 2) by
      rw [show 1 - x / (ξ * x + (1 - ξ) ^ 2) = (1 - ξ) * (1 - ξ - x) / (ξ * x + (1 - ξ) ^ 2) by
        field_simp; ring, log_div (by positivity) l4.ne', log_mul hy.ne' l1.ne'])
    (show _ = 1 / x - ξ / (ξ * x + (1 - ξ) ^ 2) by field_simp)
  have t10 := i5Li₂_hasDerivAt_comp' (f := fun x => ξ * (1 - ξ) / (ξ * x + (1 - ξ)))
    ((hasDerivAt_const x (ξ * (1 - ξ))).div d2 l2.ne')
    (by positivity) (by rw [abs_of_pos (by positivity), div_lt_one l2]; nlinarith)
    (show log (1 - ξ * (1 - ξ) / (ξ * x + (1 - ξ))) = log (ξ * x + (1 - ξ) ^ 2) -
        log (ξ * x + (1 - ξ)) by
      rw [show 1 - ξ * (1 - ξ) / (ξ * x + (1 - ξ)) = (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)) by
        field_simp; ring, log_div l4.ne' l2.ne'])
    (show _ = -(ξ / (ξ * x + (1 - ξ))) by field_simp; ring)
  have t13 := i5Li₂_hasDerivAt_comp' (f := fun x => ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2))
    (((hid.const_mul ξ).mul d3).div d4 l4.ne') (by positivity)
    (by rw [abs_of_pos (by positivity), div_lt_one l4]; nlinarith)
    (show log (1 - ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) = log (ξ * x ^ 2 + (1 - ξ) ^ 2) -
        log (ξ * x + (1 - ξ) ^ 2) by
      rw [show 1 - ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2) =
        (ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2) by field_simp; ring,
        log_div l5.ne' l4.ne'])
    (show _ = 1 / x + -1 / (1 - x) - ξ / (ξ * x + (1 - ξ) ^ 2) by
      simp only [Pi.mul_apply]
      field_simp)
  have hD : ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) < (1 - ξ) ^ 4 * (1 - x) := by
    have a : x ^ 3 < (1 - ξ) ^ 3 := by gcongr
    have b : ξ * x + (1 - ξ) ^ 2 < ξ * (1 - ξ) + (1 - ξ) ^ 2 := by nlinarith
    have c : ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) < ξ * (1 - ξ) ^ 3 * (1 - ξ) := by
      calc ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) < ξ * (1 - ξ) ^ 3 * (ξ * (1 - ξ) + (1 - ξ) ^ 2) := by
            gcongr
        _ = ξ * (1 - ξ) ^ 3 * (1 - ξ) := by ring
    nlinarith [pow_pos hy 4]
  have tD := i5Li₂_hasDerivAt_comp'
    (f := fun x => ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - x)))
    ((((hid.pow 3).const_mul ξ).mul d4).div
    (d3.const_mul ((1 - ξ) ^ 4)) (by positivity)) (by positivity)
    (by rw [abs_of_pos (by positivity), div_lt_one (by positivity)]; exact hD)
    (show log (1 - ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - x))) =
        log (1 - ξ - x) + log (ξ * x + (1 - ξ)) + log (ξ * x ^ 2 + (1 - ξ) ^ 2) - log (1 - x) -
        4 * log (1 - ξ) by
      rw [show 1 - ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - x)) =
        (1 - ξ - x) * (ξ * x + (1 - ξ)) * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - x)) by
        field_simp; ring, log_div (by positivity) (by positivity), log_mul (by positivity)
        l5.ne', log_mul l1.ne' l2.ne', log_mul (by positivity) l3.ne', log_pow]
      push_cast; ring)
    (show _ = 3 * (1 / x) + ξ / (ξ * x + (1 - ξ) ^ 2) - -1 / (1 - x) by
      simp only [Pi.mul_apply, Pi.pow_apply]
      field_simp; ring)
  have g1 := d1.log l1.ne'
  have g2 := d2.log l2.ne'
  have g3 := d3.log l3.ne'
  have g4 := d4.log l4.ne'
  have e := tD.sub (((((((((((((t0.const_mul (-2)).add (t1.const_mul 2)).add t2).add
    (t4.const_mul 2)).sub t5).add (t6.const_mul 2)).sub (t7.const_mul 2)).add t9).add t10).sub
    t13).sub (((g1.mul g4).const_mul 2))).add ((g1.mul_const (log (1 - ξ))).const_mul 2)) |>.add
    (g2.mul g3) |>.sub (g2.mul g4) |>.add (g2.mul_const (log (1 - ξ))) |>.add (g3.mul g4) |>.sub
    ((g3.mul_const (log (1 - ξ))).const_mul 4) |>.add ((g4.mul_const (log (1 - ξ))).const_mul 3)
    |>.sub (hasDerivAt_const x (3 * log (1 - ξ) ^ 2)))
  convert e using 1
  · funext x
    simp only [i5C1D3R, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  ring

/-- Continuity of `Li₂ ∘ f` where `f` takes values in `[-1, 1]`. -/
theorem i5Li₂_continuousOn_comp {f : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (h : ∀ x ∈ s, -1 ≤ f x ∧ f x ≤ 1) : ContinuousOn (fun x => Li₂ (f x)) s :=
  continuousOn_Li₂.comp hf fun x hx => h x hx

/-- **A two-variable dilogarithm identity**: for `0 < x < y = 1 - ξ`,
`Li₂(ξ x³ (ξ x + y²)/(y⁴ (1 - x)))` in the dilogarithm basis of `I(x)`. -/
theorem i5C1_dilogD3 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ (ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - x))) = i5C1D3R ξ x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  set F := fun x => Li₂ (ξ * x ^ 3 * (ξ * x + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - x))) -
    i5C1D3R ξ x with hF
  have hI : ∀ z ∈ Icc 0 x, 0 ≤ z ∧ z < 1 - ξ := fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have p1 : ∀ z ∈ Icc 0 x, 0 < 1 - ξ - z := fun z hz => by linarith [(hI z hz).2]
  have p2 : ∀ z ∈ Icc 0 x, 0 < ξ * z + (1 - ξ) := fun z hz => by nlinarith [(hI z hz).1]
  have p3 : ∀ z ∈ Icc 0 x, 0 < 1 - z := fun z hz => by linarith [(hI z hz).2]
  have p4 : ∀ z ∈ Icc 0 x, 0 < ξ * z + (1 - ξ) ^ 2 := fun z hz => by
    nlinarith [(hI z hz).1, pow_pos hy 2]
  have p5 : ∀ z ∈ Icc 0 x, 0 < ξ * z ^ 2 + (1 - ξ) ^ 2 := fun z hz => by positivity
  have cl : ∀ g : ℝ → ℝ, Continuous g → (∀ z ∈ Icc 0 x, 0 < g z) →
      ContinuousOn (fun z => log (g z)) (Icc 0 x) := fun g hg hp =>
    hg.continuousOn.log fun z hz => (hp z hz).ne'
  have c0 := i5Li₂_continuousOn_comp (f := fun z => z) (s := Icc 0 x) continuousOn_id
    fun z hz => ⟨by linarith [(hI z hz).1], by linarith [(hI z hz).2]⟩
  have c1 := i5Li₂_continuousOn_comp (f := fun z => z / (1 - ξ)) (s := Icc 0 x) (by fun_prop)
    fun z hz => ⟨by have := div_nonneg (hI z hz).1 hy.le; linarith,
      (div_le_one hy).mpr (hI z hz).2.le⟩
  have c2 := i5Li₂_continuousOn_comp (f := fun z => ξ / (1 - z)) (s := Icc 0 x)
    (continuousOn_const.div (by fun_prop) fun z hz => (p3 z hz).ne')
    fun z hz => ⟨by have := div_pos h0 (p3 z hz); linarith,
      (div_le_one (p3 z hz)).mpr (by linarith [(hI z hz).2])⟩
  have c4 := i5Li₂_continuousOn_comp (f := fun z => -(ξ * z / (1 - ξ))) (s := Icc 0 x)
    (by fun_prop) fun z hz => ⟨by
      rw [neg_le_neg_iff, div_le_one hy]; nlinarith [(hI z hz).1, (hI z hz).2],
      by have := div_nonneg (mul_nonneg h0.le (hI z hz).1) hy.le; linarith⟩
  have c5 := i5Li₂_continuousOn_comp (f := fun z => z / (ξ * z + (1 - ξ))) (s := Icc 0 x)
    (continuousOn_id.div (by fun_prop) fun z hz => (p2 z hz).ne')
    fun z hz => ⟨by have := div_nonneg (hI z hz).1 (p2 z hz).le; linarith,
      (div_le_one (p2 z hz)).mpr (by nlinarith [(hI z hz).1, (hI z hz).2])⟩
  have c6 := i5Li₂_continuousOn_comp (f := fun z => -(ξ * z ^ 2 / (1 - ξ) ^ 2)) (s := Icc 0 x)
    (by fun_prop) fun z hz => ⟨by
      rw [neg_le_neg_iff, div_le_one (by positivity)]
      have a := (hI z hz).2
      have b := (hI z hz).1
      nlinarith [mul_le_mul a.le a.le b hy.le],
      by have := div_nonneg (mul_nonneg h0.le (sq_nonneg z)) (sq_nonneg (1 - ξ)); linarith⟩
  have c7 := i5Li₂_continuousOn_comp (f := fun z => ξ * (1 - ξ - z) / (1 - ξ)) (s := Icc 0 x)
    (by fun_prop) fun z hz => ⟨by
      have := div_nonneg (mul_nonneg h0.le (p1 z hz).le) hy.le; linarith,
      (div_le_one hy).mpr (by nlinarith [(hI z hz).1, p1 z hz])⟩
  have c9 := i5Li₂_continuousOn_comp (f := fun z => z / (ξ * z + (1 - ξ) ^ 2)) (s := Icc 0 x)
    (continuousOn_id.div (by fun_prop) fun z hz => (p4 z hz).ne')
    fun z hz => ⟨by have := div_nonneg (hI z hz).1 (p4 z hz).le; linarith,
      (div_le_one (p4 z hz)).mpr (by nlinarith [(hI z hz).1, (hI z hz).2])⟩
  have c10 := i5Li₂_continuousOn_comp (f := fun z => ξ * (1 - ξ) / (ξ * z + (1 - ξ)))
    (s := Icc 0 x) (continuousOn_const.div (by fun_prop) fun z hz => (p2 z hz).ne')
    fun z hz => ⟨by have := div_pos (mul_pos h0 hy) (p2 z hz); linarith,
      (div_le_one (p2 z hz)).mpr (by nlinarith [(hI z hz).1])⟩
  have c13 := i5Li₂_continuousOn_comp (f := fun z => ξ * z * (1 - z) / (ξ * z + (1 - ξ) ^ 2))
    (s := Icc 0 x) (ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => (p4 z hz).ne')
    fun z hz => ⟨by
      have := div_nonneg (mul_nonneg (mul_nonneg h0.le (hI z hz).1) (p3 z hz).le) (p4 z hz).le
      linarith, (div_le_one (p4 z hz)).mpr (by
        have b := (hI z hz).1
        nlinarith [mul_nonneg (mul_nonneg h0.le b) b, pow_pos hy 2])⟩
  have cD := i5Li₂_continuousOn_comp
    (f := fun z => ξ * z ^ 3 * (ξ * z + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - z))) (s := Icc 0 x)
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz =>
      (mul_pos (pow_pos hy 4) (p3 z hz)).ne') fun z hz => ⟨by
      have := div_nonneg (mul_nonneg (mul_nonneg h0.le (pow_nonneg (hI z hz).1 3))
        (p4 z hz).le) (mul_pos (pow_pos hy 4) (p3 z hz)).le
      linarith, (div_le_one (mul_pos (pow_pos hy 4) (p3 z hz))).mpr (by
      have a : z ^ 3 ≤ (1 - ξ) ^ 3 := pow_le_pow_left₀ (hI z hz).1 (hI z hz).2.le 3
      have b : ξ * z + (1 - ξ) ^ 2 ≤ ξ * (1 - ξ) + (1 - ξ) ^ 2 := by nlinarith [(hI z hz).2]
      have c : ξ * z ^ 3 * (ξ * z + (1 - ξ) ^ 2) ≤ ξ * (1 - ξ) ^ 3 * (1 - ξ) := by
        calc ξ * z ^ 3 * (ξ * z + (1 - ξ) ^ 2) ≤
            ξ * (1 - ξ) ^ 3 * (ξ * (1 - ξ) + (1 - ξ) ^ 2) := by
              have := (p4 z hz).le
              gcongr
          _ = ξ * (1 - ξ) ^ 3 * (1 - ξ) := by ring
      nlinarith [pow_pos hy 4, (hI z hz).2])⟩
  have g1 := cl (fun z => 1 - ξ - z) (by fun_prop) p1
  have g2 := cl (fun z => ξ * z + (1 - ξ)) (by fun_prop) p2
  have g3 := cl (fun z => 1 - z) (by fun_prop) p3
  have g4 := cl (fun z => ξ * z + (1 - ξ) ^ 2) (by fun_prop) p4
  have hc : ContinuousOn F (Icc 0 x) := by
    have e : F = fun z => Li₂ (ξ * z ^ 3 * (ξ * z + (1 - ξ) ^ 2) / ((1 - ξ) ^ 4 * (1 - z))) -
        (-2 * Li₂ z + 2 * Li₂ (z / (1 - ξ)) + Li₂ (ξ / (1 - z)) + 2 * Li₂ (-(ξ * z / (1 - ξ))) -
        Li₂ (z / (ξ * z + (1 - ξ))) + 2 * Li₂ (-(ξ * z ^ 2 / (1 - ξ) ^ 2)) -
        2 * Li₂ (ξ * (1 - ξ - z) / (1 - ξ)) + Li₂ (z / (ξ * z + (1 - ξ) ^ 2)) +
        Li₂ (ξ * (1 - ξ) / (ξ * z + (1 - ξ))) - Li₂ (ξ * z * (1 - z) / (ξ * z + (1 - ξ) ^ 2)) -
        2 * log (1 - ξ - z) * log (ξ * z + (1 - ξ) ^ 2) + 2 * log (1 - ξ - z) * log (1 - ξ) +
        log (ξ * z + (1 - ξ)) * log (1 - z) - log (ξ * z + (1 - ξ)) * log (ξ * z + (1 - ξ) ^ 2) +
        log (ξ * z + (1 - ξ)) * log (1 - ξ) + log (1 - z) * log (ξ * z + (1 - ξ) ^ 2) -
        4 * log (1 - z) * log (1 - ξ) + 3 * log (ξ * z + (1 - ξ) ^ 2) * log (1 - ξ) -
        3 * log (1 - ξ) ^ 2) := rfl
    rw [e]
    have k := continuousOn_const (c := log (1 - ξ)) (s := Icc (0 : ℝ) x)
    exact cD.sub ((((((((((((((((((continuousOn_const.mul c0).add (continuousOn_const.mul c1)).add
      c2).add (continuousOn_const.mul c4)).sub c5).add (continuousOn_const.mul c6)).sub
      (continuousOn_const.mul c7)).add c9).add c10).sub c13).sub
      ((continuousOn_const.mul g1).mul g4)).add ((continuousOn_const.mul g1).mul k)).add
      (g2.mul g3)).sub (g2.mul g4)).add (g2.mul k)).add (g3.mul g4)).sub
      ((continuousOn_const.mul g3).mul k)).add ((continuousOn_const.mul g4).mul k) |>.sub
      continuousOn_const)
  obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0) hx hc
    fun z hz => hasDerivAt_i5C1D3 ⟨h0, h1⟩ hz.1 (by linarith [hz.2])
  have hF0 : F 0 = 0 := by
    simp only [hF, i5C1D3R]
    norm_num
    rw [show ξ * (1 - ξ) / (1 - ξ) = ξ by field_simp]
    ring
  have : F x = F 0 := by
    have := hc2.symm
    rw [div_eq_zero_iff, sub_eq_zero] at this
    rcases this with h | h
    · exact h
    · linarith
  have h2 := this.trans hF0
  simp only [hF] at h2
  linarith

end QED.ThreeLoopD
