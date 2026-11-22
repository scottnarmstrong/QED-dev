/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemKuT
public import QED.Polylog.HPLShuffle

/-!
# Set (d), master `I₉`: an antiderivative of the outer `K_u` integrand

By `QED.ThreeLoopD.integral_log_one_sub_mul_i9A1Dens_eq` and
`QED.ThreeLoopD.integral_log_i9KuP_sq`, `K_u = ∫₀¹ I(w) dw` with

  `I(w) = F(w) · 3 (1 - w²)/(2 w²) · T(w)`,   `F(w) = w + (1 - w) log (1 - w)`,

`T(w)` the closed form `QED.ThreeLoopD.i9KuT` in harmonic polylogarithms over `{0, 1, -1}`.
The antiderivative `Ψ` is a sum of `21` terms `ρ(w) H(v; w)` over words `v` of weight at most
four, with `ρ(w) = a/w + b + c w + d w²` (`QED.ThreeLoopD.i9KuRat`). The check `Ψ' = I`
rewrites every word of weight two or three that is not a Lyndon word (for the order
`0 < 1 < -1`) by a shuffle product, after which both sides are the same polynomial in the
Lyndon words.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i9KuPsi`: `Ψ'(w) = I(w)` on `(0, 1)`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The coefficient `a/w + b + c w + d w²`. -/
noncomputable def i9KuRat (a b c d w : ℝ) : ℝ := a / w + b + c * w + d * w ^ 2

/-- The derivative `-a/w² + c + 2 d w` of `QED.ThreeLoopD.i9KuRat`. -/
noncomputable def i9KuRat' (a c d w : ℝ) : ℝ := -a / w ^ 2 + c + 2 * d * w

theorem hasDerivAt_i9KuRat (a b c d : ℝ) {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (i9KuRat a b c d) (i9KuRat' a c d w) w := by
  have h1 := (hasDerivAt_inv hw).const_mul a
  have h2 := (hasDerivAt_id' w).const_mul c
  have h3 := (hasDerivAt_pow 2 w).const_mul d
  have h := ((h1.add_const b).add h2).add h3
  convert h using 1
  · funext x
    simp [i9KuRat, div_eq_mul_inv]
  · simp only [i9KuRat']
    field_simp
    ring

/-- The outer integrand `I(w) = F(w) · 3 (1 - w²)/(2 w²) · T(w)`. -/
noncomputable def i9KuI (w : ℝ) : ℝ := i9KuF w * (3 * (1 - w ^ 2) / (2 * w ^ 2)) * i9KuT w

/-! ### Shuffle reductions of the non-Lyndon words -/

section Words

variable {x : ℝ}

theorem i9Ku_hpl_m0 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero] x =
      (-1) * hpl [zero, negOne] x +
        (1) * (hpl [negOne] x * hpl [zero] x) := by
  have h0 := hpl_mul_hpl [negOne] [zero] hx
  simp [shuffle_cons_cons] at h0
  linear_combination (-1) * h0

theorem i9Ku_hpl_m1 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one] x =
      (-1) * hpl [one, negOne] x +
        (1) * (hpl [negOne] x * hpl [one] x) := by
  have h0 := hpl_mul_hpl [negOne] [one] hx
  simp [shuffle_cons_cons] at h0
  linear_combination (-1) * h0

theorem i9Ku_hpl_10 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero] x =
      (-1) * hpl [zero, one] x +
        (1) * (hpl [zero] x * hpl [one] x) := by
  have h0 := hpl_mul_hpl [zero] [one] hx
  simp [shuffle_cons_cons] at h0
  linear_combination (-1) * h0

theorem i9Ku_hpl_11 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one] x =
      (1 / 2) * (hpl [one] x * hpl [one] x) := by
  have h0 := hpl_mul_hpl [one] [one] hx
  simp [shuffle_cons_cons] at h0
  linear_combination (-1 / 2) * h0

theorem i9Ku_hpl_m01 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero, one] x =
      (-1) * hpl [zero, one, negOne] x +
        (-1) * hpl [zero, negOne, one] x +
        (1) * (hpl [negOne] x * hpl [zero, one] x) := by
  have h0 := hpl_mul_hpl [negOne] [zero, one] hx
  simp [shuffle_cons_cons] at h0
  linear_combination (-1) * h0

theorem i9Ku_hpl_m10 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one, zero] x =
      (1) * hpl [zero, one, negOne] x +
        (1) * (hpl [zero] x * hpl [negOne, one] x) +
        (-1) * (hpl [negOne] x * hpl [zero, one] x) := by
  have h0 := hpl_mul_hpl [zero] [negOne, one] hx
  have h1 := hpl_mul_hpl [negOne] [zero, one] hx
  simp [shuffle_cons_cons] at h0 h1
  linear_combination (-1) * h0 + (1) * h1

theorem i9Ku_hpl_1m0 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne, zero] x =
      (1) * hpl [zero, negOne, one] x +
        (1) * (hpl [zero] x * hpl [one, negOne] x) +
        (-1) * (hpl [one] x * hpl [zero, negOne] x) := by
  have h0 := hpl_mul_hpl [zero] [one, negOne] hx
  have h1 := hpl_mul_hpl [one] [zero, negOne] hx
  simp [shuffle_cons_cons] at h0 h1
  linear_combination (-1) * h0 + (1) * h1

theorem i9Ku_hpl_101 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, one] x =
      (-2) * hpl [zero, one, one] x +
        (1) * (hpl [one] x * hpl [zero, one] x) := by
  have h0 := hpl_mul_hpl [one] [zero, one] hx
  simp [shuffle_cons_cons] at h0
  linear_combination (-1) * h0

theorem i9Ku_hpl_110 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, zero] x =
      (1) * hpl [zero, one, one] x +
        (1) * (hpl [zero] x * hpl [one, one] x) +
        (-1) * (hpl [one] x * hpl [zero, one] x) := by
  have h0 := hpl_mul_hpl [zero] [one, one] hx
  have h1 := hpl_mul_hpl [one] [zero, one] hx
  simp [shuffle_cons_cons] at h0 h1
  linear_combination (-1) * h0 + (1) * h1

theorem i9Ku_hpl_111 (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, one] x =
      (1 / 3) * (hpl [one] x * hpl [one, one] x) := by
  have h0 := hpl_mul_hpl [one] [one, one] hx
  simp [shuffle_cons_cons] at h0
  linear_combination (-1 / 3) * h0

end Words

/-! ### The antiderivative -/

/-- **The antiderivative** `Ψ` of the outer integrand. -/
noncomputable def i9KuPsi (w : ℝ) : ℝ :=
  i9KuRat (0) (0) (9 * (π ^ 2 / 6)) (9 / 2 * (π ^ 2 / 6)) w +
    i9KuRat (0) (0) (21) (0) w * hpl [zero] w +
    i9KuRat (0) (-21 + -3 * (π ^ 2 / 6)) (21) (3 * (π ^ 2 / 6)) w * hpl [one] w +
    i9KuRat (0) (-33 / 2) (-21) (-9 / 2) w * hpl [negOne, zero] w +
    i9KuRat (0) (-6 * (π ^ 2 / 6)) (-12) (-9) w * hpl [zero, one] w +
    i9KuRat (0) (-9 / 2) (9) (-9 / 2) w * hpl [one, zero] w +
    i9KuRat (0) (-9) (18) (-9) w * hpl [one, one] w +
    i9KuRat (-6) (-9) (-6) (-3) w * hpl [negOne, zero, one] w +
    i9KuRat (-6) (-9) (-6) (-3) w * hpl [negOne, one, zero] w +
    i9KuRat (0) (-24) (0) (-12) w * hpl [zero, one, one] w +
    i9KuRat (-6) (15) (-6) (-3) w * hpl [one, negOne, zero] w +
    i9KuRat (6) (-3) (6) (-9) w * hpl [one, zero, one] w +
    i9KuRat (12) (-18) (12) (-6) w * hpl [one, one, zero] w +
    i9KuRat (36) (-54) (36) (-18) w * hpl [one, one, one] w +
    i9KuRat (0) (6) (0) (0) w * hpl [zero, negOne, zero, one] w +
    i9KuRat (0) (6) (0) (0) w * hpl [zero, negOne, one, zero] w +
    i9KuRat (0) (24) (0) (0) w * hpl [zero, zero, one, one] w +
    i9KuRat (0) (6) (0) (0) w * hpl [zero, one, negOne, zero] w +
    i9KuRat (0) (18) (0) (0) w * hpl [zero, one, zero, one] w +
    i9KuRat (0) (12) (0) (0) w * hpl [zero, one, one, zero] w +
    i9KuRat (0) (36) (0) (0) w * hpl [zero, one, one, one] w

theorem hasDerivAt_i9KuPsi {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i9KuPsi (i9KuI w) w := by
  have hw0 : w ≠ 0 := hw.1.ne'
  have hw1 : 1 - w ≠ 0 := sub_ne_zero.2 hw.2.ne'
  have hw2 : 1 + w ≠ 0 := by linarith [hw.1]
  have d0 := (hasDerivAt_i9KuRat (0) (0) (9 * (π ^ 2 / 6)) (9 / 2 * (π ^ 2 / 6)) hw0)
  have d1 := d0.add
    ((hasDerivAt_i9KuRat (0) (0) (21) (0) hw0).mul
        (hasDerivAt_hpl_cons zero [] hw))
  have d2 := d1.add
    ((hasDerivAt_i9KuRat (0) (-21 + -3 * (π ^ 2 / 6)) (21) (3 * (π ^ 2 / 6)) hw0).mul
        (hasDerivAt_hpl_cons one [] hw))
  have d3 := d2.add
    ((hasDerivAt_i9KuRat (0) (-33 / 2) (-21) (-9 / 2) hw0).mul
        (hasDerivAt_hpl_cons negOne [zero] hw))
  have d4 := d3.add
    ((hasDerivAt_i9KuRat (0) (-6 * (π ^ 2 / 6)) (-12) (-9) hw0).mul
        (hasDerivAt_hpl_cons zero [one] hw))
  have d5 := d4.add
    ((hasDerivAt_i9KuRat (0) (-9 / 2) (9) (-9 / 2) hw0).mul
        (hasDerivAt_hpl_cons one [zero] hw))
  have d6 := d5.add
    ((hasDerivAt_i9KuRat (0) (-9) (18) (-9) hw0).mul
        (hasDerivAt_hpl_cons one [one] hw))
  have d7 := d6.add
    ((hasDerivAt_i9KuRat (-6) (-9) (-6) (-3) hw0).mul
        (hasDerivAt_hpl_cons negOne [zero, one] hw))
  have d8 := d7.add
    ((hasDerivAt_i9KuRat (-6) (-9) (-6) (-3) hw0).mul
        (hasDerivAt_hpl_cons negOne [one, zero] hw))
  have d9 := d8.add
    ((hasDerivAt_i9KuRat (0) (-24) (0) (-12) hw0).mul
        (hasDerivAt_hpl_cons zero [one, one] hw))
  have d10 := d9.add
    ((hasDerivAt_i9KuRat (-6) (15) (-6) (-3) hw0).mul
        (hasDerivAt_hpl_cons one [negOne, zero] hw))
  have d11 := d10.add
    ((hasDerivAt_i9KuRat (6) (-3) (6) (-9) hw0).mul
        (hasDerivAt_hpl_cons one [zero, one] hw))
  have d12 := d11.add
    ((hasDerivAt_i9KuRat (12) (-18) (12) (-6) hw0).mul
        (hasDerivAt_hpl_cons one [one, zero] hw))
  have d13 := d12.add
    ((hasDerivAt_i9KuRat (36) (-54) (36) (-18) hw0).mul
        (hasDerivAt_hpl_cons one [one, one] hw))
  have d14 := d13.add
    ((hasDerivAt_i9KuRat (0) (6) (0) (0) hw0).mul
        (hasDerivAt_hpl_cons zero [negOne, zero, one] hw))
  have d15 := d14.add
    ((hasDerivAt_i9KuRat (0) (6) (0) (0) hw0).mul
        (hasDerivAt_hpl_cons zero [negOne, one, zero] hw))
  have d16 := d15.add
    ((hasDerivAt_i9KuRat (0) (24) (0) (0) hw0).mul
        (hasDerivAt_hpl_cons zero [zero, one, one] hw))
  have d17 := d16.add
    ((hasDerivAt_i9KuRat (0) (6) (0) (0) hw0).mul
        (hasDerivAt_hpl_cons zero [one, negOne, zero] hw))
  have d18 := d17.add
    ((hasDerivAt_i9KuRat (0) (18) (0) (0) hw0).mul
        (hasDerivAt_hpl_cons zero [one, zero, one] hw))
  have d19 := d18.add
    ((hasDerivAt_i9KuRat (0) (12) (0) (0) hw0).mul
        (hasDerivAt_hpl_cons zero [one, one, zero] hw))
  have d20 := d19.add
    ((hasDerivAt_i9KuRat (0) (36) (0) (0) hw0).mul
        (hasDerivAt_hpl_cons zero [one, one, one] hw))
  refine d20.congr_deriv ?_
  simp only [i9KuRat, i9KuRat', kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  simp only [i9Ku_hpl_m01 hw, i9Ku_hpl_m10 hw, i9Ku_hpl_1m0 hw, i9Ku_hpl_101 hw,
    i9Ku_hpl_110 hw, i9Ku_hpl_111 hw]
  simp only [i9Ku_hpl_m0 hw, i9Ku_hpl_m1 hw, i9Ku_hpl_10 hw, i9Ku_hpl_11 hw]
  have hl : Real.log (1 - w) = -hpl [one] w := by rw [hpl_one hw]; ring
  unfold i9KuI i9KuF i9KuT
  rw [hl]
  field_simp
  ring

end QED.ThreeLoopD
