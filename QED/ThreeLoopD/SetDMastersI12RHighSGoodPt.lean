/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighSGood
public import QED.ThreeLoopD.SetDMastersI12RHighPt

/-!
# Set (d), master `I₁₂`: the pointwise `ε`-derivatives of the good part

At each point of `(0, 2) × (0, ∞) × (0, 1)` the good part `QED.ThreeLoopD.i12HSGood` of the
bulk remainder is, for each of its two scales `H = h(x)`, `H = h(0)`, a sum of five terms
`C e^{λε}` or `C ε e^{λε}`: with `r = s k / H` and
`Λ = log x + 2 log s + log u - 2 log (1 - u) - log H` (`QED.ThreeLoopD.i12HSLam`),

  `x ^ (ε - 1) s ^ (2ε - 1) w(u) H ^ (-ε - 1) D(s, k/H) = e^{Λε} / (x s H) ·
    [(r + 1)²/r e^{-3ε log (r + 1)} - r e^{-3ε log r} - 1/r - (2 - 3ε) e^{-3ε log r · 1_{s ≥ 1}}]`.

Hence the `n`-th derivative at `ε = 0` is the polynomial in logarithms
`QED.ThreeLoopD.i12HSGoodHDn n x s u H` (scale `h(x)` minus scale `h(0)`). These are the
integrands `Good_n` of the order-`n` split `∫_{Reg} W_n = ∫ Good_n + ∫ (W_n - Good_n)`.

## Main results

* `QED.ThreeLoopD.differentiable_i12HSGoodH`.
* `QED.ThreeLoopD.iteratedDeriv_i12HSGoodH`, `QED.ThreeLoopD.iteratedDeriv_i12HSGood`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- The logarithmic exponent of the prefactor `x ^ (ε - 1) s ^ (2ε - 1) w(u) H ^ (-ε - 1)`. -/
noncomputable def i12HSLam (x s u H : ℝ) : ℝ :=
  Real.log x + 2 * Real.log s + Real.log u + -2 * Real.log (1 - u) + -Real.log H

/-- The pointwise `n`-th `ε`-derivative at `0` of one scale `H` of the good part,
`x ^ (ε - 1) s ^ (2ε - 1) w(u) H ^ (-ε - 1) D(s, k/H)`: five terms `C λⁿ` or `C n λⁿ⁻¹`
(`r = s k / H`, `Λ = QED.ThreeLoopD.i12HSLam`). -/
noncomputable def i12HSGoodHDn (n : ℕ) (x s u H : ℝ) : ℝ :=
  (s * (i12HSk u / H) + 1) ^ 2 / (s * (i12HSk u / H)) / (x * s * H) *
      (i12HSLam x s u H + -3 * Real.log (s * (i12HSk u / H) + 1)) ^ n +
    -(s * (i12HSk u / H)) / (x * s * H) *
      (i12HSLam x s u H + -3 * Real.log (s * (i12HSk u / H))) ^ n +
    -1 / (s * (i12HSk u / H)) / (x * s * H) * i12HSLam x s u H ^ n +
    if s < 1 then
      -2 / (x * s * H) * i12HSLam x s u H ^ n +
        3 / (x * s * H) * (n * i12HSLam x s u H ^ (n - 1))
    else
      -2 / (x * s * H) * (i12HSLam x s u H + -3 * Real.log (s * (i12HSk u / H))) ^ n +
        3 / (x * s * H) * (n * (i12HSLam x s u H + -3 * Real.log (s * (i12HSk u / H))) ^ (n - 1))

theorem i12HS_cpow_neg_two_mul {y : ℝ} (hy : 0 < y) (ε : ℂ) :
    (y : ℂ) ^ (-2 * ε) = exp (((-2 * Real.log y : ℝ) : ℂ) * ε) := by
  rw [i12_cpow_lin hy]; push_cast; ring_nf

theorem i12HS_cpow_neg_sub_one {y : ℝ} (hy : 0 < y) (ε : ℂ) :
    (y : ℂ) ^ (-ε - 1) = exp (((-Real.log y : ℝ) : ℂ) * ε) / y := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  rw [cpow_sub _ _ hy', cpow_one, i12_cpow_lin hy]; push_cast; ring_nf

/-- The prefactor as one exponential. -/
theorem i12HS_pre_eq {x s u H : ℝ} (hx : 0 < x) (hs : 0 < s) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hH : 0 < H) (ε : ℂ) :
    (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u * (H : ℂ) ^ (-ε - 1) =
      exp ((i12HSLam x s u H : ℂ) * ε) / ((x * s * H : ℝ) : ℂ) := by
  have hv : 0 < 1 - u := by linarith [hu.2]
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hH' : (H : ℂ) ≠ 0 := ofReal_ne_zero.mpr hH.ne'
  simp only [i12HSw, i12HSLam]
  rw [i12_cpow_sub_one hx, i12_cpow_two_mul_sub_one hs, i12_cpow_self hu.1,
    i12HS_cpow_neg_two_mul hv, i12HS_cpow_neg_sub_one hH]
  simp only [i12_exp_add_mul]
  push_cast
  field_simp

/-- **The pointwise derivatives of one scale of the good part.** -/
theorem iteratedDeriv_i12HSGoodH {x s u H : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hH : 0 < H) (n : ℕ) :
    iteratedDeriv n (fun ε => (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
      ((H : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / H))) 0 = i12HSGoodHDn n x s u H := by
  have hk : 0 < i12HSk u := div_pos hu.1 (by linarith [hu.2])
  set r := s * (i12HSk u / H) with hrd
  have hr : 0 < r := by positivity
  have hr1 : 0 < r + 1 := by linarith
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hxsH : ((x * s * H : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  set Λ := i12HSLam x s u H with hΛd
  have hpre := i12HS_pre_eq hx hs hu hH
  have hD : ∀ ε : ℂ, i12HSD ε s (i12HSk u / H) =
      ((r + 1) ^ 2 / r : ℝ) * exp (((-3 * Real.log (r + 1) : ℝ) : ℂ) * ε) -
        (r : ℂ) * exp (((-3 * Real.log r : ℝ) : ℂ) * ε) - 1 / (r : ℂ) -
        (if s < 1 then (2 - 3 * ε) else
          (2 - 3 * ε) * exp (((-3 * Real.log r : ℝ) : ℂ) * ε)) := by
    intro ε
    simp only [i12HSD, i12Phi0, ← hrd, mul_one, ofReal_one, one_cpow]
    rw [i12_cpow_two_sub_three_mul hr1, i12_cpow_two_sub_three_mul hr,
      i12_cpow_neg_three_mul hr]
    push_cast
    field_simp
  have hsplit : ∀ ε : ℂ, (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
      ((H : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / H)) =
      exp ((Λ : ℂ) * ε) / ((x * s * H : ℝ) : ℂ) * i12HSD ε s (i12HSk u / H) := by
    intro ε; rw [← hpre ε]; ring
  by_cases hs1 : s < 1
  · have hfun : (fun ε => (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
        ((H : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / H))) = fun ε =>
        (((r + 1) ^ 2 / r / (x * s * H) : ℝ) : ℂ) *
            exp (((Λ + -3 * Real.log (r + 1) : ℝ) : ℂ) * ε) +
          ((-r / (x * s * H) : ℝ) : ℂ) * exp (((Λ + -3 * Real.log r : ℝ) : ℂ) * ε) +
          ((-1 / r / (x * s * H) : ℝ) : ℂ) * exp ((Λ : ℂ) * ε) +
          ((-2 / (x * s * H) : ℝ) : ℂ) * exp ((Λ : ℂ) * ε) +
          ((3 / (x * s * H) : ℝ) : ℂ) * (ε * exp ((Λ : ℂ) * ε)) := by
      funext ε
      rw [hsplit, hD]
      simp only [hs1, ↓reduceIte]
      simp only [i12_exp_add_mul]
      push_cast at hxsH ⊢
      field_simp
      ring
    rw [hfun, iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero,
      i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_mul_exp_zero, i12HSGoodHDn, ← hrd, ← hΛd]
    simp only [hs1, ↓reduceIte]
    push_cast
    field_simp
    ring
  · have hfun : (fun ε => (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
        ((H : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / H))) = fun ε =>
        (((r + 1) ^ 2 / r / (x * s * H) : ℝ) : ℂ) *
            exp (((Λ + -3 * Real.log (r + 1) : ℝ) : ℂ) * ε) +
          ((-r / (x * s * H) : ℝ) : ℂ) * exp (((Λ + -3 * Real.log r : ℝ) : ℂ) * ε) +
          ((-1 / r / (x * s * H) : ℝ) : ℂ) * exp ((Λ : ℂ) * ε) +
          ((-2 / (x * s * H) : ℝ) : ℂ) * exp (((Λ + -3 * Real.log r : ℝ) : ℂ) * ε) +
          ((3 / (x * s * H) : ℝ) : ℂ) * (ε * exp (((Λ + -3 * Real.log r : ℝ) : ℂ) * ε)) := by
      funext ε
      rw [hsplit, hD]
      simp only [hs1, ↓reduceIte]
      simp only [i12_exp_add_mul]
      push_cast at hxsH ⊢
      field_simp
      ring
    rw [hfun, iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_exp_zero,
      i12_iteratedDeriv_exp_zero, i12_iteratedDeriv_mul_exp_zero, i12HSGoodHDn, ← hrd, ← hΛd]
    simp only [hs1, ↓reduceIte]
    push_cast
    field_simp
    ring

theorem differentiable_i12HSGoodH {x s u H : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hH : 0 < H) :
    Differentiable ℂ fun ε => (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
      ((H : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / H)) := by
  have hu0 : 0 < u := hu.1
  have hv : 0 < 1 - u := by linarith [hu.2]
  have hr : 0 < s * (i12HSk u / H) := mul_pos hs (div_pos (div_pos hu.1 hv) hH)
  have hP := differentiable_i12Phi0 hr one_pos
  unfold i12HSD i12HSw
  split_ifs <;>
    fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr (ne_of_gt (by assumption))))

/-- **The pointwise `n`-th `ε`-derivative of the good part** at `ε = 0`, for `0 < x < 2`,
`s > 0`, `u ∈ (0, 1)`: the scale `h(x)` minus the scale `h(0)`. -/
theorem iteratedDeriv_i12HSGood {x s u : ℝ} (hx : 0 < x) (hx2 : x < 2) (hs : 0 < s)
    (hu : u ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    iteratedDeriv n (fun ε => i12HSGood ε x s u) 0 =
      i12HSGoodHDn n x s u (i12H x) - i12HSGoodHDn n x s u (i12H 0) := by
  have hA := i12HS_h_pos hx2
  have hB := i12HS_h_pos (x := 0) (by norm_num)
  have e : (fun ε => i12HSGood ε x s u) = fun ε =>
      (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
          (((i12H x : ℝ) : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / i12H x)) -
        (x : ℂ) ^ (ε - 1) * (s : ℂ) ^ (2 * ε - 1) * i12HSw ε u *
          (((i12H 0 : ℝ) : ℂ) ^ (-ε - 1) * i12HSD ε s (i12HSk u / i12H 0)) := by
    funext ε; simp only [i12HSGood]; ring
  rw [e, iteratedDeriv_fun_sub (differentiable_i12HSGoodH hx hs hu hA).contDiff.contDiffAt
    (differentiable_i12HSGoodH hx hs hu hB).contDiff.contDiffAt,
    iteratedDeriv_i12HSGoodH hx hs hu hA, iteratedDeriv_i12HSGoodH hx hs hu hB]

end QED.ThreeLoopD
