/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3
public import QED.ThreeLoopD.SetDMastersI13R4C

/-!
# Set (d), master `I₈`: the fourth coefficients of the integrands of `Rem`

The angular coefficient `A₄ = r C₄` (`QED.ThreeLoopD.i8AC_four`), where `C₄` is a combination of
`8ξ/(1 + ξ)` and fifteen harmonic polylogarithms of weight at most four with letters `0, -1`,
from `C₄' = t A₃/(1 + ξ)²` (`QED.ThreeLoopD.i8AC_succ_of`). With `λ = log t` and
`B₀ = 1`, `B₁ = 2β₁`, `B₂ = 2β₂ + β₁²`, `B₃ = 2β₃ + 2β₁β₂`, `B₄ = 2β₄ + 2β₁β₃ + β₂²`, the fourth
Taylor coefficient of `t ^ (1 - ε) b_ε² A_ε` is

  `p₄ = t ∑_{l ≤ 4} (-λ)^l / l! ∑_{i + j = 4 - l} Bᵢ Aⱼ`

(`QED.ThreeLoopD.i8P4`); that of the subtraction is `a₄` (`QED.ThreeLoopD.i8A4r`), with primitive
`A₄` (`QED.ThreeLoopD.i8Prim4`), `A₄(1) = 473 - 11π² - 28ζ(3) - π⁴/45`.

## Main results

* `QED.ThreeLoopD.i8AC_four`.
* `QED.ThreeLoopD.i8Dsl_remInt1_four`, `QED.ThreeLoopD.i8Dsl_remInt2_four`.
* `QED.ThreeLoopD.hasDerivAt_i8Prim4`, `QED.ThreeLoopD.i8Prim4_one`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### `A₄` -/

/-- `A₄` in the variable `ξ`. -/
noncomputable def i8A4x (x : ℝ) : ℝ :=
  (1 + x) / (1 - x) * (8 * x / (1 + x) - 4 * hpl [negOne] x + 4 * hpl [negOne, negOne] x -
    2 * hpl [zero, negOne] x - 4 * hpl [negOne, negOne, negOne] x +
    2 * hpl [negOne, zero, negOne] x + 2 * hpl [zero, negOne, negOne] x -
    hpl [zero, zero, negOne] x + 8 * hpl [negOne, negOne, negOne, negOne] x -
    4 * hpl [negOne, negOne, zero, negOne] x - 4 * hpl [negOne, zero, negOne, negOne] x +
    2 * hpl [negOne, zero, zero, negOne] x - 4 * hpl [zero, negOne, negOne, negOne] x +
    2 * hpl [zero, negOne, zero, negOne] x + 2 * hpl [zero, zero, negOne, negOne] x -
    hpl [zero, zero, zero, negOne] x)

theorem i8AC_four_x {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8AC ((1 - x) ^ 2 / x) 4 = (i8A4x x : ℂ) := by
  have hlim : Tendsto (fun x => 8 * x / (1 + x) - 4 * hpl [negOne] x +
    4 * hpl [negOne, negOne] x - 2 * hpl [zero, negOne] x - 4 * hpl [negOne, negOne, negOne] x +
    2 * hpl [negOne, zero, negOne] x + 2 * hpl [zero, negOne, negOne] x -
    hpl [zero, zero, negOne] x + 8 * hpl [negOne, negOne, negOne, negOne] x -
    4 * hpl [negOne, negOne, zero, negOne] x - 4 * hpl [negOne, zero, negOne, negOne] x +
    2 * hpl [negOne, zero, zero, negOne] x - 4 * hpl [zero, negOne, negOne, negOne] x +
    2 * hpl [zero, negOne, zero, negOne] x + 2 * hpl [zero, zero, negOne, negOne] x -
    hpl [zero, zero, zero, negOne] x) (𝓝[>] 0) (𝓝 0) := by
    have := ((((((((((((((((i8_tendsto_rat_zero (c := 8)).sub
      ((tendsto_hpl_zero (w := [negOne]) (by simp)).const_mul 4)).add
      ((tendsto_hpl_zero (w := [negOne, negOne]) (by simp)).const_mul 4)).sub
      ((tendsto_hpl_zero (w := [zero, negOne]) (by simp)).const_mul 2)).sub
      ((tendsto_hpl_zero (w := [negOne, negOne, negOne]) (by simp)).const_mul 4)).add
      ((tendsto_hpl_zero (w := [negOne, zero, negOne]) (by simp)).const_mul 2)).add
      ((tendsto_hpl_zero (w := [zero, negOne, negOne]) (by simp)).const_mul 2)).sub
      (tendsto_hpl_zero (w := [zero, zero, negOne]) (by simp))).add
      ((tendsto_hpl_zero (w := [negOne, negOne, negOne, negOne]) (by simp)).const_mul 8)).sub
      ((tendsto_hpl_zero (w := [negOne, negOne, zero, negOne]) (by simp)).const_mul 4)).sub
      ((tendsto_hpl_zero (w := [negOne, zero, negOne, negOne]) (by simp)).const_mul 4)).add
      ((tendsto_hpl_zero (w := [negOne, zero, zero, negOne]) (by simp)).const_mul 2)).sub
      ((tendsto_hpl_zero (w := [zero, negOne, negOne, negOne]) (by simp)).const_mul 4)).add
      ((tendsto_hpl_zero (w := [zero, negOne, zero, negOne]) (by simp)).const_mul 2)).add
      ((tendsto_hpl_zero (w := [zero, zero, negOne, negOne]) (by simp)).const_mul 2)).sub
      (tendsto_hpl_zero (w := [zero, zero, zero, negOne]) (by simp)))
    simpa using this
  refine i8AC_succ_of (k := 3) (Ap := i8A3x) (fun y hy => i8AC_three_x hy) (fun y hy => ?_) hlim hx
    |>.trans ?_
  · have h0 : y ≠ 0 := hy.1.ne'
    have h1 : 1 - y ≠ 0 := by linarith [hy.2]
    have h2 : 1 + y ≠ 0 := by linarith [hy.1]
    have e := ((((((((((((((((((hasDerivAt_id' y).const_mul 8).div ((hasDerivAt_id' y).const_add 1)
      h2).sub
      ((hasDerivAt_hpl_cons negOne [] hy).const_mul 4)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hy).const_mul 4)).sub
      ((hasDerivAt_hpl_cons zero [negOne] hy).const_mul 2)).sub
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hy).const_mul 4)).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hy).const_mul 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hy).const_mul 2)).sub
      (hasDerivAt_hpl_cons zero [zero, negOne] hy)).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, negOne] hy).const_mul 8)).sub
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hy).const_mul 4)).sub
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hy).const_mul 4)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hy).const_mul 2)).sub
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hy).const_mul 4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hy).const_mul 2)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hy).const_mul 2)).sub
      (hasDerivAt_hpl_cons zero [zero, zero, negOne] hy))
    refine e.congr_deriv ?_
    unfold i8A3x
    simp only [kernel_negOne, kernel_zero, hpl_nil, OfNat.ofNat_ne_zero, ↓reduceIte]
    field_simp
    ring
  · unfold i8A4x; simp

theorem i8AC_four {t : ℝ} (ht : 0 < t) : i8AC t 4 = (i8A4x (i13Xi t) : ℂ) := by
  conv_lhs => rw [i13Xi_t ht.le]
  exact i8AC_four_x (i8_xi_mem ht)

/-! ### The coefficients `p₄` and `a₄` -/

/-- `p₄(t)`, the fourth coefficient of `t ^ (1 - ε) b_ε(t)² A_ε(t)`. -/
noncomputable def i8P4 (t : ℝ) : ℝ :=
  t * (i8A4x (i13Xi t) + 2 * i13Be1r t * i8A3x (i13Xi t) + (2 * i13Be2r t +
    i13Be1r t ^ 2) * i8A2x (i13Xi t) + (2 * i13Be3r t +
    2 * i13Be1r t * i13Be2r t) * i8A1x (i13Xi t) + (2 * i13Be4r t +
    2 * i13Be1r t * i13Be3r t + i13Be2r t ^ 2) * (i13Xi t / (1 - i13Xi t))) -
    t * Real.log t * (i8A3x (i13Xi t) + 2 * i13Be1r t * i8A2x (i13Xi t) + (2 * i13Be2r t +
    i13Be1r t ^ 2) * i8A1x (i13Xi t) + (2 * i13Be3r t +
    2 * i13Be1r t * i13Be2r t) * (i13Xi t / (1 - i13Xi t))) +
    t * Real.log t ^ 2 / 2 * (i8A2x (i13Xi t) + 2 * i13Be1r t * i8A1x (i13Xi t) +
    (2 * i13Be2r t + i13Be1r t ^ 2) * (i13Xi t / (1 - i13Xi t))) -
    t * Real.log t ^ 3 / 6 * (i8A1x (i13Xi t) + 2 * i13Be1r t * (i13Xi t / (1 - i13Xi t))) +
    t * Real.log t ^ 4 / 24 * ((i13Xi t / (1 - i13Xi t)))

/-- The fourth coefficient `a₄` of the large-`t` subtraction. -/
noncomputable def i8A4r (t : ℝ) : ℝ :=
  80 - 96 * Real.log t - 18 * Real.log t ^ 3 - 16 * zeta3 - 4 * π ^ 2 + 54 * Real.log t ^ 2 -
    π ^ 4 / 45 + 27 / 8 * Real.log t ^ 4 + 4 * Real.log t * π ^ 2 + 12 * Real.log t * zeta3 -
    3 / 2 * π ^ 2 * Real.log t ^ 2 + (-2553 / 16 + 10 * zeta3 - 385 / 8 * Real.log t ^ 2 +
    Real.log t ^ 3 / 4 + π ^ 4 / 30 + 49 / 12 * π ^ 2 + 179 / 24 * Real.log t ^ 4 +
    1131 / 8 * Real.log t + 20 * Real.log t * zeta3 - 19 / 6 * π ^ 2 * Real.log t ^ 2 -
    Real.log t * π ^ 2 / 2) / t

theorem i8R1C_four (t : ℝ) :
    i8R1C t 4 = t * (i8AC t 4 + 2 * i13BubC t 1 * i8AC t 3 + (2 * i13BubC t 2 +
      i13BubC t 1 ^ 2) * i8AC t 2 + (2 * i13BubC t 3 +
      2 * i13BubC t 1 * i13BubC t 2) * i8AC t 1 + (2 * i13BubC t 4 +
      2 * i13BubC t 1 * i13BubC t 3 + i13BubC t 2 ^ 2) * i8AC t 0) -
      t * (Real.log t : ℂ) * (i8AC t 3 + 2 * i13BubC t 1 * i8AC t 2 + (2 * i13BubC t 2 +
      i13BubC t 1 ^ 2) * i8AC t 1 + (2 * i13BubC t 3 +
      2 * i13BubC t 1 * i13BubC t 2) * i8AC t 0) + t * (Real.log t : ℂ) ^ 2 / 2 * (i8AC t 2 +
      2 * i13BubC t 1 * i8AC t 1 + (2 * i13BubC t 2 + i13BubC t 1 ^ 2) * i8AC t 0) -
      t * (Real.log t : ℂ) ^ 3 / 6 * (i8AC t 1 + 2 * i13BubC t 1 * i8AC t 0) +
      t * (Real.log t : ℂ) ^ 4 / 24 * (i8AC t 0) := by
  unfold i8R1C
  rw [show i13Cauchy i8NC (i8JC t) = i8AC t from rfl]
  simp only [i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    i13BubC_zero, Complex.cpow_one]
  norm_num [i13BubC_zero, Nat.factorial]
  ring

theorem i8AsymC_four {t : ℝ} (ht : 0 < t) : i8AsymC t 4 = (i8A4r t : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [i8AsymC, i13A0C, i13A1C, i13B0C, i13Cauchy, i13TpC,
    Finset.sum_range_succ, Finset.sum_range_zero, i13GC_zero, i13GC_one, i13GC_two, i13GC_three,
    i13GC_four, Complex.cpow_zero, Complex.cpow_neg_one]
  unfold i8A4r
  norm_num [i13GC_zero, i13GC_one, i13GC_two, i13GC_three, i13GC_four, Nat.factorial]
  field_simp
  ring

theorem i8Dsl_remInt1_four {t : ℝ} (ht : 0 < t) :
    i13Dsl (i8RemInt1 t) 4 0 = (i8P4 t : ℂ) := by
  rw [(i8Jet_remInt1 ht).dsl_eq, i8R1C_four, i13BubC_one ht, i13BubC_two ht, i13BubC_three ht,
    i13BubC_four ht, i8AC_zero ht, i8AC_one ht, i8AC_two ht, i8AC_three ht, i8AC_four ht]
  unfold i8P4
  push_cast
  ring

theorem i8Dsl_remInt2_four {t : ℝ} (ht : 0 < t) :
    i13Dsl (i8RemInt2 t) 4 0 = ((i8P4 t - i8A4r t : ℝ) : ℂ) := by
  rw [(i8Jet_remInt2 ht).dsl_eq, i8R1C_four, i13BubC_one ht, i13BubC_two ht, i13BubC_three ht,
    i13BubC_four ht, i8AC_zero ht, i8AC_one ht, i8AC_two ht, i8AC_three ht, i8AC_four ht,
    i8AsymC_four ht]
  unfold i8P4
  push_cast
  ring

/-! ### The primitive of `a₄` -/

/-- The primitive `A₄` of `a₄`. -/
noncomputable def i8Prim4 (t : ℝ) : ℝ :=
    (27 / 8) * (t * Real.log t ^ 4) +
    (-63 / 2) * (t * Real.log t ^ 3) +
    (297 / 2 - 3 / 2 * π ^ 2) * (t * Real.log t ^ 2) +
    (-393 + 7 * π ^ 2 + 12 * zeta3) * (t * Real.log t) +
    (473 - 28 * zeta3 - 11 * π ^ 2 - π ^ 2 ^ 2 / 45) * t +
    (179 / 120) * Real.log t ^ 5 +
    (1 / 16) * Real.log t ^ 4 +
    (-385 / 24 - 19 / 18 * π ^ 2) * Real.log t ^ 3 +
    (1131 / 16 + 10 * zeta3 - π ^ 2 / 4) * Real.log t ^ 2 +
    (-2553 / 16 + 10 * zeta3 + π ^ 2 ^ 2 / 30 + 49 / 12 * π ^ 2) * Real.log t

theorem hasDerivAt_i8Prim4 {t : ℝ} (ht : 0 < t) : HasDerivAt i8Prim4 (i8A4r t) t := by
  have L := Real.hasDerivAt_log ht.ne'
  have X := hasDerivAt_id' t
  have e := (((((((((((X.mul (L.pow 4)).const_mul (27 / 8)).add
    ((X.mul (L.pow 3)).const_mul (-63 / 2))).add
    ((X.mul (L.pow 2)).const_mul (297 / 2 - 3 / 2 * π ^ 2))).add
    ((X.mul L).const_mul (-393 + 7 * π ^ 2 + 12 * zeta3))).add
    (X.const_mul (473 - 28 * zeta3 - 11 * π ^ 2 - π ^ 2 ^ 2 / 45))).add
    ((L.pow 5).const_mul (179 / 120))).add
    ((L.pow 4).const_mul (1 / 16))).add
    ((L.pow 3).const_mul (-385 / 24 - 19 / 18 * π ^ 2))).add
    ((L.pow 2).const_mul (1131 / 16 + 10 * zeta3 - π ^ 2 / 4))).add
    (L.const_mul (-2553 / 16 + 10 * zeta3 + π ^ 2 ^ 2 / 30 + 49 / 12 * π ^ 2)))
  unfold i8Prim4
  refine e.congr_deriv ?_
  unfold i8A4r
  simp only [Pi.pow_apply]
  field_simp
  ring


theorem i8Prim4_one : i8Prim4 1 = 473 - 11 * π ^ 2 - 28 * zeta3 - π ^ 4 / 45 := by
  unfold i8Prim4
  norm_num
  ring

end QED.ThreeLoopD
