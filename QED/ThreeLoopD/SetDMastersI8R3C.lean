/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R2

/-!
# Set (d), master `I₈`: the third coefficients of the integrands of `Rem`

The angular coefficient `A₃ = r C₃` (`QED.ThreeLoopD.i8AC_three`), with

  `C₃ = 4ξ/(1 + ξ) - 2 H(-1) - H(0, -1) + 2 H(-1, -1) - H(0, 0, -1) + 2 H(-1, 0, -1)
    - 4 H(-1, -1, -1) + 2 H(0, -1, -1)`,

from `C₃' = t A₂/(1 + ξ)²` (`QED.ThreeLoopD.i8AC_succ_of`). With `λ = log t`, the third Taylor
coefficient of `t ^ (1 - ε) b_ε² A_ε` is

  `p₃ = t ((2β₃ + 2β₁β₂) A₀ + (2β₂ + β₁²) A₁ + 2β₁ A₂ + A₃) - t λ ((2β₂ + β₁²) A₀ + 2β₁ A₁ + A₂)
    + t λ²/2 (2β₁ A₀ + A₁) - t λ³/6 A₀`

(`QED.ThreeLoopD.i8P3`); that of the subtraction is `a₃` (`QED.ThreeLoopD.i8A3r`), with primitive
`A₃` (`QED.ThreeLoopD.i8Prim3`), `A₃(1) = 131 - 7π²/3 - 4ζ(3)`.

## Main results

* `QED.ThreeLoopD.i8AC_three`.
* `QED.ThreeLoopD.i8Dsl_remInt1_three`, `QED.ThreeLoopD.i8Dsl_remInt2_three`.
* `QED.ThreeLoopD.hasDerivAt_i8Prim3`, `QED.ThreeLoopD.i8Prim3_one`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### `A₃` -/

/-- `A₃` in the variable `ξ`. -/
noncomputable def i8A3x (x : ℝ) : ℝ :=
  (1 + x) / (1 - x) * (4 * x / (1 + x) - 2 * hpl [negOne] x - hpl [zero, negOne] x +
    2 * hpl [negOne, negOne] x - hpl [zero, zero, negOne] x + 2 * hpl [negOne, zero, negOne] x -
    4 * hpl [negOne, negOne, negOne] x + 2 * hpl [zero, negOne, negOne] x)

theorem i8AC_three_x {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8AC ((1 - x) ^ 2 / x) 3 = (i8A3x x : ℂ) := by
  have hlim : Tendsto (fun x => 4 * x / (1 + x) - 2 * hpl [negOne] x - hpl [zero, negOne] x +
      2 * hpl [negOne, negOne] x - hpl [zero, zero, negOne] x +
      2 * hpl [negOne, zero, negOne] x - 4 * hpl [negOne, negOne, negOne] x +
      2 * hpl [zero, negOne, negOne] x) (𝓝[>] 0) (𝓝 0) := by
    have := ((((((((i8_tendsto_rat_zero (c := 4)).sub
      ((tendsto_hpl_zero (w := [negOne]) (by simp)).const_mul 2)).sub
      (tendsto_hpl_zero (w := [zero, negOne]) (by simp))).add
      ((tendsto_hpl_zero (w := [negOne, negOne]) (by simp)).const_mul 2)).sub
      (tendsto_hpl_zero (w := [zero, zero, negOne]) (by simp))).add
      ((tendsto_hpl_zero (w := [negOne, zero, negOne]) (by simp)).const_mul 2)).sub
      ((tendsto_hpl_zero (w := [negOne, negOne, negOne]) (by simp)).const_mul 4)).add
      ((tendsto_hpl_zero (w := [zero, negOne, negOne]) (by simp)).const_mul 2))
    simpa using this
  refine i8AC_succ_of (k := 2) (Ap := i8A2x) (fun y hy => i8AC_two_x hy) (fun y hy => ?_) hlim hx
    |>.trans ?_
  · have h0 : y ≠ 0 := hy.1.ne'
    have h1 : 1 - y ≠ 0 := by linarith [hy.2]
    have h2 : 1 + y ≠ 0 := by linarith [hy.1]
    have e := ((((((((((hasDerivAt_id' y).const_mul 4).div ((hasDerivAt_id' y).const_add 1)
      h2).sub ((hasDerivAt_hpl_cons negOne [] hy).const_mul 2)).sub
      (hasDerivAt_hpl_cons zero [negOne] hy)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hy).const_mul 2)).sub
      (hasDerivAt_hpl_cons zero [zero, negOne] hy)).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hy).const_mul 2)).sub
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hy).const_mul 4)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hy).const_mul 2))
    refine e.congr_deriv ?_
    unfold i8A2x
    simp only [kernel_negOne, kernel_zero, hpl_nil, OfNat.ofNat_ne_zero, ↓reduceIte]
    field_simp
    ring
  · unfold i8A3x; simp

theorem i8AC_three {t : ℝ} (ht : 0 < t) : i8AC t 3 = (i8A3x (i13Xi t) : ℂ) := by
  conv_lhs => rw [i13Xi_t ht.le]
  exact i8AC_three_x (i8_xi_mem ht)

/-! ### The coefficients `p₃` and `a₃` -/

/-- `p₃(t)`, the third coefficient of `t ^ (1 - ε) b_ε(t)² A_ε(t)`. -/
noncomputable def i8P3 (t : ℝ) : ℝ :=
  t * ((2 * i13Be3r t + 2 * i13Be1r t * i13Be2r t) * (i13Xi t / (1 - i13Xi t)) +
      (2 * i13Be2r t + i13Be1r t ^ 2) * i8A1x (i13Xi t) + 2 * i13Be1r t * i8A2x (i13Xi t) +
      i8A3x (i13Xi t)) -
    t * Real.log t * ((2 * i13Be2r t + i13Be1r t ^ 2) * (i13Xi t / (1 - i13Xi t)) +
      2 * i13Be1r t * i8A1x (i13Xi t) + i8A2x (i13Xi t)) +
    t * Real.log t ^ 2 / 2 * (2 * i13Be1r t * (i13Xi t / (1 - i13Xi t)) + i8A1x (i13Xi t)) -
    t * Real.log t ^ 3 / 6 * (i13Xi t / (1 - i13Xi t))

/-- The third coefficient `a₃` of the large-`t` subtraction. -/
noncomputable def i8A3r (t : ℝ) : ℝ :=
  -9 / 2 * Real.log t ^ 3 - 49 * Real.log t ^ 3 / (6 * t) + 18 * Real.log t ^ 2 -
    33 * Real.log t ^ 2 / (4 * t) + π ^ 2 * Real.log t + 5 * π ^ 2 * Real.log t / (3 * t) -
    36 * Real.log t + 203 * Real.log t / (4 * t) - 4 * π ^ 2 / 3 + 5 * π ^ 2 / (6 * t) -
    4 * zeta3 + 32 - 4 * zeta3 / t - 537 / (8 * t)

theorem i8R1C_three (t : ℝ) :
    i8R1C t 3 = t * ((2 * i13BubC t 3 + 2 * i13BubC t 1 * i13BubC t 2) * i8AC t 0 +
        (2 * i13BubC t 2 + i13BubC t 1 ^ 2) * i8AC t 1 + 2 * i13BubC t 1 * i8AC t 2 +
        i8AC t 3) -
      t * (Real.log t : ℂ) * ((2 * i13BubC t 2 + i13BubC t 1 ^ 2) * i8AC t 0 +
        2 * i13BubC t 1 * i8AC t 1 + i8AC t 2) +
      t * (Real.log t : ℂ) ^ 2 / 2 * (2 * i13BubC t 1 * i8AC t 0 + i8AC t 1) -
      t * (Real.log t : ℂ) ^ 3 / 6 * i8AC t 0 := by
  unfold i8R1C
  rw [show i13Cauchy i8NC (i8JC t) = i8AC t from rfl]
  simp only [i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    i13BubC_zero, Complex.cpow_one]
  norm_num [i13BubC_zero, Nat.factorial]
  ring

theorem i8AsymC_three {t : ℝ} (ht : 0 < t) : i8AsymC t 3 = (i8A3r t : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [i8AsymC, i13A0C, i13A1C, i13B0C, i13Cauchy, i13TpC,
    Finset.sum_range_succ, Finset.sum_range_zero, i13GC_zero, i13GC_one, i13GC_two, i13GC_three,
    Complex.cpow_zero, Complex.cpow_neg_one]
  unfold i8A3r
  norm_num [i13GC_zero, i13GC_one, i13GC_two, i13GC_three, Nat.factorial]
  field_simp
  ring

theorem i8Dsl_remInt1_three {t : ℝ} (ht : 0 < t) :
    i13Dsl (i8RemInt1 t) 3 0 = (i8P3 t : ℂ) := by
  rw [(i8Jet_remInt1 ht).dsl_eq, i8R1C_three, i13BubC_one ht, i13BubC_two ht, i13BubC_three ht,
    i8AC_zero ht, i8AC_one ht, i8AC_two ht, i8AC_three ht]
  unfold i8P3
  push_cast
  ring

theorem i8Dsl_remInt2_three {t : ℝ} (ht : 0 < t) :
    i13Dsl (i8RemInt2 t) 3 0 = ((i8P3 t - i8A3r t : ℝ) : ℂ) := by
  rw [(i8Jet_remInt2 ht).dsl_eq, i8R1C_three, i13BubC_one ht, i13BubC_two ht, i13BubC_three ht,
    i8AC_zero ht, i8AC_one ht, i8AC_two ht, i8AC_three ht, i8AsymC_three ht]
  unfold i8P3
  push_cast
  ring

/-! ### The primitive of `a₃` -/

/-- The primitive `A₃` of `a₃`. -/
noncomputable def i8Prim3 (t : ℝ) : ℝ :=
    (-9 / 2) * (t * Real.log t ^ 3) +
    (63 / 2) * (t * Real.log t ^ 2) +
    (-99 + π ^ 2) * (t * Real.log t) +
    (131 - 4 * zeta3 - 7 / 3 * π ^ 2) * t +
    (-49 / 24) * Real.log t ^ 4 +
    (-11 / 4) * Real.log t ^ 3 +
    (203 / 8 + 5 / 6 * π ^ 2) * Real.log t ^ 2 +
    (-537 / 8 - 4 * zeta3 + 5 / 6 * π ^ 2) * Real.log t

theorem hasDerivAt_i8Prim3 {t : ℝ} (ht : 0 < t) : HasDerivAt i8Prim3 (i8A3r t) t := by
  have L := Real.hasDerivAt_log ht.ne'
  have X := hasDerivAt_id' t
  have e := (((((((((X.mul (L.pow 3)).const_mul (-9 / 2)).add
    ((X.mul (L.pow 2)).const_mul (63 / 2))).add
    ((X.mul L).const_mul (-99 + π ^ 2))).add
    (X.const_mul (131 - 4 * zeta3 - 7 / 3 * π ^ 2))).add
    ((L.pow 4).const_mul (-49 / 24))).add
    ((L.pow 3).const_mul (-11 / 4))).add
    ((L.pow 2).const_mul (203 / 8 + 5 / 6 * π ^ 2))).add
    (L.const_mul (-537 / 8 - 4 * zeta3 + 5 / 6 * π ^ 2)))
  unfold i8Prim3
  refine e.congr_deriv ?_
  unfold i8A3r
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem i8Prim3_one : i8Prim3 1 = 131 - 7 * π ^ 2 / 3 - 4 * zeta3 := by
  unfold i8Prim3
  norm_num
  ring

end QED.ThreeLoopD
