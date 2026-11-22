/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R2B

/-!
# Set (d), master `I₁₃`: the second coefficients of the integrands of `Rem` and their primitives

With `λ = log t`, `β₁ = 2 + log ξ (1 + ξ)/(1 - ξ)` and the second bubble coefficient
(`QED.ThreeLoopD.i13_integral_log_sq`)

  `β₂ = 4 - (1 + ξ)/(1 - ξ) (2 Li₂ (-ξ) + 2 log ξ log (1 + ξ) - log² ξ/2 - 2 log ξ + π²/6)`,

the second Taylor coefficients of the integrands of `Rem` are `p₂ = t (λ²/2 - 2λβ₁ + 2β₂ + β₁²)`
on `(0, 1)` and `p₂ - a₂` on `(1, ∞)`, with

  `a₂ = λ² (9t/2 + 10 - 6/t) + λ (28/t - 12t) - 2π²/3 + t (12 - π²/3) - 12 + (2π²/3 + 7)/t`.

The primitive of `p₂` is `F₂(t) = Ψ₂(ξ(t)) + (t λ)²/4 - 9 t² λ/4 + 57 t²/8`, where `Ψ₂`
(`QED.ThreeLoopD.i13Psi2`) involves `Li₂ (±ξ)` and `Li₃ (±ξ)`; the primitive of `a₂` is
elementary (`QED.ThreeLoopD.i13Prim2`). `F₂` is continuous on `[0, ∞)`, with
`F₂(0) = Ψ₂(1) = 4ζ(3) + 16`.

## Main results

* `QED.ThreeLoopD.i13Dsl_remInt1_two`, `QED.ThreeLoopD.i13Dsl_remInt2_two`.
* `QED.ThreeLoopD.hasDerivAt_i13F2`, `QED.ThreeLoopD.hasDerivAt_i13Prim2`.
* `QED.ThreeLoopD.continuousOn_i13F2`, `QED.ThreeLoopD.i13F2_zero`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### The second coefficients -/

/-- `β₂(t) = 4 - (1 + ξ)/(1 - ξ) (2 Li₂ (-ξ) + 2 log ξ log (1 + ξ) - log² ξ/2 - 2 log ξ + π²/6)`. -/
noncomputable def i13Be2r (t : ℝ) : ℝ :=
  4 - (1 + i13Xi t) / (1 - i13Xi t) * (2 * Li₂ (-i13Xi t) +
    2 * Real.log (i13Xi t) * Real.log (1 + i13Xi t) - Real.log (i13Xi t) ^ 2 / 2 -
    2 * Real.log (i13Xi t) + π ^ 2 / 6)

/-- `p₂(t) = t (λ²/2 - 2λβ₁ + 2β₂ + β₁²)`, `λ = log t`. -/
noncomputable def i13P2 (t : ℝ) : ℝ :=
  t * (Real.log t ^ 2 / 2 - 2 * Real.log t * i13Be1r t + 2 * i13Be2r t + i13Be1r t ^ 2)

/-- `a₂(t) = λ² (9t/2 + 10 - 6/t) + λ (28/t - 12t) - 2π²/3 + t (12 - π²/3) - 12 + (2π²/3 + 7)/t`. -/
noncomputable def i13A2r (t : ℝ) : ℝ :=
  Real.log t ^ 2 * (9 * t / 2 + 10 - 6 / t) + Real.log t * (28 / t - 12 * t) - 2 * π ^ 2 / 3 +
    t * (12 - π ^ 2 / 3) - 12 + (2 * π ^ 2 / 3 + 7) / t

theorem i13BubC_two {t : ℝ} (ht : 0 < t) : i13BubC t 2 = (i13Be2r t : ℂ) := by
  have e : (fun x : ℝ =>
      ((-Real.log (1 + x * (1 - x) * t) : ℝ) : ℂ) ^ 2 / ((Nat.factorial 2 : ℕ) : ℂ)) =
      fun x => ((Real.log (1 + x * (1 - x) * t) ^ 2 / 2 : ℝ) : ℂ) := by
    funext x
    push_cast
    simp only [Nat.factorial]
    ring
  unfold i13BubC
  rw [e, integral_complex_ofReal, integral_div, i13_integral_log_sq ht]
  unfold i13Be2r
  push_cast
  ring

theorem i13GC_two : i13GC 2 = -1 / 6 * (π : ℂ) ^ 2 := i13GC_eq 2 (by norm_num)

theorem i13R1C_two (t : ℝ) :
    i13R1C t 2 = t * (2 * i13BubC t 2 + i13BubC t 1 ^ 2) -
      2 * t * (Real.log t : ℂ) * i13BubC t 1 + t * (Real.log t : ℂ) ^ 2 / 2 := by
  simp only [i13R1C, i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    i13BubC_zero, Complex.cpow_one]
  norm_num [i13BubC_zero, Nat.factorial]
  ring

theorem i13AsymC_two {t : ℝ} (ht : 0 < t) :
    i13AsymC t 2 = (i13A2r t : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [i13AsymC, i13A0C, i13A1C, i13A2C, i13B0C, i13B1C, i13Cauchy, i13TpC,
    Finset.sum_range_succ, Finset.sum_range_zero, i13GC_zero, i13GC_one, i13GC_two,
    Complex.cpow_one, Complex.cpow_zero, Complex.cpow_neg_one]
  unfold i13A2r
  norm_num [i13GC_zero, i13GC_one, i13GC_two, Nat.factorial]
  field_simp
  ring

theorem i13Dsl_remInt1_two {t : ℝ} (ht : 0 < t) :
    i13Dsl (i13RemInt1 t) 2 0 = (i13P2 t : ℂ) := by
  rw [i13Dsl_remInt1 ht, i13R1C_two, i13BubC_one ht, i13BubC_two ht]
  unfold i13P2
  push_cast
  ring

theorem i13Dsl_remInt2_two {t : ℝ} (ht : 0 < t) :
    i13Dsl (i13RemInt2 t) 2 0 = ((i13P2 t - i13A2r t : ℝ) : ℂ) := by
  rw [i13Dsl_remInt2 ht, i13R1C_two, i13BubC_one ht, i13BubC_two ht, i13AsymC_two ht]
  unfold i13P2
  push_cast
  ring

/-! ### The primitive of `p₂` -/

/-- The part of the primitive of `p₂` in the variable `ξ`. -/
noncomputable def i13Psi2 (ξ : ℝ) : ℝ :=
  (2 * ξ ^ 2 - 2 / ξ ^ 2) * Li₂ (-ξ) - 16 * Li₃ (-ξ) + 2 * Real.log ξ ^ 3 +
    Real.log ξ ^ 2 * (-ξ ^ 2 + 2 * ξ + 6 + 2 / ξ + 2 / ξ ^ 2) +
    Real.log ξ * (8 * Li₂ (-ξ) + 8 * Li₂ ξ + 2 * Real.log (1 + ξ) * (ξ ^ 2 - 1 / ξ ^ 2) -
      2 * π ^ 2 / 3 - 5 * ξ ^ 2 - 4 * ξ - 1 + 4 / ξ + 6 / ξ ^ 2) - 8 * Li₃ ξ +
    π ^ 2 * (ξ ^ 2 - 1 / ξ ^ 2) / 6 + (3 * ξ ^ 2 + 5 * ξ + 5 / ξ + 3 / ξ ^ 2) +
    Real.negMulLog (1 - ξ) *
      (2 * Real.log ξ * (1 + ξ) * (1 + ξ ^ 2) + (1 - ξ) * (1 + ξ) ^ 2) / ξ ^ 2

theorem hasDerivAt_i13Psi2 {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ < 1) :
    HasDerivAt i13Psi2 (-(1 + ξ) ^ 2 * (1 - ξ) / ξ ^ 3 * ((1 - ξ) * (3 * Real.log ξ ^ 2 -
      4 * Real.log (1 - ξ) * Real.log ξ - 4 * Li₂ (-ξ) - 4 * Real.log ξ * Real.log (1 + ξ) +
      8 * Real.log ξ - π ^ 2 / 3) + (1 + ξ) * Real.log ξ ^ 2)) ξ := by
  have hn : ξ ≠ 0 := h0.ne'
  have hm : |-ξ| < 1 := by rw [abs_neg, abs_of_pos h0]; exact h1
  have hp : |ξ| < 1 := by rw [abs_of_pos h0]; exact h1
  have hn' : -ξ ≠ 0 := neg_ne_zero.mpr hn
  have h1' : 1 - ξ ≠ 0 := by linarith
  have h2' : 1 + ξ ≠ 0 := by linarith
  have X := hasDerivAt_id' ξ
  have I := hasDerivAt_inv hn
  have L := Real.hasDerivAt_log hn
  have L1 := (X.const_add 1).log h2'
  have NM := (Real.hasDerivAt_negMulLog h1').comp ξ (X.const_sub 1)
  have D2 := (hasDerivAt_Li₂ hm hn').comp ξ (hasDerivAt_neg' ξ)
  have D3 := (hasDerivAt_Li₃ hm hn').comp ξ (hasDerivAt_neg' ξ)
  have P2 := hasDerivAt_Li₂ hp hn
  have P3 := hasDerivAt_Li₃ hp hn
  have e1 := ((((X.pow 2).const_mul 2).sub ((I.pow 2).const_mul 2)).mul D2).sub (D3.const_mul 16)
  have e2 := ((L.pow 3).const_mul 2).add ((L.pow 2).mul
    (((((X.pow 2).neg.add (X.const_mul 2)).add_const 6).add (I.const_mul 2)).add
      ((I.pow 2).const_mul 2)))
  have e3 := L.mul (((((((((D2.const_mul 8).add (P2.const_mul 8)).add
    ((L1.mul ((X.pow 2).sub (I.pow 2))).const_mul 2)).sub_const (2 * π ^ 2 / 3)).sub
    ((X.pow 2).const_mul 5)).sub (X.const_mul 4)).sub_const 1).add (I.const_mul 4)).add
    ((I.pow 2).const_mul 6))
  have e4 := ((P3.const_mul 8).neg.add (((X.pow 2).sub (I.pow 2)).const_mul (π ^ 2 / 6))).add
    (((((X.pow 2).const_mul 3).add (X.const_mul 5)).add (I.const_mul 5)).add
      ((I.pow 2).const_mul 3))
  have e5 := (NM.mul ((((L.const_mul 2).mul (X.const_add 1)).mul ((X.pow 2).const_add 1)).add
    ((X.const_sub 1).mul ((X.const_add 1).pow 2)))).mul (I.pow 2)
  have e := (((e1.add e2).add e3).add e4).add e5
  convert e using 1
  · funext y
    simp only [i13Psi2, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply, Pi.neg_apply]
    ring
  · simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.neg_apply, sub_neg_eq_add, Real.negMulLog, Nat.reduceSub, pow_one]
    field_simp
    ring

/-- `F₂(t) = Ψ₂(ξ(t)) + (t log t)²/4 - 9 t² log t/4 + 57 t²/8`. -/
noncomputable def i13F2 (t : ℝ) : ℝ :=
  i13Psi2 (i13Xi t) + ((t * Real.log t) ^ 2 / 4 - 9 * (t ^ 2 * Real.log t) / 4 + 57 * t ^ 2 / 8)

theorem i13_log_eq_xi {t : ℝ} (ht : 0 < t) :
    Real.log t = 2 * Real.log (1 - i13Xi t) - Real.log (i13Xi t) := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have h1 : 0 < 1 - i13Xi t := by linarith
  conv_lhs => rw [hT]
  rw [Real.log_div (by positivity) hx0.ne', Real.log_pow]
  push_cast; ring

/-- `Ψ₂'(ξ) ξ'(t) = t (-2λ (β₁ - 2) + 2β₂ + β₁² - 12)`, in terms of `ξ`. -/
theorem i13Psi2_deriv_mul {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ < 1) :
    -(1 + ξ) ^ 2 * (1 - ξ) / ξ ^ 3 * ((1 - ξ) * (3 * Real.log ξ ^ 2 -
      4 * Real.log (1 - ξ) * Real.log ξ - 4 * Li₂ (-ξ) - 4 * Real.log ξ * Real.log (1 + ξ) +
      8 * Real.log ξ - π ^ 2 / 3) + (1 + ξ) * Real.log ξ ^ 2) * (-ξ ^ 2 / (1 - ξ ^ 2)) =
    (1 - ξ) ^ 2 / ξ * (-2 * (2 * Real.log (1 - ξ) - Real.log ξ) *
      (Real.log ξ * (1 + ξ) / (1 - ξ)) + 2 * (4 - (1 + ξ) / (1 - ξ) * (2 * Li₂ (-ξ) +
      2 * Real.log ξ * Real.log (1 + ξ) - Real.log ξ ^ 2 / 2 - 2 * Real.log ξ + π ^ 2 / 6)) +
      (2 + Real.log ξ * (1 + ξ) / (1 - ξ)) ^ 2 - 12) := by
  have h0' : ξ ≠ 0 := h0.ne'
  have h1' : 1 - ξ ≠ 0 := by linarith
  have h2' : 1 + ξ ≠ 0 := by linarith
  have h3' : 1 - ξ ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem hasDerivAt_i13F2 {t : ℝ} (ht : 0 < t) : HasDerivAt i13F2 (i13P2 t) t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have hlog := i13_log_eq_xi ht
  have X := hasDerivAt_id' t
  have L := Real.hasDerivAt_log ht.ne'
  have e := ((hasDerivAt_i13Psi2 hx0 hx1).comp t (hasDerivAt_i13Xi ht)).add
    (((((X.mul L).pow 2).div_const 4).sub ((((X.pow 2).mul L).const_mul 9).div_const 4)).add
      (((X.pow 2).const_mul 57).div_const 8))
  convert e using 1
  · funext y
    simp only [i13F2, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
  · rw [i13Psi2_deriv_mul hx0 hx1, ← hT, ← hlog]
    unfold i13P2 i13Be1r i13Be2r
    simp only [Pi.pow_apply, Pi.mul_apply, Nat.reduceSub, pow_one]
    field_simp
    ring

/-! ### The primitive of `a₂` -/

/-- `A₂(t) = -π²t²/6 + 81t²/8 - 2π²t/3 + 8t + (9t²/4 + 10t + 14) λ²
  + (-33t²/4 - 20t + 2π²/3 + 7) λ - 2λ³`. -/
noncomputable def i13Prim2 (t : ℝ) : ℝ :=
  -π ^ 2 * t ^ 2 / 6 + 81 * t ^ 2 / 8 - 2 * π ^ 2 * t / 3 + 8 * t +
    (9 * t ^ 2 / 4 + 10 * t + 14) * Real.log t ^ 2 +
    (-33 * t ^ 2 / 4 - 20 * t + 2 * π ^ 2 / 3 + 7) * Real.log t - 2 * Real.log t ^ 3

theorem hasDerivAt_i13Prim2 {t : ℝ} (ht : 0 < t) : HasDerivAt i13Prim2 (i13A2r t) t := by
  have L := Real.hasDerivAt_log ht.ne'
  have X := hasDerivAt_id' t
  have e := ((((((((X.pow 2).const_mul (-π ^ 2)).div_const 6).add
    (((X.pow 2).const_mul 81).div_const 8)).sub ((X.const_mul (2 * π ^ 2)).div_const 3)).add
    (X.const_mul 8)).add (((((X.pow 2).const_mul 9).div_const 4).add (X.const_mul 10)).add_const
    14 |>.mul (L.pow 2))).add (((((X.pow 2).const_mul (-33)).div_const 4).sub
    (X.const_mul 20)).add_const (2 * π ^ 2 / 3 + 7) |>.mul L)).sub ((L.pow 3).const_mul 2)
  convert e using 1
  · funext y
    simp only [i13Prim2, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · unfold i13A2r
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    field_simp
    ring

/-! ### Continuity of `F₂` and its value at `0` -/

theorem continuousOn_i13Psi2 : ContinuousOn i13Psi2 (Ioc 0 1) := by
  have hP2 : ContinuousOn Li₂ (Ioc 0 1) := continuousOn_Li₂.mono fun y hy =>
    ⟨by linarith [hy.1], hy.2⟩
  have hP3 : ContinuousOn Li₃ (Ioc 0 1) := continuousOn_Li₃.mono fun y hy =>
    ⟨by linarith [hy.1], hy.2⟩
  have hD2 : ContinuousOn (fun y => Li₂ (-y)) (Ioc 0 1) :=
    continuousOn_Li₂.comp continuousOn_neg fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hD3 : ContinuousOn (fun y => Li₃ (-y)) (Ioc 0 1) :=
    continuousOn_Li₃.comp continuousOn_neg fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h0 : ∀ y ∈ Ioc (0 : ℝ) 1, y ≠ 0 := fun y hy => hy.1.ne'
  have h1 : ∀ y ∈ Ioc (0 : ℝ) 1, 1 + y ≠ 0 := fun y hy => by linarith [hy.1]
  unfold i13Psi2
  fun_prop (disch := first | assumption | (intro y hy; simp_all))

theorem continuousOn_i13F2 : ContinuousOn i13F2 (Ici 0) := by
  have hX : ContinuousOn (fun t => i13Psi2 (i13Xi t)) (Ici 0) :=
    continuousOn_i13Psi2.comp continuous_i13Xi.continuousOn fun t ht =>
      ⟨i13Xi_pos ht, i13Xi_le_one ht⟩
  have hE : Continuous fun t : ℝ =>
      (t * Real.log t) ^ 2 / 4 - 9 * (t ^ 2 * Real.log t) / 4 + 57 * t ^ 2 / 8 :=
    (((Real.continuous_mul_log.pow 2).div_const 4).sub
      ((continuous_mul_sq_log.const_mul 9).div_const 4)).add (by fun_prop)
  exact hX.add hE.continuousOn

theorem i13Psi2_one : i13Psi2 1 = 4 * zeta3 + 16 := by
  unfold i13Psi2
  rw [Li₃_one, Li₃_neg_one]
  norm_num
  ring

theorem i13F2_zero : i13F2 0 = 4 * zeta3 + 16 := by
  unfold i13F2
  rw [i13Xi_zero, i13Psi2_one]
  norm_num

end QED.ThreeLoopD
