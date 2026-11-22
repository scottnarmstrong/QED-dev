/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R2K

/-!
# Set (d), master `I₈`: the second coefficients of the integrands of `Rem`

With `λ = log t`, `βₖ` the bubble coefficients and `Aₖ` the angular coefficients
(`QED.ThreeLoopD.i8AC_zero`, `QED.ThreeLoopD.i8AC_one`, `QED.ThreeLoopD.i8AC_two`), the second
Taylor coefficient of `t ^ (1 - ε) b_ε² A_ε` is

  `p₂ = t ((2β₂ + β₁²) A₀ + 2β₁ A₁ + A₂) - t λ (2β₁ A₀ + A₁) + t λ²/2 A₀`

(`QED.ThreeLoopD.i8P2`), and that of the subtraction is
`a₂ = 9λ²/2 + 11λ²/(2t) - 12λ + 27λ/(2t) - π²/3 - π²/(3t) + 12 - 105/(4t)`
(`QED.ThreeLoopD.i8A2r`), with primitive `A₂` (`QED.ThreeLoopD.i8Prim2`),
`A₂(1) = 33 - π²/3`.

## Main results

* `QED.ThreeLoopD.i8Dsl_remInt1_two`, `QED.ThreeLoopD.i8Dsl_remInt2_two`.
* `QED.ThreeLoopD.hasDerivAt_i8Prim2`, `QED.ThreeLoopD.i8Prim2_one`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real Complex

namespace QED.ThreeLoopD

/-- `p₂(t)`, the second coefficient of `t ^ (1 - ε) b_ε(t)² A_ε(t)`. -/
noncomputable def i8P2 (t : ℝ) : ℝ :=
  t * ((2 * i13Be2r t + i13Be1r t ^ 2) * (i13Xi t / (1 - i13Xi t)) +
      2 * i13Be1r t * i8A1x (i13Xi t) + i8A2x (i13Xi t)) -
    t * Real.log t * (2 * i13Be1r t * (i13Xi t / (1 - i13Xi t)) + i8A1x (i13Xi t)) +
    t * Real.log t ^ 2 / 2 * (i13Xi t / (1 - i13Xi t))

/-- The second coefficient `a₂` of the large-`t` subtraction. -/
noncomputable def i8A2r (t : ℝ) : ℝ :=
  9 / 2 * Real.log t ^ 2 + 11 * Real.log t ^ 2 / (2 * t) - 12 * Real.log t +
    27 * Real.log t / (2 * t) - π ^ 2 / 3 - π ^ 2 / (3 * t) + 12 - 105 / (4 * t)

theorem i8R1C_two (t : ℝ) :
    i8R1C t 2 = t * ((2 * i13BubC t 2 + i13BubC t 1 ^ 2) * i8AC t 0 +
        2 * i13BubC t 1 * i8AC t 1 + i8AC t 2) -
      t * (Real.log t : ℂ) * (2 * i13BubC t 1 * i8AC t 0 + i8AC t 1) +
      t * (Real.log t : ℂ) ^ 2 / 2 * i8AC t 0 := by
  unfold i8R1C
  rw [show i13Cauchy i8NC (i8JC t) = i8AC t from rfl]
  simp only [i13Cauchy, i13TpC, Finset.sum_range_succ, Finset.sum_range_zero,
    i13BubC_zero, cpow_one]
  norm_num [i13BubC_zero, Nat.factorial]
  ring

theorem i8AsymC_two {t : ℝ} (ht : 0 < t) : i8AsymC t 2 = (i8A2r t : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  simp only [i8AsymC, i13A0C, i13A1C, i13B0C, i13Cauchy, i13TpC,
    Finset.sum_range_succ, Finset.sum_range_zero, i13GC_zero, i13GC_one, i13GC_two, cpow_zero,
    cpow_neg_one]
  unfold i8A2r
  norm_num [i13GC_zero, i13GC_one, i13GC_two, Nat.factorial]
  field_simp
  ring

theorem i8Dsl_remInt1_two {t : ℝ} (ht : 0 < t) :
    i13Dsl (i8RemInt1 t) 2 0 = (i8P2 t : ℂ) := by
  rw [(i8Jet_remInt1 ht).dsl_eq, i8R1C_two, i13BubC_one ht, i13BubC_two ht, i8AC_zero ht,
    i8AC_one ht, i8AC_two ht]
  unfold i8P2
  push_cast
  ring

theorem i8Dsl_remInt2_two {t : ℝ} (ht : 0 < t) :
    i13Dsl (i8RemInt2 t) 2 0 = ((i8P2 t - i8A2r t : ℝ) : ℂ) := by
  rw [(i8Jet_remInt2 ht).dsl_eq, i8R1C_two, i13BubC_one ht, i13BubC_two ht, i8AC_zero ht,
    i8AC_one ht, i8AC_two ht, i8AsymC_two ht]
  unfold i8P2
  push_cast
  ring

/-! ### The primitive of `a₂` -/

/-- The primitive `A₂` of `a₂`. -/
noncomputable def i8Prim2 (t : ℝ) : ℝ :=
  11 / 6 * Real.log t ^ 3 + 9 / 2 * (t * Real.log t ^ 2) + 27 / 4 * Real.log t ^ 2 -
    π ^ 2 / 3 * Real.log t - 21 * (t * Real.log t) - 105 / 4 * Real.log t - π ^ 2 / 3 * t +
    33 * t

theorem hasDerivAt_i8Prim2 {t : ℝ} (ht : 0 < t) : HasDerivAt i8Prim2 (i8A2r t) t := by
  have L := Real.hasDerivAt_log ht.ne'
  have X := hasDerivAt_id' t
  have e := ((((((((L.pow 3).const_mul (11 / 6)).add ((X.mul (L.pow 2)).const_mul (9 / 2))).add
    ((L.pow 2).const_mul (27 / 4))).sub (L.const_mul (π ^ 2 / 3))).sub
    ((X.mul L).const_mul 21)).sub (L.const_mul (105 / 4))).sub (X.const_mul (π ^ 2 / 3))).add
    (X.const_mul 33)
  unfold i8Prim2
  refine e.congr_deriv ?_
  unfold i8A2r
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem i8Prim2_one : i8Prim2 1 = 33 - π ^ 2 / 3 := by
  unfold i8Prim2
  norm_num
  ring

end QED.ThreeLoopD
