/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Jet
public import QED.ThreeLoopD.SetDMastersI5C0

/-!
# Set (d), master `I₅`: the radial integral of `c₁`, given a primitive

By `QED.ThreeLoopD.i5Dsl_remInt1_one` and `QED.ThreeLoopD.i5Dsl_remInt2_one` the pointwise first
coefficients of the integrands of `Rem` are `g(t) = t ((-λ + β₁) K₀ + K₁)` on `(0, 1)` and
`g(t) - a(t)` on `(1, ∞)`, `a(t) = (-5λ²/2 - 2λ + 8 + π²/6)/t`, `λ = log t`. The function
`A(t) = -5λ³/6 - λ² + (8 + π²/6) λ` (`QED.ThreeLoopD.i5Prim1`) is a primitive of `a` with
`A(1) = 0`. So if `g` is real with a primitive `Φ` continuous on `[0, 1]` and
`Φ - A → L` at infinity, then

  `c₁ = (Φ(1) - Φ(0)) + (L - Φ(1)) = L - Φ(0)`

(`QED.ThreeLoopD.i5RemCoeff_one_of_prim`). Integrability of both pieces comes from the bounds
behind `QED.ThreeLoopD.integrableOn_i5Dsl_remInt1`.

## Main results

* `QED.ThreeLoopD.i5RemCoeff_one_of_prim`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopD

/-- The large-`t` subtraction of the first coefficient, `(-5λ²/2 - 2λ + 8 + π²/6)/t`. -/
noncomputable def i5Asym1 (t : ℝ) : ℝ :=
  (-5 / 2 * Real.log t ^ 2 - 2 * Real.log t + 8 + π ^ 2 / 6) / t

/-- Its primitive `A(t) = -5λ³/6 - λ² + (8 + π²/6) λ`. -/
noncomputable def i5Prim1 (t : ℝ) : ℝ :=
  -5 / 6 * Real.log t ^ 3 - Real.log t ^ 2 + (8 + π ^ 2 / 6) * Real.log t

theorem hasDerivAt_i5Prim1 {t : ℝ} (ht : 0 < t) : HasDerivAt i5Prim1 (i5Asym1 t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  refine ((((hl.pow 3).const_mul (-5 / 6)).sub (hl.pow 2)).add
    (hl.const_mul (8 + π ^ 2 / 6))).congr_deriv ?_
  unfold i5Asym1
  field_simp
  ring

theorem i5Prim1_one : i5Prim1 1 = 0 := by simp [i5Prim1]

/-- **The first coefficient from a primitive of the integrand.** -/
theorem i5RemCoeff_one_of_prim {g Φ : ℝ → ℝ} {L : ℝ}
    (hg : ∀ t : ℝ, 0 < t →
      (t : ℂ) * ((-(Real.log t : ℂ) + i13Be1r t) * i5Ker 0 t + i5KerC t 1) = g t)
    (hΦ : ∀ t > 0, HasDerivAt Φ (g t) t) (hΦc : ContinuousOn Φ (Icc 0 1))
    (hL : Tendsto (fun t => Φ t - i5Prim1 t) atTop (𝓝 L)) :
    i5RemCoeff 1 = ((L - Φ 0 : ℝ) : ℂ) := by
  have e1 : ∀ t ∈ Ioo (0 : ℝ) 1, i13Dsl (i5RemInt1 t) 1 0 = (g t : ℂ) := fun t ht => by
    rw [i5Dsl_remInt1_one ht.1, hg t ht.1]
  have e2 : ∀ t ∈ Ioi (1 : ℝ), i13Dsl (i5RemInt2 t) 1 0 = ((g t - i5Asym1 t : ℝ) : ℂ) :=
    fun t (ht : 1 < t) => by
      rw [i5Dsl_remInt2_one (zero_lt_one.trans ht), hg t (zero_lt_one.trans ht), i5Asym1]
      push_cast
      ring
  have i1 : IntegrableOn g (Ioo (0 : ℝ) 1) :=
    (integrableOn_i5Dsl_remInt1 1).re.congr_fun (fun t ht => by simp [e1 t ht])
      measurableSet_Ioo
  have i2 : IntegrableOn (fun t => g t - i5Asym1 t) (Ioi (1 : ℝ)) :=
    (integrableOn_i5Dsl_remInt2 1).re.congr_fun (fun t ht => by simp [e2 t ht])
      measurableSet_Ioi
  have I1 : ∫ t in Ioo (0 : ℝ) 1, g t = Φ 1 - Φ 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hΦc
        (fun t ht => hΦ t ht.1)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
          (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact i1))]
  have I2 : ∫ t in Ioi (1 : ℝ), (g t - i5Asym1 t) = L - Φ 1 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => Φ t - i5Prim1 t)
      ((hΦ 1 one_pos).sub (hasDerivAt_i5Prim1 one_pos)).continuousAt.continuousWithinAt
      (fun t ht => (hΦ t (zero_lt_one.trans ht)).sub
        (hasDerivAt_i5Prim1 (zero_lt_one.trans ht))) i2 hL, i5Prim1_one, sub_zero]
  unfold i5RemCoeff
  rw [setIntegral_congr_fun measurableSet_Ioo e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_complex_ofReal, integral_complex_ofReal, I1, I2]
  push_cast
  ring

end QED.ThreeLoopD
