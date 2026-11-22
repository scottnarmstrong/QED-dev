/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R1Fub
public import QED.Polylog.ExtraIntegrals

/-!
# Set (d), master `I₈`: the bubble part of `c₁`, through a primitive in `ξ`

With `λ = log t`, `β₁ = 2 + log ξ (1 + ξ)/(1 - ξ)` and `ξ = ξ(t)` (`QED.ThreeLoopD.i13Xi`), the
bubble part of the first coefficient is `p(t) = (1 - ξ)(-λ + 2β₁)` on `(0, 1)`, with large-`t`
subtraction `a(t) = 4 - 3λ - (8 + λ)/t`. They have the primitives `F(t) = Φ(ξ(t))` and
`A(t) = 7t - 3tλ - 8λ - λ²/2`, where (`QED.ThreeLoopD.i8Phi1`)

  `Φ(ξ) = 7/ξ + 2ξ - 11ξ²/4 + 2 Li₂(ξ) + (ξ² - ξ + 2)/ξ · (-(1 - ξ) log (1 - ξ))`
    `+ log ξ (2 + 3/ξ + 3ξ + ξ²/2) - log² ξ / 2`.

`F(0) = Φ(1) = 25/4 + π²/3`, `A(1) = 7` and `F - A → 10` at infinity, so
`∫₀¹ p + ∫₁^∞ (p - a) = 10 + 7 - 25/4 - π²/3 = 43/4 - π²/3` (the value `F(1)` cancels).

## Main results

* `QED.ThreeLoopD.i8_integral_P1`, `QED.ThreeLoopD.i8_integral_P1_sub`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- `p(t) = (1 - ξ)(-log t + 2 β₁(t))`. -/
noncomputable def i8P1 (t : ℝ) : ℝ := (1 - i13Xi t) * (-Real.log t + 2 * i13Be1r t)

/-- `a(t) = 4 - 3 log t - (8 + log t)/t`. -/
noncomputable def i8A1r (t : ℝ) : ℝ := 4 - 3 * Real.log t - (8 + Real.log t) / t

/-- `Φ(ξ)`, the primitive of `p` in the variable `ξ`. -/
noncomputable def i8Phi1 (ξ : ℝ) : ℝ :=
  7 / ξ + 2 * ξ - 11 * ξ ^ 2 / 4 + 2 * Li₂ ξ + (ξ ^ 2 - ξ + 2) / ξ * negMulLog (1 - ξ) +
    Real.log ξ * (2 + 3 / ξ + 3 * ξ + ξ ^ 2 / 2) - Real.log ξ ^ 2 / 2

/-- `A(t) = 7t - 3t log t - 8 log t - log² t / 2`. -/
noncomputable def i8Prim1 (t : ℝ) : ℝ :=
  7 * t - 3 * t * Real.log t - 8 * Real.log t - Real.log t ^ 2 / 2

theorem hasDerivAt_i8Phi1 {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ < 1) :
    HasDerivAt i8Phi1 (-(1 - ξ ^ 2) / ξ ^ 2 * ((1 - ξ) * (4 - 2 * Real.log (1 - ξ) +
      Real.log ξ) + 2 * (1 + ξ) * Real.log ξ)) ξ := by
  have hξ := h0.ne'
  have h1' : 1 - ξ ≠ 0 := by linarith
  have hx := hasDerivAt_id' ξ
  have hl := Real.hasDerivAt_log hξ
  have hL := hasDerivAt_Li₂' ⟨h0, h1⟩
  have hN := (Real.hasDerivAt_negMulLog h1').comp ξ ((hasDerivAt_id' ξ).const_sub 1)
  have e := ((((((hasDerivAt_const ξ (7 : ℝ)).div hx hξ).add (hx.const_mul 2)).sub
    (((hx.pow 2).const_mul 11).div_const 4)).add (hL.const_mul 2)).add
    (((((hx.pow 2).sub hx).add_const 2).div hx hξ).mul hN)).add
    (hl.mul ((((hasDerivAt_const ξ (2 : ℝ)).add ((hasDerivAt_const ξ (3 : ℝ)).div hx hξ)).add
      (hx.const_mul 3)).add ((hx.pow 2).div_const 2))) |>.sub ((hl.pow 2).div_const 2)
  convert e using 1
  · funext y
    simp only [i8Phi1, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply,
      Function.comp_apply]
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply,
      negMulLog]
    norm_num
    field_simp
    ring

theorem i8_log_eq {t : ℝ} (ht : 0 < t) :
    Real.log t = 2 * Real.log (1 - i13Xi t) - Real.log (i13Xi t) := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have h1 : 0 < 1 - i13Xi t := by linarith
  conv_lhs => rw [hT]
  rw [Real.log_div (by positivity) hx0.ne', Real.log_pow]
  push_cast; ring

theorem hasDerivAt_i8F1 {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => i8Phi1 (i13Xi t)) (i8P1 t) t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  refine ((hasDerivAt_i8Phi1 hx0 hx1).comp t (hasDerivAt_i13Xi ht)).congr_deriv ?_
  unfold i8P1 i13Be1r
  rw [i8_log_eq ht]
  set ξ := i13Xi t
  have h0 : ξ ≠ 0 := hx0.ne'
  have h1 : 1 - ξ ≠ 0 := by linarith
  have h2 : 1 + ξ ≠ 0 := by linarith
  have h3 : 1 - ξ ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem hasDerivAt_i8Prim1 {t : ℝ} (ht : 0 < t) : HasDerivAt i8Prim1 (i8A1r t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hx := hasDerivAt_id' t
  refine ((((hx.const_mul 7).sub ((hx.const_mul 3).mul hl)).sub (hl.const_mul 8)).sub
    ((hl.pow 2).div_const 2)).congr_deriv ?_
  unfold i8A1r
  field_simp
  ring

theorem i8Phi1_one : i8Phi1 1 = 25 / 4 + π ^ 2 / 3 := by
  unfold i8Phi1
  rw [Li₂_one]
  simp
  ring

theorem continuousOn_i8Phi1 : ContinuousOn i8Phi1 (Ioc 0 1) := by
  have hLi : ContinuousOn Li₂ (Ioc 0 1) :=
    continuousOn_Li₂.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hne : ∀ x ∈ Ioc (0 : ℝ) 1, x ≠ 0 := fun x hx => hx.1.ne'
  unfold i8Phi1
  fun_prop (disch := exact hne)

theorem continuousOn_i8F1 : ContinuousOn (fun t => i8Phi1 (i13Xi t)) (Icc 0 1) :=
  continuousOn_i8Phi1.comp continuous_i13Xi.continuousOn fun _ ht =>
    ⟨i13Xi_pos ht.1, i13Xi_le_one ht.1⟩

/-! ### The limit at infinity -/

/-- `F - A` in terms of `ξ`. -/
noncomputable def i8D1 (ξ : ℝ) : ℝ :=
  Real.log ξ * (ξ ^ 2 / 2 - 2 * Real.log (1 - ξ)) + 2 * Real.log (1 - ξ) ^ 2 +
    Real.log (1 - ξ) * (ξ ^ 2 + 4 * ξ + 7) + 4 * Real.log (1 - ξ) / ξ + 2 * Li₂ ξ -
    11 * ξ ^ 2 / 4 - 5 * ξ + 14

theorem i8F1_sub_prim1 {t : ℝ} (ht : 0 < t) :
    i8Phi1 (i13Xi t) - i8Prim1 t = i8D1 (i13Xi t) := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  unfold i8Phi1 i8Prim1 i8D1
  rw [i8_log_eq ht]
  simp only [negMulLog]
  set ξ := i13Xi t
  rw [hT]
  have h0 : ξ ≠ 0 := hx0.ne'
  field_simp
  ring

theorem tendsto_i8D1 : Tendsto i8D1 (𝓝[>] 0) (𝓝 10) := by
  have hxl : Tendsto (fun ξ : ℝ => ξ * Real.log ξ) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hx : Tendsto (fun ξ : ℝ => ξ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hl1 : Tendsto (fun ξ : ℝ => Real.log (1 - ξ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ξ : ℝ => Real.log (1 - ξ)) (𝓝 0) (𝓝 (Real.log (1 - 0))) :=
      ((continuous_const.sub continuous_id).continuousAt.log (by norm_num)).tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hl1d : Tendsto (fun ξ : ℝ => Real.log (1 - ξ) / ξ) (𝓝[>] 0) (𝓝 (-1)) := by
    have hd : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).const_sub 1).log (by norm_num)
      simpa using this
    refine (hd.tendsto_slope_zero_right).congr fun y => ?_
    simp [div_eq_inv_mul]
  have hlim := (((((((hxl.mul hx).div_const 2).sub ((hxl.mul hl1d).const_mul 2)).add
    ((hl1.pow 2).const_mul 2)).add (hl1.mul (((hx.pow 2).add (hx.const_mul 4)).add_const 7))).add
    (hl1d.const_mul 4)).add (tendsto_Li₂_zero_right.const_mul 2)).sub
    (((hx.pow 2).const_mul 11).div_const 4) |>.sub (hx.const_mul 5) |>.add_const 14
  have e : Tendsto i8D1 (𝓝[>] 0) (𝓝 (0 * 0 / 2 - 2 * (0 * -1) + 2 * 0 ^ 2 +
      0 * (0 ^ 2 + 4 * 0 + 7) + 4 * -1 + 2 * 0 - 11 * 0 ^ 2 / 4 - 5 * 0 + 14)) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    have h0 : ξ ≠ 0 := (show 0 < ξ from hξ).ne'
    unfold i8D1
    field_simp
  convert e using 2
  norm_num

theorem tendsto_i8F1_sub_prim1 :
    Tendsto (fun t => i8Phi1 (i13Xi t) - i8Prim1 t) atTop (𝓝 10) :=
  (tendsto_i8D1.comp tendsto_i13Xi_atTop).congr'
    (eventually_atTop.2 ⟨1, fun t ht => (i8F1_sub_prim1 (by linarith)).symm⟩)

/-! ### The integrals -/

theorem i8_integral_P1 (hi : IntegrableOn i8P1 (Ioo (0 : ℝ) 1)) :
    ∫ t in Ioo (0 : ℝ) 1, i8P1 t = i8Phi1 (i13Xi 1) - (25 / 4 + π ^ 2 / 3) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one continuousOn_i8F1
      (fun t ht => hasDerivAt_i8F1 ht.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (by rw [integrableOn_Ioc_iff_integrableOn_Ioo]; exact hi)), i13Xi_zero, i8Phi1_one]

theorem i8_integral_P1_sub (hi : IntegrableOn (fun t => i8P1 t - i8A1r t) (Ioi (1 : ℝ))) :
    ∫ t in Ioi (1 : ℝ), (i8P1 t - i8A1r t) = 10 - (i8Phi1 (i13Xi 1) - 7) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => i8Phi1 (i13Xi t) - i8Prim1 t)
    (((hasDerivAt_i8F1 one_pos).sub (hasDerivAt_i8Prim1 one_pos)).continuousAt
      |>.continuousWithinAt)
    (fun _ ht => (hasDerivAt_i8F1 (zero_lt_one.trans ht)).sub
      (hasDerivAt_i8Prim1 (zero_lt_one.trans ht)))
    hi tendsto_i8F1_sub_prim1]
  unfold i8Prim1
  norm_num

end QED.ThreeLoopD
