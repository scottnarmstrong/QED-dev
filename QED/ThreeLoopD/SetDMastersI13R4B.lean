/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R3

/-!
# Set (d), master `I₁₃`: the fourth bubble coefficient

In the variable `ξ` (`t = (1 - ξ)²/ξ`, `r = (1 + ξ)/(1 - ξ)`), the bubble differential equation
(`QED.ThreeLoopD.hasDerivAt_i13BubR`) reads `(β₄/r)' = (1 - ξ)²/(ξ (1 + ξ)²) β₃`, and
`β₃ = r (P₃ - P₃(1))` (`QED.ThreeLoopD.i13BubR_three`). The function

  `P₄(ξ) = 32/(1 + ξ) + (8 - 2ζ(3) - π²/3) H(0) + (4ζ(3) + 2π²/3) H(-1) + …`

(`QED.ThreeLoopD.i13PB4`, eighteen harmonic polylogarithms of `ξ` of weight at most four with
constant coefficients) has `P₄' = (1 - ξ)²/(ξ (1 + ξ)²) β₃` (`QED.ThreeLoopD.hasDerivAt_i13PB4`).
So `β₄/r - P₄` is constant on `(0, 1)`; as `ξ → 1⁻`, `β₄ → 0` and
`P₄ → P₄(1) = 16 + 4ζ(3) + 2π²/3 + π⁴/40`, whence

  `β₄(t) = r (P₄(ξ) - 16 - 4ζ(3) - 2π²/3 - π⁴/40)` (`QED.ThreeLoopD.i13BubR_four`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i13PB4`, `QED.ThreeLoopD.i13PB4_one`.
* `QED.ThreeLoopD.i13BubR_four`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### The function `P₄` -/

/-- The harmonic-polylogarithm part of `P₄`. -/
noncomputable def i13PB4H (x : ℝ) : ℝ :=
    (8 - 2 * zeta3 - π ^ 2 / 3) * hpl [zero] x +
    (4 * zeta3 + 2 / 3 * π ^ 2) * hpl [negOne] x +
    (4 - π ^ 2 / 6) * hpl [zero, zero] x +
    (π ^ 2 / 3) * hpl [zero, negOne] x +
    (-8 + π ^ 2 / 3) * hpl [negOne, zero] x +
    (-2 / 3 * π ^ 2) * hpl [negOne, negOne] x +
    (2) * hpl [zero, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (8) * hpl [negOne, negOne, zero] x +
    (1) * hpl [zero, zero, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-2) * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (-2) * hpl [negOne, zero, zero, zero] x +
    (4) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, negOne, zero, zero] x +
    (-8) * hpl [negOne, negOne, negOne, zero] x

theorem hasDerivAt_i13PB4H {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13PB4H (
      (8 - 2 * zeta3 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
      (4 * zeta3 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
      (4 - π ^ 2 / 6) * (zero.kernel x * hpl [zero] x) +
      (π ^ 2 / 3) * (zero.kernel x * hpl [negOne] x) +
      (-8 + π ^ 2 / 3) * (negOne.kernel x * hpl [zero] x) +
      (-2 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x) +
      (2) * (zero.kernel x * hpl [zero, zero] x) +
      (-4) * (zero.kernel x * hpl [negOne, zero] x) +
      (-4) * (negOne.kernel x * hpl [zero, zero] x) +
      (8) * (negOne.kernel x * hpl [negOne, zero] x) +
      (1) * (zero.kernel x * hpl [zero, zero, zero] x) +
      (-2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
      (-2) * (zero.kernel x * hpl [negOne, zero, zero] x) +
      (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
      (-2) * (negOne.kernel x * hpl [zero, zero, zero] x) +
      (4) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
      (4) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
      (-8) * (negOne.kernel x * hpl [negOne, negOne, zero] x)) x := by
  unfold i13PB4H
  exact (((((((((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (8 - 2 * zeta3 -
    π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (4 * zeta3 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-8)))

theorem tendsto_i13PB4H_one : Tendsto i13PB4H (𝓝[<] 1) (𝓝 (i13PB4H 1)) := by
  unfold i13PB4H
  exact (((((((((((((((((((tendsto_hpl_one (a := zero) (by decide) []).const_mul (8 - 2 * zeta3 -
    π ^ 2 / 3)).add
      ((tendsto_hpl_one (a := negOne) (by decide) []).const_mul (4 * zeta3 + 2 / 3 * π ^ 2))).add
      ((tendsto_hpl_one (a := zero) (by decide) [zero]).const_mul (4 - π ^ 2 / 6))).add
      ((tendsto_hpl_one (a := zero) (by decide) [negOne]).const_mul (π ^ 2 / 3))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [zero]).const_mul (-8 + π ^ 2 / 3))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [negOne]).const_mul (-2 / 3 * π ^ 2))).add
      ((tendsto_hpl_one (a := zero) (by decide) [zero, zero]).const_mul (2))).add
      ((tendsto_hpl_one (a := zero) (by decide) [negOne, zero]).const_mul (-4))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [zero, zero]).const_mul (-4))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [negOne, zero]).const_mul (8))).add
      ((tendsto_hpl_one (a := zero) (by decide) [zero, zero, zero]).const_mul (1))).add
      ((tendsto_hpl_one (a := zero) (by decide) [zero, negOne, zero]).const_mul (-2))).add
      ((tendsto_hpl_one (a := zero) (by decide) [negOne, zero, zero]).const_mul (-2))).add
      ((tendsto_hpl_one (a := zero) (by decide) [negOne, negOne, zero]).const_mul (4))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [zero, zero, zero]).const_mul (-2))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [zero, negOne, zero]).const_mul (4))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [negOne, zero, zero]).const_mul (4))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [negOne, negOne, zero]).const_mul (-8)))

/-- `P₄(ξ)`. -/
noncomputable def i13PB4 (x : ℝ) : ℝ := 32 / (1 + x) + i13PB4H x

/-- `β₃` in the variable `ξ`: `i13Be3r t = i13Be3x (i13Xi t)`. -/
noncomputable def i13Be3x (x : ℝ) : ℝ := (1 + x) / (1 - x) * (i13PB x - i13P1c)

theorem i13Be3r_eq (t : ℝ) : i13Be3r t = i13Be3x (i13Xi t) := rfl

theorem hasDerivAt_i13PB4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13PB4 ((1 - x) ^ 2 / (x * (1 + x) ^ 2) * i13Be3x x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have e := ((hasDerivAt_const x (32 : ℝ)).div ((hasDerivAt_id' x).const_add 1) h2).add
    (hasDerivAt_i13PB4H hx)
  unfold i13PB4
  refine e.congr_deriv ?_
  unfold i13Be3x i13PB i13PBH i13P1c
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  ring

theorem i13PB4_one : i13PB4 1 = 16 + 4 * zeta3 + 2 * π ^ 2 / 3 + π ^ 4 / 40 := by
  unfold i13PB4 i13PB4H
  rw [
    hpl_zero_at_one, hpl_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_negOne_at_one,
    hpl_negOne_zero_at_one, hpl_negOne_negOne_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_zero_zero_zero_zero_at_one, hpl_zero_zero_negOne_zero_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_negOne_zero_zero_zero_at_one, hpl_negOne_zero_negOne_zero_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_negOne_negOne_zero_at_one]
  ring

theorem tendsto_i13PB4_one :
    Tendsto i13PB4 (𝓝[<] 1) (𝓝 (16 + 4 * zeta3 + 2 * π ^ 2 / 3 + π ^ 4 / 40)) := by
  rw [← i13PB4_one]
  unfold i13PB4
  refine Tendsto.add ?_ tendsto_i13PB4H_one
  exact ((continuousAt_const.div (continuousAt_const.add continuousAt_id)
    (by norm_num)).tendsto).mono_left nhdsWithin_le_nhds

/-! ### The fourth bubble coefficient -/

/-- The constant `P₄(1) = 16 + 4ζ(3) + 2π²/3 + π⁴/40`. -/
noncomputable def i13P4c : ℝ := 16 + 4 * zeta3 + 2 * π ^ 2 / 3 + π ^ 4 / 40

/-- `β₄(t) = r (P₄(ξ) - P₄(1))`, `ξ = ξ(t)`. -/
noncomputable def i13Be4r (t : ℝ) : ℝ :=
  (1 + i13Xi t) / (1 - i13Xi t) * (i13PB4 (i13Xi t) - i13P4c)

/-- `β₄(t(ξ)) (1 - ξ)/(1 + ξ) - P₄(ξ)`. -/
noncomputable def i13B4G (x : ℝ) : ℝ :=
  i13BubR 4 ((1 - x) ^ 2 / x) * ((1 - x) / (1 + x)) - (i13PB4 x - i13P4c)

theorem hasDerivAt_i13B4G {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i13B4G 0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have hT : 0 < (1 - x) ^ 2 / x := div_pos (by nlinarith [hx.2]) hx.1
  have hdT : HasDerivAt (fun y => (1 - y) ^ 2 / y) (-(1 - x) * (1 + x) / x ^ 2) x := by
    have := (((hasDerivAt_id' x).const_sub 1).pow 2).div (hasDerivAt_id' x) h0
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hB := HasDerivAt.comp (h := fun y => (1 - y) ^ 2 / y) x (hasDerivAt_i13BubR 3 hT) hdT
  have hq : HasDerivAt (fun y => (1 - y) / (1 + y)) (-2 / (1 + x) ^ 2) x := by
    have := ((hasDerivAt_id' x).const_sub 1).div ((hasDerivAt_id' x).const_add 1) h2
    refine this.congr_deriv ?_
    field_simp
    ring
  have e := (hB.mul hq).sub ((hasDerivAt_i13PB4 hx).sub_const i13P4c)
  unfold i13B4G
  refine e.congr_deriv ?_
  rw [i13BubR_three hT, i13Be3r_eq, i13Xi_of_xi hx.1 hx.2.le]
  have h4 : (1 - x) ^ 2 / x + 4 = (1 + x) ^ 2 / x := by field_simp; ring
  simp only [Function.comp_apply, h4]
  generalize i13BubR (3 + 1) ((1 - x) ^ 2 / x) = B
  generalize i13Be3x x = b
  field_simp
  ring

theorem tendsto_i13B4G_one : Tendsto i13B4G (𝓝[<] 1) (𝓝 0) := by
  have hT : Tendsto (fun y : ℝ => (1 - y) ^ 2 / y) (𝓝[<] 1) (𝓝 0) := by
    have : ContinuousAt (fun y : ℝ => (1 - y) ^ 2 / y) 1 :=
      ((continuous_const.sub continuous_id).pow 2).continuousAt.div continuousAt_id one_ne_zero
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun y : ℝ => i13BubR 4 ((1 - y) ^ 2 / y)) (𝓝[<] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hT.pow 4)
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with y hy
    rw [Real.norm_eq_abs]
    exact abs_i13BubR_le 4 (div_nonneg (sq_nonneg _) hy.1.le)
  have hq : Tendsto (fun y : ℝ => (1 - y) / (1 + y)) (𝓝[<] 1) (𝓝 0) := by
    have : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 1 :=
      (continuous_const.sub continuous_id).continuousAt.div
        (continuous_const.add continuous_id).continuousAt (by norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have := (hB.mul hq).sub (tendsto_i13PB4_one.sub_const i13P4c)
  unfold i13B4G
  simpa [i13P4c] using this

/-- **The fourth bubble coefficient** `β₄(t) = r (P₄(ξ) - 16 - 4ζ(3) - 2π²/3 - π⁴/40)`, `t > 0`. -/
theorem i13BubR_four {t : ℝ} (ht : 0 < t) : i13BubR 4 t = i13Be4r t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have h := eq_of_hasDerivAt_zero_of_tendsto_left zero_lt_one (fun x hx => hasDerivAt_i13B4G hx)
    tendsto_i13B4G_one (i13Xi t) ⟨hx0, hx1⟩
  unfold i13B4G at h
  rw [← hT] at h
  unfold i13Be4r
  have h1 : 1 - i13Xi t ≠ 0 := by linarith
  have h2 : 1 + i13Xi t ≠ 0 := by linarith
  have h' : i13PB4 (i13Xi t) - i13P4c =
      i13BubR 4 t * ((1 - i13Xi t) / (1 + i13Xi t)) := by linarith
  rw [h']
  field_simp

end QED.ThreeLoopD
