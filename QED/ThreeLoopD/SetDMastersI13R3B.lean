/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R3O
public import QED.ThreeLoopD.SetDMastersI13R3W
public import QED.Polylog.HPLValues

/-!
# Set (d), master `I₁₃`: the third bubble coefficient

In the variable `ξ` (`t = (1 - ξ)²/ξ`, `r = (1 + ξ)/(1 - ξ)`), the bubble differential equation
(`QED.ThreeLoopD.hasDerivAt_i13BubR`) reads `(β₃/r)' = (1 - ξ)²/(ξ (1 + ξ)²) β₂`. With

  `P(ξ) = 16/(1 + ξ) + (4 - π²/6) H(0) + π²/3 H(-1) - 4 H(-1, 0) + 2 H(0, 0) - 2 H(0, -1, 0)
    + 4 H(-1, -1, 0) + H(0, 0, 0) - 2 H(-1, 0, 0)`

(`QED.ThreeLoopD.i13PB`, harmonic polylogarithms of `ξ`), `P' = (1 - ξ)²/(ξ (1 + ξ)²) β₂`
(`QED.ThreeLoopD.hasDerivAt_i13PB`). So `β₃/r - P` is constant on `(0, 1)`; as `ξ → 1⁻`,
`t → 0`, `β₃ → 0` and `P → P(1) = 8 + 2ζ(3) + π²/3`, whence

  `β₃(t) = r (P(ξ) - 8 - 2ζ(3) - π²/3)` (`QED.ThreeLoopD.i13BubR_three`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i13PB`, `QED.ThreeLoopD.i13PB_one`.
* `QED.ThreeLoopD.i13BubR_three`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### Classical functions as harmonic polylogarithms -/

theorem i13_Li₂_neg_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : Li₂ (-x) = -hpl [zero, negOne] x := by
  rw [hpl_zero_negOne hx, Li_two, neg_neg]

theorem i13_log_one_add_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.log (1 + x) = hpl [negOne] x := (hpl_negOne hx).symm

theorem i13_log_one_sub_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.log (1 - x) = -hpl [one] x := by
  rw [hpl_one hx, neg_neg]

/-! ### The function `P` -/

/-- The harmonic-polylogarithm part of `P`. -/
noncomputable def i13PBH (x : ℝ) : ℝ :=
    (π ^ 2 / 3) * hpl [negOne] x +
    (4 - π ^ 2 / 6) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (2) * hpl [zero, zero] x +
    (4) * hpl [negOne, negOne, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, zero] x

theorem hasDerivAt_i13PBH {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13PBH (
      (π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
      (4 - π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
      (-4) * (negOne.kernel x * hpl [zero] x) +
      (2) * (zero.kernel x * hpl [zero] x) +
      (4) * (negOne.kernel x * hpl [negOne, zero] x) +
      (-2) * (negOne.kernel x * hpl [zero, zero] x) +
      (-2) * (zero.kernel x * hpl [negOne, zero] x) +
      (1) * (zero.kernel x * hpl [zero, zero] x)) x := by
  unfold i13PBH
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1))

theorem tendsto_i13PBH_one : Tendsto i13PBH (𝓝[<] 1) (𝓝 (i13PBH 1)) := by
  unfold i13PBH
  exact ((((((((tendsto_hpl_one (a := negOne) (by decide) []).const_mul (π ^ 2 / 3)).add
      ((tendsto_hpl_one (a := zero) (by decide) []).const_mul (4 - π ^ 2 / 6))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [zero]).const_mul (-4))).add
      ((tendsto_hpl_one (a := zero) (by decide) [zero]).const_mul (2))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [negOne, zero]).const_mul (4))).add
      ((tendsto_hpl_one (a := negOne) (by decide) [zero, zero]).const_mul (-2))).add
      ((tendsto_hpl_one (a := zero) (by decide) [negOne, zero]).const_mul (-2))).add
      ((tendsto_hpl_one (a := zero) (by decide) [zero, zero]).const_mul (1))

/-- `P(ξ)`. -/
noncomputable def i13PB (x : ℝ) : ℝ := 16 / (1 + x) + i13PBH x

/-- `β₂` in the variable `ξ`: `i13Be2r t = i13Be2x (i13Xi t)`. -/
noncomputable def i13Be2x (x : ℝ) : ℝ :=
  4 - (1 + x) / (1 - x) * (2 * Li₂ (-x) + 2 * Real.log x * Real.log (1 + x) -
    Real.log x ^ 2 / 2 - 2 * Real.log x + π ^ 2 / 6)

theorem i13Be2r_eq (t : ℝ) : i13Be2r t = i13Be2x (i13Xi t) := rfl

theorem hasDerivAt_i13PB {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13PB ((1 - x) ^ 2 / (x * (1 + x) ^ 2) * i13Be2x x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have e := ((hasDerivAt_const x (16 : ℝ)).div ((hasDerivAt_id' x).const_add 1) h2).add
    (hasDerivAt_i13PBH hx)
  unfold i13PB
  refine e.congr_deriv ?_
  unfold i13Be2x
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_00,
    i13_Li₂_neg_eq hx, i13_log_one_add_eq hx]
  field_simp
  ring

theorem i13PB_one : i13PB 1 = 8 + 2 * zeta3 + π ^ 2 / 3 := by
  unfold i13PB i13PBH
  rw [hpl_negOne_at_one, hpl_zero_at_one, hpl_negOne_zero_at_one, hpl_zero_zero_at_one,
    hpl_negOne_negOne_zero_at_one, hpl_negOne_zero_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_zero_zero_at_one]
  ring

theorem tendsto_i13PB_one : Tendsto i13PB (𝓝[<] 1) (𝓝 (8 + 2 * zeta3 + π ^ 2 / 3)) := by
  rw [← i13PB_one]
  unfold i13PB
  refine Tendsto.add ?_ tendsto_i13PBH_one
  exact ((continuousAt_const.div (continuousAt_const.add continuousAt_id)
    (by norm_num)).tendsto).mono_left nhdsWithin_le_nhds

/-! ### The third bubble coefficient -/

theorem i13Xi_of_xi {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) : i13Xi ((1 - x) ^ 2 / x) = x := by
  unfold i13Xi
  have hs : √((1 - x) ^ 2 / x * ((1 - x) ^ 2 / x + 4)) = (1 - x) * (1 + x) / x := by
    rw [show (1 - x) ^ 2 / x * ((1 - x) ^ 2 / x + 4) = ((1 - x) * (1 + x) / x) ^ 2 by
      field_simp; ring]
    exact Real.sqrt_sq (div_nonneg (mul_nonneg (by linarith) (by linarith)) h0.le)
  rw [hs]
  field_simp
  ring

/-- The constant `P(1) = 8 + 2ζ(3) + π²/3`. -/
noncomputable def i13P1c : ℝ := 8 + 2 * zeta3 + π ^ 2 / 3

/-- `β₃(t) = r (P(ξ) - P(1))`, `ξ = ξ(t)`. -/
noncomputable def i13Be3r (t : ℝ) : ℝ :=
  (1 + i13Xi t) / (1 - i13Xi t) * (i13PB (i13Xi t) - i13P1c)

/-- `β₃(t(ξ)) (1 - ξ)/(1 + ξ) - P(ξ)`. -/
noncomputable def i13B3G (x : ℝ) : ℝ :=
  i13BubR 3 ((1 - x) ^ 2 / x) * ((1 - x) / (1 + x)) - (i13PB x - i13P1c)

theorem hasDerivAt_i13B3G {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i13B3G 0 x := by
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
  have hB := HasDerivAt.comp (h := fun y => (1 - y) ^ 2 / y) x (hasDerivAt_i13BubR 2 hT) hdT
  have hq : HasDerivAt (fun y => (1 - y) / (1 + y)) (-2 / (1 + x) ^ 2) x := by
    have := ((hasDerivAt_id' x).const_sub 1).div ((hasDerivAt_id' x).const_add 1) h2
    refine this.congr_deriv ?_
    field_simp
    ring
  have e := (hB.mul hq).sub ((hasDerivAt_i13PB hx).sub_const i13P1c)
  unfold i13B3G
  refine e.congr_deriv ?_
  rw [i13BubR_two hT, i13Be2r_eq, i13Xi_of_xi hx.1 hx.2.le]
  have h4 : (1 - x) ^ 2 / x + 4 = (1 + x) ^ 2 / x := by field_simp; ring
  simp only [Function.comp_apply, h4]
  generalize i13BubR (2 + 1) ((1 - x) ^ 2 / x) = B
  generalize i13Be2x x = b
  field_simp
  ring

theorem tendsto_i13B3G_one : Tendsto i13B3G (𝓝[<] 1) (𝓝 0) := by
  have hT : Tendsto (fun y : ℝ => (1 - y) ^ 2 / y) (𝓝[<] 1) (𝓝 0) := by
    have : ContinuousAt (fun y : ℝ => (1 - y) ^ 2 / y) 1 :=
      ((continuous_const.sub continuous_id).pow 2).continuousAt.div continuousAt_id one_ne_zero
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun y : ℝ => i13BubR 3 ((1 - y) ^ 2 / y)) (𝓝[<] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hT.pow 3)
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with y hy
    rw [Real.norm_eq_abs]
    exact abs_i13BubR_le 3 (div_nonneg (sq_nonneg _) hy.1.le)
  have hq : Tendsto (fun y : ℝ => (1 - y) / (1 + y)) (𝓝[<] 1) (𝓝 0) := by
    have : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 1 :=
      (continuous_const.sub continuous_id).continuousAt.div
        (continuous_const.add continuous_id).continuousAt (by norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have := (hB.mul hq).sub (tendsto_i13PB_one.sub_const i13P1c)
  unfold i13B3G
  simpa [i13P1c] using this

/-- **The third bubble coefficient** `β₃(t) = r (P(ξ) - 8 - 2ζ(3) - π²/3)`, `t > 0`. -/
theorem i13BubR_three {t : ℝ} (ht : 0 < t) : i13BubR 3 t = i13Be3r t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have hT := i13Xi_t ht.le
  have h := eq_of_hasDerivAt_zero_of_tendsto_left zero_lt_one (fun x hx => hasDerivAt_i13B3G hx)
    tendsto_i13B3G_one (i13Xi t) ⟨hx0, hx1⟩
  unfold i13B3G at h
  rw [← hT] at h
  unfold i13Be3r
  have h1 : 1 - i13Xi t ≠ 0 := by linarith
  have h2 : 1 + i13Xi t ≠ 0 := by linarith
  have h' : i13PB (i13Xi t) - i13P1c =
      i13BubR 3 t * ((1 - i13Xi t) / (1 + i13Xi t)) := by linarith
  rw [h']
  field_simp

end QED.ThreeLoopD
