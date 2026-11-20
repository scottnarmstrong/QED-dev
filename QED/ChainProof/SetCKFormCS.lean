/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInKt
public import QED.ChainProof.SetCKFormOSX
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the inner corner weight integrated over `x`

Helper level (no frozen statement). First step of the closed form of the inner corner density
`ρ_C` (`rhoCornIn`). At a node `(Y, y₃)` with `0 < y₃ < Y < 1` the total `w`-weight
`K_tot(Y, y₃, x, m)` (`cornInKt`) is integrated over `x ∈ (0, 1)` at a fixed value `m` of `w`.
The threshold `w₀(x) = β(x) x` (`cornInW0`) is strictly increasing in `x`
(`cornInW0_lt_of_lt`), so if `w₀(s) = m` the weight is `K(m)` (a polynomial in `x`) for
`x < s` and `-(1 - x)/2 - 1{x* < x} φ'(x)` for `x > s`. With `φ(1) = φ(x*) = 0`:

**`integral_cornInKt_x`**: `∫₀¹ K_tot(Y, y₃, x, m) dx = P(s) - (1 - s)²/4 + φ(max(s, x*))`,

where `P` (`formCPrim`) is the antiderivative of `K(m)` in `x` with `P(0) = 0`
(`hasDerivAt_formCPrim`). No square root of the threshold equation is needed: the value is
stated at any `s` with `w₀(s) = m`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `m³ K(m) = k₁ x + k₂ x² + k₃ x³ + k₄ x⁴`: the coefficient `k₁`. -/
noncomputable def formCk1 (Y y3 m : ℝ) : ℝ :=
  -m * (-Y ^ 3 * y3 - Y ^ 2 * m + 3 * Y ^ 2 * y3 + Y * m * y3 + 2 * Y * m - 2 * Y * y3 +
    m * y3 - 2 * m) / 2

/-- The coefficient `k₂` of `m³ K(m)`. -/
noncomputable def formCk2 (Y y3 m : ℝ) : ℝ :=
  m * (-8 * Y ^ 2 * y3 ^ 2 + 2 * Y ^ 2 * y3 + 2 * Y * m * y3 + 2 * Y * m + 4 * Y * y3 ^ 2 +
    4 * Y * y3 + 6 * m * y3 ^ 2 - 2 * m * y3 - 5 * m + 4 * y3 ^ 2 - 6 * y3) / 4

/-- The coefficient `k₃` of `m³ K(m)`. -/
noncomputable def formCk3 (Y y3 m : ℝ) : ℝ :=
  y3 * (2 * Y ^ 2 * m * y3 - 2 * Y ^ 2 * y3 ^ 2 + Y ^ 2 * y3 + 2 * Y * m * y3 ^ 2 -
    2 * Y * m * y3 - 2 * Y * m + 4 * Y * y3 ^ 2 - 2 * Y * y3 - 2 * m ^ 2 * y3 + 2 * m ^ 2 -
    2 * m * y3 ^ 2 + 2 * m - 2 * y3 ^ 2 + y3)

/-- The coefficient `k₄` of `m³ K(m)`. -/
noncomputable def formCk4 (Y y3 m : ℝ) : ℝ :=
  -5 * y3 ^ 2 * (Y - 1) * (-2 * Y * y3 + Y + 2 * m * y3 - 2 * m + 2 * y3 - 1) / 4

/-- **The antiderivative** `P(x) = ∫₀^x K(m)` of the weight beyond the threshold. -/
noncomputable def formCPrim (Y y3 m x : ℝ) : ℝ :=
  formOSP6 0 0 (formCk1 Y y3 m / (2 * m ^ 3)) (formCk2 Y y3 m / (3 * m ^ 3))
    (formCk3 Y y3 m / (4 * m ^ 3)) (formCk4 Y y3 m / (5 * m ^ 3)) 0 x

/-- `K(m)` at the node `(Y, y₃, x)`. -/
noncomputable def formCOm (Y y3 x m : ℝ) : ℝ :=
  cornInOm (cornerA1 x y3 (Y - y3)) (cornerA2 x y3 (Y - y3)) (cornerC1 x y3 (Y - y3))
    (cornerC2 x y3 (Y - y3)) (cornerC3 x y3 (Y - y3)) x m

theorem formCPrim_zero (Y y3 m : ℝ) : formCPrim Y y3 m 0 = 0 := by
  simp [formCPrim, formOSP6]

theorem hasDerivAt_formCPrim {Y y3 m : ℝ} (hm : m ≠ 0) (x : ℝ) :
    HasDerivAt (formCPrim Y y3 m) (formCOm Y y3 x m) x := by
  refine (hasDerivAt_formOSP6 _ _ _ _ _ _ _ x).congr_deriv ?_
  simp only [formOSP6, formCOm, cornInOm, formCk1, formCk2, formCk3, formCk4, cornerA1,
    cornerA2, cornerC1, cornerC2, cornerC3, cornerG, cornerQ, cornerR,
    QED.TwoLoop.UnitSCReduce.cornerP1, QED.TwoLoop.UnitSCReduce.cornerP2]
  field_simp
  ring

theorem continuous_formCOm (Y y3 m : ℝ) : Continuous fun x => formCOm Y y3 x m := by
  unfold formCOm cornInOm cornerA1 cornerA2 cornerC1 cornerC2 cornerC3 cornerG cornerQ cornerR
    QED.TwoLoop.UnitSCReduce.cornerP1 QED.TwoLoop.UnitSCReduce.cornerP2
  fun_prop

/-- **The threshold `w₀(x)` is strictly increasing** on `(0, 1)`. -/
theorem cornInW0_lt_of_lt {Y y3 x x' : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hx : 0 < x) (hxx : x < x') (hx' : x' < 1) : cornInW0 Y y3 x < cornInW0 Y y3 x' := by
  have hg : 0 < cornerG y3 (Y - y3) := by unfold cornerG; nlinarith
  have hb : 0 < betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x := betaG_pos hg
  have hmono : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x ≤
      betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x' := by
    unfold betaG
    refine max_le_max le_rfl ?_
    have he : 0 ≤ y3 * (Y - y3) := by nlinarith
    have h1 : 0 < 1 - x := by linarith
    have h1' : 0 < 1 - x' := by linarith
    rw [div_le_div_iff₀ h1 h1']
    nlinarith [mul_nonneg he (sub_nonneg.2 hxx.le)]
  unfold cornInW0
  calc _ < betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x * x' :=
        mul_lt_mul_of_pos_left hxx hb
    _ ≤ _ := mul_le_mul_of_nonneg_right hmono (by linarith)

/-- **The `x`-integral of the total weight** at a node, given the threshold `w₀(s) = m`. -/
theorem integral_cornInKt_x {Y y3 s m : ℝ} (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hm : cornInW0 Y y3 s = m) :
    IntegrableOn (fun x => cornInKt Y y3 x m) (Ioo 0 1) ∧
      ∫ x in Ioo (0 : ℝ) 1, cornInKt Y y3 x m =
        formCPrim Y y3 m s - (1 - s) ^ 2 / 4 + cornInPhi Y y3 (max s (cornInXs Y y3)) := by
  have hm0 : 0 < m := hm ▸ cornInW0_pos hY h3 hs.1
  set xs := cornInXs Y y3 with hxs_def
  have hxs := cornInXs_mem h3 h34 hY
  set a := max s xs with ha
  have hsa : s ≤ a := le_max_left _ _
  have ha1 : a < 1 := max_lt hs.2 hxs.2
  set f := fun x => cornInKt Y y3 x m with hf
  -- below the threshold
  have e1 : EqOn f (fun x => formCOm Y y3 x m) (uIoo 0 s) := by
    intro x hx
    rw [uIoo_of_le hs.1.le] at hx
    have hlt : cornInW0 Y y3 x < m := hm ▸ cornInW0_lt_of_lt h3 h34 hY hx.1 hx.2 hs.2
    simp only [hf, cornInKt, cornInKw_of_lt hlt, not_le.2 hlt, ↓reduceIte, mul_zero, sub_zero,
      formCOm]
  -- above the threshold
  have e2 : EqOn f (fun x => -((1 - x) / 2) - cornInDPhiC Y y3 x) (uIoo s 1) := by
    intro x hx
    rw [uIoo_of_le hs.2.le] at hx
    have hlt : m < cornInW0 Y y3 x := hm ▸ cornInW0_lt_of_lt h3 h34 hY hs.1 hx.1 hx.2
    simp only [hf, cornInKt, cornInKw_of_le (hs.1.trans hx.1).ne' hlt.le, hlt.le, ↓reduceIte,
      mul_one]
  have e3 : EqOn (cornInDPhiC Y y3) (fun _ => 0) (uIoo s a) := by
    intro x hx
    rw [uIoo_of_le hsa] at hx
    have : ¬ xs < x := by
      intro h
      exact absurd hx.2 (not_lt.2 (max_le hx.1.le h.le))
    simp only [cornInDPhiC, ← hxs_def, this, ↓reduceIte]
  have e4 : EqOn (cornInDPhiC Y y3) (cornInDPhi Y y3) (uIoo a 1) := by
    intro x hx
    rw [uIoo_of_le ha1.le] at hx
    simp only [cornInDPhiC, ← hxs_def, (le_max_right s xs).trans_lt hx.1, ↓reduceIte]
  -- the boundary function `φ` on `[a, 1]`
  have ha0 : 0 < a := hs.1.trans_le hsa
  have hd : ∀ x ∈ uIcc a 1, HasDerivAt (cornInPhi Y y3) (cornInDPhi Y y3 x) x := by
    intro x hx
    rw [uIcc_of_le ha1.le] at hx
    exact hasDerivAt_cornInPhi (by linarith [hx.1]) (by linarith [hx.2]) h3.ne'
      (by linarith)
  have cD : ContinuousOn (cornInDPhi Y y3) (uIcc a 1) := by
    intro x hx
    rw [uIcc_of_le ha1.le] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hx2 : x - 2 ≠ 0 := by linarith [hx.2]
    have hy : y3 - Y ≠ 0 := by linarith
    unfold cornInDPhi
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    have := h3.ne'
    positivity
  have iD : IntervalIntegrable (cornInDPhi Y y3) volume a 1 := cD.intervalIntegrable
  have iDC : IntervalIntegrable (cornInDPhiC Y y3) volume s 1 :=
    (((intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo fun x hx => (e3 hx).symm).trans
      (iD.congr_uIoo fun x hx => (e4 hx).symm))
  have iL : IntervalIntegrable (fun x : ℝ => -((1 - x) / 2)) volume s 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have i1 : IntervalIntegrable f volume 0 s :=
    ((continuous_formCOm Y y3 m).intervalIntegrable 0 s).congr_uIoo fun x hx => (e1 hx).symm
  have i2 : IntervalIntegrable f volume s 1 :=
    (iL.sub iDC).congr_uIoo fun x hx => (e2 hx).symm
  have i12 := i1.trans i2
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 i12, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    intervalIntegral.integral_congr_uIoo e1, intervalIntegral.integral_congr_uIoo e2,
    intervalIntegral.integral_sub iL iDC,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_formCPrim hm0.ne' x)
      ((continuous_formCOm Y y3 m).intervalIntegrable 0 s), formCPrim_zero]
  have iC0 : IntervalIntegrable (cornInDPhiC Y y3) volume s a :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo fun x hx => (e3 hx).symm
  have iC1 : IntervalIntegrable (cornInDPhiC Y y3) volume a 1 :=
    iD.congr_uIoo fun x hx => (e4 hx).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals iC0 iC1,
    intervalIntegral.integral_congr_uIoo e3, intervalIntegral.integral_congr_uIoo e4,
    intervalIntegral.integral_const, smul_zero, zero_add,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd iD, cornInPhi_one]
  have hL : ∫ x in s..1, -((1 - x) / 2) = -((1 - s) ^ 2 / 4) := by
    have h : ∀ x ∈ uIcc s 1, HasDerivAt (fun x : ℝ => (1 - x) ^ 2 / 4) (-((1 - x) / 2)) x := by
      intro x _
      have := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)).pow 2 |>.div_const 4
      refine this.congr_deriv ?_
      simp only [Pi.sub_apply]
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h iL]
    ring
  rw [hL]
  ring

end QED.ChainProof.SetCK

end
