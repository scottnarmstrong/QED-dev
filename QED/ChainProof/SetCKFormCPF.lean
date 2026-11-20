/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCSig
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: integrating the branch-2 partial fractions in `s`

Helper level (no frozen statement). At fixed `(X, u)` the branch-2 integrand is a rational
function of `s` with poles only at the zeros of `s`, `B = u - X(1 - s)`, `C = X(1 - s) + (1 - X)u`
and `D = X²(1 - s) + (1 - X)(2 - s)u` (`coordD`), with `D' = -P`, `P = X² + (1 - X)u`. For
arbitrary coefficients, the partial-fraction sum `formCPF` (`q₀ + q₁ s + r/s + r'/s² + b/B + c/C +
d₁/D + d₂/D² + d₃/D³`) has the explicit antiderivative `formCPFA` (logs and poles):

**`hasDerivAt_formCPFA`**, **`integral_formCPFA`**: `∫_{(a, b)} formCPF = A(b) - A(a)` on any
`[a, b] ⊂ (0, ∞)` where `B, C, D > 0`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

/-- The coefficient vector of a branch-2 partial-fraction sum. -/
structure FormCPFc where
  /-- constant term -/
  q0 : ℝ
  /-- coefficient of `s` -/
  q1 : ℝ
  /-- coefficient of `1/s` -/
  r1 : ℝ
  /-- coefficient of `1/s²` -/
  r2 : ℝ
  /-- coefficient of `1/B` -/
  b : ℝ
  /-- coefficient of `1/C` -/
  c : ℝ
  /-- coefficient of `1/D` -/
  d1 : ℝ
  /-- coefficient of `1/D²` -/
  d2 : ℝ
  /-- coefficient of `1/D³` -/
  d3 : ℝ

/-- `B = u - X(1 - s)`. -/
def formCB (X u s : ℝ) : ℝ := u - X * (1 - s)

/-- `C = X(1 - s) + (1 - X)u`. -/
def formCC (X u s : ℝ) : ℝ := X * (1 - s) + (1 - X) * u

/-- `P = X² + (1 - X)u`, so that `∂ₛ D = -P`. -/
def formCP (X u : ℝ) : ℝ := X ^ 2 + (1 - X) * u

/-- **The partial-fraction sum.** -/
noncomputable def formCPF (k : FormCPFc) (X u s : ℝ) : ℝ :=
  k.q0 + k.q1 * s + k.r1 / s + k.r2 / s ^ 2 + k.b / formCB X u s + k.c / formCC X u s +
    k.d1 / coordD X u s + k.d2 / coordD X u s ^ 2 + k.d3 / coordD X u s ^ 3

/-- **Its antiderivative in `s`.** -/
noncomputable def formCPFA (k : FormCPFc) (X u s : ℝ) : ℝ :=
  k.q0 * s + k.q1 * s ^ 2 / 2 + k.r1 * log s - k.r2 / s + k.b / X * log (formCB X u s) -
    k.c / X * log (formCC X u s) - k.d1 / formCP X u * log (coordD X u s) +
    k.d2 / (formCP X u * coordD X u s) + k.d3 / (2 * formCP X u * coordD X u s ^ 2)

theorem hasDerivAt_formCPFA (k : FormCPFc) {X u s : ℝ} (hX : X ≠ 0) (hP : formCP X u ≠ 0)
    (hs : s ≠ 0) (hB : formCB X u s ≠ 0) (hC : formCC X u s ≠ 0) (hD : coordD X u s ≠ 0) :
    HasDerivAt (formCPFA k X u) (formCPF k X u s) s := by
  have hBd : HasDerivAt (fun s => formCB X u s) X s := by
    unfold formCB
    exact ((((hasDerivAt_id' s).const_sub 1).const_mul X).const_sub u).congr_deriv (by ring)
  have hCd : HasDerivAt (fun s => formCC X u s) (-X) s := by
    unfold formCC
    exact ((((hasDerivAt_id' s).const_sub 1).const_mul X).add_const _).congr_deriv (by ring)
  have hDd : HasDerivAt (fun s => coordD X u s) (-formCP X u) s := by
    unfold coordD formCP
    exact ((((hasDerivAt_id' s).const_sub 1).const_mul (X ^ 2)).add
      ((((hasDerivAt_id' s).const_sub 2).const_mul (1 - X)).mul_const u)).congr_deriv (by ring)
  have hd2 := ((hDd.const_mul (formCP X u)).inv (mul_ne_zero hP hD)).const_mul k.d2
  have hd3 := (((hDd.pow 2).const_mul (2 * formCP X u)).inv
    (mul_ne_zero (mul_ne_zero two_ne_zero hP) (pow_ne_zero 2 hD))).const_mul k.d3
  have h := ((((((((hasDerivAt_id' s).const_mul k.q0).add
    (((hasDerivAt_pow 2 s).const_mul k.q1).div_const 2)).add
    ((hasDerivAt_log hs).const_mul k.r1)).sub ((hasDerivAt_inv hs).const_mul k.r2)).add
    ((hBd.log hB).const_mul (k.b / X))).sub ((hCd.log hC).const_mul (k.c / X))).sub
    ((hDd.log hD).const_mul (k.d1 / formCP X u))).add hd2 |>.add hd3
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · simp only [Pi.pow_apply, Nat.cast_ofNat]
    unfold formCPF
    field_simp
    ring
  · simp only [formCPFA, div_eq_mul_inv, Pi.add_apply, Pi.sub_apply, Pi.inv_apply,
      Pi.pow_apply, mul_inv, mul_assoc]

/-- **The `s`-integral of a branch-2 partial-fraction sum.** -/
theorem integral_formCPF (k : FormCPFc) {X u a b : ℝ} (hX : X ≠ 0) (hP : formCP X u ≠ 0)
    (ha : 0 < a) (hab : a ≤ b)
    (hpos : ∀ s ∈ Icc a b, 0 < formCB X u s ∧ 0 < formCC X u s ∧ 0 < coordD X u s) :
    ∫ s in Ioo a b, formCPF k X u s = formCPFA k X u b - formCPFA k X u a := by
  have hc : ContinuousOn (formCPF k X u) (uIcc a b) := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    obtain ⟨hB, hC, hD⟩ := hpos s hs
    have : s ≠ 0 := (ha.trans_le hs.1).ne'
    have hB := hB.ne'
    have hC := hC.ne'
    have hD := hD.ne'
    have := pow_ne_zero 2 this
    have := pow_ne_zero 2 hD
    have := pow_ne_zero 3 hD
    unfold formCPF formCB formCC coordD at *
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => ?_) hc.intervalIntegrable
  rw [uIcc_of_le hab] at hs
  obtain ⟨hB, hC, hD⟩ := hpos s hs
  exact hasDerivAt_formCPFA k hX hP (ha.trans_le hs.1).ne' hB.ne' hC.ne' hD.ne'

end QED.ChainProof.SetCK

end
