/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOSX
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the `x`-integral of the outer self-energy node integrand

Helper level (no frozen statement). For `X ∈ (0, 1)` (**`integral_formOSF_x`**):

`∫₀^X F(x, Q(X) - Q(x)) dx = E(X)`,

`E(X) = e_X log X + e₁ log(1 - X) + e₂ log(2 - X) + e₀` with rational `e` (`formOSE`). Proof:
on `(0, X)` the integrand is `formOSFx X x` (`formOSF_eq`), which is interval integrable on
`[0, X]` (polynomials times `log(X - x)`, `log x` and logarithms of positive linear forms), and
`formOSG X` is a continuous antiderivative; its values at `X` and `0` give `E`
(`formOSG_sub`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The closed form of the kernel part of `H_oS`**. -/
noncomputable def formOSE (X : ℝ) : ℝ :=
  X ^ 4 * (3 + X ^ 2 - 4 * X + 2 * X ^ 3) / (12 * (-1 + X) ^ 4) * log X +
    (1 + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4) / 12 * log (1 - X) -
    X ^ 5 * (-2 + X) * (1 + X ^ 2 - X) / (6 * (-1 + X) ^ 4) * log (2 - X) +
    X * (-6 - 130 * X ^ 3 + 3 * X + 36 * X ^ 4 + 73 * X ^ 2) / (72 * (-1 + X))

section

variable {X x : ℝ}

/-- On `(0, X)` the node integrand is `formOSFx X`. -/
theorem formOSF_eq (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo 0 X) :
    formOSF x (setCKQ X - setCKQ x) = formOSFx X x := by
  have h0 := hx.1
  have h1x : 0 < 1 - x := by linarith [hx.2, hX.2]
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have hXx : 0 < X - x := by linarith [hx.2]
  have hB : 0 < X + x * (1 - X) := add_pos hX.1 (mul_pos h0 h1X)
  have hv : setCKQ X - setCKQ x = (X - x) * (X + x * (1 - X)) / ((1 - X) * (1 - x)) := by
    unfold setCKQ
    field_simp
    ring
  have hs : scOutRho x + (setCKQ X - setCKQ x) = x + setCKQ X := by
    unfold scOutRho setCKQ
    field_simp
    ring
  have lv : log (setCKQ X - setCKQ x) =
      log (X - x) + log (X + x * (1 - X)) - log (1 - X) - log (1 - x) := by
    rw [hv, log_div (by positivity) (by positivity), log_mul hXx.ne' hB.ne',
      log_mul h1X.ne' h1x.ne']
    ring
  have lr : log (scOutRho x) = log x - log (1 - x) := log_div h0.ne' h1x.ne'
  unfold formOSF formOSFx
  rw [hs, lv, lr]

/-- The values of the antiderivative at the ends give `E`. -/
theorem formOSG_sub (hX : X ∈ Ioo (0 : ℝ) 1) : formOSG X X - formOSG X 0 = formOSE X := by
  have h0 := hX.1
  have h1X : 0 < 1 - X := by linarith [hX.2]
  have h2X : 0 < 2 - X := by linarith [hX.2]
  have e1 : X + X * (1 - X) = X * (2 - X) := by ring
  have e2 : X + setCKQ X = X / (1 - X) := by
    unfold setCKQ
    field_simp
    ring
  have e3 : log (setCKQ X) = 2 * log X - log (1 - X) := by
    unfold setCKQ
    rw [log_div (by positivity) h1X.ne', log_pow]
    push_cast
    ring
  unfold formOSG
  simp only [sub_self, zero_mul, mul_zero, sub_zero, zero_add, add_zero, log_one]
  rw [e1, e2, e3, log_mul h0.ne' h2X.ne', log_div h0.ne' h1X.ne']
  unfold formOSSA formOSSB formOSSD formOSSx formOSS1 formOST formOSP6 formOSE setCKQ
  generalize log X = LX
  generalize log (1 - X) = L1
  generalize log (2 - X) = L2
  have : -1 + X ≠ 0 := by linarith [hX.2]
  have := h1X.ne'
  have := h0.ne'
  field_simp
  ring

theorem intervalIntegrable_formOSFx (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (formOSFx X) volume 0 X := by
  have h0 := hX.1
  have hQ : 0 < setCKQ X := by
    unfold setCKQ
    have : 0 < 1 - X := by linarith [hX.2]
    positivity
  set s := uIcc 0 X with hs
  have mem : ∀ y ∈ s, 0 ≤ y ∧ y ≤ X := fun y hy => by
    rw [hs, uIcc_of_le h0.le] at hy
    exact hy
  have cQ : ContinuousOn (fun y => setCKQ y) s := by
    unfold setCKQ
    exact (continuousOn_pow 2).div (continuousOn_const.sub continuousOn_id) fun y hy => by
      linarith [(mem y hy).2, hX.2]
  have cB : ContinuousOn (fun y => log (X + y * (1 - X))) s :=
    ContinuousOn.log (by fun_prop) fun y hy => by
      have := (mem y hy).1
      have : 0 < 1 - X := by linarith [hX.2]
      positivity
  have c1 : ContinuousOn (fun y => log (1 - y)) s :=
    ContinuousOn.log (by fun_prop) fun y hy => by linarith [(mem y hy).2, hX.2]
  have cD : ContinuousOn (fun y => log (y + setCKQ X)) s :=
    ContinuousOn.log (by fun_prop) fun y hy => by linarith [(mem y hy).1, hQ]
  have cv : ContinuousOn (fun y => formOSCv y (setCKQ X - setCKQ y)) s := by
    unfold formOSCv
    fun_prop
  have cr : ContinuousOn (fun y => formOSCr y) s := by
    unfold formOSCr
    fun_prop
  have c0 : ContinuousOn (fun y => formOSC0 y (setCKQ X - setCKQ y)) s := by
    unfold formOSC0
    fun_prop
  have iA : IntervalIntegrable (fun y => log (X - y)) volume 0 X := by
    simpa using (intervalIntegral.intervalIntegrable_log' (a := X) (b := 0)).comp_sub_left X
  have iX : IntervalIntegrable (fun y => log y) volume 0 X :=
    intervalIntegral.intervalIntegrable_log'
  have iR : IntervalIntegrable (fun y => formOSCv y (setCKQ X - setCKQ y) *
      (log (X + y * (1 - X)) - log (1 - X) - log (1 - y) - log (y + setCKQ X)) +
        formOSCr y * (-log (1 - y) - log (y + setCKQ X)) +
        formOSC0 y (setCKQ X - setCKQ y)) volume 0 X := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ((cv.mul (((cB.sub continuousOn_const).sub c1).sub cD)).add
      (cr.mul (c1.neg.sub cD))).add c0
  have e : formOSFx X = fun y => formOSCv y (setCKQ X - setCKQ y) * log (X - y) +
      formOSCr y * log y + (formOSCv y (setCKQ X - setCKQ y) *
        (log (X + y * (1 - X)) - log (1 - X) - log (1 - y) - log (y + setCKQ X)) +
        formOSCr y * (-log (1 - y) - log (y + setCKQ X)) +
        formOSC0 y (setCKQ X - setCKQ y)) := by
    funext y
    unfold formOSFx
    ring
  rw [e]
  exact ((iA.continuousOn_mul cv).add (iX.continuousOn_mul cr)).add iR

end

/-- **The `x`-integral of the outer self-energy node integrand**: for `X ∈ (0, 1)`,
`x ↦ F(x, Q(X) - Q(x))` is integrable on `(0, X)` with integral `E(X)`. -/
theorem integral_formOSF_x {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => formOSF x (setCKQ X - setCKQ x)) (Ioo 0 X) ∧
      ∫ x in Ioo 0 X, formOSF x (setCKQ X - setCKQ x) = formOSE X := by
  have hi := intervalIntegrable_formOSFx hX
  have he : EqOn (fun x => formOSF x (setCKQ X - setCKQ x)) (formOSFx X) (Ioo 0 X) :=
    fun x hx => formOSF_eq hX hx
  refine ⟨(((intervalIntegrable_iff_integrableOn_Ioc_of_le hX.1.le).1 hi).mono_set
    Ioo_subset_Ioc_self).congr_fun he.symm measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo he, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hX.1.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX.1.le
      (continuous_formOSG X).continuousOn (fun x hx => hasDerivAt_formOSG hX hx) hi,
    formOSG_sub hX]

end QED.ChainProof.SetCK

end
