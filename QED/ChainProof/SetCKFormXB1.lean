/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXBr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the branch-1 `s`-integral of `I(X)`

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 24+). On branch 1, with `Y = Y(u)` (`coordY1`) and `y₃ = (Y - u)/s`, the integrand
`J₁ S₁` is a Laurent polynomial in `s` (sympy `fxf/r1.py`):

**`formXKin1_eq`**: `formXKin1 X u s = formXL1 Y u s = (b₀ + b₁ s + b₂ s² + b₃ s³ + b₄ s⁴) /
(12 s³ (Y - 1))`, with `b_k = formXb k` polynomials in `(Y, u)`;

its antiderivative `formXA1` (with `b₂ log s`) gives, for `u ∈ (0, X)`,

**`integral_formXKin1`**: `∫_{(s_lo(u), 1-u]} formXKin1 X u s ds =
  A₁(Y, u, 1 - u) - A₁(Y, u, s_lo(u))`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `b₀`. -/
def formXb0 (Y u : ℝ) : ℝ := (Y - u) ^ 2 * (4 * Y ^ 2 + Y * u - 9 * Y - u + 6)

/-- `b₁`. -/
def formXb1 (Y u : ℝ) : ℝ :=
  (Y - u) * (Y - 1) * (-4 * Y ^ 2 + 3 * Y * u + 7 * Y + 6 * u ^ 2 - 8 * u - 3)

/-- `b₂`, the coefficient of `log s` in the antiderivative. -/
def formXb2 (Y u : ℝ) : ℝ :=
  2 * Y ^ 4 + 2 * Y ^ 3 * u - 11 * Y ^ 3 + 2 * Y ^ 2 * u ^ 2 - 10 * Y ^ 2 * u + 27 * Y ^ 2 -
    16 * Y * u ^ 2 + 23 * Y * u - 25 * Y + 14 * u ^ 2 - 15 * u + 6

/-- `b₃`. -/
def formXb3 (Y u : ℝ) : ℝ := (Y - 1) * (4 * Y ^ 2 + 8 * Y * u - 20 * Y - 14 * u + 11)

/-- `b₄`. -/
def formXb4 (Y : ℝ) : ℝ := 6 * (Y - 1) ^ 2

/-- **The branch-1 integrand** as a Laurent polynomial in `s`. -/
noncomputable def formXL1 (Y u s : ℝ) : ℝ :=
  (formXb0 Y u + formXb1 Y u * s + formXb2 Y u * s ^ 2 + formXb3 Y u * s ^ 3 +
    formXb4 Y * s ^ 4) / (12 * s ^ 3 * (Y - 1))

/-- **Its `s`-antiderivative** `A₁`. -/
noncomputable def formXA1 (Y u s : ℝ) : ℝ :=
  (-formXb0 Y u / (2 * s ^ 2) - formXb1 Y u / s + formXb2 Y u * log s + formXb3 Y u * s +
    formXb4 Y * s ^ 2 / 2) / (12 * (Y - 1))

section

variable {X u : ℝ}

theorem formX_coordJ1_eq (hX : X ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) (s : ℝ) :
    coordJ1 X u s = (1 - coordY1 X u) ^ 2 * (coordY1 X u - u) / s ^ 2 := by
  have hM := (coordM_pos hX hu).ne'
  unfold coordJ1 coordY1
  field_simp
  unfold coordM
  ring

theorem formX_Y1_lt_one (hX : X ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) : coordY1 X u < 1 := by
  have hM := coordM_pos hX hu
  unfold coordY1
  rw [div_lt_one hM]
  unfold coordM
  nlinarith [hX.2]

theorem formX_Y1_sub_pos (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) : 0 < coordY1 X u - u := by
  have hM := coordM_pos hX hu.1.le
  have h1 : coordY1 X u - u = (X - u) * (X + u - X * u) / coordM X u := by
    unfold coordY1
    field_simp
    unfold coordM
    ring
  rw [h1]
  have : 0 < X - u := by linarith [hu.2]
  have : 0 < X + u - X * u := by nlinarith [hu.1, hX.2]
  positivity

/-- The branch-1 identity, as an identity of rational functions of `(Y, y₃ = (Y - u)/s, s)`. -/
theorem formXL1_eq {Y s : ℝ} (hs : s ≠ 0) (hYu : Y - u ≠ 0) (hY : Y - 1 ≠ 0) :
    (1 - Y) ^ 2 * (Y - u) / s ^ 2 * formXS1 Y ((Y - u) / s) s = formXL1 Y u s := by
  unfold formXS1 formXN1 formXL1 formXb0 formXb1 formXb2 formXb3 formXb4
  field_simp
  ring

/-- **The branch-1 integrand in closed form.** -/
theorem formXKin1_eq (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) {s : ℝ} (hs : s ≠ 0) :
    formXKin1 X u s = formXL1 (coordY1 X u) u s := by
  unfold formXKin1 coordPsi1
  rw [formX_coordJ1_eq hX hu.1.le]
  exact formXL1_eq hs (formX_Y1_sub_pos hX hu).ne' (by linarith [formX_Y1_lt_one hX hu.1.le])

theorem hasDerivAt_formXA1 {Y : ℝ} (hY : Y - 1 ≠ 0) (u : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (formXA1 Y u) (formXL1 Y u s) s := by
  have h2 := (hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs)
  have h := (((((h2.const_mul (-formXb0 Y u / 2)).sub ((hasDerivAt_inv hs).const_mul
    (formXb1 Y u))).add ((hasDerivAt_log hs).const_mul (formXb2 Y u))).add
    ((hasDerivAt_id' s).const_mul (formXb3 Y u))).add
    (((hasDerivAt_pow 2 s).const_mul (formXb4 Y)).div_const 2)).div_const (12 * (Y - 1))
  convert h using 1
  · funext t
    simp only [formXA1, Pi.add_apply, Pi.sub_apply, Pi.inv_apply]
    ring
  · unfold formXL1
    field_simp
    ring

theorem formX_sLo_pos (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) : 0 < coordSLo X u := by
  have := hX.1
  have : 0 < X - u := by linarith [hu.2]
  have : 0 < X + u - X * u := by nlinarith [hu.1, hX.2]
  have : 0 < 1 - X := by linarith [hX.2]
  have : 0 < X ^ 2 + (1 - X) * u := by nlinarith [hu.1]
  unfold coordSLo
  positivity

theorem formX_sLo_le (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) : coordSLo X u ≤ 1 - u := by
  have : 0 < X ^ 2 + (1 - X) * u := by nlinarith [hu.1, hX.1, hX.2]
  unfold coordSLo
  rw [div_le_iff₀ this]
  nlinarith [hu.1, hX.2]

/-- **The branch-1 `s`-integral** by the fundamental theorem of calculus. -/
theorem integral_formXKin1 (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) :
    ∫ s in Ioc (coordSLo X u) (1 - u), formXKin1 X u s =
      formXA1 (coordY1 X u) u (1 - u) - formXA1 (coordY1 X u) u (coordSLo X u) := by
  have ha := formX_sLo_pos hX hu
  have hab := formX_sLo_le hX hu
  have hY : coordY1 X u - 1 ≠ 0 := by linarith [formX_Y1_lt_one hX hu.1.le]
  have hc : ContinuousOn (formXL1 (coordY1 X u) u) (uIcc (coordSLo X u) (1 - u)) := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have : s ≠ 0 := (ha.trans_le hs.1).ne'
    unfold formXL1
    exact (ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [this, hY])).continuousWithinAt
  rw [setIntegral_congr_fun measurableSet_Ioc (g := formXL1 (coordY1 X u) u)
    fun s hs => formXKin1_eq hX hu (ha.trans hs.1).ne']
  rw [← intervalIntegral.integral_of_le hab]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => ?_)
    (hc.intervalIntegrable)
  rw [uIcc_of_le hab] at hs
  exact hasDerivAt_formXA1 hY u (ha.trans_le hs.1).ne'

end

end QED.ChainProof.SetCK

end
