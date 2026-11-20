/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCB2PF
public import QED.ChainProof.SetCKFormCSig
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the `u`-integrand of `σ_C` in a fixed log basis

Helper level (no frozen statement). After both `s`-integrals the `u`-integrand of
`cornInSig_ae_eq_br` is

`J(u) = R(u) + (ℓ(u) - r₁(u)) log(1 - u) - ℓ(u) (log(X - u) + log(X + u - Xu) - log P)`
`  + c_X(u) log(1 - X) + c_M(u) log M`

(`formCJ`), `P = X² + (1 - X)u`, `M = X² + (1 - X)(1 + u)`, `Q = X² + 2(1 - X)u`, with every
coefficient written in partial fractions in `u` (poles only at the zeros of `P`, `Q`, `M`, `1 - u`;
generated in exact arithmetic, scratch `stageK/fcd/j5.py`, `j6.py`):

**`integral_formCF2`**: `∫_{(1-u, 1)} F₂ ds = A(1) - A(1 - u)` (`formCF2_eq_formCPF`,
`integral_formCPF`); **`formCJ_eq`**: for `0 < u < X < 1` the integrand equals `formCJ X u`;
**`cornInSig_ae_eq_formCJ`**: for a.e. `X`, `σ_C(X) = ∫_{(0, X)} J(u) du` (`J` integrable).

Each source of `J` (the branch-1 antiderivative and each partial-fraction coefficient of
`formCPFA` at `s = 1, 1 - u`) is put in partial fractions separately (`formCJ_src…`); the rational
part `formCJR` is kept as the signed sum of these blocks, and the log atoms are matched by one
`linear_combination`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

/-- `K = X² - 2X + 2`, the value of `M` at `u = 1`. -/
def formCK (X : ℝ) : ℝ := X ^ 2 - 2 * X + 2

/-- Partial fractions in `u` of the rational source `A1a`. -/
noncomputable def formCJRA1a (X u : ℝ) : ℝ :=
  (1 / 6) +
      ((X - 1) ^ 3 / (4 * formCK X ^ 3)) / (1 - u) +
      (-(2 * X ^ 8 - 18 * X ^ 7 + 78 * X ^ 6 - 208 * X ^ 5 + 375 * X ^ 4 - 468 * X ^ 3 + 394 * X
          ^ 2 - 204 * X + 51) / (12 * formCK X ^ 3)) / coordM X u +
      ((X - 1) ^ 2 * (2 * X ^ 4 - 8 * X ^ 3 + 13 * X ^ 2 - 10 * X + 5) / (12 * formCK X)) /
          coordM X u ^ 3 +
      (-(X - 1) * (X ^ 2 - X + 1) * (2 * X ^ 4 - 11 * X ^ 3 + 28 * X ^ 2 - 34 * X + 17) / (12 *
          formCK X ^ 2)) / coordM X u ^ 2

/-- Partial fractions in `u` of the rational source `A1b`. -/
noncomputable def formCJRA1b (X u : ℝ) : ℝ :=
  (1 / 6) +
      (-X ^ 4 / 12) / formCP X u ^ 2 +
      ((X - 1) ^ 3 / 12) / coordM X u ^ 3 +
      ((X ^ 4 - 5 * X ^ 3 + 10 * X ^ 2 - 10 * X + 5) / (12 * (X - 1))) / coordM X u +
      ((X - 1) * (X ^ 2 + 4 * X - 4) / 12) / coordM X u ^ 2 +
      (-X ^ 2 * (X ^ 2 - 3 * X + 3) / (12 * (X - 1))) / formCP X u

/-- Partial fractions in `u` of the rational source `Q0`. -/
noncomputable def formCJRQ0 (X u : ℝ) : ℝ :=
  ((3 * X ^ 2 - 7 * X + 7) / (12 * (X - 1))) +
      (X ^ 6 / 6) / formCP X u ^ 3 +
      (X ^ 2 / 12) / formCP X u +
      (u * (X ^ 2 - X + 1) / (2 * X ^ 2)) +
      (u ^ 2 * (X - 1) / (2 * X ^ 2)) +
      (-X ^ 4 * (3 * X ^ 2 - 4 * X + 4) / (12 * (X - 1))) / formCP X u ^ 2

/-- Partial fractions in `u` of the rational source `Q1`. -/
noncomputable def formCJRQ1 (X u : ℝ) : ℝ :=
  (-(X - 2) ^ 2 / (12 * (X - 1))) +
      (-X ^ 2 / 6) / formCP X u +
      (-u ^ 2 * (X - 1) / (4 * X ^ 2)) +
      (-u * (X ^ 2 - 3 * X + 3) / (6 * X ^ 2)) +
      (X ^ 4 * formCK X / (12 * (X - 1))) / formCP X u ^ 2

/-- Partial fractions in `u` of the rational source `R2`. -/
noncomputable def formCJRR2 (X u : ℝ) : ℝ :=
  (-u / 16) +
      (formCK X / (32 * (X - 1))) +
      (-(X - 1) ^ 3 / (2 * formCK X ^ 3)) / (1 - u) +
      (X ^ 4 * (X - 2) ^ 4 / (16 * formCK X ^ 2)) / formCQ X u ^ 2 +
      (X ^ 6 * (X - 2) ^ 4 / (32 * (X - 1) * formCK X)) / formCQ X u ^ 3 +
      (-X ^ 4 * (X - 2) ^ 2 * (X ^ 4 - 5 * X ^ 3 + 13 * X ^ 2 - 16 * X + 8) / (16 * (X - 1) *
          formCK X ^ 3)) / formCQ X u

/-- Partial fractions in `u` of the rational source `D2`. -/
noncomputable def formCJRD2 (X u : ℝ) : ℝ :=
  (-1 / 16) +
      (u / 16) +
      (-X ^ 6 / 3) / formCP X u ^ 3 +
      ((3 * X ^ 10 - 13 * X ^ 9 + 28 * X ^ 8 - 31 * X ^ 7 + 7 * X ^ 6 + 47 * X ^ 5 - 95 * X ^ 4
          + 104 * X ^ 3 - 71 * X ^ 2 + 30 * X - 6) / (12 * (X - 1) * formCK X ^ 3)) / coordM X u +
      (-X ^ 2 * (X ^ 2 + 3 * X - 3) / (4 * (X - 1))) / formCP X u +
      (X ^ 4 * (X ^ 2 - 6 * X + 6) / (12 * (X - 1))) / formCP X u ^ 2 +
      (X ^ 6 * (X - 2) ^ 4 / (16 * (X - 1) * formCK X)) / formCQ X u ^ 3 +
      (-X ^ 4 * (X - 2) ^ 4 * (11 * X ^ 2 - 10 * X + 10) / (96 * (X - 1) * formCK X ^ 2)) /
          formCQ X u ^ 2 +
      (-X ^ 2 * (X - 2) ^ 2 * (3 * X ^ 6 - 74 * X ^ 5 + 378 * X ^ 4 - 896 * X ^ 3 + 1168 * X ^ 2
          - 864 * X + 288) / (96 * (X - 1) * formCK X ^ 3)) / formCQ X u

/-- Partial fractions in `u` of the rational source `D3`. -/
noncomputable def formCJRD3 (X u : ℝ) : ℝ :=
  (-X ^ 2 / (32 * (X - 1))) +
      (X ^ 6 / 6) / formCP X u ^ 3 +
      (X ^ 2 * (2 * X ^ 2 + 11 * X - 11) / (12 * (X - 1))) / formCP X u +
      (-X ^ 4 * (X - 2) ^ 2 / (12 * (X - 1))) / formCP X u ^ 2 +
      (-X ^ 4 * (X - 2) ^ 6 / (32 * (X - 1) * formCK X ^ 2)) / formCQ X u ^ 2 +
      (-X ^ 4 * (2 * X ^ 6 - 8 * X ^ 5 + 17 * X ^ 4 - 23 * X ^ 3 + 24 * X ^ 2 - 15 * X + 5) /
          (12 * (X - 1) * formCK X ^ 3)) / coordM X u +
      (X ^ 2 * (X - 1) * (2 * X ^ 4 - 4 * X ^ 3 + 7 * X ^ 2 - 6 * X + 3) / (24 * formCK X ^ 2))
          / coordM X u ^ 2 +
      (X ^ 2 * (X - 2) ^ 4 * (7 * X ^ 4 - 42 * X ^ 3 + 86 * X ^ 2 - 88 * X + 44) / (48 * (X - 1)
          * formCK X ^ 3)) / formCQ X u

/-- Partial fractions in `u` of `(1 - Y) a₁/12` (branch-1 log coefficient). -/
noncomputable def formCJl (X u : ℝ) : ℝ :=
  ((X - 1) ^ 3 / 3) / coordM X u ^ 3 +
      (1 / 6 - X / 6) / coordM X u +
      (-(X - 1) * formCK X / 12) / coordM X u ^ 2

/-- Partial fractions in `u` of the coefficient `r₁` of `log s`. -/
noncomputable def formCJr1 (X u : ℝ) : ℝ :=
  (-u / 48) +
      (-(X - 4) * (3 * X - 4) / (192 * (X - 1))) +
      (1 / 3 - X / 3) / formCQ X u +
      (7 * X ^ 4 * (X - 2) ^ 4 / (96 * (X - 1))) / formCQ X u ^ 3 +
      (-3 * X ^ 6 * (X - 2) ^ 4 / (64 * (X - 1))) / formCQ X u ^ 4 +
      (-X ^ 2 * (X - 2) ^ 2 * (X ^ 2 - 8 * X + 8) / (96 * (X - 1))) / formCQ X u ^ 2

/-- Partial fractions in `u` of the coefficient of `log(1 - X)`. -/
noncomputable def formCJ1X (X u : ℝ) : ℝ :=
  (-(13 * X ^ 3 - 32 * X ^ 2 + 32 * X - 32) / (192 * X * (X - 1))) +
      (X / 3 - 1 / 3) / formCQ X u +
      (X ^ 6 / 6) / formCP X u ^ 3 +
      (1 / 6 - X / 6) / formCP X u +
      (u ^ 2 * (X - 1) ^ 2 / (2 * X ^ 3 * (X - 2))) +
      (-u * (23 * X - 32) / (48 * X)) +
      (-X ^ 2 * (X ^ 4 - X ^ 3 + 2 * X ^ 2 - 2 * X + 1) / (12 * (X - 1))) / formCP X u ^ 2 +
      (3 * X ^ 6 * (X - 2) ^ 4 / (64 * (X - 1))) / formCQ X u ^ 4 +
      (-7 * X ^ 4 * (X - 2) ^ 4 / (96 * (X - 1))) / formCQ X u ^ 3 +
      (X ^ 2 * (X - 2) ^ 2 * (X ^ 2 - 8 * X + 8) / (96 * (X - 1))) / formCQ X u ^ 2

/-- Partial fractions in `u` of the coefficient of `log M`. -/
noncomputable def formCJM (X u : ℝ) : ℝ :=
  (7 * u / 48) +
      (-(X - 4) * (3 * X - 4) / (192 * (X - 1))) +
      (X / 6 - 1 / 6) / formCP X u +
      (1 / 3 - X / 3) / formCQ X u +
      (-X ^ 6 / 6) / formCP X u ^ 3 +
      (7 * X ^ 4 * (X - 2) ^ 4 / (96 * (X - 1))) / formCQ X u ^ 3 +
      (-3 * X ^ 6 * (X - 2) ^ 4 / (64 * (X - 1))) / formCQ X u ^ 4 +
      (X ^ 2 * (X ^ 4 - X ^ 3 + 2 * X ^ 2 - 2 * X + 1) / (12 * (X - 1))) / formCP X u ^ 2 +
      (-X ^ 2 * (X - 2) ^ 2 * (X ^ 2 - 8 * X + 8) / (96 * (X - 1))) / formCQ X u ^ 2

theorem formCJ_srcA1a {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    (1 - coordY1 X u) / 12 * (formCa3 (coordY1 X u) * (1 - u) ^ 2 / 2 +
        formCa2 (coordY1 X u) u * (1 - u) - formCa0 (coordY1 X u) u / (1 - u)) =
      formCJRA1a X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  have hY : coordY1 X u = formCP X u / coordM X u := rfl
  simp only [hY, formCJRA1a, formCa0, formCa2, formCa3]
  field_simp
  simp only [formCP, coordM, formCK]
  ring

theorem formCJ_srcA1b {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    (1 - coordY1 X u) / 12 * (formCa3 (coordY1 X u) * coordSLo X u ^ 2 / 2 +
        formCa2 (coordY1 X u) u * coordSLo X u - formCa0 (coordY1 X u) u / coordSLo X u) =
      formCJRA1b X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  have hY : coordY1 X u = formCP X u / coordM X u := rfl
  have hS : coordSLo X u = (X - u) * (X + u - X * u) / formCP X u := rfl
  have h0 : formCa0 (coordY1 X u) u / coordSLo X u =
      3 * (coordY1 X u - 1) * formCP X u / coordM X u := by
    have hYu : formCP X u - u * coordM X u = (X - u) * (X + u - X * u) := by
      unfold formCP coordM
      ring
    have : formCP X u - u * coordM X u ≠ 0 := by
      rw [hYu]
      exact mul_ne_zero (by linarith) (by nlinarith)
    have e1 : coordY1 X u - u = (formCP X u - u * coordM X u) / coordM X u := by
      rw [hY]
      field_simp
    unfold formCa0
    rw [e1, hS, ← hYu]
    generalize formCP X u - u * coordM X u = Z at *
    field_simp
  rw [h0]
  simp only [hY, hS, formCJRA1b, formCa2, formCa3]
  field_simp
  simp only [formCP, coordM]
  ring

theorem formCJ_srcQ0 {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    formC2q0 X u * u =
      formCJRQ0 X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  simp only [formCJRQ0, formC2q0, formC2L, formC2Nq0]
  field_simp
  simp only [formCP]
  ring

theorem formCJ_srcQ1 {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    formC2q1 X u * (1 - (1 - u) ^ 2) / 2 =
      formCJRQ1 X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  simp only [formCJRQ1, formC2q1, formC2L, formC2Nq1]
  field_simp
  simp only [formCP, formCK]
  ring

theorem formCJ_srcR2 {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    -formC2r2 X u + formC2r2 X u / (1 - u) =
      formCJRR2 X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  simp only [formCJRR2, formC2r2, formC2L, formC2Nr2]
  field_simp
  simp only [formCQ, formCK]
  ring

theorem formCJ_srcD2 {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    formC2d2 X u / (formCP X u * ((1 - X) * u)) -
      formC2d2 X u / (formCP X u * (u * coordM X u)) =
      formCJRD2 X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  simp only [formCJRD2, formC2d2, formC2L, formC2Nd2]
  field_simp
  simp only [formCP, formCQ, coordM, formCK]
  ring

theorem formCJ_srcD3 {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    formC2d3 X u / (2 * formCP X u * ((1 - X) * u) ^ 2) -
      formC2d3 X u / (2 * formCP X u * (u * coordM X u) ^ 2) =
      formCJRD3 X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  simp only [formCJRD3, formC2d3, formC2L, formC2Nd3]
  field_simp
  simp only [formCP, formCQ, coordM, formCK]
  ring

theorem formCJ_srcCl {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    (1 - coordY1 X u) / 12 * formCa1 (coordY1 X u) u =
      formCJl X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  have hY : coordY1 X u = formCP X u / coordM X u := rfl
  simp only [hY, formCJl, formCa1]
  field_simp
  simp only [formCP, coordM, formCK]
  ring

theorem formCJ_srcR1 {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    formC2r1 X u =
      formCJr1 X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  simp only [formCJr1, formC2r1, formC2L, formC2Nr1]
  field_simp
  simp only [formCQ]
  ring

theorem formCJ_src1X {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    -formC2b X u / X - formC2c X u / X - formC2d1 X u / formCP X u =
      formCJ1X X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  simp only [formCJ1X, formC2d1, formC2L, formC2Nd1, formC2c, formC2Nc, formC2b, formC2Nb]
  field_simp
  simp only [formCP, formCQ]
  ring

theorem formCJ_srcM {X u : ℝ} (hX : 0 < X) (hX1 : X < 1) (hu : 0 < u) (huX : u < X) :
    formC2d1 X u / formCP X u =
      formCJM X u := by
  have := hX.ne'
  have : X - 1 ≠ 0 := by linarith
  have : X - 2 ≠ 0 := by linarith
  have : 1 - X ≠ 0 := by linarith
  have := hu.ne'
  have : 1 - u ≠ 0 := by linarith
  have : u - 1 ≠ 0 := by linarith
  have : X - u ≠ 0 := by linarith
  have := mul_pos (sub_pos.2 hX1) hu
  have : X ^ 2 + (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + 2 * (1 - X) * u ≠ 0 := by positivity
  have : X ^ 2 + (1 - X) * (1 + u) ≠ 0 := by nlinarith
  have : X + u - X * u ≠ 0 := by nlinarith
  have : X - X * u + u ≠ 0 := by nlinarith
  have : X ^ 2 - 2 * X + 2 ≠ 0 := by nlinarith [sq_nonneg (X - 1)]
  have : formCK X ≠ 0 := by unfold formCK; nlinarith [sq_nonneg (X - 1)]
  have : formCP X u ≠ 0 := by unfold formCP; positivity
  have : formCQ X u ≠ 0 := by unfold formCQ; positivity
  have : coordM X u ≠ 0 := by unfold coordM; nlinarith
  simp only [formCJM, formC2d1, formC2L, formC2Nd1]
  field_simp
  simp only [formCP, formCQ]
  ring

/-- **The rational part** `R(u)` of `J(u)`, as the sum of its sources. -/
noncomputable def formCJR (X u : ℝ) : ℝ :=
  formCJRA1a X u - formCJRA1b X u + formCJRQ0 X u + formCJRQ1 X u + formCJRR2 X u + formCJRD2 X
      u + formCJRD3 X u

/-- **The `u`-integrand `J(u)` in the fixed log basis** `log(1 - u)`, `log(X - u)`,
`log(X + u - Xu)`, `log P`, `log(1 - X)`, `log M`. -/
noncomputable def formCJ (X u : ℝ) : ℝ :=
  formCJR X u + (formCJl X u - formCJr1 X u) * log (1 - u) -
    formCJl X u * (log (X - u) + log (X + u - X * u) - log (formCP X u)) +
    formCJ1X X u * log (1 - X) + formCJM X u * log (coordM X u)

theorem formCJ_pos {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) {s : ℝ}
    (hs : s ∈ Icc (1 - u) 1) :
    0 < formCB X u s ∧ 0 < formCC X u s ∧ 0 < coordD X u s := by
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨hu0, huX⟩ := hu
  obtain ⟨hs1, hs2⟩ := hs
  have h1X : 0 < 1 - X := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold formCB
    nlinarith
  · unfold formCC
    nlinarith [mul_pos h1X hu0]
  · unfold coordD
    nlinarith [mul_pos h1X hu0, mul_nonneg (sq_nonneg X) (sub_nonneg.2 hs2)]

/-- The `s`-integral of the branch-2 integrand, by `formCF2_eq_formCPF` and `integral_formCPF`. -/
theorem integral_formCF2 {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) :
    ∫ s in Ioo (1 - u) 1, formCF2 X u s =
      formCPFA (formC2k X u) X u 1 - formCPFA (formC2k X u) X u (1 - u) := by
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨hu0, huX⟩ := hu
  have := mul_pos (sub_pos.2 hX1) hu0
  have hP : formCP X u ≠ 0 := by unfold formCP; positivity
  have hQ : formCQ X u ≠ 0 := by unfold formCQ; positivity
  rw [← integral_formCPF (formC2k X u) hX0.ne' hP (by linarith) (by linarith)
    (fun s hs => formCJ_pos ⟨hX0, hX1⟩ ⟨hu0, huX⟩ hs)]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  obtain ⟨hB, hC, hD⟩ := formCJ_pos ⟨hX0, hX1⟩ ⟨hu0, huX⟩ (Ioo_subset_Icc_self hs)
  exact formCF2_eq_formCPF hX0.ne' (by linarith) (by linarith) hP hQ
    (by linarith [hs.1]) hB.ne' hC.ne' hD.ne'

/-- **`J(u)` in closed form**: the `u`-integrand of `cornInSig_ae_eq_br` equals `formCJ`. -/
theorem formCJ_eq {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X) :
    formCA1 (coordY1 X u) u (1 - u) - formCA1 (coordY1 X u) u (coordSLo X u) +
      ∫ s in Ioo (1 - u) 1, formCF2 X u s = formCJ X u := by
  rw [integral_formCF2 hX hu]
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨hu0, huX⟩ := hu
  have h1X : 0 < 1 - X := by linarith
  have := mul_pos h1X hu0
  have hP : 0 < formCP X u := by unfold formCP; positivity
  have hM : 0 < coordM X u := by unfold coordM; nlinarith
  have hA : 0 < X + u - X * u := by nlinarith
  have eB1 : formCB X u 1 = u := by unfold formCB; ring
  have eB2 : formCB X u (1 - u) = u * (1 - X) := by unfold formCB; ring
  have eC1 : formCC X u 1 = u * (1 - X) := by unfold formCC; ring
  have eC2 : formCC X u (1 - u) = u := by unfold formCC; ring
  have eD1 : coordD X u 1 = u * (1 - X) := by unfold coordD; ring
  have eD2 : coordD X u (1 - u) = u * coordM X u := by unfold coordD coordM; ring
  have eL : log (coordSLo X u) =
      log (X - u) + log (X + u - X * u) - log (formCP X u) := by
    rw [coordSLo, ← formCP, log_div (mul_pos (by linarith) hA).ne' hP.ne', log_mul (by linarith)
        hA.ne']
  have eL1 : log (u * (1 - X)) = log u + log (1 - X) := log_mul hu0.ne' h1X.ne'
  have eL2 : log (u * coordM X u) = log u + log (coordM X u) := log_mul hu0.ne' hM.ne'
  unfold formCPFA formCA1 formCJ
  simp only [formC2k, eB1, eB2, eC1, eC2, eD1, eD2, eL, eL1, eL2, log_one]
  simp only [formCJR]
  linear_combination formCJ_srcA1a hX0 hX1 hu0 huX - formCJ_srcA1b hX0 hX1 hu0 huX +
    formCJ_srcQ0 hX0 hX1 hu0 huX + formCJ_srcQ1 hX0 hX1 hu0 huX +
    formCJ_srcR2 hX0 hX1 hu0 huX + formCJ_srcD2 hX0 hX1 hu0 huX +
    formCJ_srcD3 hX0 hX1 hu0 huX +
    (log (1 - u) - log (X - u) - log (X + u - X * u) + log (formCP X u)) *
      formCJ_srcCl hX0 hX1 hu0 huX -
    log (1 - u) * formCJ_srcR1 hX0 hX1 hu0 huX + log (1 - X) * formCJ_src1X hX0 hX1 hu0 huX +
    log (coordM X u) * formCJ_srcM hX0 hX1 hu0 huX

/-- **`σ_C` as a `u`-integral of the closed form `J`**, for almost every outer node. -/
theorem cornInSig_ae_eq_formCJ :
    ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (formCJ X) (Ioo 0 X) ∧ cornInSig X = ∫ u in Ioo 0 X, formCJ X u := by
  filter_upwards [cornInSig_ae_eq_br, ae_restrict_mem measurableSet_Ioo] with X hI hX
  have h : EqOn (fun u => formCA1 (coordY1 X u) u (1 - u) -
      formCA1 (coordY1 X u) u (coordSLo X u) + ∫ s in Ioo (1 - u) 1, formCF2 X u s)
      (formCJ X) (Ioo 0 X) := fun u hu => formCJ_eq hX hu
  exact ⟨hI.1.congr_fun h measurableSet_Ioo,
    hI.2.trans (setIntegral_congr_fun measurableSet_Ioo h)⟩

end QED.ChainProof.SetCK

end
