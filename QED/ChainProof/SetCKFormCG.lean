/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCJ
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the rational parts of the `u`-antiderivative of `J`

Helper level (no frozen statement). The `u`-antiderivative `G` of `J = formCJ X` (task 3 of the
`ρ_C` closed form, scratch `stageK/fce/`) is, per log letter `L` of `J`, `F_L log L` plus one
dilogarithm block for each simple pole of the coefficient of `log L`, plus a rational part `H`
and constant multiples of logarithms. This file holds the rational functions (`P`, `Q`, `M` as
in `SetCKFormCJ`; generated in exact arithmetic, `gen1.py`, and checked in sympy, `verify1.py`):

* `formCGm` (the `M`-part, `F_P = -F_A = formCGm`), `formCGq` (the `Q`-part), `formCGp` (the
  `P`-part);
* `formCFU`, `formCFV`, `formCFM`, `formCFX`: the coefficients of `log(1 - u)`, `log(X - u)`,
  `log M` and `log(1 - X)`; `formCFV` vanishes at `u = X` (`formCFV_eq`);
* `formCHr`: the rational part.

Each has an explicit `u`-derivative (`hasDerivAt_formCGm`, …, `hasDerivAt_formCFX`; the
derivative of `formCHr` is in `SetCKFormCH`); the derivatives are stated so that, together with
the dilogarithm blocks (`SetCKFormCGD`), they add up to `J` (`SetCKFormCFTC`).
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

/-- The `M`-part of the log coefficients. -/
noncomputable def formCGm (X u : ℝ) : ℝ :=
  (-formCK X / 12) / coordM X u + ((X - 1) ^ 2 / 6) / coordM X u ^ 2

/-- The `Q`-part of the log coefficients. -/
noncomputable def formCGq (X u : ℝ) : ℝ :=
  (X ^ 2 * (X - 2) ^ 2 * (X ^ 2 - 8 * X + 8) / (192 * (X - 1) ^ 2)) / formCQ X u +
    (-7 * X ^ 4 * (X - 2) ^ 4 / (384 * (X - 1) ^ 2)) / formCQ X u ^ 2 +
    (X ^ 6 * (X - 2) ^ 4 / (128 * (X - 1) ^ 2)) / formCQ X u ^ 3

/-- The `P`-part of the log coefficients. -/
noncomputable def formCGp (X u : ℝ) : ℝ :=
  (-X ^ 2 * (X ^ 4 - X ^ 3 + 2 * X ^ 2 - 2 * X + 1) / (12 * (X - 1) ^ 2)) / formCP X u +
    (X ^ 6 / (12 * (X - 1))) / formCP X u ^ 2

/-- The linear coefficient `(X - 4)(3X - 4)/(192(X - 1))`. -/
noncomputable def formCc (X : ℝ) : ℝ := (X - 4) * (3 * X - 4) / (192 * (X - 1))

/-- The coefficient of `log(1 - u)`. -/
noncomputable def formCFU (X u : ℝ) : ℝ :=
  formCGm X u + u ^ 2 / 96 + formCc X * u + formCGq X u

/-- The coefficient of `log(X - u)`. -/
noncomputable def formCFV (X u : ℝ) : ℝ := -formCGm X u + X * (X - 2) / 12

/-- The coefficient of `log M`. -/
noncomputable def formCFM (X u : ℝ) : ℝ :=
  7 / 96 * u ^ 2 - formCc X * u - formCGp X u - formCGq X u

/-- The rational coefficient of `log(1 - X)`. -/
noncomputable def formCFX (X u : ℝ) : ℝ :=
  formCGp X u + formCGq X u - (23 * X - 32) / (96 * X) * u ^ 2 -
    (13 * X ^ 3 - 32 * X ^ 2 + 32 * X - 32) / (192 * X * (X - 1)) * u +
    (X - 1) ^ 2 / (6 * X ^ 3 * (X - 2)) * u ^ 3

/-- The rational part of the antiderivative. -/
noncomputable def formCHr (X u : ℝ) : ℝ :=
  ((X - 1) * (2 * X ^ 2 + 3 * X - 3) / (24 * formCK X)) / coordM X u +
    ((X - 1) * (X ^ 2 - X + 1) * (2 * X ^ 2 - 7 * X + 7) / (24 * formCK X)) / coordM X u ^ 2 +
    (-X ^ 4 * (X ^ 2 - X + 1) / (12 * (X - 1) ^ 2)) / formCP X u +
    (-7 * X ^ 4 * (X - 2) ^ 4 / (192 * (X - 1) ^ 2 * formCK X)) / formCQ X u +
    (X ^ 6 * (X - 2) ^ 4 / (64 * (X - 1) ^ 2 * formCK X)) / formCQ X u ^ 2 +
    (3 * X ^ 2 - 10 * X + 10) / (32 * (X - 1)) * u + 1 / 8 * u ^ 2 +
    (X - 1) / (12 * X ^ 2) * u ^ 3

/-- The constant coefficient of `log(1 - u)` in the rational part. -/
noncomputable def formChU (X : ℝ) : ℝ :=
  (X ^ 4 - 4 * X ^ 3 + 20 * X ^ 2 - 32 * X + 16) / (192 * (X - 1) ^ 2)

/-- The constant coefficient of `log M` in the rational part. -/
noncomputable def formChM (X : ℝ) : ℝ :=
  -(17 * X ^ 4 - 36 * X ^ 3 + 52 * X ^ 2 - 32 * X + 16) / (192 * (X - 1) ^ 2)

/-- The constant coefficient of `log P` in the rational part. -/
noncomputable def formChP (X : ℝ) : ℝ := -X ^ 2 * formCK X / (12 * (X - 1) ^ 2)

/-- The constant coefficient of `log(X + u - Xu)` in the rational part. -/
noncomputable def formChA (X : ℝ) : ℝ := -X * (X - 2) / (12 * (X - 1) ^ 2)

/-- The cofactor of `X - u` in `formCFV`. -/
noncomputable def formCFh (X u : ℝ) : ℝ :=
  (1 - X) * (-X ^ 4 + X ^ 3 * u + 3 * X ^ 3 - 3 * X ^ 2 * u - 5 * X ^ 2 + 2 * X * u + 6 * X - 2) /
    (12 * coordM X u ^ 2)

/-- `F_V` vanishes at `u = X`: `F_V = (X - u) F_h`. -/
theorem formCFV_eq {X u : ℝ} (hM : coordM X u ≠ 0) : formCFV X u = (X - u) * formCFh X u := by
  unfold formCFV formCGm formCFh formCK
  field_simp
  unfold coordM
  ring

section deriv

variable {X u : ℝ}

theorem formC_hasDerivAt_P (X u : ℝ) : HasDerivAt (formCP X) (1 - X) u :=
  (((hasDerivAt_id u).const_mul (1 - X)).const_add (X ^ 2)).congr_deriv (by simp)

theorem formC_hasDerivAt_Q (X u : ℝ) : HasDerivAt (formCQ X) (2 * (1 - X)) u :=
  (((hasDerivAt_id u).const_mul (2 * (1 - X))).const_add (X ^ 2)).congr_deriv (by simp)

theorem formC_hasDerivAt_M (X u : ℝ) : HasDerivAt (coordM X) (1 - X) u :=
  ((((hasDerivAt_id u).const_add 1).const_mul (1 - X)).const_add (X ^ 2)).congr_deriv
    (by simp)

/-- `(c/p)' = -c p'/p²`. -/
theorem formC_hasDerivAt_div {p : ℝ → ℝ} {p' : ℝ} (c : ℝ) (hp : HasDerivAt p p' u)
    (h : p u ≠ 0) : HasDerivAt (fun v => c / p v) (-(c * p') / p u ^ 2) u :=
  ((hasDerivAt_const u c).div hp h).congr_deriv (by ring)

/-- `(c/p^k)' = -k c p'/p^(k+1)`. -/
theorem formC_hasDerivAt_div_pow {p : ℝ → ℝ} {p' : ℝ} (c : ℝ) (k : ℕ) (hp : HasDerivAt p p' u)
    (h : p u ≠ 0) :
    HasDerivAt (fun v => c / p v ^ (k + 1)) (-((k + 1) * c * p') / p u ^ (k + 2)) u := by
  refine ((hasDerivAt_const u c).div (hp.pow (k + 1)) (pow_ne_zero _ h)).congr_deriv ?_
  have e : (p u ^ (k + 1)) ^ 2 = p u ^ k * p u ^ (k + 2) := by ring
  have hk : p u ^ k ≠ 0 := pow_ne_zero _ h
  simp only [Pi.pow_apply]
  rw [e, Nat.add_sub_cancel, mul_comm (p u ^ k)]
  push_cast
  field_simp
  ring

variable (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X)
include hX hu

theorem formC_pos_PQM : 0 < formCP X u ∧ 0 < formCQ X u ∧ 0 < coordM X u := by
  obtain ⟨h0, h1⟩ := hX
  obtain ⟨hu0, huX⟩ := hu
  have := mul_pos (sub_pos.2 h1) hu0
  refine ⟨?_, ?_, ?_⟩
  · unfold formCP; positivity
  · unfold formCQ; positivity
  · unfold coordM; nlinarith

theorem hasDerivAt_formCGm :
    HasDerivAt (formCGm X) (formCJl X u + ((X - 1) / 6) / coordM X u) u := by
  obtain ⟨hP, hQ, hM⟩ := formC_pos_PQM hX hu
  have h1 := formC_hasDerivAt_div (-formCK X / 12) (formC_hasDerivAt_M X u) hM.ne'
  have h2 := formC_hasDerivAt_div_pow ((X - 1) ^ 2 / 6) 1 (formC_hasDerivAt_M X u) hM.ne'
  refine (h1.add h2).congr_deriv ?_
  unfold formCJl
  field_simp
  ring

theorem hasDerivAt_formCGq :
    HasDerivAt (formCGq X) (-formCJr1 X u - u / 48 - formCc X + ((1 - X) / 3) / formCQ X u) u := by
  obtain ⟨hP, hQ, hM⟩ := formC_pos_PQM hX hu
  have hX1 : X - 1 ≠ 0 := by linarith [hX.2]
  have h1 := formC_hasDerivAt_div (X ^ 2 * (X - 2) ^ 2 * (X ^ 2 - 8 * X + 8) / (192 * (X - 1) ^ 2))
    (formC_hasDerivAt_Q X u) hQ.ne'
  have h2 := formC_hasDerivAt_div_pow (-7 * X ^ 4 * (X - 2) ^ 4 / (384 * (X - 1) ^ 2)) 1
    (formC_hasDerivAt_Q X u) hQ.ne'
  have h3 := formC_hasDerivAt_div_pow (X ^ 6 * (X - 2) ^ 4 / (128 * (X - 1) ^ 2)) 2
    (formC_hasDerivAt_Q X u) hQ.ne'
  refine ((h1.add h2).add h3).congr_deriv ?_
  unfold formCJr1 formCc
  field_simp
  ring

theorem hasDerivAt_formCGp :
    HasDerivAt (formCGp X) (formCJr1 X u - formCJM X u + u / 6 + ((X - 1) / 6) / formCP X u) u := by
  obtain ⟨hP, hQ, hM⟩ := formC_pos_PQM hX hu
  have hX1 : X - 1 ≠ 0 := by linarith [hX.2]
  have h1 := formC_hasDerivAt_div
    (-X ^ 2 * (X ^ 4 - X ^ 3 + 2 * X ^ 2 - 2 * X + 1) / (12 * (X - 1) ^ 2))
    (formC_hasDerivAt_P X u) hP.ne'
  have h2 := formC_hasDerivAt_div_pow (X ^ 6 / (12 * (X - 1))) 1
    (formC_hasDerivAt_P X u) hP.ne'
  refine (h1.add h2).congr_deriv ?_
  unfold formCJM formCJr1
  field_simp
  ring

theorem hasDerivAt_formCFU : HasDerivAt (formCFU X)
    (formCJl X u - formCJr1 X u - ((X - 1) / 3) / formCQ X u + ((X - 1) / 6) / coordM X u) u := by
  have h := (((hasDerivAt_formCGm hX hu).add ((hasDerivAt_pow 2 u).div_const 96)).add
    ((hasDerivAt_id u).const_mul (formCc X))).add (hasDerivAt_formCGq hX hu)
  refine h.congr_deriv ?_
  push_cast
  ring

theorem hasDerivAt_formCFV :
    HasDerivAt (formCFV X) (-formCJl X u - ((X - 1) / 6) / coordM X u) u :=
  ((hasDerivAt_formCGm hX hu).neg.add_const (X * (X - 2) / 12)).congr_deriv (by ring)

theorem hasDerivAt_formCFM : HasDerivAt (formCFM X)
    (formCJM X u - ((X - 1) / 6) / formCP X u + ((X - 1) / 3) / formCQ X u) u := by
  have h := ((((hasDerivAt_pow 2 u).const_mul (7 / 96)).sub
    ((hasDerivAt_id u).const_mul (formCc X))).sub (hasDerivAt_formCGp hX hu)).sub
    (hasDerivAt_formCGq hX hu)
  refine h.congr_deriv ?_
  push_cast
  ring

theorem hasDerivAt_formCFX : HasDerivAt (formCFX X)
    (formCJ1X X u - ((1 - X) / formCP X u - 2 * (1 - X) / formCQ X u) / 6) u := by
  obtain ⟨hP, hQ, hM⟩ := formC_pos_PQM hX hu
  have hX0 : X ≠ 0 := hX.1.ne'
  have hX1 : X - 1 ≠ 0 := by linarith [hX.2]
  have hX2 : X - 2 ≠ 0 := by linarith [hX.2]
  have h := (((((hasDerivAt_formCGp hX hu).add (hasDerivAt_formCGq hX hu)).sub
    ((hasDerivAt_pow 2 u).const_mul ((23 * X - 32) / (96 * X)))).sub
    ((hasDerivAt_id u).const_mul ((13 * X ^ 3 - 32 * X ^ 2 + 32 * X - 32) /
      (192 * X * (X - 1))))).add ((hasDerivAt_pow 3 u).const_mul
        ((X - 1) ^ 2 / (6 * X ^ 3 * (X - 2)))))
  refine h.congr_deriv ?_
  unfold formCJ1X formCJM formCJr1 formCc
  push_cast
  field_simp
  ring

end deriv

end QED.ChainProof.SetCK

end
