/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCG
public import QED.ChainProof.SetCKLi2Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the seven dilogarithm blocks of the `u`-antiderivative

Helper level (no frozen statement). The simple poles of the log coefficients of `J = formCJ X`
give seven terms `a log L/p` (`p ∈ {P, Q, M}` linear in `u`, `L` a log letter), each with
`a/p' = ±1/6`. With `w = 1 - L/L(u₀)` (`u₀` the zero of `p`) the antiderivative is
`(a/p')(log|L(u₀)| log p + Φ(w))`, `Φ` one of the three forms of `SetCKLi2Deriv` with its
`Li₂` argument in `(-1, 1)` on `0 < u < X < 1` (`K = formCK X`):

| block | term | `w` | form |
|---|---|---|---|
| `formCD1` | `((X - 1)/3) log(1 - u)/Q` | `Q/K` | direct |
| `formCD2` | `((1 - X)/6) log(1 - u)/M` | `M/K` | direct |
| `formCD3` | `((X - 1)/6) log(X - u)/M` | `M` (`= 1` at `u = X`) | direct |
| `formCD4` | `((X - 1)/6) log(X + u - Xu)/M` | `M/(1 - X)²` | inversion |
| `formCD5` | `((1 - X)/6) log P/M` | `M/(1 - X)` | inversion |
| `formCD6` | `((X - 1)/6) log M/P` | `-P/(1 - X)` | Landen |
| `formCD7` | `((1 - X)/3) log M/Q` | `-Q/K` | direct |

(`hasDerivAt_formCD1`, …, `hasDerivAt_formCD7`.)
-/

@[expose] public section

open Real Set QED.Polylog

namespace QED.ChainProof.SetCK

/-- Block 1: `((X - 1)/3) log(1 - u)/Q`. -/
noncomputable def formCD1 (X u : ℝ) : ℝ :=
  -1 / 6 * (log (formCK X / (2 * (1 - X))) * log (formCQ X u) + -Li₂ (formCQ X u / formCK X))

/-- Block 2: `((1 - X)/6) log(1 - u)/M`. -/
noncomputable def formCD2 (X u : ℝ) : ℝ :=
  1 / 6 * (log (formCK X / (1 - X)) * log (coordM X u) + -Li₂ (coordM X u / formCK X))

/-- Block 3: `((X - 1)/6) log(X - u)/M`. -/
noncomputable def formCD3 (X u : ℝ) : ℝ :=
  -1 / 6 * (-log (1 - X) * log (coordM X u) + -Li₂ (coordM X u))

/-- Block 4: `((X - 1)/6) log(X + u - Xu)/M`. -/
noncomputable def formCD4 (X u : ℝ) : ℝ :=
  -1 / 6 * (2 * log (1 - X) * log (coordM X u) +
    (Li₂ (1 / (coordM X u / (1 - X) ^ 2)) + log (coordM X u / (1 - X) ^ 2) ^ 2 / 2))

/-- Block 5: `((1 - X)/6) log P/M`. -/
noncomputable def formCD5 (X u : ℝ) : ℝ :=
  1 / 6 * (log (1 - X) * log (coordM X u) +
    (Li₂ (1 / (coordM X u / (1 - X))) + log (coordM X u / (1 - X)) ^ 2 / 2))

/-- Block 6: `((X - 1)/6) log M/P`. -/
noncomputable def formCD6 (X u : ℝ) : ℝ :=
  -1 / 6 * (log (1 - X) * log (formCP X u) +
    (Li₂ (-formCP X u / (1 - X) / (-formCP X u / (1 - X) - 1)) +
      log (1 - -formCP X u / (1 - X)) ^ 2 / 2))

/-- Block 7: `((1 - X)/3) log M/Q`. -/
noncomputable def formCD7 (X u : ℝ) : ℝ :=
  1 / 6 * (log (formCK X / 2) * log (formCQ X u) + -Li₂ (-formCQ X u / formCK X))

section deriv

variable {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X)
include hX hu

theorem formCD_facts : 0 < formCP X u ∧ 0 < formCQ X u ∧ 0 < coordM X u ∧ 0 < 1 - X ∧
    0 < 1 - u ∧ 0 < X - u ∧ 0 < X + u - X * u ∧ 0 < formCK X ∧
    formCQ X u < formCK X ∧ coordM X u < formCK X ∧ coordM X u < 1 := by
  obtain ⟨hP, hQ, hM⟩ := formC_pos_PQM hX hu
  obtain ⟨h0, h1⟩ := hX
  obtain ⟨hu0, huX⟩ := hu
  have h1X : 0 < 1 - X := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hXu : 0 < X - u := by linarith
  refine ⟨hP, hQ, hM, h1X, h1u, hXu, by nlinarith, by unfold formCK; nlinarith, ?_, ?_, ?_⟩
  · have : formCK X - formCQ X u = 2 * (1 - X) * (1 - u) := by unfold formCK formCQ; ring
    nlinarith [mul_pos h1X h1u]
  · have : formCK X - coordM X u = (1 - X) * (1 - u) := by unfold formCK coordM; ring
    nlinarith [mul_pos h1X h1u]
  · have : 1 - coordM X u = (1 - X) * (X - u) := by unfold coordM; ring
    nlinarith [mul_pos h1X hXu]

theorem hasDerivAt_formCD1 :
    HasDerivAt (formCD1 X) (((X - 1) / 3) / formCQ X u * log (1 - u)) u := by
  obtain ⟨hP, hQ, hM, h1X, h1u, hXu, hA, hK, hQK, hMK, hM1⟩ := formCD_facts hX hu
  have hw := (formC_hasDerivAt_Q X u).div_const (formCK X)
  have h := li2_hasDerivAt_neg hw (by rw [abs_of_pos (by positivity), div_lt_one hK]; exact hQK)
    (by positivity)
  have hl := (formC_hasDerivAt_Q X u).log hQ.ne'
  refine (((hl.const_mul (log (formCK X / (2 * (1 - X))))).add h).const_mul (-1 / 6)).congr_deriv
    ?_
  have e : 1 - formCQ X u / formCK X = 2 * (1 - X) * (1 - u) / formCK X := by
    field_simp; unfold formCK formCQ; ring
  rw [e, log_div (by positivity) hK.ne', log_mul (by positivity) h1u.ne',
    log_div hK.ne' (by positivity)]
  field_simp
  ring

theorem hasDerivAt_formCD2 :
    HasDerivAt (formCD2 X) (((1 - X) / 6) / coordM X u * log (1 - u)) u := by
  obtain ⟨hP, hQ, hM, h1X, h1u, hXu, hA, hK, hQK, hMK, hM1⟩ := formCD_facts hX hu
  have hw := (formC_hasDerivAt_M X u).div_const (formCK X)
  have h := li2_hasDerivAt_neg hw (by rw [abs_of_pos (by positivity), div_lt_one hK]; exact hMK)
    (by positivity)
  have hl := (formC_hasDerivAt_M X u).log hM.ne'
  refine (((hl.const_mul (log (formCK X / (1 - X)))).add h).const_mul (1 / 6)).congr_deriv ?_
  have e : 1 - coordM X u / formCK X = (1 - X) * (1 - u) / formCK X := by
    field_simp; unfold formCK coordM; ring
  rw [e, log_div (by positivity) hK.ne', log_mul h1X.ne' h1u.ne', log_div hK.ne' h1X.ne']
  field_simp
  ring

theorem hasDerivAt_formCD3 :
    HasDerivAt (formCD3 X) (((X - 1) / 6) / coordM X u * log (X - u)) u := by
  obtain ⟨hP, hQ, hM, h1X, h1u, hXu, hA, hK, hQK, hMK, hM1⟩ := formCD_facts hX hu
  have h := li2_hasDerivAt_neg (formC_hasDerivAt_M X u) (by rw [abs_of_pos hM]; exact hM1)
    hM.ne'
  have hl := (formC_hasDerivAt_M X u).log hM.ne'
  refine (((hl.const_mul (-log (1 - X))).add h).const_mul (-1 / 6)).congr_deriv ?_
  have e : 1 - coordM X u = (1 - X) * (X - u) := by unfold coordM; ring
  rw [e, log_mul h1X.ne' hXu.ne']
  field_simp
  ring

theorem hasDerivAt_formCD4 :
    HasDerivAt (formCD4 X) (((X - 1) / 6) / coordM X u * log (X + u - X * u)) u := by
  obtain ⟨hP, hQ, hM, h1X, h1u, hXu, hA, hK, hQK, hMK, hM1⟩ := formCD_facts hX hu
  have hw := (formC_hasDerivAt_M X u).div_const ((1 - X) ^ 2)
  have hw1 : 1 < coordM X u / (1 - X) ^ 2 := by
    rw [one_lt_div (by positivity)]
    have : coordM X u - (1 - X) ^ 2 = X + u - X * u := by unfold coordM; ring
    linarith
  have h := li2_hasDerivAt_inv hw hw1
  have hl := (formC_hasDerivAt_M X u).log hM.ne'
  refine (((hl.const_mul (2 * log (1 - X))).add h).const_mul (-1 / 6)).congr_deriv ?_
  have e : coordM X u / (1 - X) ^ 2 - 1 = (X + u - X * u) / (1 - X) ^ 2 := by
    field_simp; unfold coordM; ring
  rw [e, log_div hA.ne' (by positivity), log_pow]
  push_cast
  field_simp
  ring

theorem hasDerivAt_formCD5 :
    HasDerivAt (formCD5 X) (((1 - X) / 6) / coordM X u * log (formCP X u)) u := by
  obtain ⟨hP, hQ, hM, h1X, h1u, hXu, hA, hK, hQK, hMK, hM1⟩ := formCD_facts hX hu
  have hw := (formC_hasDerivAt_M X u).div_const (1 - X)
  have hw1 : 1 < coordM X u / (1 - X) := by
    rw [one_lt_div h1X]
    have : coordM X u - (1 - X) = formCP X u := by unfold coordM formCP; ring
    linarith
  have h := li2_hasDerivAt_inv hw hw1
  have hl := (formC_hasDerivAt_M X u).log hM.ne'
  refine (((hl.const_mul (log (1 - X))).add h).const_mul (1 / 6)).congr_deriv ?_
  have e : coordM X u / (1 - X) - 1 = formCP X u / (1 - X) := by
    field_simp; unfold coordM formCP; ring
  rw [e, log_div hP.ne' h1X.ne']
  field_simp
  ring

theorem hasDerivAt_formCD6 :
    HasDerivAt (formCD6 X) (((X - 1) / 6) / formCP X u * log (coordM X u)) u := by
  obtain ⟨hP, hQ, hM, h1X, h1u, hXu, hA, hK, hQK, hMK, hM1⟩ := formCD_facts hX hu
  have hw := (formC_hasDerivAt_P X u).neg.div_const (1 - X)
  have hw0 : -formCP X u / (1 - X) < 0 := div_neg_of_neg_of_pos (by linarith) h1X
  have h := li2_hasDerivAt_landen hw hw0
  have hl := (formC_hasDerivAt_P X u).log hP.ne'
  refine (((hl.const_mul (log (1 - X))).add h).const_mul (-1 / 6)).congr_deriv ?_
  have e : 1 - -formCP X u / (1 - X) = coordM X u / (1 - X) := by
    field_simp; unfold coordM formCP; ring
  simp only [Pi.neg_apply]
  rw [e, log_div hM.ne' h1X.ne']
  field_simp
  ring

theorem hasDerivAt_formCD7 :
    HasDerivAt (formCD7 X) (((1 - X) / 3) / formCQ X u * log (coordM X u)) u := by
  obtain ⟨hP, hQ, hM, h1X, h1u, hXu, hA, hK, hQK, hMK, hM1⟩ := formCD_facts hX hu
  have hw := (formC_hasDerivAt_Q X u).neg.div_const (formCK X)
  have h := li2_hasDerivAt_neg hw
    (by
      rw [abs_lt, lt_div_iff₀ hK, div_lt_iff₀ hK]
      simp only [Pi.neg_apply]
      constructor <;> linarith)
    (div_ne_zero (neg_ne_zero.2 hQ.ne') hK.ne')
  have hl := (formC_hasDerivAt_Q X u).log hQ.ne'
  refine (((hl.const_mul (log (formCK X / 2))).add h).const_mul (1 / 6)).congr_deriv ?_
  have e : 1 - -formCQ X u / formCK X = 2 * coordM X u / formCK X := by
    field_simp; unfold formCK formCQ coordM; ring
  simp only [Pi.neg_apply]
  rw [e, log_div (by positivity) hK.ne', log_mul (by norm_num) hM.ne',
    log_div hK.ne' (by norm_num)]
  field_simp
  ring

end deriv

end QED.ChainProof.SetCK

end
