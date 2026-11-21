/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCNInt

/-!
# Set (c), Stage K, closed forms: `N(a, X)` in letters

Helper level (no frozen statement). Item 3 of the `ρ_oC` route (Stage K notes, Session 30+).
Evaluating the antiderivative `formOCNF` at `x = X` and `x = 0` (`Q = Q(X)`; the letter `X - x`
drops out at `x = X` since it enters as `(X - x) log(X - x)`) gives **`formOCNC`**:

`N = rat + c_a (log a + log X) + c₂ log(2 - X) + c_L log(1 - a X) + c_M log(1 - X + a X)`

(no `log(1 - X)`; scratch `stageK/foc5/g4.py`, `g5.py`, agreeing with `foc4/n4.pkl`), and
**`formOCN_eq_NC`**: `formOCN a X = formOCNC a X` for `a ∈ (0, 1)`, `a ≠ 1/2`, `X ∈ (0, 1)`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `N(a, X)`: rational part. -/
noncomputable def formOCNCrat (a X : ℝ) : ℝ :=
  (-X^6*a^6/4 + X^6*a^5 - 5*X^6*a^4/4 + X^6*a^3/2 - X^5*a^7/4 + 25*X^5*a^6/24 - 55*X^5*a^5/24
    + 65*X^5*a^4/24 - 35*X^5*a^3/24 + X^5*a^2/4 - 7*X^4*a^6/24 + 35*X^4*a^5/24 - 19*X^4*a^4/6
    + 79*X^4*a^3/24 - 4*X^4*a^2/3 + X^4*a/24 - X^3*a^6/12 + X^3*a^5/6 + 7*X^3*a^4/8 - 4*X^3*a^3/3
    - 25*X^3*a^2/24 + 7*X^3*a/4 - 7*X^3/12 - X^2*a^5/12 + X^2*a^4/6 - 17*X^2*a^3/12
    + 95*X^2*a^2/24 - 79*X^2*a/24 + 7*X^2/6 - X*a^4/6 + 11*X*a^3/12 - 23*X*a^2/12 + 3*X*a/2
    - 7*X/12) /
    ((1 - X) * (1 - a * X) * (1 - X + a * X) * a ^ 2 * (a - 1) ^ 2)

/-- `N(a, X)`: coefficient of `log a + log X`. -/
noncomputable def formOCNCa (a X : ℝ) : ℝ :=
  (X^7*a^5/4 + X^7*a^4/12 - X^7*a^3/3 - X^7*a^2/3 + X^7*a/12 - 7*X^6*a^4/12 + 5*X^6*a^2/3
    + X^6*a/3 - 5*X^6/12 + X^5*a^4/3 + X^5*a^3/4 - 19*X^5*a^2/12 - 31*X^5*a/12 + 7*X^5/4
    - X^4*a^3/3 + 5*X^4*a^2/12 + 13*X^4*a/3 - 11*X^4/4 - X^3*a^2/6 - 8*X^3*a/3 + 23*X^3/12
    + X^2*a/2 - X^2/2) /
    ((1 - X) ^ 2 * (1 - X + a * X) * (1 - a * X) ^ 2)

/-- `N(a, X)`: coefficient of `log (2 - X)`. -/
noncomputable def formOCNC2X (a X : ℝ) : ℝ :=
  (5*X^8*a^2/12 - X^8*a/12 - 5*X^7*a^2/3 - 2*X^7*a/3 + 5*X^7/12 + 13*X^6*a^2/6 + 14*X^6*a/3
    - 13*X^6/6 - X^5*a^2/3 - 31*X^5*a/3 + 9*X^5/2 - 5*X^4*a^2/3 + 65*X^4*a/6 - 55*X^4/12
    + 2*X^3*a^2/3 - 13*X^3*a/3 + 11*X^3/6) /
    ((1 - X) ^ 2 * (1 - a * X) ^ 2 * (1 - X + a * X) ^ 2)

/-- `N(a, X)`: coefficient of `log (1 - a X)`. -/
noncomputable def formOCNCaX (a X : ℝ) : ℝ :=
  (-5*X^4*a^4/6 + 7*X^4*a^3/12 - X^4*a^2/12 + 5*X^3*a^4/3 - 5*X^3*a^3/6 - X^3*a^2/2 + X^3*a/4
    - X^2*a^4/6 - 11*X^2*a^3/4 + 59*X^2*a^2/12 - 35*X^2*a/12 + 7*X^2/12 - 2*X*a^4/3 + 10*X*a^3/3
    - 17*X*a^2/3 + 25*X*a/6 - 7*X/6 - a^3/3 + 4*a^2/3 - 3*a/2 + 7/12) /
    ((2 * a - 1) * (1 - X + a * X) ^ 2 * a ^ 3)

/-- `N(a, X)`: coefficient of `log (1 - X + a X)`. -/
noncomputable def formOCNCbX (a X : ℝ) : ℝ :=
  (-X^6*a^8/2 + 13*X^6*a^7/12 + X^6*a^6/12 - 13*X^6*a^5/12 - 5*X^6*a^4/12 + 17*X^6*a^3/12
    - 2*X^6*a^2/3 + X^6*a/12 + 5*X^5*a^7/3 - 7*X^5*a^6/2 - 5*X^5*a^5/3 + 15*X^5*a^4/2
    - 10*X^5*a^3/3 - 7*X^5*a^2/3 + 25*X^5*a/12 - 5*X^5/12 - 2*X^4*a^7/3 - X^4*a^6/2
    + 59*X^4*a^5/12 + X^4*a^4/12 - 83*X^4*a^3/6 + 101*X^4*a^2/6 - 95*X^4*a/12 + 4*X^4/3
    + 4*X^3*a^6/3 - 4*X^3*a^5/3 - 9*X^3*a^4 + 64*X^3*a^3/3 - 62*X^3*a^2/3 + 35*X^3*a/4
    - 17*X^3/12 - X^2*a^5 + 9*X^2*a^4/2 - 15*X^2*a^3/2 + 31*X^2*a^2/4 - 11*X^2*a/4 + X^2/2
    - X*a^2/2 - X*a/2 + a/4) /
    ((1 - X) ^ 2 * (2 * a - 1) * (1 - a * X) ^ 2 * (a - 1) ^ 3)

/-- **`N(a, X)` in letters.** -/
noncomputable def formOCNC (a X : ℝ) : ℝ :=
  formOCNCrat a X + formOCNCa a X * (log a + log X) + formOCNC2X a X * log (2 - X) +
    formOCNCaX a X * log (1 - a * X) + formOCNCbX a X * log (1 - X + a * X)

theorem formOCN_pol_int (c : Fin 5 → ℝ) (z : ℝ) :
    formXPol (formOCNint c) z =
      c 0 * z + c 1 * z ^ 2 / 2 + c 2 * z ^ 3 / 3 + c 3 * z ^ 4 / 4 + c 4 * z ^ 5 / 5 := by
  simp [formXPol, formOCNint, Fin.sum_univ_succ]
  ring

section

variable {a X : ℝ}

theorem formOCN_D_eq (hX : X ≠ 1) :
    1 + a * (1 - a) * setCKQ X = (1 - a * X) * (1 - X + a * X) / (1 - X) := by
  have h : 1 - X ≠ 0 := sub_ne_zero.2 (Ne.symm hX)
  unfold setCKQ
  field_simp
  ring

theorem formOCNC_a_eq (h2a : 2 * a - 1 ≠ 0) (hX1 : 1 - X ≠ 0) (hL : 1 - a * X ≠ 0)
    (hM : 1 - X + a * X ≠ 0) :
    formXPol (formOCNcP a (setCKQ X)) X - formXPol (formOCNcP a (setCKQ X)) (-(a * setCKQ X)) -
      formOCNr3 a (setCKQ X) =
      formOCNCa a X := by
  simp only [formOCNcP, formOCN_pol_int, formOCNcR, Matrix.cons_val]
  simp only [formOCNr3, formOCNrT2E, formOCNrT3E, formOCNrT4E, formOCNrT5E, formOCNCa]
  rw [formOCN_D_eq (fun h => hX1 (by rw [h]; ring))]
  unfold setCKQ
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  field_simp
  subst hLg hMg hAg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCNC_2X_eq (h2a : 2 * a - 1 ≠ 0) (hX1 : 1 - X ≠ 0) (hL : 1 - a * X ≠ 0)
    (hM : 1 - X + a * X ≠ 0) :
    formXPol (formOCNcP a (setCKQ X)) X - formXPol (formOCNcP a (setCKQ X)) (formOCNrho X) =
      formOCNC2X a X := by
  simp only [formOCNcP, formOCN_pol_int, formOCNcR, Matrix.cons_val]
  simp only [formOCNC2X]
  rw [formOCN_D_eq (fun h => hX1 (by rw [h]; ring))]
  unfold setCKQ formOCNrho
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  field_simp
  subst hLg hMg hAg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCNC_aX_eq (ha0 : a ≠ 0) (h2a : 2 * a - 1 ≠ 0) (hX1 : 1 - X ≠ 0) (hL : 1 - a * X ≠ 0)
    (hM : 1 - X + a * X ≠ 0) :
    formXPol (formOCNcP a (setCKQ X)) (1 / a) - formXPol (formOCNcP a (setCKQ X)) X -
      formOCNr1 a (setCKQ X) / a =
      formOCNCaX a X := by
  simp only [formOCNcP, formOCN_pol_int, formOCNcR, Matrix.cons_val]
  simp only [formOCNr1, formOCNrT4L, formOCNCaX]
  rw [formOCN_D_eq (fun h => hX1 (by rw [h]; ring))]
  unfold setCKQ
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  field_simp
  subst hLg hMg hAg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCNC_bX_eq (ha1 : a - 1 ≠ 0)
    (h2a : 2 * a - 1 ≠ 0) (hX1 : 1 - X ≠ 0) (hL : 1 - a * X ≠ 0)
    (hM : 1 - X + a * X ≠ 0) :
    formXPol (formOCNcP a (setCKQ X)) (-(a * setCKQ X)) - formXPol (formOCNcP a (setCKQ X)) X +
      formOCNr3 a (setCKQ X) + formOCNr2 a (setCKQ X) / (a - 1) =
      formOCNCbX a X := by
  simp only [formOCNcP, formOCN_pol_int, formOCNcR, Matrix.cons_val]
  simp only [formOCNr3, formOCNrT2E, formOCNrT3E, formOCNrT4E, formOCNrT5E, formOCNr2, formOCNrT4M,
    formOCNCbX]
  rw [formOCN_D_eq (fun h => hX1 (by rw [h]; ring))]
  unfold setCKQ
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  field_simp
  subst hLg hMg hAg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCN_E_eq (hX : X ≠ 1) :
    X + a * setCKQ X = X * (1 - X + a * X) / (1 - X) := by
  have h : 1 - X ≠ 0 := sub_ne_zero.2 (Ne.symm hX)
  unfold setCKQ
  field_simp

theorem formOCNC_rat_eq (ha0 : a ≠ 0) (ha1 : a - 1 ≠ 0) (h2a : 2 * a - 1 ≠ 0) (hX0 : X ≠ 0)
    (hX1 : 1 - X ≠ 0) (hL : 1 - a * X ≠ 0) (hM : 1 - X + a * X ≠ 0) :
    formXPol (formOCNint (formOCNcd a (setCKQ X) X)) X -
        formOCNr4 a (setCKQ X) / (X + a * setCKQ X) + formOCNr4 a (setCKQ X) / (a * setCKQ X) =
      formOCNCrat a X := by
  have hX' : X ≠ 1 := fun h => hX1 (by rw [h]; ring)
  rw [formOCN_E_eq hX', formOCN_pol_int]
  simp only [formOCNcd, formOCNquo, formOCNcT, formOCNcP, formOCNint, formOCNcR, formOCNcT1,
    formOCNcT2, formOCNcT3, formOCNcT4, formOCNcT5, Matrix.cons_val, formOCNr4, formOCNrT2E2,
    formOCNrT3E2, formOCNrho, formOCNCrat]
  rw [formOCN_D_eq hX']
  unfold setCKQ
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  field_simp
  subst hLg hMg hAg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

/-- `F(X) - F(0)`, letter by letter. -/
theorem formOCNF_sub (ha : a ∈ Ioo (0 : ℝ) 1) (hX : X ∈ Ioo (0 : ℝ) 1) :
    formOCNF a (setCKQ X) X X - formOCNF a (setCKQ X) X 0 =
      (formXPol (formOCNint (formOCNcd a (setCKQ X) X)) X -
        formOCNr4 a (setCKQ X) / (X + a * setCKQ X) +
          formOCNr4 a (setCKQ X) / (a * setCKQ X)) +
      (formXPol (formOCNcP a (setCKQ X)) X -
        formXPol (formOCNcP a (setCKQ X)) (-(a * setCKQ X)) - formOCNr3 a (setCKQ X)) *
          (log a + log X) +
      (formXPol (formOCNcP a (setCKQ X)) X -
        formXPol (formOCNcP a (setCKQ X)) (formOCNrho X)) * log (2 - X) +
      (formXPol (formOCNcP a (setCKQ X)) (1 / a) - formXPol (formOCNcP a (setCKQ X)) X -
        formOCNr1 a (setCKQ X) / a) * log (1 - a * X) +
      (formXPol (formOCNcP a (setCKQ X)) (-(a * setCKQ X)) -
        formXPol (formOCNcP a (setCKQ X)) X + formOCNr3 a (setCKQ X) +
          formOCNr2 a (setCKQ X) / (a - 1)) * log (1 - X + a * X) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hX0, hX1⟩ := hX
  have h1X : 0 < 1 - X := by linarith
  have h2X : 0 < 2 - X := by linarith
  have hM : 0 < 1 - X + a * X := by nlinarith
  have hP0 : formXPol (formOCNcP a (setCKQ X)) 0 = 0 := by
    simp [formOCNcP, formOCN_pol_int]
  have hPol0 : formXPol (formOCNint (formOCNcd a (setCKQ X) X)) 0 = 0 := by
    simp [formOCN_pol_int]
  have hQX0 := formOCN_quo (formOCNcP a (setCKQ X)) X 0
  rw [hP0] at hQX0
  have eE : a * setCKQ X + 1 * X = X * (1 - X + a * X) / (1 - X) := by
    unfold setCKQ
    field_simp
    ring
  have eE0 : a * setCKQ X + 1 * 0 = a * X ^ 2 / (1 - X) := by
    unfold setCKQ
    ring
  unfold formOCNF
  rw [hPol0, hP0, show X + (1 - X) * X = X * (2 - X) by ring,
    show 1 + -a * X = 1 - a * X by ring, eE, show 1 + (a - 1) * X = 1 - X + a * X by ring,
    show X + (1 - X) * 0 = X by ring, show 1 + -a * 0 = 1 by ring, eE0,
    show 1 + (a - 1) * 0 = 1 by ring, sub_self, sub_zero, log_one, log_zero,
    log_mul hX0.ne' h2X.ne', log_div (mul_ne_zero hX0.ne' hM.ne') h1X.ne',
    log_mul hX0.ne' hM.ne', log_div (mul_ne_zero ha0.ne' (pow_ne_zero 2 hX0.ne')) h1X.ne',
    log_mul ha0.ne' (pow_ne_zero 2 hX0.ne'), log_pow]
  linear_combination (log X) * hQX0

/-- **`N(a, X)` in letters.** -/
theorem formOCN_eq_NC (ha : a ∈ Ioo (0 : ℝ) 1) (h2a : 2 * a - 1 ≠ 0) (hX : X ∈ Ioo (0 : ℝ) 1) :
    formOCN a X = formOCNC a X := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have ha1 : a - 1 ≠ 0 := by linarith [ha.2]
  have hX1 : 1 - X ≠ 0 := by linarith [hX.2]
  have hL : 1 - a * X ≠ 0 := by nlinarith [ha.1, ha.2, hX.1, hX.2]
  have hM : 1 - X + a * X ≠ 0 := by nlinarith [ha.1, ha.2, hX.1, hX.2]
  rw [(formOC_N_eq ha h2a hX).2, formOCNF_sub ha hX,
    formOCNC_rat_eq ha0 ha1 h2a hX.1.ne' hX1 hL hM, formOCNC_a_eq h2a hX1 hL hM,
    formOCNC_2X_eq h2a hX1 hL hM, formOCNC_aX_eq ha0 h2a hX1 hL hM,
    formOCNC_bX_eq ha1 h2a hX1 hL hM, formOCNC]


end

end QED.ChainProof.SetCK

end
