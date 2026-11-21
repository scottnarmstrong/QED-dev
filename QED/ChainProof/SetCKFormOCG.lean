/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCNC
public import QED.ChainProof.SetCKFormOCLCF

/-!
# Set (c), Stage K, closed forms: the `a`-integrand `G = f + Q′ N - ℓ_a` in letters

Helper level (no frozen statement). Item 5 of the `ρ_oC` route (Stage K notes, Session 30+).
With `ℓ_a` in letters (`formOCellC`, `SetCKFormOCLCF`), **`formOCG`** is
`G` in letters (`log a` and `log X` share one coefficient; the `(2a - 1)` and `(a - 1)` poles of
`N` and `ℓ_a` cancel). **`formOCG_eq`**: for `a ∈ (0, 1)`, `a ≠ 1/2`, `X ∈ (0, 1)`,
`f(a, X) + Q′(X) N(a, X) - ℓ_a(a, X) = G(a, X)` (`formOCf`, `setCKdQ`, `formOCN`).
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

/-- `G` in letters: rational part. -/
noncomputable def formOCGcRat (a X : ℝ) : ℝ :=
  (X^7*a^5/4 + 5*X^7*a^4/24 - 7*X^7*a^3/24 - X^7*a^2/2 - X^6*a^5/2 - 7*X^6*a^4/8 + 11*X^6*a^3/24
    + 29*X^6*a^2/8 - X^6*a/6 + 5*X^5*a^4/4 + X^5*a^3/2 - 53*X^5*a^2/6 - X^5*a/4 + X^5/3
    - 2*X^4*a^4/3 - 2*X^4*a^3/3 + 211*X^4*a^2/24 + 5*X^4*a/2 - 4*X^4/3 + X^3*a^3/3
    - 49*X^3*a^2/12 - 13*X^3*a/4 + 5*X^3/3 + 2*X^2*a^2/3 + 7*X^2*a/6 - 2*X^2/3) /
    ((1 - X) ^ 3 * (1 - a * X) * (1 - X + a * X) * a ^ 2)

/-- `G` in letters: coefficient of `log a + log X`. -/
noncomputable def formOCGcA (a X : ℝ) : ℝ :=
  (-X^8*a^4/4 - X^8*a^3/3 + X^8*a/3 + X^7*a^4/2 + 3*X^7*a^3/2 + 7*X^7*a^2/6 - 7*X^7*a/6 - 2*X^7/3
    - 2*X^6*a^3 - 15*X^6*a^2/4 + 35*X^6/12 + 2*X^5*a^3/3 + 7*X^5*a^2/2 + 11*X^5*a/3 - 29*X^5/6
    - 4*X^4*a^2/3 - 23*X^4*a/6 + 43*X^4/12 + X^3*a - X^3) /
    ((1 - X) ^ 4 * (1 - a * X) ^ 2)

/-- `G` in letters: coefficient of `log (2 - X)`. -/
noncomputable def formOCGc2X (a X : ℝ) : ℝ :=
  (-2*X^10*a^2/3 + X^10*a/3 + 7*X^9*a^2/2 - X^9*a/2 - 2*X^9/3 - 7*X^8*a^2 - 9*X^8*a/2 + 17*X^8/4
    + 17*X^7*a^2/3 + 56*X^7*a/3 - 34*X^7/3 + X^6*a^2/2 - 31*X^6*a + 193*X^6/12 - 4*X^5*a^2
    + 26*X^5*a - 25*X^5/2 + 4*X^4*a^2/3 - 26*X^4*a/3 + 25*X^4/6) /
    ((1 - X) ^ 4 * (1 - a * X) ^ 2 * (1 - X + a * X) ^ 2)

/-- `G` in letters: coefficient of `log (1 - a X)`. -/
noncomputable def formOCGcaX (a X : ℝ) : ℝ :=
  (X^5*a^5/4 - X^5*a^4/2 - 5*X^5*a^3/12 + X^5*a^2/3 - X^4*a^5/4 + X^4*a^4 + 3*X^4*a^3/4
    - 5*X^4*a^2/6 - X^3*a^4/2 + X^3*a^3/4 - X^3*a^2 + 5*X^3*a/4 - X^3/3 - 11*X^2*a^3/12
    + 17*X^2*a^2/6 - 37*X^2*a/12 + X^2 - X*a^2/3 + 7*X*a/6 - 2*X/3) /
    ((1 - X) * (1 - X + a * X) ^ 2 * a ^ 3)

/-- `G` in letters: coefficient of `log (1 - X + a X)`. -/
noncomputable def formOCGcbX (a X : ℝ) : ℝ :=
  (X^8*a^4/4 + X^8*a^3/3 - X^8*a^2/4 - X^8*a/3 - X^7*a^4/2 - 3*X^7*a^3/2 - X^7*a^2/6 + 5*X^7*a/3
    + 2*X^7/3 + 2*X^6*a^3 + 9*X^6*a^2/4 - 2*X^6*a - 19*X^6/6 - 2*X^5*a^3/3 - 5*X^5*a^2/2
    - 2*X^5*a/3 + 35*X^5/6 + 13*X^4*a^2/12 + 11*X^4*a/6 - 61*X^4/12 - X^3*a/2 + 2*X^3 - X^2/4) /
    ((1 - X) ^ 4 * (1 - a * X) ^ 2)

/-- **`G = f + Q′ N - ℓ_a` in letters.** -/
noncomputable def formOCG (a X : ℝ) : ℝ :=
  formOCGcRat a X + formOCGcA a X * (log a + log X) + X ^ 2 / 4 * log (1 - X) +
    formOCGc2X a X * log (2 - X) + formOCGcaX a X * log (1 - a * X) +
    formOCGcbX a X * log (1 - X + a * X)

section

variable {a X : ℝ}

theorem formOCG_rat_eq (ha0 : a ≠ 0) (ha1 : a - 1 ≠ 0) (h2a : 2 * a - 1 ≠ 0)
    (hX0 : X ≠ 0) (hX1 : 1 - X ≠ 0) (h2X : 2 - X ≠ 0) (hL : 1 - a * X ≠ 0)
    (hM : 1 - X + a * X ≠ 0) :
    formOCfR a X + X ^ 2 / 4 + setCKdQ X * formOCNCrat a X - formOCellCR a X =
      formOCGcRat a X := by
  simp only [setCKdQ, formOCfR, formOCNCrat, formOCellCR, formOCGcRat]
  have hL' : a * X - 1 ≠ 0 := fun h => hL (by linarith)
  have hM' : a * X - X + 1 ≠ 0 := fun h => hM (by linarith)
  generalize hL2 : a * X - 1 = L2 at *
  generalize hM2 : a * X - X + 1 = M2 at *
  have hL3 : X * a - 1 ≠ 0 := fun h => hL (by linarith)
  have hM3 : X * a - X + 1 ≠ 0 := fun h => hM (by linarith)
  have hXm : X - 1 ≠ 0 := fun h => hX1 (by linarith)
  generalize hL3g : X * a - 1 = L3 at *
  generalize hM3g : X * a - X + 1 = M3 at *
  generalize hXmg : X - 1 = Xm at *
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  generalize hTg : 2 - X = Tg at *
  field_simp
  subst hL2 hM2 hL3g hM3g hXmg hLg hMg hAg hTg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCG_a_eq (h2a : 2 * a - 1 ≠ 0) (hX0 : X ≠ 0) (hX1 : 1 - X ≠ 0)
    (h2X : 2 - X ≠ 0) (hL : 1 - a * X ≠ 0) (hM : 1 - X + a * X ≠ 0) :
    -(-X ^ 4 / (4 * ((1 - a * X) * (1 - X + a * X)))) + setCKdQ X * formOCNCa a X =
      formOCGcA a X := by
  simp only [setCKdQ, formOCNCa, formOCGcA]
  have hL3 : X * a - 1 ≠ 0 := fun h => hL (by linarith)
  have hM3 : X * a - X + 1 ≠ 0 := fun h => hM (by linarith)
  have hXm : X - 1 ≠ 0 := fun h => hX1 (by linarith)
  generalize hL3g : X * a - 1 = L3 at *
  generalize hM3g : X * a - X + 1 = M3 at *
  generalize hXmg : X - 1 = Xm at *
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  generalize hTg : 2 - X = Tg at *
  field_simp
  subst hL3g hM3g hXmg hLg hMg hAg hTg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCG_X_eq (h2a : 2 * a - 1 ≠ 0) (hX0 : X ≠ 0) (hX1 : 1 - X ≠ 0)
    (h2X : 2 - X ≠ 0) (hL : 1 - a * X ≠ 0) (hM : 1 - X + a * X ≠ 0) :
    (-X ^ 4 / (4 * ((1 - a * X) * (1 - X + a * X)))) + setCKdQ X * formOCNCa a X - formOCellCX a X =
      formOCGcA a X := by
  simp only [setCKdQ, formOCNCa, formOCellCX, formOCGcA]
  have hL3 : X * a - 1 ≠ 0 := fun h => hL (by linarith)
  have hM3 : X * a - X + 1 ≠ 0 := fun h => hM (by linarith)
  have hXm : X - 1 ≠ 0 := fun h => hX1 (by linarith)
  generalize hL3g : X * a - 1 = L3 at *
  generalize hM3g : X * a - X + 1 = M3 at *
  generalize hXmg : X - 1 = Xm at *
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  generalize hTg : 2 - X = Tg at *
  field_simp
  subst hL3g hM3g hXmg hLg hMg hAg hTg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCG_1X_eq (h2a : 2 * a - 1 ≠ 0) (hX0 : X ≠ 0) (hX1 : 1 - X ≠ 0)
    (h2X : 2 - X ≠ 0) (hL : 1 - a * X ≠ 0) (hM : 1 - X + a * X ≠ 0) :
    -(2 * (-X ^ 4 / (4 * ((1 - a * X) * (1 - X + a * X))))) + X ^ 2 / 4 - (-formOCellCX a X) =
      X ^ 2 / 4 := by
  simp only [formOCellCX]
  have hL3 : X * a - 1 ≠ 0 := fun h => hL (by linarith)
  have hM3 : X * a - X + 1 ≠ 0 := fun h => hM (by linarith)
  have hXm : X - 1 ≠ 0 := fun h => hX1 (by linarith)
  generalize hL3g : X * a - 1 = L3 at *
  generalize hM3g : X * a - X + 1 = M3 at *
  generalize hXmg : X - 1 = Xm at *
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  generalize hTg : 2 - X = Tg at *
  field_simp
  subst hL3g hM3g hXmg hLg hMg hAg hTg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCG_2X_eq (h2a : 2 * a - 1 ≠ 0) (hX0 : X ≠ 0) (hX1 : 1 - X ≠ 0)
    (h2X : 2 - X ≠ 0) (hL : 1 - a * X ≠ 0) (hM : 1 - X + a * X ≠ 0) :
    setCKdQ X * formOCNC2X a X - formOCellC2 a X =
      formOCGc2X a X := by
  simp only [setCKdQ, formOCNC2X, formOCellC2, formOCGc2X]
  have hL3 : X * a - 1 ≠ 0 := fun h => hL (by linarith)
  have hM3 : X * a - X + 1 ≠ 0 := fun h => hM (by linarith)
  have hXm : X - 1 ≠ 0 := fun h => hX1 (by linarith)
  generalize hL3g : X * a - 1 = L3 at *
  generalize hM3g : X * a - X + 1 = M3 at *
  generalize hXmg : X - 1 = Xm at *
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  generalize hTg : 2 - X = Tg at *
  field_simp
  subst hL3g hM3g hXmg hLg hMg hAg hTg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCG_aX_eq (ha0 : a ≠ 0) (h2a : 2 * a - 1 ≠ 0) (hX0 : X ≠ 0)
    (hX1 : 1 - X ≠ 0) (h2X : 2 - X ≠ 0) (hL : 1 - a * X ≠ 0) (hM : 1 - X + a * X ≠ 0) :
    (-X ^ 4 / (4 * ((1 - a * X) * (1 - X + a * X)))) - X ^ 2 / 4 + setCKdQ X * formOCNCaX a X
      - formOCellCL a X =
      formOCGcaX a X := by
  simp only [setCKdQ, formOCNCaX, formOCellCL, formOCGcaX]
  have hL3 : X * a - 1 ≠ 0 := fun h => hL (by linarith)
  have hM3 : X * a - X + 1 ≠ 0 := fun h => hM (by linarith)
  have hXm : X - 1 ≠ 0 := fun h => hX1 (by linarith)
  generalize hL3g : X * a - 1 = L3 at *
  generalize hM3g : X * a - X + 1 = M3 at *
  generalize hXmg : X - 1 = Xm at *
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  generalize hTg : 2 - X = Tg at *
  field_simp
  subst hL3g hM3g hXmg hLg hMg hAg hTg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOCG_bX_eq (ha1 : a - 1 ≠ 0) (h2a : 2 * a - 1 ≠ 0) (hX0 : X ≠ 0)
    (hX1 : 1 - X ≠ 0) (h2X : 2 - X ≠ 0) (hL : 1 - a * X ≠ 0) (hM : 1 - X + a * X ≠ 0) :
    (-X ^ 4 / (4 * ((1 - a * X) * (1 - X + a * X)))) - X ^ 2 / 4 + setCKdQ X * formOCNCbX a X
      - formOCellCM a X =
      formOCGcbX a X := by
  simp only [setCKdQ, formOCNCbX, formOCellCM, formOCGcbX]
  have hL3 : X * a - 1 ≠ 0 := fun h => hL (by linarith)
  have hM3 : X * a - X + 1 ≠ 0 := fun h => hM (by linarith)
  have hXm : X - 1 ≠ 0 := fun h => hX1 (by linarith)
  generalize hL3g : X * a - 1 = L3 at *
  generalize hM3g : X * a - X + 1 = M3 at *
  generalize hXmg : X - 1 = Xm at *
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hOg : 1 - X = Og at *
  generalize hAg : 2 * a - 1 = Ag at *
  generalize hTg : 2 - X = Tg at *
  field_simp
  subst hL3g hM3g hXmg hLg hMg hAg hTg
  obtain rfl : X = 1 - Og := by rw [← hOg]; ring
  ring

/-- **`f + Q′ N - ℓ_a = G`.** -/
theorem formOCG_eq (ha : a ∈ Ioo (0 : ℝ) 1) (h2a : 2 * a - 1 ≠ 0) (hX : X ∈ Ioo (0 : ℝ) 1) :
    formOCf a X + setCKdQ X * formOCN a X - formOCellC a X = formOCG a X := by
  have ha0 : a ≠ 0 := ha.1.ne'
  have ha1 : a - 1 ≠ 0 := by linarith [ha.2]
  have hX0 : X ≠ 0 := hX.1.ne'
  have hX1 : 1 - X ≠ 0 := by linarith [hX.2]
  have h2X : 2 - X ≠ 0 := by linarith [hX.2]
  have hL : 1 - a * X ≠ 0 := by nlinarith [ha.1, ha.2, hX.1, hX.2]
  have hM : 1 - X + a * X ≠ 0 := by nlinarith [ha.1, ha.2, hX.1, hX.2]
  have e1 := formOCG_rat_eq ha0 ha1 h2a hX0 hX1 h2X hL hM
  have e2 := formOCG_a_eq h2a hX0 hX1 h2X hL hM
  have e3 := formOCG_X_eq h2a hX0 hX1 h2X hL hM
  have e4 := formOCG_1X_eq h2a hX0 hX1 h2X hL hM
  have e5 := formOCG_2X_eq h2a hX0 hX1 h2X hL hM
  have e6 := formOCG_aX_eq ha0 h2a hX0 hX1 h2X hL hM
  have e7 := formOCG_bX_eq ha1 h2a hX0 hX1 h2X hL hM
  rw [formOCN_eq_NC ha h2a hX, formOCf_eq ha hX, formOCbeta_eq (by linarith [hX.2])]
  unfold formOCNC formOCellC formOCG
  linear_combination e1 + log a * e2 + log X * e3 + log (1 - X) * e4 + log (2 - X) * e5 +
    log (1 - a * X) * e6 + log (1 - X + a * X) * e7

end

end QED.ChainProof.SetCK

end
