/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCG
public import QED.Polylog.Basic
import QED.Polylog.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Set (c), Stage K, closed forms: the `a`-antiderivative `𝒢` of `G`, coefficients

Helper level (no frozen statement). Item 5 of the `ρ_oC` route (Stage K notes). The
`a`-antiderivative of `G = formOCG` is
`𝒢 = c₀ + c_l log a + c_L log(1 - aX) + K (log a + log X) log(1 - aX) + c_M log(1 - X + aX)
  + c_x log X + (a X²/4) log(1 - X) + c_T log(2 - X)
  + K (2 Li₂(aX) - Li₂((1 - X + aX)/(2 - X)) + Li₂((1 - aX)/(2 - X)))`
(`formOCH` in `SetCKFormOCH2`). This file defines the coefficients (each a quartic in `a`,
`formOCHq`, over a product of the letters `a`, `1 - aX`, `1 - X + aX`) and proves the six
rational identities, one per letter, that make `∂_a 𝒢 = G` (`formOCH_letter_*`): each takes the
derivative of the coefficient as a hypothesis `HasDerivAt`.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

/-- A quartic in `a`. -/
noncomputable def formOCHq (c₀ c₁ c₂ c₃ c₄ a : ℝ) : ℝ :=
  c₀ + c₁ * a + c₂ * a ^ 2 + c₃ * a ^ 3 + c₄ * a ^ 4

/-- Its derivative. -/
noncomputable def formOCHqD (c₁ c₂ c₃ c₄ a : ℝ) : ℝ :=
  c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + 4 * c₄ * a ^ 3

theorem hasDerivAt_formOCHq (c₀ c₁ c₂ c₃ c₄ a : ℝ) :
    HasDerivAt (formOCHq c₀ c₁ c₂ c₃ c₄) (formOCHqD c₁ c₂ c₃ c₄ a) a := by
  have h := (((((hasDerivAt_id' a).const_mul c₁).const_add c₀).add
    ((hasDerivAt_pow 2 a).const_mul c₂)).add ((hasDerivAt_pow 3 a).const_mul c₃)).add
    ((hasDerivAt_pow 4 a).const_mul c₄)
  unfold formOCHq formOCHqD
  refine h.congr_deriv ?_
  push_cast
  ring

/-- The quotient rule for a quartic over a denominator. -/
theorem formOCH_hasDerivAt_div {c₀ c₁ c₂ c₃ c₄ a D' : ℝ} {D : ℝ → ℝ} (hD : HasDerivAt D D' a)
    (h : D a ≠ 0) :
    HasDerivAt (fun b => formOCHq c₀ c₁ c₂ c₃ c₄ b / D b)
      ((formOCHqD c₁ c₂ c₃ c₄ a * D a - formOCHq c₀ c₁ c₂ c₃ c₄ a * D') / D a ^ 2) a :=
  (hasDerivAt_formOCHq c₀ c₁ c₂ c₃ c₄ a).div hD h

/-- The common coefficient `K` of the dilogarithms. -/
noncomputable def formOCHK (X : ℝ) : ℝ :=
  X * (X - 2) * (2 * X ^ 4 - 3 * X ^ 3 + 2 * X ^ 2 + 2 * X - 1) / (6 * (X - 1) ^ 4)

/-- `𝒢` in letters: rational part. -/
noncomputable def formOCHc0 (a X : ℝ) : ℝ :=
  formOCHq
    (-X^2*(X - 2)/(6*(X - 1)^2))
    (0)
    (X^2*(17*X^3 - 51*X^2 + 50*X - 20)/(24*(X - 1)^3))
    (X^4*(X - 2)/(12*(X - 1)^3))
    (0)
    a / a

/-- `𝒢` in letters: coefficient of `log a`. -/
noncomputable def formOCHcl (a X : ℝ) : ℝ :=
  formOCHq
    (0)
    (-X^2*(4*X^5 - 21*X^4 + 42*X^3 - 39*X^2 + 22*X - 4)/(12*(X - 1)^4))
    (-X^3*(X - 2)*(2*X - 1)^2/(6*(X - 1)^4))
    (X^4*(X - 2)*(2*X^2 - 3*X + 2)/(12*(X - 1)^4))
    (X^6*(X - 2)/(12*(X - 1)^4))
    a / (1 - a * X)

/-- `𝒢` in letters: coefficient of `log (1 - a X)`. -/
noncomputable def formOCHcL (a X : ℝ) : ℝ :=
  formOCHq
    (X*(X - 2)/(6*(X - 1)))
    (-X*(X - 2)*(9*X - 7)/(12*(X - 1)^2))
    (-X*(2*X^6 - 20*X^5 + 63*X^4 - 79*X^3 + 27*X^2 + 13*X - 10)/(12*(X - 2)*(X - 1)^3))
    (X^2*(X^5 - 12*X^4 + 37*X^3 - 46*X^2 + 20*X - 4)/(12*(X - 2)*(X - 1)^3))
    (-X^3/4)
    a / (a ^ 2 * (1 - X + a * X))

/-- `𝒢` in letters: coefficient of `log (1 - X + a X)`. -/
noncomputable def formOCHcM (a X : ℝ) : ℝ :=
  formOCHq
    (X*(4*X^5 - 15*X^4 + 19*X^3 - 11*X^2 + 9*X - 2)/(12*(X - 2)*(X - 1)^3))
    (-X^2*(13*X^5 - 68*X^4 + 135*X^3 - 128*X^2 + 64*X - 12)/(12*(X - 2)*(X - 1)^4))
    (X^3*(3*X^4 - 4*X^3 - 6*X^2 + 6*X - 1)/(12*(X - 1)^4))
    (-X^4*(X - 2)*(2*X^2 - 3*X + 2)/(12*(X - 1)^4))
    (-X^6*(X - 2)/(12*(X - 1)^4))
    a / (1 - a * X)

/-- `𝒢` in letters: coefficient of `log X`. -/
noncomputable def formOCHcx (a X : ℝ) : ℝ :=
  formOCHq
    (-X*(4*X^5 - 21*X^4 + 48*X^3 - 57*X^2 + 34*X - 4)/(12*(X - 1)^4))
    (X^3*(X - 2)/(2*(X - 1)^3))
    (-X^3*(X - 2)*(2*X - 1)^2/(6*(X - 1)^4))
    (X^4*(X - 2)*(2*X^2 - 3*X + 2)/(12*(X - 1)^4))
    (X^6*(X - 2)/(12*(X - 1)^4))
    a / (1 - a * X)

/-- `𝒢` in letters: coefficient of `log (2 - X)`. -/
noncomputable def formOCHcT (a X : ℝ) : ℝ :=
  formOCHq
    (X^2*(8*X^4 - 41*X^3 + 89*X^2 - 96*X + 48)/(12*(X - 1)^3))
    (-X^2*(X^2 - 2*X + 2)*(X^4 - 3*X^3 + 2*X^2 + 2*X - 1)/(3*(X - 1)^4))
    (0)
    (0)
    (0)
    a / ((1 - a * X) * (1 - X + a * X))

section

variable {a X d : ℝ}

theorem formOCH_hasDerivAt_L (X a : ℝ) :
    HasDerivAt (fun b : ℝ => 1 - b * X) (-X) a := by
  simpa using ((hasDerivAt_id' a).mul_const X).const_sub 1

theorem formOCH_hasDerivAt_M (X a : ℝ) :
    HasDerivAt (fun b : ℝ => 1 - X + b * X) X a := by
  simpa using ((hasDerivAt_id' a).mul_const X).const_add (1 - X)

/-- The letter `1`. -/
theorem formOCH_letter_one (ha : a ≠ 0) (hX1 : X - 1 ≠ 0) (hX2 : X - 2 ≠ 0)
    (hL : 1 - a * X ≠ 0) (hM : 1 - X + a * X ≠ 0)
    (hd : HasDerivAt (fun b => formOCHc0 b X) d a) :
    d + formOCHcl a X / a - formOCHcL a X * X / (1 - a * X) +
      formOCHcM a X * X / (1 - X + a * X) = formOCGcRat a X := by
  rw [hd.unique (formOCH_hasDerivAt_div (hasDerivAt_id' a) ha)]
  simp only [formOCHcl, formOCHcL, formOCHcM, formOCGcRat, formOCHq, formOCHqD]
  have hO : 1 - X ≠ 0 := fun h => hX1 (by linarith)
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hXg : X - 1 = Xm at *
  generalize hTg : X - 2 = Xt at *
  generalize hOg : 1 - X = Og at *
  field_simp
  subst hLg hMg hXg hTg hOg
  ring

/-- The letter `log a`. -/
theorem formOCH_letter_log (hX1 : X - 1 ≠ 0) (hL : 1 - a * X ≠ 0)
    (hd : HasDerivAt (fun b => formOCHcl b X) d a) :
    d - formOCHK X * X / (1 - a * X) = formOCGcA a X := by
  rw [hd.unique (formOCH_hasDerivAt_div (formOCH_hasDerivAt_L X a) hL)]
  simp only [formOCHK, formOCGcA, formOCHq, formOCHqD]
  have hO : 1 - X ≠ 0 := fun h => hX1 (by linarith)
  generalize hLg : 1 - a * X = Lg at *
  generalize hXg : X - 1 = Xm at *
  generalize hOg : 1 - X = Og at *
  field_simp
  subst hLg hXg hOg
  ring

/-- The letter `log X`. -/
theorem formOCH_letter_X (hX1 : X - 1 ≠ 0) (hL : 1 - a * X ≠ 0)
    (hd : HasDerivAt (fun b => formOCHcx b X) d a) :
    d - formOCHK X * X / (1 - a * X) = formOCGcA a X := by
  rw [hd.unique (formOCH_hasDerivAt_div (formOCH_hasDerivAt_L X a) hL)]
  simp only [formOCHK, formOCGcA, formOCHq, formOCHqD]
  have hO : 1 - X ≠ 0 := fun h => hX1 (by linarith)
  generalize hLg : 1 - a * X = Lg at *
  generalize hXg : X - 1 = Xm at *
  generalize hOg : 1 - X = Og at *
  field_simp
  subst hLg hXg hOg
  ring

/-- The letter `log (1 - a X)`. -/
theorem formOCH_letter_L (ha : a ≠ 0) (hX1 : X - 1 ≠ 0) (hX2 : X - 2 ≠ 0)
    (hM : 1 - X + a * X ≠ 0) (hd : HasDerivAt (fun b => formOCHcL b X) d a) :
    d + formOCHK X / a - 2 * formOCHK X / a + formOCHK X * X / (1 - X + a * X) =
      formOCGcaX a X := by
  have hD : HasDerivAt (fun b : ℝ => b ^ 2 * (1 - X + b * X))
      (2 * a * (1 - X + a * X) + a ^ 2 * X) a := by
    refine ((hasDerivAt_pow 2 a).mul (formOCH_hasDerivAt_M X a)).congr_deriv ?_
    push_cast
    ring
  rw [hd.unique (formOCH_hasDerivAt_div hD (mul_ne_zero (pow_ne_zero 2 ha) hM))]
  simp only [formOCHK, formOCGcaX, formOCHq, formOCHqD]
  have hO : 1 - X ≠ 0 := fun h => hX1 (by linarith)
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hXg : X - 1 = Xm at *
  generalize hTg : X - 2 = Xt at *
  generalize hOg : 1 - X = Og at *
  field_simp
  subst hMg hXg hTg hOg
  ring

/-- The letter `log (1 - X + a X)`. -/
theorem formOCH_letter_M (hX1 : X - 1 ≠ 0) (hX2 : X - 2 ≠ 0) (hL : 1 - a * X ≠ 0)
    (hd : HasDerivAt (fun b => formOCHcM b X) d a) :
    d + formOCHK X * X / (1 - a * X) = formOCGcbX a X := by
  rw [hd.unique (formOCH_hasDerivAt_div (formOCH_hasDerivAt_L X a) hL)]
  simp only [formOCHK, formOCGcbX, formOCHq, formOCHqD]
  have hO : 1 - X ≠ 0 := fun h => hX1 (by linarith)
  generalize hLg : 1 - a * X = Lg at *
  generalize hXg : X - 1 = Xm at *
  generalize hTg : X - 2 = Xt at *
  generalize hOg : 1 - X = Og at *
  field_simp
  subst hLg hXg hTg hOg
  ring

/-- The letter `log (2 - X)`. -/
theorem formOCH_letter_T (hX1 : X - 1 ≠ 0) (hL : 1 - a * X ≠ 0) (hM : 1 - X + a * X ≠ 0)
    (hd : HasDerivAt (fun b => formOCHcT b X) d a) :
    d - formOCHK X * X / (1 - X + a * X) - formOCHK X * X / (1 - a * X) =
      formOCGc2X a X := by
  have hD : HasDerivAt (fun b : ℝ => (1 - b * X) * (1 - X + b * X))
      (-X * (1 - X + a * X) + (1 - a * X) * X) a :=
    (formOCH_hasDerivAt_L X a).mul (formOCH_hasDerivAt_M X a)
  rw [hd.unique (formOCH_hasDerivAt_div hD (mul_ne_zero hL hM))]
  simp only [formOCHK, formOCGc2X, formOCHq, formOCHqD]
  have hO : 1 - X ≠ 0 := fun h => hX1 (by linarith)
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hXg : X - 1 = Xm at *
  generalize hOg : 1 - X = Og at *
  field_simp
  subst hLg hMg hXg hOg
  ring

end

end QED.ChainProof.SetCK

end
