/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormXPF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the branch-2 basis functions in partial fractions

Helper level (no frozen statement). Step 4 of route D for `ρ_X` (scratch `stageK/STATUS.md`,
session 24+). After the substitution `y₃ = ℓ t/(sD)`, `Y - y₃ = BC/(sD)`
(`ℓ = (X - u)(X + u - Xu)`, `formXLl`), the branch-2 integrand is a combination, with
coefficients in `s`, of the fourteen functions `φ = ℓ^a (BC)^i / ((BC)^j D^k)` (`formXPhi`). Each
is written here as a partial-fraction sum `formXPF` with an explicit coefficient vector
(`formXk…`, generated and checked in sympy, `stageK/fxf/m3.py`, `m4.py`), under the
non-vanishing hypotheses `formXPFHyp`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

/-- `ℓ = (X - u)(X + u - Xu)`. -/
def formXLl (X u : ℝ) : ℝ := (X - u) * (X + u - X * u)

/-- The basis function `ℓ^a (BC)^i / ((BC)^j D^k)`. -/
noncomputable def formXPhi (a i j k : ℕ) (X s u : ℝ) : ℝ :=
  formXLl X u ^ a * (formXLb X u s * formXLc X u s) ^ i /
    ((formXLb X u s * formXLc X u s) ^ j * coordD X u s ^ k)

/-- The non-vanishing hypotheses of the partial-fraction identities. -/
def formXPFHyp (X s u : ℝ) : Prop :=
  formXLb X u s ≠ 0 ∧ formXLc X u s ≠ 0 ∧ coordD X u s ≠ 0 ∧ X ≠ 0 ∧ X - 1 ≠ 0 ∧ X - 2 ≠ 0 ∧
    s - 1 ≠ 0 ∧ s - 2 ≠ 0

/-- Partial fractions of `ℓ^0 (BC)^-1 / D^0`. -/
noncomputable def formXk0m10 (X s : ℝ) : Fin 9 → ℝ :=
  ![0, 0, (1) / (X*(X - 2)*(s - 1)), 0, (X - 1) / (X*(X - 2)*(s - 1)), 0, 0, 0, 0]

theorem formXPhi_0m10 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 0 0 1 0 X s u = formXPF (formXk0m10 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk0m10, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^0 (BC)^0 / D^1`. -/
noncomputable def formXk0p01 (_X _s : ℝ) : Fin 9 → ℝ :=
  ![0, 0, 0, 0, 0, 0, 1, 0, 0]

theorem formXPhi_0p01 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 0 0 0 1 X s u = formXPF (formXk0p01 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk0p01, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^0 (BC)^1 / D^2`. -/
noncomputable def formXk0p12 (X s : ℝ) : Fin 9 → ℝ :=
  ![(-1) / ((X - 1)*(s - 2)^2), 0, 0, 0, 0, 0, (-X^2*s*(s - 1)) / ((X - 1)*(s - 2)^2), (-X^2*(s -
      1)^2*(X + s - 2)*(X*s - X - s + 2)) / ((X - 1)*(s - 2)^2), 0]

theorem formXPhi_0p12 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 0 1 0 2 X s u = formXPF (formXk0p12 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk0p12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^0 (BC)^2 / D^3`. -/
noncomputable def formXk0p23 (X s : ℝ) : Fin 9 → ℝ :=
  ![(X^2*(s - 1)*(2*s - 1)) / ((X - 1)^2*(s - 2)^4), (1) / ((X - 1)*(s - 2)^3), 0, 0, 0, 0, (X^2*(s
      - 1)^2*(X^2*s^2 + 2*X^2*s - 2*X^2 + 2*X*s^2 - 8*X*s + 8*X - 2*s^2 + 8*s - 8)) / ((X - 1)^2*(s
      - 2)^4), (2*X^4*s*(s - 1)^3*(X + s - 2)*(X*s - X - s + 2)) / ((X - 1)^2*(s - 2)^4), (X^4*(s -
      1)^4*(X + s - 2)^2*(X*s - X - s + 2)^2) / ((X - 1)^2*(s - 2)^4)]

theorem formXPhi_0p23 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 0 2 0 3 X s u = formXPF (formXk0p23 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk0p23, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^1 (BC)^-2 / D^0`. -/
noncomputable def formXk1m20 (X s : ℝ) : Fin 9 → ℝ :=
  ![0, 0, (X^2*s - X^2 + 2*X*s^2 - 4*X*s + 4*X - 2*s^2 + 4*s - 4) / (X*(X - 2)^3*(s - 1)^3), (s*(X*s
      - X - s + 2)) / ((X - 2)^2*(s - 1)^2), ((X - 1)*(X^2*s - X^2 + 2*X*s^2 - 4*X*s + 4*X - 2*s^2
      + 4*s - 4)) / (X*(X - 2)^3*(s - 1)^3), (s*(X - 1)*(X + s - 2)) / ((X - 2)^2*(s - 1)^2), 0, 0,
      0]

theorem formXPhi_1m20 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 1 0 2 0 X s u = formXPF (formXk1m20 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk1m20, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^1 (BC)^-1 / D^1`. -/
noncomputable def formXk1m11 (X s : ℝ) : Fin 9 → ℝ :=
  ![0, 0, (-s) / ((X - 2)*(s - 1)^2), 0, (-s) / ((X - 2)*(s - 1)^2), 0, (-1) / ((s - 1)^2), 0, 0]

theorem formXPhi_1m11 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 1 0 1 1 X s u = formXPF (formXk1m11 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk1m11, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^1 (BC)^0 / D^2`. -/
noncomputable def formXk1p02 (X s : ℝ) : Fin 9 → ℝ :=
  ![(1) / ((X - 1)*(s - 2)^2), 0, 0, 0, 0, 0, (X^2*s) / ((X - 1)*(s - 2)^2), (X^2*(X + s - 2)*(X*s
      - X - s + 2)) / ((X - 1)*(s - 2)^2), 0]

theorem formXPhi_1p02 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 1 0 0 2 X s u = formXPF (formXk1p02 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk1p02, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^1 (BC)^1 / D^3`. -/
noncomputable def formXk1p13 (X s : ℝ) : Fin 9 → ℝ :=
  ![(-X^2*(s^2 - s + 1)) / ((X - 1)^2*(s - 2)^4), (-1) / ((X - 1)*(s - 2)^3), 0, 0, 0, 0,
      (-X^2*(2*X^2*s^3 - 4*X^2*s^2 + 4*X^2*s - 2*X^2 + X*s^4 - 6*X*s^3 + 14*X*s^2 - 16*X*s + 8*X -
      s^4 + 6*s^3 - 14*s^2 + 16*s - 8)) / ((X - 1)^2*(s - 2)^4), (-X^4*s^2*(s - 1)*(X + s - 2)*(X*s
      - X - s + 2)) / ((X - 1)^2*(s - 2)^4), (-X^4*(s - 1)^2*(X + s - 2)^2*(X*s - X - s +
      2)^2) / ((X - 1)^2*(s - 2)^4)]

theorem formXPhi_1p13 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 1 1 0 3 X s u = formXPF (formXk1p13 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk1p13, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^2 (BC)^-2 / D^1`. -/
noncomputable def formXk2m21 (X s : ℝ) : Fin 9 → ℝ :=
  ![0, 0, (s*(X^2*s^2 - 2*X^2*s + 2*X^2 - 5*X*s^2 + 8*X*s - 8*X + 4*s^2 - 8*s + 8)) / ((X - 2)^3*(s
      - 1)^4), (-X*s^2*(X*s - X - s + 2)) / ((X - 2)^2*(s - 1)^3), (-s*(2*X^2*s - 2*X^2 + 3*X*s^2 -
      8*X*s + 8*X - 4*s^2 + 8*s - 8)) / ((X - 2)^3*(s - 1)^4), (-X*s^2*(X + s - 2)) / ((X - 2)^2*(s
      - 1)^3), (1) / ((s - 1)^4), 0, 0]

theorem formXPhi_2m21 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 2 0 2 1 X s u = formXPF (formXk2m21 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk2m21, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^2 (BC)^-1 / D^2`. -/
noncomputable def formXk2m12 (X s : ℝ) : Fin 9 → ℝ :=
  ![(-1) / ((X - 1)*(s - 2)^2), 0, (X*s^2) / ((X - 2)*(s - 1)^3), 0, (X*s^2) / ((X - 2)*(X - 1)*(s
      - 1)^3), 0, (-X^2*s*(2*s - 3)) / ((X - 1)*(s - 2)^2*(s - 1)^3), (-X^2*(X + s - 2)*(X*s - X - s
      + 2)) / ((X - 1)*(s - 2)^2*(s - 1)^2), 0]

theorem formXPhi_2m12 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 2 0 1 2 X s u = formXPF (formXk2m12 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk2m12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^2 (BC)^0 / D^3`. -/
noncomputable def formXk2p03 (X s : ℝ) : Fin 9 → ℝ :=
  ![(X^2*(s + 1)) / ((X - 1)^2*(s - 2)^4), (1) / ((X - 1)*(s - 2)^3), 0, 0, 0, 0, (X^2*(X^2*s^2 +
      2*X^2*s - 2*X^2 + 2*X*s^2 - 8*X*s + 8*X - 2*s^2 + 8*s - 8)) / ((X - 1)^2*(s - 2)^4),
      (2*X^4*s*(X + s - 2)*(X*s - X - s + 2)) / ((X - 1)^2*(s - 2)^4), (X^4*(X + s - 2)^2*(X*s - X
      - s + 2)^2) / ((X - 1)^2*(s - 2)^4)]

theorem formXPhi_2p03 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 2 0 0 3 X s u = formXPF (formXk2p03 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk2p03, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^3 (BC)^-2 / D^2`. -/
noncomputable def formXk3m22 (X s : ℝ) : Fin 9 → ℝ :=
  ![(1) / ((X - 1)*(s - 2)^2), 0, (-X*s^2*(2*X^2*s^2 - 3*X^2*s + 3*X^2 - 8*X*s^2 + 12*X*s - 12*X +
      6*s^2 - 12*s + 12)) / ((X - 2)^3*(s - 1)^5), (X^2*s^3*(X*s - X - s + 2)) / ((X - 2)^2*(s -
      1)^4), (X*s^2*(3*X^2*s - 3*X^2 + 4*X*s^2 - 12*X*s + 12*X - 6*s^2 + 12*s - 12)) / ((X - 2)^3*(X
      - 1)*(s - 1)^5), (X^2*s^3*(X + s - 2)) / ((X - 2)^2*(X - 1)*(s - 1)^4), (X^2*s*(3*s -
      5)) / ((X - 1)*(s - 2)^2*(s - 1)^5), (X^2*(X + s - 2)*(X*s - X - s + 2)) / ((X - 1)*(s -
      2)^2*(s - 1)^4), 0]

theorem formXPhi_3m22 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 3 0 2 2 X s u = formXPF (formXk3m22 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk3m22, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^3 (BC)^-1 / D^3`. -/
noncomputable def formXk3m13 (X s : ℝ) : Fin 9 → ℝ :=
  ![(X^2*(s^2 - 3*s - 1)) / ((X - 1)^2*(s - 2)^4), (-1) / ((X - 1)*(s - 2)^3), (-X^2*s^3) / ((X -
      2)*(s - 1)^4), 0, (-X^2*s^3) / ((X - 2)*(X - 1)^2*(s - 1)^4), 0, (-X^2*(3*X^2*s^4 - 6*X^2*s^3
      - 2*X^2*s^2 + 8*X^2*s - 2*X^2 + 3*X*s^4 - 18*X*s^3 + 38*X*s^2 - 32*X*s + 8*X - 3*s^4 + 18*s^3
      - 38*s^2 + 32*s - 8)) / ((X - 1)^2*(s - 2)^4*(s - 1)^4), (-X^4*s*(3*s - 4)*(X + s - 2)*(X*s -
      X - s + 2)) / ((X - 1)^2*(s - 2)^4*(s - 1)^3), (-X^4*(X + s - 2)^2*(X*s - X - s + 2)^2) / ((X
      - 1)^2*(s - 2)^4*(s - 1)^2)]

theorem formXPhi_3m13 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 3 0 1 3 X s u = formXPF (formXk3m13 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk3m13, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

/-- Partial fractions of `ℓ^4 (BC)^-2 / D^3`. -/
noncomputable def formXk4m23 (X s : ℝ) : Fin 9 → ℝ :=
  ![(-X^2*(2*s^2 - 5*s - 1)) / ((X - 1)^2*(s - 2)^4), (1) / ((X - 1)*(s - 2)^3), (X^2*s^3*(3*X^2*s^2
      - 4*X^2*s + 4*X^2 - 11*X*s^2 + 16*X*s - 16*X + 8*s^2 - 16*s + 16)) / ((X - 2)^3*(s - 1)^6),
      (-X^3*s^4*(X*s - X - s + 2)) / ((X - 2)^2*(s - 1)^5), (-X^2*s^3*(4*X^2*s - 4*X^2 + 5*X*s^2 -
      16*X*s + 16*X - 8*s^2 + 16*s - 16)) / ((X - 2)^3*(X - 1)^2*(s - 1)^6), (-X^3*s^4*(X + s -
      2)) / ((X - 2)^2*(X - 1)^2*(s - 1)^5), (X^2*(6*X^2*s^4 - 16*X^2*s^3 + 5*X^2*s^2 + 10*X^2*s -
      2*X^2 + 4*X*s^4 - 24*X*s^3 + 50*X*s^2 - 40*X*s + 8*X - 4*s^4 + 24*s^3 - 50*s^2 + 40*s -
      8)) / ((X - 1)^2*(s - 2)^4*(s - 1)^6), (2*X^4*s*(2*s - 3)*(X + s - 2)*(X*s - X - s + 2)) / ((X
      - 1)^2*(s - 2)^4*(s - 1)^5), (X^4*(X + s - 2)^2*(X*s - X - s + 2)^2) / ((X - 1)^2*(s - 2)^4*(s
      - 1)^4)]

theorem formXPhi_4m23 {X s u : ℝ} (h : formXPFHyp X s u) :
    formXPhi 4 0 2 3 X s u = formXPF (formXk4m23 X s) X s u := by
  obtain ⟨hB, hC, hD, hX0, hX1, hX2, hs1, hs2⟩ := h
  simp only [formXPhi, formXPF, formXk4m23, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp
  unfold formXLl formXLb formXLc coordD
  ring

end QED.ChainProof.SetCK

end
