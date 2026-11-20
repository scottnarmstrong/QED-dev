/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCG
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the derivative of the rational part `H`

Helper level (no frozen statement). The rational part `formCHr` of the `u`-antiderivative of `J`
satisfies `H' = R + F_U/(1 - u) + F_V/(X - u) - (1 - X) G_m/P + (1 - X) G_m/(X + u - Xu)
- (1 - X) F_M/M + h_U/(1 - u) - (1 - X) h_M/M - (1 - X) h_P/P - (1 - X) h_A/(X + u - Xu)`
(`hasDerivAt_formCHr`), so that the `L'/L`-terms of `Σ F_L log L` and of the constant log terms
cancel against `R = formCJR`. Each product is first put in partial fractions (`formCS1`, …,
`formCS5`; `formCS1_eq`, …), and the identity is then checked with `P`, `Q`, `M` as atoms.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

/-- Partial fractions of `F_U/(1 - u)`. -/
noncomputable def formCS1 (X u : ℝ) : ℝ :=
  ((X - 1) * (X ^ 4 - 4 * X ^ 3 + 6 * X ^ 2 - 4 * X + 2)/(12 * formCK X ^ 2)) / coordM X u +
    (-(X - 1) ^ 3/(6 * formCK X)) / coordM X u ^ 2 +
    (X ^ 2 * (X - 2) ^ 2 * (X ^ 6 - 3 * X ^ 5 - 5 * X ^ 4 + 48 * X ^ 3 - 104 * X ^ 2 + 96 * X -
        32)/(96 * (X - 1) * formCK X ^ 3)) / formCQ X u +
    (X ^ 4 * (X - 2) ^ 4 * (2 * X ^ 2 - 7 * X + 7)/(96 * (X - 1) * formCK X ^ 2)) / formCQ X u ^ 2 +
    (-X ^ 6 * (X - 2) ^ 4/(64 * (X - 1) * formCK X)) / formCQ X u ^ 3 +
    (-(X ^ 10 - 10 * X ^ 9 + 62 * X ^ 8 - 256 * X ^ 7 + 732 * X ^ 6 - 1528 * X ^ 5 + 2376 * X ^ 4 -
        2656 * X ^ 3 + 1984 * X ^ 2 - 880 * X + 176)/(192 * (X - 1) ^ 2 * formCK X ^ 3)) / (1 - u) +
    (-(3 * X ^ 2 - 14 * X + 14)/(192 * (X - 1))) +
    (-1/96) * u

/-- Partial fractions of `F_V/(X - u)`. -/
noncomputable def formCS2 (X u : ℝ) : ℝ :=
  (X * (X - 2) * (X - 1)/12) / coordM X u +
    ((X - 1) ^ 3/6) / coordM X u ^ 2

/-- Partial fractions of `(1 - X) G_m/P`. -/
noncomputable def formCS3 (X u : ℝ) : ℝ :=
  (X ^ 2/12) / coordM X u +
    (-(X - 1) ^ 2/6) / coordM X u ^ 2 +
    (-X ^ 2/12) / formCP X u

/-- Partial fractions of `(1 - X) G_m/(X + u - Xu)`. -/
noncomputable def formCS4 (X u : ℝ) : ℝ :=
  (X * (X - 2)/(12 * (X - 1))) / (X + u - X * u) +
    (-X * (X - 2)/(12 * (X - 1))) / coordM X u +
    ((X - 1)/6) / coordM X u ^ 2

/-- Partial fractions of `(1 - X) F_M/M`. -/
noncomputable def formCS5 (X u : ℝ) : ℝ :=
  (-(X ^ 10 - 26 * X ^ 9 + 142 * X ^ 8 - 384 * X ^ 7 + 620 * X ^ 6 - 632 * X ^ 5 + 360 * X ^ 4 - 32
      * X ^ 3 - 112 * X ^ 2 + 80 * X - 16)/(192 * (X - 1) * formCK X ^ 3)) / coordM X u +
    (-X ^ 2 * (X ^ 2 - X + 1)/(12 * (X - 1))) / formCP X u +
    (-X ^ 6/(12 * (X - 1))) / formCP X u ^ 2 +
    (X ^ 2 * (X - 2) ^ 2 * (6 * X ^ 6 - 39 * X ^ 5 + 103 * X ^ 4 - 160 * X ^ 3 + 160 * X ^ 2 - 96 *
        X + 32)/(96 * (X - 1) * formCK X ^ 3)) / formCQ X u +
    (-X ^ 4 * (X - 2) ^ 4 * (5 * X ^ 2 - 7 * X + 7)/(96 * (X - 1) * formCK X ^ 2)) / formCQ X u ^ 2
        +
    (X ^ 6 * (X - 2) ^ 4/(64 * (X - 1) * formCK X)) / formCQ X u ^ 3 +
    ((11 * X ^ 2 + 2 * X - 2)/(192 * (X - 1))) +
    (7/96) * u

/-- The derivative of `formCHr`, in partial fractions. -/
noncomputable def formCHrD (X u : ℝ) : ℝ :=
  ((X - 1) ^ 2 * (2 * X ^ 2 + 3 * X - 3) / (24 * formCK X)) / coordM X u ^ 2 +
    ((X - 1) ^ 2 * (X ^ 2 - X + 1) * (2 * X ^ 2 - 7 * X + 7) / (12 * formCK X)) / coordM X u ^ 3 +
    (-X ^ 4 * (X ^ 2 - X + 1) / (12 * (X - 1))) / formCP X u ^ 2 +
    (-7 * X ^ 4 * (X - 2) ^ 4 / (96 * (X - 1) * formCK X)) / formCQ X u ^ 2 +
    (X ^ 6 * (X - 2) ^ 4 / (16 * (X - 1) * formCK X)) / formCQ X u ^ 3 +
    ((3 * X ^ 2 - 10 * X + 10) / (32 * (X - 1))) +
    (1 / 4) * u +
    ((X - 1) / (4 * X ^ 2)) * u ^ 2

section deriv

variable {X u : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo 0 X)
include hX hu

theorem formCS_ne : formCP X u ≠ 0 ∧ formCQ X u ≠ 0 ∧ coordM X u ≠ 0 ∧ X ≠ 0 ∧ X - 1 ≠ 0 ∧
    X - 2 ≠ 0 ∧ 1 - u ≠ 0 ∧ X - u ≠ 0 ∧ X + u - X * u ≠ 0 ∧ formCK X ≠ 0 := by
  obtain ⟨hP, hQ, hM⟩ := formC_pos_PQM hX hu
  obtain ⟨h0, h1⟩ := hX
  obtain ⟨hu0, huX⟩ := hu
  refine ⟨hP.ne', hQ.ne', hM.ne', h0.ne', by linarith, by linarith, by linarith, by linarith,
    by nlinarith, by unfold formCK; nlinarith⟩

theorem formCS1_eq : formCFU X u / (1 - u) = formCS1 X u := by
  obtain ⟨hP, hQ, hM, hX0, hX1, hX2, hU, hV, hA, hK⟩ := formCS_ne hX hu
  unfold formCFU formCGm formCGq formCc formCS1
  field_simp
  unfold formCQ coordM formCK
  ring

theorem formCS2_eq : formCFV X u / (X - u) = formCS2 X u := by
  obtain ⟨hP, hQ, hM, hX0, hX1, hX2, hU, hV, hA, hK⟩ := formCS_ne hX hu
  unfold formCFV formCGm formCS2
  field_simp
  unfold coordM formCK
  ring

theorem formCS3_eq : formCGm X u * (1 - X) / formCP X u = formCS3 X u := by
  obtain ⟨hP, hQ, hM, hX0, hX1, hX2, hU, hV, hA, hK⟩ := formCS_ne hX hu
  unfold formCGm formCS3
  field_simp
  unfold formCP coordM formCK
  ring

theorem formCS4_eq : formCGm X u * (1 - X) / (X + u - X * u) = formCS4 X u := by
  obtain ⟨hP, hQ, hM, hX0, hX1, hX2, hU, hV, hA, hK⟩ := formCS_ne hX hu
  unfold formCGm formCS4
  field_simp
  unfold coordM formCK
  ring

theorem formCS5_eq : formCFM X u * (1 - X) / coordM X u = formCS5 X u := by
  obtain ⟨hP, hQ, hM, hX0, hX1, hX2, hU, hV, hA, hK⟩ := formCS_ne hX hu
  unfold formCFM formCGp formCGq formCc formCS5
  field_simp
  unfold formCP formCQ coordM formCK
  ring

theorem hasDerivAt_formCHrD : HasDerivAt (formCHr X) (formCHrD X u) u := by
  obtain ⟨hP, hQ, hM, hX0, hX1, hX2, hU, hV, hA, hK⟩ := formCS_ne hX hu
  have dM := formC_hasDerivAt_M X u
  have dP := formC_hasDerivAt_P X u
  have dQ := formC_hasDerivAt_Q X u
  have h := ((((((((formC_hasDerivAt_div
    ((X - 1) * (2 * X ^ 2 + 3 * X - 3) / (24 * formCK X)) dM hM).add
    (formC_hasDerivAt_div_pow ((X - 1) * (X ^ 2 - X + 1) * (2 * X ^ 2 - 7 * X + 7) /
      (24 * formCK X)) 1 dM hM)).add
    (formC_hasDerivAt_div (-X ^ 4 * (X ^ 2 - X + 1) / (12 * (X - 1) ^ 2)) dP hP)).add
    (formC_hasDerivAt_div (-7 * X ^ 4 * (X - 2) ^ 4 / (192 * (X - 1) ^ 2 * formCK X))
      dQ hQ)).add
    (formC_hasDerivAt_div_pow (X ^ 6 * (X - 2) ^ 4 / (64 * (X - 1) ^ 2 * formCK X)) 1
      dQ hQ)).add
    ((hasDerivAt_id u).const_mul ((3 * X ^ 2 - 10 * X + 10) / (32 * (X - 1))))).add
    ((hasDerivAt_pow 2 u).const_mul (1 / 8))).add
    ((hasDerivAt_pow 3 u).const_mul ((X - 1) / (12 * X ^ 2))))
  refine h.congr_deriv ?_
  unfold formCHrD
  push_cast
  field_simp
  ring

/-- **The partial-fraction identity** behind `hasDerivAt_formCHr`, checked per pole order. -/
theorem formCHrD_eq : formCHrD X u =
    formCJR X u + formCS1 X u + formCS2 X u - formCS3 X u + formCS4 X u - formCS5 X u +
      formChU X / (1 - u) - formChM X * (1 - X) / coordM X u -
      formChP X * (1 - X) / formCP X u - formChA X * (1 - X) / (X + u - X * u) := by
  obtain ⟨hP, hQ, hM, hX0, hX1, hX2, hU, hV, hA, hK⟩ := formCS_ne hX hu
  have hA1 : 0 = (X * (X - 2)/(12 * (X - 1))) - (formChA X * (1 - X)) := by
    simp only [formChA]
    field_simp
    ring
  have hM1 : 0 = (-(2 * X ^ 8 - 18 * X ^ 7 + 78 * X ^ 6 - 208 * X ^ 5 + 375 * X ^ 4 - 468 * X ^ 3 +
      394 * X ^ 2 - 204 * X + 51) / (12 * formCK X ^ 3)) - ((X ^ 4 - 5 * X ^ 3 + 10 * X ^ 2 - 10 *
      X + 5) / (12 * (X - 1))) + ((3 * X ^ 10 - 13 * X ^ 9 + 28 * X ^ 8 - 31 * X ^ 7 + 7 * X ^ 6 +
      47 * X ^ 5 - 95 * X ^ 4 + 104 * X ^ 3 - 71 * X ^ 2 + 30 * X - 6) / (12 * (X - 1) * formCK X ^
      3)) + (-X ^ 4 * (2 * X ^ 6 - 8 * X ^ 5 + 17 * X ^ 4 - 23 * X ^ 3 + 24 * X ^ 2 - 15 * X + 5) /
      (12 * (X - 1) * formCK X ^ 3)) + ((X - 1) * (X ^ 4 - 4 * X ^ 3 + 6 * X ^ 2 - 4 * X + 2)/(12 *
      formCK X ^ 2)) + (X * (X - 2) * (X - 1)/12) - (X ^ 2/12) + (-X * (X - 2)/(12 * (X - 1))) -
      (-(X ^ 10 - 26 * X ^ 9 + 142 * X ^ 8 - 384 * X ^ 7 + 620 * X ^ 6 - 632 * X ^ 5 + 360 * X ^ 4
      - 32 * X ^ 3 - 112 * X ^ 2 + 80 * X - 16)/(192 * (X - 1) * formCK X ^ 3)) - (formChM X * (1 -
      X)) := by
    simp only [formChM]
    field_simp
    unfold formCK
    ring
  have hM2 : ((X - 1) ^ 2 * (2 * X ^ 2 + 3 * X - 3) / (24 * formCK X)) = (-(X - 1) * (X ^ 2 - X +
      1) * (2 * X ^ 4 - 11 * X ^ 3 + 28 * X ^ 2 - 34 * X + 17) / (12 * formCK X ^ 2)) - ((X - 1) *
      (X ^ 2 + 4 * X - 4) / 12) + (X ^ 2 * (X - 1) * (2 * X ^ 4 - 4 * X ^ 3 + 7 * X ^ 2 - 6 * X +
      3) / (24 * formCK X ^ 2)) + (-(X - 1) ^ 3/(6 * formCK X)) + ((X - 1) ^ 3/6) - (-(X - 1) ^
      2/6) + ((X - 1)/6) := by
    field_simp
    unfold formCK
    ring
  have hM3 : ((X - 1) ^ 2 * (X ^ 2 - X + 1) * (2 * X ^ 2 - 7 * X + 7) / (12 * formCK X)) = ((X - 1)
      ^ 2 * (2 * X ^ 4 - 8 * X ^ 3 + 13 * X ^ 2 - 10 * X + 5) / (12 * formCK X)) - ((X - 1) ^ 3 /
      12) := by
    field_simp
    unfold formCK
    ring
  have hP1 : 0 = -(-X ^ 2 * (X ^ 2 - 3 * X + 3) / (12 * (X - 1))) + (X ^ 2 / 12) + (-X ^ 2 / 6) +
      (-X ^ 2 * (X ^ 2 + 3 * X - 3) / (4 * (X - 1))) + (X ^ 2 * (2 * X ^ 2 + 11 * X - 11) / (12 *
      (X - 1))) - (-X ^ 2/12) - (-X ^ 2 * (X ^ 2 - X + 1)/(12 * (X - 1))) - (formChP X * (1 - X))
      := by
    simp only [formChP]
    field_simp
    unfold formCK
    ring
  have hP2 : (-X ^ 4 * (X ^ 2 - X + 1) / (12 * (X - 1))) = -(-X ^ 4 / 12) + (-X ^ 4 * (3 * X ^ 2 -
      4 * X + 4) / (12 * (X - 1))) + (X ^ 4 * formCK X / (12 * (X - 1))) + (X ^ 4 * (X ^ 2 - 6 * X
      + 6) / (12 * (X - 1))) + (-X ^ 4 * (X - 2) ^ 2 / (12 * (X - 1))) - (-X ^ 6/(12 * (X - 1))) :=
      by
    field_simp
    unfold formCK
    ring
  have hP3 : 0 = (X ^ 6 / 6) + (-X ^ 6 / 3) + (X ^ 6 / 6) := by
    field_simp
    ring
  have hQ1 : 0 = (-X ^ 4 * (X - 2) ^ 2 * (X ^ 4 - 5 * X ^ 3 + 13 * X ^ 2 - 16 * X + 8) / (16 * (X -
      1) * formCK X ^ 3)) + (-X ^ 2 * (X - 2) ^ 2 * (3 * X ^ 6 - 74 * X ^ 5 + 378 * X ^ 4 - 896 * X
      ^ 3 + 1168 * X ^ 2 - 864 * X + 288) / (96 * (X - 1) * formCK X ^ 3)) + (X ^ 2 * (X - 2) ^ 4 *
      (7 * X ^ 4 - 42 * X ^ 3 + 86 * X ^ 2 - 88 * X + 44) / (48 * (X - 1) * formCK X ^ 3)) + (X ^ 2
      * (X - 2) ^ 2 * (X ^ 6 - 3 * X ^ 5 - 5 * X ^ 4 + 48 * X ^ 3 - 104 * X ^ 2 + 96 * X - 32)/(96
      * (X - 1) * formCK X ^ 3)) - (X ^ 2 * (X - 2) ^ 2 * (6 * X ^ 6 - 39 * X ^ 5 + 103 * X ^ 4 -
      160 * X ^ 3 + 160 * X ^ 2 - 96 * X + 32)/(96 * (X - 1) * formCK X ^ 3)) := by
    field_simp
    ring
  have hQ2 : (-7 * X ^ 4 * (X - 2) ^ 4 / (96 * (X - 1) * formCK X)) = (X ^ 4 * (X - 2) ^ 4 / (16 *
      formCK X ^ 2)) + (-X ^ 4 * (X - 2) ^ 4 * (11 * X ^ 2 - 10 * X + 10) / (96 * (X - 1) * formCK
      X ^ 2)) + (-X ^ 4 * (X - 2) ^ 6 / (32 * (X - 1) * formCK X ^ 2)) + (X ^ 4 * (X - 2) ^ 4 * (2
      * X ^ 2 - 7 * X + 7)/(96 * (X - 1) * formCK X ^ 2)) - (-X ^ 4 * (X - 2) ^ 4 * (5 * X ^ 2 - 7
      * X + 7)/(96 * (X - 1) * formCK X ^ 2)) := by
    field_simp
    unfold formCK
    ring
  have hQ3 : (X ^ 6 * (X - 2) ^ 4 / (16 * (X - 1) * formCK X)) = (X ^ 6 * (X - 2) ^ 4 / (32 * (X -
      1) * formCK X)) + (X ^ 6 * (X - 2) ^ 4 / (16 * (X - 1) * formCK X)) + (-X ^ 6 * (X - 2) ^
      4/(64 * (X - 1) * formCK X)) - (X ^ 6 * (X - 2) ^ 4/(64 * (X - 1) * formCK X)) := by
    field_simp
    ring
  have hU1 : 0 = ((X - 1) ^ 3 / (4 * formCK X ^ 3)) + (-(X - 1) ^ 3 / (2 * formCK X ^ 3)) + (-(X ^
      10 - 10 * X ^ 9 + 62 * X ^ 8 - 256 * X ^ 7 + 732 * X ^ 6 - 1528 * X ^ 5 + 2376 * X ^ 4 - 2656
      * X ^ 3 + 1984 * X ^ 2 - 880 * X + 176)/(192 * (X - 1) ^ 2 * formCK X ^ 3)) + formChU X := by
    simp only [formChU]
    field_simp
    unfold formCK
    ring
  have hpoly0 : (((3 * X ^ 2 - 10 * X + 10) / (32 * (X - 1)))) + ((1 / 4) * u) + (((X - 1) / (4 * X
      ^ 2)) * u ^ 2) = ((1 / 6)) - ((1 / 6)) + (((3 * X ^ 2 - 7 * X + 7) / (12 * (X - 1)))) + ((u *
      (X ^ 2 - X + 1) / (2 * X ^ 2))) + ((u ^ 2 * (X - 1) / (2 * X ^ 2))) + ((-(X - 2) ^ 2 / (12 *
      (X - 1)))) + ((-u ^ 2 * (X - 1) / (4 * X ^ 2))) + ((-u * (X ^ 2 - 3 * X + 3) / (6 * X ^ 2)))
      + ((-u / 16)) + ((formCK X / (32 * (X - 1)))) + ((-1 / 16)) + ((u / 16)) + ((-X ^ 2 / (32 *
      (X - 1)))) + ((-(3 * X ^ 2 - 14 * X + 14)/(192 * (X - 1)))) + ((-1/96) * u) - (((11 * X ^ 2 +
      2 * X - 2)/(192 * (X - 1)))) - ((7/96) * u) := by
    field_simp
    unfold formCK
    ring
  unfold formCHrD formCJR formCJRA1a formCJRA1b formCJRQ0 formCJRQ1 formCJRR2 formCJRD2 formCJRD3
    formCS1 formCS2 formCS3 formCS4 formCS5
  linear_combination hA1 / (X + u - X * u) + hM1 / coordM X u + hM2 / coordM X u ^ 2 + hM3 / coordM
      X u ^ 3 + hP1 / formCP X u + hP2 / formCP X u ^ 2 + hP3 / formCP X u ^ 3 + hQ1 / formCQ X u +
      hQ2 / formCQ X u ^ 2 + hQ3 / formCQ X u ^ 3 + hU1 / (1 - u) + hpoly0

theorem hasDerivAt_formCHr : HasDerivAt (formCHr X)
    (formCJR X u + formCS1 X u + formCS2 X u - formCS3 X u + formCS4 X u - formCS5 X u +
      formChU X / (1 - u) - formChM X * (1 - X) / coordM X u -
      formChP X * (1 - X) / formCP X u - formChA X * (1 - X) / (X + u - X * u)) u :=
  formCHrD_eq hX hu ▸ hasDerivAt_formCHrD hX hu

end deriv

end QED.ChainProof.SetCK

end
