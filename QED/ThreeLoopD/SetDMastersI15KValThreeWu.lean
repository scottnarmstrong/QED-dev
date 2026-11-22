/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValThreeG
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiCalculus
import QED.Polylog.LiLimits
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₅`: the `u`-integral of `b₁³ - b₂³`

For `r ∈ (0, 1)` and `u ∈ (0, 1]` write `A = log (1 + u/r)`, `B = log (1 + r u)` and

  `b₁ = -log r + log u + 2 log (1 + r) - 2A - 2B`,  `b₂ = log r - 2 log (1 + r) - log u`

(the logarithms of `QED.ThreeLoopD.SetDMastersI15KValThreeW` in the coordinate
`r = x/(1 - x)`). This file gives an explicit primitive `Φ` of `b₁³ - b₂³` in `u`: a polynomial
in `u`, `log u`, `A`, `B` plus `G(X) = Li₃ X - Li₂ X log X` and `Li₂ X` at the eight
cross-ratio arguments `X ∈ (0, 1)` of the points `0, -r, -1/r, ∞`
(`r(1 + ru)/(r + u)`, `u/(r + u)`, `ru/(1 + ru)`, ... and their complements). Its derivative is a
polynomial identity in the logarithms once `log X` and `log (1 - X)` are written in `log u`,
`A`, `B` and constants. Since `b₁ ≤ b₂`, the integrand is `≤ 0`, so the fundamental theorem
of calculus gives integrability and `∫₀¹ (b₁³ - b₂³) du = Φ(1) - Φ(0⁺)`
(`QED.ThreeLoopD.integral_i15WuF`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i15WuPhi`, `QED.ThreeLoopD.tendsto_i15WuPhi_zero`.
* `QED.ThreeLoopD.integral_i15WuF`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- `A = log (1 + u/r)`. -/
noncomputable def i15WuA (r u : ℝ) : ℝ := log (1 + u / r)

/-- `B = log (1 + r u)`. -/
noncomputable def i15WuB (r u : ℝ) : ℝ := log (1 + r * u)

/-- The integrand `b₁³ - b₂³`. -/
noncomputable def i15WuF (r u : ℝ) : ℝ :=
  (-log r + log u + 2 * log (1 + r) - 2 * i15WuA r u - 2 * i15WuB r u) ^ 3 -
    (log r - 2 * log (1 + r) - log u) ^ 3

/-- The argument `X0`. -/
noncomputable def i15WuX0 (r u : ℝ) : ℝ := r * (1 + r * u) / (r + u)

/-- The argument `X1`. -/
noncomputable def i15WuX1 (r u : ℝ) : ℝ := u * ((1 - r) * (1 + r)) / (r + u)

/-- The argument `X2`. -/
noncomputable def i15WuX2 (r u : ℝ) : ℝ := r / (r + u)

/-- The argument `X3`. -/
noncomputable def i15WuX3 (r u : ℝ) : ℝ := u / (r + u)

/-- The argument `X4`. -/
noncomputable def i15WuX4 (r u : ℝ) : ℝ := 1 / (1 + r * u)

/-- The argument `X5`. -/
noncomputable def i15WuX5 (r u : ℝ) : ℝ := r * u / (1 + r * u)

/-- The argument `X6`. -/
noncomputable def i15WuX6 (r u : ℝ) : ℝ := (1 - r) * (1 + r) / (1 + r * u)

/-- The argument `X7`. -/
noncomputable def i15WuX7 (r u : ℝ) : ℝ := r * (r + u) / (1 + r * u)

/-- The polynomial part of the primitive. -/
noncomputable def i15WuP (r : ℝ) : List (ℝ × (ℕ × ℕ × ℕ × ℕ × ℕ)) :=
  [(2, (1, 3, 0, 0, 0)),
   (-6, (1, 2, 1, 0, 0)),
   (-6, (1, 2, 0, 1, 0)),
   (6 - 6 * Real.log r + 12 * Real.log (1 + r), (1, 2, 0, 0, 0)),
   (12, (1, 1, 2, 0, 0)),
   (24, (1, 1, 1, 1, 0)),
   (-36 - 24 * Real.log (1 + r) + 12 * Real.log r, (1, 1, 1, 0, 0)),
   (12, (1, 1, 0, 2, 0)),
   (-36 - 24 * Real.log (1 + r) + 12 * Real.log r, (1, 1, 0, 1, 0)),
   (60 - 12 * Real.log r + 6 * Real.log r ^ 2 + 24 * Real.log (1 + r) + 24 * Real.log (1 + r) ^ 2 -
       24 * Real.log (1 + r) * Real.log r, (1, 1, 0, 0, 0)),
   (-8, (1, 0, 3, 0, 0)),
   (-24, (1, 0, 2, 1, 0)),
   (36 - 12 * Real.log r + 24 * Real.log (1 + r), (1, 0, 2, 0, 0)),
   (-24, (1, 0, 1, 2, 0)),
   (72 - 24 * Real.log r + 48 * Real.log (1 + r), (1, 0, 1, 1, 0)),
   (-108 - 72 * Real.log (1 + r) - 24 * Real.log (1 + r) ^ 2 - 6 * Real.log r ^ 2 + 36 * Real.log r
       + 24 * Real.log (1 + r) * Real.log r, (1, 0, 1, 0, 0)),
   (-8, (1, 0, 0, 3, 0)),
   (36 - 12 * Real.log r + 24 * Real.log (1 + r), (1, 0, 0, 2, 0)),
   (-108 - 72 * Real.log (1 + r) - 24 * Real.log (1 + r) ^ 2 - 6 * Real.log r ^ 2 + 36 * Real.log r
       + 24 * Real.log (1 + r) * Real.log r, (1, 0, 0, 1, 0)),
   (156 - 60 * Real.log r - 2 * Real.log r ^ 3 + 6 * Real.log r ^ 2 + 16 * Real.log (1 + r) ^ 3 +
       24 * Real.log (1 + r) ^ 2 + 120 * Real.log (1 + r) - 24 * Real.log (1 + r) * Real.log r - 24
       * Real.log r * Real.log (1 + r) ^ 2 + 12 * Real.log (1 + r) * Real.log r ^ 2, (1, 0, 0, 0,
       0)),
   (-6 * r, (0, 2, 1, 0, 0)),
   (-6 * r⁻¹, (0, 2, 0, 1, 0)),
   (12 * r, (0, 1, 2, 0, 0)),
   (-24 * r + 24 * r⁻¹, (0, 1, 1, 1, 0)),
   (-36 * r - 60 * Real.log (1 + r) * r - 36 * Real.log (1 - r) * r + 12 * Real.log r * r + 36 *
       Real.log (1 - r) * r⁻¹ + 36 * Real.log (1 + r) * r⁻¹, (0, 1, 1, 0, 0)),
   (-12 * r⁻¹ + 24 * r, (0, 1, 0, 2, 0)),
   (72 * r - 192 * Real.log r * r - 12 * Real.log (1 - r) * r⁻¹ - 12 * Real.log (1 + r) * r⁻¹ + 12
       * Real.log (1 - r) * r + 60 * Real.log (1 + r) * r + 108 * Real.log r * r⁻¹, (0, 1, 0, 1,
       0)),
   (-8 * r, (0, 0, 3, 0, 0)),
   (-24 * r⁻¹ + 24 * r, (0, 0, 2, 1, 0)),
   (54 * r - 24 * Real.log (1 - r) * r⁻¹ - 24 * Real.log (1 + r) * r⁻¹ - 12 * Real.log r * r + 24 *
       Real.log (1 - r) * r + 60 * Real.log (1 + r) * r, (0, 0, 2, 0, 0)),
   (-72 * r + 24 * r⁻¹, (0, 0, 1, 2, 0)),
   (-36 * r + 54 * r⁻¹ - 72 * Real.log r * r⁻¹ - 24 * Real.log (1 + r) * r + 36 * Real.log (1 + r)
       * r⁻¹ + 120 * Real.log r * r, (0, 0, 1, 1, 0)),
   (-108 * r - 72 * Real.log (1 + r) * r - 24 * r * Real.log (1 + r) ^ 2 - 6 * r * Real.log r ^ 2 +
       36 * Real.log r * r + 24 * Real.log (1 + r) * Real.log r * r, (0, 0, 1, 0, 0)),
   (-24 * r⁻¹ + 32 * r, (0, 0, 0, 3, 0)),
   (-108 * r⁻¹ - 72 * Real.log (1 + r) * r⁻¹ - 24 * r⁻¹ * Real.log (1 + r) ^ 2 - 6 * r⁻¹ * Real.log
       r ^ 2 + 36 * Real.log r * r⁻¹ + 24 * Real.log (1 + r) * Real.log r * r⁻¹, (0, 0, 0, 1, 0))]

/-- **The primitive `Φ`** of `b₁³ - b₂³` in `u`. -/
noncomputable def i15WuPhi (r u : ℝ) : ℝ :=
  i15TPoly (i15WuP r) u (log u) (i15WuA r u) (i15WuB r u) 0 +
    (-24 * r) * i15TG (i15WuX0 r u) +
    (-24 * r + 24 * r⁻¹) * i15TG (i15WuX1 r u) +
    (36 * r) * i15TG (i15WuX2 r u) +
    (-24 * r⁻¹ + 12 * r) * i15TG (i15WuX3 r u) +
    (36 * r⁻¹) * i15TG (i15WuX4 r u) +
    (-24 * r + 12 * r⁻¹) * i15TG (i15WuX5 r u) +
    (-72 * r⁻¹ + 72 * r) * i15TG (i15WuX6 r u) +
    (-24 * r⁻¹ + 48 * r) * i15TG (i15WuX7 r u) +
    (-60 * Real.log r * r + 12 * Real.log r * r⁻¹) * Li₂ (i15WuX0 r u) +
    (-54 * r⁻¹ + 108 * r - 36 * Real.log (1 + r) * r⁻¹ + 72 * Real.log (1 + r) * r) * Li₂ (i15WuX1
        r u) +
    (-36 * Real.log (1 - r) * r⁻¹ - 36 * Real.log (1 + r) * r⁻¹ - 12 * Real.log r * r⁻¹ + 36 *
        Real.log (1 - r) * r + 36 * Real.log (1 + r) * r + 60 * Real.log r * r) * Li₂ (i15WuX2 r u)
        +
    (-72 * r + 54 * r⁻¹ - 36 * Real.log (1 + r) * r - 12 * Real.log (1 - r) * r⁻¹ + 12 * Real.log
        (1 - r) * r + 24 * Real.log (1 + r) * r⁻¹) * Li₂ (i15WuX3 r u) +
    (-72 * r - 36 * r⁻¹ - 84 * Real.log r * r⁻¹ - 60 * Real.log (1 + r) * r - 12 * Real.log (1 - r)
        * r - 12 * Real.log (1 + r) * r⁻¹ + 12 * Real.log (1 - r) * r⁻¹ + 132 * Real.log r * r) *
        Li₂ (i15WuX4 r u) +
    (-54 * r⁻¹ + 36 * r - 72 * Real.log r * r⁻¹ - 48 * Real.log (1 + r) * r⁻¹ - 12 * Real.log (1 -
        r) * r⁻¹ + 12 * Real.log (1 - r) * r + 36 * Real.log (1 + r) * r + 144 * Real.log r * r) *
        Li₂ (i15WuX5 r u) +
    (18 * r⁻¹ + 36 * r - 96 * Real.log (1 - r) * r⁻¹ - 84 * Real.log (1 + r) * r⁻¹ - 36 * Real.log
        r * r + 36 * Real.log r * r⁻¹ + 96 * Real.log (1 - r) * r + 120 * Real.log (1 + r) * r) *
        Li₂ (i15WuX6 r u)

theorem i15Wu_pos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    0 < r ∧ 0 < u ∧ 0 < 1 - r ∧ 0 < 1 + r ∧ 0 < r + u ∧ 0 < 1 + r * u ∧ 0 < 1 + u / r := by
  obtain ⟨h0, h1⟩ := hr
  refine ⟨h0, hu, by linarith, by linarith, by linarith, by positivity, by positivity⟩

theorem i15WuX0_pos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : 0 < i15WuX0 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX0
  positivity

theorem i15WuX1_pos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : 0 < i15WuX1 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX1
  positivity

theorem i15WuX2_pos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : 0 < i15WuX2 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX2
  positivity

theorem i15WuX3_pos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : 0 < i15WuX3 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX3
  positivity

theorem i15WuX4_pos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : 0 < i15WuX4 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX4
  positivity

theorem i15WuX5_pos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : 0 < i15WuX5 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX5
  positivity

theorem i15WuX6_pos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : 0 < i15WuX6 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX6
  positivity

theorem i15WuX7_pos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : 0 < i15WuX7 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX7
  positivity

theorem i15WuX0_one_sub {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    1 - i15WuX0 r u = i15WuX1 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX0 i15WuX1
  field_simp
  try ring

theorem i15WuX0_log {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    log (i15WuX0 r u) = -i15WuA r u + i15WuB r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  rw [← exp_eq_exp, exp_log (i15WuX0_pos hr hu)]
  simp only [i15WuX0, i15WuA, i15WuB, exp_add, exp_neg, exp_log h5, exp_log h6]
  field_simp

theorem i15WuX0_mem {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    i15WuX0 r u ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15WuX0_pos hr hu, by linarith [i15WuX0_one_sub hr hu, i15WuX1_pos hr hu]⟩

theorem i15WuX1_one_sub {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    1 - i15WuX1 r u = i15WuX0 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX1 i15WuX0
  field_simp
  try ring

theorem i15WuX1_log {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    log (i15WuX1 r u) = Real.log u + -i15WuA r u + (-Real.log r + Real.log (1 + r) + Real.log (1 -
        r)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  rw [← exp_eq_exp, exp_log (i15WuX1_pos hr hu)]
  simp only [i15WuX1, i15WuA, exp_add, exp_neg, exp_log h0, exp_log h1, exp_log h2, exp_log h3,
      exp_log h6]
  field_simp

theorem i15WuX1_mem {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    i15WuX1 r u ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15WuX1_pos hr hu, by linarith [i15WuX1_one_sub hr hu, i15WuX0_pos hr hu]⟩

theorem i15WuX2_one_sub {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    1 - i15WuX2 r u = i15WuX3 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX2 i15WuX3
  field_simp
  try ring

theorem i15WuX2_log {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    log (i15WuX2 r u) = -i15WuA r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  rw [← exp_eq_exp, exp_log (i15WuX2_pos hr hu)]
  simp only [i15WuX2, i15WuA, exp_neg, exp_log h6]
  field_simp

theorem i15WuX2_mem {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    i15WuX2 r u ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15WuX2_pos hr hu, by linarith [i15WuX2_one_sub hr hu, i15WuX3_pos hr hu]⟩

theorem i15WuX3_one_sub {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    1 - i15WuX3 r u = i15WuX2 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX3 i15WuX2
  field_simp
  try ring

theorem i15WuX3_log {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    log (i15WuX3 r u) = Real.log u + -i15WuA r u + (-Real.log r) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  rw [← exp_eq_exp, exp_log (i15WuX3_pos hr hu)]
  simp only [i15WuX3, i15WuA, exp_add, exp_neg, exp_log h0, exp_log h1, exp_log h6]
  field_simp

theorem i15WuX3_mem {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    i15WuX3 r u ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15WuX3_pos hr hu, by linarith [i15WuX3_one_sub hr hu, i15WuX2_pos hr hu]⟩

theorem i15WuX4_one_sub {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    1 - i15WuX4 r u = i15WuX5 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX4 i15WuX5
  field_simp
  try ring

theorem i15WuX4_log {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    log (i15WuX4 r u) = -i15WuB r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  rw [← exp_eq_exp, exp_log (i15WuX4_pos hr hu)]
  simp only [i15WuX4, i15WuB, exp_neg, exp_log h5]
  field_simp

theorem i15WuX4_mem {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    i15WuX4 r u ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15WuX4_pos hr hu, by linarith [i15WuX4_one_sub hr hu, i15WuX5_pos hr hu]⟩

theorem i15WuX5_one_sub {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    1 - i15WuX5 r u = i15WuX4 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX5 i15WuX4
  field_simp
  try ring

theorem i15WuX5_log {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    log (i15WuX5 r u) = Real.log u + -i15WuB r u + (Real.log r) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  rw [← exp_eq_exp, exp_log (i15WuX5_pos hr hu)]
  simp only [i15WuX5, i15WuB, exp_add, exp_neg, exp_log h0, exp_log h1, exp_log h5]
  field_simp

theorem i15WuX5_mem {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    i15WuX5 r u ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15WuX5_pos hr hu, by linarith [i15WuX5_one_sub hr hu, i15WuX4_pos hr hu]⟩

theorem i15WuX6_one_sub {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    1 - i15WuX6 r u = i15WuX7 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX6 i15WuX7
  field_simp
  try ring

theorem i15WuX6_log {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    log (i15WuX6 r u) = -i15WuB r u + (Real.log (1 + r) + Real.log (1 - r)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  rw [← exp_eq_exp, exp_log (i15WuX6_pos hr hu)]
  simp only [i15WuX6, i15WuB, exp_add, exp_neg, exp_log h2, exp_log h3, exp_log h5]
  field_simp

theorem i15WuX6_mem {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    i15WuX6 r u ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15WuX6_pos hr hu, by linarith [i15WuX6_one_sub hr hu, i15WuX7_pos hr hu]⟩

theorem i15WuX7_one_sub {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    1 - i15WuX7 r u = i15WuX6 r u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  unfold i15WuX7 i15WuX6
  field_simp
  try ring

theorem i15WuX7_log {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    log (i15WuX7 r u) = i15WuA r u + -i15WuB r u + (Real.log r + Real.log r) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  rw [← exp_eq_exp, exp_log (i15WuX7_pos hr hu)]
  simp only [i15WuX7, i15WuA, i15WuB, exp_add, exp_neg, exp_log h0, exp_log h5, exp_log h6]
  field_simp

theorem i15WuX7_mem {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    i15WuX7 r u ∈ Ioo (0 : ℝ) 1 :=
  ⟨i15WuX7_pos hr hu, by linarith [i15WuX7_one_sub hr hu, i15WuX6_pos hr hu]⟩

theorem hasDerivAt_i15WuPhi {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    HasDerivAt (i15WuPhi r) (i15WuF r u) u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  have hLu : HasDerivAt (fun t => log t) u⁻¹ u := hasDerivAt_log h1.ne'
  have hLa : HasDerivAt (fun t => i15WuA r t) (r + u)⁻¹ u := by
    have h := (((hasDerivAt_id u).div_const r).const_add 1).log h6.ne'
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hLb : HasDerivAt (fun t => i15WuB r t) (r * (1 + r * u)⁻¹) u := by
    have h := (((hasDerivAt_id u).const_mul r).const_add 1).log h5.ne'
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hP := hasDerivAt_i15TPoly (i15WuP r) hLu hLa hLb (hasDerivAt_const u (0 : ℝ))
  have hX0 := i15T_hasDerivAt_of_log (X := i15WuX0 r) (ℓ := fun t => -i15WuA r t + i15WuB r t)
    (Ioi_mem_nhds hu) (fun t ht => ⟨i15WuX0_pos hr ht, i15WuX0_log hr ht⟩) (hLa.neg.add hLb)
  have hS0 : log (1 - i15WuX0 r u) = Real.log u + -i15WuA r u + (-Real.log r + Real.log (1 + r) +
      Real.log (1 - r)) := by
    rw [i15WuX0_one_sub hr hu]; exact i15WuX1_log hr hu
  have hG0 := (hasDerivAt_i15TG_comp hX0 (i15WuX0_mem hr hu) (i15WuX0_log hr hu) hS0).const_mul
    (-24 * r)
  have hL0 := (hasDerivAt_i15TLi₂_comp hX0 (i15WuX0_mem hr hu) hS0).const_mul
    (-60 * Real.log r * r + 12 * Real.log r * r⁻¹)
  have hX1 := i15T_hasDerivAt_of_log (X := i15WuX1 r) (ℓ := fun t => Real.log t + -i15WuA r t +
      (-Real.log r + Real.log (1 + r) + Real.log (1 - r)))
    (Ioi_mem_nhds hu) (fun t ht => ⟨i15WuX1_pos hr ht, i15WuX1_log hr ht⟩) ((hLu.add
        hLa.neg).add_const (-Real.log r + Real.log (1 + r) + Real.log (1 - r)))
  have hS1 : log (1 - i15WuX1 r u) = -i15WuA r u + i15WuB r u := by
    rw [i15WuX1_one_sub hr hu]; exact i15WuX0_log hr hu
  have hG1 := (hasDerivAt_i15TG_comp hX1 (i15WuX1_mem hr hu) (i15WuX1_log hr hu) hS1).const_mul
    (-24 * r + 24 * r⁻¹)
  have hL1 := (hasDerivAt_i15TLi₂_comp hX1 (i15WuX1_mem hr hu) hS1).const_mul
    (-54 * r⁻¹ + 108 * r - 36 * Real.log (1 + r) * r⁻¹ + 72 * Real.log (1 + r) * r)
  have hX2 := i15T_hasDerivAt_of_log (X := i15WuX2 r) (ℓ := fun t => -i15WuA r t)
    (Ioi_mem_nhds hu) (fun t ht => ⟨i15WuX2_pos hr ht, i15WuX2_log hr ht⟩) hLa.neg
  have hS2 : log (1 - i15WuX2 r u) = Real.log u + -i15WuA r u + (-Real.log r) := by
    rw [i15WuX2_one_sub hr hu]; exact i15WuX3_log hr hu
  have hG2 := (hasDerivAt_i15TG_comp hX2 (i15WuX2_mem hr hu) (i15WuX2_log hr hu) hS2).const_mul
    (36 * r)
  have hL2 := (hasDerivAt_i15TLi₂_comp hX2 (i15WuX2_mem hr hu) hS2).const_mul
    (-36 * Real.log (1 - r) * r⁻¹ - 36 * Real.log (1 + r) * r⁻¹ - 12 * Real.log r * r⁻¹ + 36 *
        Real.log (1 - r) * r + 36 * Real.log (1 + r) * r + 60 * Real.log r * r)
  have hX3 := i15T_hasDerivAt_of_log (X := i15WuX3 r) (ℓ := fun t => Real.log t + -i15WuA r t +
      (-Real.log r))
    (Ioi_mem_nhds hu) (fun t ht => ⟨i15WuX3_pos hr ht, i15WuX3_log hr ht⟩) ((hLu.add
        hLa.neg).add_const (-Real.log r))
  have hS3 : log (1 - i15WuX3 r u) = -i15WuA r u := by
    rw [i15WuX3_one_sub hr hu]; exact i15WuX2_log hr hu
  have hG3 := (hasDerivAt_i15TG_comp hX3 (i15WuX3_mem hr hu) (i15WuX3_log hr hu) hS3).const_mul
    (-24 * r⁻¹ + 12 * r)
  have hL3 := (hasDerivAt_i15TLi₂_comp hX3 (i15WuX3_mem hr hu) hS3).const_mul
    (-72 * r + 54 * r⁻¹ - 36 * Real.log (1 + r) * r - 12 * Real.log (1 - r) * r⁻¹ + 12 * Real.log
        (1 - r) * r + 24 * Real.log (1 + r) * r⁻¹)
  have hX4 := i15T_hasDerivAt_of_log (X := i15WuX4 r) (ℓ := fun t => -i15WuB r t)
    (Ioi_mem_nhds hu) (fun t ht => ⟨i15WuX4_pos hr ht, i15WuX4_log hr ht⟩) hLb.neg
  have hS4 : log (1 - i15WuX4 r u) = Real.log u + -i15WuB r u + (Real.log r) := by
    rw [i15WuX4_one_sub hr hu]; exact i15WuX5_log hr hu
  have hG4 := (hasDerivAt_i15TG_comp hX4 (i15WuX4_mem hr hu) (i15WuX4_log hr hu) hS4).const_mul
    (36 * r⁻¹)
  have hL4 := (hasDerivAt_i15TLi₂_comp hX4 (i15WuX4_mem hr hu) hS4).const_mul
    (-72 * r - 36 * r⁻¹ - 84 * Real.log r * r⁻¹ - 60 * Real.log (1 + r) * r - 12 * Real.log (1 - r)
        * r - 12 * Real.log (1 + r) * r⁻¹ + 12 * Real.log (1 - r) * r⁻¹ + 132 * Real.log r * r)
  have hX5 := i15T_hasDerivAt_of_log (X := i15WuX5 r) (ℓ := fun t => Real.log t + -i15WuB r t +
      (Real.log r))
    (Ioi_mem_nhds hu) (fun t ht => ⟨i15WuX5_pos hr ht, i15WuX5_log hr ht⟩) ((hLu.add
        hLb.neg).add_const (Real.log r))
  have hS5 : log (1 - i15WuX5 r u) = -i15WuB r u := by
    rw [i15WuX5_one_sub hr hu]; exact i15WuX4_log hr hu
  have hG5 := (hasDerivAt_i15TG_comp hX5 (i15WuX5_mem hr hu) (i15WuX5_log hr hu) hS5).const_mul
    (-24 * r + 12 * r⁻¹)
  have hL5 := (hasDerivAt_i15TLi₂_comp hX5 (i15WuX5_mem hr hu) hS5).const_mul
    (-54 * r⁻¹ + 36 * r - 72 * Real.log r * r⁻¹ - 48 * Real.log (1 + r) * r⁻¹ - 12 * Real.log (1 -
        r) * r⁻¹ + 12 * Real.log (1 - r) * r + 36 * Real.log (1 + r) * r + 144 * Real.log r * r)
  have hX6 := i15T_hasDerivAt_of_log (X := i15WuX6 r) (ℓ := fun t => -i15WuB r t + (Real.log (1 +
      r) + Real.log (1 - r)))
    (Ioi_mem_nhds hu) (fun t ht => ⟨i15WuX6_pos hr ht, i15WuX6_log hr ht⟩) (hLb.neg.add_const
        (Real.log (1 + r) + Real.log (1 - r)))
  have hS6 : log (1 - i15WuX6 r u) = i15WuA r u + -i15WuB r u + (Real.log r + Real.log r) := by
    rw [i15WuX6_one_sub hr hu]; exact i15WuX7_log hr hu
  have hG6 := (hasDerivAt_i15TG_comp hX6 (i15WuX6_mem hr hu) (i15WuX6_log hr hu) hS6).const_mul
    (-72 * r⁻¹ + 72 * r)
  have hL6 := (hasDerivAt_i15TLi₂_comp hX6 (i15WuX6_mem hr hu) hS6).const_mul
    (18 * r⁻¹ + 36 * r - 96 * Real.log (1 - r) * r⁻¹ - 84 * Real.log (1 + r) * r⁻¹ - 36 * Real.log
        r * r + 36 * Real.log r * r⁻¹ + 96 * Real.log (1 - r) * r + 120 * Real.log (1 + r) * r)
  have hX7 := i15T_hasDerivAt_of_log (X := i15WuX7 r) (ℓ := fun t => i15WuA r t + -i15WuB r t +
      (Real.log r + Real.log r))
    (Ioi_mem_nhds hu) (fun t ht => ⟨i15WuX7_pos hr ht, i15WuX7_log hr ht⟩) ((hLa.add
        hLb.neg).add_const (Real.log r + Real.log r))
  have hS7 : log (1 - i15WuX7 r u) = -i15WuB r u + (Real.log (1 + r) + Real.log (1 - r)) := by
    rw [i15WuX7_one_sub hr hu]; exact i15WuX6_log hr hu
  have hG7 := (hasDerivAt_i15TG_comp hX7 (i15WuX7_mem hr hu) (i15WuX7_log hr hu) hS7).const_mul
    (-24 * r⁻¹ + 48 * r)
  have h := (((((((((((((((hP.add hG0).add hG1).add hG2).add hG3).add hG4).add hG5).add hG6).add
      hG7).add hL0).add hL1).add hL2).add hL3).add hL4).add hL5).add hL6)
  refine HasDerivAt.congr_deriv (f := i15WuPhi r) h ?_
  have eu : u * u⁻¹ = 1 := by field_simp
  have ea : u * (r + u)⁻¹ = 1 - r * (r + u)⁻¹ := by field_simp; ring
  have eb : r * u * (1 + r * u)⁻¹ = 1 - (1 + r * u)⁻¹ := by field_simp; ring
  have er : r * r⁻¹ = 1 := by field_simp
  simp only [i15WuP, i15TPolyD, i15TMonoD, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.reduceSub, i15WuF]
  linear_combination (60 - 36 * i15WuA r u - 36 * i15WuB r u - 12 * Real.log r + 6 * Real.log u ^ 2
      + 6 * Real.log r ^ 2 + 12 * Real.log u + 12 * i15WuA r u ^ 2 + 12 * i15WuB r u ^ 2 + 24 *
      Real.log (1 + r) + 24 * Real.log (1 + r) ^ 2 - 24 * i15WuA r u * Real.log (1 + r) - 24 *
      i15WuB r u * Real.log (1 + r) - 24 * Real.log (1 + r) * Real.log r - 12 * i15WuA r u *
      Real.log u - 12 * i15WuB r u * Real.log u - 12 * Real.log u * Real.log r + 12 * i15WuA r u *
      Real.log r + 12 * i15WuB r u * Real.log r + 24 * i15WuA r u * i15WuB r u + 24 * Real.log u *
      Real.log (1 + r)) * eu + (-108 - 72 * Real.log (1 + r) - 36 * Real.log u - 24 * i15WuA r u ^
      2 - 24 * i15WuB r u ^ 2 - 24 * Real.log (1 + r) ^ 2 - 6 * Real.log u ^ 2 - 6 * Real.log r ^ 2
      + 36 * Real.log r + 72 * i15WuA r u + 72 * i15WuB r u - 48 * i15WuA r u * i15WuB r u - 24 *
      i15WuA r u * Real.log r - 24 * i15WuB r u * Real.log r - 24 * Real.log u * Real.log (1 + r) +
      12 * Real.log u * Real.log r + 24 * i15WuA r u * Real.log u + 24 * i15WuB r u * Real.log u +
      24 * Real.log (1 + r) * Real.log r + 48 * i15WuA r u * Real.log (1 + r) + 48 * i15WuB r u *
      Real.log (1 + r)) * ea + (-108 - 72 * Real.log (1 + r) - 36 * Real.log u - 24 * i15WuA r u ^
      2 - 24 * i15WuB r u ^ 2 - 24 * Real.log (1 + r) ^ 2 - 6 * Real.log u ^ 2 - 6 * Real.log r ^ 2
      + 36 * Real.log r + 72 * i15WuA r u + 72 * i15WuB r u - 48 * i15WuA r u * i15WuB r u - 24 *
      i15WuA r u * Real.log r - 24 * i15WuB r u * Real.log r - 24 * Real.log u * Real.log (1 + r) +
      12 * Real.log u * Real.log r + 24 * i15WuA r u * Real.log u + 24 * i15WuB r u * Real.log u +
      24 * Real.log (1 + r) * Real.log r + 48 * i15WuA r u * Real.log (1 + r) + 48 * i15WuB r u *
      Real.log (1 + r)) * eb + (-108 * (1 + r * u)⁻¹ - 72 * Real.log (1 + r) * (1 + r * u)⁻¹ - 36 *
      Real.log u * (1 + r * u)⁻¹ - 24 * (1 + r * u)⁻¹ * i15WuA r u ^ 2 - 24 * (1 + r * u)⁻¹ *
      i15WuB r u ^ 2 - 24 * (1 + r * u)⁻¹ * Real.log (1 + r) ^ 2 - 6 * (1 + r * u)⁻¹ * Real.log u ^
      2 - 6 * (1 + r * u)⁻¹ * Real.log r ^ 2 + 36 * Real.log r * (1 + r * u)⁻¹ + 72 * i15WuA r u *
      (1 + r * u)⁻¹ + 72 * i15WuB r u * (1 + r * u)⁻¹ - 48 * i15WuA r u * i15WuB r u * (1 + r *
      u)⁻¹ - 24 * i15WuA r u * Real.log r * (1 + r * u)⁻¹ - 24 * i15WuB r u * Real.log r * (1 + r *
      u)⁻¹ - 24 * Real.log u * Real.log (1 + r) * (1 + r * u)⁻¹ + 12 * Real.log u * Real.log r * (1
      + r * u)⁻¹ + 24 * i15WuA r u * Real.log u * (1 + r * u)⁻¹ + 24 * i15WuB r u * Real.log u * (1
      + r * u)⁻¹ + 24 * Real.log (1 + r) * Real.log r * (1 + r * u)⁻¹ + 48 * i15WuA r u * Real.log
      (1 + r) * (1 + r * u)⁻¹ + 48 * i15WuB r u * Real.log (1 + r) * (1 + r * u)⁻¹) * er

/-- The value of the primitive at `0⁺`. -/
noncomputable def i15WuPhi0 (r : ℝ) : ℝ :=
  i15TPoly (i15WuP r) 0 1 0 0 0 +
    (-24 * r) * i15TG (i15WuX0 r 0) +
    (-24 * r + 24 * r⁻¹) * i15TG (i15WuX1 r 0) +
    (36 * r) * i15TG (i15WuX2 r 0) +
    (-24 * r⁻¹ + 12 * r) * i15TG (i15WuX3 r 0) +
    (36 * r⁻¹) * i15TG (i15WuX4 r 0) +
    (-24 * r + 12 * r⁻¹) * i15TG (i15WuX5 r 0) +
    (-72 * r⁻¹ + 72 * r) * i15TG (i15WuX6 r 0) +
    (-24 * r⁻¹ + 48 * r) * i15TG (i15WuX7 r 0) +
    (-60 * Real.log r * r + 12 * Real.log r * r⁻¹) * Li₂ (i15WuX0 r 0) +
    (-54 * r⁻¹ + 108 * r - 36 * Real.log (1 + r) * r⁻¹ + 72 * Real.log (1 + r) * r) * Li₂ (i15WuX1
        r 0) +
    (-36 * Real.log (1 - r) * r⁻¹ - 36 * Real.log (1 + r) * r⁻¹ - 12 * Real.log r * r⁻¹ + 36 *
        Real.log (1 - r) * r + 36 * Real.log (1 + r) * r + 60 * Real.log r * r) * Li₂ (i15WuX2 r 0)
        +
    (-72 * r + 54 * r⁻¹ - 36 * Real.log (1 + r) * r - 12 * Real.log (1 - r) * r⁻¹ + 12 * Real.log
        (1 - r) * r + 24 * Real.log (1 + r) * r⁻¹) * Li₂ (i15WuX3 r 0) +
    (-72 * r - 36 * r⁻¹ - 84 * Real.log r * r⁻¹ - 60 * Real.log (1 + r) * r - 12 * Real.log (1 - r)
        * r - 12 * Real.log (1 + r) * r⁻¹ + 12 * Real.log (1 - r) * r⁻¹ + 132 * Real.log r * r) *
        Li₂ (i15WuX4 r 0) +
    (-54 * r⁻¹ + 36 * r - 72 * Real.log r * r⁻¹ - 48 * Real.log (1 + r) * r⁻¹ - 12 * Real.log (1 -
        r) * r⁻¹ + 12 * Real.log (1 - r) * r + 36 * Real.log (1 + r) * r + 144 * Real.log r * r) *
        Li₂ (i15WuX5 r 0) +
    (18 * r⁻¹ + 36 * r - 96 * Real.log (1 - r) * r⁻¹ - 84 * Real.log (1 + r) * r⁻¹ - 36 * Real.log
        r * r + 36 * Real.log r * r⁻¹ + 96 * Real.log (1 - r) * r + 120 * Real.log (1 + r) * r) *
        Li₂ (i15WuX6 r 0)

theorem i15WuX0_zero {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : i15WuX0 r 0 = 1 := by
  simp only [i15WuX0, mul_zero, add_zero, mul_one]
  exact div_self hr.1.ne'

theorem continuousAt_i15WuX0 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : ContinuousAt (i15WuX0 r) 0 := by
  unfold i15WuX0
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hr.1.ne')

theorem i15WuX1_zero (r : ℝ) : i15WuX1 r 0 = 0 := by
  simp [i15WuX1]

theorem continuousAt_i15WuX1 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : ContinuousAt (i15WuX1 r) 0 := by
  unfold i15WuX1
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hr.1.ne')

theorem i15WuX2_zero {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : i15WuX2 r 0 = 1 := by
  simp only [i15WuX2, add_zero]
  exact div_self hr.1.ne'

theorem continuousAt_i15WuX2 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : ContinuousAt (i15WuX2 r) 0 := by
  unfold i15WuX2
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hr.1.ne')

theorem i15WuX3_zero (r : ℝ) : i15WuX3 r 0 = 0 := by
  simp [i15WuX3]

theorem continuousAt_i15WuX3 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : ContinuousAt (i15WuX3 r) 0 := by
  unfold i15WuX3
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hr.1.ne')

theorem i15WuX4_zero (r : ℝ) : i15WuX4 r 0 = 1 := by
  simp [i15WuX4]

theorem continuousAt_i15WuX4 (r : ℝ) : ContinuousAt (i15WuX4 r) 0 := by
  unfold i15WuX4
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)

theorem i15WuX5_zero (r : ℝ) : i15WuX5 r 0 = 0 := by
  simp [i15WuX5]

theorem continuousAt_i15WuX5 (r : ℝ) : ContinuousAt (i15WuX5 r) 0 := by
  unfold i15WuX5
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)

theorem i15WuX6_zero (r : ℝ) : i15WuX6 r 0 = (1 - r) * (1 + r) := by
  simp [i15WuX6]

theorem continuousAt_i15WuX6 (r : ℝ) : ContinuousAt (i15WuX6 r) 0 := by
  unfold i15WuX6
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)

theorem i15WuX7_zero (r : ℝ) : i15WuX7 r 0 = r ^ 2 := by
  simp only [i15WuX7, add_zero, mul_zero, div_one]
  ring

theorem continuousAt_i15WuX7 (r : ℝ) : ContinuousAt (i15WuX7 r) 0 := by
  unfold i15WuX7
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)

theorem i15Wu_val_mem {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (1 - r) * (1 + r) ∈ Ioc (0 : ℝ) 1 ∧ r ^ 2 ∈ Ioc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hr
  exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by positivity, by nlinarith⟩⟩

theorem tendsto_i15WuPhi_zero {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i15WuPhi r) (𝓝[>] 0) (𝓝 (i15WuPhi0 r)) := by
  have h0 := hr.1
  have h1 := hr.2
  have hm := i15Wu_val_mem hr
  have hA : ∀ u ∈ Ioo (0 : ℝ) 1, |i15WuA r u| ≤ (r⁻¹ + r) * u := fun u hu => by
    have h := abs_log_one_add_le (x := u / r) (div_nonneg hu.1.le h0.le)
    unfold i15WuA
    refine h.trans ?_
    rw [div_eq_inv_mul]
    nlinarith [hu.1]
  have hB : ∀ u ∈ Ioo (0 : ℝ) 1, |i15WuB r u| ≤ (r⁻¹ + r) * u := fun u hu => by
    have h := abs_log_one_add_le (x := r * u) (by nlinarith [hu.1])
    unfold i15WuB
    refine h.trans ?_
    have : 0 ≤ r⁻¹ * u := by have := hu.1; positivity
    nlinarith
  have hC : ∀ u ∈ Ioo (0 : ℝ) 1, |(fun _ : ℝ => (0 : ℝ)) u| ≤ (r⁻¹ + r) * u := fun u hu => by
    simp only [abs_zero]; have := hu.1; positivity
  have hP := tendsto_i15TPoly_zero' (i15WuP r) hA hB hC
    (by simp only [i15WuP, List.map_cons, List.map_nil]; decide)
  have hX0 := continuousAt_i15WuX0 ⟨h0, h1⟩
  have hz0 := i15WuX0_zero ⟨h0, h1⟩
  have hG0 := i15T_tendsto_TG hX0 (by rw [hz0]; exact ⟨one_pos, le_rfl⟩)
    fun u hu => i15WuX0_mem ⟨h0, h1⟩ hu.1
  have hL0 := i15T_tendsto_Li₂ hX0 (by rw [hz0]; exact ⟨zero_le_one, le_rfl⟩)
    fun u hu => i15WuX0_mem ⟨h0, h1⟩ hu.1
  have hX1 := continuousAt_i15WuX1 ⟨h0, h1⟩
  have hz1 := i15WuX1_zero r
  have hG1 : Tendsto (fun u => i15TG (i15WuX1 r u)) (𝓝[>] 0) (𝓝 (i15TG (i15WuX1 r 0))) := by
    rw [hz1, show i15TG 0 = 0 by simp [i15TG]]
    exact i15T_tendsto_TG_zero hX1 hz1 fun u hu => i15WuX1_mem ⟨h0, h1⟩ hu.1
  have hL1 := i15T_tendsto_Li₂ hX1 (by rw [hz1]; exact ⟨le_rfl, zero_le_one⟩)
    fun u hu => i15WuX1_mem ⟨h0, h1⟩ hu.1
  have hX2 := continuousAt_i15WuX2 ⟨h0, h1⟩
  have hz2 := i15WuX2_zero ⟨h0, h1⟩
  have hG2 := i15T_tendsto_TG hX2 (by rw [hz2]; exact ⟨one_pos, le_rfl⟩)
    fun u hu => i15WuX2_mem ⟨h0, h1⟩ hu.1
  have hL2 := i15T_tendsto_Li₂ hX2 (by rw [hz2]; exact ⟨zero_le_one, le_rfl⟩)
    fun u hu => i15WuX2_mem ⟨h0, h1⟩ hu.1
  have hX3 := continuousAt_i15WuX3 ⟨h0, h1⟩
  have hz3 := i15WuX3_zero r
  have hG3 : Tendsto (fun u => i15TG (i15WuX3 r u)) (𝓝[>] 0) (𝓝 (i15TG (i15WuX3 r 0))) := by
    rw [hz3, show i15TG 0 = 0 by simp [i15TG]]
    exact i15T_tendsto_TG_zero hX3 hz3 fun u hu => i15WuX3_mem ⟨h0, h1⟩ hu.1
  have hL3 := i15T_tendsto_Li₂ hX3 (by rw [hz3]; exact ⟨le_rfl, zero_le_one⟩)
    fun u hu => i15WuX3_mem ⟨h0, h1⟩ hu.1
  have hX4 := continuousAt_i15WuX4 r
  have hz4 := i15WuX4_zero r
  have hG4 := i15T_tendsto_TG hX4 (by rw [hz4]; exact ⟨one_pos, le_rfl⟩)
    fun u hu => i15WuX4_mem ⟨h0, h1⟩ hu.1
  have hL4 := i15T_tendsto_Li₂ hX4 (by rw [hz4]; exact ⟨zero_le_one, le_rfl⟩)
    fun u hu => i15WuX4_mem ⟨h0, h1⟩ hu.1
  have hX5 := continuousAt_i15WuX5 r
  have hz5 := i15WuX5_zero r
  have hG5 : Tendsto (fun u => i15TG (i15WuX5 r u)) (𝓝[>] 0) (𝓝 (i15TG (i15WuX5 r 0))) := by
    rw [hz5, show i15TG 0 = 0 by simp [i15TG]]
    exact i15T_tendsto_TG_zero hX5 hz5 fun u hu => i15WuX5_mem ⟨h0, h1⟩ hu.1
  have hL5 := i15T_tendsto_Li₂ hX5 (by rw [hz5]; exact ⟨le_rfl, zero_le_one⟩)
    fun u hu => i15WuX5_mem ⟨h0, h1⟩ hu.1
  have hX6 := continuousAt_i15WuX6 r
  have hz6 := i15WuX6_zero r
  have hG6 := i15T_tendsto_TG hX6 (by rw [hz6]; exact hm.1)
    fun u hu => i15WuX6_mem ⟨h0, h1⟩ hu.1
  have hL6 := i15T_tendsto_Li₂ hX6 (by rw [hz6]; exact ⟨hm.1.1.le, hm.1.2⟩)
    fun u hu => i15WuX6_mem ⟨h0, h1⟩ hu.1
  have hX7 := continuousAt_i15WuX7 r
  have hz7 := i15WuX7_zero r
  have hG7 := i15T_tendsto_TG hX7 (by rw [hz7]; exact hm.2)
    fun u hu => i15WuX7_mem ⟨h0, h1⟩ hu.1
  exact (((((((((((((((hP.add (hG0.const_mul (-24 * r))).add (hG1.const_mul (-24 * r + 24 *
      r⁻¹))).add (hG2.const_mul (36 * r))).add (hG3.const_mul (-24 * r⁻¹ + 12 * r))).add
      (hG4.const_mul (36 * r⁻¹))).add (hG5.const_mul (-24 * r + 12 * r⁻¹))).add (hG6.const_mul (-72
      * r⁻¹ + 72 * r))).add (hG7.const_mul (-24 * r⁻¹ + 48 * r))).add (hL0.const_mul (-60 *
      Real.log r * r + 12 * Real.log r * r⁻¹))).add (hL1.const_mul (-54 * r⁻¹ + 108 * r - 36 *
      Real.log (1 + r) * r⁻¹ + 72 * Real.log (1 + r) * r))).add (hL2.const_mul (-36 * Real.log (1 -
      r) * r⁻¹ - 36 * Real.log (1 + r) * r⁻¹ - 12 * Real.log r * r⁻¹ + 36 * Real.log (1 - r) * r +
      36 * Real.log (1 + r) * r + 60 * Real.log r * r))).add (hL3.const_mul (-72 * r + 54 * r⁻¹ -
      36 * Real.log (1 + r) * r - 12 * Real.log (1 - r) * r⁻¹ + 12 * Real.log (1 - r) * r + 24 *
      Real.log (1 + r) * r⁻¹))).add (hL4.const_mul (-72 * r - 36 * r⁻¹ - 84 * Real.log r * r⁻¹ - 60
      * Real.log (1 + r) * r - 12 * Real.log (1 - r) * r - 12 * Real.log (1 + r) * r⁻¹ + 12 *
      Real.log (1 - r) * r⁻¹ + 132 * Real.log r * r))).add (hL5.const_mul (-54 * r⁻¹ + 36 * r - 72
      * Real.log r * r⁻¹ - 48 * Real.log (1 + r) * r⁻¹ - 12 * Real.log (1 - r) * r⁻¹ + 12 *
      Real.log (1 - r) * r + 36 * Real.log (1 + r) * r + 144 * Real.log r * r))).add (hL6.const_mul
      (18 * r⁻¹ + 36 * r - 96 * Real.log (1 - r) * r⁻¹ - 84 * Real.log (1 + r) * r⁻¹ - 36 *
      Real.log r * r + 36 * Real.log r * r⁻¹ + 96 * Real.log (1 - r) * r + 120 * Real.log (1 + r) *
      r)))

theorem i15WuF_nonpos {r u : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) : i15WuF r u ≤ 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := i15Wu_pos hr hu
  have key : u * (1 + r) ^ 2 ≤ r * (1 + u / r) * (1 + r * u) := by
    have e : r * (1 + u / r) = r + u := by field_simp
    rw [e]
    nlinarith [sq_nonneg (1 - u), mul_nonneg h0.le (sq_nonneg (1 - u))]
  have hl := log_le_log (by positivity) key
  rw [log_mul h1.ne' (by positivity), log_pow, log_mul (mul_pos h0 h6).ne' h5.ne',
    log_mul h0.ne' h6.ne'] at hl
  unfold i15WuF
  set x := -log r + log u + 2 * log (1 + r) - 2 * i15WuA r u - 2 * i15WuB r u
  set y := log r - 2 * log (1 + r) - log u
  have hxy : x ≤ y := by
    simp only [x, y, i15WuA, i15WuB]
    push_cast at hl
    linarith
  have e : x ^ 3 - y ^ 3 = (x - y) * ((x + y / 2) ^ 2 + 3 / 4 * y ^ 2) := by ring
  rw [e]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- **`∫₀¹ (b₁³ - b₂³) du = Φ(1) - Φ(0⁺)`**, with integrability. -/
theorem integral_i15WuF {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (i15WuF r) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, i15WuF r u = i15WuPhi r 1 - i15WuPhi0 r :=
  intervalIntegrable_and_integral_eq_of_nonpos' zero_lt_one
    (fun _ hu => hasDerivAt_i15WuPhi hr hu.1) (fun _ hu => i15WuF_nonpos hr hu.1)
    (tendsto_i15WuPhi_zero hr)
    ((hasDerivAt_i15WuPhi hr one_pos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

end QED.ThreeLoopD
