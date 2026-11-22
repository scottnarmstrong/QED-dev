/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighPt

/-!
# Set (d), master `I₁₂`: the reflection between the two sectors of the bulk remainder

The two sectors `t < v` (`v = ρ`, `t = ρθ`) and `v < t` (`t = ρ`, `v = ρθ`) of the bulk part
`S = R₁ + R_A + R_B` of the remainder of `I₁₂` are two charts of one integrand on the square
`(v, t) ∈ (0, 1)²`. In the chart of the sector `t < v` the sector `v < t` is the region `θ > 1`:
the map `(ρ, θ) ↦ (ρθ, θ⁻¹)` carries the main term of `R_B` onto the main term of `R_A`,
continued past the sector boundary `θ = 1`. This holds for every `ε` (by the homogeneity of
`Φ₀` of degree `-3ε`), hence at every order:

* `QED.ThreeLoopD.i12Phi0_mul_mul`: `Φ₀(λX, λY) = λ^{-3ε} Φ₀(X, Y)`;
* `QED.ThreeLoopD.i12GA_reflect`: `G_A(ρθ, θ⁻¹, u) = θ^{3ε} G_B(ρ, θ, u)`, and
  `QED.ThreeLoopD.i12GA_zero_reflect` for the faces `ρ = 0`;
* `QED.ThreeLoopD.i12RA3Dn_eq_main_add_face`, `QED.ThreeLoopD.i12RB3Dn_eq_main_add_face`:
  each pointwise `n`-th derivative splits into a main part (the terms of `G_A`, `G_B`) and the
  subtraction terms of the faces;
* **`QED.ThreeLoopD.i12HSMainB_eq_reflect`**: for every `n`, the main part of `R_B` at
  `(ρ, θ, u)` is `θ⁻¹` times the main part of `R_A` at `(ρθ, θ⁻¹, u)` (the factor `θ⁻¹` is the
  Jacobian of the reflection).

So the extra letters of the individual sectors, which come from the artificial boundary
`θ = 1` (`t = v`), cancel in the sum of the sectors: over `θ ∈ (0, ∞)` the main term is a Mellin
integral in closed form (Gamma functions and `₂F₁(·, ·; ·; 1/2)`), and what is left lives on
the boundary `t = 1` of the original square.
-/

@[expose] public section

open Complex

namespace QED.ThreeLoopD

/-- **Homogeneity of `Φ₀`**: `Φ₀(λX, λY) = λ^{-3ε} Φ₀(X, Y)` for `λ, X, Y > 0`. -/
theorem i12Phi0_mul_mul (ε : ℂ) {l X Y : ℝ} (hl : 0 < l) (hX : 0 < X) (hY : 0 < Y) :
    i12Phi0 ε (l * X) (l * Y) = (l : ℂ) ^ (-3 * ε) * i12Phi0 ε X Y := by
  have hl' : (l : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
  have hX' : (X : ℂ) ≠ 0 := ofReal_ne_zero.mpr hX.ne'
  have hY' : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
  have hm : ∀ Z : ℝ, 0 ≤ Z → ((l * Z : ℝ) : ℂ) ^ (2 - 3 * ε) =
      (l : ℂ) ^ (2 : ℂ) * (l : ℂ) ^ (-3 * ε) * (Z : ℂ) ^ (2 - 3 * ε) := by
    intro Z hZ
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hl.le hZ, sub_eq_add_neg,
      cpow_add _ _ hl', neg_mul]
  simp only [i12Phi0]
  rw [show l * X + l * Y = l * (X + Y) by ring, hm _ (by positivity), hm _ hX.le, hm _ hY.le]
  have h2 : (l : ℂ) ^ (2 : ℂ) = (l : ℂ) ^ 2 := by norm_cast
  rw [h2]
  push_cast
  field_simp

/-- **Reflection of the sectors**: `G_A(ρθ, θ⁻¹, u) = θ^{3ε} G_B(ρ, θ, u)`. -/
theorem i12GA_reflect (ε : ℂ) {ρ θ u : ℝ} (hθ : 0 < θ) (hu0 : 0 < u) (hu1 : u < 1)
    (hH : 0 < i12H (ρ * θ)) :
    i12GA ε (ρ * θ) θ⁻¹ u = (θ : ℂ) ^ (3 * ε) * i12GB ε ρ θ u := by
  have hθi : 0 < θ⁻¹ := inv_pos.mpr hθ
  have hY : 0 < (1 - u) * θ * i12H (ρ * θ) := by
    have : 0 < 1 - u := by linarith
    positivity
  have h1 : ρ * θ * θ⁻¹ = ρ := by field_simp
  have hΦ : i12Phi0 ε (u * θ⁻¹) ((1 - u) * i12H (ρ * θ)) =
      (θ : ℂ) ^ (3 * ε) * i12Phi0 ε u ((1 - u) * θ * i12H (ρ * θ)) := by
    have := i12Phi0_mul_mul ε hθi hu0 hY
    rw [show θ⁻¹ * u = u * θ⁻¹ by ring,
      show θ⁻¹ * ((1 - u) * θ * i12H (ρ * θ)) = (1 - u) * i12H (ρ * θ) by field_simp] at this
    rw [this, ofReal_inv, inv_cpow _ _ (by simp [arg_ofReal_of_nonneg hθ.le, Real.pi_ne_zero.symm]),
      ← cpow_neg]
    ring_nf
  simp only [i12GA, i12GB]
  rw [h1, hΦ]
  ring

/-- The faces `ρ = 0`: `G_A(0, θ⁻¹, u) = θ^{3ε} G_B(0, θ, u)`. -/
theorem i12GA_zero_reflect (ε : ℂ) {θ u : ℝ} (hθ : 0 < θ) (hu0 : 0 < u) (hu1 : u < 1) :
    i12GA ε 0 θ⁻¹ u = (θ : ℂ) ^ (3 * ε) * i12GB ε 0 θ u := by
  have h := i12GA_reflect ε (ρ := 0) hθ hu0 hu1 (by norm_num [i12H])
  simpa using h

/-- The main part of `QED.ThreeLoopD.i12RA3Dn`: its three terms coming from `G_A` itself. -/
noncomputable def i12HSMainA (n : ℕ) (ρ θ u : ℝ) : ℝ :=
  ((u * θ + (1 - u) * i12H ρ) ^ 2 / (u * θ * ((1 - u) * i12H ρ)) / (i12H ρ) / (ρ * θ)) *
      (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H ρ) +
      -Real.log (1 - ρ * θ) + -3 * Real.log (u * θ + (1 - u) * i12H ρ)) ^ n +
    (-(u * θ) ^ 2 / (u * θ * ((1 - u) * i12H ρ)) / (i12H ρ) / (ρ * θ)) * (Real.log ρ + 2 *
        Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H ρ) + -Real.log (1 - ρ * θ) + -3 *
        Real.log (u * θ)) ^ n +
    (-((1 - u) * i12H ρ) ^ 2 / (u * θ * ((1 - u) * i12H ρ)) / (i12H ρ) / (ρ * θ)) * (Real.log ρ +
        2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H ρ) + -Real.log (1 - ρ * θ) +
        -3 * Real.log ((1 - u) * i12H ρ)) ^ n

/-- The face part of `QED.ThreeLoopD.i12RA3Dn`: its seven subtraction terms. -/
noncomputable def i12HSFaceA (n : ℕ) (ρ θ u : ℝ) : ℝ :=
  (-(u * θ + (1 - u) * i12H 0) ^ 2 / (u * θ * ((1 - u) * i12H 0)) / (i12H 0) / (ρ * θ)) *
        (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 *
        Real.log (u * θ + (1 - u) * i12H 0)) ^ n +
    ((u * θ) ^ 2 / (u * θ * ((1 - u) * i12H 0)) / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 *
        Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log (u * θ)) ^ n +
    (((1 - u) * i12H 0) ^ 2 / (u * θ * ((1 - u) * i12H 0)) / (i12H 0) / (ρ * θ)) * (Real.log ρ +
        2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log ((1 - u) *
        i12H 0)) ^ n +
    (-2 / (i12H ρ) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H ρ) + -3 * Real.log ((1 - u) * i12H ρ)) ^ n +
    (3 / (i12H ρ) / (ρ * θ)) * (n * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H ρ) + -3 * Real.log ((1 - u) * i12H ρ)) ^ (n - 1)) +
    (2 / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -3 * Real.log ((1 - u) * i12H 0)) ^ n +
    (-3 / (i12H 0) / (ρ * θ)) * (n * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -3 * Real.log ((1 - u) * i12H 0)) ^ (n - 1))

theorem i12RA3Dn_eq_main_add_face (n : ℕ) (ρ θ u : ℝ) :
    i12RA3Dn n ρ θ u = i12HSMainA n ρ θ u + i12HSFaceA n ρ θ u := by
  simp only [i12RA3Dn, i12HSMainA, i12HSFaceA]
  ring

/-- The main part of `QED.ThreeLoopD.i12RB3Dn`: its three terms coming from `G_B` itself. -/
noncomputable def i12HSMainB (n : ℕ) (ρ θ u : ℝ) : ℝ :=
  ((u + (1 - u) * θ * i12H (ρ * θ)) ^ 2 / (u * ((1 - u) * θ * i12H (ρ * θ))) / (i12H (ρ * θ)) /
      (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ *
      θ)) + -Real.log (1 - ρ) + -3 * Real.log (u + (1 - u) * θ * i12H (ρ * θ))) ^ n +
    (-(u) ^ 2 / (u * ((1 - u) * θ * i12H (ρ * θ))) / (i12H (ρ * θ)) / (ρ * θ)) * (Real.log ρ + 2 *
        Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ * θ)) + -Real.log (1 - ρ) +
        -3 * Real.log (u)) ^ n +
    (-((1 - u) * θ * i12H (ρ * θ)) ^ 2 / (u * ((1 - u) * θ * i12H (ρ * θ))) / (i12H (ρ * θ)) /
        (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ *
        θ)) + -Real.log (1 - ρ) + -3 * Real.log ((1 - u) * θ * i12H (ρ * θ))) ^ n

/-- The face part of `QED.ThreeLoopD.i12RB3Dn`: its seven subtraction terms. -/
noncomputable def i12HSFaceB (n : ℕ) (ρ θ u : ℝ) : ℝ :=
  (-(u + (1 - u) * θ * i12H 0) ^ 2 / (u * ((1 - u) * θ * i12H 0)) / (i12H 0) / (ρ * θ)) *
        (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 *
        Real.log (u + (1 - u) * θ * i12H 0)) ^ n +
    ((u) ^ 2 / (u * ((1 - u) * θ * i12H 0)) / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ +
        Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 * Real.log (u)) ^ n +
    (((1 - u) * θ * i12H 0) ^ 2 / (u * ((1 - u) * θ * i12H 0)) / (i12H 0) / (ρ * θ)) *
        (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H 0) + -3 *
        Real.log ((1 - u) * θ * i12H 0)) ^ n +
    (-2 / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -Real.log (1 - ρ) + -3 * Real.log (u)) ^ n +
    (3 / (i12H 0) / (ρ * θ)) * (n * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -Real.log (1 - ρ) + -3 * Real.log (u)) ^ (n - 1)) +
    (2 / (i12H 0) / (ρ * θ)) * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -3 * Real.log (u)) ^ n +
    (-3 / (i12H 0) / (ρ * θ)) * (n * (Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 *
        Real.log (i12H 0) + -3 * Real.log (u)) ^ (n - 1))

theorem i12RB3Dn_eq_main_add_face (n : ℕ) (ρ θ u : ℝ) :
    i12RB3Dn n ρ θ u = i12HSMainB n ρ θ u + i12HSFaceB n ρ θ u := by
  simp only [i12RB3Dn, i12HSMainB, i12HSFaceB]
  ring

/-- **The reflection at every order**: the main part of `R_B` at `(ρ, θ, u)` is `θ⁻¹` times the
main part of `R_A` at `(ρθ, θ⁻¹, u)`, the latter continued to `θ⁻¹ > 1`. -/
theorem i12HSMainB_eq_reflect (n : ℕ) {ρ θ u : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) (hu0 : 0 < u)
    (hu1 : u < 1) (hH : 0 < i12H (ρ * θ)) :
    i12HSMainB n ρ θ u = θ⁻¹ * i12HSMainA n (ρ * θ) θ⁻¹ u := by
  have hv : 0 < 1 - u := by linarith
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hS : 0 < u + (1 - u) * θ * i12H (ρ * θ) := by positivity
  have hY : 0 < (1 - u) * i12H (ρ * θ) := by positivity
  have e1 : 1 - ρ * θ * θ⁻¹ = 1 - ρ := by field_simp
  have e2 : Real.log (ρ * θ) = Real.log ρ + Real.log θ := Real.log_mul hρ.ne' hθ0
  have e3 : Real.log θ⁻¹ = -Real.log θ := Real.log_inv θ
  have e4 : Real.log (u * θ⁻¹ + (1 - u) * i12H (ρ * θ)) =
      Real.log (u + (1 - u) * θ * i12H (ρ * θ)) - Real.log θ := by
    rw [← Real.log_div hS.ne' hθ0]
    congr 1
    field_simp
  have e5 : Real.log (u * θ⁻¹) = Real.log u - Real.log θ := by
    rw [Real.log_mul hu0.ne' (inv_ne_zero hθ0), e3]; ring
  have e6 : Real.log ((1 - u) * θ * i12H (ρ * θ)) =
      Real.log ((1 - u) * i12H (ρ * θ)) + Real.log θ := by
    rw [← Real.log_mul hY.ne' hθ0]
    congr 1
    ring
  simp only [i12HSMainA, i12HSMainB]
  rw [e1, e2, e3, e4, e5, e6]
  have b1 : Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ * θ)) +
      -Real.log (1 - ρ) + -3 * Real.log (u + (1 - u) * θ * i12H (ρ * θ)) =
      Real.log ρ + Real.log θ + 2 * -Real.log θ + Real.log (u * (1 - u)) +
      2 * Real.log (i12H (ρ * θ)) + -Real.log (1 - ρ) +
      -3 * (Real.log (u + (1 - u) * θ * i12H (ρ * θ)) - Real.log θ) := by ring
  have b2 : Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ * θ)) +
      -Real.log (1 - ρ) + -3 * Real.log u =
      Real.log ρ + Real.log θ + 2 * -Real.log θ + Real.log (u * (1 - u)) +
      2 * Real.log (i12H (ρ * θ)) + -Real.log (1 - ρ) + -3 * (Real.log u - Real.log θ) := by ring
  have b3 : Real.log ρ + 2 * Real.log θ + Real.log (u * (1 - u)) + 2 * Real.log (i12H (ρ * θ)) +
      -Real.log (1 - ρ) + -3 * (Real.log ((1 - u) * i12H (ρ * θ)) + Real.log θ) =
      Real.log ρ + Real.log θ + 2 * -Real.log θ + Real.log (u * (1 - u)) +
      2 * Real.log (i12H (ρ * θ)) + -Real.log (1 - ρ) +
      -3 * Real.log ((1 - u) * i12H (ρ * θ)) := by ring
  rw [b1, b2, b3]
  have hu' : u ≠ 0 := hu0.ne'
  have hH' : i12H (ρ * θ) ≠ 0 := hH.ne'
  have hv' : 1 - u ≠ 0 := hv.ne'
  have hρ' : ρ ≠ 0 := hρ.ne'
  field_simp

end QED.ThreeLoopD
