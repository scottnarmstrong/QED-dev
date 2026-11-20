/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# (R-Π₄) step L9: the divided-difference bound of a Pauli–Villars block

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling of
the fermion regulators). A block of the frozen statement has the masses `m < M₁, M₂` and the
coefficients `(1, c₁, c₂)` with `1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0`. As `M₂ / M₁ → 1`
the coefficients blow up, so the regulator terms `c₁ r(M₁²) + c₂ r(M₂²)` of a per-flavour
function `r` (in `x = M²`) are controlled only in divided-difference form: if `r` is small and
Lipschitz on the scale of `x` beyond `R²`, the regulator terms are small, uniformly in the
coefficients.

* `dec_pv_c₂_mul`: `c₂ (x₂ - x₁) = x₁ - x₀` (the coefficients in closed form);
* `dec_pv_affine`: the block kills affine functions of `x`;
* `dec_norm_pv_le`: **`‖c₁ r(x₁) + c₂ r(x₂)‖ ≤ 2ε`** given `‖r‖ ≤ ε` and
  `‖r y - r x‖ ≤ ε (y - x) / x` for `R² ≤ x ≤ y`.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

section DD

variable {x₀ x₁ x₂ c₁ c₂ : ℝ}

/-- The Pauli–Villars coefficients in closed form: `c₂ (x₂ - x₁) = x₁ - x₀`. -/
theorem dec_pv_c₂_mul (hc : 1 + c₁ + c₂ = 0) (hc' : x₀ + c₁ * x₁ + c₂ * x₂ = 0) :
    c₂ * (x₂ - x₁) = x₁ - x₀ := by
  linear_combination hc' - x₁ * hc

/-- The two regulator masses of a block are distinct. -/
theorem dec_pv_ne (hc : 1 + c₁ + c₂ = 0) (hc' : x₀ + c₁ * x₁ + c₂ * x₂ = 0) (h₀ : x₀ < x₁) :
    x₁ ≠ x₂ := by
  rintro rfl
  have := dec_pv_c₂_mul hc hc'
  simp only [sub_self, mul_zero] at this
  linarith

/-- **A block kills affine functions** of `x = M²`. -/
theorem dec_pv_affine (hc : 1 + c₁ + c₂ = 0) (hc' : x₀ + c₁ * x₁ + c₂ * x₂ = 0) (α β : ℂ) :
    (α + β * x₀) + (c₁ : ℂ) * (α + β * x₁) + (c₂ : ℂ) * (α + β * x₂) = 0 := by
  have h1 : (1 + c₁ + c₂ : ℂ) = 0 := by exact_mod_cast hc
  have h2 : (x₀ + c₁ * x₁ + c₂ * x₂ : ℂ) = 0 := by exact_mod_cast hc'
  linear_combination α * h1 + β * h2

variable {r : ℝ → ℂ} {R2 ε : ℝ}

/-- The ordered case `x₁ < x₂` of `dec_norm_pv_le`. -/
theorem dec_norm_pv_le_of_lt (hc : 1 + c₁ + c₂ = 0) (hc' : x₀ + c₁ * x₁ + c₂ * x₂ = 0)
    (hx₀ : 0 ≤ x₀) (h₀ : x₀ < x₁) (h₁₂ : x₁ < x₂) (hR : R2 ≤ x₁)
    (hr : ∀ x, R2 ≤ x → ‖r x‖ ≤ ε)
    (hL : ∀ x y, R2 ≤ x → x ≤ y → ‖r y - r x‖ ≤ ε * ((y - x) / x)) :
    ‖(c₁ : ℂ) * r x₁ + (c₂ : ℂ) * r x₂‖ ≤ 2 * ε := by
  have hx₁ : 0 < x₁ := hx₀.trans_lt h₀
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hr x₁ hR)
  have hd : 0 < x₂ - x₁ := sub_pos.2 h₁₂
  have hmul := dec_pv_c₂_mul hc hc'
  have hc₂ : 0 ≤ c₂ := by
    by_contra h
    nlinarith
  have hc₁ : (c₁ : ℂ) = -1 - c₂ := by exact_mod_cast (by linarith : c₁ = -1 - c₂)
  have e : (c₁ : ℂ) * r x₁ + (c₂ : ℂ) * r x₂ = (c₂ : ℂ) * (r x₂ - r x₁) - r x₁ := by
    rw [hc₁]
    ring
  have hk : c₂ * ((x₂ - x₁) / x₁) ≤ 1 := by
    rw [← mul_div_assoc, hmul, div_le_one hx₁]
    linarith
  rw [e]
  calc ‖(c₂ : ℂ) * (r x₂ - r x₁) - r x₁‖ ≤ ‖(c₂ : ℂ) * (r x₂ - r x₁)‖ + ‖r x₁‖ :=
        norm_sub_le _ _
    _ ≤ c₂ * (ε * ((x₂ - x₁) / x₁)) + ε := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc₂]
        exact add_le_add (mul_le_mul_of_nonneg_left (hL x₁ x₂ hR h₁₂.le) hc₂) (hr x₁ hR)
    _ = ε * (c₂ * ((x₂ - x₁) / x₁)) + ε := by ring
    _ ≤ ε * 1 + ε := by gcongr
    _ = 2 * ε := by ring

/-- **The divided-difference bound of a block**: if the per-flavour function `r` (in `x = M²`)
is bounded by `ε` and `ε`-Lipschitz on the scale of `x` beyond `R²`, the regulator terms of a
block with `x₀ < x₁, x₂` are bounded by `2ε`, uniformly in the coefficients. -/
theorem dec_norm_pv_le (hc : 1 + c₁ + c₂ = 0) (hc' : x₀ + c₁ * x₁ + c₂ * x₂ = 0)
    (hx₀ : 0 ≤ x₀) (h₁ : x₀ < x₁) (h₂ : x₀ < x₂) (hR₁ : R2 ≤ x₁) (hR₂ : R2 ≤ x₂)
    (hr : ∀ x, R2 ≤ x → ‖r x‖ ≤ ε)
    (hL : ∀ x y, R2 ≤ x → x ≤ y → ‖r y - r x‖ ≤ ε * ((y - x) / x)) :
    ‖(c₁ : ℂ) * r x₁ + (c₂ : ℂ) * r x₂‖ ≤ 2 * ε := by
  rcases lt_or_gt_of_ne (dec_pv_ne hc hc' h₁) with h | h
  · exact dec_norm_pv_le_of_lt hc hc' hx₀ h₁ h hR₁ hr hL
  · rw [add_comm]
    exact dec_norm_pv_le_of_lt (by linarith) (by linarith) hx₀ h₂ h hR₂ hr hL

end DD

end QED.GradedProof.RPi4

end
