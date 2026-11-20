/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# (R-Π₄) step L6d1: elementary bounds for the sector integrals

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1 (model-free). The
heavy-photon density needs only a rate `r(u) → 0` with `∫^∞ r(u)/u du < ∞`, so every majorant
`θ (c + θσ)⁻²` of the face and bulk sectors may be traded for `c^{-1/2} θ^{-1/2} σ^{-3/2}`:

* `inv_sq_add_le_rpow`: `(c + x)⁻² ≤ c^{-1/2} x^{-3/2}`;
* `integral_face_majorant_le`: `∫₀¹ θ (c + θσ)⁻² dθ ≤ 2 c^{-1/2} σ^{-3/2}`;
* `integral_Ioi_rpow_neg_three_halves`: `∫_{R}^∞ σ^{-3/2} = 2 R^{-1/2}`;
* `abs_inv_pow_sub_inv_pow_le`: `|a⁻ʲ - b⁻ʲ| ≤ j |a - b| c^{-(j+1)}` for `a, b ≥ c > 0` (the
  `s`-subtraction in the loop-UV corner).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.GradedProof.RPi4

/-- **`(c + x)⁻² ≤ c^{-1/2} x^{-3/2}`** for `c, x > 0`. -/
theorem inv_sq_add_le_rpow {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ((c + x) ^ 2)⁻¹ ≤ c ^ (-(1 / 2) : ℝ) * x ^ (-(3 / 2) : ℝ) := by
  have h1 : c ^ (1 / 2 : ℝ) ≤ (c + x) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hc.le (by linarith) (by norm_num)
  have h2 : x ^ (3 / 2 : ℝ) ≤ (c + x) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hx.le (by linarith) (by norm_num)
  have hcx : 0 < c + x := by linarith
  have e : (c + x) ^ (1 / 2 : ℝ) * (c + x) ^ (3 / 2 : ℝ) = (c + x) ^ 2 := by
    rw [← Real.rpow_add hcx]
    norm_num
  have hp : c ^ (1 / 2 : ℝ) * x ^ (3 / 2 : ℝ) ≤ (c + x) ^ 2 := by
    rw [← e]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  rw [Real.rpow_neg hc.le, Real.rpow_neg hx.le, ← mul_inv]
  exact inv_anti₀ (by positivity) hp

/-- **The face majorant**: `∫₀¹ θ (c + θσ)⁻² dθ ≤ 2 c^{-1/2} σ^{-3/2}`. -/
theorem integral_face_majorant_le {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    ∫ θ in (0 : ℝ)..1, θ * ((c + θ * σ) ^ 2)⁻¹ ≤
      2 * (c ^ (-(1 / 2) : ℝ) * σ ^ (-(3 / 2) : ℝ)) := by
  have hr : ∫ θ in (0 : ℝ)..1, θ ^ (-(1 / 2) : ℝ) = 2 := by
    rw [integral_rpow (Or.inl (by norm_num))]
    norm_num
  have hi : IntervalIntegrable (fun θ : ℝ => θ ^ (-(1 / 2) : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpt : ∀ θ ∈ Ioc (0 : ℝ) 1, θ * ((c + θ * σ) ^ 2)⁻¹ ≤
      c ^ (-(1 / 2) : ℝ) * σ ^ (-(3 / 2) : ℝ) * θ ^ (-(1 / 2) : ℝ) := fun θ hθ => by
    have hθ0 := hθ.1
    have h := inv_sq_add_le_rpow hc (mul_pos hθ0 hσ)
    have e : θ * (c ^ (-(1 / 2) : ℝ) * (θ * σ) ^ (-(3 / 2) : ℝ)) =
        c ^ (-(1 / 2) : ℝ) * σ ^ (-(3 / 2) : ℝ) * θ ^ (-(1 / 2) : ℝ) := by
      rw [Real.mul_rpow hθ0.le hσ.le]
      have : θ * θ ^ (-(3 / 2) : ℝ) = θ ^ (-(1 / 2) : ℝ) := by
        rw [show θ * θ ^ (-(3 / 2) : ℝ) = θ ^ ((1 : ℝ) + -(3 / 2)) by
          rw [Real.rpow_add hθ0, Real.rpow_one]]
        norm_num
      calc θ * (c ^ (-(1 / 2) : ℝ) * (θ ^ (-(3 / 2) : ℝ) * σ ^ (-(3 / 2) : ℝ)))
          = c ^ (-(1 / 2) : ℝ) * σ ^ (-(3 / 2) : ℝ) * (θ * θ ^ (-(3 / 2) : ℝ)) := by ring
        _ = _ := by rw [this]
    rw [← e]
    exact mul_le_mul_of_nonneg_left h hθ0.le
  have hgi : IntervalIntegrable (fun θ : ℝ => θ * ((c + θ * σ) ^ 2)⁻¹) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_id.mul (ContinuousOn.inv₀ (by fun_prop) fun θ hθ => ?_)
    have : 0 ≤ θ := by rw [uIcc_of_le zero_le_one] at hθ; exact hθ.1
    positivity
  calc ∫ θ in (0 : ℝ)..1, θ * ((c + θ * σ) ^ 2)⁻¹
      ≤ ∫ θ in (0 : ℝ)..1, c ^ (-(1 / 2) : ℝ) * σ ^ (-(3 / 2) : ℝ) * θ ^ (-(1 / 2) : ℝ) :=
        intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hgi (hi.const_mul _)
          fun θ hθ => hpt θ (Ioo_subset_Ioc_self hθ)
    _ = _ := by rw [intervalIntegral.integral_const_mul, hr]; ring

/-- `∫_{R}^∞ σ^{-3/2} dσ = 2 R^{-1/2}`. -/
theorem integral_Ioi_rpow_neg_three_halves {R : ℝ} (hR : 0 < R) :
    ∫ σ in Ioi R, σ ^ (-(3 / 2) : ℝ) = 2 * R ^ (-(1 / 2) : ℝ) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) hR]
  norm_num
  ring

/-- **The difference of inverse powers**: `|a⁻ʲ - b⁻ʲ| ≤ j |a - b| c^{-(j+1)}` for
`a, b ≥ c > 0`. -/
theorem abs_inv_pow_sub_inv_pow_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) (j : ℕ) :
    |(a ^ j)⁻¹ - (b ^ j)⁻¹| ≤ j * |a - b| * (c ^ (j + 1))⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ha0 : 0 < a := hc.trans_le ha
    have hb0 : 0 < b := hc.trans_le hb
    have e : (a ^ (j + 1))⁻¹ - (b ^ (j + 1))⁻¹ =
        a⁻¹ * ((a ^ j)⁻¹ - (b ^ j)⁻¹) + (b ^ j)⁻¹ * (a⁻¹ - b⁻¹) := by
      field_simp; ring
    have e2 : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
    have hai : a⁻¹ ≤ c⁻¹ := inv_anti₀ hc ha
    have hbj : (b ^ j)⁻¹ ≤ (c ^ j)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hb j)
    have h2 : |a⁻¹ - b⁻¹| ≤ |a - b| * (c ^ 2)⁻¹ := by
      rw [e2, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) (abs_nonneg _)
      nlinarith
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 ha0), abs_of_pos (inv_pos.2 (pow_pos hb0 j))]
    calc a⁻¹ * |(a ^ j)⁻¹ - (b ^ j)⁻¹| + (b ^ j)⁻¹ * |a⁻¹ - b⁻¹|
        ≤ c⁻¹ * (j * |a - b| * (c ^ (j + 1))⁻¹) + (c ^ j)⁻¹ * (|a - b| * (c ^ 2)⁻¹) :=
          add_le_add (mul_le_mul hai ih (abs_nonneg _) (by positivity))
            (mul_le_mul hbj h2 (abs_nonneg _) (by positivity))
      _ = ((j + 1 : ℕ) : ℝ) * |a - b| * (c ^ (j + 1 + 1))⁻¹ := by
          push_cast
          field_simp
          ring

end QED.GradedProof.RPi4

end
