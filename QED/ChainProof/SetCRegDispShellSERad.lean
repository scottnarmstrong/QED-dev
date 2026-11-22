/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SpatialIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Radial integrals with half-integer powers in three dimensions

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (the closed form
of the limits `QED.ChainProof.SetCRegDispSE.seProdLim`). At zero prescription the closed-form
energy integral `seSpatial` contains `(-W)^{-s}` with `W = |v⃗ + a⃗|² + Δ` and half-integer
`s = n + 1/2`, `n + 3/2`, `n ≥ 1`; its spatial integral needs the radial integrals
`F_s(D) = ∫₀^∞ r² (r² + D)^{-s} dr` for every half-integer `s ≥ 5/2`
(`QED.Integration.SpatialIntegral` has `s = 5/2` only).

* `integral_Ioi_sq_mul_rpow_add_one`: the recursion `F_{s+1} = (2s - 3)/(2s D) F_s` for
  `s > 3/2`, from the antiderivative identity
  `d/dr [r³ (r² + D)^{-s}] = (3 - 2s) r² (r² + D)^{-s} + 2s D r² (r² + D)^{-s-1}`;
* `seRadC`, **`integral_Ioi_sq_mul_rpow_half`**: `F_{i+5/2}(D) = c_i D^{-(i+1)}`,
  `c₀ = 1/3`, `c_{i+1} = (2i+2)/(2i+5) c_i`;
* **`integral_sum_sq_add_rpow_half`**, `integral_sum_sq_mul_sum_sq_add_rpow_half`: the
  three-dimensional integrals `∫ (|v|² + D)^{-(i+5/2)}` and `∫ |v|² (|v|² + D)^{-(i+7/2)}`;
* `neg_ofReal_cpow_neg`: `(-W)^{-s} = e^{-iπ s} W^{-s}` for `W > 0` (the boundary value from
  `Im > 0`, the branch of the limit `QED.ChainProof.SetCRegDispSE.tendsto_integral_seSpatial`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDispSE

open QED.Integration

/-! ### The recursion -/

theorem integrableOn_sq_mul_rpow {D s : ℝ} (hD : 0 < D) (hs : 3 / 2 < s) :
    IntegrableOn (fun r : ℝ => r ^ 2 * (r ^ 2 + D) ^ (-s)) (Ioi 0) := by
  have h := (integrable_comp_sum_sq_iff (fun x : ℝ => (x + D) ^ (-s))).1
    (integrable_sum_sq_add_rpow hD hs)
  simpa only [smul_eq_mul] using h

theorem hasDerivAt_cube_mul_rpow {D : ℝ} (hD : 0 < D) (s r : ℝ) :
    HasDerivAt (fun r : ℝ => r ^ 3 * (r ^ 2 + D) ^ (-s))
      ((3 - 2 * s) * (r ^ 2 * (r ^ 2 + D) ^ (-s)) +
        2 * s * D * (r ^ 2 * (r ^ 2 + D) ^ (-(s + 1)))) r := by
  have hX : 0 < r ^ 2 + D := by positivity
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2 + D) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).add_const D
  have h2 := h1.rpow_const (p := -s) (Or.inl hX.ne')
  have h3 := (hasDerivAt_pow 3 r).mul h2
  refine h3.congr_deriv ?_
  have e : (r ^ 2 + D) ^ (-s - 1) = (r ^ 2 + D) ^ (-(s + 1)) := by ring_nf
  have e2 : (r ^ 2 + D) ^ (-s) = (r ^ 2 + D) * (r ^ 2 + D) ^ (-(s + 1)) := by
    rw [show -s = 1 + -(s + 1) by ring, Real.rpow_add hX, Real.rpow_one]
  rw [e]
  simp only [Nat.cast_ofNat]
  rw [e2]
  ring

theorem tendsto_cube_mul_rpow {D s : ℝ} (hD : 0 < D) (hs : 3 / 2 < s) :
    Tendsto (fun r : ℝ => r ^ 3 * (r ^ 2 + D) ^ (-s)) atTop (𝓝 0) := by
  have hX : Tendsto (fun r : ℝ => r ^ 2 + D) atTop atTop :=
    tendsto_atTop_add_const_right _ D (tendsto_pow_atTop (by norm_num))
  have hlim := (tendsto_rpow_neg_atTop (by linarith : 0 < s - 3 / 2)).comp hX
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact mul_nonneg (pow_nonneg hr 3) (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    have hXp : 0 < r ^ 2 + D := by positivity
    have hr3 : r ^ 3 ≤ (r ^ 2 + D) ^ (3 / 2 : ℝ) := by
      have : r ^ 3 = (r ^ 2) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr]
        norm_num
      rw [this]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    simp only [Function.comp_apply]
    calc r ^ 3 * (r ^ 2 + D) ^ (-s) ≤ (r ^ 2 + D) ^ (3 / 2 : ℝ) * (r ^ 2 + D) ^ (-s) := by
          gcongr
      _ = (r ^ 2 + D) ^ (-(s - 3 / 2)) := by
          rw [← Real.rpow_add hXp]
          ring_nf

/-- **The recursion** `F_{s+1}(D) = (2s - 3)/(2s D) F_s(D)` for `s > 3/2`. -/
theorem integral_Ioi_sq_mul_rpow_add_one {D s : ℝ} (hD : 0 < D) (hs : 3 / 2 < s) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * (r ^ 2 + D) ^ (-(s + 1)) =
      (2 * s - 3) / (2 * s * D) * ∫ r in Ioi (0 : ℝ), r ^ 2 * (r ^ 2 + D) ^ (-s) := by
  have i1 := integrableOn_sq_mul_rpow hD hs
  have i2 := integrableOn_sq_mul_rpow hD (by linarith : 3 / 2 < s + 1)
  have hcont : Continuous fun r : ℝ => r ^ 3 * (r ^ 2 + D) ^ (-s) :=
    (continuous_pow 3).mul ((continuous_pow 2).add continuous_const |>.rpow_const
      fun r => Or.inl (by nlinarith [sq_nonneg r] : (0 : ℝ) < r ^ 2 + D).ne')
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
    (fun r _ => hasDerivAt_cube_mul_rpow hD s r) ((i1.const_mul _).add (i2.const_mul _))
    (tendsto_cube_mul_rpow hD hs)
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero] at h
  have hs0 : 0 < s := by linarith
  field_simp
  linear_combination h

/-! ### Half-integer powers -/

/-- The constants `c₀ = 1/3`, `c_{i+1} = (2i + 2)/(2i + 5) c_i`, so that
`∫₀^∞ r² (r² + D)^{-(i + 5/2)} dr = c_i D^{-(i+1)}`. -/
noncomputable def seRadC : ℕ → ℝ
  | 0 => 1 / 3
  | i + 1 => (2 * i + 2) / (2 * i + 5) * seRadC i

/-- **`∫₀^∞ r² (r² + D)^{-(i + 5/2)} dr = c_i D^{-(i+1)}`.** -/
theorem integral_Ioi_sq_mul_rpow_half {D : ℝ} (hD : 0 < D) (i : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * (r ^ 2 + D) ^ (-((i : ℝ) + 5 / 2)) =
      seRadC i * D ^ (-((i : ℝ) + 1)) := by
  induction i with
  | zero =>
    simp only [Nat.cast_zero, zero_add, seRadC]
    rw [integral_Ioi_sq_mul_rpow_neg_five_halves hD, Real.rpow_neg_one]
    field_simp
  | succ i ih =>
    have e : (((i + 1 : ℕ) : ℝ) + 5 / 2) = ((i : ℝ) + 5 / 2) + 1 := by push_cast; ring
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    rw [e, integral_Ioi_sq_mul_rpow_add_one hD (by linarith), ih, seRadC]
    have e2 : D ^ (-(((i + 1 : ℕ) : ℝ) + 1)) = D ^ (-((i : ℝ) + 1)) * D⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hD]
      push_cast
      ring_nf
    rw [e2]
    field_simp
    ring

/-- **`∫_{ℝ³} (|v|² + D)^{-(i + 5/2)} d³v = 4π c_i D^{-(i+1)}`.** -/
theorem integral_sum_sq_add_rpow_half {D : ℝ} (hD : 0 < D) (i : ℕ) :
    ∫ v : Fin 3 → ℝ, (∑ k, v k ^ 2 + D) ^ (-((i : ℝ) + 5 / 2)) =
      4 * π * (seRadC i * D ^ (-((i : ℝ) + 1))) := by
  have h := integral_comp_sum_sq (fun x : ℝ => (x + D) ^ (-((i : ℝ) + 5 / 2)))
  simp only [smul_eq_mul] at h
  rw [h, integral_Ioi_sq_mul_rpow_half hD i]

/-- **The second moment**: `∫_{ℝ³} |v|² (|v|² + D)^{-(i + 7/2)} d³v
= 4π (c_i D^{-(i+1)} - c_{i+1} D^{-(i+1)})`. -/
theorem integral_sum_sq_mul_sum_sq_add_rpow_half {D : ℝ} (hD : 0 < D) (i : ℕ) :
    ∫ v : Fin 3 → ℝ, (∑ k, v k ^ 2) * (∑ k, v k ^ 2 + D) ^ (-((i : ℝ) + 7 / 2)) =
      4 * π * ((seRadC i - seRadC (i + 1)) * D ^ (-((i : ℝ) + 1))) := by
  have hpt : ∀ v : Fin 3 → ℝ, (∑ k, v k ^ 2) * (∑ k, v k ^ 2 + D) ^ (-((i : ℝ) + 7 / 2)) =
      (∑ k, v k ^ 2 + D) ^ (-((i : ℝ) + 5 / 2)) -
        D * (∑ k, v k ^ 2 + D) ^ (-(((i + 1 : ℕ) : ℝ) + 5 / 2)) := by
    intro v
    have hX : 0 < ∑ k, v k ^ 2 + D := by positivity
    have e1 : (-(((i + 1 : ℕ) : ℝ) + 5 / 2)) = -((i : ℝ) + 7 / 2) := by push_cast; ring
    have e2 : (∑ k, v k ^ 2 + D) ^ (-((i : ℝ) + 5 / 2)) =
        (∑ k, v k ^ 2 + D) * (∑ k, v k ^ 2 + D) ^ (-((i : ℝ) + 7 / 2)) := by
      rw [show -((i : ℝ) + 5 / 2) = 1 + -((i : ℝ) + 7 / 2) by ring, Real.rpow_add hX,
        Real.rpow_one]
    rw [e1, e2]
    ring
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  simp_rw [hpt]
  rw [integral_sub (integrable_sum_sq_add_rpow hD (by linarith))
    ((integrable_sum_sq_add_rpow hD (by push_cast; linarith)).const_mul D), integral_const_mul,
    integral_sum_sq_add_rpow_half hD, integral_sum_sq_add_rpow_half hD]
  have e3 : D ^ (-(((i + 1 : ℕ) : ℝ) + 1)) = D ^ (-((i : ℝ) + 1)) * D⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hD]
    push_cast
    ring_nf
  rw [e3]
  field_simp

/-! ### The branch at the negative real axis -/

/-- `(-W)^{-s} = e^{-iπ s} W^{-s}` for `W > 0` and real `s`. -/
theorem neg_ofReal_cpow_neg {W : ℝ} (hW : 0 < W) (s : ℝ) :
    (-(W : ℂ)) ^ (-((s : ℝ) : ℂ)) = exp (π * I * (-((s : ℝ) : ℂ))) * ((W ^ (-s) : ℝ) : ℂ) := by
  have h := Complex.ofReal_cpow_of_nonpos (x := -W) (by linarith) (-((s : ℝ) : ℂ))
  push_cast at h
  rw [h, Complex.ofReal_cpow hW.le]
  push_cast
  ring_nf

end QED.ChainProof.SetCRegDispSE

end
