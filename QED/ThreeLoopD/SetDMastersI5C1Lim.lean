/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Prim

/-!
# Set (d), master `I₅`: the limit of `Φ₁ - A₁` and `c₁`, given `t K₁(t)` in closed form

As `t → ∞`, `ξ(t) → 0⁺`. With `log t = 2 log (1 - ξ) - log ξ`, every word of `Φ₁` written in
the Lyndon basis and every basis function other than `log ξ` written as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`
(`QED.ThreeLoopD.i13hpl_rho_01` and its companions), the difference of `Φ₁(ξ(t))` and
`A₁(t) = -5λ³/6 - λ² + (8 + π²/6) λ` (`QED.ThreeLoopD.i5Prim1`) is exactly
(`QED.ThreeLoopD.i5D1_eq`)

  `Φ₁ - A₁ = 25 + π²/6 + ξ (Q₀ + Q₁ log ξ + Q₂ log² ξ)`,

with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; hence `Φ₁ - A₁ → 25 + π²/6`
(`QED.ThreeLoopD.tendsto_i5Phi1t_sub_prim1`). With `Φ₁(1) = 11π²/6 + 5ζ(3) + 4π⁴/45`,
`QED.ThreeLoopD.i5RemCoeff_one_of_prim` gives

  `c₁ = 25 + π²/6 - Φ₁(1) = -4π⁴/45 - 5π²/3 - 5ζ(3) + 25`

(`QED.ThreeLoopD.i5RemCoeff_one_of_kerC`), under the hypothesis `t K₁(t) = K(ξ(t))` for `t > 0`
(`QED.ThreeLoopD.i5K1x`), which is not proved here.

## Main results

* `QED.ThreeLoopD.i5D1_eq`, `QED.ThreeLoopD.tendsto_i5Phi1t_sub_prim1`.
* `QED.ThreeLoopD.i5RemCoeff_one_of_kerC`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- `Φ₁ - A₁` in terms of `ξ`. -/
noncomputable def i5D1 (x : ℝ) : ℝ :=
  i5Phi1 x - (-5 / 6 * (2 * Real.log (1 - x) - Real.log x) ^ 3 -
    (2 * Real.log (1 - x) - Real.log x) ^ 2 + (8 + π ^ 2 / 6) * (2 * Real.log (1 - x) - Real.log x))

theorem i5Phi1t_sub_prim1 {t : ℝ} (ht : 0 < t) : i5Phi1t t - i5Prim1 t = i5D1 (i13Xi t) := by
  unfold i5D1 i5Phi1t i5Prim1
  rw [i8_log_eq ht]

/-- The polynomial `Q0` of the limit of `Φ₁ - A₁`. -/
noncomputable def i5LQ0 (x r_0001 r_001 r_00m r_01 r_011 r_01m r_0m r_0m1 r_1 r_m : ℝ) : ℝ :=
    35 / 2 - 7 * x ^ 3 - 49 / 6 * x ^ 2 - 13 / 2 * x ^ 4 - 5 / 6 * x ^ 5 + π ^ 2 / 4 +
    17 / 2 * x + r_m * x ^ 5 - 23 * r_1 ^ 2 * x ^ 6 - 10 * r_01 * x ^ 2 - 10 * r_1 ^ 2 * x ^ 7 -
    9 * r_1 * x ^ 4 - 8 * r_01m * x - 8 * r_01m * x ^ 3 - 8 * r_0m1 * x - 8 * r_0m1 * x ^ 3 -
    6 * r_00m * x ^ 2 - 6 * r_0m * x ^ 3 - 5 * r_1 * x ^ 6 - 3 * r_m * x ^ 3 - 2 * r_001 * x -
    2 * r_001 * x ^ 2 - 2 * r_001 * x ^ 3 - 2 * r_m * x ^ 2 + 2 * r_01 * x ^ 5 + 2 * r_011 * x +
    2 * r_011 * x ^ 3 + 2 * r_m * x + 2 * r_m * x ^ 4 + 3 * r_0m * x + 3 * r_0m * x ^ 5 +
    3 * r_1 ^ 2 * x ^ 4 + 4 * r_00m * x + 4 * r_00m * x ^ 3 + 4 * r_01 * x ^ 3 +
    4 * r_1 ^ 2 * x ^ 5 + 8 * r_0001 * x ^ 2 + 8 * r_011 * x ^ 2 + 8 * r_0m * x ^ 2 +
    8 * r_1 * x + 10 * r_01 * x + 12 * r_01m * x ^ 2 + 12 * r_0m1 * x ^ 2 + 32 * r_1 * x ^ 2 -
    49 / 2 * r_1 * x ^ 5 - 37 / 2 * r_1 * x ^ 3 - 20 / 3 * r_1 ^ 3 * x ^ 8 + π ^ 2 * x / 6 +
    π ^ 2 * x ^ 2 / 12 - 12 * r_0m * r_1 * x ^ 5 - 8 * r_01 * r_1 * x ^ 5 -
    2 * r_1 * r_m * x ^ 4 + 2 * r_1 * r_m * x ^ 6 + 4 * r_01 * r_1 * x ^ 4 +
    4 * r_01 * r_1 * x ^ 6 + 6 * r_0m * r_1 * x ^ 4 + 6 * r_0m * r_1 * x ^ 6 +
    π ^ 2 * r_1 * x / 6 + π ^ 2 * r_1 * x ^ 3 / 6

/-- The polynomial `Q1` of the limit of `Φ₁ - A₁`. -/
noncomputable def i5LQ1 (x _r_0001 r_001 _r_00m r_01 _r_011 _r_01m r_0m _r_0m1 r_1 r_m : ℝ) : ℝ :=
    -19 / 4 - 49 / 4 * x ^ 2 - 17 / 2 * x - 7 / 2 * x ^ 3 - x ^ 4 / 2 + r_m * x ^ 3 -
    r_0m * x - r_0m * x ^ 3 - r_m * x - 22 * r_1 * x ^ 3 - 10 * r_1 * x ^ 4 - 8 * r_001 * x ^ 2 -
    6 * r_1 ^ 2 * x ^ 5 - 2 * r_01 * x ^ 2 - 2 * r_1 * x - 2 * r_1 * x ^ 5 - 2 * r_1 ^ 2 * x ^ 4 -
    2 * r_1 ^ 2 * x ^ 6 + 2 * r_01 * x ^ 3 + 6 * r_01 * x + 10 * r_1 * x ^ 2

/-- The polynomial `Q2` of the limit of `Φ₁ - A₁`. -/
noncomputable def i5LQ2 (x _r_0001 _r_001 _r_00m r_01 _r_011 _r_01m _r_0m _r_0m1 r_1 _r_m : ℝ) : ℝ
    :=
    -7 / 4 - x - x ^ 2 / 4 - 2 * r_1 * x ^ 2 + 2 * r_01 * x ^ 2 - 5 / 2 * r_1 * x - r_1 * x ^ 3 / 2

theorem i5D1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i5D1 x = 25 + π ^ 2 / 6 + x * (i5LQ0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) + Real.log x * i5LQ1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i5LQ2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i5D1 i5Phi1 i5Phi1N0 i5Phi1N1 i5Phi1N2
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_m0 hx, i13hw_10 hx, i13hw_1m hx, i13hw_11 hx,
    i13hw_0m0 hx, i13hw_010 hx, i13hw_100 hx, i13hw_10m hx, i13hw_110 hx, i13hw_0100 hx,
    i13_log_one_sub_eq hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_00m h0, i13hpl_rho_01 h0,
    i13hpl_rho_011 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0]
  unfold i5LQ0 i5LQ1 i5LQ2
  field_simp
  ring

/-- The vector of the arguments `ξ, ρ_w(ξ)` of the polynomials `Qⱼ`. -/
noncomputable def i5LV (x : ℝ) : Fin 11 → ℝ :=
  ![x, i13Rho [zero, zero, zero, one] x, i13Rho [zero, zero, one] x, i13Rho [zero, zero, negOne] x,
    i13Rho [zero, one] x, i13Rho [zero, one, one] x, i13Rho [zero, one, negOne] x, i13Rho [zero,
    negOne] x, i13Rho [zero, negOne, one] x, i13Rho [one] x, i13Rho [negOne] x]

theorem norm_i5LV_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : ‖i5LV x‖ ≤ 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  fin_cases i
  · show ‖x‖ ≤ 2
    rw [Real.norm_eq_abs, abs_of_pos hx.1]
    linarith [hx.2]
  · show ‖i13Rho [zero, zero, zero, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx

theorem i5LQ0_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i5LQ0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤
    M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 11 → ℝ => i5LQ0 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v
    10)) (by unfold i5LQ0; fun_prop)
  exact ⟨M, fun x hx => hM (i5LV x) (norm_i5LV_le hx)⟩

theorem i5LQ1_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i5LQ1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤
    M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 11 → ℝ => i5LQ1 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v
    10)) (by unfold i5LQ1; fun_prop)
  exact ⟨M, fun x hx => hM (i5LV x) (norm_i5LV_le hx)⟩

theorem i5LQ2_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i5LQ2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤
    M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 11 → ℝ => i5LQ2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v
    10)) (by unfold i5LQ2; fun_prop)
  exact ⟨M, fun x hx => hM (i5LV x) (norm_i5LV_le hx)⟩

/-! ### The limit -/

theorem tendsto_i5D1 : Tendsto i5D1 (𝓝[>] 0) (𝓝 (25 + π ^ 2 / 6)) := by
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) i5LQ0_bdd).add
    (i13_tendsto_mul_log_pow_mul (j := 1) i5LQ1_bdd)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) i5LQ2_bdd) |>.const_add (25 + π ^ 2 / 6)
  rw [add_zero, add_zero, add_zero] at H
  refine H.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
  rw [i5D1_eq hx]
  ring

/-- **The limit** `Φ₁ - A₁ → 25 + π²/6` as `t → ∞`. -/
theorem tendsto_i5Phi1t_sub_prim1 :
    Tendsto (fun t => i5Phi1t t - i5Prim1 t) atTop (𝓝 (25 + π ^ 2 / 6)) :=
  (tendsto_i5D1.comp tendsto_i13Xi_atTop).congr'
    (eventually_atTop.2 ⟨1, fun t ht => (i5Phi1t_sub_prim1 (by linarith)).symm⟩)

/-! ### The coefficient -/

/-- **`c₁` from the closed form of `t K₁(t)`**: if `t K₁(t) = K(ξ(t))` for `t > 0`, then
`c₁ = -4π⁴/45 - 5π²/3 - 5ζ(3) + 25`. -/
theorem i5RemCoeff_one_of_kerC
    (hK : ∀ t : ℝ, 0 < t → (t : ℂ) * i5KerC t 1 = i5K1x (i13Xi t)) :
    i5RemCoeff 1 = -4 / 45 * (π : ℂ) ^ 4 - 5 / 3 * (π : ℂ) ^ 2 - 5 * (zeta3 : ℂ) + 25 := by
  rw [i5RemCoeff_one_of_prim (g := i5G1) (Φ := i5Phi1t) (fun t ht => i5G1_eq ht (hK t ht))
    (fun t ht => hasDerivAt_i5Phi1t ht) (continuousOn_i5Phi1t.mono Icc_subset_Ici_self)
    tendsto_i5Phi1t_sub_prim1, i5Phi1t_zero]
  push_cast
  ring

end QED.ThreeLoopD
