/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R2V

/-!
# Set (d), master `I₈`: the limit of `F₂ - A₂` at infinity

As `t → ∞`, `ξ(t) → 0⁺`. In terms of `ξ` (`log t = 2 log (1 - ξ) - log ξ`), after writing every
word of `Ψ₂` in the Lyndon basis and every basis function other than `log ξ` as
`c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)` (`QED.ThreeLoopD.i13hpl_rho_01` and its companions), the difference of
the primitives is exactly (`QED.ThreeLoopD.i8D2_eq`)

  `F₂ - A₂ = 323/8 - 2π²/3 + ξ (Q₀ + Q₁ log ξ + Q₂ log² ξ)`,

with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; hence `F₂ - A₂ → 323/8 - 2π²/3`.

## Main results

* `QED.ThreeLoopD.i8D2_eq`.
* `QED.ThreeLoopD.tendsto_i8F2_sub_prim2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- `A₂(t(ξ))`, with `log t = 2 log (1 - ξ) - log ξ`. -/
noncomputable def i8Prim2x (x : ℝ) : ℝ :=
  11 / 6 * (2 * Real.log (1 - x) - Real.log x) ^ 3 +
    9 / 2 * ((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 2) +
    27 / 4 * (2 * Real.log (1 - x) - Real.log x) ^ 2 -
    π ^ 2 / 3 * (2 * Real.log (1 - x) - Real.log x) -
    21 * ((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x)) -
    105 / 4 * (2 * Real.log (1 - x) - Real.log x) - π ^ 2 / 3 * ((1 - x) ^ 2 / x) +
    33 * ((1 - x) ^ 2 / x)

/-- `F₂ - A₂` in terms of `ξ`. -/
noncomputable def i8D2 (x : ℝ) : ℝ := i8Psi2 x - i8Prim2x x

theorem i8F2_sub_prim2 {t : ℝ} (ht : 0 < t) : i8F2 t - i8Prim2 t = i8D2 (i13Xi t) := by
  have hT := (i13Xi_t ht.le).symm
  have hlog := (i8_log_eq ht).symm
  unfold i8D2 i8F2
  congr 1
  unfold i8Prim2x i8Prim2
  rw [hT, hlog]

/-- The polynomial `Q0` of the limit of `F₂ - A₂`. -/
noncomputable def i8LQ0 (x r_001 r_00m r_01 r_011 r_01m r_0m r_0m1 r_0mm r_1 r_m : ℝ) : ℝ :=
    -77 / 2 - 317 / 8 * x - 125 / 6 * x ^ 2 - 7 / 2 * r_m - 2 / 3 * π ^ 2 - r_0m / 2 +
    9 / 8 * x ^ 3 + 13 / 2 * x ^ 4 + 29 / 24 * x ^ 5 + r_m * x ^ 6 + r_m ^ 2 * x ^ 3 / 2 -
    r_m * x ^ 2 - 39 * r_1 * x ^ 3 - 28 * r_1 * x - 16 * r_1 ^ 2 * x ^ 4 - 15 * r_1 * x ^ 2 -
    8 * r_00m * x ^ 2 - 4 * r_01m * x ^ 2 - 4 * r_0m1 * x ^ 2 - 4 * r_m * x + 2 * r_001 * x ^ 2 +
    4 * r_011 * x ^ 2 + 4 * r_0m * x + 4 * r_0m * x ^ 2 + 4 * r_0m * x ^ 3 + 4 * r_0mm * x ^ 2 +
    4 * r_m * x ^ 3 + 6 * r_1 ^ 2 * x ^ 5 + 11 * r_1 * x ^ 4 + 18 * r_01 * x ^ 2 +
    21 * r_1 ^ 2 * x ^ 7 + 27 * r_1 * x ^ 5 + 28 * r_1 ^ 2 * x ^ 6 - π ^ 2 * x / 2 -
    r_m ^ 2 * x ^ 7 / 2 + 5 / 2 * r_0m * x ^ 4 + 7 / 2 * r_m * x ^ 4 + 19 / 2 * r_1 * x ^ 6 +
    44 / 3 * r_1 ^ 3 * x ^ 8 + r_1 * r_m * x ^ 7 - r_1 * r_m * x ^ 3 - 2 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The polynomial `Q1` of the limit of `F₂ - A₂`. -/
noncomputable def i8LQ1 (x _r_001 _r_00m r_01 _r_011 _r_01m r_0m _r_0m1 _r_0mm r_1 r_m : ℝ) : ℝ :=
    -25 / 2 - 3 / 2 * r_m + 17 / 2 * x + 29 / 4 * x ^ 3 + 37 / 2 * x ^ 2 - 12 * r_1 * x -
    12 * r_m * x ^ 2 - 8 * r_m * x - 8 * r_m * x ^ 3 - 4 * r_1 * x ^ 2 - 2 * r_01 * x ^ 2 +
    2 * r_0m * x ^ 2 + 22 * r_1 ^ 2 * x ^ 5 + 23 * r_1 * x ^ 4 + 32 * r_1 * x ^ 3 -
    5 / 2 * r_m * x ^ 4

/-- The polynomial `Q2` of the limit of `F₂ - A₂`. -/
noncomputable def i8LQ2 (x _r_001 _r_00m _r_01 _r_011 _r_01m _r_0m _r_0m1 _r_0mm r_1 _r_m : ℝ) : ℝ
    :=
    7 + 25 / 4 * x + 11 * r_1 * x ^ 2

theorem i8D2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8D2 x = 323 / 8 - 2 / 3 * π ^ 2 +
    x * (i8LQ0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x * i8LQ1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8LQ2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one]
    x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8D2 i8Prim2x i8Psi2 i8Psi2N0 i8Psi2N1 i8Psi2N2 i8Psi2N3 i8Psi2N4 i8Psi2W
  simp only [hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_mm hx, i13hw_10 hx, i13hw_1m hx, i13hw_11 hx,
    i13hw_000, i13hw_0m0 hx, i13hw_010 hx, i13_log_one_sub_eq hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_00m h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0,
    i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_0mm h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0]
  unfold i8LQ0 i8LQ1 i8LQ2
  field_simp
  ring

/-! ### Boundedness of the polynomials -/

/-- The vector of the arguments `ξ, ρ_w(ξ)` of the polynomials `Qⱼ`. -/
noncomputable def i8LV (x : ℝ) : Fin 11 → ℝ :=
  ![x, i13Rho [zero, zero, one] x, i13Rho [zero, zero, negOne] x, i13Rho [zero, one] x, i13Rho
    [zero, one, one] x, i13Rho [zero, one, negOne] x, i13Rho [zero, negOne] x, i13Rho [zero, negOne,
    one] x, i13Rho [zero, negOne, negOne] x, i13Rho [one] x, i13Rho [negOne] x]

theorem norm_i8LV_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : ‖i8LV x‖ ≤ 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  fin_cases i
  · show ‖x‖ ≤ 2
    rw [Real.norm_eq_abs, abs_of_pos hx.1]
    linarith [hx.2]
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
  · show ‖i13Rho [zero, negOne, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx

theorem i8LQ0_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i8LQ0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤
    M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 11 → ℝ => i8LQ0 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v
    10)) (by unfold i8LQ0; fun_prop)
  exact ⟨M, fun x hx => hM (i8LV x) (norm_i8LV_le hx)⟩

theorem i8LQ1_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i8LQ1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤
    M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 11 → ℝ => i8LQ1 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v
    10)) (by unfold i8LQ1; fun_prop)
  exact ⟨M, fun x hx => hM (i8LV x) (norm_i8LV_le hx)⟩

theorem i8LQ2_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i8LQ2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤
    M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 11 → ℝ => i8LQ2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v
    10)) (by unfold i8LQ2; fun_prop)
  exact ⟨M, fun x hx => hM (i8LV x) (norm_i8LV_le hx)⟩

/-! ### The limit -/

theorem tendsto_i8D2 : Tendsto i8D2 (𝓝[>] 0) (𝓝 (323 / 8 - 2 / 3 * π ^ 2)) := by
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) i8LQ0_bdd).add
    (i13_tendsto_mul_log_pow_mul (j := 1) i8LQ1_bdd)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) i8LQ2_bdd) |>.const_add (323 / 8 - 2 / 3 * π ^ 2)
  rw [add_zero, add_zero, add_zero] at H
  refine H.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
  rw [i8D2_eq hx]
  ring

/-- **The limit** `F₂ - A₂ → 323/8 - 2π²/3` as `t → ∞`. -/
theorem tendsto_i8F2_sub_prim2 :
    Tendsto (fun t => i8F2 t - i8Prim2 t) atTop (𝓝 (323 / 8 - 2 / 3 * π ^ 2)) :=
  (tendsto_i8D2.comp tendsto_i13Xi_atTop).congr'
    (eventually_atTop.2 ⟨1, fun t ht => (i8F2_sub_prim2 (by linarith)).symm⟩)

end QED.ThreeLoopD
