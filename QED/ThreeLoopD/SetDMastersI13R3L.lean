/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R3S
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Set (d), master `I₁₃`: the limit of `F₃ - A₃` at infinity

As `t → ∞`, `ξ(t) → 0⁺`. In terms of `ξ` (`log t = 2 log (1 - ξ) - log ξ`), after writing every
word of `Ψ₃` in the Lyndon basis and every basis function other than `log ξ` as
`c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)` (`QED.ThreeLoopD.i13hpl_rho_01` and its companions), the difference of
the primitives is exactly (`QED.ThreeLoopD.i13D3_eq`)

  `F₃ - A₃ = π²/3 - 4ζ(3) - 843/8 + ξ (Q₀ + Q₁ log ξ + Q₂ log² ξ + Q₃ log³ ξ)`,

with polynomials `Qⱼ` in `ξ` and the `ρ_w(ξ)`: all negative powers of `ξ` cancel. The `ρ_w` are
bounded (`QED.ThreeLoopD.abs_i13Rho_le`), so the `Qⱼ` are bounded near `0` (by compactness), and
`ξ logʲ ξ → 0`; hence `F₃ - A₃ → π²/3 - 4ζ(3) - 843/8`.

## Main results

* `QED.ThreeLoopD.i13D3_eq`.
* `QED.ThreeLoopD.tendsto_i13F3_sub_prim3`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- `A₃(t(ξ))`, with `log t = 2 log (1 - ξ) - log ξ`. -/
noncomputable def i13Prim3x (x : ℝ) : ℝ :=
    (-9 / 4) * (((1 - x) ^ 2 / x) ^ 2 * (2 * Real.log (1 - x) - Real.log x) ^ 3) +
    (99 / 8) * (((1 - x) ^ 2 / x) ^ 2 * (2 * Real.log (1 - x) - Real.log x) ^ 2) + (-243 / 8 +
    π ^ 2 / 2) * (((1 - x) ^ 2 / x) ^ 2 * (2 * Real.log (1 - x) - Real.log x)) + (499 / 16 -
    2 * zeta3 - 11 / 12 * π ^ 2) * (((1 - x) ^ 2 / x) ^ 2) + (-38 / 3) * (((1 -
    x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x) ^ 3) + (50) * (((1 -
    x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x) ^ 2) + (-92 + 8 / 3 * π ^ 2) * (((1 -
    x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x)) + (64 - 8 * zeta3 -
    10 / 3 * π ^ 2) * (((1 - x) ^ 2 / x)) + (7 / 6) * ((2 * Real.log (1 - x) -
    Real.log x) ^ 4) + (-56 / 3) * ((2 * Real.log (1 - x) - Real.log x) ^ 3) + (15 -
    2 / 3 * π ^ 2) * ((2 * Real.log (1 - x) - Real.log x) ^ 2) + (43 / 2 + 8 * zeta3 +
    13 / 3 * π ^ 2) * ((2 * Real.log (1 - x) - Real.log x))

theorem i13hw_0000 (x : ℝ) : hpl [zero, zero, zero, zero] x = Real.log x ^ 4 / 24 := by
  rw [hpl_of_allZero (by decide)]
  simp [Nat.factorial]

/-- `F₃ - A₃` in terms of `ξ`. -/
noncomputable def i13D3 (x : ℝ) : ℝ := i13Psi3 x - i13Prim3x x

theorem i13F3_sub_prim3 {t : ℝ} (ht : 0 < t) : i13F3 t - i13Prim3 t = i13D3 (i13Xi t) := by
  have hT := (i13Xi_t ht.le).symm
  have hlog := (i13_log_eq_xi ht).symm
  unfold i13D3 i13F3
  congr 1
  unfold i13Prim3x i13Prim3
  rw [hT, hlog]

/-- The polynomial `Q0` of the limit of `F₃ - A₃`. -/
noncomputable def i13LQ0 (x r_0001 r_000m r_001 r_0011 r_00m r_01 _r_011 _r_01m r_0m r_0m01 _r_0m1
    r_0mm r_1 r_m : ℝ) : ℝ :=
    205 / 6 + 2 * r_00m + 4 * r_0mm + 5 * π ^ 2 + 11 * r_0m + 16 * zeta3 - 2635 / 12 * x ^ 3 -
    661 / 6 * x ^ 2 - 593 / 3 * x ^ 4 - 283 / 3 * x ^ 5 - 81 / 2 * r_1 - 79 / 3 * x ^ 6 -
    10 / 3 * x ^ 7 + 57 / 2 * x + r_m * x ^ 2 - r_m * x ^ 6 - 341 * r_1 * x ^ 6 -
    328 * r_1 ^ 2 * x ^ 7 - 220 * r_1 ^ 2 * x ^ 6 - 212 * r_1 ^ 2 * x ^ 8 - 132 * r_1 * x ^ 7 -
    72 * r_1 * x - 72 * r_1 ^ 2 * x ^ 4 - 54 * r_1 ^ 2 * x ^ 5 - 54 * r_1 ^ 2 * x ^ 9 -
    44 * r_001 * x ^ 2 - 44 * r_1 ^ 2 * x ^ 3 - 37 * r_1 * x ^ 2 - 32 * r_1 ^ 3 * x ^ 7 -
    24 * r_000m * x ^ 2 - 20 * r_1 * x ^ 3 - 16 * r_0011 * x ^ 2 - 16 * r_0m01 * x ^ 2 -
    8 * r_0m * x ^ 3 - 8 * r_0m ^ 2 * x ^ 5 - 4 * r_01 * x ^ 4 - 4 * r_0m * x ^ 6 -
    4 * r_0mm * x ^ 4 - 4 * r_m * x - 3 * r_0m * x ^ 4 - 2 * r_00m * x ^ 4 + 4 * r_0m * x ^ 2 +
    4 * r_m * x ^ 5 + 8 * r_0m * x + 12 * x * zeta3 + 16 * r_01 * x ^ 3 + 24 * r_0001 * x ^ 2 +
    24 * r_00m * x ^ 2 - 1376 / 3 * r_1 * x ^ 5 - 547 / 2 * r_1 * x ^ 4 -
    320 / 3 * r_1 ^ 3 * x ^ 9 - 164 / 3 * r_1 ^ 3 * x ^ 10 - 152 / 3 * r_1 ^ 3 * x ^ 8 -
    67 / 3 * r_1 * x ^ 8 - 56 / 3 * r_1 ^ 4 * x ^ 11 - 52 / 3 * r_1 ^ 3 * x ^ 6 +
    π ^ 2 * r_m / 3 + 2 / 3 * π ^ 2 * r_1 + 3 / 2 * π ^ 2 * x ^ 3 + 13 / 3 * π ^ 2 * x ^ 2 +
    43 / 6 * π ^ 2 * x - 4 * r_0m * r_1 * x ^ 7 - 4 * r_0m * r_m * x ^ 3 +
    4 * π ^ 2 * r_1 * x ^ 2 + 4 * π ^ 2 * r_1 * x ^ 4 + 4 * r_0m * r_1 * x ^ 3 +
    4 * r_0m * r_m * x ^ 7 + 16 * r_01 * r_0m * x ^ 5 + 16 * r_1 * zeta3 * x ^ 2 -
    4 / 3 * π ^ 2 * r_01 * x ^ 2 - π ^ 2 * r_m * x ^ 4 / 3 + 4 / 3 * π ^ 2 * r_0m * x ^ 2 +
    4 / 3 * π ^ 2 * r_1 * x + 8 / 3 * π ^ 2 * r_1 ^ 2 * x ^ 5 + 20 / 3 * π ^ 2 * r_1 * x ^ 3

/-- The polynomial `Q1` of the limit of `F₃ - A₃`. -/
noncomputable def i13LQ1 (x _r_0001 _r_000m r_001 _r_0011 r_00m r_01 r_011 r_01m r_0m _r_0m01 r_0m1
    r_0mm r_1 r_m : ℝ) : ℝ :=
    14 - 182 * x ^ 3 - 143 * x - 66 * x ^ 4 - 33 * r_1 - 11 * r_m + 4 * r_0m - 712 / 3 * x ^ 2 -
    79 / 6 * x ^ 5 + 8 / 3 * π ^ 2 - 339 * r_1 * x ^ 4 - 228 * r_1 * x ^ 3 - 212 * r_1 * x ^ 5 -
    160 * r_1 ^ 2 * x ^ 6 - 84 * r_1 ^ 2 * x ^ 7 - 76 * r_1 ^ 2 * x ^ 5 - 64 * r_1 * x -
    58 * r_1 * x ^ 6 - 50 * r_1 * x ^ 2 - 48 * r_1 ^ 2 * x ^ 4 - 24 * r_001 * x ^ 2 -
    24 * r_1 ^ 2 * x ^ 3 - 16 * r_01m * x ^ 2 - 16 * r_0m1 * x ^ 2 - 8 * r_m * x -
    4 * r_m * x ^ 2 - 2 * r_m ^ 2 * x ^ 7 + 2 * π ^ 2 * x + 2 * r_m ^ 2 * x ^ 3 +
    4 * r_m * x ^ 6 + 8 * r_0m * x + 8 * r_0m * x ^ 3 + 8 * r_m * x ^ 3 + 11 * r_m * x ^ 4 +
    16 * r_011 * x ^ 2 + 16 * r_0mm * x ^ 2 + 32 * r_00m * x ^ 2 + 44 * r_01 * x ^ 2 -
    112 / 3 * r_1 ^ 3 * x ^ 8 - 4 * r_1 * r_m * x ^ 3 + 4 * r_1 * r_m * x ^ 7 +
    8 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The polynomial `Q2` of the limit of `F₃ - A₃`. -/
noncomputable def i13LQ2 (x _r_0001 _r_000m _r_001 _r_0011 _r_00m r_01 _r_011 _r_01m r_0m _r_0m01
    _r_0m1 _r_0mm r_1 r_m : ℝ) : ℝ :=
    -64 - 48 * x ^ 2 - 15 * x ^ 3 - 9 * r_1 - 5 * r_m - 169 / 2 * x + r_m * x ^ 4 -
    76 * r_1 * x ^ 3 - 48 * r_1 * x ^ 2 - 43 * r_1 * x ^ 4 - 28 * r_1 ^ 2 * x ^ 5 -
    20 * r_1 * x - 12 * r_0m * x ^ 2 - 12 * r_m * x ^ 2 - 8 * r_m * x - 8 * r_m * x ^ 3 +
    12 * r_01 * x ^ 2

/-- The polynomial `Q3` of the limit of `F₃ - A₃`. -/
noncomputable def i13LQ3 (x _r_0001 _r_000m _r_001 _r_0011 _r_00m _r_01 _r_011 _r_01m _r_0m _r_0m01
    _r_0m1 _r_0mm r_1 _r_m : ℝ) : ℝ :=
    -28 / 3 - 7 * x - 28 / 3 * r_1 * x ^ 2

theorem i13D3_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i13D3 x = -843 / 8 - 4 * zeta3 + π ^ 2 / 3 +
    x * (i13LQ0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x * i13LQ1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i13LQ2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i13LQ3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i13D3 i13Prim3x i13Psi3 i13Psi3N0 i13Psi3N1 i13Psi3N2 i13Psi3N3 i13Psi3N4 i13Psi3W
  simp only [hpl_zero, i13hw_0000, i13hw_00, i13hw_m0 hx, i13hw_10 hx, i13hw_11 hx, i13hw_000,
    i13hw_0m0 hx, i13hw_010 hx, i13hw_m00 hx, i13hw_m01 hx, i13hw_mm0 hx, i13hw_m10 hx, i13hw_100
    hx, i13hw_101 hx, i13hw_1m0 hx, i13hw_110 hx, i13hw_111 hx, i13hw_00m0 hx, i13hw_0010 hx,
    i13hw_0m00 hx, i13hw_0mm0 hx, i13hw_0m10 hx, i13hw_0100 hx, i13hw_0101 hx, i13hw_01m0 hx,
    i13hw_0110 hx, i13_log_one_sub_eq hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_000m h0, i13hpl_rho_001 h0, i13hpl_rho_0011 h0,
    i13hpl_rho_00m h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_0mm h0, i13hpl_rho_1 h0, i13hpl_rho_m h0]
  unfold i13LQ0 i13LQ1 i13LQ2 i13LQ3
  field_simp
  ring

/-! ### Boundedness of the polynomials -/

theorem i13_bdd_of_continuous {N : ℕ} {F : (Fin N → ℝ) → ℝ} (hF : Continuous F) :
    ∃ M, ∀ v : Fin N → ℝ, ‖v‖ ≤ 2 → |F v| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin N → ℝ) 2).exists_bound_of_continuousOn
    hF.continuousOn
  exact ⟨M, fun v hv => by simpa using hM v (mem_closedBall_zero_iff.2 hv)⟩

/-- The vector of the arguments `ξ, ρ_w(ξ)` of the polynomials `Qⱼ`. -/
noncomputable def i13LV (x : ℝ) : Fin 15 → ℝ :=
  ![x, i13Rho [zero, zero, zero, one] x, i13Rho [zero, zero, zero, negOne] x, i13Rho [zero, zero,
    one] x, i13Rho [zero, zero, one, one] x, i13Rho [zero, zero, negOne] x, i13Rho [zero, one] x,
    i13Rho [zero, one, one] x, i13Rho [zero, one, negOne] x, i13Rho [zero, negOne] x, i13Rho [zero,
    negOne, zero, one] x, i13Rho [zero, negOne, one] x, i13Rho [zero, negOne, negOne] x, i13Rho
    [one] x, i13Rho [negOne] x]

theorem norm_i13LV_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : ‖i13LV x‖ ≤ 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  fin_cases i
  · show ‖x‖ ≤ 2
    rw [Real.norm_eq_abs, abs_of_pos hx.1]
    linarith [hx.2]
  · show ‖i13Rho [zero, zero, zero, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, zero, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, one, one] x‖ ≤ 2
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
  · show ‖i13Rho [zero, negOne, zero, one] x‖ ≤ 2
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

theorem i13LQ0_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i13LQ0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤ M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 15 → ℝ => i13LQ0 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) (v 14)) (by unfold i13LQ0; fun_prop)
  exact ⟨M, fun x hx => hM (i13LV x) (norm_i13LV_le hx)⟩

theorem i13LQ1_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i13LQ1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤ M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 15 → ℝ => i13LQ1 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) (v 14)) (by unfold i13LQ1; fun_prop)
  exact ⟨M, fun x hx => hM (i13LV x) (norm_i13LV_le hx)⟩

theorem i13LQ2_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i13LQ2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤ M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 15 → ℝ => i13LQ2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) (v 14)) (by unfold i13LQ2; fun_prop)
  exact ⟨M, fun x hx => hM (i13LV x) (norm_i13LV_le hx)⟩

theorem i13LQ3_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i13LQ3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)| ≤ M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 15 → ℝ => i13LQ3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) (v 14)) (by unfold i13LQ3; fun_prop)
  exact ⟨M, fun x hx => hM (i13LV x) (norm_i13LV_le hx)⟩

/-! ### The limit -/

theorem i13_tendsto_mul_log_pow (j : ℕ) :
    Tendsto (fun x : ℝ => x * Real.log x ^ j) (𝓝[>] 0) (𝓝 0) := by
  rcases j with _ | n
  · simp only [pow_zero, mul_one]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hr : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  have h := (tendsto_log_mul_rpow_nhdsGT_zero hr).pow (n + 1)
  rw [zero_pow (Nat.succ_ne_zero n)] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [mul_pow, ← Real.rpow_natCast (x ^ _), ← Real.rpow_mul hx.le]
  rw [show 1 / ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) = 1 by field_simp, Real.rpow_one]
  ring

theorem i13_tendsto_mul_log_pow_mul {j : ℕ} {f : ℝ → ℝ} (hf : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |f x| ≤ M) : Tendsto (fun x : ℝ => x * (Real.log x ^ j * f x)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hf
  have h := ((i13_tendsto_mul_log_pow j).abs.mul_const M)
  rw [abs_zero, zero_mul] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
  rw [Real.norm_eq_abs, ← mul_assoc, abs_mul]
  exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)

theorem tendsto_i13D3 : Tendsto i13D3 (𝓝[>] 0) (𝓝 (-843 / 8 - 4 * zeta3 + π ^ 2 / 3)) := by
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) i13LQ0_bdd).add
    (i13_tendsto_mul_log_pow_mul (j := 1) i13LQ1_bdd)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) i13LQ2_bdd)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) i13LQ3_bdd) |>.const_add
    (-843 / 8 - 4 * zeta3 + π ^ 2 / 3)
  rw [add_zero, add_zero, add_zero, add_zero] at H
  refine H.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
  rw [i13D3_eq hx]
  ring

/-- **The limit** `F₃ - A₃ → π²/3 - 4ζ(3) - 843/8` as `t → ∞`. -/
theorem tendsto_i13F3_sub_prim3 :
    Tendsto (fun t => i13F3 t - i13Prim3 t) atTop (𝓝 (-843 / 8 - 4 * zeta3 + π ^ 2 / 3)) :=
  (tendsto_i13D3.comp tendsto_i13Xi_atTop).congr'
    (eventually_atTop.2 ⟨1, fun t ht => (i13F3_sub_prim3 (by linarith)).symm⟩)

end QED.ThreeLoopD
