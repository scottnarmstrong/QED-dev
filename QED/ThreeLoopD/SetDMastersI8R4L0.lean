/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4F
public import QED.ThreeLoopD.SetDMastersI8R4S

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 0

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_0_eq`, `QED.ThreeLoopD.tendsto_i8L4RG0` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- `A₄(t(ξ))`, with `log t = 2 log (1 - ξ) - log ξ`. -/
noncomputable def i8Prim4x (x : ℝ) : ℝ :=
    (27 / 8) * (((1 - x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x) ^ 4) +
    (-63 / 2) * (((1 - x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x) ^ 3) +
    (297 / 2 - 3 / 2 * π ^ 2) * (((1 - x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x) ^ 2) +
    (-393 + 7 * π ^ 2 + 12 * zeta3) * (((1 - x) ^ 2 / x) * (2 * Real.log (1 - x) - Real.log x)) +
    (473 - 28 * zeta3 - 11 * π ^ 2 - π ^ 4 / 45) * ((1 - x) ^ 2 / x) +
    (179 / 120) * (2 * Real.log (1 - x) - Real.log x) ^ 5 +
    (1 / 16) * (2 * Real.log (1 - x) - Real.log x) ^ 4 +
    (-385 / 24 - 19 / 18 * π ^ 2) * (2 * Real.log (1 - x) - Real.log x) ^ 3 +
    (1131 / 16 + 10 * zeta3 - π ^ 2 / 4) * (2 * Real.log (1 - x) - Real.log x) ^ 2 +
    (-2553 / 16 + 10 * zeta3 + π ^ 4 / 30 + 49 / 12 * π ^ 2) * (2 * Real.log (1 - x) - Real.log x)

/-- `F₄ - A₄` in terms of `ξ`. -/
noncomputable def i8D4 (x : ℝ) : ℝ := i8Psi4 x - i8Prim4x x

theorem i8F4_sub_prim4 {t : ℝ} (ht : 0 < t) : i8F4 t - i8Prim4 t = i8D4 (i13Xi t) := by
  have hT := (i13Xi_t ht.le).symm
  have hlog := (i8_log_eq ht).symm
  unfold i8D4 i8F4
  congr 1
  unfold i8Prim4x i8Prim4
  rw [hT, hlog]
  ring

/-- The words `w` of the functions `ρ_w` in the polynomials `Qⱼ`. -/
def i8L4W : List (List Letter) :=
  [[zero, zero, zero, zero, one], [zero, zero, zero, zero, negOne], [zero, zero, zero, one], [zero,
    zero, zero, one, one], [zero, zero, zero, one, negOne], [zero, zero, zero, negOne], [zero, zero,
    zero, negOne, one], [zero, zero, zero, negOne, negOne], [zero, zero, one], [zero, zero, one,
    zero, one], [zero, zero, one, zero, negOne], [zero, zero, one, one], [zero, zero, one, one,
    one], [zero, zero, one, one, negOne], [zero, zero, one, negOne], [zero, zero, one, negOne, one],
    [zero, zero, one, negOne, negOne], [zero, zero, negOne], [zero, zero, negOne, zero, one], [zero,
    zero, negOne, zero, negOne], [zero, zero, negOne, one], [zero, zero, negOne, one, one], [zero,
    zero, negOne, one, negOne], [zero, zero, negOne, negOne], [zero, zero, negOne, negOne, one],
    [zero, zero, negOne, negOne, negOne], [zero, one], [zero, one, zero, one, negOne], [zero, one,
    one], [zero, one, one, one], [zero, one, one, one, one], [zero, one, one, one, negOne], [zero,
    one, one, negOne], [zero, one, one, negOne, one], [zero, one, one, negOne, negOne], [zero, one,
    negOne], [zero, one, negOne, one], [zero, one, negOne, one, one], [zero, one, negOne, one,
    negOne], [zero, one, negOne, negOne], [zero, one, negOne, negOne, one], [zero, one, negOne,
    negOne, negOne], [zero, negOne], [zero, negOne, zero, one], [zero, negOne, zero, one, one],
    [zero, negOne, zero, one, negOne], [zero, negOne, zero, negOne, one], [zero, negOne, zero,
    negOne, negOne], [zero, negOne, one], [zero, negOne, one, zero, one], [zero, negOne, one, one],
    [zero, negOne, one, one, one], [zero, negOne, one, one, negOne], [zero, negOne, one, negOne],
    [zero, negOne, one, negOne, one], [zero, negOne, one, negOne, negOne], [zero, negOne, negOne],
    [zero, negOne, negOne, zero, one], [zero, negOne, negOne, one], [zero, negOne, negOne, one,
    one], [zero, negOne, negOne, one, negOne], [zero, negOne, negOne, negOne], [zero, negOne,
    negOne, negOne, one], [zero, negOne, negOne, negOne, negOne], [one], [negOne], [negOne, one],
    [negOne, one, one], [negOne, negOne, one], [negOne, negOne, one, one]]

/-- The vector of the arguments `ξ, ρ_w(ξ)` of the polynomials `Qⱼ`. -/
noncomputable def i8L4V (x : ℝ) : Fin 71 → ℝ :=
  fun i => if (i : ℕ) = 0 then x else i13Rho (i8L4W.getD ((i : ℕ) - 1) []) x

theorem i8L4W_good : ∀ i : Fin 71, (i : ℕ) ≠ 0 →
    (i8L4W.getD ((i : ℕ) - 1) []).getLast? ≠ some zero ∧ i8L4W.getD ((i : ℕ) - 1) [] ≠ [] := by
  decide

theorem norm_i8L4V_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : ‖i8L4V x‖ ≤ 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  unfold i8L4V
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_of_pos hx.1]
    linarith [hx.2]
  · rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (i8L4W_good i h).1 (i8L4W_good i h).2 hx

/-- The singular part of `Ψ₄⁽0⁾` at `ξ = 0`. -/
noncomputable def i8L4S0 (x : ℝ) : ℝ :=
    223 / 16 + Real.log x / 16

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽0⁾`. -/
noncomputable def i8L4Q0_0 (x r_0000m r_000m r_000mm r_00m r_00m0m r_00mm r_00mmm r_0m r_0m0mm r_0mm
    r_0mmm r_0mmmm r_m : ℝ) : ℝ :=
    11 / 16 - r_00mm - 3 * x ^ 5 - 2 * r_0mmm - 199 / 24 * x ^ 3 - 47 / 12 * x - 43 / 16 * r_m -
      11 / 8 * r_0m - 3 / 2 * r_0mm - 3 / 4 * r_00m - 3 / 8 * x ^ 7 - r_000m / 2 - x ^ 9 / 96 +
      x ^ 8 / 12 + 31 / 24 * x ^ 6 + 35 / 6 * x ^ 4 + 269 / 48 * x ^ 2 + r_00mm * x ^ 4 +
      r_0mm * x ^ 6 + r_0m ^ 2 * x ^ 5 + r_m ^ 2 * x ^ 10 + r_000m * x ^ 4 / 2 +
      r_00m * x ^ 6 / 2 + r_m ^ 2 * x ^ 6 / 2 + r_m ^ 3 * x ^ 10 / 2 - r_000m * x ^ 2 -
      r_00m * x ^ 2 - r_00m * x ^ 5 - r_0m * x ^ 7 - 20 * r_000mm * x ^ 2 - 10 * r_0mm * x ^ 3 -
      8 * r_00m0m * x ^ 2 - 5 * r_m ^ 2 * x ^ 4 - 4 * r_0m * x ^ 2 - 4 * r_0mmm * x ^ 2 -
      2 * r_0000m * x ^ 2 - 2 * r_00mm * x ^ 2 - 2 * r_0mm * x ^ 5 - 2 * r_m ^ 2 * x ^ 9 +
      2 * r_00m * x + 2 * r_0mmm * x ^ 4 + 3 * r_00m * x ^ 3 + 4 * r_0m * x + 4 * r_0mm * x +
      4 * r_m ^ 2 * x ^ 5 + 16 * r_0m0mm * x ^ 2 + 16 * r_0mmmm * x ^ 2 + 40 * r_00mmm * x ^ 2 -
      95 / 8 * r_m * x ^ 2 - 37 / 4 * r_m * x ^ 5 - 25 / 6 * r_m * x ^ 7 -
      25 / 8 * r_m ^ 2 * x ^ 7 - 5 / 2 * r_0m * x ^ 5 - 2 / 3 * r_m ^ 3 * x ^ 9 -
      2 / 3 * r_m ^ 3 * x ^ 11 - r_m * x ^ 9 / 2 - r_m ^ 3 * x ^ 6 / 2 - r_m ^ 3 * x ^ 8 / 3 -
      r_00m * x ^ 4 / 4 - r_m ^ 2 * x ^ 11 / 4 - r_m ^ 4 * x ^ 13 / 6 + r_m ^ 3 * x ^ 12 / 3 +
      r_0m * x ^ 8 / 4 + r_m ^ 4 * x ^ 9 / 6 + r_0m * x ^ 4 / 8 + r_m * x ^ 10 / 12 +
      4 / 3 * r_m ^ 3 * x ^ 7 + 7 / 2 * r_0mm * x ^ 4 + 7 / 2 * r_m ^ 2 * x ^ 8 +
      7 / 4 * r_0m * x ^ 6 + 11 / 2 * r_0m * x ^ 3 + 11 / 8 * r_m ^ 2 * x ^ 3 +
      13 / 8 * r_m * x ^ 8 + 21 / 2 * r_m * x + 41 / 12 * r_m * x ^ 3 + 97 / 16 * r_m * x ^ 4 +
      163 / 24 * r_m * x ^ 6 + r_00m * r_m * x ^ 3 + r_0m * r_m * x ^ 5 +
      r_0m * r_m ^ 2 * x ^ 10 - r_00m * r_m * x ^ 7 - r_0m * r_m * x ^ 9 -
      r_0m * r_m ^ 2 * x ^ 6 - 8 * r_0m * r_0mm * x ^ 5 - 4 * r_0m * r_m * x ^ 4 -
      2 * r_0mm * r_m * x ^ 7 + 2 * r_0m * r_m * x ^ 6 + 2 * r_0m * r_m * x ^ 8 +
      2 * r_0mm * r_m * x ^ 3 + 4 * r_00m * r_0m * x ^ 5 - 3 / 2 * r_0m * r_m * x ^ 7 +
      3 / 2 * r_0m * r_m * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽0⁾`. -/
noncomputable def i8L4Q0_1 (_x _r_0000m _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_00mmm _r_0m
    _r_0m0mm _r_0mm _r_0mmm _r_0mmmm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽0⁾`. -/
noncomputable def i8L4Q0_2 (_x _r_0000m _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_00mmm _r_0m
    _r_0m0mm _r_0mm _r_0mmm _r_0mmmm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽0⁾`. -/
noncomputable def i8L4Q0_3 (_x _r_0000m _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_00mmm _r_0m
    _r_0m0mm _r_0mm _r_0mmm _r_0mmmm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽0⁾`. -/
noncomputable def i8L4Q0_4 (_x _r_0000m _r_000m _r_000mm _r_00m _r_00m0m _r_00mm _r_00mmm _r_0m
    _r_0m0mm _r_0mm _r_0mmm _r_0mmmm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s0 x = i8L4S0 x + x * (i8L4Q0_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne]
      x) + Real.log x * i8L4Q0_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q0_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q0_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q0_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s0 i8Psi4s0N0 i8Psi4s0N1 i8Psi4s0N2 i8Psi4s0N3 i8Psi4s0N4 i8Psi4s0W
  simp only [hpl_zero, i13hw_0m0m hx, i13hw_m00m hx, i13hw_m0m hx, i13hw_m0mm hx, i13hw_mm hx,
    i13hw_mmm hx, i8hw_0m00m hx, i8hw_0mm0m hx, i8hw_mm0m hx, i8hw_mmmm hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_000mm h0, i13hpl_rho_00m h0,
    i13hpl_rho_00m0m h0, i13hpl_rho_00mm h0, i13hpl_rho_00mmm h0, i13hpl_rho_0m h0, i13hpl_rho_0m0mm
    h0, i13hpl_rho_0mm h0, i13hpl_rho_0mmm h0, i8hpl_rho_0mmmm h0, i13hpl_rho_m h0]
  unfold i8L4S0 i8L4Q0_0 i8L4Q0_1 i8L4Q0_2 i8L4Q0_3 i8L4Q0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽0⁾`. -/
noncomputable def i8L4R0 (x : ℝ) : ℝ :=
  x * (i8L4Q0_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
    negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho
    [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q0_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho
    [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q0_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q0_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q0_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    negOne, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R0 : Tendsto i8L4R0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q0_0 (v 0) (v 2) (v 6) (v 8) (v 18) (v 20) (v 24) (v 26) (v 43)
      (v 48) (v 57) (v 62) (v 64) (v 66)) (by
      unfold i8L4Q0_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q0_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho
    [zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne, negOne] x)
    (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R0
  unfold i8L4Q0_1 i8L4Q0_2 i8L4Q0_3 i8L4Q0_4
  ring

/-- The singular part of `Ψ₄⁽1⁾` at `ξ = 0`. -/
noncomputable def i8L4S1 (x : ℝ) : ℝ :=
    -17 / 4 + Real.log x / 2 + Real.log x ^ 2 / 8

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽1⁾`. -/
noncomputable def i8L4Q1_0 (x r_000m r_00m r_00mm r_0m r_0mm r_0mmm r_m : ℝ) : ℝ :=
    23 / 24 - 5 * r_0mm - 4 * r_0m - 59 / 8 * r_m - 17 / 8 * x ^ 5 - 11 / 3 * x - 5 / 2 * r_00m -
      5 / 24 * x ^ 7 - 3 / 4 * x ^ 3 + 7 / 2 * x ^ 4 + 9 / 8 * x ^ 2 + 11 / 12 * x ^ 6 +
      r_m ^ 2 * x ^ 8 - r_0m * x ^ 5 - r_m ^ 2 * x ^ 6 - 8 * r_0mm * x - 8 * r_0mmm * x ^ 2 -
      5 * r_0m * x ^ 4 - 4 * r_00m * x - 4 * r_00mm * x ^ 2 - 3 * r_m * x ^ 7 -
      2 * r_000m * x ^ 2 - 2 * r_00m * x ^ 2 - 2 * r_m * x ^ 3 + 2 * r_0m ^ 2 * x ^ 5 +
      4 * r_00m * x ^ 3 + 4 * r_0m * x ^ 2 + 4 * r_0mm * x ^ 2 + 4 * r_m ^ 2 * x ^ 3 +
      4 * r_m ^ 2 * x ^ 7 + 5 * r_0m * x ^ 3 + 5 * r_0mm * x ^ 4 + 5 * r_m * x +
      8 * r_0mm * x ^ 3 - 31 / 8 * r_m * x ^ 4 - 11 / 2 * r_m ^ 2 * x ^ 5 -
      8 / 3 * r_m ^ 3 * x ^ 7 - 5 / 2 * r_m ^ 2 * x ^ 9 - 5 / 3 * r_m ^ 3 * x ^ 6 +
      5 / 2 * r_00m * x ^ 4 + 5 / 2 * r_0m * x ^ 6 + 5 / 3 * r_m ^ 3 * x ^ 10 +
      5 / 4 * r_m * x ^ 8 + 8 / 3 * r_m ^ 3 * x ^ 9 + 9 / 4 * r_m * x ^ 6 + 31 / 4 * r_m * x ^ 2 -
      8 * r_0m * r_m * x ^ 6 - 5 * r_0m * r_m * x ^ 7 + 5 * r_0m * r_m * x ^ 3 +
      8 * r_0m * r_m * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽1⁾`. -/
noncomputable def i8L4Q1_1 (x _r_000m r_00m _r_00mm r_0m r_0mm _r_0mmm r_m : ℝ) : ℝ :=
    7 / 12 - r_00m - 2 * r_0mm - 47 / 24 * x ^ 3 - 11 / 4 * r_m - 7 / 4 * x ^ 2 - 3 / 2 * r_0m -
      x ^ 6 / 6 + x ^ 4 / 6 + x ^ 5 / 8 + x ^ 7 / 12 + 7 / 12 * x + r_m * x ^ 6 +
      r_m ^ 2 * x ^ 9 + r_0m * x ^ 4 / 2 - r_00m * x ^ 4 - r_0m * x ^ 6 - r_m * x ^ 5 -
      12 * r_0mm * x ^ 2 - 8 * r_0mm * x - 8 * r_0mm * x ^ 3 - 6 * r_00m * x ^ 2 - 6 * r_m * x -
      4 * r_00m * x - 4 * r_00m * x ^ 3 - 4 * r_0m * x - 4 * r_m ^ 3 * x ^ 8 - 2 * r_0m * x ^ 2 -
      2 * r_0m * x ^ 5 - 2 * r_0mm * x ^ 4 - 2 * r_m ^ 2 * x ^ 6 + 2 * r_0m * x ^ 3 +
      2 * r_m ^ 2 * x ^ 5 + 2 * r_m ^ 2 * x ^ 8 + 4 * r_m ^ 2 * x ^ 4 + 5 * r_m * x ^ 3 -
      8 / 3 * r_m ^ 3 * x ^ 7 - 8 / 3 * r_m ^ 3 * x ^ 9 - 2 / 3 * r_m ^ 3 * x ^ 6 -
      2 / 3 * r_m ^ 3 * x ^ 10 - r_m * x ^ 2 / 2 - r_m * x ^ 8 / 2 - r_m ^ 2 * x ^ 7 / 2 +
      3 / 2 * r_m ^ 2 * x ^ 3 + 3 / 4 * r_m * x ^ 4 + 2 * r_0m * r_m * x ^ 3 +
      2 * r_0m * r_m * x ^ 7 + 8 * r_0m * r_m * x ^ 4 + 8 * r_0m * r_m * x ^ 6 +
      12 * r_0m * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽1⁾`. -/
noncomputable def i8L4Q1_2 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_0mmm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽1⁾`. -/
noncomputable def i8L4Q1_3 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_0mmm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽1⁾`. -/
noncomputable def i8L4Q1_4 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_0mmm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s1 x = i8L4S1 x + x * (i8L4Q1_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q1_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q1_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q1_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q1_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s1 i8Psi4s1N0 i8Psi4s1N1 i8Psi4s1N2 i8Psi4s1N3 i8Psi4s1N4 i8Psi4s1W i8Psi4s1N0c0
    i8Psi4s1N0c1 i8Psi4s1N1c0 i8Psi4s1N1c1 i8Psi4s1N3c0 i8Psi4s1N3c1 i8Psi4s1N4c0 i8Psi4s1N4c1
  simp only [hpl_zero, i13hw_00, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_m0
    hx, i13hw_m00m hx, i13hw_m0m hx, i13hw_m0m0 hx, i13hw_m0mm hx, i13hw_mm hx, i13hw_mm0 hx,
    i13hw_mmm hx, i13hw_mmm0 hx, i8hw_mm0m hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0mm h0, i13hpl_rho_0mmm h0, i13hpl_rho_m h0]
  unfold i8L4S1 i8L4Q1_0 i8L4Q1_1 i8L4Q1_2 i8L4Q1_3 i8L4Q1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽1⁾`. -/
noncomputable def i8L4R1 (x : ℝ) : ℝ :=
  x * (i8L4Q1_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q1_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q1_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q1_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q1_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R1 : Tendsto i8L4R1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q1_0 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 62) (v 66)) (by
      unfold i8L4Q1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q1_1 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 62) (v 66)) (by
      unfold i8L4Q1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q1_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x)
    (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q1_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R1
  unfold i8L4Q1_2 i8L4Q1_3 i8L4Q1_4
  ring

/-- The singular part of `Ψ₄⁽2⁾` at `ξ = 0`. -/
noncomputable def i8L4S2 (x : ℝ) : ℝ :=
    (28 + 2 * Real.log x ^ 2 + 8 * x + 12 * Real.log x - 2 / 3 * π ^ 2 + 8 * Real.log x * x -
      2 / 3 * x * Real.log x ^ 3 + 2 / 3 * Real.log x * π ^ 2 * x) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽2⁾`. -/
noncomputable def i8L4Q2_0 (x r_00m r_0m _r_m : ℝ) : ℝ :=
    2 - x ^ 3 + 2 * x ^ 2 - 7 / 2 * x - 2 / 3 * π ^ 2 - 16 * r_00m * x ^ 2 + 4 * r_0m * x ^ 4 +
      8 * r_0m * x + 8 * r_0m * x ^ 3 + 12 * r_0m * x ^ 2 - π ^ 2 * x / 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽2⁾`. -/
noncomputable def i8L4Q2_1 (x _r_00m r_0m r_m : ℝ) : ℝ :=
    8 + x + 2 * x ^ 3 - 12 * r_m * x ^ 2 - 8 * r_m * x - 8 * r_m * x ^ 3 - 4 * r_m * x ^ 4 +
      8 * r_0m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽2⁾`. -/
noncomputable def i8L4Q2_2 (x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    2 + x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽2⁾`. -/
noncomputable def i8L4Q2_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽2⁾`. -/
noncomputable def i8L4Q2_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s2 x = i8L4S2 x + x * (i8L4Q2_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x * i8L4Q2_1 x (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q2_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 3 * i8L4Q2_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 4 * i8L4Q2_4 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s2 i8Psi4s2N0 i8Psi4s2N1 i8Psi4s2N2 i8Psi4s2N3 i8Psi4s2N4 i8Psi4s2W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S2 i8L4Q2_0 i8L4Q2_1 i8L4Q2_2 i8L4Q2_3 i8L4Q2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽2⁾`. -/
noncomputable def i8L4R2 (x : ℝ) : ℝ :=
  x * (i8L4Q2_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q2_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q2_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q2_3 x (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q2_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R2 : Tendsto i8L4R2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q2_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q2_1 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q2_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q2_2 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q2_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q2_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q2_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q2_2 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R2
  unfold i8L4Q2_3 i8L4Q2_4
  ring

/-- The singular part of `Ψ₄⁽3⁾` at `ξ = 0`. -/
noncomputable def i8L4S3 (x : ℝ) : ℝ :=
    (-14 - Real.log x ^ 2 - 6 * Real.log x - 91 / 8 * x + π ^ 2 / 3 + x * Real.log x ^ 2 +
      x * Real.log x ^ 3 / 2 + 7 / 12 * π ^ 2 * x - Real.log x * π ^ 2 * x / 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽3⁾`. -/
noncomputable def i8L4Q3_0 (x r_00m r_0m r_m : ℝ) : ℝ :=
    -5 / 4 + x ^ 4 / 2 - 21 / 4 * r_m - 3 / 8 * x ^ 3 - x ^ 2 / 4 - x ^ 5 / 4 + π ^ 2 / 6 +
      35 / 8 * x + r_0m * x ^ 6 + r_m * x ^ 6 / 2 - r_0m * x ^ 4 - 12 * r_m * x -
      5 * r_0m * x ^ 2 - 4 * r_0m * x - 2 * r_0m * x ^ 3 + 2 * r_0m * x ^ 5 +
      12 * r_00m * x ^ 2 - 15 / 2 * r_m * x ^ 2 - π ^ 2 * x ^ 2 / 6 - π ^ 2 * x ^ 3 / 12 +
      r_m * x ^ 4 / 4 + π ^ 2 * r_m / 6 + π ^ 2 * x / 12 + π ^ 2 * r_m * x ^ 2 -
      12 * r_0m * r_m * x ^ 5 - 8 * r_0m * r_m * x ^ 4 - 8 * r_0m * r_m * x ^ 6 -
      2 * r_0m * r_m * x ^ 3 - 2 * r_0m * r_m * x ^ 7 + π ^ 2 * r_m * x ^ 4 / 6 +
      2 / 3 * π ^ 2 * r_m * x + 2 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽3⁾`. -/
noncomputable def i8L4Q3_1 (x _r_00m r_0m r_m : ℝ) : ℝ :=
    -9 / 2 + x / 2 + x ^ 5 / 2 - 5 / 2 * r_m - 5 / 4 * x ^ 3 + 5 / 2 * x ^ 2 + r_m * x ^ 4 / 2 -
      6 * r_0m * x ^ 2 - 4 * r_m * x - 4 * r_m * x ^ 2 - 4 * r_m * x ^ 5 - 2 * r_m * x ^ 6 +
      2 * r_m ^ 2 * x ^ 3 + 2 * r_m ^ 2 * x ^ 7 + 8 * r_m ^ 2 * x ^ 4 + 8 * r_m ^ 2 * x ^ 6 +
      12 * r_m ^ 2 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽3⁾`. -/
noncomputable def i8L4Q3_2 (x _r_00m _r_0m r_m : ℝ) : ℝ :=
    -1 / 2 + x ^ 2 / 2 - r_m / 2 - x / 4 + x ^ 3 / 4 - 3 * r_m * x ^ 2 - 2 * r_m * x -
      2 * r_m * x ^ 3 - r_m * x ^ 4 / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽3⁾`. -/
noncomputable def i8L4Q3_3 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽3⁾`. -/
noncomputable def i8L4Q3_4 (_x _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_3_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s3 x = i8L4S3 x + x * (i8L4Q3_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x * i8L4Q3_1 x (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q3_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x) + Real.log x ^ 3 * i8L4Q3_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 4 * i8L4Q3_4 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s3 i8Psi4s3N0 i8Psi4s3N1 i8Psi4s3N2 i8Psi4s3N3 i8Psi4s3N4 i8Psi4s3W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0m0 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m0m hx,
    i13hw_mm0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S3 i8L4Q3_0 i8L4Q3_1 i8L4Q3_2 i8L4Q3_3 i8L4Q3_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽3⁾`. -/
noncomputable def i8L4R3 (x : ℝ) : ℝ :=
  x * (i8L4Q3_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q3_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x) + Real.log x ^ 2 * i8L4Q3_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q3_3 x (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q3_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))

theorem tendsto_i8L4R3 : Tendsto i8L4R3 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q3_0 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q3_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q3_1 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q3_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q3_2 (v 0) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q3_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q3_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q3_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q3_2 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R3
  unfold i8L4Q3_3 i8L4Q3_4
  ring

/-- The singular part of `Ψ₄⁽4⁾` at `ξ = 0`. -/
noncomputable def i8L4S4 (x : ℝ) : ℝ :=
    (-14 - Real.log x ^ 2 - 34 * x - 6 * Real.log x + π ^ 2 / 3 + 2 * Real.log x * x +
      3 / 2 * x * Real.log x ^ 2 + 5 / 4 * π ^ 2 * x + 7 / 12 * x * Real.log x ^ 3 -
      7 / 12 * Real.log x * π ^ 2 * x) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽4⁾`. -/
noncomputable def i8L4Q4_0 (x r_000m r_00m r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    -13 / 8 - 27 / 8 * r_m - 23 / 8 * x ^ 3 - 21 / 4 * r_0m + π ^ 2 / 12 + 3 / 4 * x ^ 4 +
      75 / 8 * x + 109 / 8 * x ^ 2 + r_0m * x ^ 6 / 2 - r_0m * x ^ 3 - r_m * x ^ 5 -
      47 * r_m * x ^ 2 - 30 * r_0m * x ^ 2 - 24 * r_m * x - 21 * r_m * x ^ 3 - 16 * r_0m * x -
      8 * r_0m ^ 2 * x ^ 4 - 8 * r_0m ^ 2 * x ^ 6 - 6 * r_0m ^ 2 * x ^ 5 - 3 * r_0m * x ^ 5 -
      2 * r_0m ^ 2 * x ^ 3 - 2 * r_0m ^ 2 * x ^ 7 + 5 * r_00m * x ^ 2 + 6 * r_000m * x ^ 2 +
      24 * r_00mm * x ^ 2 - r_0m * x ^ 4 / 4 - r_m * x ^ 6 / 4 + π ^ 2 * x ^ 2 / 4 +
      π ^ 2 * r_0m / 6 + π ^ 2 * r_m / 12 + π ^ 2 * x / 24 + 37 / 8 * r_m * x ^ 4 +
      r_0m * r_m * x ^ 7 - r_0m * r_m * x ^ 3 - 8 * r_0m * r_m * x ^ 4 + 8 * r_0m * r_m * x ^ 6 -
      2 / 3 * π ^ 2 * r_m * x ^ 3 - π ^ 2 * r_m * x ^ 4 / 12 + π ^ 2 * r_0m * x ^ 4 / 6 +
      2 / 3 * π ^ 2 * r_0m * x + 2 / 3 * π ^ 2 * r_0m * x ^ 3 + 2 / 3 * π ^ 2 * r_m * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽4⁾`. -/
noncomputable def i8L4Q4_1 (x _r_000m r_00m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -5 - 14 * x ^ 2 - 5 / 2 * r_0m - 3 / 2 * r_m - 3 / 2 * x ^ 4 + 17 / 8 * x + 33 / 8 * x ^ 3 +
      r_m ^ 2 * x ^ 3 + r_m * x ^ 6 / 2 - r_0m * x ^ 6 - r_m ^ 2 * x ^ 7 - 24 * r_0mm * x ^ 2 -
      9 * r_m * x ^ 4 - 8 * r_0m * x - 8 * r_m * x - 8 * r_m ^ 2 * x ^ 6 - 7 * r_0m * x ^ 2 -
      6 * r_00m * x ^ 2 - 2 * r_0m * x ^ 3 - 2 * r_0m * x ^ 5 + 6 * r_m * x ^ 5 +
      8 * r_m ^ 2 * x ^ 4 + 22 * r_m * x ^ 3 + 30 * r_m * x ^ 2 - r_0m * x ^ 4 / 2 +
      2 * r_0m * r_m * x ^ 3 + 2 * r_0m * r_m * x ^ 7 + 8 * r_0m * r_m * x ^ 4 +
      8 * r_0m * r_m * x ^ 6 + 12 * r_0m * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽4⁾`. -/
noncomputable def i8L4Q4_2 (x _r_000m _r_00m _r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    -1 / 4 - 3 / 4 * x ^ 2 - r_0m / 2 - r_m / 4 - x / 8 - 2 * r_0m * x - 2 * r_0m * x ^ 3 -
      2 * r_m * x + 2 * r_m * x ^ 3 - r_0m * x ^ 4 / 2 + r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽4⁾`. -/
noncomputable def i8L4Q4_3 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽4⁾`. -/
noncomputable def i8L4Q4_4 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_4_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s4 x = i8L4S4 x + x * (i8L4Q4_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q4_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q4_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q4_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q4_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s4 i8Psi4s4N0 i8Psi4s4N1 i8Psi4s4N2 i8Psi4s4N3 i8Psi4s4N4 i8Psi4s4W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_0m0m
    hx, i13hw_0mm0 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m00m hx, i13hw_m0m hx, i13hw_m0m0 hx,
    i13hw_mm0 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S4 i8L4Q4_0 i8L4Q4_1 i8L4Q4_2 i8L4Q4_3 i8L4Q4_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽4⁾`. -/
noncomputable def i8L4R4 (x : ℝ) : ℝ :=
  x * (i8L4Q4_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [negOne] x) + Real.log x * i8L4Q4_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q4_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q4_3 x (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q4_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R4 : Tendsto i8L4R4 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q4_0 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q4_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q4_1 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q4_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q4_2 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q4_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q4_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q4_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q4_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R4
  unfold i8L4Q4_3 i8L4Q4_4
  ring

/-- The singular part of `Ψ₄⁽5⁾` at `ξ = 0`. -/
noncomputable def i8L4S5 (x : ℝ) : ℝ :=
    91 / 4 - 8 * Real.log x - 2 * Real.log x ^ 2 - π ^ 2 / 2 - Real.log x ^ 3 / 3 +
      Real.log x * π ^ 2 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽5⁾`. -/
noncomputable def i8L4Q5_0 (x r_000m _r_00m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    2 + x ^ 6 / 2 - 125 / 16 * x - 35 / 2 * x ^ 2 - 13 / 16 * x ^ 5 - x ^ 7 / 8 + π ^ 2 / 3 +
      x ^ 4 / 4 + 31 / 8 * x ^ 3 + r_0m * x ^ 8 / 2 + r_m * x ^ 5 / 2 + r_m * x ^ 8 / 2 -
      r_m * x ^ 7 - 24 * r_00mm * x ^ 2 - 6 * r_000m * x ^ 2 - 6 * r_0m ^ 2 * x ^ 5 -
      4 * r_0m * x ^ 3 - 2 * r_0m * x ^ 6 + 2 * r_0m * x ^ 5 + 2 * r_0mm * x ^ 2 +
      12 * r_m ^ 2 * x ^ 4 + 28 * r_m * x + 62 * r_m * x ^ 2 - 45 / 4 * r_m * x ^ 4 -
      r_0m * x ^ 4 / 2 - r_m ^ 2 * x ^ 9 / 2 - r_m ^ 2 * x ^ 7 / 4 - π ^ 2 * x ^ 2 / 6 -
      π ^ 2 * x ^ 5 / 24 + π ^ 2 * x ^ 3 / 6 + π ^ 2 * x / 24 + 3 / 4 * r_m * x ^ 6 +
      15 / 2 * r_m ^ 2 * x ^ 5 + 21 / 4 * r_m ^ 2 * x ^ 3 + 29 / 2 * r_0m * x ^ 2 +
      49 / 2 * r_m * x ^ 3 + π ^ 2 * r_0m * x ^ 2 - π ^ 2 * r_m ^ 2 * x ^ 5 -
      4 * r_0m * r_m * x ^ 8 - 2 * r_0m * r_m * x ^ 9 + 2 * r_0m * r_m * x ^ 7 +
      2 * r_0m * r_m ^ 2 * x ^ 6 + 2 * r_0m * r_m ^ 2 * x ^ 10 + 4 * r_0m * r_m * x ^ 6 +
      8 * r_0m * r_m * x ^ 4 + 8 * r_0m * r_m * x ^ 5 + 8 * r_0m * r_m ^ 2 * x ^ 7 +
      8 * r_0m * r_m ^ 2 * x ^ 9 + 12 * r_0m * r_m ^ 2 * x ^ 8 - 2 / 3 * π ^ 2 * r_m * x -
      2 / 3 * π ^ 2 * r_m * x ^ 2 - 2 / 3 * π ^ 2 * r_m ^ 2 * x ^ 4 -
      2 / 3 * π ^ 2 * r_m ^ 2 * x ^ 6 - π ^ 2 * r_m * x ^ 3 / 3 - π ^ 2 * r_m * x ^ 4 / 6 -
      π ^ 2 * r_m ^ 2 * x ^ 3 / 6 - π ^ 2 * r_m ^ 2 * x ^ 7 / 6 + π ^ 2 * r_m * x ^ 5 / 3 +
      π ^ 2 * r_m * x ^ 6 / 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽5⁾`. -/
noncomputable def i8L4Q5_1 (x _r_000m r_00m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    2 - 6 * x ^ 3 + 3 * x ^ 4 - 11 / 8 * x - 3 / 8 * x ^ 5 - x ^ 6 / 2 + x ^ 7 / 4 +
      23 / 2 * x ^ 2 - 12 * r_m ^ 3 * x ^ 8 - 11 * r_m * x ^ 3 - 8 * r_m ^ 3 * x ^ 7 -
      8 * r_m ^ 3 * x ^ 9 - 7 * r_m * x ^ 5 - 4 * r_0m * x ^ 2 - 2 * r_m ^ 2 * x ^ 6 -
      2 * r_m ^ 3 * x ^ 6 - 2 * r_m ^ 3 * x ^ 10 + 3 * r_m ^ 2 * x ^ 9 + 6 * r_00m * x ^ 2 +
      6 * r_m ^ 2 * x ^ 8 + 12 * r_m * x + 24 * r_0mm * x ^ 2 - 29 / 2 * r_m * x ^ 2 -
      3 / 2 * r_m * x ^ 8 - 3 / 2 * r_m ^ 2 * x ^ 7 + 5 / 2 * r_m ^ 2 * x ^ 3 +
      9 / 2 * r_m * x ^ 6 + 11 / 2 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽5⁾`. -/
noncomputable def i8L4Q5_2 (x _r_000m _r_00m _r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    -1 + x ^ 2 / 2 - x ^ 3 / 2 - x / 8 + x ^ 5 / 8 + r_m * x ^ 3 + r_m * x ^ 4 / 2 +
      r_m ^ 2 * x ^ 3 / 2 + r_m ^ 2 * x ^ 7 / 2 - r_m * x ^ 5 - 3 * r_0m * x ^ 2 + 2 * r_m * x +
      2 * r_m * x ^ 2 + 2 * r_m ^ 2 * x ^ 4 + 2 * r_m ^ 2 * x ^ 6 + 3 * r_m ^ 2 * x ^ 5 -
      r_m * x ^ 6 / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽5⁾`. -/
noncomputable def i8L4Q5_3 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽5⁾`. -/
noncomputable def i8L4Q5_4 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_5_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s5 x = i8L4S5 x + x * (i8L4Q5_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q5_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q5_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q5_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q5_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s5 i8Psi4s5N0 i8Psi4s5N1 i8Psi4s5N2 i8Psi4s5N3 i8Psi4s5N4 i8Psi4s5W i8Psi4s5N2c0
    i8Psi4s5N2c1 i8Psi4s5N3c0 i8Psi4s5N3c1 i8Psi4s5N4c0 i8Psi4s5N4c1
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_0m0m
    hx, i13hw_0mm0 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m00m hx, i13hw_m0m hx, i13hw_m0m0 hx,
    i13hw_m0mm hx, i13hw_mm hx, i13hw_mm0 hx, i13hw_mm00 hx, i13hw_mmm0 hx, i8hw_mm0m hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S5 i8L4Q5_0 i8L4Q5_1 i8L4Q5_2 i8L4Q5_3 i8L4Q5_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽5⁾`. -/
noncomputable def i8L4R5 (x : ℝ) : ℝ :=
  x * (i8L4Q5_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [negOne] x) + Real.log x * i8L4Q5_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q5_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q5_3 x (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q5_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R5 : Tendsto i8L4R5 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q5_0 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q5_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q5_1 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q5_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q5_2 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q5_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q5_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q5_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q5_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R5
  unfold i8L4Q5_3 i8L4Q5_4
  ring

/-- The singular part of `Ψ₄⁽6⁾` at `ξ = 0`. -/
noncomputable def i8L4S6 (x : ℝ) : ℝ :=
    (20 + 2 * Real.log x ^ 2 + 12 * Real.log x - 4 * x * Real.log x ^ 2 - 2 * x * Real.log x ^ 3 +
      8 * Real.log x * x) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽6⁾`. -/
noncomputable def i8L4Q6_0 (x : ℝ) : ℝ :=
    -12 - 13 / 2 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽6⁾`. -/
noncomputable def i8L4Q6_1 (x : ℝ) : ℝ :=
    20 + 5 * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽6⁾`. -/
noncomputable def i8L4Q6_2 (x : ℝ) : ℝ :=
    -6 - x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽6⁾`. -/
noncomputable def i8L4Q6_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽6⁾`. -/
noncomputable def i8L4Q6_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_6_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s6 x = i8L4S6 x + x * (i8L4Q6_0 x + Real.log x * i8L4Q6_1 x +
      Real.log x ^ 2 * i8L4Q6_2 x + Real.log x ^ 3 * i8L4Q6_3 x + Real.log x ^ 4 * i8L4Q6_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s6 i8Psi4s6N0 i8Psi4s6N1 i8Psi4s6N2 i8Psi4s6N3 i8Psi4s6N4 i8Psi4s6W
  simp only [hpl_zero, i13hw_00, i13hw_000]

  unfold i8L4S6 i8L4Q6_0 i8L4Q6_1 i8L4Q6_2 i8L4Q6_3 i8L4Q6_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽6⁾`. -/
noncomputable def i8L4R6 (x : ℝ) : ℝ :=
  x * (i8L4Q6_0 x + Real.log x * i8L4Q6_1 x + Real.log x ^ 2 * i8L4Q6_2 x +
    Real.log x ^ 3 * i8L4Q6_3 x + Real.log x ^ 4 * i8L4Q6_4 x)

theorem tendsto_i8L4R6 : Tendsto i8L4R6 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q6_0 (v 0)) (by
      unfold i8L4Q6_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q6_1 (v 0)) (by
      unfold i8L4Q6_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q6_2 (v 0)) (by
      unfold i8L4Q6_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q6_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q6_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q6_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R6
  unfold i8L4Q6_3 i8L4Q6_4
  ring

/-- The singular part of `Ψ₄⁽7⁾` at `ξ = 0`. -/
noncomputable def i8L4S7 (x : ℝ) : ℝ :=
    (-10 - Real.log x ^ 2 - 6 * Real.log x - 115 / 8 * x - 2 * Real.log x * x +
      3 * x * Real.log x ^ 2 + 7 / 6 * x * Real.log x ^ 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽7⁾`. -/
noncomputable def i8L4Q7_0 (x r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    23 / 4 - 19 / 4 * x ^ 2 - 13 / 4 * r_m - 13 / 8 * x ^ 3 + 65 / 8 * x - 16 * r_m * x +
      12 * r_000m * x ^ 2 + 16 * r_m * x ^ 3 + 19 * r_0m * x ^ 2 + 13 / 4 * r_m * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽7⁾`. -/
noncomputable def i8L4Q7_1 (x _r_000m r_00m _r_0m r_m : ℝ) : ℝ :=
    -21 / 2 + x / 2 - 5 / 2 * r_m + 5 / 4 * x ^ 3 + 11 / 2 * x ^ 2 - 27 * r_m * x ^ 2 -
      16 * r_m * x - 16 * r_m * x ^ 3 - 12 * r_00m * x ^ 2 - 5 / 2 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽7⁾`. -/
noncomputable def i8L4Q7_2 (x _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    9 / 2 - 3 / 2 * x ^ 2 - r_m / 2 - x ^ 3 / 4 + 9 / 4 * x + r_m * x ^ 4 / 2 - 4 * r_m * x +
      4 * r_m * x ^ 3 + 6 * r_0m * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽7⁾`. -/
noncomputable def i8L4Q7_3 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽7⁾`. -/
noncomputable def i8L4Q7_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_7_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s7 x = i8L4S7 x + x * (i8L4Q7_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q7_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q7_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q7_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q7_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s7 i8Psi4s7N0 i8Psi4s7N1 i8Psi4s7N2 i8Psi4s7N3 i8Psi4s7N4 i8Psi4s7W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_m0 hx,
    i13hw_m00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S7 i8L4Q7_0 i8L4Q7_1 i8L4Q7_2 i8L4Q7_3 i8L4Q7_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽7⁾`. -/
noncomputable def i8L4R7 (x : ℝ) : ℝ :=
  x * (i8L4Q7_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q7_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q7_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q7_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q7_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R7 : Tendsto i8L4R7 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q7_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q7_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q7_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q7_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q7_2 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q7_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q7_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q7_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q7_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R7
  unfold i8L4Q7_3 i8L4Q7_4
  ring

/-- The singular part of `Ψ₄⁽8⁾` at `ξ = 0`. -/
noncomputable def i8L4S8 (x : ℝ) : ℝ :=
    67 / 4 - 4 * Real.log x - 2 * Real.log x ^ 2 - Real.log x ^ 3 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽8⁾`. -/
noncomputable def i8L4Q8_0 (x r_000m r_000mm r_00m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    2 - 101 / 16 * x - 81 / 2 * x ^ 2 - 13 / 16 * x ^ 5 - 3 / 4 * x ^ 4 + 83 / 8 * x ^ 3 -
      38 * r_0mm * x ^ 2 - 24 * r_000mm * x ^ 2 - 16 * r_m ^ 2 * x ^ 6 - 14 * r_000m * x ^ 2 +
      16 * r_m ^ 2 * x ^ 4 + 20 * r_m * x + 42 * r_00m * x ^ 2 + 104 * r_m * x ^ 2 -
      109 / 4 * r_m * x ^ 4 - 13 / 4 * r_m ^ 2 * x ^ 7 + 11 / 2 * r_0m * x ^ 2 +
      13 / 4 * r_m * x ^ 6 + 13 / 4 * r_m ^ 2 * x ^ 3 + 19 / 2 * r_m * x ^ 5 + 101 / 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽8⁾`. -/
noncomputable def i8L4Q8_1 (x _r_000m _r_000mm r_00m r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    2 - 21 / 4 * x ^ 3 - 3 / 8 * x + 3 / 2 * x ^ 4 + 5 / 8 * x ^ 5 + 21 / 2 * x ^ 2 -
      42 * r_0m * x ^ 2 - 11 * r_m * x ^ 5 - 3 * r_m * x ^ 3 + 2 * r_m * x ^ 4 + 12 * r_m * x +
      14 * r_00m * x ^ 2 + 16 * r_m ^ 2 * x ^ 4 + 16 * r_m ^ 2 * x ^ 6 + 24 * r_00mm * x ^ 2 +
      27 * r_m ^ 2 * x ^ 5 - 5 / 2 * r_m * x ^ 6 - 3 / 2 * r_m * x ^ 2 + 5 / 2 * r_m ^ 2 * x ^ 3 +
      5 / 2 * r_m ^ 2 * x ^ 7

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽8⁾`. -/
noncomputable def i8L4Q8_2 (x _r_000m _r_000mm _r_00m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    -3 - 6 * x ^ 2 - 17 / 8 * x - x ^ 4 / 2 - x ^ 5 / 8 + 13 / 4 * x ^ 3 + r_m * x ^ 6 / 2 +
      r_m ^ 2 * x ^ 3 / 2 - 12 * r_0mm * x ^ 2 - 7 * r_0m * x ^ 2 - 4 * r_m ^ 2 * x ^ 6 +
      2 * r_m * x + 3 * r_m * x ^ 3 + 3 * r_m * x ^ 5 + 4 * r_m ^ 2 * x ^ 4 + 15 * r_m * x ^ 2 -
      15 / 2 * r_m * x ^ 4 - r_m ^ 2 * x ^ 7 / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽8⁾`. -/
noncomputable def i8L4Q8_3 (_x _r_000m _r_000mm _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽8⁾`. -/
noncomputable def i8L4Q8_4 (_x _r_000m _r_000mm _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_8_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s8 x = i8L4S8 x + x * (i8L4Q8_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q8_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q8_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q8_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q8_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s8 i8Psi4s8N0 i8Psi4s8N1 i8Psi4s8N2 i8Psi4s8N3 i8Psi4s8N4 i8Psi4s8W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_00mm0 hx, i13hw_0m0 hx, i13hw_0m00
    hx, i13hw_0m0m hx, i13hw_0m0m0 hx, i13hw_0mm0 hx, i13hw_0mm00 hx, i13hw_m0 hx, i13hw_m00 hx,
    i13hw_m00m hx, i13hw_m0m hx, i13hw_m0m0 hx, i13hw_mm hx, i13hw_mm0 hx, i13hw_mm00 hx, i8hw_0m00m
    hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_000mm h0, i13hpl_rho_00m h0, i13hpl_rho_00mm h0,
    i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S8 i8L4Q8_0 i8L4Q8_1 i8L4Q8_2 i8L4Q8_3 i8L4Q8_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽8⁾`. -/
noncomputable def i8L4R8 (x : ℝ) : ℝ :=
  x * (i8L4Q8_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q8_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q8_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q8_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q8_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R8 : Tendsto i8L4R8 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q8_0 (v 0) (v 6) (v 8) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q8_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q8_1 (v 0) (v 6) (v 8) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q8_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q8_2 (v 0) (v 6) (v 8) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q8_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q8_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne]
    x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q8_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q8_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R8
  unfold i8L4Q8_3 i8L4Q8_4
  ring

/-- The singular part of `Ψ₄⁽9⁾` at `ξ = 0`. -/
noncomputable def i8L4S9 (x : ℝ) : ℝ :=
    (-10 - Real.log x ^ 2 - 54 * x - 6 * Real.log x - Real.log x * x +
      5 / 4 * x * Real.log x ^ 3 + 7 / 2 * x * Real.log x ^ 2) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽9⁾`. -/
noncomputable def i8L4Q9_0 (x r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    43 / 8 - 19 / 8 * r_m - 13 / 4 * r_0m + 3 / 8 * x ^ 3 + 71 / 4 * x + 135 / 8 * x ^ 2 -
      40 * r_m * x - 40 * r_m * x ^ 3 - 23 * r_00m * x ^ 2 - 16 * r_0m * x +
      12 * r_0000m * x ^ 2 + 16 * r_0m * x ^ 3 - 301 / 4 * r_m * x ^ 2 - 19 / 8 * r_m * x ^ 4 +
      13 / 4 * r_0m * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽9⁾`. -/
noncomputable def i8L4Q9_1 (x _r_0000m r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    -11 - 9 * x ^ 2 - 5 / 2 * r_0m - 3 / 2 * r_m - x ^ 3 / 8 + 33 / 8 * x - 24 * r_m * x -
      16 * r_0m * x - 16 * r_0m * x ^ 3 - 12 * r_000m * x ^ 2 + 15 * r_0m * x ^ 2 +
      24 * r_m * x ^ 3 - 5 / 2 * r_0m * x ^ 4 + 3 / 2 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽9⁾`. -/
noncomputable def i8L4Q9_2 (x _r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    21 / 4 - r_0m / 2 - r_m / 4 + 5 / 4 * x ^ 2 + 25 / 8 * x + r_0m * x ^ 4 / 2 - 4 * r_0m * x -
      4 * r_m * x - 4 * r_m * x ^ 3 + 4 * r_0m * x ^ 3 + 6 * r_00m * x ^ 2 -
      15 / 2 * r_m * x ^ 2 - r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽9⁾`. -/
noncomputable def i8L4Q9_3 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽9⁾`. -/
noncomputable def i8L4Q9_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_9_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s9 x = i8L4S9 x + x * (i8L4Q9_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q9_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q9_2 x (i13Rho [zero, zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q9_3 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q9_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s9 i8Psi4s9N0 i8Psi4s9N1 i8Psi4s9N2 i8Psi4s9N3 i8Psi4s9N4 i8Psi4s9W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_000m0 hx, i13hw_00m0 hx, i13hw_00m00 hx, i13hw_0m0
    hx, i13hw_0m00 hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S9 i8L4Q9_0 i8L4Q9_1 i8L4Q9_2 i8L4Q9_3 i8L4Q9_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽9⁾`. -/
noncomputable def i8L4R9 (x : ℝ) : ℝ :=
  x * (i8L4Q9_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q9_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q9_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q9_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q9_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R9 : Tendsto i8L4R9 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q9_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q9_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q9_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q9_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q9_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q9_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q9_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q9_1 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q9_2 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R9
  unfold i8L4Q9_3 i8L4Q9_4
  ring

/-- The singular part of `Ψ₄⁽10⁾` at `ξ = 0`. -/
noncomputable def i8L4S10 (x : ℝ) : ℝ :=
    (30 - π ^ 2 - 4 * zeta3 + 3 * Real.log x ^ 2 + 14 * Real.log x + 16 * x + Real.log x ^ 3 / 3 +
      4 * Real.log x * x - Real.log x * π ^ 2 / 3 - x * Real.log x ^ 4 / 12 + 2 / 3 * π ^ 2 * x +
      4 * Real.log x * x * zeta3 + π ^ 2 * x * Real.log x ^ 2 / 6) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽10⁾`. -/
noncomputable def i8L4Q10_0 (x r_00m r_0m r_0mm r_m : ℝ) : ℝ :=
    17 / 2 - 4 * zeta3 + 2 * x ^ 4 - 5 / 8 * x - 2 / 3 * π ^ 2 - x ^ 5 / 2 + x ^ 3 / 4 +
      9 / 2 * x ^ 2 + r_0m * x ^ 4 + r_m * x ^ 6 - 10 * r_m * x ^ 3 - 8 * r_m * x ^ 2 -
      6 * r_00m * x ^ 2 - 5 * r_m * x ^ 4 - 2 * r_m * x ^ 5 - 2 * x * zeta3 + 2 * r_00m * x ^ 4 +
      2 * r_0m * x ^ 6 + 4 * r_00m * x + 4 * r_00m * x ^ 3 + 4 * r_0mm * x ^ 4 +
      4 * r_0m ^ 2 * x ^ 5 + 7 * r_0m * x ^ 2 + 8 * r_0m * x ^ 3 + 8 * r_0mm * x +
      8 * r_0mm * x ^ 3 + 12 * r_0m * x + 12 * r_0mm * x ^ 2 - π ^ 2 * x ^ 3 / 6 -
      π ^ 2 * x / 12 + π ^ 2 * r_m * x ^ 2 - 12 * r_0m * r_m * x ^ 5 - 8 * r_0m * r_m * x ^ 4 -
      8 * r_0m * r_m * x ^ 6 - 4 * r_0m * r_m * x ^ 7 - 2 / 3 * π ^ 2 * r_0m * x ^ 2 +
      π ^ 2 * r_m * x ^ 4 / 3 + 2 / 3 * π ^ 2 * r_m * x + 2 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽10⁾`. -/
noncomputable def i8L4Q10_1 (x r_00m r_0m r_0mm r_m : ℝ) : ℝ :=
    4 + x ^ 5 / 2 - x ^ 4 - 2 * x ^ 2 + 2 * x ^ 3 - π ^ 2 / 3 + 15 / 4 * x - 12 * r_m * x -
      8 * r_0mm * x ^ 2 - 7 * r_m * x ^ 2 - 4 * r_00m * x ^ 2 - 3 * r_m * x ^ 4 -
      2 * r_m * x ^ 6 + 2 * r_m ^ 2 * x ^ 7 + 4 * r_m ^ 2 * x ^ 4 + 4 * r_m ^ 2 * x ^ 6 +
      6 * r_0m * x ^ 2 + 6 * r_m ^ 2 * x ^ 5 - π ^ 2 * x / 6

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽10⁾`. -/
noncomputable def i8L4Q10_2 (x _r_00m r_0m _r_0mm r_m : ℝ) : ℝ :=
    2 + x ^ 3 / 2 + x / 4 - r_m * x ^ 4 - 3 * r_m * x ^ 2 - 2 * r_m * x - 2 * r_m * x ^ 3 +
      2 * r_0m * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽10⁾`. -/
noncomputable def i8L4Q10_3 (x _r_00m _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    1 / 3 + x / 6

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽10⁾`. -/
noncomputable def i8L4Q10_4 (_x _r_00m _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_10_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s10 x = i8L4S10 x + x * (i8L4Q10_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q10_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q10_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q10_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q10_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s10 i8Psi4s10N0 i8Psi4s10N1 i8Psi4s10N2 i8Psi4s10N3 i8Psi4s10N4 i8Psi4s10W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx,
    i13hw_0mm0 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_mm0 hx]
  simp only [i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S10 i8L4Q10_0 i8L4Q10_1 i8L4Q10_2 i8L4Q10_3 i8L4Q10_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽10⁾`. -/
noncomputable def i8L4R10 (x : ℝ) : ℝ :=
  x * (i8L4Q10_0 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q10_1 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q10_2 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q10_3 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q10_4 x (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R10 : Tendsto i8L4R10 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q10_0 (v 0) (v 18) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q10_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q10_1 (v 0) (v 18) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q10_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q10_2 (v 0) (v 18) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q10_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q10_3 (v 0) (v 18) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q10_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q10_0 x (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q10_1 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q10_2 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q10_3 x (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R10
  unfold i8L4Q10_4
  ring

/-- The regular parts of group 0. -/
noncomputable def i8L4RG0 (x : ℝ) : ℝ :=
  i8L4R0 x + i8L4R1 x + i8L4R2 x + i8L4R3 x + i8L4R4 x + i8L4R5 x + i8L4R6 x + i8L4R7 x +
    i8L4R8 x + i8L4R9 x + i8L4R10 x

theorem tendsto_i8L4RG0 : Tendsto i8L4RG0 (𝓝[>] 0) (𝓝 0) := by
  have H := ((((((((((tendsto_i8L4R0.add tendsto_i8L4R1).add tendsto_i8L4R2).add tendsto_i8L4R3).add
    tendsto_i8L4R4).add tendsto_i8L4R5).add tendsto_i8L4R6).add tendsto_i8L4R7).add
    tendsto_i8L4R8).add tendsto_i8L4R9).add tendsto_i8L4R10)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
