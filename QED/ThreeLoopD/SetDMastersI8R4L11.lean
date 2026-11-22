/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L10
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 11

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_115k1_eq`, `QED.ThreeLoopD.tendsto_i8L4RG11` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽115k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S115k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽115k1⁾`. -/
noncomputable def i8L4Q115k1_0 (x r_001m r_00m r_00m1m r_00mm1 r_01 r_01m r_01mm r_0m r_0m01m r_0m1
    r_0m1m r_0mm1 r_1 r_m r_m1 r_mm1 : ℝ) : ℝ :=
    1 / 2 + x ^ 3 / 2 - r_mm1 + 2 * r_0m1m + 2 * r_0mm1 + 4 * r_01mm - 3 / 2 * x ^ 2 -
      3 / 8 * x ^ 5 + x / 4 + 3 / 4 * x ^ 4 + r_0m1 * x ^ 2 + r_m1 * x + r_m1 * x ^ 4 +
      r_m1 * x ^ 5 + r_0m * x ^ 2 / 2 + r_m * x ^ 3 / 2 - r_01 * x ^ 2 - r_01m * x ^ 4 -
      r_01m * x ^ 6 - r_1 * x ^ 5 - r_mm1 * x ^ 4 - 8 * r_00m1m * x ^ 2 - 8 * r_0m01m * x ^ 2 -
      4 * r_001m * x ^ 2 - 4 * r_01m * x - 4 * r_01mm * x ^ 4 - 2 * r_0m1m * x ^ 4 -
      2 * r_0mm1 * x ^ 4 - 2 * r_m1 * x ^ 3 + 2 * r_00m * x ^ 2 + 2 * r_01m * x ^ 3 +
      2 * r_01m * x ^ 5 + 2 * r_1 * x ^ 4 + 2 * r_mm1 * x ^ 2 + 3 * r_01m * x ^ 2 +
      3 * r_m * x ^ 2 + 8 * r_00mm1 * x ^ 2 - 7 / 2 * r_1 * x ^ 3 - 5 / 4 * r_m * x ^ 4 -
      r_m1 * x ^ 6 / 2 + r_1 * x ^ 6 / 4 + 3 / 4 * r_m * x ^ 6 + 7 / 2 * r_m1 * x ^ 2 +
      9 / 4 * r_1 * x ^ 2 + r_1 * r_m * x ^ 4 + r_1 * r_m * x ^ 6 + r_m * r_m1 * x ^ 3 +
      r_m * r_m1 * x ^ 7 - 2 * r_01m * r_m * x ^ 3 - 2 * r_m * r_m1 * x ^ 5 +
      2 * r_01m * r_m * x ^ 7 - 3 / 2 * r_1 * r_m * x ^ 5 - r_1 * r_m * x ^ 7 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽115k1⁾`. -/
noncomputable def i8L4Q115k1_1 (x _r_001m _r_00m _r_00m1m _r_00mm1 _r_01 r_01m _r_01mm r_0m _r_0m01m
    _r_0m1 r_0m1m _r_0mm1 r_1 r_m r_m1 r_mm1 : ℝ) : ℝ :=
    x ^ 3 / 2 - 4 * r_mm1 - x / 2 - x ^ 2 / 2 - x ^ 4 / 2 + x ^ 5 / 4 + r_m1 * x ^ 6 -
      r_m * x ^ 3 - r_m1 * x ^ 4 - 2 * r_0m * x ^ 2 - 2 * r_1 * x ^ 3 - 2 * r_m * x ^ 4 -
      2 * r_m1 * x ^ 5 + 2 * r_01m * x ^ 2 + 2 * r_1 * x ^ 2 + 2 * r_1 * x ^ 5 +
      2 * r_m1 * x ^ 3 + 4 * r_mm1 * x ^ 4 + 8 * r_0m1m * x ^ 2 - 3 / 2 * r_1 * x ^ 4 -
      r_1 * x ^ 6 / 2 - r_m * x ^ 6 / 2 + 3 / 2 * r_m * x ^ 2 + r_1 * r_m * x ^ 7 -
      r_1 * r_m * x ^ 5 - 2 * r_1 * r_m * x ^ 6 - 2 * r_m * r_m1 * x ^ 7 + 2 * r_1 * r_m * x ^ 4 +
      2 * r_m * r_m1 * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽115k1⁾`. -/
noncomputable def i8L4Q115k1_2 (_x _r_001m _r_00m _r_00m1m _r_00mm1 _r_01 _r_01m _r_01mm _r_0m
    _r_0m01m _r_0m1 _r_0m1m _r_0mm1 _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽115k1⁾`. -/
noncomputable def i8L4Q115k1_3 (_x _r_001m _r_00m _r_00m1m _r_00mm1 _r_01 _r_01m _r_01mm _r_0m
    _r_0m01m _r_0m1 _r_0m1m _r_0mm1 _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽115k1⁾`. -/
noncomputable def i8L4Q115k1_4 (_x _r_001m _r_00m _r_00m1m _r_00mm1 _r_01 _r_01m _r_01mm _r_0m
    _r_0m01m _r_0m1 _r_0m1m _r_0mm1 _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

theorem i8L4_115k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s115k1 x = i8L4S115k1 x + x * (i8L4Q115k1_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero,
      negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x * i8L4Q115k1_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero,
      negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x ^ 2 * i8L4Q115k1_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero,
      negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x ^ 3 * i8L4Q115k1_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero,
      negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x ^ 4 * i8L4Q115k1_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero,
      negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s115k1 i8Psi4s115k1N0 i8Psi4s115k1N1 i8Psi4s115k1N2 i8Psi4s115k1N3 i8Psi4s115k1N4
    i8Psi4s115k1W
  simp only [hpl_zero, i13hw_010m hx, i13hw_01m0 hx, i13hw_0m0 hx, i13hw_0m1m0 hx, i13hw_10m hx,
    i13hw_1m hx, i13hw_1m0 hx, i13hw_m0 hx, i13hw_m1m0 hx, i8hw_0m10m hx, i8hw_m10m hx, i8hw_m1m hx]
  simp only [i13hpl_rho_001m h0, i13hpl_rho_00m h0, i8hpl_rho_00m1m h0, i8hpl_rho_00mm1 h0,
    i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_01mm h0, i13hpl_rho_0m h0, i8hpl_rho_0m01m h0,
    i13hpl_rho_0m1 h0, i13hpl_rho_0m1m h0, i13hpl_rho_0mm1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0, i8hpl_rho_mm1 h0]
  unfold i8L4S115k1 i8L4Q115k1_0 i8L4Q115k1_1 i8L4Q115k1_2 i8L4Q115k1_3 i8L4Q115k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽115k1⁾`. -/
noncomputable def i8L4R115k1 (x : ℝ) : ℝ :=
  x * (i8L4Q115k1_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x * i8L4Q115k1_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 2 * i8L4Q115k1_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 3 * i8L4Q115k1_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 4 * i8L4Q115k1_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x) (i13Rho [zero, zero, negOne, negOne,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x))

theorem tendsto_i8L4R115k1 : Tendsto i8L4R115k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q115k1_0 (v 0) (v 15) (v 18) (v 23) (v 25) (v 27) (v 36) (v 40)
      (v 43) (v 46) (v 49) (v 54) (v 59) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q115k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q115k1_1 (v 0) (v 15) (v 18) (v 23) (v 25) (v 27) (v 36) (v 40)
      (v 43) (v 46) (v 49) (v 54) (v 59) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q115k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q115k1_0 x (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one, negOne]
    x) (i13Rho [zero, zero, negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne]
    x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) (i13Rho [negOne, negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q115k1_1 x (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one, negOne] x)
      (i13Rho [zero, zero, negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one,
      negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R115k1
  unfold i8L4Q115k1_2 i8L4Q115k1_3 i8L4Q115k1_4
  ring

/-- The singular part of `Ψ₄⁽115k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S115k2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽115k2⁾`. -/
noncomputable def i8L4Q115k2_0 (x r_001mm r_00m r_00mm _r_01mm r_0m r_0mm r_1 r_m r_m1 r_mm1 : ℝ) :
    ℝ :=
    1 / 2 + r_mm1 - x ^ 6 / 8 + x ^ 4 / 8 + x ^ 3 / 16 + x ^ 7 / 16 + r_1 * x ^ 5 +
      r_mm1 * x ^ 4 + r_1 * x ^ 2 / 2 + r_m * x ^ 3 / 2 + r_m * x ^ 6 / 2 + r_m1 * x ^ 2 / 2 +
      r_m1 * x ^ 6 / 2 + r_m ^ 2 * x ^ 6 / 2 + r_m ^ 2 * x ^ 8 / 2 - r_m1 * x - r_m1 * x ^ 4 -
      r_m1 * x ^ 5 - 8 * r_001mm * x ^ 2 - 2 * r_0mm * x ^ 2 - 2 * r_mm1 * x ^ 2 +
      2 * r_00m * x ^ 2 + 2 * r_00mm * x ^ 2 + 2 * r_m1 * x ^ 3 + 2 * r_m ^ 2 * x ^ 4 -
      7 / 2 * r_0m * x ^ 2 - 7 / 8 * r_1 * x ^ 4 - 3 / 2 * r_m * x ^ 4 - r_1 * x ^ 3 / 2 -
      r_1 * x ^ 7 / 2 - r_m * x ^ 5 / 2 - r_m * x ^ 8 / 4 + r_1 * x ^ 6 / 4 +
      r_m ^ 2 * x ^ 9 / 4 + r_1 * x ^ 8 / 8 + 5 / 4 * r_m * x ^ 2 + 11 / 4 * r_m ^ 2 * x ^ 5 +
      r_1 * r_m * x ^ 4 + r_1 * r_m * x ^ 7 + r_1 * r_m * x ^ 8 + r_1 * r_m ^ 2 * x ^ 6 / 2 +
      r_1 * r_m ^ 2 * x ^ 10 / 2 - r_1 * r_m ^ 2 * x ^ 8 - r_m * r_m1 * x ^ 3 -
      r_m * r_m1 * x ^ 7 - 2 * r_1 * r_m * x ^ 6 + 2 * r_m * r_m1 * x ^ 5 -
      r_1 * r_m * x ^ 5 / 2 - r_1 * r_m * x ^ 9 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽115k2⁾`. -/
noncomputable def i8L4Q115k2_1 (x _r_001mm _r_00m _r_00mm r_01mm r_0m r_0mm r_1 r_m r_m1 r_mm1 : ℝ)
    : ℝ :=
    -1 + x ^ 3 / 2 + 2 * r_mm1 - 3 / 2 * x ^ 2 - x ^ 5 / 8 - x ^ 7 / 8 + x ^ 4 / 4 + x ^ 6 / 4 +
      r_1 * x ^ 2 + r_1 * x ^ 7 + r_m * x ^ 3 + r_m1 * x ^ 2 + r_m ^ 2 * x ^ 5 +
      r_m * x ^ 8 / 2 - r_1 * x ^ 3 - r_1 * x ^ 6 - r_m1 * x ^ 6 - r_m ^ 2 * x ^ 6 -
      r_m ^ 2 * x ^ 8 - 2 * r_0m * x ^ 2 - 2 * r_0mm * x ^ 2 - 2 * r_m1 * x - 2 * r_mm1 * x ^ 4 +
      2 * r_m1 * x ^ 5 + 2 * r_m ^ 2 * x ^ 4 + 8 * r_01mm * x ^ 2 - 5 / 2 * r_m * x ^ 4 -
      r_m * x ^ 6 / 2 - r_m ^ 2 * x ^ 7 / 2 - r_m ^ 2 * x ^ 9 / 2 - r_1 * x ^ 8 / 4 +
      r_1 * x ^ 4 / 4 + 7 / 2 * r_m * x ^ 2 + r_1 * r_m * x ^ 9 + r_1 * r_m ^ 2 * x ^ 6 -
      r_1 * r_m * x ^ 5 - r_1 * r_m ^ 2 * x ^ 10 - 2 * r_1 * r_m * x ^ 8 -
      2 * r_m * r_m1 * x ^ 3 + 2 * r_1 * r_m * x ^ 4 + 2 * r_m * r_m1 * x ^ 7

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽115k2⁾`. -/
noncomputable def i8L4Q115k2_2 (_x _r_001mm _r_00m _r_00mm _r_01mm _r_0m _r_0mm _r_1 _r_m _r_m1
    _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽115k2⁾`. -/
noncomputable def i8L4Q115k2_3 (_x _r_001mm _r_00m _r_00mm _r_01mm _r_0m _r_0mm _r_1 _r_m _r_m1
    _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽115k2⁾`. -/
noncomputable def i8L4Q115k2_4 (_x _r_001mm _r_00m _r_00mm _r_01mm _r_0m _r_0mm _r_1 _r_m _r_m1
    _r_mm1 : ℝ) : ℝ :=
    0

theorem i8L4_115k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s115k2 x = i8L4S115k2 x + x * (i8L4Q115k2_0 x (i13Rho [zero, zero, one, negOne, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
      Real.log x * i8L4Q115k2_1 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
      Real.log x ^ 2 * i8L4Q115k2_2 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
      Real.log x ^ 3 * i8L4Q115k2_3 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
      Real.log x ^ 4 * i8L4Q115k2_4 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s115k2 i8Psi4s115k2N0 i8Psi4s115k2N1 i8Psi4s115k2N2 i8Psi4s115k2N3 i8Psi4s115k2N4
    i8Psi4s115k2W
  simp only [hpl_zero, i13hw_01mm0 hx, i13hw_0m0 hx, i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_10mm hx,
    i13hw_1m0m hx, i13hw_1mm hx, i13hw_1mm0 hx, i13hw_m0 hx, i13hw_m0m hx, i13hw_mm hx, i13hw_mm0
    hx, i8hw_010mm hx, i8hw_01m0m hx]
  simp only [i8hpl_rho_001mm h0, i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_01mm h0,
    i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0,
    i8hpl_rho_mm1 h0]
  unfold i8L4S115k2 i8L4Q115k2_0 i8L4Q115k2_1 i8L4Q115k2_2 i8L4Q115k2_3 i8L4Q115k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽115k2⁾`. -/
noncomputable def i8L4R115k2 (x : ℝ) : ℝ :=
  x * (i8L4Q115k2_0 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x * i8L4Q115k2_1 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 2 * i8L4Q115k2_2 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 3 * i8L4Q115k2_3 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 4 * i8L4Q115k2_4 x (i13Rho [zero, zero, one, negOne, negOne] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x))

theorem tendsto_i8L4R115k2 : Tendsto i8L4R115k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q115k2_0 (v 0) (v 17) (v 18) (v 24) (v 40) (v 43) (v 57) (v 65)
      (v 66) (v 67) (v 69)) (by
      unfold i8L4Q115k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q115k2_1 (v 0) (v 17) (v 18) (v 24) (v 40) (v 43) (v 57) (v 65)
      (v 66) (v 67) (v 69)) (by
      unfold i8L4Q115k2_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q115k2_0 x (i13Rho [zero,
    zero, one, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
    [negOne, negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q115k2_1 x (i13Rho [zero, zero, one,
      negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R115k2
  unfold i8L4Q115k2_2 i8L4Q115k2_3 i8L4Q115k2_4
  ring

/-- The singular part of `Ψ₄⁽116k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S116k0 (x : ℝ) : ℝ :=
    -21 / 8 + Real.log x / 2 + Real.log x ^ 2 / 4

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽116k0⁾`. -/
noncomputable def i8L4Q116k0_0 (x r_0001m r_000m1 r_001 r_001m _r_00m1 r_01 r_01m r_0m r_0m1 r_1 r_m
    _r_m1 : ℝ) : ℝ :=
    1 / 4 - r_01m - 2 * r_001m - r_0m1 / 2 - x ^ 5 / 8 + x ^ 2 / 8 + x ^ 3 / 16 + 11 / 16 * x +
      r_1 * x ^ 3 + r_001 * x ^ 2 / 2 + r_0m * x ^ 2 / 2 + r_1 * x ^ 5 / 2 + r_m * x ^ 3 / 2 +
      r_m * x ^ 5 / 2 - r_01m * x ^ 4 - r_0m1 * x ^ 2 - r_m * x - 8 * r_0001m * x ^ 2 +
      2 * r_001m * x ^ 4 + 4 * r_000m1 * x ^ 2 - 5 / 4 * r_01 * x ^ 2 - 3 / 2 * r_1 * x -
      3 / 8 * r_1 * x ^ 4 - r_0m1 * x ^ 4 / 2 - r_m * x ^ 2 / 2 - r_1 * x ^ 6 / 4 +
      r_m * x ^ 4 / 4 + r_m * x ^ 6 / 4 + 5 / 8 * r_1 * x ^ 2 + r_1 * r_m * x ^ 7 / 2 -
      r_1 * r_m * x ^ 3 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽116k0⁾`. -/
noncomputable def i8L4Q116k0_1 (x _r_0001m _r_000m1 _r_001 _r_001m r_00m1 r_01 _r_01m _r_0m r_0m1
    r_1 _r_m r_m1 : ℝ) : ℝ :=
    -1 / 4 - r_0m1 - r_m1 / 2 - x / 8 + x ^ 3 / 8 + r_0m1 * x ^ 4 + r_m1 * x ^ 2 -
      4 * r_00m1 * x ^ 2 - r_01 * x ^ 2 / 2 - r_1 * x / 2 - r_1 * x ^ 3 / 2 - r_m1 * x ^ 4 / 2 +
      r_1 * x ^ 4 / 4 + 3 / 4 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽116k0⁾`. -/
noncomputable def i8L4Q116k0_2 (_x _r_0001m _r_000m1 _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_0m
    _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽116k0⁾`. -/
noncomputable def i8L4Q116k0_3 (_x _r_0001m _r_000m1 _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_0m
    _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽116k0⁾`. -/
noncomputable def i8L4Q116k0_4 (_x _r_0001m _r_000m1 _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_0m
    _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_116k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s116k0 x = i8L4S116k0 x + x * (i8L4Q116k0_0 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q116k0_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 2 * i8L4Q116k0_2 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q116k0_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 4 * i8L4Q116k0_4 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s116k0 i8Psi4s116k0N0 i8Psi4s116k0N1 i8Psi4s116k0N2 i8Psi4s116k0N3 i8Psi4s116k0N4
    i8Psi4s116k0W
  simp only [hpl_zero, i13hw_00, i13hw_00m10 hx, i13hw_010 hx, i13hw_0m10 hx, i13hw_10 hx, i13hw_1m
    hx, i13hw_m01 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_0001m h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0, i13hpl_rho_001m h0,
    i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0,
    i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S116k0 i8L4Q116k0_0 i8L4Q116k0_1 i8L4Q116k0_2 i8L4Q116k0_3 i8L4Q116k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽116k0⁾`. -/
noncomputable def i8L4R116k0 (x : ℝ) : ℝ :=
  x * (i8L4Q116k0_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q116k0_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x ^ 2 * i8L4Q116k0_2 x (i13Rho [zero, zero, zero, one, negOne] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q116k0_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x ^ 4 * i8L4Q116k0_4 x (i13Rho [zero, zero, zero, one, negOne] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R116k0 : Tendsto i8L4R116k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q116k0_0 (v 0) (v 5) (v 7) (v 9) (v 15) (v 21) (v 27) (v 36) (v
      43) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q116k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q116k0_1 (v 0) (v 5) (v 7) (v 9) (v 15) (v 21) (v 27) (v 36) (v
      43) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q116k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q116k0_0 x (i13Rho [zero,
    zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one]
    x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
    x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q116k0_1 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R116k0
  unfold i8L4Q116k0_2 i8L4Q116k0_3 i8L4Q116k0_4
  ring

/-- The singular part of `Ψ₄⁽116k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S116k1 (x : ℝ) : ℝ :=
    -35 / 8 - Real.log x / 2 + 3 / 4 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽116k1⁾`. -/
noncomputable def i8L4Q116k1_0 (x r_0001m r_000m r_0010m r_001m _r_00m _r_00m1 _r_01 r_01m r_0m
    _r_0m01 r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ :=
    -3 / 4 + r_01m + r_0m1 / 2 + 2 * r_001m - 7 / 8 * x ^ 2 - 5 / 8 * x ^ 3 - x ^ 4 / 8 +
      x ^ 5 / 16 + 19 / 8 * x + r_01m * x ^ 4 + r_1 * x ^ 3 + r_0m1 * x ^ 4 / 2 +
      r_m * x ^ 4 / 2 - r_000m * x ^ 2 - r_0m1 * x ^ 2 - 3 * r_m * x - 2 * r_001m * x ^ 4 -
      2 * r_01m * x ^ 2 - 2 * r_0m * x + 3 * r_m * x ^ 3 + 4 * r_0010m * x ^ 2 +
      12 * r_0001m * x ^ 2 - r_0m * x ^ 3 / 2 - r_0m * x ^ 5 / 2 - r_1 * x / 2 -
      r_1 * x ^ 5 / 2 - r_m * x ^ 2 / 2 - r_0m * x ^ 6 / 4 - r_1 * x ^ 4 / 4 + r_1 * x ^ 2 / 8 +
      r_1 * x ^ 6 / 8 + 9 / 4 * r_0m * x ^ 2 + r_0m * r_1 * x ^ 5 - r_0m * r_1 * x ^ 3 / 2 -
      r_0m * r_1 * x ^ 7 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽116k1⁾`. -/
noncomputable def i8L4Q116k1_1 (x _r_0001m _r_000m _r_0010m r_001m r_00m r_00m1 r_01 _r_01m r_0m
    r_0m01 r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    3 / 4 + r_0m1 + r_m1 / 2 + x ^ 2 / 2 + x ^ 4 / 4 + 5 / 8 * x ^ 3 + r_00m * x ^ 2 +
      r_01 * x ^ 4 + r_0m * x ^ 5 + r_1 * x ^ 3 + r_0m * x ^ 6 / 2 + r_1 * x ^ 2 / 2 +
      r_1 * x ^ 5 / 2 + r_m1 * x ^ 4 / 2 - r_0m1 * x ^ 4 - r_m1 * x ^ 2 - 4 * r_01 * x ^ 3 -
      3 * r_0m * x ^ 3 - 2 * r_0m * x - 2 * r_m * x + 4 * r_001m * x ^ 2 + 4 * r_0m01 * x ^ 2 +
      8 * r_00m1 * x ^ 2 - 11 / 4 * r_m * x ^ 2 - 3 / 2 * r_1 * x - r_0m * x ^ 4 / 2 -
      r_1 * x ^ 4 / 2 - r_m * x ^ 3 / 2 - r_m * x ^ 5 / 2 - r_m * x ^ 6 / 4 +
      r_0m * r_1 * x ^ 7 + r_1 * r_m * x ^ 5 - r_0m * r_1 * x ^ 3 - 4 * r_01 * r_0m * x ^ 5 -
      r_1 * r_m * x ^ 3 / 2 - r_1 * r_m * x ^ 7 / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽116k1⁾`. -/
noncomputable def i8L4Q116k1_2 (_x _r_0001m _r_000m _r_0010m _r_001m _r_00m _r_00m1 _r_01 _r_01m
    _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽116k1⁾`. -/
noncomputable def i8L4Q116k1_3 (_x _r_0001m _r_000m _r_0010m _r_001m _r_00m _r_00m1 _r_01 _r_01m
    _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽116k1⁾`. -/
noncomputable def i8L4Q116k1_4 (_x _r_0001m _r_000m _r_0010m _r_001m _r_00m _r_00m1 _r_01 _r_01m
    _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_116k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s116k1 x = i8L4S116k1 x + x * (i8L4Q116k1_0 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x) + Real.log x * i8L4Q116k1_1 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q116k1_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) + Real.log x ^ 3 * i8L4Q116k1_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho
      [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 4 * i8L4Q116k1_4 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s116k1 i8Psi4s116k1N0 i8Psi4s116k1N1 i8Psi4s116k1N2 i8Psi4s116k1N3 i8Psi4s116k1N4
    i8Psi4s116k1W
  simp only [hpl_zero, i13hw_00, i13hw_001m0 hx, i13hw_00m0 hx, i13hw_010m hx, i13hw_010m0 hx,
    i13hw_01m0 hx, i13hw_0m0 hx, i13hw_100m hx, i13hw_10m hx, i13hw_10m0 hx, i13hw_1m0 hx, i13hw_m0
    hx, i8hw_0100m hx]
  simp only [i13hpl_rho_0001m h0, i13hpl_rho_000m h0, i13hpl_rho_0010m h0, i13hpl_rho_001m h0,
    i13hpl_rho_00m h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S116k1 i8L4Q116k1_0 i8L4Q116k1_1 i8L4Q116k1_2 i8L4Q116k1_3 i8L4Q116k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽116k1⁾`. -/
noncomputable def i8L4R116k1 (x : ℝ) : ℝ :=
  x * (i8L4Q116k1_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q116k1_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q116k1_2 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q116k1_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q116k1_4 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R116k1 : Tendsto i8L4R116k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q116k1_0 (v 0) (v 5) (v 6) (v 11) (v 15) (v 18) (v 21) (v 27) (v
      36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q116k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q116k1_1 (v 0) (v 5) (v 6) (v 11) (v 15) (v 18) (v 21) (v 27) (v
      36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q116k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q116k1_0 x (i13Rho [zero,
    zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one,
    zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q116k1_1 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, zero, negOne]
      x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R116k1
  unfold i8L4Q116k1_2 i8L4Q116k1_3 i8L4Q116k1_4
  ring

/-- The singular part of `Ψ₄⁽117⁾` at `ξ = 0`. -/
noncomputable def i8L4S117 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽117⁾`. -/
noncomputable def i8L4Q117_0 (x r_01 r_011 r_1 : ℝ) : ℝ :=
    -4 - x ^ 2 - x ^ 4 - x ^ 3 / 2 - x ^ 5 / 2 - 8 * r_01 * x ^ 2 - 6 * r_1 ^ 2 * x ^ 5 -
      4 * r_1 * x ^ 3 - 2 * r_1 * x ^ 6 - 2 * r_1 ^ 2 * x ^ 7 + 4 * r_1 ^ 2 * x ^ 4 +
      4 * r_1 ^ 2 * x ^ 6 + 6 * r_1 * x ^ 2 + 8 * r_011 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽117⁾`. -/
noncomputable def i8L4Q117_1 (_x _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽117⁾`. -/
noncomputable def i8L4Q117_2 (_x _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽117⁾`. -/
noncomputable def i8L4Q117_3 (_x _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽117⁾`. -/
noncomputable def i8L4Q117_4 (_x _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_117_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s117 x = i8L4S117 x + x * (i8L4Q117_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x * i8L4Q117_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, one]
      x) (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q117_2 x (i13Rho [zero, one] x) (i13Rho [zero, one,
      one] x) (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q117_3 x (i13Rho [zero, one] x) (i13Rho [zero,
      one, one] x) (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q117_4 x (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s117 i8Psi4s117N0 i8Psi4s117N1 i8Psi4s117N2 i8Psi4s117N3 i8Psi4s117N4 i8Psi4s117W
  simp only [i13hw_11 hx]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S117 i8L4Q117_0 i8L4Q117_1 i8L4Q117_2 i8L4Q117_3 i8L4Q117_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽117⁾`. -/
noncomputable def i8L4R117 (x : ℝ) : ℝ :=
  x * (i8L4Q117_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q117_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q117_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one]
    x) + Real.log x ^ 3 * i8L4Q117_3 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
    [one] x) + Real.log x ^ 4 * i8L4Q117_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [one] x))

theorem tendsto_i8L4R117 : Tendsto i8L4R117 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q117_0 (v 0) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q117_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q117_0 x (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R117
  unfold i8L4Q117_1 i8L4Q117_2 i8L4Q117_3 i8L4Q117_4
  ring

/-- The singular part of `Ψ₄⁽118⁾` at `ξ = 0`. -/
noncomputable def i8L4S118 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽118⁾`. -/
noncomputable def i8L4Q118_0 (x r_01 r_011 r_011m r_01m r_01m1 r_0m r_0m1 r_0m11 r_1 r_m : ℝ) : ℝ :=
    2 + x / 2 + 2 * x ^ 2 - x ^ 6 / 4 - x ^ 7 / 8 + x ^ 4 / 4 + x ^ 5 / 8 + 5 / 4 * x ^ 3 +
      r_1 * x ^ 6 + r_m * x ^ 7 + r_1 ^ 2 * x ^ 5 + r_1 ^ 2 * x ^ 6 + r_1 ^ 2 * x ^ 8 -
      8 * r_011m * x ^ 2 - 8 * r_01m1 * x ^ 2 - 8 * r_0m11 * x ^ 2 - 5 * r_1 * x ^ 2 -
      2 * r_011 * x ^ 2 - 2 * r_1 ^ 2 * x ^ 4 + 2 * r_01m * x ^ 2 + 2 * r_0m * x ^ 2 +
      2 * r_0m1 * x ^ 2 + 2 * r_m * x ^ 5 + 4 * r_01 * x ^ 2 - r_1 * x ^ 8 / 2 -
      r_m * x ^ 2 / 2 - r_1 ^ 2 * x ^ 7 / 2 - r_1 ^ 2 * x ^ 9 / 2 + r_m * x ^ 8 / 4 +
      3 / 2 * r_m * x ^ 6 + 7 / 4 * r_m * x ^ 4 + 9 / 2 * r_1 * x ^ 4 + r_1 * r_m * x ^ 7 +
      r_1 * r_m * x ^ 9 + r_m * r_1 ^ 2 * x ^ 10 - r_m * r_1 ^ 2 * x ^ 6 - 4 * r_1 * r_m * x ^ 4 -
      2 * r_1 * r_m * x ^ 5 + 2 * r_1 * r_m * x ^ 6 + 2 * r_1 * r_m * x ^ 8

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽118⁾`. -/
noncomputable def i8L4Q118_1 (_x _r_01 _r_011 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11 _r_1 _r_m
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽118⁾`. -/
noncomputable def i8L4Q118_2 (_x _r_01 _r_011 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11 _r_1 _r_m
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽118⁾`. -/
noncomputable def i8L4Q118_3 (_x _r_01 _r_011 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11 _r_1 _r_m
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽118⁾`. -/
noncomputable def i8L4Q118_4 (_x _r_01 _r_011 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11 _r_1 _r_m
    : ℝ) : ℝ :=
    0

theorem i8L4_118_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s118 x = i8L4S118 x + x * (i8L4Q118_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
      one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q118_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q118_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q118_3 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q118_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s118 i8Psi4s118N0 i8Psi4s118N1 i8Psi4s118N2 i8Psi4s118N3 i8Psi4s118N4 i8Psi4s118W
  simp only [i13hw_11 hx, i13hw_11m hx, i13hw_1m hx, i13hw_1m1 hx]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_011m h0, i13hpl_rho_01m h0,
    i13hpl_rho_01m1 h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_0m11 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0]
  unfold i8L4S118 i8L4Q118_0 i8L4Q118_1 i8L4Q118_2 i8L4Q118_3 i8L4Q118_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽118⁾`. -/
noncomputable def i8L4R118 (x : ℝ) : ℝ :=
  x * (i8L4Q118_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) + Real.log x * i8L4Q118_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, one]
    x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q118_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
    one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q118_3 x (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q118_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
    one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R118 : Tendsto i8L4R118 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q118_0 (v 0) (v 27) (v 29) (v 33) (v 36) (v 37) (v 43) (v 49) (v
      51) (v 65) (v 66)) (by
      unfold i8L4Q118_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q118_0 x (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R118
  unfold i8L4Q118_1 i8L4Q118_2 i8L4Q118_3 i8L4Q118_4
  ring

/-- The singular part of `Ψ₄⁽119k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S119k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽119k0⁾`. -/
noncomputable def i8L4Q119k0_0 (x r_011 r_011m r_01m r_01m1 r_01mm1 r_0m1 r_0m11 r_0m11m r_0m1m1
    r_0mm1 r_0mm11 r_1 r_m r_m1 r_m11 r_mm1 r_mm11 : ℝ) : ℝ :=
    -4 * r_mm11 - 7 / 8 * x ^ 3 - 5 / 2 * x - x ^ 7 / 8 + 3 / 4 * x ^ 4 + 5 / 2 * x ^ 2 +
      5 / 4 * x ^ 5 + r_1 * x ^ 7 + r_m1 * x ^ 4 + r_1 ^ 2 * x ^ 6 + r_m * x ^ 7 / 2 -
      r_1 * x ^ 5 - 8 * r_0m1 * x ^ 2 - 5 * r_m1 * x ^ 2 - 4 * r_011 * x ^ 2 - 4 * r_01m * x ^ 2 -
      4 * r_0mm1 * x ^ 2 - 4 * r_m11 * x ^ 5 - 4 * r_mm1 * x ^ 3 - 4 * r_mm1 * x ^ 5 -
      2 * r_m11 * x ^ 2 - 2 * r_mm1 * x ^ 4 - 2 * r_mm1 * x ^ 6 - 2 * r_1 ^ 2 * x ^ 7 -
      2 * r_m1 ^ 2 * x ^ 3 + 2 * r_m * x ^ 3 + 2 * r_m1 * x ^ 3 + 2 * r_m1 * x ^ 6 +
      2 * r_m11 * x ^ 6 + 2 * r_1 ^ 2 * x ^ 8 + 2 * r_m1 ^ 2 * x ^ 7 + 4 * r_011m * x ^ 2 +
      4 * r_01m1 * x ^ 2 + 4 * r_0m11 * x ^ 2 + 4 * r_m11 * x + 4 * r_mm1 * x ^ 2 +
      4 * r_mm11 * x ^ 4 + 7 * r_1 * x ^ 3 + 8 * r_mm1 * x + 16 * r_01mm1 * x ^ 2 +
      16 * r_0m11m * x ^ 2 + 16 * r_0m1m1 * x ^ 2 + 16 * r_0mm11 * x ^ 2 - 11 / 2 * r_1 * x ^ 2 -
      5 / 2 * r_1 * x ^ 4 - 5 / 2 * r_m * x ^ 5 - 3 / 2 * r_m * x ^ 2 - 3 / 4 * r_m * x ^ 6 -
      r_1 * x ^ 8 / 2 - r_1 ^ 2 * x ^ 5 / 2 - r_1 ^ 2 * x ^ 9 / 2 + r_m * x ^ 8 / 4 +
      3 / 2 * r_1 * x ^ 6 + r_1 * r_m * x ^ 9 + r_m * r_1 ^ 2 * x ^ 10 - r_m * r_1 ^ 2 * x ^ 8 -
      4 * r_1 * r_m * x ^ 7 - 4 * r_1 * r_mm1 * x ^ 7 - 4 * r_m * r_m11 * x ^ 7 -
      2 * r_1 * r_m * x ^ 6 - 2 * r_m * r_1 ^ 2 * x ^ 9 + 2 * r_m * r_1 ^ 2 * x ^ 7 +
      4 * r_1 * r_mm1 * x ^ 3 + 4 * r_m * r_m11 * x ^ 3 + 5 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽119k0⁾`. -/
noncomputable def i8L4Q119k0_1 (_x _r_011 _r_011m _r_01m _r_01m1 _r_01mm1 _r_0m1 _r_0m11 _r_0m11m
    _r_0m1m1 _r_0mm1 _r_0mm11 _r_1 _r_m _r_m1 _r_m11 _r_mm1 _r_mm11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽119k0⁾`. -/
noncomputable def i8L4Q119k0_2 (_x _r_011 _r_011m _r_01m _r_01m1 _r_01mm1 _r_0m1 _r_0m11 _r_0m11m
    _r_0m1m1 _r_0mm1 _r_0mm11 _r_1 _r_m _r_m1 _r_m11 _r_mm1 _r_mm11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽119k0⁾`. -/
noncomputable def i8L4Q119k0_3 (_x _r_011 _r_011m _r_01m _r_01m1 _r_01mm1 _r_0m1 _r_0m11 _r_0m11m
    _r_0m1m1 _r_0mm1 _r_0mm11 _r_1 _r_m _r_m1 _r_m11 _r_mm1 _r_mm11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽119k0⁾`. -/
noncomputable def i8L4Q119k0_4 (_x _r_011 _r_011m _r_01m _r_01m1 _r_01mm1 _r_0m1 _r_0m11 _r_0m11m
    _r_0m1m1 _r_0mm1 _r_0mm11 _r_1 _r_m _r_m1 _r_m11 _r_mm1 _r_mm11 : ℝ) : ℝ :=
    0

theorem i8L4_119k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s119k0 x = i8L4S119k0 x + x * (i8L4Q119k0_0 x (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, one, negOne, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, one, negOne] x) (i13Rho [zero, negOne, one,
      negOne, one] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one,
      one] x) (i13Rho [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
      Real.log x * i8L4Q119k0_1 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne,
      negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [zero, negOne, one, one, negOne] x) (i13Rho [zero, negOne, one, negOne, one] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne, negOne,
      one] x) (i13Rho [negOne, negOne, one, one] x) +
      Real.log x ^ 2 * i8L4Q119k0_2 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one,
      negOne, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [zero, negOne, one, one, negOne] x) (i13Rho [zero, negOne, one, negOne, one] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho
      [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
      Real.log x ^ 3 * i8L4Q119k0_3 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one,
      negOne, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [zero, negOne, one, one, negOne] x) (i13Rho [zero, negOne, one, negOne, one] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho
      [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
      Real.log x ^ 4 * i8L4Q119k0_4 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one,
      negOne, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [zero, negOne, one, one, negOne] x) (i13Rho [zero, negOne, one, negOne, one] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho
      [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s119k0 i8Psi4s119k0N0 i8Psi4s119k0N1 i8Psi4s119k0N2 i8Psi4s119k0N3 i8Psi4s119k0N4
    i8Psi4s119k0W
  simp only [i13hw_11 hx, i13hw_11m hx, i13hw_1m hx, i13hw_1m1 hx, i8hw_1mm1 hx, i8hw_m11m
    hx, i8hw_m1m1 hx]
  simp only [i13hpl_rho_011 h0, i13hpl_rho_011m h0, i13hpl_rho_01m h0, i13hpl_rho_01m1 h0,
    i8hpl_rho_01mm1 h0, i13hpl_rho_0m1 h0, i13hpl_rho_0m11 h0, i8hpl_rho_0m11m h0, i8hpl_rho_0m1m1
    h0, i13hpl_rho_0mm1 h0, i8hpl_rho_0mm11 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0,
    i8hpl_rho_m11 h0, i8hpl_rho_mm1 h0, i8hpl_rho_mm11 h0]
  unfold i8L4S119k0 i8L4Q119k0_0 i8L4Q119k0_1 i8L4Q119k0_2 i8L4Q119k0_3 i8L4Q119k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽119k0⁾`. -/
noncomputable def i8L4R119k0 (x : ℝ) : ℝ :=
  x * (i8L4Q119k0_0 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [zero, negOne, one,
    one, negOne] x) (i13Rho [zero, negOne, one, negOne, one] x) (i13Rho [zero, negOne, negOne, one]
    x) (i13Rho [zero, negOne, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne, negOne, one] x) (i13Rho [negOne,
    negOne, one, one] x) + Real.log x * i8L4Q119k0_1 x (i13Rho [zero, one, one] x) (i13Rho [zero,
    one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
    [zero, one, negOne, negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one,
    one] x) (i13Rho [zero, negOne, one, one, negOne] x) (i13Rho [zero, negOne, one, negOne, one] x)
    (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, one] x) (i13Rho [one]
    x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne,
    negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
    Real.log x ^ 2 * i8L4Q119k0_2 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne,
    negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [zero, negOne, one, one, negOne] x) (i13Rho [zero, negOne, one, negOne, one] x) (i13Rho [zero,
    negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne, negOne, one]
    x) (i13Rho [negOne, negOne, one, one] x) +
    Real.log x ^ 3 * i8L4Q119k0_3 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne,
    negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [zero, negOne, one, one, negOne] x) (i13Rho [zero, negOne, one, negOne, one] x) (i13Rho [zero,
    negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne, negOne, one]
    x) (i13Rho [negOne, negOne, one, one] x) +
    Real.log x ^ 4 * i8L4Q119k0_4 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne,
    negOne, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [zero, negOne, one, one, negOne] x) (i13Rho [zero, negOne, one, negOne, one] x) (i13Rho [zero,
    negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne, negOne, one]
    x) (i13Rho [negOne, negOne, one, one] x))

theorem tendsto_i8L4R119k0 : Tendsto i8L4R119k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q119k0_0 (v 0) (v 29) (v 33) (v 36) (v 37) (v 41) (v 49) (v 51)
      (v 53) (v 55) (v 59) (v 60) (v 65) (v 66) (v 67) (v 68) (v 69) (v 70)) (by
      unfold i8L4Q119k0_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q119k0_0 x (i13Rho [zero, one,
    one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, one, negOne, negOne, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, one, negOne] x) (i13Rho [zero,
    negOne, one, negOne, one] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne,
    negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
    [negOne, one, one] x) (i13Rho [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R119k0
  unfold i8L4Q119k0_1 i8L4Q119k0_2 i8L4Q119k0_3 i8L4Q119k0_4
  ring

/-- The singular part of `Ψ₄⁽119k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S119k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽119k1⁾`. -/
noncomputable def i8L4Q119k1_0 (x r_011mm r_01m r_01m1m r_01mm r_0m1m r_0mm r_1 r_m r_m1 r_m11 r_mm1
    r_mm11 : ℝ) : ℝ :=
    4 * r_mm11 - 11 / 16 * x ^ 5 - 7 / 8 * x ^ 3 - 5 / 2 * x ^ 2 - 3 / 4 * x ^ 4 - x ^ 9 / 16 +
      3 / 2 * x + 3 / 8 * x ^ 7 + r_1 * x ^ 3 + r_1 * x ^ 6 + r_m * x ^ 4 + r_1 ^ 2 * x ^ 5 +
      r_1 ^ 2 * x ^ 10 + r_1 * x ^ 9 / 2 + r_m * x ^ 9 / 2 + r_m ^ 2 * x ^ 5 / 2 -
      r_m * x ^ 7 - r_m1 * x ^ 4 - r_1 ^ 2 * x ^ 6 - r_1 ^ 2 * x ^ 9 - r_m ^ 2 * x ^ 10 -
      8 * r_mm1 * x - 4 * r_01m * x ^ 2 - 4 * r_01mm * x ^ 2 - 4 * r_0m1m * x ^ 2 -
      4 * r_0mm * x ^ 2 - 4 * r_m11 * x - 4 * r_mm1 * x ^ 2 - 4 * r_mm11 * x ^ 4 -
      3 * r_1 * x ^ 5 - 2 * r_m1 * x ^ 3 - 2 * r_m1 * x ^ 6 - 2 * r_m11 * x ^ 6 -
      2 * r_m ^ 2 * x ^ 8 - 2 * r_m1 ^ 2 * x ^ 7 + 2 * r_m11 * x ^ 2 + 2 * r_mm1 * x ^ 4 +
      2 * r_mm1 * x ^ 6 + 2 * r_m1 ^ 2 * x ^ 3 + 4 * r_m11 * x ^ 5 + 4 * r_mm1 * x ^ 3 +
      4 * r_mm1 * x ^ 5 + 5 * r_m1 * x ^ 2 + 6 * r_m * x ^ 3 + 7 * r_m * x ^ 2 +
      16 * r_011mm * x ^ 2 + 16 * r_01m1m * x ^ 2 - 7 / 4 * r_m * x ^ 6 -
      7 / 4 * r_m ^ 2 * x ^ 7 - 3 / 2 * r_1 * x ^ 7 - 3 / 2 * r_m * x ^ 5 -
      3 / 2 * r_m ^ 2 * x ^ 9 - r_m * x ^ 8 / 2 - r_1 * x ^ 10 / 4 - r_1 ^ 2 * x ^ 11 / 4 -
      r_m ^ 2 * x ^ 11 / 4 + r_m * x ^ 10 / 4 + r_1 ^ 2 * x ^ 7 / 4 + 3 / 2 * r_1 * x ^ 4 +
      3 / 4 * r_1 * x ^ 8 + r_1 * r_m * x ^ 11 + r_m * r_1 ^ 2 * x ^ 12 +
      r_1 ^ 2 * r_m ^ 2 * x ^ 9 - r_1 * r_m ^ 2 * x ^ 10 - r_1 * r_m ^ 2 * x ^ 12 -
      r_m * r_1 ^ 2 * x ^ 8 - r_1 ^ 2 * r_m ^ 2 * x ^ 13 - 5 * r_1 * r_m * x ^ 7 -
      4 * r_1 * r_mm1 * x ^ 3 - 4 * r_m * r_m11 * x ^ 3 - 3 * r_1 * r_m * x ^ 9 -
      2 * r_1 * r_m ^ 2 * x ^ 9 - 2 * r_1 * r_m ^ 2 * x ^ 11 - 2 * r_m * r_1 ^ 2 * x ^ 11 +
      2 * r_1 * r_m * x ^ 6 + 2 * r_1 * r_m ^ 2 * x ^ 8 + 2 * r_m * r_1 ^ 2 * x ^ 7 +
      4 * r_1 * r_mm1 * x ^ 7 + 4 * r_1 * r_m ^ 2 * x ^ 7 + 4 * r_m * r_m11 * x ^ 7 +
      5 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽119k1⁾`. -/
noncomputable def i8L4Q119k1_1 (_x _r_011mm _r_01m _r_01m1m _r_01mm _r_0m1m _r_0mm _r_1 _r_m _r_m1
    _r_m11 _r_mm1 _r_mm11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽119k1⁾`. -/
noncomputable def i8L4Q119k1_2 (_x _r_011mm _r_01m _r_01m1m _r_01mm _r_0m1m _r_0mm _r_1 _r_m _r_m1
    _r_m11 _r_mm1 _r_mm11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽119k1⁾`. -/
noncomputable def i8L4Q119k1_3 (_x _r_011mm _r_01m _r_01m1m _r_01mm _r_0m1m _r_0mm _r_1 _r_m _r_m1
    _r_m11 _r_mm1 _r_mm11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽119k1⁾`. -/
noncomputable def i8L4Q119k1_4 (_x _r_011mm _r_01m _r_01m1m _r_01mm _r_0m1m _r_0mm _r_1 _r_m _r_m1
    _r_m11 _r_mm1 _r_mm11 : ℝ) : ℝ :=
    0

theorem i8L4_119k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s119k1 x = i8L4S119k1 x + x * (i8L4Q119k1_0 x (i13Rho [zero, one, one, negOne, negOne] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one,
      negOne, negOne] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x)
      (i13Rho [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
      Real.log x * i8L4Q119k1_1 x (i13Rho [zero, one, one, negOne, negOne] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne,
      negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
      Real.log x ^ 2 * i8L4Q119k1_2 x (i13Rho [zero, one, one, negOne, negOne] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one, negOne,
      negOne] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho
      [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
      Real.log x ^ 3 * i8L4Q119k1_3 x (i13Rho [zero, one, one, negOne, negOne] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one, negOne,
      negOne] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho
      [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
      Real.log x ^ 4 * i8L4Q119k1_4 x (i13Rho [zero, one, one, negOne, negOne] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one, negOne,
      negOne] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho
      [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s119k1 i8Psi4s119k1N0 i8Psi4s119k1N1 i8Psi4s119k1N2 i8Psi4s119k1N3 i8Psi4s119k1N4
    i8Psi4s119k1W
  simp only [i13hw_1m hx, i13hw_1mm hx, i13hw_mm hx, i8hw_11mm hx, i8hw_1m1m hx, i8hw_m1m
    hx]
  simp only [i8hpl_rho_011mm h0, i13hpl_rho_01m h0, i8hpl_rho_01m1m h0, i13hpl_rho_01mm h0,
    i13hpl_rho_0m1m h0, i13hpl_rho_0mm h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0,
    i8hpl_rho_m11 h0, i8hpl_rho_mm1 h0, i8hpl_rho_mm11 h0]
  unfold i8L4S119k1 i8L4Q119k1_0 i8L4Q119k1_1 i8L4Q119k1_2 i8L4Q119k1_3 i8L4Q119k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽119k1⁾`. -/
noncomputable def i8L4R119k1 (x : ℝ) : ℝ :=
  x * (i8L4Q119k1_0 x (i13Rho [zero, one, one, negOne, negOne] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
    [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne, negOne, one]
    x) (i13Rho [negOne, negOne, one, one] x) +
    Real.log x * i8L4Q119k1_1 x (i13Rho [zero, one, one, negOne, negOne] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne,
    negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
    Real.log x ^ 2 * i8L4Q119k1_2 x (i13Rho [zero, one, one, negOne, negOne] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne,
    negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
    Real.log x ^ 3 * i8L4Q119k1_3 x (i13Rho [zero, one, one, negOne, negOne] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne,
    negOne, one] x) (i13Rho [negOne, negOne, one, one] x) +
    Real.log x ^ 4 * i8L4Q119k1_4 x (i13Rho [zero, one, one, negOne, negOne] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, one, negOne, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
    (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) (i13Rho [negOne,
    negOne, one] x) (i13Rho [negOne, negOne, one, one] x))

theorem tendsto_i8L4R119k1 : Tendsto i8L4R119k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q119k1_0 (v 0) (v 35) (v 36) (v 39) (v 40) (v 54) (v 57) (v 65)
      (v 66) (v 67) (v 68) (v 69) (v 70)) (by
      unfold i8L4Q119k1_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q119k1_0 x (i13Rho [zero, one,
    one, negOne, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one, negOne]
    x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
    [negOne, one, one] x) (i13Rho [negOne, negOne, one] x) (i13Rho [negOne, negOne, one, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R119k1
  unfold i8L4Q119k1_1 i8L4Q119k1_2 i8L4Q119k1_3 i8L4Q119k1_4
  ring

/-- The singular part of `Ψ₄⁽120k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S120k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽120k0⁾`. -/
noncomputable def i8L4Q120k0_0 (x r_0011m r_001m1 r_00m1 r_00m11 r_01 r_011 r_011m r_01m r_0m
    r_0m011 r_0m1 r_0m101 r_0m11 r_1 r_m r_m1 : ℝ) : ℝ :=
    1 - 2 * r_011m + 2 * r_0m11 - 5 / 8 * x ^ 3 - x / 4 + x ^ 4 / 8 + x ^ 6 / 8 + x ^ 5 / 16 +
      x ^ 7 / 16 + r_01m * x ^ 2 + r_0m * x ^ 2 + r_0m1 * x ^ 6 + r_1 ^ 2 * x ^ 5 +
      r_1 * x ^ 4 / 2 + r_1 ^ 2 * x ^ 6 / 2 - r_011 * x ^ 2 - r_0m1 * x ^ 4 - r_1 ^ 2 * x ^ 4 -
      8 * r_0011m * x ^ 2 - 6 * r_0m1 * x ^ 3 - 4 * r_0m1 * x - 2 * r_01 * x ^ 4 -
      2 * r_0m11 * x ^ 4 - 2 * r_m1 * x - 2 * r_m1 * x ^ 3 + 2 * r_00m1 * x ^ 2 +
      2 * r_011m * x ^ 4 + 2 * r_0m1 * x ^ 5 + 4 * r_01 * x ^ 2 + 8 * r_001m1 * x ^ 2 +
      8 * r_0m101 * x ^ 2 + 16 * r_0m011 * x ^ 2 + 24 * r_00m11 * x ^ 2 - 23 / 4 * r_1 * x ^ 2 -
      15 / 2 * r_m1 * x ^ 2 - 11 / 4 * r_m * x ^ 2 - r_1 * x ^ 6 / 2 - r_m * x ^ 6 / 2 -
      r_m * x ^ 7 / 2 - r_m1 * x ^ 4 / 2 - r_1 ^ 2 * x ^ 8 / 2 - r_1 ^ 2 * x ^ 7 / 4 -
      r_m * x ^ 8 / 8 + r_1 * x ^ 8 / 4 + r_1 ^ 2 * x ^ 9 / 4 + 7 / 8 * r_m * x ^ 4 +
      11 / 2 * r_1 * x ^ 3 + r_1 * r_m * x ^ 6 + r_m * r_1 ^ 2 * x ^ 8 + r_1 * r_m * x ^ 7 / 2 -
      r_1 * r_m * x ^ 8 - 8 * r_01 * r_0m1 * x ^ 5 - 2 * r_0m1 * r_1 * x ^ 3 -
      2 * r_1 * r_m * x ^ 4 + 2 * r_0m1 * r_1 * x ^ 7 + 2 * r_1 * r_m * x ^ 5 -
      r_1 * r_m * x ^ 9 / 2 - r_m * r_1 ^ 2 * x ^ 6 / 2 - r_m * r_1 ^ 2 * x ^ 10 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽120k0⁾`. -/
noncomputable def i8L4Q120k0_1 (_x _r_0011m _r_001m1 _r_00m1 _r_00m11 _r_01 _r_011 _r_011m _r_01m
    _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽120k0⁾`. -/
noncomputable def i8L4Q120k0_2 (_x _r_0011m _r_001m1 _r_00m1 _r_00m11 _r_01 _r_011 _r_011m _r_01m
    _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽120k0⁾`. -/
noncomputable def i8L4Q120k0_3 (_x _r_0011m _r_001m1 _r_00m1 _r_00m11 _r_01 _r_011 _r_011m _r_01m
    _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽120k0⁾`. -/
noncomputable def i8L4Q120k0_4 (_x _r_0011m _r_001m1 _r_00m1 _r_00m11 _r_01 _r_011 _r_011m _r_01m
    _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_120k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s120k0 x = i8L4S120k0 x + x * (i8L4Q120k0_0 x (i13Rho [zero, zero, one, one, negOne] x)
      (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x * i8L4Q120k0_1 x (i13Rho [zero, zero, one, one, negOne] x)
      (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 2 * i8L4Q120k0_2 x (i13Rho [zero, zero, one, one, negOne] x)
      (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 3 * i8L4Q120k0_3 x (i13Rho [zero, zero, one, one, negOne] x)
      (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 4 * i8L4Q120k0_4 x (i13Rho [zero, zero, one, one, negOne] x)
      (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s120k0 i8Psi4s120k0N0 i8Psi4s120k0N1 i8Psi4s120k0N2 i8Psi4s120k0N3 i8Psi4s120k0N4
    i8Psi4s120k0W
  simp only [i13hw_10m1 hx, i13hw_11 hx, i13hw_11m hx, i13hw_1m hx, i13hw_1m1 hx,
    i8hw_010m1 hx]
  simp only [i8hpl_rho_0011m h0, i8hpl_rho_001m1 h0, i13hpl_rho_00m1 h0, i8hpl_rho_00m11 h0,
    i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_011m h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m011 h0, i13hpl_rho_0m1 h0, i8hpl_rho_0m101 h0, i13hpl_rho_0m11 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S120k0 i8L4Q120k0_0 i8L4Q120k0_1 i8L4Q120k0_2 i8L4Q120k0_3 i8L4Q120k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽120k0⁾`. -/
noncomputable def i8L4R120k0 (x : ℝ) : ℝ :=
  x * (i8L4Q120k0_0 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, one, negOne,
    one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q120k0_1 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, one,
    negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne,
    one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q120k0_2 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
    one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one]
    x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero,
    negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q120k0_3 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
    one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one]
    x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero,
    negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q120k0_4 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
    one, negOne, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one]
    x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero,
    negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R120k0 : Tendsto i8L4R120k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q120k0_0 (v 0) (v 14) (v 16) (v 21) (v 22) (v 27) (v 29) (v 33)
      (v 36) (v 43) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q120k0_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q120k0_0 x (i13Rho [zero, zero,
    one, one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne, one]
    x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R120k0
  unfold i8L4Q120k0_1 i8L4Q120k0_2 i8L4Q120k0_3 i8L4Q120k0_4
  ring

/-- The regular parts of group 11. -/
noncomputable def i8L4RG11 (x : ℝ) : ℝ :=
  i8L4R115k1 x + i8L4R115k2 x + i8L4R116k0 x + i8L4R116k1 x + i8L4R117 x + i8L4R118 x +
    i8L4R119k0 x + i8L4R119k1 x + i8L4R120k0 x

theorem tendsto_i8L4RG11 : Tendsto i8L4RG11 (𝓝[>] 0) (𝓝 0) := by
  have H := ((((((((tendsto_i8L4R115k1.add tendsto_i8L4R115k2).add tendsto_i8L4R116k0).add
    tendsto_i8L4R116k1).add tendsto_i8L4R117).add tendsto_i8L4R118).add tendsto_i8L4R119k0).add
    tendsto_i8L4R119k1).add tendsto_i8L4R120k0)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
