/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L5
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 6

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_77_eq`, `QED.ThreeLoopD.tendsto_i8L4RG6` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽77⁾` at `ξ = 0`. -/
noncomputable def i8L4S77 (x : ℝ) : ℝ :=
    (-22 - Real.log x ^ 3 - 22 * Real.log x - 7 * Real.log x ^ 2 - 405 / 16 * x +
      π ^ 2 / 3 + Real.log x * π ^ 2 / 3 + 2 / 3 * x * Real.log x ^ 3 +
      3 / 8 * x * Real.log x ^ 4 + 5 / 8 * π ^ 2 * x - π ^ 2 * x * Real.log x ^ 2 / 4) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽77⁾`. -/
noncomputable def i8L4Q77_0 (x r_000m r_00m r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    1 / 8 - 43 / 16 * x ^ 3 - 27 / 8 * r_m - π ^ 2 / 4 + x ^ 4 / 4 + x ^ 5 / 8 + 57 / 8 * x +
      115 / 8 * x ^ 2 + r_00m * x ^ 2 - r_m * x ^ 5 - 47 * r_m * x ^ 2 - 24 * r_m * x -
      21 * r_m * x ^ 3 - 12 * r_000m * x ^ 2 - 4 * r_0m * x - 3 * r_0m * x ^ 5 +
      3 * r_0m * x ^ 3 + 4 * r_0m * x ^ 4 + 6 * r_0m ^ 2 * x ^ 5 + 24 * r_00mm * x ^ 2 -
      45 / 2 * r_0m * x ^ 2 - r_0m * x ^ 6 / 2 - π ^ 2 * x / 3 - r_m * x ^ 6 / 4 +
      π ^ 2 * x ^ 2 / 4 + π ^ 2 * r_m / 12 + π ^ 2 * x ^ 3 / 24 + 37 / 8 * r_m * x ^ 4 +
      r_0m * r_m * x ^ 7 - π ^ 2 * r_0m * x ^ 2 - r_0m * r_m * x ^ 3 - 8 * r_0m * r_m * x ^ 4 +
      8 * r_0m * r_m * x ^ 6 - 2 / 3 * π ^ 2 * r_m * x ^ 3 - π ^ 2 * r_m * x ^ 4 / 12 +
      2 / 3 * π ^ 2 * r_m * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽77⁾`. -/
noncomputable def i8L4Q77_1 (x _r_000m r_00m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    13 / 4 - 67 / 4 * x ^ 2 - 27 / 4 * r_m - x ^ 4 / 2 - x ^ 5 / 2 + π ^ 2 / 6 + 43 / 8 * x ^ 3 +
      51 / 8 * x + r_0m * x ^ 6 + r_m ^ 2 * x ^ 3 - r_0m * x ^ 2 - r_0m * x ^ 4 -
      r_m ^ 2 * x ^ 7 - 24 * r_0mm * x ^ 2 - 20 * r_m * x - 8 * r_m ^ 2 * x ^ 6 - 4 * r_0m * x -
      2 * r_0m * x ^ 3 + 2 * r_0m * x ^ 5 + 6 * r_m * x ^ 5 + 8 * r_m ^ 2 * x ^ 4 +
      12 * r_00m * x ^ 2 + 18 * r_m * x ^ 3 - 53 / 4 * r_m * x ^ 4 - π ^ 2 * x ^ 2 / 6 -
      π ^ 2 * x ^ 3 / 12 + π ^ 2 * r_m / 6 + π ^ 2 * x / 12 + 3 / 2 * r_m * x ^ 6 +
      45 / 2 * r_m * x ^ 2 + π ^ 2 * r_m * x ^ 2 - 12 * r_0m * r_m * x ^ 5 -
      8 * r_0m * r_m * x ^ 4 - 8 * r_0m * r_m * x ^ 6 - 2 * r_0m * r_m * x ^ 3 -
      2 * r_0m * r_m * x ^ 7 + π ^ 2 * r_m * x ^ 4 / 6 + 2 / 3 * π ^ 2 * r_m * x +
      2 / 3 * π ^ 2 * r_m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽77⁾`. -/
noncomputable def i8L4Q77_2 (x _r_000m _r_00m _r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    -15 / 4 + x ^ 5 / 2 - 11 / 4 * r_m - 11 / 8 * x ^ 3 + 3 / 2 * x + 7 / 4 * x ^ 2 -
      6 * r_m * x - 4 * r_m * x ^ 2 - 4 * r_m * x ^ 5 - 3 * r_0m * x ^ 2 - 2 * r_m * x ^ 6 +
      2 * r_m * x ^ 3 + 2 * r_m ^ 2 * x ^ 3 + 2 * r_m ^ 2 * x ^ 7 + 8 * r_m ^ 2 * x ^ 4 +
      8 * r_m ^ 2 * x ^ 6 + 12 * r_m ^ 2 * x ^ 5 + 3 / 4 * r_m * x ^ 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽77⁾`. -/
noncomputable def i8L4Q77_3 (x _r_000m _r_00m _r_00mm _r_0m _r_0mm r_m : ℝ) : ℝ :=
    -1 / 2 + x ^ 2 / 2 - r_m / 2 - x / 4 + x ^ 3 / 4 - 3 * r_m * x ^ 2 - 2 * r_m * x -
      2 * r_m * x ^ 3 - r_m * x ^ 4 / 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽77⁾`. -/
noncomputable def i8L4Q77_4 (_x _r_000m _r_00m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_77_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s77 x = i8L4S77 x + x * (i8L4Q77_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q77_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q77_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q77_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q77_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s77 i8Psi4s77N0 i8Psi4s77N1 i8Psi4s77N2 i8Psi4s77N3 i8Psi4s77N4 i8Psi4s77W
    i8Psi4s77N1c0 i8Psi4s77N1c1 i8Psi4s77N3c0 i8Psi4s77N3c1 i8Psi4s77N4c0 i8Psi4s77N4c1
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx,
    i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m000 hx, i13hw_m00m hx, i13hw_m0m
    hx, i13hw_m0m0 hx, i13hw_mm0 hx, i13hw_mm00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S77 i8L4Q77_0 i8L4Q77_1 i8L4Q77_2 i8L4Q77_3 i8L4Q77_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽77⁾`. -/
noncomputable def i8L4R77 (x : ℝ) : ℝ :=
  x * (i8L4Q77_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [negOne] x) + Real.log x * i8L4Q77_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q77_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q77_3 x (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q77_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R77 : Tendsto i8L4R77 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q77_0 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q77_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q77_1 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q77_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q77_2 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q77_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q77_3 (v 0) (v 6) (v 18) (v 24) (v 43) (v 57) (v 66)) (by
      unfold i8L4Q77_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q77_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q77_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q77_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q77_3 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R77
  unfold i8L4Q77_4
  ring

/-- The singular part of `Ψ₄⁽78⁾` at `ξ = 0`. -/
noncomputable def i8L4S78 (x : ℝ) : ℝ :=
    28 - 16 * Real.log x - 4 * Real.log x ^ 2 - 2 / 3 * π ^ 2 - 2 / 3 * Real.log x ^ 3 +
      2 / 3 * Real.log x * π ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽78⁾`. -/
noncomputable def i8L4Q78_0 (x r_0001 r_001 r_00m r_01 _r_01m r_0m r_0m01 r_0m1 r_1 _r_m _r_m1 : ℝ)
    : ℝ :=
    -2 + π ^ 2 - 29 / 4 * x - 11 / 2 * x ^ 2 - x ^ 5 / 2 + 13 / 4 * x ^ 3 - r_1 * x ^ 6 -
      16 * r_00m * x ^ 2 - 14 * r_1 * x ^ 3 - 12 * r_0m * x ^ 3 - 10 * r_001 * x ^ 2 -
      8 * r_01 * x ^ 3 - 4 * r_0001 * x ^ 2 - 2 * r_0m * x ^ 4 + 2 * r_01 * x ^ 4 +
      2 * r_0m * x ^ 6 + 2 * r_1 * x ^ 5 + 8 * r_0m * x ^ 5 + 8 * r_0m01 * x ^ 2 +
      18 * r_0m * x ^ 2 + 28 * r_1 * x + 32 * r_0m1 * x ^ 2 + 41 * r_01 * x ^ 2 -
      35 / 2 * r_1 * x ^ 2 - 2 / 3 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 6 + π ^ 2 * x / 6 +
      5 / 2 * r_1 * x ^ 4 - 20 * r_0m * r_1 * x ^ 5 - 8 * r_01 * r_0m * x ^ 5 +
      4 * r_0m * r_1 * x ^ 7 + 8 * r_0m * r_1 * x ^ 4 + 8 * r_0m * r_1 * x ^ 6 -
      2 / 3 * π ^ 2 * r_1 * x - 2 / 3 * π ^ 2 * r_1 * x ^ 3 - π ^ 2 * r_1 * x ^ 4 / 3 +
      2 / 3 * π ^ 2 * r_01 * x ^ 2 + 5 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽78⁾`. -/
noncomputable def i8L4Q78_1 (x _r_0001 r_001 _r_00m r_01 r_01m r_0m _r_0m01 r_0m1 r_1 r_m r_m1 : ℝ)
    : ℝ :=
    2 + x ^ 5 + x / 2 + 2 * x ^ 4 + 7 * x ^ 2 - 11 / 2 * x ^ 3 - 33 * r_1 * x ^ 2 -
      32 * r_m1 * x ^ 2 - 18 * r_m * x ^ 2 - 13 * r_1 * x ^ 4 - 8 * r_m * x ^ 5 -
      2 * r_m * x ^ 6 + 2 * r_1 * x ^ 6 + 4 * r_001 * x ^ 2 + 4 * r_m * x ^ 3 +
      8 * r_01m * x ^ 2 + 8 * r_0m * x ^ 2 + 8 * r_0m1 * x ^ 2 + 10 * r_01 * x ^ 2 +
      12 * r_1 * x + 32 * r_1 * x ^ 3 - 8 * r_1 * r_m * x ^ 4 - 8 * r_1 * r_m * x ^ 6 -
      4 * r_1 * r_m * x ^ 7 + 20 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽78⁾`. -/
noncomputable def i8L4Q78_2 (x _r_0001 _r_001 _r_00m r_01 _r_01m _r_0m _r_0m01 _r_0m1 r_1 _r_m _r_m1
    : ℝ) : ℝ :=
    -3 + x ^ 3 / 2 + 2 * x ^ 2 - x / 2 + r_1 * x ^ 4 - 5 * r_1 * x ^ 2 - 2 * r_01 * x ^ 2 +
      2 * r_1 * x + 2 * r_1 * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽78⁾`. -/
noncomputable def i8L4Q78_3 (_x _r_0001 _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽78⁾`. -/
noncomputable def i8L4Q78_4 (_x _r_0001 _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_78_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s78 x = i8L4S78 x + x * (i8L4Q78_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q78_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q78_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q78_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q78_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s78 i8Psi4s78N0 i8Psi4s78N1 i8Psi4s78N2 i8Psi4s78N3 i8Psi4s78N4 i8Psi4s78W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01m0
    hx, i13hw_0m0 hx, i13hw_0m10 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1m0 hx, i13hw_m0 hx, i13hw_m01
    hx, i13hw_m10 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_00m h0, i13hpl_rho_01 h0,
    i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S78 i8L4Q78_0 i8L4Q78_1 i8L4Q78_2 i8L4Q78_3 i8L4Q78_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽78⁾`. -/
noncomputable def i8L4R78 (x : ℝ) : ℝ :=
  x * (i8L4Q78_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q78_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q78_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q78_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q78_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R78 : Tendsto i8L4R78 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q78_0 (v 0) (v 3) (v 9) (v 18) (v 27) (v 36) (v 43) (v 44) (v
      49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q78_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q78_1 (v 0) (v 3) (v 9) (v 18) (v 27) (v 36) (v 43) (v 44) (v
      49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q78_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q78_2 (v 0) (v 3) (v 9) (v 18) (v 27) (v 36) (v 43) (v 44) (v
      49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q78_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q78_0 x (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one]
    x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q78_1 x (i13Rho [zero, zero, zero, one]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q78_2 x (i13Rho [zero, zero, zero, one]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R78
  unfold i8L4Q78_3 i8L4Q78_4
  ring

/-- The singular part of `Ψ₄⁽79⁾` at `ξ = 0`. -/
noncomputable def i8L4S79 (x : ℝ) : ℝ :=
    -24 + π ^ 2 + 16 * Real.log x - 2 / 3 * Real.log x * π ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽79⁾`. -/
noncomputable def i8L4Q79_0 (x r_01 r_01m r_0m r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    -2 * x - 2 * x ^ 5 + 4 * x ^ 3 - 4 / 3 * π ^ 2 + π ^ 2 * x ^ 3 - 32 * r_01m * x ^ 2 -
      32 * r_0m1 * x ^ 2 - 16 * r_1 * x - 16 * r_m * x - 8 * r_01 * x ^ 2 - 8 * r_m * x ^ 2 -
      4 * r_1 * x ^ 4 - 4 * r_1 * x ^ 6 + 4 * r_m * x ^ 4 + 4 * r_m * x ^ 6 + 8 * r_0m * x ^ 2 +
      8 * r_1 * x ^ 2 + 8 * r_1 * x ^ 3 + 8 * r_1 * x ^ 5 + 8 * r_m * x ^ 3 + 8 * r_m * x ^ 5 -
      7 / 12 * π ^ 2 * x - π ^ 2 * x ^ 2 / 3 - π ^ 2 * x ^ 4 / 3 - π ^ 2 * x ^ 5 / 12 +
      π ^ 2 * r_m * x ^ 5 - π ^ 2 * r_01 * x ^ 2 - π ^ 2 * r_m * x ^ 3 - 8 * r_1 * r_m * x ^ 3 -
      5 * π ^ 2 * r_1 * x ^ 3 + 2 * π ^ 2 * r_1 * x ^ 2 + 8 * r_1 * r_m * x ^ 7 -
      5 / 3 * π ^ 2 * r_0m * x ^ 2 - π ^ 2 * r_1 * x ^ 5 / 3 - π ^ 2 * r_1 * x ^ 6 / 6 -
      π ^ 2 * r_m * x ^ 4 / 6 + π ^ 2 * r_m * x ^ 6 / 6 + 2 / 3 * π ^ 2 * r_1 * x +
      2 / 3 * π ^ 2 * r_m * x + 10 / 3 * π ^ 2 * r_m * x ^ 2 + 16 / 3 * π ^ 2 * r_m1 * x ^ 2 +
      17 / 6 * π ^ 2 * r_1 * x ^ 4 - 10 / 3 * π ^ 2 * r_1 * r_m * x ^ 5 +
      π ^ 2 * r_1 * r_m * x ^ 3 / 3 + π ^ 2 * r_1 * r_m * x ^ 7 / 3 +
      4 / 3 * π ^ 2 * r_1 * r_m * x ^ 4 + 4 / 3 * π ^ 2 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽79⁾`. -/
noncomputable def i8L4Q79_1 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽79⁾`. -/
noncomputable def i8L4Q79_2 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽79⁾`. -/
noncomputable def i8L4Q79_3 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽79⁾`. -/
noncomputable def i8L4Q79_4 (_x _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_79_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s79 x = i8L4S79 x + x * (i8L4Q79_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x * i8L4Q79_1 x (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q79_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 3 * i8L4Q79_3 x (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q79_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s79 i8Psi4s79N0 i8Psi4s79N1 i8Psi4s79N2 i8Psi4s79N3 i8Psi4s79N4 i8Psi4s79W
  simp only [hpl_zero, i13hw_1m hx]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1
    h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S79 i8L4Q79_0 i8L4Q79_1 i8L4Q79_2 i8L4Q79_3 i8L4Q79_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽79⁾`. -/
noncomputable def i8L4R79 (x : ℝ) : ℝ :=
  x * (i8L4Q79_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q79_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) + Real.log x ^ 2 * i8L4Q79_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q79_3 x (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q79_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x))

theorem tendsto_i8L4R79 : Tendsto i8L4R79 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q79_0 (v 0) (v 27) (v 36) (v 43) (v 49) (v 65) (v 66) (v 67))
      (by
      unfold i8L4Q79_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q79_0 x (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R79
  unfold i8L4Q79_1 i8L4Q79_2 i8L4Q79_3 i8L4Q79_4
  ring

/-- The singular part of `Ψ₄⁽80k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S80k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽80k0⁾`. -/
noncomputable def i8L4Q80k0_0 (x r_001 r_001m r_00m1 r_01 r_01m r_01mm r_0m r_0m1 r_1 r_m r_m1
    _r_mm1 : ℝ) : ℝ :=
    4 - 12 * x ^ 2 - 8 * r_01mm - 3 * x ^ 4 + 2 * x - x ^ 5 / 4 + 17 / 4 * x ^ 3 +
      r_m * x ^ 6 / 2 - 50 * r_1 * x ^ 3 - 48 * r_01mm * x ^ 2 - 32 * r_01mm * x -
      32 * r_01mm * x ^ 3 - 12 * r_001m * x ^ 2 - 8 * r_01mm * x ^ 4 - 8 * r_0m1 * x -
      5 * r_1 * x ^ 5 - 4 * r_01m * x ^ 5 - 4 * r_0m * x ^ 2 - 4 * r_0m1 * x ^ 3 -
      2 * r_01m * x ^ 6 - 2 * r_0m1 * x ^ 2 - 2 * r_0m1 * x ^ 4 - 2 * r_m * x ^ 3 +
      2 * r_01m * x ^ 4 + 2 * r_0m1 * x ^ 6 + 4 * r_01m * x ^ 3 + 4 * r_0m1 * x ^ 5 +
      4 * r_m * x ^ 4 + 7 * r_m * x ^ 5 + 8 * r_001 * x ^ 2 + 8 * r_01m * x +
      14 * r_01m * x ^ 2 + 18 * r_01 * x ^ 2 + 19 * r_1 * x ^ 4 + 32 * r_m1 * x ^ 2 +
      36 * r_00m1 * x ^ 2 - r_1 * x ^ 6 / 2 + 33 / 2 * r_m * x ^ 2 + 73 / 2 * r_1 * x ^ 2 +
      r_1 * r_m * x ^ 7 - 24 * r_0m1 * r_m * x ^ 5 - 17 * r_1 * r_m * x ^ 5 -
      16 * r_0m1 * r_m * x ^ 4 - 16 * r_0m1 * r_m * x ^ 6 - 4 * r_0m1 * r_m * x ^ 3 -
      4 * r_0m1 * r_m * x ^ 7 + 4 * r_01m * r_m * x ^ 3 + 4 * r_01m * r_m * x ^ 7 +
      4 * r_1 * r_m * x ^ 4 + 12 * r_1 * r_m * x ^ 6 + 16 * r_01m * r_m * x ^ 4 +
      16 * r_01m * r_m * x ^ 6 + 24 * r_01m * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽80k0⁾`. -/
noncomputable def i8L4Q80k0_1 (x _r_001 _r_001m _r_00m1 r_01 _r_01m _r_01mm _r_0m r_0m1 r_1 _r_m
    r_m1 r_mm1 : ℝ) : ℝ :=
    -4 - x ^ 3 - 4 * x + 8 * r_mm1 - 24 * r_0m1 * x ^ 2 - 24 * r_m1 * x ^ 3 - 22 * r_1 * x ^ 2 -
      12 * r_m1 * x ^ 2 - 8 * r_01 * x ^ 2 - 4 * r_m1 * x ^ 4 + 2 * r_1 * x ^ 4 + 8 * r_m1 * x +
      8 * r_mm1 * x ^ 4 + 20 * r_1 * x ^ 3 + 32 * r_mm1 * x + 32 * r_mm1 * x ^ 3 +
      48 * r_mm1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽80k0⁾`. -/
noncomputable def i8L4Q80k0_2 (_x _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_01mm _r_0m _r_0m1 _r_1 _r_m
    _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽80k0⁾`. -/
noncomputable def i8L4Q80k0_3 (_x _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_01mm _r_0m _r_0m1 _r_1 _r_m
    _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽80k0⁾`. -/
noncomputable def i8L4Q80k0_4 (_x _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_01mm _r_0m _r_0m1 _r_1 _r_m
    _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

theorem i8L4_80k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s80k0 x = i8L4S80k0 x + x * (i8L4Q80k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)
      (i13Rho [negOne, negOne, one] x) +
      Real.log x * i8L4Q80k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one]
      x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one]
      x) + Real.log x ^ 2 * i8L4Q80k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x ^ 3 * i8L4Q80k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)
      (i13Rho [negOne, negOne, one] x) + Real.log x ^ 4 * i8L4Q80k0_4 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s80k0 i8Psi4s80k0N0 i8Psi4s80k0N1 i8Psi4s80k0N2 i8Psi4s80k0N3 i8Psi4s80k0N4
    i8Psi4s80k0W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0m10 hx, i13hw_10 hx, i13hw_1m hx, i13hw_m01 hx,
    i13hw_m01m hx, i13hw_m10 hx, i13hw_mm01 hx, i13hw_mm10 hx, i8hw_m0m1 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_001m h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0,
    i13hpl_rho_01m h0, i13hpl_rho_01mm h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0, i13hpl_rho_m1 h0, i8hpl_rho_mm1 h0]
  unfold i8L4S80k0 i8L4Q80k0_0 i8L4Q80k0_1 i8L4Q80k0_2 i8L4Q80k0_3 i8L4Q80k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽80k0⁾`. -/
noncomputable def i8L4R80k0 (x : ℝ) : ℝ :=
  x * (i8L4Q80k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x * i8L4Q80k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 2 * i8L4Q80k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 3 * i8L4Q80k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 4 * i8L4Q80k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x))

theorem tendsto_i8L4R80k0 : Tendsto i8L4R80k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q80k0_0 (v 0) (v 9) (v 15) (v 21) (v 27) (v 36) (v 40) (v 43) (v
      49) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q80k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q80k0_1 (v 0) (v 9) (v 15) (v 21) (v 27) (v 36) (v 40) (v 43) (v
      49) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q80k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q80k0_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) (i13Rho [negOne, negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q80k0_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R80k0
  unfold i8L4Q80k0_2 i8L4Q80k0_3 i8L4Q80k0_4
  ring

/-- The singular part of `Ψ₄⁽80k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S80k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽80k1⁾`. -/
noncomputable def i8L4Q80k1_0 (x r_001m r_00m r_00m1 r_00mm r_01 r_01m r_01mm r_0m r_0m01 r_0m1
    r_0m1m _r_0mm r_1 r_m r_m1 _r_mm1 : ℝ) : ℝ :=
    12 - 13 * x ^ 4 - 7 * x ^ 2 + 7 * x ^ 5 + 8 * r_01mm + 8 * x - x ^ 7 / 4 + 9 / 8 * x ^ 3 +
      r_0m * x ^ 8 + r_1 * x ^ 7 + r_m * x ^ 7 + r_m * x ^ 8 / 2 - r_m * x ^ 5 -
      64 * r_0m1m * x ^ 2 - 64 * r_m1 * x ^ 3 - 49 * r_1 * x ^ 5 - 24 * r_00m1 * x ^ 2 -
      24 * r_01m * x ^ 2 - 22 * r_1 * x ^ 3 - 12 * r_0m * x ^ 6 - 12 * r_0m01 * x ^ 2 -
      8 * r_01m * x - 8 * r_1 * x ^ 2 - 6 * r_m * x ^ 3 - 4 * r_01m * x ^ 3 - 4 * r_0m1 * x ^ 5 -
      3 * r_01 * x ^ 4 - 2 * r_01m * x ^ 4 - 2 * r_0m1 * x ^ 6 + 2 * r_01m * x ^ 6 +
      2 * r_0m1 * x ^ 4 + 4 * r_01m * x ^ 5 + 4 * r_0m * x ^ 5 + 4 * r_0m * x ^ 7 +
      4 * r_0m1 * x ^ 3 + 7 * r_0m * x ^ 4 + 8 * r_01mm * x ^ 4 + 8 * r_0m1 * x +
      10 * r_0m ^ 2 * x ^ 5 + 12 * r_01 * x ^ 3 + 16 * r_0m * x ^ 3 + 16 * r_m1 * x ^ 4 +
      23 * r_m * x ^ 2 + 23 * r_m * x ^ 4 + 24 * r_001m * x ^ 2 + 24 * r_00m * x ^ 2 +
      24 * r_0m1 * x ^ 2 + 32 * r_01mm * x + 32 * r_01mm * x ^ 3 + 40 * r_00mm * x ^ 2 +
      48 * r_01mm * x ^ 2 + 48 * r_0m * x ^ 2 + 66 * r_1 * x ^ 4 - 25 / 2 * r_m * x ^ 6 -
      r_1 * x ^ 8 / 2 + 25 / 2 * r_1 * x ^ 6 + r_1 * r_m * x ^ 9 - 64 * r_0m * r_m1 * x ^ 5 -
      40 * r_0m * r_m * x ^ 5 - 34 * r_0m * r_1 * x ^ 7 - 26 * r_1 * r_m * x ^ 7 -
      24 * r_01m * r_m * x ^ 5 - 24 * r_0m * r_1 * x ^ 5 - 16 * r_01m * r_m * x ^ 4 -
      16 * r_01m * r_m * x ^ 6 - 15 * r_1 * r_m * x ^ 5 - 12 * r_0m * r_m * x ^ 8 -
      8 * r_0m * r_1 * x ^ 4 - 8 * r_0m * r_m * x ^ 4 - 4 * r_01m * r_m * x ^ 3 -
      4 * r_01m * r_m * x ^ 7 - 4 * r_1 * r_m * x ^ 4 - 2 * r_0m * r_m * x ^ 9 +
      2 * r_0m * r_1 * x ^ 9 + 2 * r_0m * r_m * x ^ 7 + 4 * r_0m * r_1 * x ^ 8 +
      4 * r_0m1 * r_m * x ^ 3 + 4 * r_0m1 * r_m * x ^ 7 + 12 * r_01 * r_0m * x ^ 5 +
      12 * r_0m * r_m * x ^ 6 + 16 * r_0m1 * r_m * x ^ 4 + 16 * r_0m1 * r_m * x ^ 6 +
      24 * r_0m1 * r_m * x ^ 5 + 44 * r_1 * r_m * x ^ 6 + 60 * r_0m * r_1 * x ^ 6 -
      16 * r_0m * r_1 * r_m * x ^ 7 - 16 * r_0m * r_1 * r_m * x ^ 9 -
      4 * r_0m * r_1 * r_m * x ^ 6 - 4 * r_0m * r_1 * r_m * x ^ 10 + 40 * r_0m * r_1 * r_m * x ^ 8

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽80k1⁾`. -/
noncomputable def i8L4Q80k1_1 (x _r_001m _r_00m _r_00m1 _r_00mm _r_01 r_01m _r_01mm r_0m _r_0m01
    _r_0m1 _r_0m1m r_0mm r_1 r_m r_m1 r_mm1 : ℝ) : ℝ :=
    -4 + x ^ 6 + x ^ 7 / 2 - 17 * x ^ 3 - 8 * r_mm1 - 2 * x + 17 * x ^ 4 + 28 * x ^ 2 -
      19 / 2 * x ^ 5 + r_1 * x ^ 8 - 176 * r_mm1 * x ^ 2 - 89 * r_1 * x ^ 4 - 60 * r_m1 * x ^ 4 -
      40 * r_0mm * x ^ 2 - 36 * r_m * x ^ 2 - 32 * r_mm1 * x - 32 * r_mm1 * x ^ 3 -
      24 * r_01m * x ^ 2 - 20 * r_1 * x ^ 6 - 20 * r_m1 * x ^ 2 - 18 * r_m * x ^ 4 -
      16 * r_0m * x ^ 2 - 12 * r_m ^ 2 * x ^ 6 - 8 * r_m * x ^ 5 - 8 * r_m * x ^ 7 -
      8 * r_m1 * x - 8 * r_mm1 * x ^ 4 - 2 * r_m * x ^ 8 - 2 * r_m ^ 2 * x ^ 7 +
      2 * r_m ^ 2 * x ^ 9 + 8 * r_m ^ 2 * x ^ 4 + 12 * r_1 * x ^ 2 + 12 * r_m ^ 2 * x ^ 8 +
      24 * r_m * x ^ 6 + 28 * r_1 * x ^ 3 + 32 * r_m * x ^ 3 + 40 * r_m ^ 2 * x ^ 5 +
      68 * r_1 * x ^ 5 + 152 * r_m1 * x ^ 3 - 120 * r_1 * r_m * x ^ 6 -
      40 * r_1 * r_m ^ 2 * x ^ 8 - 8 * r_1 * r_m * x ^ 8 - 4 * r_1 * r_m * x ^ 9 +
      4 * r_1 * r_m ^ 2 * x ^ 6 + 4 * r_1 * r_m ^ 2 * x ^ 10 + 16 * r_1 * r_m * x ^ 4 +
      16 * r_1 * r_m ^ 2 * x ^ 7 + 16 * r_1 * r_m ^ 2 * x ^ 9 + 48 * r_1 * r_m * x ^ 5 +
      68 * r_1 * r_m * x ^ 7 + 128 * r_m * r_m1 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽80k1⁾`. -/
noncomputable def i8L4Q80k1_2 (_x _r_001m _r_00m _r_00m1 _r_00mm _r_01 _r_01m _r_01mm _r_0m _r_0m01
    _r_0m1 _r_0m1m _r_0mm _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽80k1⁾`. -/
noncomputable def i8L4Q80k1_3 (_x _r_001m _r_00m _r_00m1 _r_00mm _r_01 _r_01m _r_01mm _r_0m _r_0m01
    _r_0m1 _r_0m1m _r_0mm _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽80k1⁾`. -/
noncomputable def i8L4Q80k1_4 (_x _r_001m _r_00m _r_00m1 _r_00mm _r_01 _r_01m _r_01mm _r_0m _r_0m01
    _r_0m1 _r_0m1m _r_0mm _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

theorem i8L4_80k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s80k1 x = i8L4S80k1 x + x * (i8L4Q80k1_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x)
      + Real.log x * i8L4Q80k1_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
      Real.log x ^ 2 * i8L4Q80k1_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
      Real.log x ^ 3 * i8L4Q80k1_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
      Real.log x ^ 4 * i8L4Q80k1_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s80k1 i8Psi4s80k1N0 i8Psi4s80k1N1 i8Psi4s80k1N2 i8Psi4s80k1N3 i8Psi4s80k1N4
    i8Psi4s80k1W
  simp only [hpl_zero, i13hw_010m hx, i13hw_01m0 hx, i13hw_0m0 hx, i13hw_0m0m hx, i13hw_0mm0 hx,
    i13hw_10m hx, i13hw_1m0 hx, i13hw_1m0m hx, i13hw_1mm0 hx, i13hw_m0 hx, i13hw_m0m hx, i13hw_m1m0
    hx, i13hw_mm0 hx, i8hw_m10m hx]
  simp only [i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0, i13hpl_rho_00mm h0,
    i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_01mm h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0,
    i13hpl_rho_0m1 h0, i13hpl_rho_0m1m h0, i13hpl_rho_0mm h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0, i8hpl_rho_mm1 h0]
  unfold i8L4S80k1 i8L4Q80k1_0 i8L4Q80k1_1 i8L4Q80k1_2 i8L4Q80k1_3 i8L4Q80k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽80k1⁾`. -/
noncomputable def i8L4R80k1 (x : ℝ) : ℝ :=
  x * (i8L4Q80k1_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x * i8L4Q80k1_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one]
    x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 2 * i8L4Q80k1_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 3 * i8L4Q80k1_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 4 * i8L4Q80k1_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x))

theorem tendsto_i8L4R80k1 : Tendsto i8L4R80k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q80k1_0 (v 0) (v 15) (v 18) (v 21) (v 24) (v 27) (v 36) (v 40)
      (v 43) (v 44) (v 49) (v 54) (v 57) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q80k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q80k1_1 (v 0) (v 15) (v 18) (v 21) (v 24) (v 27) (v 36) (v 40)
      (v 43) (v 44) (v 49) (v 54) (v 57) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q80k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q80k1_0 x (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
    negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q80k1_1 x (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne]
      x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one]
      x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R80k1
  unfold i8L4Q80k1_2 i8L4Q80k1_3 i8L4Q80k1_4
  ring

/-- The singular part of `Ψ₄⁽81k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S81k0 (x : ℝ) : ℝ :=
    -21 / 4 - Real.log x ^ 2 / 2 + Real.log x ^ 3 / 3 + 3 / 2 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽81k0⁾`. -/
noncomputable def i8L4Q81k0_0 (x r_0001 r_001 r_00m1 r_01 r_01m r_0m01 r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ
    :=
    15 / 2 + r_01m + r_0m1 - 2 * r_00m1 - 2 * r_0m01 - 17 / 8 * x ^ 3 - 5 / 4 * x ^ 4 -
      x ^ 5 / 8 + 3 / 8 * x + 27 / 4 * x ^ 2 + r_1 * x ^ 4 / 2 - r_01m * x ^ 4 - r_0m1 * x ^ 4 -
      r_m * x - 16 * r_01 * x ^ 2 - 12 * r_00m1 * x ^ 2 - 8 * r_00m1 * x - 8 * r_00m1 * x ^ 3 -
      8 * r_01m * x ^ 3 - 8 * r_0m01 * x - 8 * r_0m01 * x ^ 3 - 8 * r_0m1 * x ^ 3 -
      3 * r_01 * x ^ 3 - 3 * r_01 * x ^ 5 - 3 * r_1 * x - 2 * r_00m1 * x ^ 4 - 2 * r_01 * x -
      2 * r_0m01 * x ^ 4 - 2 * r_m * x ^ 3 + 2 * r_001 * x ^ 2 + 3 * r_m * x ^ 5 +
      6 * r_0001 * x ^ 2 + 8 * r_01m * x + 8 * r_0m1 * x + 8 * r_m * x ^ 4 + 13 * r_1 * x ^ 3 -
      33 / 4 * r_m * x ^ 2 - 21 / 2 * r_1 * x ^ 2 - r_01 * x ^ 6 / 2 + r_m * x ^ 6 / 4 +
      15 / 2 * r_01 * x ^ 4 + r_01 * r_m * x ^ 7 - r_01 * r_m * x ^ 3 - 8 * r_01 * r_m * x ^ 4 +
      8 * r_01 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽81k0⁾`. -/
noncomputable def i8L4Q81k0_1 (x _r_0001 r_001 _r_00m1 r_01 _r_01m _r_0m01 r_0m1 r_1 _r_m _r_m1 : ℝ)
    : ℝ :=
    -5 + 2 * r_0m1 - 3 / 2 * x ^ 2 + x ^ 3 / 4 + 5 / 4 * x - 6 * r_001 * x ^ 2 - 6 * r_1 * x ^ 3 -
      2 * r_1 * x + 2 * r_0m1 * x ^ 4 + 5 * r_01 * x ^ 2 + 8 * r_0m1 * x + 8 * r_0m1 * x ^ 3 +
      12 * r_0m1 * x ^ 2 - r_1 * x ^ 4 / 2 + 17 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽81k0⁾`. -/
noncomputable def i8L4Q81k0_2 (x _r_0001 _r_001 _r_00m1 r_01 _r_01m _r_0m01 _r_0m1 r_1 _r_m r_m1 :
    ℝ) : ℝ :=
    3 / 2 - r_m1 - x / 4 - x ^ 3 / 4 + r_1 * x ^ 4 / 2 - r_1 * x - r_m1 * x ^ 4 -
      6 * r_m1 * x ^ 2 - 4 * r_m1 * x - 4 * r_m1 * x ^ 3 + 3 * r_01 * x ^ 2 + 3 * r_1 * x ^ 3 -
      5 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽81k0⁾`. -/
noncomputable def i8L4Q81k0_3 (_x _r_0001 _r_001 _r_00m1 _r_01 _r_01m _r_0m01 _r_0m1 _r_1 _r_m _r_m1
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽81k0⁾`. -/
noncomputable def i8L4Q81k0_4 (_x _r_0001 _r_001 _r_00m1 _r_01 _r_01m _r_0m01 _r_0m1 _r_1 _r_m _r_m1
    : ℝ) : ℝ :=
    0

theorem i8L4_81k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s81k0 x = i8L4S81k0 x + x * (i8L4Q81k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q81k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q81k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q81k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q81k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s81k0 i8Psi4s81k0N0 i8Psi4s81k0N1 i8Psi4s81k0N2 i8Psi4s81k0N3 i8Psi4s81k0N4
    i8Psi4s81k0W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_10 hx,
    i13hw_100 hx, i13hw_m001 hx, i13hw_m01 hx, i13hw_m010 hx, i13hw_m100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0,
    i13hpl_rho_01m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0]
  unfold i8L4S81k0 i8L4Q81k0_0 i8L4Q81k0_1 i8L4Q81k0_2 i8L4Q81k0_3 i8L4Q81k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽81k0⁾`. -/
noncomputable def i8L4R81k0 (x : ℝ) : ℝ :=
  x * (i8L4Q81k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x * i8L4Q81k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q81k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q81k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q81k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R81k0 : Tendsto i8L4R81k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q81k0_0 (v 0) (v 3) (v 9) (v 21) (v 27) (v 36) (v 44) (v 49) (v
      65) (v 66) (v 67)) (by
      unfold i8L4Q81k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q81k0_1 (v 0) (v 3) (v 9) (v 21) (v 27) (v 36) (v 44) (v 49) (v
      65) (v 66) (v 67)) (by
      unfold i8L4Q81k0_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q81k0_2 (v 0) (v 3) (v 9) (v 21) (v 27) (v 36) (v 44) (v 49) (v
      65) (v 66) (v 67)) (by
      unfold i8L4Q81k0_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q81k0_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q81k0_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q81k0_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R81k0
  unfold i8L4Q81k0_3 i8L4Q81k0_4
  ring

/-- The singular part of `Ψ₄⁽81k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S81k1 (x : ℝ) : ℝ :=
    3 + Real.log x ^ 2 - 3 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽81k1⁾`. -/
noncomputable def i8L4Q81k1_0 (x r_001 r_001m r_00m r_00m1 r_01 r_01m r_0m r_0m1 r_1 r_m r_m1 : ℝ) :
    ℝ :=
    -10 - x - 2 * r_001m - 2 * r_00m1 - 2 * r_01m - 2 * r_0m1 - 15 / 4 * x ^ 3 + x ^ 5 / 4 +
      3 / 2 * x ^ 2 + 7 / 2 * x ^ 4 + r_01 * x ^ 3 + r_01 * x ^ 4 / 2 + r_1 * x ^ 6 / 2 -
      r_0m * x ^ 5 - 32 * r_m1 * x ^ 2 - 18 * r_00m * x ^ 2 - 16 * r_01m * x - 16 * r_0m1 * x -
      14 * r_001 * x ^ 2 - 8 * r_001m * x - 8 * r_001m * x ^ 3 - 8 * r_00m1 * x -
      8 * r_00m1 * x ^ 3 - 3 * r_0m * x ^ 3 - 2 * r_001m * x ^ 4 - 2 * r_00m1 * x ^ 4 +
      2 * r_01m * x ^ 4 + 2 * r_0m1 * x ^ 4 + 3 * r_01 * x ^ 5 + 4 * r_01 * x + 4 * r_0m * x +
      14 * r_01 * x ^ 2 + 16 * r_01m * x ^ 3 + 16 * r_0m1 * x ^ 3 + 18 * r_0m * x ^ 2 -
      97 / 4 * r_1 * x ^ 4 - 35 / 4 * r_m * x ^ 2 - 31 / 4 * r_m * x ^ 4 - 29 / 4 * r_1 * x ^ 2 -
      15 / 2 * r_m * x ^ 5 - r_0m * x ^ 4 / 2 - r_m * x ^ 6 / 2 + 9 / 2 * r_1 * x ^ 5 +
      13 / 2 * r_m * x ^ 3 + 53 / 2 * r_1 * x ^ 3 + r_01 * r_m * x ^ 3 + r_0m * r_1 * x ^ 3 -
      r_01 * r_m * x ^ 7 - r_0m * r_1 * x ^ 7 - 8 * r_01 * r_m * x ^ 6 - 8 * r_0m * r_1 * x ^ 6 -
      8 * r_1 * r_m * x ^ 4 - 8 * r_1 * r_m * x ^ 6 + 2 * r_01 * r_0m * x ^ 3 +
      2 * r_01 * r_0m * x ^ 7 + 8 * r_01 * r_0m * x ^ 4 + 8 * r_01 * r_0m * x ^ 6 +
      8 * r_01 * r_m * x ^ 4 + 8 * r_0m * r_1 * x ^ 4 + 17 * r_1 * r_m * x ^ 5 -
      r_1 * r_m * x ^ 3 / 2 - r_1 * r_m * x ^ 7 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽81k1⁾`. -/
noncomputable def i8L4Q81k1_1 (x _r_001 _r_001m _r_00m _r_00m1 r_01 r_01m r_0m r_0m1 r_1 r_m _r_m1 :
    ℝ) : ℝ :=
    4 - 2 * r_01m - 2 * r_0m1 - 2 * x ^ 2 - 2 * x ^ 4 - x ^ 3 / 2 - x ^ 5 / 4 + 7 / 4 * x +
      r_1 * x ^ 2 + r_m * x ^ 6 / 2 - r_m * x ^ 2 - 8 * r_01m * x - 8 * r_01m * x ^ 3 -
      8 * r_0m1 * x - 8 * r_0m1 * x ^ 3 - 3 * r_1 * x ^ 3 - 3 * r_1 * x ^ 5 - 2 * r_01m * x ^ 4 -
      2 * r_0m1 * x ^ 4 - 2 * r_1 * x - 2 * r_m * x + 5 * r_m * x ^ 3 + 5 * r_m * x ^ 5 +
      7 * r_01 * x ^ 2 + 9 * r_0m * x ^ 2 - r_1 * x ^ 6 / 2 + 15 / 2 * r_1 * x ^ 4 +
      17 / 2 * r_m * x ^ 4 + r_1 * r_m * x ^ 7 - r_1 * r_m * x ^ 3 - 8 * r_1 * r_m * x ^ 4 +
      8 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽81k1⁾`. -/
noncomputable def i8L4Q81k1_2 (_x _r_001 _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽81k1⁾`. -/
noncomputable def i8L4Q81k1_3 (_x _r_001 _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽81k1⁾`. -/
noncomputable def i8L4Q81k1_4 (_x _r_001 _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_81k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s81k1 x = i8L4S81k1 x + x * (i8L4Q81k1_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q81k1_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q81k1_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q81k1_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q81k1_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s81k1 i8Psi4s81k1N0 i8Psi4s81k1N1 i8Psi4s81k1N2 i8Psi4s81k1N3 i8Psi4s81k1N4
    i8Psi4s81k1W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_01m0 hx, i13hw_0m0 hx, i13hw_0m10 hx, i13hw_10
    hx, i13hw_1m hx, i13hw_1m0 hx, i13hw_m0 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0,
    i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S81k1 i8L4Q81k1_0 i8L4Q81k1_1 i8L4Q81k1_2 i8L4Q81k1_3 i8L4Q81k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽81k1⁾`. -/
noncomputable def i8L4R81k1 (x : ℝ) : ℝ :=
  x * (i8L4Q81k1_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q81k1_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q81k1_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q81k1_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q81k1_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R81k1 : Tendsto i8L4R81k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q81k1_0 (v 0) (v 9) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43) (v
      49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q81k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q81k1_1 (v 0) (v 9) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43) (v
      49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q81k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q81k1_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
    zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q81k1_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
      x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R81k1
  unfold i8L4Q81k1_2 i8L4Q81k1_3 i8L4Q81k1_4
  ring

/-- The singular part of `Ψ₄⁽81k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S81k2 (x : ℝ) : ℝ :=
    -21 / 4 - Real.log x ^ 2 / 2 + Real.log x ^ 3 / 3 + 3 / 2 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽81k2⁾`. -/
noncomputable def i8L4Q81k2_0 (x r_000m r_001m r_00m r_00m1 r_01 r_01m r_0m r_0m01 r_0m1 r_1 r_m
    _r_m1 : ℝ) : ℝ :=
    21 / 2 + r_01m + r_0m1 + 2 * r_001m + 2 * r_0m01 + 4 * r_00m1 - x ^ 4 / 4 + 7 / 2 * x +
      15 / 8 * x ^ 3 + 39 / 4 * x ^ 2 + r_0m * x ^ 5 + r_01 * x ^ 6 / 2 + r_0m * x ^ 4 / 2 -
      r_01m * x ^ 4 - r_0m1 * x ^ 4 - r_1 * x - r_1 * x ^ 5 - 19 * r_m * x ^ 3 -
      8 * r_01 * x ^ 4 - 8 * r_01m * x ^ 3 - 8 * r_0m1 * x ^ 3 - 4 * r_0m * x - 3 * r_m * x -
      2 * r_00m * x ^ 2 - 2 * r_01 * x + 2 * r_001m * x ^ 4 + 2 * r_01 * x ^ 3 +
      2 * r_0m01 * x ^ 4 + 2 * r_1 * x ^ 3 + 3 * r_0m * x ^ 3 + 4 * r_00m1 * x ^ 4 +
      8 * r_001m * x + 8 * r_001m * x ^ 3 + 8 * r_01m * x + 8 * r_0m01 * x + 8 * r_0m01 * x ^ 3 +
      8 * r_0m1 * x + 8 * r_1 * x ^ 4 + 10 * r_000m * x ^ 2 + 16 * r_00m1 * x +
      16 * r_00m1 * x ^ 3 + 20 * r_001m * x ^ 2 - 49 / 2 * r_0m * x ^ 2 - 43 / 2 * r_m * x ^ 2 -
      31 / 4 * r_1 * x ^ 2 - 15 / 2 * r_01 * x ^ 2 - r_m * x ^ 4 / 2 - r_1 * x ^ 6 / 4 +
      r_0m * r_1 * x ^ 7 - r_0m * r_1 * x ^ 3 - 8 * r_01 * r_0m * x ^ 4 -
      8 * r_01 * r_0m * x ^ 6 - 8 * r_0m * r_1 * x ^ 4 - 2 * r_01 * r_0m * x ^ 3 -
      2 * r_01 * r_0m * x ^ 7 + 8 * r_0m * r_1 * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽81k2⁾`. -/
noncomputable def i8L4Q81k2_1 (x _r_000m _r_001m r_00m _r_00m1 _r_01 r_01m r_0m _r_0m01 _r_0m1 _r_1
    r_m _r_m1 : ℝ) : ℝ :=
    -7 + 2 * r_01m - 5 / 2 * x ^ 2 - 3 / 4 * x + x ^ 3 / 4 + r_m * x ^ 4 / 2 -
      20 * r_01m * x ^ 2 - 10 * r_00m * x ^ 2 - 2 * r_m * x + 2 * r_01m * x ^ 4 + 8 * r_01m * x +
      8 * r_01m * x ^ 3 + 10 * r_m * x ^ 3 + 11 * r_0m * x ^ 2 + 15 / 2 * r_m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽81k2⁾`. -/
noncomputable def i8L4Q81k2_2 (x _r_000m _r_001m _r_00m _r_00m1 _r_01 _r_01m r_0m _r_0m01 _r_0m1 r_1
    r_m r_m1 : ℝ) : ℝ :=
    5 / 2 + r_m1 + x ^ 2 + x ^ 4 + 2 * x - 11 / 4 * x ^ 3 + x ^ 5 / 4 + r_1 * x ^ 5 +
      r_m1 * x ^ 4 + r_1 * x ^ 6 / 2 + r_m * x ^ 4 / 2 - r_1 * x - 10 * r_m * x ^ 2 -
      10 * r_m1 * x ^ 2 - 9 * r_1 * x ^ 4 - 3 * r_m * x ^ 5 - 2 * r_m * x + 3 * r_m * x ^ 3 +
      4 * r_m1 * x + 4 * r_m1 * x ^ 3 + 5 * r_0m * x ^ 2 + 12 * r_1 * x ^ 3 -
      7 / 2 * r_1 * x ^ 2 - r_m * x ^ 6 / 2 - r_1 * r_m * x ^ 3 - r_1 * r_m * x ^ 7 -
      4 * r_1 * r_m * x ^ 4 - 4 * r_1 * r_m * x ^ 6 + 10 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽81k2⁾`. -/
noncomputable def i8L4Q81k2_3 (_x _r_000m _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1
    _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽81k2⁾`. -/
noncomputable def i8L4Q81k2_4 (_x _r_000m _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1
    _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_81k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s81k2 x = i8L4S81k2 x + x * (i8L4Q81k2_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x) + Real.log x * i8L4Q81k2_1 x (i13Rho [zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q81k2_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) + Real.log x ^ 3 * i8L4Q81k2_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 4 * i8L4Q81k2_4 x (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s81k2 i8Psi4s81k2N0 i8Psi4s81k2N1 i8Psi4s81k2N2 i8Psi4s81k2N3 i8Psi4s81k2N4
    i8Psi4s81k2W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_010m hx, i13hw_0m0 hx, i13hw_0m00
    hx, i13hw_100m hx, i13hw_10m hx, i13hw_10m0 hx, i13hw_1m00 hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0,
    i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0,
    i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S81k2 i8L4Q81k2_0 i8L4Q81k2_1 i8L4Q81k2_2 i8L4Q81k2_3 i8L4Q81k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽81k2⁾`. -/
noncomputable def i8L4R81k2 (x : ℝ) : ℝ :=
  x * (i8L4Q81k2_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q81k2_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) + Real.log x ^ 2 * i8L4Q81k2_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q81k2_3 x (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q81k2_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x))

theorem tendsto_i8L4R81k2 : Tendsto i8L4R81k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q81k2_0 (v 0) (v 6) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43) (v
      44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q81k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q81k2_1 (v 0) (v 6) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43) (v
      44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q81k2_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q81k2_2 (v 0) (v 6) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43) (v
      44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q81k2_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q81k2_0 x (i13Rho [zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q81k2_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q81k2_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R81k2
  unfold i8L4Q81k2_3 i8L4Q81k2_4
  ring

/-- The singular part of `Ψ₄⁽82⁾` at `ξ = 0`. -/
noncomputable def i8L4S82 (x : ℝ) : ℝ :=
    -14 + 4 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽82⁾`. -/
noncomputable def i8L4Q82_0 (x r_001 r_00m r_01 r_01m r_0m r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ :=
    -16 - 12 * x ^ 2 - 4 * x ^ 4 - x ^ 5 / 2 + 9 / 2 * x + r_m * x ^ 6 - r_1 * x ^ 6 -
      40 * r_01m * x ^ 2 - 20 * r_00m * x ^ 2 - 18 * r_1 * x ^ 3 - 12 * r_001 * x ^ 2 -
      8 * r_1 * x - 8 * r_m * x - 6 * r_1 * x ^ 5 + 10 * r_m * x ^ 5 + 13 * r_m * x ^ 2 +
      14 * r_1 * x ^ 4 + 18 * r_m * x ^ 4 + 19 * r_1 * x ^ 2 + 24 * r_01 * x ^ 2 +
      24 * r_0m1 * x ^ 2 + 30 * r_m * x ^ 3 + 40 * r_0m * x ^ 2 - 16 * r_1 * r_m * x ^ 4 -
      2 * r_1 * r_m * x ^ 3 + 2 * r_1 * r_m * x ^ 7 + 16 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽82⁾`. -/
noncomputable def i8L4Q82_1 (x _r_001 _r_00m r_01 _r_01m r_0m _r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    16 + x ^ 5 - 12 * x ^ 3 + 4 * x ^ 2 + 4 * x ^ 4 + 7 * x - 64 * r_m1 * x ^ 2 -
      40 * r_m * x ^ 2 - 34 * r_1 * x ^ 4 - 24 * r_1 * x ^ 2 - 12 * r_m * x ^ 5 - 8 * r_1 * x -
      8 * r_m * x - 2 * r_m * x ^ 6 + 2 * r_1 * x ^ 6 + 2 * r_m * x ^ 4 + 4 * r_1 * x ^ 5 +
      12 * r_01 * x ^ 2 + 12 * r_m * x ^ 3 + 20 * r_0m * x ^ 2 + 60 * r_1 * x ^ 3 -
      16 * r_1 * r_m * x ^ 4 - 16 * r_1 * r_m * x ^ 6 - 4 * r_1 * r_m * x ^ 3 -
      4 * r_1 * r_m * x ^ 7 + 40 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽82⁾`. -/
noncomputable def i8L4Q82_2 (_x _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽82⁾`. -/
noncomputable def i8L4Q82_3 (_x _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽82⁾`. -/
noncomputable def i8L4Q82_4 (_x _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_82_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s82 x = i8L4S82 x + x * (i8L4Q82_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q82_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q82_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q82_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q82_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s82 i8Psi4s82N0 i8Psi4s82N1 i8Psi4s82N2 i8Psi4s82N3 i8Psi4s82N4 i8Psi4s82W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_0m0 hx, i13hw_10 hx, i13hw_10m hx, i13hw_1m hx,
    i13hw_1m0 hx, i13hw_m0 hx, i13hw_m01 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_00m h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0,
    i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S82 i8L4Q82_0 i8L4Q82_1 i8L4Q82_2 i8L4Q82_3 i8L4Q82_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽82⁾`. -/
noncomputable def i8L4R82 (x : ℝ) : ℝ :=
  x * (i8L4Q82_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one]
    x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q82_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q82_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q82_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q82_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R82 : Tendsto i8L4R82 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q82_0 (v 0) (v 9) (v 18) (v 27) (v 36) (v 43) (v 49) (v 65) (v
      66) (v 67)) (by
      unfold i8L4Q82_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q82_1 (v 0) (v 9) (v 18) (v 27) (v 36) (v 43) (v 49) (v 65) (v
      66) (v 67)) (by
      unfold i8L4Q82_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q82_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q82_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R82
  unfold i8L4Q82_2 i8L4Q82_3 i8L4Q82_4
  ring

/-- The regular parts of group 6. -/
noncomputable def i8L4RG6 (x : ℝ) : ℝ :=
  i8L4R77 x + i8L4R78 x + i8L4R79 x + i8L4R80k0 x + i8L4R80k1 x + i8L4R81k0 x +
    i8L4R81k1 x + i8L4R81k2 x + i8L4R82 x

theorem tendsto_i8L4RG6 : Tendsto i8L4RG6 (𝓝[>] 0) (𝓝 0) := by
  have H := ((((((((tendsto_i8L4R77.add tendsto_i8L4R78).add tendsto_i8L4R79).add
    tendsto_i8L4R80k0).add tendsto_i8L4R80k1).add tendsto_i8L4R81k0).add tendsto_i8L4R81k1).add
    tendsto_i8L4R81k2).add tendsto_i8L4R82)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
