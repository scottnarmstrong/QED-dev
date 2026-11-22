/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L9
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 10

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_108k3_eq`, `QED.ThreeLoopD.tendsto_i8L4RG10` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽108k3⁾` at `ξ = 0`. -/
noncomputable def i8L4S108k3 (x : ℝ) : ℝ :=
    48 - 36 * Real.log x - 2 * Real.log x ^ 3 + 12 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽108k3⁾`. -/
noncomputable def i8L4Q108k3_0 (x r_00001 r_0001 r_0001m r_000m r_001 r_0010m _r_001m r_00m r_00m1
    r_01 _r_01m r_0m r_0m01 r_0m1 r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -841 / 4 - 307 / 4 * x - 81 / 4 * x ^ 2 - 5 / 2 * x ^ 4 - x ^ 5 / 4 + 47 / 4 * x ^ 3 +
      r_0m * x ^ 6 - 216 * r_00001 * x ^ 2 - 108 * r_0001 * x ^ 3 - 51 * r_001 * x ^ 2 -
      36 * r_1 * x ^ 3 - 24 * r_0m1 * x ^ 3 - 20 * r_01 * x ^ 3 - 18 * r_0001 * x ^ 4 -
      8 * r_0m1 * x - 4 * r_1 * x ^ 5 - 2 * r_0m1 * x ^ 4 + 3 * r_001 * x ^ 4 + 4 * r_0m * x ^ 3 +
      4 * r_0m * x ^ 4 + 5 * r_01 * x ^ 4 + 8 * r_1 * x ^ 2 + 12 * r_001 * x +
      14 * r_0m * x ^ 5 + 20 * r_0m01 * x ^ 2 + 24 * r_000m * x ^ 2 + 24 * r_0010m * x ^ 2 +
      34 * r_0m1 * x ^ 2 + 36 * r_0001 * x + 36 * r_001 * x ^ 3 + 36 * r_00m * x ^ 2 +
      40 * r_00m1 * x ^ 2 + 60 * r_0m * x ^ 2 + 72 * r_0001m * x ^ 2 - r_1 * x ^ 6 / 2 +
      65 / 2 * r_1 * x ^ 4 - 34 * r_0m * r_1 * x ^ 5 - 20 * r_01 * r_0m * x ^ 5 +
      2 * r_0m * r_1 * x ^ 7 + 8 * r_0m * r_1 * x ^ 4 + 24 * r_0m * r_1 * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽108k3⁾`. -/
noncomputable def i8L4Q108k3_1 (x _r_00001 r_0001 _r_0001m _r_000m r_001 _r_0010m r_001m r_00m
    r_00m1 r_01 r_01m r_0m r_0m01 r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    100 + x ^ 5 + 8 * x ^ 4 + 15 * x ^ 2 - 69 / 4 * x ^ 3 + 155 / 4 * x - r_m * x ^ 6 -
      70 * r_1 * x ^ 4 - 60 * r_01 * x ^ 3 - 60 * r_m * x ^ 2 - 36 * r_0m * x ^ 2 -
      34 * r_m1 * x ^ 2 - 28 * r_0m * x ^ 3 - 24 * r_001 * x - 24 * r_001m * x ^ 2 -
      24 * r_00m * x ^ 2 - 24 * r_m * x ^ 3 - 22 * r_0m * x ^ 4 - 20 * r_0m1 * x ^ 2 -
      16 * r_0m * x ^ 5 - 14 * r_m * x ^ 5 - 12 * r_01 * x - 9 * r_m * x ^ 4 - 8 * r_0m1 * x -
      2 * r_0m * x ^ 6 + 2 * r_1 * x ^ 6 + 2 * r_m1 * x ^ 4 + 3 * r_01 * x ^ 4 +
      4 * r_0m1 * x ^ 4 + 8 * r_m1 * x + 12 * r_001 * x ^ 4 + 12 * r_1 * x ^ 5 +
      20 * r_01m * x ^ 2 + 24 * r_0m01 * x ^ 2 + 24 * r_0m1 * x ^ 3 + 24 * r_m1 * x ^ 3 +
      48 * r_00m1 * x ^ 2 + 51 * r_01 * x ^ 2 + 56 * r_1 * x ^ 3 + 72 * r_001 * x ^ 3 +
      108 * r_0001 * x ^ 2 - 24 * r_01 * r_0m * x ^ 5 - 24 * r_0m * r_1 * x ^ 6 -
      24 * r_1 * r_m * x ^ 6 - 8 * r_1 * r_m * x ^ 4 - 4 * r_0m * r_1 * x ^ 7 -
      2 * r_1 * r_m * x ^ 7 + 8 * r_0m * r_1 * x ^ 4 + 20 * r_0m * r_1 * x ^ 5 +
      34 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽108k3⁾`. -/
noncomputable def i8L4Q108k3_2 (x _r_00001 _r_0001 _r_0001m _r_000m r_001 _r_0010m _r_001m _r_00m
    _r_00m1 r_01 r_01m r_0m _r_0m01 _r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    -31 / 2 - x ^ 5 - 6 * x ^ 4 + 5 * x ^ 2 + 6 * x ^ 3 - 25 / 4 * x - 24 * r_m1 * x ^ 3 -
      18 * r_001 * x ^ 2 - 18 * r_01 * x ^ 3 - 8 * r_1 * x ^ 5 - 4 * r_m1 * x ^ 4 -
      3 * r_01 * x ^ 4 - 2 * r_1 * x ^ 6 + 2 * r_1 * x ^ 3 + 2 * r_m * x ^ 6 + 4 * r_m * x ^ 3 +
      6 * r_01 * x + 6 * r_1 * x + 8 * r_0m * x ^ 2 + 8 * r_m1 * x + 16 * r_m * x ^ 4 +
      16 * r_m * x ^ 5 + 18 * r_m * x ^ 2 + 20 * r_m1 * x ^ 2 + 24 * r_01m * x ^ 2 -
      67 / 2 * r_1 * x ^ 2 + 71 / 2 * r_1 * x ^ 4 - 20 * r_1 * r_m * x ^ 5 -
      8 * r_1 * r_m * x ^ 4 + 4 * r_1 * r_m * x ^ 7 + 24 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽108k3⁾`. -/
noncomputable def i8L4Q108k3_3 (_x _r_00001 _r_0001 _r_0001m _r_000m _r_001 _r_0010m _r_001m _r_00m
    _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽108k3⁾`. -/
noncomputable def i8L4Q108k3_4 (_x _r_00001 _r_0001 _r_0001m _r_000m _r_001 _r_0010m _r_001m _r_00m
    _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_108k3_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k3 x = i8L4S108k3 x + x * (i8L4Q108k3_0 x (i13Rho [zero, zero, zero, zero, one] x)
      (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q108k3_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 2 * i8L4Q108k3_2 x (i13Rho [zero, zero, zero, zero, one] x)
      (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q108k3_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 4 * i8L4Q108k3_4 x (i13Rho [zero, zero, zero, zero, one] x)
      (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s108k3 i8Psi4s108k3N0 i8Psi4s108k3N1 i8Psi4s108k3N2 i8Psi4s108k3N3 i8Psi4s108k3N4
    i8Psi4s108k3W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00100 hx, i13hw_001m0 hx, i13hw_00m0 hx,
    i13hw_0100 hx, i13hw_010m0 hx, i13hw_01m0 hx, i13hw_01m00 hx, i13hw_0m0 hx, i13hw_0m00 hx,
    i13hw_100 hx, i13hw_10m0 hx, i13hw_1m0 hx, i13hw_1m00 hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_00001 h0, i13hpl_rho_0001 h0, i13hpl_rho_0001m h0, i13hpl_rho_000m h0,
    i13hpl_rho_001 h0, i13hpl_rho_0010m h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1
    h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1
    h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S108k3 i8L4Q108k3_0 i8L4Q108k3_1 i8L4Q108k3_2 i8L4Q108k3_3 i8L4Q108k3_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽108k3⁾`. -/
noncomputable def i8L4R108k3 (x : ℝ) : ℝ :=
  x * (i8L4Q108k3_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q108k3_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) + Real.log x ^ 2 * i8L4Q108k3_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho
    [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho
    [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q108k3_3 x (i13Rho [zero, zero, zero, zero, one]
    x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x)
    (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q108k3_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x))

theorem tendsto_i8L4R108k3 : Tendsto i8L4R108k3 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k3_0 (v 0) (v 1) (v 3) (v 5) (v 6) (v 9) (v 11) (v 15) (v
      18) (v 21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q108k3_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k3_1 (v 0) (v 1) (v 3) (v 5) (v 6) (v 9) (v 11) (v 15) (v
      18) (v 21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q108k3_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k3_2 (v 0) (v 1) (v 3) (v 5) (v 6) (v 9) (v 11) (v 15) (v
      18) (v 21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q108k3_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q108k3_0 x (i13Rho [zero,
    zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one,
    negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q108k3_1 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one,
      zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q108k3_2 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one,
      zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R108k3
  unfold i8L4Q108k3_3 i8L4Q108k3_4
  ring

/-- The singular part of `Ψ₄⁽108k4⁾` at `ξ = 0`. -/
noncomputable def i8L4S108k4 (x : ℝ) : ℝ :=
    -12 - 6 * Real.log x ^ 2 + 2 * Real.log x ^ 3 + 12 * Real.log x - Real.log x ^ 4 / 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽108k4⁾`. -/
noncomputable def i8L4Q108k4_0 (x r_00001 r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    621 / 4 + 39 * x + 3 / 8 * x ^ 3 + 33 / 4 * x ^ 2 - 30 * r_0001 * x ^ 2 - 12 * r_0001 * x +
      6 * r_0001 * x ^ 4 + 36 * r_0001 * x ^ 3 + 144 * r_00001 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽108k4⁾`. -/
noncomputable def i8L4Q108k4_1 (x _r_00001 r_0001 r_001 _r_01 _r_1 : ℝ) : ℝ :=
    -237 / 2 - 159 / 4 * x - 21 / 2 * x ^ 2 - 3 / 4 * x ^ 3 - 108 * r_0001 * x ^ 2 -
      36 * r_001 * x ^ 3 - 6 * r_001 * x ^ 4 + 12 * r_001 * x + 30 * r_001 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽108k4⁾`. -/
noncomputable def i8L4Q108k4_2 (x _r_00001 _r_0001 r_001 r_01 _r_1 : ℝ) : ℝ :=
    81 / 2 + 3 / 4 * x ^ 3 + 15 / 2 * x ^ 2 + 39 / 2 * x - 15 * r_01 * x ^ 2 - 6 * r_01 * x +
      3 * r_01 * x ^ 4 + 18 * r_01 * x ^ 3 + 36 * r_001 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽108k4⁾`. -/
noncomputable def i8L4Q108k4_3 (x _r_00001 _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    -7 - 4 * x ^ 2 - 11 / 2 * x - x ^ 3 / 2 - r_1 * x ^ 4 - 6 * r_01 * x ^ 2 - 6 * r_1 * x ^ 3 +
      2 * r_1 * x + 5 * r_1 * x ^ 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽108k4⁾`. -/
noncomputable def i8L4Q108k4_4 (_x _r_00001 _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_108k4_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k4 x = i8L4S108k4 x + x * (i8L4Q108k4_0 x (i13Rho [zero, zero, zero, zero, one] x)
      (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
      [one] x) + Real.log x * i8L4Q108k4_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero,
      zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q108k4_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q108k4_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q108k4_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s108k4 i8Psi4s108k4N0 i8Psi4s108k4N1 i8Psi4s108k4N2 i8Psi4s108k4N3 i8Psi4s108k4N4
    i8Psi4s108k4W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_01000 hx, i13hw_1000 hx]
  simp only [i13hpl_rho_00001 h0, i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S108k4 i8L4Q108k4_0 i8L4Q108k4_1 i8L4Q108k4_2 i8L4Q108k4_3 i8L4Q108k4_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽108k4⁾`. -/
noncomputable def i8L4R108k4 (x : ℝ) : ℝ :=
  x * (i8L4Q108k4_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q108k4_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q108k4_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q108k4_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q108k4_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R108k4 : Tendsto i8L4R108k4 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k4_0 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q108k4_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k4_1 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q108k4_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k4_2 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q108k4_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k4_3 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q108k4_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q108k4_0 x (i13Rho [zero,
    zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q108k4_1 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q108k4_2 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q108k4_3 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R108k4
  unfold i8L4Q108k4_4
  ring

/-- The singular part of `Ψ₄⁽109⁾` at `ξ = 0`. -/
noncomputable def i8L4S109 (x : ℝ) : ℝ :=
    (2 + Real.log x ^ 2 + 2 * Real.log x + x * Real.log x ^ 3 / 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽109⁾`. -/
noncomputable def i8L4Q109_0 (x : ℝ) : ℝ :=
    2 - x / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽109⁾`. -/
noncomputable def i8L4Q109_1 (x : ℝ) : ℝ :=
    -2 + x / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽109⁾`. -/
noncomputable def i8L4Q109_2 (x : ℝ) : ℝ :=
    1 - x / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽109⁾`. -/
noncomputable def i8L4Q109_3 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽109⁾`. -/
noncomputable def i8L4Q109_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_109_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s109 x = i8L4S109 x + x * (i8L4Q109_0 x + Real.log x * i8L4Q109_1 x +
      Real.log x ^ 2 * i8L4Q109_2 x + Real.log x ^ 3 * i8L4Q109_3 x +
      Real.log x ^ 4 * i8L4Q109_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s109 i8Psi4s109N0 i8Psi4s109N1 i8Psi4s109N2 i8Psi4s109N3 i8Psi4s109N4 i8Psi4s109W
  simp only [hpl_zero, i13hw_00, i13hw_000]

  unfold i8L4S109 i8L4Q109_0 i8L4Q109_1 i8L4Q109_2 i8L4Q109_3 i8L4Q109_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽109⁾`. -/
noncomputable def i8L4R109 (x : ℝ) : ℝ :=
  x * (i8L4Q109_0 x + Real.log x * i8L4Q109_1 x + Real.log x ^ 2 * i8L4Q109_2 x +
    Real.log x ^ 3 * i8L4Q109_3 x + Real.log x ^ 4 * i8L4Q109_4 x)

theorem tendsto_i8L4R109 : Tendsto i8L4R109 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q109_0 (v 0)) (by
      unfold i8L4Q109_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q109_1 (v 0)) (by
      unfold i8L4Q109_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q109_2 (v 0)) (by
      unfold i8L4Q109_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q109_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q109_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q109_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R109
  unfold i8L4Q109_3 i8L4Q109_4
  ring

/-- The singular part of `Ψ₄⁽110⁾` at `ξ = 0`. -/
noncomputable def i8L4S110 (x : ℝ) : ℝ :=
    (-1 - Real.log x - Real.log x ^ 2 / 2 + x / 16 - x * Real.log x ^ 3 / 12) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽110⁾`. -/
noncomputable def i8L4Q110_0 (x r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    -13 / 8 - r_m / 8 - x ^ 3 / 16 + x ^ 2 / 8 + x / 16 - 2 * r_000m * x ^ 2 -
      r_0m * x ^ 2 / 2 + r_m * x ^ 4 / 8

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽110⁾`. -/
noncomputable def i8L4Q110_1 (x _r_000m r_00m _r_0m r_m : ℝ) : ℝ :=
    7 / 4 - r_m / 4 - x / 4 - x ^ 2 / 4 + x ^ 3 / 8 + r_m * x ^ 2 / 2 + 2 * r_00m * x ^ 2 -
      r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽110⁾`. -/
noncomputable def i8L4Q110_2 (x _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    -3 / 4 - r_m / 4 - x ^ 3 / 8 + x ^ 2 / 4 + x / 8 - r_0m * x ^ 2 + r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽110⁾`. -/
noncomputable def i8L4Q110_3 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽110⁾`. -/
noncomputable def i8L4Q110_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_110_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s110 x = i8L4S110 x + x * (i8L4Q110_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q110_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q110_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q110_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q110_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s110 i8Psi4s110N0 i8Psi4s110N1 i8Psi4s110N2 i8Psi4s110N3 i8Psi4s110N4 i8Psi4s110W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_m0 hx,
    i13hw_m00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S110 i8L4Q110_0 i8L4Q110_1 i8L4Q110_2 i8L4Q110_3 i8L4Q110_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽110⁾`. -/
noncomputable def i8L4R110 (x : ℝ) : ℝ :=
  x * (i8L4Q110_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q110_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q110_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q110_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q110_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R110 : Tendsto i8L4R110 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q110_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q110_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q110_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q110_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q110_2 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q110_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q110_0 x (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q110_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q110_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R110
  unfold i8L4Q110_3 i8L4Q110_4
  ring

/-- The singular part of `Ψ₄⁽111k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S111k0 (x : ℝ) : ℝ :=
    -1 / 4 - Real.log x ^ 3 / 6 + 3 / 4 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽111k0⁾`. -/
noncomputable def i8L4Q111k0_0 (x r_000m r_00m r_00m0m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    3 / 4 + r_00mm + r_0mm / 2 - 17 / 32 * x - x ^ 5 / 32 + x ^ 2 / 4 + x ^ 4 / 8 +
      r_000m * x ^ 2 + r_0m * x ^ 3 / 2 + r_0m * x ^ 5 / 2 + r_0mm * x ^ 4 / 2 + r_m * x / 2 +
      r_0m ^ 2 * x ^ 7 / 2 - r_00mm * x ^ 4 - r_0mm * x ^ 2 - 4 * r_00m0m * x ^ 2 -
      3 * r_0m * x ^ 2 - 2 * r_0m * x - 3 / 2 * r_00m * x ^ 2 - r_m * x ^ 5 / 2 -
      r_0m ^ 2 * x ^ 3 / 2 - r_0m * x ^ 4 / 4 - r_m * x ^ 4 / 8 + r_m * x ^ 6 / 8 +
      r_0m * r_m * x ^ 5 - r_0m * r_m * x ^ 3 / 2 - r_0m * r_m * x ^ 7 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽111k0⁾`. -/
noncomputable def i8L4Q111k0_1 (x _r_000m r_00m _r_00m0m r_00mm r_0m _r_0mm r_m : ℝ) : ℝ :=
    -1 - 15 / 16 * x - 3 / 4 * x ^ 2 - x ^ 4 / 4 + x ^ 5 / 16 + 3 / 8 * x ^ 3 + r_0m * x ^ 2 +
      r_m * x ^ 3 / 2 + r_m * x ^ 5 / 2 - r_00m * x ^ 2 - 4 * r_00mm * x ^ 2 + 2 * r_m * x -
      r_m ^ 2 * x ^ 5 / 2 - r_m * x ^ 6 / 4 + r_m ^ 2 * x ^ 3 / 4 + r_m ^ 2 * x ^ 7 / 4 +
      13 / 4 * r_m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽111k0⁾`. -/
noncomputable def i8L4Q111k0_2 (x _r_000m _r_00m _r_00m0m _r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    1 / 2 + x ^ 2 / 2 - 3 / 8 * x ^ 3 - x / 16 - x ^ 5 / 16 + x ^ 4 / 4 + r_m * x +
      r_0m * x ^ 2 / 2 + 2 * r_0mm * x ^ 2 - r_m * x ^ 2 / 2 - r_m * x ^ 3 / 2 -
      r_m * x ^ 5 / 2 - r_m ^ 2 * x ^ 7 / 4 + r_m * x ^ 4 / 4 + r_m * x ^ 6 / 4 +
      r_m ^ 2 * x ^ 3 / 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽111k0⁾`. -/
noncomputable def i8L4Q111k0_3 (_x _r_000m _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽111k0⁾`. -/
noncomputable def i8L4Q111k0_4 (_x _r_000m _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_111k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s111k0 x = i8L4S111k0 x +
      x * (i8L4Q111k0_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q111k0_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q111k0_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q111k0_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q111k0_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s111k0 i8Psi4s111k0N0 i8Psi4s111k0N1 i8Psi4s111k0N2 i8Psi4s111k0N3 i8Psi4s111k0N4
    i8Psi4s111k0W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_00mm0 hx, i13hw_0m0 hx, i13hw_0m00
    hx, i13hw_0m0m0 hx, i13hw_0mm0 hx, i13hw_0mm00 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m00m hx,
    i13hw_m0m0 hx, i13hw_mm0 hx, i13hw_mm00 hx, i8hw_0m00m hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_00m0m h0, i13hpl_rho_00mm h0,
    i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S111k0 i8L4Q111k0_0 i8L4Q111k0_1 i8L4Q111k0_2 i8L4Q111k0_3 i8L4Q111k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽111k0⁾`. -/
noncomputable def i8L4R111k0 (x : ℝ) : ℝ :=
  x * (i8L4Q111k0_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q111k0_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q111k0_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q111k0_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q111k0_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R111k0 : Tendsto i8L4R111k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q111k0_0 (v 0) (v 6) (v 18) (v 20) (v 24) (v 43) (v 57) (v 66))
      (by
      unfold i8L4Q111k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q111k0_1 (v 0) (v 6) (v 18) (v 20) (v 24) (v 43) (v 57) (v 66))
      (by
      unfold i8L4Q111k0_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q111k0_2 (v 0) (v 6) (v 18) (v 20) (v 24) (v 43) (v 57) (v 66))
      (by
      unfold i8L4Q111k0_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q111k0_0 x (i13Rho [zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q111k0_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q111k0_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R111k0
  unfold i8L4Q111k0_3 i8L4Q111k0_4
  ring

/-- The singular part of `Ψ₄⁽111k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S111k1 (x : ℝ) : ℝ :=
    17 / 8 - 3 / 4 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽111k1⁾`. -/
noncomputable def i8L4Q111k1_0 (x r_000mm r_00m r_00m0m r_00mm r_0m r_0mm r_m : ℝ) : ℝ :=
    1 / 4 + x ^ 2 - r_00mm - 5 / 16 * x ^ 3 - r_0mm / 2 + r_00mm * x ^ 4 + r_00m * x ^ 2 / 2 +
      r_m * x ^ 4 / 2 + r_0m ^ 2 * x ^ 3 / 2 + 2 * r_0m * x + 2 * r_0mm * x ^ 2 +
      4 * r_000mm * x ^ 2 + 4 * r_00m0m * x ^ 2 - 7 / 4 * r_m * x ^ 3 - r_0m * x ^ 3 / 2 -
      r_0m * x ^ 5 / 2 - r_0mm * x ^ 4 / 2 - r_m * x ^ 2 / 2 - r_0m ^ 2 * x ^ 7 / 2 -
      r_0m * x ^ 2 / 4 - r_m ^ 2 * x ^ 7 / 8 + r_0m * x ^ 4 / 4 + r_m * x ^ 5 / 4 +
      r_m ^ 2 * x ^ 3 / 8 + 3 / 2 * r_m * x + r_0m * r_m * x ^ 3 / 2 + r_0m * r_m * x ^ 7 / 2 -
      r_0m * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽111k1⁾`. -/
noncomputable def i8L4Q111k1_1 (_x _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽111k1⁾`. -/
noncomputable def i8L4Q111k1_2 (_x _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽111k1⁾`. -/
noncomputable def i8L4Q111k1_3 (_x _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽111k1⁾`. -/
noncomputable def i8L4Q111k1_4 (_x _r_000mm _r_00m _r_00m0m _r_00mm _r_0m _r_0mm _r_m : ℝ) : ℝ :=
    0

theorem i8L4_111k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s111k1 x = i8L4S111k1 x + x * (i8L4Q111k1_0 x (i13Rho [zero, zero, zero, negOne, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [negOne] x) + Real.log x * i8L4Q111k1_1 x (i13Rho [zero, zero, zero, negOne, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q111k1_2 x (i13Rho [zero, zero, zero, negOne,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q111k1_3 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q111k1_4 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x)) :=
      by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s111k1 i8Psi4s111k1N0 i8Psi4s111k1N1 i8Psi4s111k1N2 i8Psi4s111k1N3 i8Psi4s111k1N4
    i8Psi4s111k1W
  simp only [hpl_zero, i13hw_0m0m hx, i13hw_m0m hx, i13hw_mm hx]
  simp only [i13hpl_rho_000mm h0, i13hpl_rho_00m h0, i13hpl_rho_00m0m h0, i13hpl_rho_00mm h0,
    i13hpl_rho_0m h0, i13hpl_rho_0mm h0, i13hpl_rho_m h0]
  unfold i8L4S111k1 i8L4Q111k1_0 i8L4Q111k1_1 i8L4Q111k1_2 i8L4Q111k1_3 i8L4Q111k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽111k1⁾`. -/
noncomputable def i8L4R111k1 (x : ℝ) : ℝ :=
  x * (i8L4Q111k1_0 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q111k1_1 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q111k1_2 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q111k1_3 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q111k1_4 x (i13Rho [zero, zero, zero, negOne, negOne] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne, zero, negOne] x) (i13Rho [zero, zero, negOne,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R111k1 : Tendsto i8L4R111k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q111k1_0 (v 0) (v 8) (v 18) (v 20) (v 24) (v 43) (v 57) (v 66))
      (by
      unfold i8L4Q111k1_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q111k1_0 x (i13Rho [zero, zero,
    zero, negOne, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero,
    negOne] x) (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R111k1
  unfold i8L4Q111k1_1 i8L4Q111k1_2 i8L4Q111k1_3 i8L4Q111k1_4
  ring

/-- The singular part of `Ψ₄⁽112⁾` at `ξ = 0`. -/
noncomputable def i8L4S112 (x : ℝ) : ℝ :=
    (-1 - Real.log x - Real.log x ^ 2 / 2 + x / 8 - x * Real.log x ^ 3 / 24) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽112⁾`. -/
noncomputable def i8L4Q112_0 (x r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -29 / 16 - 3 / 16 * r_m - r_0m / 8 - x ^ 2 / 16 + x ^ 3 / 16 + r_00m * x ^ 2 / 2 -
      2 * r_0000m * x ^ 2 - 3 / 16 * r_m * x ^ 4 + r_0m * x ^ 4 / 8 + 3 / 8 * r_m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽112⁾`. -/
noncomputable def i8L4Q112_1 (x _r_0000m r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    2 - 3 / 16 * x - r_0m / 4 - r_m / 4 - x ^ 3 / 16 + 2 * r_000m * x ^ 2 - r_0m * x ^ 2 / 2 -
      r_0m * x ^ 4 / 4 + r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽112⁾`. -/
noncomputable def i8L4Q112_2 (x _r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -7 / 8 - r_0m / 4 - r_m / 8 + x ^ 2 / 8 + x / 16 - r_00m * x ^ 2 - r_m * x ^ 4 / 8 +
      r_0m * x ^ 4 / 4 + r_m * x ^ 2 / 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽112⁾`. -/
noncomputable def i8L4Q112_3 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽112⁾`. -/
noncomputable def i8L4Q112_4 (_x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_112_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s112 x = i8L4S112 x + x * (i8L4Q112_0 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x * i8L4Q112_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q112_2 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q112_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)
      + Real.log x ^ 4 * i8L4Q112_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s112 i8Psi4s112N0 i8Psi4s112N1 i8Psi4s112N2 i8Psi4s112N3 i8Psi4s112N4 i8Psi4s112W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_000m0 hx, i13hw_00m0 hx, i13hw_00m00 hx, i13hw_0m0
    hx, i13hw_0m00 hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S112 i8L4Q112_0 i8L4Q112_1 i8L4Q112_2 i8L4Q112_3 i8L4Q112_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽112⁾`. -/
noncomputable def i8L4R112 (x : ℝ) : ℝ :=
  x * (i8L4Q112_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q112_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q112_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q112_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q112_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R112 : Tendsto i8L4R112 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q112_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q112_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q112_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q112_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q112_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q112_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q112_0 x (i13Rho [zero, zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q112_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q112_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R112
  unfold i8L4Q112_3 i8L4Q112_4
  ring

/-- The singular part of `Ψ₄⁽113⁾` at `ξ = 0`. -/
noncomputable def i8L4S113 (x : ℝ) : ℝ :=
    4 - 2 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽113⁾`. -/
noncomputable def i8L4Q113_0 (x r_001 r_01 r_1 : ℝ) : ℝ :=
    -2 + x ^ 3 / 2 - x ^ 2 - 5 / 2 * x + r_1 * x ^ 4 - r_1 * x ^ 2 - 4 * r_001 * x ^ 2 -
      4 * r_1 * x ^ 3 + 4 * r_1 * x + 6 * r_01 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽113⁾`. -/
noncomputable def i8L4Q113_1 (x _r_001 r_01 r_1 : ℝ) : ℝ :=
    2 + x - x ^ 3 - 6 * r_1 * x ^ 2 - 2 * r_1 * x ^ 4 + 4 * r_01 * x ^ 2 + 4 * r_1 * x +
      4 * r_1 * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽113⁾`. -/
noncomputable def i8L4Q113_2 (_x _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽113⁾`. -/
noncomputable def i8L4Q113_3 (_x _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽113⁾`. -/
noncomputable def i8L4Q113_4 (_x _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_113_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s113 x = i8L4S113 x + x * (i8L4Q113_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one]
      x) (i13Rho [one] x) + Real.log x * i8L4Q113_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q113_2 x (i13Rho [zero, zero, one] x) (i13Rho
      [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q113_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
      [one] x) + Real.log x ^ 4 * i8L4Q113_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s113 i8Psi4s113N0 i8Psi4s113N1 i8Psi4s113N2 i8Psi4s113N3 i8Psi4s113N4 i8Psi4s113W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S113 i8L4Q113_0 i8L4Q113_1 i8L4Q113_2 i8L4Q113_3 i8L4Q113_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽113⁾`. -/
noncomputable def i8L4R113 (x : ℝ) : ℝ :=
  x * (i8L4Q113_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q113_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q113_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one]
    x) + Real.log x ^ 3 * i8L4Q113_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
    [one] x) + Real.log x ^ 4 * i8L4Q113_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x)
    (i13Rho [one] x))

theorem tendsto_i8L4R113 : Tendsto i8L4R113 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q113_0 (v 0) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q113_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q113_1 (v 0) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q113_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q113_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q113_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R113
  unfold i8L4Q113_2 i8L4Q113_3 i8L4Q113_4
  ring

/-- The singular part of `Ψ₄⁽114k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S114k0 (x : ℝ) : ℝ :=
    -11 / 4 + Real.log x / 2 + Real.log x ^ 2 / 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽114k0⁾`. -/
noncomputable def i8L4Q114k0_0 (x r_001 r_001m r_00m1 r_01 r_01m r_0m _r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ
    :=
    1 / 2 + x - r_01m - x ^ 2 / 4 - x ^ 3 / 8 + x ^ 5 / 8 + r_001 * x ^ 2 + r_01m * x ^ 4 +
      r_0m * x ^ 2 / 2 + r_m * x ^ 3 / 2 - r_01 * x ^ 2 - r_m * x - r_m * x ^ 2 -
      4 * r_001m * x ^ 2 - 2 * r_1 * x + 4 * r_00m1 * x ^ 2 - r_1 * x ^ 3 / 2 -
      r_1 * x ^ 5 / 2 - r_m * x ^ 5 / 2 - r_m * x ^ 6 / 4 + r_1 * x ^ 6 / 4 + r_m * x ^ 4 / 4 +
      11 / 4 * r_1 * x ^ 2 + r_1 * r_m * x ^ 5 - r_1 * r_m * x ^ 3 / 2 - r_1 * r_m * x ^ 7 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽114k0⁾`. -/
noncomputable def i8L4Q114k0_1 (x _r_001 _r_001m _r_00m1 r_01 _r_01m _r_0m r_0m1 r_1 _r_m r_m1 : ℝ)
    : ℝ :=
    -1 / 2 - r_m1 - x / 4 + x ^ 3 / 4 + r_1 * x ^ 3 + r_m1 * x ^ 4 + r_1 * x ^ 2 / 2 -
      r_01 * x ^ 2 - r_1 * x - 4 * r_0m1 * x ^ 2 - r_1 * x ^ 4 / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽114k0⁾`. -/
noncomputable def i8L4Q114k0_2 (_x _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽114k0⁾`. -/
noncomputable def i8L4Q114k0_3 (_x _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽114k0⁾`. -/
noncomputable def i8L4Q114k0_4 (_x _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1
    : ℝ) : ℝ :=
    0

theorem i8L4_114k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s114k0 x = i8L4S114k0 x + x * (i8L4Q114k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q114k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 2 * i8L4Q114k0_2 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q114k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 4 * i8L4Q114k0_4 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s114k0 i8Psi4s114k0N0 i8Psi4s114k0N1 i8Psi4s114k0N2 i8Psi4s114k0N3 i8Psi4s114k0N4
    i8Psi4s114k0W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_0m10 hx, i13hw_10 hx, i13hw_1m hx, i13hw_m01
    hx, i13hw_m10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_001m h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0,
    i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0]
  unfold i8L4S114k0 i8L4Q114k0_0 i8L4Q114k0_1 i8L4Q114k0_2 i8L4Q114k0_3 i8L4Q114k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽114k0⁾`. -/
noncomputable def i8L4R114k0 (x : ℝ) : ℝ :=
  x * (i8L4Q114k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x * i8L4Q114k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q114k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q114k0_3 x (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q114k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x))

theorem tendsto_i8L4R114k0 : Tendsto i8L4R114k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q114k0_0 (v 0) (v 9) (v 15) (v 21) (v 27) (v 36) (v 43) (v 49)
      (v 65) (v 66) (v 67)) (by
      unfold i8L4Q114k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q114k0_1 (v 0) (v 9) (v 15) (v 21) (v 27) (v 36) (v 43) (v 49)
      (v 65) (v 66) (v 67)) (by
      unfold i8L4Q114k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q114k0_0 x (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q114k0_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R114k0
  unfold i8L4Q114k0_2 i8L4Q114k0_3 i8L4Q114k0_4
  ring

/-- The singular part of `Ψ₄⁽114k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S114k1 (x : ℝ) : ℝ :=
    -3 / 4 + Real.log x ^ 2 / 2 - Real.log x / 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽114k1⁾`. -/
noncomputable def i8L4Q114k1_0 (x r_001m r_00m r_01m r_0m _r_1 r_m _r_m1 : ℝ) : ℝ :=
    -1 / 2 + r_01m - x ^ 3 / 8 + x ^ 2 / 4 + 9 / 8 * x + r_0m * x ^ 2 / 2 - r_00m * x ^ 2 -
      r_01m * x ^ 4 - r_m * x - r_m * x ^ 3 + 8 * r_001m * x ^ 2 - 7 / 4 * r_m * x ^ 2 -
      r_m * x ^ 4 / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽114k1⁾`. -/
noncomputable def i8L4Q114k1_1 (x _r_001m _r_00m r_01m r_0m r_1 r_m r_m1 : ℝ) : ℝ :=
    1 / 2 + r_m1 - x ^ 5 / 4 + x ^ 3 / 4 + r_0m * x ^ 2 + r_1 * x ^ 5 + r_m * x ^ 3 +
      r_m * x ^ 5 + r_1 * x ^ 2 / 2 + r_m * x ^ 4 / 2 + r_m * x ^ 6 / 2 - r_1 * x -
      r_m * x ^ 2 - r_m1 * x ^ 4 - 4 * r_01m * x ^ 2 - 2 * r_m * x - r_1 * x ^ 6 / 2 +
      r_1 * r_m * x ^ 7 - r_1 * r_m * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽114k1⁾`. -/
noncomputable def i8L4Q114k1_2 (_x _r_001m _r_00m _r_01m _r_0m _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽114k1⁾`. -/
noncomputable def i8L4Q114k1_3 (_x _r_001m _r_00m _r_01m _r_0m _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽114k1⁾`. -/
noncomputable def i8L4Q114k1_4 (_x _r_001m _r_00m _r_01m _r_0m _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_114k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s114k1 x = i8L4S114k1 x + x * (i8L4Q114k1_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q114k1_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q114k1_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q114k1_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q114k1_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s114k1 i8Psi4s114k1N0 i8Psi4s114k1N1 i8Psi4s114k1N2 i8Psi4s114k1N3 i8Psi4s114k1N4
    i8Psi4s114k1W
  simp only [hpl_zero, i13hw_00, i13hw_010m hx, i13hw_01m0 hx, i13hw_0m0 hx, i13hw_10m hx, i13hw_1m0
    hx, i13hw_m0 hx]
  simp only [i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0,
    i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S114k1 i8L4Q114k1_0 i8L4Q114k1_1 i8L4Q114k1_2 i8L4Q114k1_3 i8L4Q114k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽114k1⁾`. -/
noncomputable def i8L4R114k1 (x : ℝ) : ℝ :=
  x * (i8L4Q114k1_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x * i8L4Q114k1_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one]
    x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q114k1_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q114k1_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q114k1_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R114k1 : Tendsto i8L4R114k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q114k1_0 (v 0) (v 15) (v 18) (v 36) (v 43) (v 65) (v 66) (v 67))
      (by
      unfold i8L4Q114k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q114k1_1 (v 0) (v 15) (v 18) (v 36) (v 43) (v 65) (v 66) (v 67))
      (by
      unfold i8L4Q114k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q114k1_0 x (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q114k1_1 x (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R114k1
  unfold i8L4Q114k1_2 i8L4Q114k1_3 i8L4Q114k1_4
  ring

/-- The singular part of `Ψ₄⁽115k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S115k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽115k0⁾`. -/
noncomputable def i8L4Q115k0_0 (x r_001 r_001m r_00m1 r_00mm1 r_01 r_01m r_01mm r_0m r_0m01m r_0m1
    r_0m1m r_0mm1 r_1 r_m r_m1 _r_mm1 : ℝ) : ℝ :=
    1 + x ^ 3 - x ^ 4 - 4 * r_01mm - 2 * r_0m1m - 2 * r_0mm1 - 9 / 4 * x ^ 2 - x / 2 +
      3 / 8 * x ^ 5 + r_01m * x ^ 4 + r_01m * x ^ 6 + r_0m1 * x ^ 2 + r_01 * x ^ 2 / 2 +
      r_m * x ^ 5 / 2 - r_01m * x ^ 2 - r_m * x ^ 3 - 16 * r_00mm1 * x ^ 2 - 10 * r_1 * x ^ 3 -
      2 * r_00m1 * x ^ 2 - 2 * r_01m * x ^ 3 - 2 * r_01m * x ^ 5 - 2 * r_0m * x ^ 2 +
      2 * r_001 * x ^ 2 + 2 * r_001m * x ^ 2 + 2 * r_0m1m * x ^ 4 + 2 * r_0mm1 * x ^ 4 +
      4 * r_01m * x + 4 * r_01mm * x ^ 4 + 7 * r_1 * x ^ 2 + 8 * r_0m01m * x ^ 2 +
      8 * r_m1 * x ^ 2 - 3 / 2 * r_1 * x ^ 5 - 3 / 4 * r_m * x ^ 6 + r_1 * x ^ 6 / 4 +
      17 / 4 * r_1 * x ^ 4 + 17 / 4 * r_m * x ^ 2 - 2 * r_01m * r_m * x ^ 7 +
      2 * r_01m * r_m * x ^ 3 + 2 * r_1 * r_m * x ^ 4 + 2 * r_1 * r_m * x ^ 6 -
      7 / 2 * r_1 * r_m * x ^ 5 - r_1 * r_m * x ^ 7 / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽115k0⁾`. -/
noncomputable def i8L4Q115k0_1 (x _r_001 _r_001m _r_00m1 _r_00mm1 r_01 _r_01m _r_01mm _r_0m _r_0m01m
    r_0m1 _r_0m1m r_0mm1 r_1 _r_m r_m1 r_mm1 : ℝ) : ℝ :=
    -1 + x + 2 * r_mm1 + x ^ 3 / 4 + r_m1 * x ^ 4 - r_m1 * x ^ 2 - 2 * r_01 * x ^ 2 -
      2 * r_m1 * x ^ 3 - 2 * r_mm1 * x ^ 4 + 2 * r_0m1 * x ^ 2 + 2 * r_m1 * x + 3 * r_1 * x ^ 3 +
      8 * r_0mm1 * x ^ 2 - 5 / 2 * r_1 * x ^ 2 - r_1 * x ^ 4 / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽115k0⁾`. -/
noncomputable def i8L4Q115k0_2 (_x _r_001 _r_001m _r_00m1 _r_00mm1 _r_01 _r_01m _r_01mm _r_0m
    _r_0m01m _r_0m1 _r_0m1m _r_0mm1 _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽115k0⁾`. -/
noncomputable def i8L4Q115k0_3 (_x _r_001 _r_001m _r_00m1 _r_00mm1 _r_01 _r_01m _r_01mm _r_0m
    _r_0m01m _r_0m1 _r_0m1m _r_0mm1 _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽115k0⁾`. -/
noncomputable def i8L4Q115k0_4 (_x _r_001 _r_001m _r_00m1 _r_00mm1 _r_01 _r_01m _r_01mm _r_0m
    _r_0m01m _r_0m1 _r_0m1m _r_0mm1 _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

theorem i8L4_115k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s115k0 x = i8L4S115k0 x + x * (i8L4Q115k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x * i8L4Q115k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x ^ 2 * i8L4Q115k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x ^ 3 * i8L4Q115k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x ^ 4 * i8L4Q115k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s115k0 i8Psi4s115k0N0 i8Psi4s115k0N1 i8Psi4s115k0N2 i8Psi4s115k0N3 i8Psi4s115k0N4
    i8Psi4s115k0W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0m10 hx, i13hw_0mm10 hx, i13hw_10 hx, i13hw_1m hx,
    i13hw_m01 hx, i13hw_m01m hx, i13hw_m10 hx, i13hw_mm01 hx, i13hw_mm10 hx, i8hw_m0m1 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_001m h0, i13hpl_rho_00m1 h0, i8hpl_rho_00mm1 h0,
    i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_01mm h0, i13hpl_rho_0m h0, i8hpl_rho_0m01m h0,
    i13hpl_rho_0m1 h0, i13hpl_rho_0m1m h0, i13hpl_rho_0mm1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0, i8hpl_rho_mm1 h0]
  unfold i8L4S115k0 i8L4Q115k0_0 i8L4Q115k0_1 i8L4Q115k0_2 i8L4Q115k0_3 i8L4Q115k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽115k0⁾`. -/
noncomputable def i8L4R115k0 (x : ℝ) : ℝ :=
  x * (i8L4Q115k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
    x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x * i8L4Q115k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 2 * i8L4Q115k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 3 * i8L4Q115k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 4 * i8L4Q115k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x))

theorem tendsto_i8L4R115k0 : Tendsto i8L4R115k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q115k0_0 (v 0) (v 9) (v 15) (v 21) (v 25) (v 27) (v 36) (v 40)
      (v 43) (v 46) (v 49) (v 54) (v 59) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q115k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q115k0_1 (v 0) (v 9) (v 15) (v 21) (v 25) (v 27) (v 36) (v 40)
      (v 43) (v 46) (v 49) (v 54) (v 59) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q115k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q115k0_0 x (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, zero, negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho
    [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)
    (i13Rho [negOne, negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q115k0_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
      negOne, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, negOne] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R115k0
  unfold i8L4Q115k0_2 i8L4Q115k0_3 i8L4Q115k0_4
  ring

/-- The regular parts of group 10. -/
noncomputable def i8L4RG10 (x : ℝ) : ℝ :=
  i8L4R108k3 x + i8L4R108k4 x + i8L4R109 x + i8L4R110 x + i8L4R111k0 x + i8L4R111k1 x +
    i8L4R112 x + i8L4R113 x + i8L4R114k0 x + i8L4R114k1 x + i8L4R115k0 x

theorem tendsto_i8L4RG10 : Tendsto i8L4RG10 (𝓝[>] 0) (𝓝 0) := by
  have H := ((((((((((tendsto_i8L4R108k3.add tendsto_i8L4R108k4).add tendsto_i8L4R109).add
    tendsto_i8L4R110).add tendsto_i8L4R111k0).add tendsto_i8L4R111k1).add tendsto_i8L4R112).add
    tendsto_i8L4R113).add tendsto_i8L4R114k0).add tendsto_i8L4R114k1).add tendsto_i8L4R115k0)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
