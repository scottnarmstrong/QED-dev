/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L11
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 12

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_120k1_eq`, `QED.ThreeLoopD.tendsto_i8L4RG12` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽120k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S120k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽120k1⁾`. -/
noncomputable def i8L4Q120k1_0 (x r_0011m r_001m r_00m r_00m1 r_00m11 r_01 r_011 r_011m r_01m r_0m
    r_0m01 r_0m011 r_0m1 r_0m101 r_0m11 r_1 r_m r_m1 : ℝ) : ℝ :=
    1 + x + x ^ 4 + x ^ 5 / 2 - 2 * r_0m11 + 2 * r_011m + 3 * x ^ 2 - x ^ 7 / 16 +
      17 / 16 * x ^ 3 + r_01m * x ^ 2 + r_0m * x ^ 7 + r_0m1 * x ^ 4 + r_1 * x ^ 5 +
      r_1 ^ 2 * x ^ 8 + r_1 * x ^ 7 / 2 + r_m1 * x ^ 4 / 2 - r_0m * x ^ 2 - r_0m1 * x ^ 6 -
      r_1 ^ 2 * x ^ 4 - 16 * r_00m11 * x ^ 2 - 8 * r_011 * x ^ 3 - 8 * r_0m011 * x ^ 2 -
      8 * r_0m101 * x ^ 2 - 7 * r_m * x ^ 2 - 4 * r_00m1 * x ^ 2 - 2 * r_001m * x ^ 2 -
      2 * r_011m * x ^ 4 - 2 * r_0m01 * x ^ 2 - 2 * r_0m1 * x ^ 5 - 2 * r_m * x ^ 3 +
      2 * r_00m * x ^ 2 + 2 * r_01 * x ^ 3 + 2 * r_011 * x ^ 4 + 2 * r_0m * x ^ 3 +
      2 * r_0m * x ^ 5 + 2 * r_0m1 * x ^ 2 + 2 * r_0m11 * x ^ 4 + 2 * r_m1 * x +
      2 * r_m1 * x ^ 3 + 4 * r_0m1 * x + 6 * r_0m1 * x ^ 3 + 16 * r_0011m * x ^ 2 -
      11 / 2 * r_1 * x ^ 2 - 9 / 2 * r_m1 * x ^ 2 - 7 / 4 * r_1 * x ^ 4 - 3 / 2 * r_m * x ^ 5 -
      r_1 * x ^ 8 / 4 - r_m * x ^ 4 / 4 - r_m * x ^ 6 / 4 - r_1 ^ 2 * x ^ 9 / 4 +
      r_0m * x ^ 4 / 4 + r_0m * x ^ 8 / 4 + r_1 ^ 2 * x ^ 5 / 4 + 3 / 2 * r_01 * x ^ 4 +
      3 / 2 * r_0m * x ^ 6 + 3 / 2 * r_1 * x ^ 6 + 9 / 2 * r_1 * x ^ 3 + r_0m * r_1 * x ^ 7 +
      r_0m * r_1 * x ^ 9 + r_0m * r_1 ^ 2 * x ^ 10 - r_0m * r_1 ^ 2 * x ^ 6 -
      8 * r_011 * r_0m * x ^ 5 - 4 * r_0m * r_1 * x ^ 4 - 2 * r_0m * r_1 * x ^ 5 -
      2 * r_0m1 * r_1 * x ^ 7 - 2 * r_1 * r_m * x ^ 4 - 2 * r_1 * r_m * x ^ 6 +
      2 * r_01 * r_0m * x ^ 5 + 2 * r_0m * r_1 * x ^ 6 + 2 * r_0m * r_1 * x ^ 8 +
      2 * r_0m1 * r_1 * x ^ 3 + 8 * r_01 * r_0m1 * x ^ 5 - r_1 * r_m * x ^ 7 / 2 +
      9 / 2 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽120k1⁾`. -/
noncomputable def i8L4Q120k1_1 (_x _r_0011m _r_001m _r_00m _r_00m1 _r_00m11 _r_01 _r_011 _r_011m
    _r_01m _r_0m _r_0m01 _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽120k1⁾`. -/
noncomputable def i8L4Q120k1_2 (_x _r_0011m _r_001m _r_00m _r_00m1 _r_00m11 _r_01 _r_011 _r_011m
    _r_01m _r_0m _r_0m01 _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽120k1⁾`. -/
noncomputable def i8L4Q120k1_3 (_x _r_0011m _r_001m _r_00m _r_00m1 _r_00m11 _r_01 _r_011 _r_011m
    _r_01m _r_0m _r_0m01 _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽120k1⁾`. -/
noncomputable def i8L4Q120k1_4 (_x _r_0011m _r_001m _r_00m _r_00m1 _r_00m11 _r_01 _r_011 _r_011m
    _r_01m _r_0m _r_0m01 _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_120k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s120k1 x = i8L4S120k1 x + x * (i8L4Q120k1_0 x (i13Rho [zero, zero, one, one, negOne] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one]
      x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q120k1_1 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q120k1_2 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q120k1_3 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q120k1_4 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s120k1 i8Psi4s120k1N0 i8Psi4s120k1N1 i8Psi4s120k1N2 i8Psi4s120k1N3 i8Psi4s120k1N4
    i8Psi4s120k1W
  simp only [i13hw_010m hx, i13hw_101m hx, i13hw_10m hx, i13hw_110m hx, i13hw_1m hx,
    i8hw_0110m hx]
  simp only [i8hpl_rho_0011m h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0,
    i8hpl_rho_00m11 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_011m h0, i13hpl_rho_01m h0,
    i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m011 h0, i13hpl_rho_0m1 h0, i8hpl_rho_0m101
    h0, i13hpl_rho_0m11 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S120k1 i8L4Q120k1_0 i8L4Q120k1_1 i8L4Q120k1_2 i8L4Q120k1_3 i8L4Q120k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽120k1⁾`. -/
noncomputable def i8L4R120k1 (x : ℝ) : ℝ :=
  x * (i8L4Q120k1_0 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
    negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne]
    x) (i13Rho [negOne, one] x) + Real.log x * i8L4Q120k1_1 x (i13Rho [zero, zero, one, one, negOne]
    x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne,
    one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q120k1_2 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
    [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q120k1_3 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
    [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q120k1_4 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
    [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R120k1 : Tendsto i8L4R120k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q120k1_0 (v 0) (v 14) (v 15) (v 18) (v 21) (v 22) (v 27) (v 29)
      (v 33) (v 36) (v 43) (v 44) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q120k1_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q120k1_0 x (i13Rho [zero, zero,
    one, one, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
    zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
    x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R120k1
  unfold i8L4Q120k1_1 i8L4Q120k1_2 i8L4Q120k1_3 i8L4Q120k1_4
  ring

/-- The singular part of `Ψ₄⁽121⁾` at `ξ = 0`. -/
noncomputable def i8L4S121 (x : ℝ) : ℝ :=
    (10 + Real.log x ^ 3 + 5 * Real.log x ^ 2 + 10 * Real.log x - x * Real.log x ^ 4 / 4 +
      2 / 3 * x * Real.log x ^ 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽121⁾`. -/
noncomputable def i8L4Q121_0 (x : ℝ) : ℝ :=
    -2 - 7 / 8 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽121⁾`. -/
noncomputable def i8L4Q121_1 (x : ℝ) : ℝ :=
    2 + 7 / 4 * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽121⁾`. -/
noncomputable def i8L4Q121_2 (x : ℝ) : ℝ :=
    -1 - 7 / 4 * x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽121⁾`. -/
noncomputable def i8L4Q121_3 (x : ℝ) : ℝ :=
    1 + x / 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽121⁾`. -/
noncomputable def i8L4Q121_4 (_x : ℝ) : ℝ :=
    0

theorem i8L4_121_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s121 x = i8L4S121 x + x * (i8L4Q121_0 x + Real.log x * i8L4Q121_1 x +
      Real.log x ^ 2 * i8L4Q121_2 x + Real.log x ^ 3 * i8L4Q121_3 x +
      Real.log x ^ 4 * i8L4Q121_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s121 i8Psi4s121N0 i8Psi4s121N1 i8Psi4s121N2 i8Psi4s121N3 i8Psi4s121N4 i8Psi4s121W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000]

  unfold i8L4S121 i8L4Q121_0 i8L4Q121_1 i8L4Q121_2 i8L4Q121_3 i8L4Q121_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽121⁾`. -/
noncomputable def i8L4R121 (x : ℝ) : ℝ :=
  x * (i8L4Q121_0 x + Real.log x * i8L4Q121_1 x + Real.log x ^ 2 * i8L4Q121_2 x +
    Real.log x ^ 3 * i8L4Q121_3 x + Real.log x ^ 4 * i8L4Q121_4 x)

theorem tendsto_i8L4R121 : Tendsto i8L4R121 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q121_0 (v 0)) (by
      unfold i8L4Q121_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q121_1 (v 0)) (by
      unfold i8L4Q121_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q121_2 (v 0)) (by
      unfold i8L4Q121_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q121_3 (v 0)) (by
      unfold i8L4Q121_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q121_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q121_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q121_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q121_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R121
  unfold i8L4Q121_4
  ring

/-- The singular part of `Ψ₄⁽122⁾` at `ξ = 0`. -/
noncomputable def i8L4S122 (x : ℝ) : ℝ :=
    (-10 - Real.log x ^ 3 - 10 * Real.log x - 5 * Real.log x ^ 2 - 185 / 16 * x -
      x * Real.log x ^ 3 / 3 + 3 / 8 * x * Real.log x ^ 4) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽122⁾`. -/
noncomputable def i8L4Q122_0 (x r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    -19 / 8 - 41 / 8 * x ^ 2 - 7 / 8 * r_m - 7 / 16 * x ^ 3 + 19 / 4 * x - 12 * r_m * x +
      10 * r_000m * x ^ 2 + 12 * r_m * x ^ 3 + 7 / 8 * r_m * x ^ 4 + 41 / 2 * r_0m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽122⁾`. -/
noncomputable def i8L4Q122_1 (x _r_000m r_00m _r_0m r_m : ℝ) : ℝ :=
    13 / 4 - 7 / 4 * r_m + 7 / 8 * x ^ 3 + 13 / 8 * x + 17 / 4 * x ^ 2 - 12 * r_m * x -
      12 * r_m * x ^ 3 - 10 * r_00m * x ^ 2 - 41 / 2 * r_m * x ^ 2 - 7 / 4 * r_m * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽122⁾`. -/
noncomputable def i8L4Q122_2 (x _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    -3 / 4 - 7 / 4 * r_m - 7 / 8 * x ^ 3 - 5 / 4 * x ^ 2 + 7 / 2 * x - 6 * r_m * x +
      5 * r_0m * x ^ 2 + 6 * r_m * x ^ 3 + 7 / 4 * r_m * x ^ 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽122⁾`. -/
noncomputable def i8L4Q122_3 (x _r_000m _r_00m _r_0m r_m : ℝ) : ℝ :=
    -1 / 2 + x ^ 2 / 2 - r_m / 2 - x / 4 + x ^ 3 / 4 - 3 * r_m * x ^ 2 - 2 * r_m * x -
      2 * r_m * x ^ 3 - r_m * x ^ 4 / 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽122⁾`. -/
noncomputable def i8L4Q122_4 (_x _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    0

theorem i8L4_122_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s122 x = i8L4S122 x + x * (i8L4Q122_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q122_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q122_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q122_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q122_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s122 i8Psi4s122N0 i8Psi4s122N1 i8Psi4s122N2 i8Psi4s122N3 i8Psi4s122N4 i8Psi4s122W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00m0 hx, i13hw_0m0 hx, i13hw_0m00 hx,
    i13hw_m0 hx, i13hw_m00 hx, i13hw_m000 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0, i13hpl_rho_m h0]
  unfold i8L4S122 i8L4Q122_0 i8L4Q122_1 i8L4Q122_2 i8L4Q122_3 i8L4Q122_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽122⁾`. -/
noncomputable def i8L4R122 (x : ℝ) : ℝ :=
  x * (i8L4Q122_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q122_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q122_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q122_3 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q122_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R122 : Tendsto i8L4R122 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q122_0 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q122_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q122_1 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q122_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q122_2 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q122_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q122_3 (v 0) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q122_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q122_0 x (i13Rho [zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
    [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q122_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q122_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q122_3 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R122
  unfold i8L4Q122_4
  ring

/-- The singular part of `Ψ₄⁽123⁾` at `ξ = 0`. -/
noncomputable def i8L4S123 (x : ℝ) : ℝ :=
    16 - 4 * Real.log x ^ 2 - 4 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽123⁾`. -/
noncomputable def i8L4Q123_0 (x r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -16 + 3 * x ^ 2 - 15 / 2 * x + 3 / 2 * x ^ 3 - 28 * r_001 * x ^ 2 - 19 * r_1 * x ^ 2 -
      8 * r_0001 * x ^ 2 + 3 * r_1 * x ^ 4 + 10 * r_01 * x ^ 2 + 16 * r_1 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽123⁾`. -/
noncomputable def i8L4Q123_1 (x _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    16 - x - 6 * x ^ 2 - 3 * x ^ 3 - 10 * r_1 * x ^ 2 - 6 * r_1 * x ^ 4 + 8 * r_001 * x ^ 2 +
      16 * r_1 * x + 28 * r_01 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽123⁾`. -/
noncomputable def i8L4Q123_2 (x _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    -6 + x ^ 3 - x + 4 * x ^ 2 - 10 * r_1 * x ^ 2 - 4 * r_01 * x ^ 2 + 2 * r_1 * x ^ 4 +
      4 * r_1 * x + 4 * r_1 * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽123⁾`. -/
noncomputable def i8L4Q123_3 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽123⁾`. -/
noncomputable def i8L4Q123_4 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_123_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s123 x = i8L4S123 x + x * (i8L4Q123_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q123_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q123_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q123_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q123_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s123 i8Psi4s123N0 i8Psi4s123N1 i8Psi4s123N2 i8Psi4s123N3 i8Psi4s123N4 i8Psi4s123W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_10 hx,
    i13hw_100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S123 i8L4Q123_0 i8L4Q123_1 i8L4Q123_2 i8L4Q123_3 i8L4Q123_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽123⁾`. -/
noncomputable def i8L4R123 (x : ℝ) : ℝ :=
  x * (i8L4Q123_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    one] x) (i13Rho [one] x) + Real.log x * i8L4Q123_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q123_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q123_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q123_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R123 : Tendsto i8L4R123 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q123_0 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q123_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q123_1 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q123_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q123_2 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q123_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q123_0 x (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q123_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q123_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R123
  unfold i8L4Q123_3 i8L4Q123_4
  ring

/-- The singular part of `Ψ₄⁽124k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S124k0 (x : ℝ) : ℝ :=
    -11 + 2 * Real.log x + 2 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽124k0⁾`. -/
noncomputable def i8L4Q124k0_0 (x r_001 r_001m r_00m1 r_01 r_01m r_0m _r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ
    :=
    2 + x ^ 5 / 2 - x ^ 2 - 4 * r_01m + 4 * x - x ^ 3 / 2 + r_1 * x ^ 6 + r_m * x ^ 4 -
      r_m * x ^ 6 - 16 * r_001m * x ^ 2 - 8 * r_1 * x - 4 * r_01 * x ^ 2 - 4 * r_m * x -
      4 * r_m * x ^ 2 - 2 * r_1 * x ^ 3 - 2 * r_1 * x ^ 5 - 2 * r_m * x ^ 5 + 2 * r_0m * x ^ 2 +
      2 * r_m * x ^ 3 + 4 * r_001 * x ^ 2 + 4 * r_01m * x ^ 4 + 11 * r_1 * x ^ 2 +
      16 * r_00m1 * x ^ 2 - 2 * r_1 * r_m * x ^ 3 - 2 * r_1 * r_m * x ^ 7 + 4 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽124k0⁾`. -/
noncomputable def i8L4Q124k0_1 (x _r_001 _r_001m _r_00m1 r_01 _r_01m _r_0m r_0m1 r_1 _r_m r_m1 : ℝ)
    : ℝ :=
    -2 + x ^ 3 - x - 4 * r_m1 - 16 * r_0m1 * x ^ 2 - 4 * r_01 * x ^ 2 - 4 * r_1 * x -
      2 * r_1 * x ^ 4 + 2 * r_1 * x ^ 2 + 4 * r_1 * x ^ 3 + 4 * r_m1 * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽124k0⁾`. -/
noncomputable def i8L4Q124k0_2 (_x _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽124k0⁾`. -/
noncomputable def i8L4Q124k0_3 (_x _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽124k0⁾`. -/
noncomputable def i8L4Q124k0_4 (_x _r_001 _r_001m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m _r_m1
    : ℝ) : ℝ :=
    0

theorem i8L4_124k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s124k0 x = i8L4S124k0 x + x * (i8L4Q124k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q124k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 2 * i8L4Q124k0_2 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q124k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 4 * i8L4Q124k0_4 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s124k0 i8Psi4s124k0N0 i8Psi4s124k0N1 i8Psi4s124k0N2 i8Psi4s124k0N3 i8Psi4s124k0N4
    i8Psi4s124k0W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_0m10 hx, i13hw_10 hx, i13hw_1m hx, i13hw_m01
    hx, i13hw_m10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_001m h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0,
    i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0]
  unfold i8L4S124k0 i8L4Q124k0_0 i8L4Q124k0_1 i8L4Q124k0_2 i8L4Q124k0_3 i8L4Q124k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽124k0⁾`. -/
noncomputable def i8L4R124k0 (x : ℝ) : ℝ :=
  x * (i8L4Q124k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x * i8L4Q124k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q124k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q124k0_3 x (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q124k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x))

theorem tendsto_i8L4R124k0 : Tendsto i8L4R124k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q124k0_0 (v 0) (v 9) (v 15) (v 21) (v 27) (v 36) (v 43) (v 49)
      (v 65) (v 66) (v 67)) (by
      unfold i8L4Q124k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q124k0_1 (v 0) (v 9) (v 15) (v 21) (v 27) (v 36) (v 43) (v 49)
      (v 65) (v 66) (v 67)) (by
      unfold i8L4Q124k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q124k0_0 x (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q124k0_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R124k0
  unfold i8L4Q124k0_2 i8L4Q124k0_3 i8L4Q124k0_4
  ring

/-- The singular part of `Ψ₄⁽124k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S124k1 (x : ℝ) : ℝ :=
    -3 - 2 * Real.log x + 2 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽124k1⁾`. -/
noncomputable def i8L4Q124k1_0 (x r_001m r_00m r_01m r_0m _r_1 r_m _r_m1 : ℝ) : ℝ :=
    -2 + x ^ 2 + 4 * r_01m - x ^ 3 / 2 + 9 / 2 * x - r_m * x ^ 4 - 7 * r_m * x ^ 2 -
      4 * r_00m * x ^ 2 - 4 * r_01m * x ^ 4 - 4 * r_m * x - 4 * r_m * x ^ 3 + 2 * r_0m * x ^ 2 +
      32 * r_001m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽124k1⁾`. -/
noncomputable def i8L4Q124k1_1 (x _r_001m _r_00m r_01m r_0m r_1 r_m r_m1 : ℝ) : ℝ :=
    2 + x ^ 3 - x ^ 5 + 4 * r_m1 - 16 * r_01m * x ^ 2 - 8 * r_m * x - 4 * r_1 * x -
      4 * r_m * x ^ 2 - 4 * r_m1 * x ^ 4 - 2 * r_1 * x ^ 6 + 2 * r_1 * x ^ 2 + 2 * r_m * x ^ 4 +
      2 * r_m * x ^ 6 + 4 * r_0m * x ^ 2 + 4 * r_1 * x ^ 5 + 4 * r_m * x ^ 3 + 4 * r_m * x ^ 5 -
      4 * r_1 * r_m * x ^ 3 + 4 * r_1 * r_m * x ^ 7

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽124k1⁾`. -/
noncomputable def i8L4Q124k1_2 (_x _r_001m _r_00m _r_01m _r_0m _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽124k1⁾`. -/
noncomputable def i8L4Q124k1_3 (_x _r_001m _r_00m _r_01m _r_0m _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽124k1⁾`. -/
noncomputable def i8L4Q124k1_4 (_x _r_001m _r_00m _r_01m _r_0m _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_124k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s124k1 x = i8L4S124k1 x + x * (i8L4Q124k1_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q124k1_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q124k1_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q124k1_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q124k1_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s124k1 i8Psi4s124k1N0 i8Psi4s124k1N1 i8Psi4s124k1N2 i8Psi4s124k1N3 i8Psi4s124k1N4
    i8Psi4s124k1W
  simp only [hpl_zero, i13hw_00, i13hw_010m hx, i13hw_01m0 hx, i13hw_0m0 hx, i13hw_10m hx, i13hw_1m0
    hx, i13hw_m0 hx]
  simp only [i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0,
    i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S124k1 i8L4Q124k1_0 i8L4Q124k1_1 i8L4Q124k1_2 i8L4Q124k1_3 i8L4Q124k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽124k1⁾`. -/
noncomputable def i8L4R124k1 (x : ℝ) : ℝ :=
  x * (i8L4Q124k1_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x * i8L4Q124k1_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one]
    x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q124k1_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q124k1_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q124k1_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R124k1 : Tendsto i8L4R124k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q124k1_0 (v 0) (v 15) (v 18) (v 36) (v 43) (v 65) (v 66) (v 67))
      (by
      unfold i8L4Q124k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q124k1_1 (v 0) (v 15) (v 18) (v 36) (v 43) (v 65) (v 66) (v 67))
      (by
      unfold i8L4Q124k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q124k1_0 x (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q124k1_1 x (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R124k1
  unfold i8L4Q124k1_2 i8L4Q124k1_3 i8L4Q124k1_4
  ring

/-- The singular part of `Ψ₄⁽125k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S125k0 (x : ℝ) : ℝ :=
    -21 / 2 - Real.log x ^ 2 + 3 * Real.log x + 2 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽125k0⁾`. -/
noncomputable def i8L4Q125k0_0 (x r_0001 r_001 r_00m1 r_01 r_01m r_0m01 r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ
    :=
    15 - 4 * r_00m1 - 4 * r_0m01 + 2 * r_01m + 2 * r_0m1 - 17 / 4 * x ^ 3 - 5 / 2 * x ^ 4 -
      x ^ 5 / 4 + 3 / 4 * x + 27 / 2 * x ^ 2 + r_1 * x ^ 4 + r_m * x ^ 6 / 2 - r_01 * x ^ 6 -
      32 * r_01 * x ^ 2 - 24 * r_00m1 * x ^ 2 - 21 * r_1 * x ^ 2 - 16 * r_00m1 * x -
      16 * r_00m1 * x ^ 3 - 16 * r_01m * x ^ 3 - 16 * r_0m01 * x - 16 * r_0m01 * x ^ 3 -
      16 * r_0m1 * x ^ 3 - 6 * r_01 * x ^ 3 - 6 * r_01 * x ^ 5 - 6 * r_1 * x -
      4 * r_00m1 * x ^ 4 - 4 * r_01 * x - 4 * r_0m01 * x ^ 4 - 4 * r_m * x ^ 3 -
      2 * r_01m * x ^ 4 - 2 * r_0m1 * x ^ 4 - 2 * r_m * x + 4 * r_001 * x ^ 2 + 6 * r_m * x ^ 5 +
      12 * r_0001 * x ^ 2 + 15 * r_01 * x ^ 4 + 16 * r_01m * x + 16 * r_0m1 * x +
      16 * r_m * x ^ 4 + 26 * r_1 * x ^ 3 - 33 / 2 * r_m * x ^ 2 - 16 * r_01 * r_m * x ^ 4 -
      2 * r_01 * r_m * x ^ 3 + 2 * r_01 * r_m * x ^ 7 + 16 * r_01 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽125k0⁾`. -/
noncomputable def i8L4Q125k0_1 (x _r_0001 r_001 _r_00m1 r_01 _r_01m _r_0m01 r_0m1 r_1 _r_m _r_m1 :
    ℝ) : ℝ :=
    -10 + x ^ 3 / 2 - 3 * x ^ 2 + 4 * r_0m1 + 5 / 2 * x - r_1 * x ^ 4 - 12 * r_001 * x ^ 2 -
      12 * r_1 * x ^ 3 - 4 * r_1 * x + 4 * r_0m1 * x ^ 4 + 10 * r_01 * x ^ 2 + 16 * r_0m1 * x +
      16 * r_0m1 * x ^ 3 + 17 * r_1 * x ^ 2 + 24 * r_0m1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽125k0⁾`. -/
noncomputable def i8L4Q125k0_2 (x _r_0001 _r_001 _r_00m1 r_01 _r_01m _r_0m01 _r_0m1 r_1 _r_m r_m1 :
    ℝ) : ℝ :=
    3 - 2 * r_m1 - x / 2 - x ^ 3 / 2 + r_1 * x ^ 4 - 12 * r_m1 * x ^ 2 - 8 * r_m1 * x -
      8 * r_m1 * x ^ 3 - 5 * r_1 * x ^ 2 - 2 * r_1 * x - 2 * r_m1 * x ^ 4 + 6 * r_01 * x ^ 2 +
      6 * r_1 * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽125k0⁾`. -/
noncomputable def i8L4Q125k0_3 (_x _r_0001 _r_001 _r_00m1 _r_01 _r_01m _r_0m01 _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽125k0⁾`. -/
noncomputable def i8L4Q125k0_4 (_x _r_0001 _r_001 _r_00m1 _r_01 _r_01m _r_0m01 _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_125k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s125k0 x = i8L4S125k0 x + x * (i8L4Q125k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q125k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q125k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q125k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q125k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s125k0 i8Psi4s125k0N0 i8Psi4s125k0N1 i8Psi4s125k0N2 i8Psi4s125k0N3 i8Psi4s125k0N4
    i8Psi4s125k0W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_10 hx,
    i13hw_100 hx, i13hw_m001 hx, i13hw_m01 hx, i13hw_m010 hx, i13hw_m100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0,
    i13hpl_rho_01m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0]
  unfold i8L4S125k0 i8L4Q125k0_0 i8L4Q125k0_1 i8L4Q125k0_2 i8L4Q125k0_3 i8L4Q125k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽125k0⁾`. -/
noncomputable def i8L4R125k0 (x : ℝ) : ℝ :=
  x * (i8L4Q125k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x * i8L4Q125k0_1 x (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q125k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q125k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q125k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R125k0 : Tendsto i8L4R125k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q125k0_0 (v 0) (v 3) (v 9) (v 21) (v 27) (v 36) (v 44) (v 49) (v
      65) (v 66) (v 67)) (by
      unfold i8L4Q125k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q125k0_1 (v 0) (v 3) (v 9) (v 21) (v 27) (v 36) (v 44) (v 49) (v
      65) (v 66) (v 67)) (by
      unfold i8L4Q125k0_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q125k0_2 (v 0) (v 3) (v 9) (v 21) (v 27) (v 36) (v 44) (v 49) (v
      65) (v 66) (v 67)) (by
      unfold i8L4Q125k0_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q125k0_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q125k0_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q125k0_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R125k0
  unfold i8L4Q125k0_3 i8L4Q125k0_4
  ring

/-- The singular part of `Ψ₄⁽125k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S125k1 (x : ℝ) : ℝ :=
    6 - 6 * Real.log x + 2 * Real.log x ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽125k1⁾`. -/
noncomputable def i8L4Q125k1_0 (x r_001 r_001m r_00m r_00m1 r_01 r_01m r_0m r_0m1 r_1 r_m r_m1 : ℝ)
    : ℝ :=
    -20 + x ^ 5 / 2 - 4 * r_001m - 4 * r_00m1 - 4 * r_01m - 4 * r_0m1 - 2 * x + 3 * x ^ 2 +
      7 * x ^ 4 - 15 / 2 * x ^ 3 + r_01 * x ^ 4 + r_1 * x ^ 6 - r_0m * x ^ 4 - r_m * x ^ 6 -
      64 * r_m1 * x ^ 2 - 36 * r_00m * x ^ 2 - 32 * r_01m * x - 32 * r_0m1 * x -
      28 * r_001 * x ^ 2 - 16 * r_001m * x - 16 * r_001m * x ^ 3 - 16 * r_00m1 * x -
      16 * r_00m1 * x ^ 3 - 15 * r_m * x ^ 5 - 6 * r_0m * x ^ 3 - 4 * r_001m * x ^ 4 -
      4 * r_00m1 * x ^ 4 - 2 * r_0m * x ^ 5 + 2 * r_01 * x ^ 3 + 4 * r_01m * x ^ 4 +
      4 * r_0m1 * x ^ 4 + 6 * r_01 * x ^ 5 + 8 * r_01 * x + 8 * r_0m * x + 9 * r_1 * x ^ 5 +
      13 * r_m * x ^ 3 + 28 * r_01 * x ^ 2 + 32 * r_01m * x ^ 3 + 32 * r_0m1 * x ^ 3 +
      36 * r_0m * x ^ 2 + 53 * r_1 * x ^ 3 - 97 / 2 * r_1 * x ^ 4 - 35 / 2 * r_m * x ^ 2 -
      31 / 2 * r_m * x ^ 4 - 29 / 2 * r_1 * x ^ 2 - r_1 * r_m * x ^ 3 - r_1 * r_m * x ^ 7 -
      16 * r_01 * r_m * x ^ 6 - 16 * r_0m * r_1 * x ^ 6 - 16 * r_1 * r_m * x ^ 4 -
      16 * r_1 * r_m * x ^ 6 - 2 * r_01 * r_m * x ^ 7 - 2 * r_0m * r_1 * x ^ 7 +
      2 * r_01 * r_m * x ^ 3 + 2 * r_0m * r_1 * x ^ 3 + 4 * r_01 * r_0m * x ^ 3 +
      4 * r_01 * r_0m * x ^ 7 + 16 * r_01 * r_0m * x ^ 4 + 16 * r_01 * r_0m * x ^ 6 +
      16 * r_01 * r_m * x ^ 4 + 16 * r_0m * r_1 * x ^ 4 + 34 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽125k1⁾`. -/
noncomputable def i8L4Q125k1_1 (x _r_001 _r_001m _r_00m _r_00m1 r_01 r_01m r_0m r_0m1 r_1 r_m _r_m1
    : ℝ) : ℝ :=
    8 - x ^ 3 - 4 * r_01m - 4 * r_0m1 - 4 * x ^ 2 - 4 * x ^ 4 - x ^ 5 / 2 + 7 / 2 * x +
      r_m * x ^ 6 - r_1 * x ^ 6 - 16 * r_01m * x - 16 * r_01m * x ^ 3 - 16 * r_0m1 * x -
      16 * r_0m1 * x ^ 3 - 6 * r_1 * x ^ 3 - 6 * r_1 * x ^ 5 - 4 * r_01m * x ^ 4 -
      4 * r_0m1 * x ^ 4 - 4 * r_1 * x - 4 * r_m * x - 2 * r_m * x ^ 2 + 2 * r_1 * x ^ 2 +
      10 * r_m * x ^ 3 + 10 * r_m * x ^ 5 + 14 * r_01 * x ^ 2 + 15 * r_1 * x ^ 4 +
      17 * r_m * x ^ 4 + 18 * r_0m * x ^ 2 - 16 * r_1 * r_m * x ^ 4 - 2 * r_1 * r_m * x ^ 3 +
      2 * r_1 * r_m * x ^ 7 + 16 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽125k1⁾`. -/
noncomputable def i8L4Q125k1_2 (_x _r_001 _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽125k1⁾`. -/
noncomputable def i8L4Q125k1_3 (_x _r_001 _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽125k1⁾`. -/
noncomputable def i8L4Q125k1_4 (_x _r_001 _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_125k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s125k1 x = i8L4S125k1 x + x * (i8L4Q125k1_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q125k1_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q125k1_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q125k1_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q125k1_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
      x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s125k1 i8Psi4s125k1N0 i8Psi4s125k1N1 i8Psi4s125k1N2 i8Psi4s125k1N3 i8Psi4s125k1N4
    i8Psi4s125k1W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_01m0 hx, i13hw_0m0 hx, i13hw_0m10 hx, i13hw_10
    hx, i13hw_1m hx, i13hw_1m0 hx, i13hw_m0 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0,
    i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S125k1 i8L4Q125k1_0 i8L4Q125k1_1 i8L4Q125k1_2 i8L4Q125k1_3 i8L4Q125k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽125k1⁾`. -/
noncomputable def i8L4R125k1 (x : ℝ) : ℝ :=
  x * (i8L4Q125k1_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q125k1_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q125k1_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q125k1_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q125k1_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R125k1 : Tendsto i8L4R125k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q125k1_0 (v 0) (v 9) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43)
      (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q125k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q125k1_1 (v 0) (v 9) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43)
      (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q125k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q125k1_0 x (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q125k1_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
      x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R125k1
  unfold i8L4Q125k1_2 i8L4Q125k1_3 i8L4Q125k1_4
  ring

/-- The singular part of `Ψ₄⁽125k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S125k2 (x : ℝ) : ℝ :=
    -21 / 2 - Real.log x ^ 2 + 3 * Real.log x + 2 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽125k2⁾`. -/
noncomputable def i8L4Q125k2_0 (x r_000m r_001m r_00m r_00m1 r_01 r_01m r_0m r_0m01 r_0m1 r_1 r_m
    _r_m1 : ℝ) : ℝ :=
    21 + 2 * r_01m + 2 * r_0m1 + 4 * r_001m + 4 * r_0m01 + 7 * x + 8 * r_00m1 - x ^ 4 / 2 +
      15 / 4 * x ^ 3 + 39 / 2 * x ^ 2 + r_01 * x ^ 6 + r_0m * x ^ 4 - r_m * x ^ 4 -
      49 * r_0m * x ^ 2 - 43 * r_m * x ^ 2 - 38 * r_m * x ^ 3 - 16 * r_01 * x ^ 4 -
      16 * r_01m * x ^ 3 - 16 * r_0m1 * x ^ 3 - 15 * r_01 * x ^ 2 - 8 * r_0m * x - 6 * r_m * x -
      4 * r_00m * x ^ 2 - 4 * r_01 * x - 2 * r_01m * x ^ 4 - 2 * r_0m1 * x ^ 4 - 2 * r_1 * x -
      2 * r_1 * x ^ 5 + 2 * r_0m * x ^ 5 + 4 * r_001m * x ^ 4 + 4 * r_01 * x ^ 3 +
      4 * r_0m01 * x ^ 4 + 4 * r_1 * x ^ 3 + 6 * r_0m * x ^ 3 + 8 * r_00m1 * x ^ 4 +
      16 * r_001m * x + 16 * r_001m * x ^ 3 + 16 * r_01m * x + 16 * r_0m01 * x +
      16 * r_0m01 * x ^ 3 + 16 * r_0m1 * x + 16 * r_1 * x ^ 4 + 20 * r_000m * x ^ 2 +
      32 * r_00m1 * x + 32 * r_00m1 * x ^ 3 + 40 * r_001m * x ^ 2 - 31 / 2 * r_1 * x ^ 2 -
      r_1 * x ^ 6 / 2 - 16 * r_01 * r_0m * x ^ 4 - 16 * r_01 * r_0m * x ^ 6 -
      16 * r_0m * r_1 * x ^ 4 - 4 * r_01 * r_0m * x ^ 3 - 4 * r_01 * r_0m * x ^ 7 -
      2 * r_0m * r_1 * x ^ 3 + 2 * r_0m * r_1 * x ^ 7 + 16 * r_0m * r_1 * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽125k2⁾`. -/
noncomputable def i8L4Q125k2_1 (x _r_000m _r_001m r_00m _r_00m1 _r_01 r_01m r_0m _r_0m01 _r_0m1 _r_1
    r_m _r_m1 : ℝ) : ℝ :=
    -14 + x ^ 3 / 2 - 5 * x ^ 2 + 4 * r_01m - 3 / 2 * x + r_m * x ^ 4 - 40 * r_01m * x ^ 2 -
      20 * r_00m * x ^ 2 - 4 * r_m * x + 4 * r_01m * x ^ 4 + 15 * r_m * x ^ 2 + 16 * r_01m * x +
      16 * r_01m * x ^ 3 + 20 * r_m * x ^ 3 + 22 * r_0m * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽125k2⁾`. -/
noncomputable def i8L4Q125k2_2 (x _r_000m _r_001m _r_00m _r_00m1 _r_01 _r_01m r_0m _r_0m01 _r_0m1
    r_1 r_m r_m1 : ℝ) : ℝ :=
    5 + x ^ 5 / 2 + 2 * r_m1 + 2 * x ^ 2 + 2 * x ^ 4 + 4 * x - 11 / 2 * x ^ 3 + r_1 * x ^ 6 +
      r_m * x ^ 4 - r_m * x ^ 6 - 20 * r_m * x ^ 2 - 20 * r_m1 * x ^ 2 - 18 * r_1 * x ^ 4 -
      7 * r_1 * x ^ 2 - 6 * r_m * x ^ 5 - 4 * r_m * x - 2 * r_1 * x + 2 * r_1 * x ^ 5 +
      2 * r_m1 * x ^ 4 + 6 * r_m * x ^ 3 + 8 * r_m1 * x + 8 * r_m1 * x ^ 3 + 10 * r_0m * x ^ 2 +
      24 * r_1 * x ^ 3 - 8 * r_1 * r_m * x ^ 4 - 8 * r_1 * r_m * x ^ 6 - 2 * r_1 * r_m * x ^ 3 -
      2 * r_1 * r_m * x ^ 7 + 20 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽125k2⁾`. -/
noncomputable def i8L4Q125k2_3 (_x _r_000m _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1
    _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽125k2⁾`. -/
noncomputable def i8L4Q125k2_4 (_x _r_000m _r_001m _r_00m _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1
    _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_125k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s125k2 x = i8L4S125k2 x +
      x * (i8L4Q125k2_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q125k2_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) + Real.log x ^ 2 * i8L4Q125k2_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q125k2_3 x (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q125k2_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s125k2 i8Psi4s125k2N0 i8Psi4s125k2N1 i8Psi4s125k2N2 i8Psi4s125k2N3 i8Psi4s125k2N4
    i8Psi4s125k2W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_00m0 hx, i13hw_010m hx, i13hw_0m0 hx, i13hw_0m00
    hx, i13hw_100m hx, i13hw_10m hx, i13hw_10m0 hx, i13hw_1m00 hx, i13hw_m0 hx, i13hw_m00 hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0,
    i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0,
    i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S125k2 i8L4Q125k2_0 i8L4Q125k2_1 i8L4Q125k2_2 i8L4Q125k2_3 i8L4Q125k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽125k2⁾`. -/
noncomputable def i8L4R125k2 (x : ℝ) : ℝ :=
  x * (i8L4Q125k2_0 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q125k2_1 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) + Real.log x ^ 2 * i8L4Q125k2_2 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q125k2_3 x (i13Rho [zero, zero, zero, negOne] x)
    (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q125k2_4 x (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x))

theorem tendsto_i8L4R125k2 : Tendsto i8L4R125k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q125k2_0 (v 0) (v 6) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43)
      (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q125k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q125k2_1 (v 0) (v 6) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43)
      (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q125k2_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q125k2_2 (v 0) (v 6) (v 15) (v 18) (v 21) (v 27) (v 36) (v 43)
      (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q125k2_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q125k2_0 x (i13Rho [zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q125k2_1 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q125k2_2 x (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R125k2
  unfold i8L4Q125k2_3 i8L4Q125k2_4
  ring

/-- The singular part of `Ψ₄⁽126⁾` at `ξ = 0`. -/
noncomputable def i8L4S126 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽126⁾`. -/
noncomputable def i8L4Q126_0 (x r_001 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -4 - 17 * x ^ 2 - 4 * x ^ 4 + 2 * x - 27 / 4 * x ^ 3 - 5 / 4 * x ^ 5 - 24 * r_1 * x ^ 3 -
      11 * r_1 ^ 2 * x ^ 5 - 10 * r_01 * x ^ 2 - 9 * r_1 * x ^ 4 - 6 * r_1 * x ^ 5 -
      5 * r_1 * x ^ 6 - 5 * r_1 ^ 2 * x ^ 7 + 4 * r_1 ^ 2 * x ^ 6 + 8 * r_001 * x ^ 2 +
      8 * r_0011 * x ^ 2 + 12 * r_1 ^ 2 * x ^ 4 + 36 * r_011 * x ^ 2 + 44 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽126⁾`. -/
noncomputable def i8L4Q126_1 (x _r_001 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -4 + x ^ 5 / 2 - 4 * x + 3 * x ^ 2 + 3 * x ^ 4 + 9 / 2 * x ^ 3 - 10 * r_1 ^ 2 * x ^ 5 -
      8 * r_01 * x ^ 2 - 8 * r_011 * x ^ 2 - 6 * r_1 * x ^ 2 - 4 * r_1 * x ^ 3 + 2 * r_1 * x ^ 6 +
      2 * r_1 ^ 2 * x ^ 7 + 4 * r_1 ^ 2 * x ^ 4 + 4 * r_1 ^ 2 * x ^ 6 + 8 * r_1 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽126⁾`. -/
noncomputable def i8L4Q126_2 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽126⁾`. -/
noncomputable def i8L4Q126_3 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽126⁾`. -/
noncomputable def i8L4Q126_4 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_126_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s126 x = i8L4S126 x + x * (i8L4Q126_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
      one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q126_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q126_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q126_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q126_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s126 i8Psi4s126N0 i8Psi4s126N1 i8Psi4s126N2 i8Psi4s126N3 i8Psi4s126N4 i8Psi4s126W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0101 hx, i13hw_0110 hx, i13hw_10 hx, i13hw_101 hx,
    i13hw_11 hx, i13hw_110 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S126 i8L4Q126_0 i8L4Q126_1 i8L4Q126_2 i8L4Q126_3 i8L4Q126_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽126⁾`. -/
noncomputable def i8L4R126 (x : ℝ) : ℝ :=
  x * (i8L4Q126_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q126_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q126_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q126_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q126_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R126 : Tendsto i8L4R126 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q126_0 (v 0) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q126_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q126_1 (v 0) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q126_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q126_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q126_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R126
  unfold i8L4Q126_2 i8L4Q126_3 i8L4Q126_4
  ring

/-- The regular parts of group 12. -/
noncomputable def i8L4RG12 (x : ℝ) : ℝ :=
  i8L4R120k1 x + i8L4R121 x + i8L4R122 x + i8L4R123 x + i8L4R124k0 x + i8L4R124k1 x +
    i8L4R125k0 x + i8L4R125k1 x + i8L4R125k2 x + i8L4R126 x

theorem tendsto_i8L4RG12 : Tendsto i8L4RG12 (𝓝[>] 0) (𝓝 0) := by
  have H := (((((((((tendsto_i8L4R120k1.add tendsto_i8L4R121).add tendsto_i8L4R122).add
    tendsto_i8L4R123).add tendsto_i8L4R124k0).add tendsto_i8L4R124k1).add tendsto_i8L4R125k0).add
    tendsto_i8L4R125k1).add tendsto_i8L4R125k2).add tendsto_i8L4R126)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
