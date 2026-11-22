/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L13
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 14

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_134_eq`, `QED.ThreeLoopD.tendsto_i8L4RG14` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽134⁾` at `ξ = 0`. -/
noncomputable def i8L4S134 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽134⁾`. -/
noncomputable def i8L4Q134_0 (x r_01 r_011 r_1 : ℝ) : ℝ :=
    -16 - 4 * x ^ 2 - 4 * x ^ 4 - 2 * x ^ 3 - 2 * x ^ 5 + 2 / 3 * π ^ 2 - 32 * r_01 * x ^ 2 -
      24 * r_1 ^ 2 * x ^ 5 - 16 * r_1 * x ^ 3 - 8 * r_1 * x ^ 6 - 8 * r_1 ^ 2 * x ^ 7 +
      16 * r_1 ^ 2 * x ^ 4 + 16 * r_1 ^ 2 * x ^ 6 + 24 * r_1 * x ^ 2 + 32 * r_011 * x ^ 2 -
      3 / 4 * π ^ 2 * x ^ 3 - π ^ 2 * x ^ 2 / 2 - π ^ 2 * x ^ 4 / 2 - π ^ 2 * x ^ 5 / 12 +
      2 / 3 * π ^ 2 * x + π ^ 2 * r_1 * x ^ 2 - 4 / 3 * π ^ 2 * r_1 * x ^ 5 -
      2 / 3 * π ^ 2 * r_1 ^ 2 * x ^ 4 - 2 / 3 * π ^ 2 * r_1 ^ 2 * x ^ 6 -
      π ^ 2 * r_1 * x ^ 6 / 3 - π ^ 2 * r_1 ^ 2 * x ^ 7 / 3 + 2 / 3 * π ^ 2 * r_1 * x ^ 3 +
      4 / 3 * π ^ 2 * r_01 * x ^ 2 + 4 / 3 * π ^ 2 * r_011 * x ^ 2 + 5 / 3 * π ^ 2 * r_1 ^ 2 * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽134⁾`. -/
noncomputable def i8L4Q134_1 (_x _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽134⁾`. -/
noncomputable def i8L4Q134_2 (_x _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽134⁾`. -/
noncomputable def i8L4Q134_3 (_x _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽134⁾`. -/
noncomputable def i8L4Q134_4 (_x _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_134_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s134 x = i8L4S134 x + x * (i8L4Q134_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x * i8L4Q134_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, one]
      x) (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q134_2 x (i13Rho [zero, one] x) (i13Rho [zero, one,
      one] x) (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q134_3 x (i13Rho [zero, one] x) (i13Rho [zero,
      one, one] x) (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q134_4 x (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s134 i8Psi4s134N0 i8Psi4s134N1 i8Psi4s134N2 i8Psi4s134N3 i8Psi4s134N4 i8Psi4s134W
  simp only [i13hw_11 hx]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S134 i8L4Q134_0 i8L4Q134_1 i8L4Q134_2 i8L4Q134_3 i8L4Q134_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽134⁾`. -/
noncomputable def i8L4R134 (x : ℝ) : ℝ :=
  x * (i8L4Q134_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q134_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q134_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one]
    x) + Real.log x ^ 3 * i8L4Q134_3 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
    [one] x) + Real.log x ^ 4 * i8L4Q134_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [one] x))

theorem tendsto_i8L4R134 : Tendsto i8L4R134 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q134_0 (v 0) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q134_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q134_0 x (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R134
  unfold i8L4Q134_1 i8L4Q134_2 i8L4Q134_3 i8L4Q134_4
  ring

/-- The singular part of `Ψ₄⁽135k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S135k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽135k0⁾`. -/
noncomputable def i8L4Q135k0_0 (x r_0011 r_0011m r_00m11 r_01 r_0101m r_011 r_01m r_01m1 r_0m01
    r_0m011 r_0m1 r_0m101 r_0m11 r_1 r_m r_m1 _r_m11 : ℝ) : ℝ :=
    x ^ 7 / 2 - 21 * x ^ 2 - 5 * x ^ 4 + 2 * x + 3 * x ^ 6 + 3 / 4 * x ^ 3 + 11 / 4 * x ^ 5 +
      r_1 * x ^ 8 - r_m * x ^ 4 - r_m * x ^ 8 - r_1 ^ 2 * x ^ 7 - 64 * r_0011m * x ^ 2 -
      40 * r_1 * x ^ 3 - 36 * r_m * x ^ 3 - 36 * r_m1 * x ^ 3 - 32 * r_0101m * x ^ 2 -
      24 * r_0m1 * x ^ 3 - 22 * r_1 * x ^ 5 - 16 * r_0011 * x ^ 2 - 16 * r_01m1 * x -
      16 * r_01m1 * x ^ 3 - 16 * r_0m11 * x - 16 * r_0m11 * x ^ 3 - 16 * r_m * x ^ 6 -
      12 * r_01 * x ^ 6 - 8 * r_01 * x ^ 3 - 8 * r_01m1 * x ^ 4 - 8 * r_0m11 * x ^ 4 -
      8 * r_m * x ^ 7 - 6 * r_1 * x ^ 6 - 4 * r_0m1 * x ^ 4 - 4 * r_1 ^ 2 * x ^ 6 +
      2 * r_01 * x ^ 8 + 2 * r_m * x ^ 5 + 2 * r_m1 * x ^ 6 + 4 * r_01 * x ^ 5 +
      4 * r_01 * x ^ 7 + 4 * r_01m * x ^ 4 + 4 * r_01m * x ^ 6 + 4 * r_0m1 * x ^ 6 +
      4 * r_1 * x ^ 7 + 5 * r_1 ^ 2 * x ^ 5 + 6 * r_m1 * x ^ 4 + 8 * r_01 * x ^ 4 +
      8 * r_01m * x ^ 3 + 12 * r_011 * x ^ 2 + 12 * r_m1 * x ^ 5 + 14 * r_01 * x ^ 2 +
      16 * r_01m * x ^ 5 + 16 * r_0m01 * x ^ 2 + 16 * r_0m1 * x ^ 5 + 16 * r_0m101 * x ^ 2 +
      16 * r_m1 * x ^ 2 + 18 * r_1 * x ^ 4 + 32 * r_00m11 * x ^ 2 + 32 * r_0m011 * x ^ 2 +
      36 * r_01m * x ^ 2 + 36 * r_0m1 * x ^ 2 + 40 * r_01m1 * x ^ 2 + 45 * r_1 * x ^ 2 +
      104 * r_0m11 * x ^ 2 - 40 * r_01 * r_m1 * x ^ 5 - 40 * r_01m * r_1 * x ^ 5 -
      40 * r_0m1 * r_1 * x ^ 5 - 36 * r_01 * r_1 * x ^ 7 - 36 * r_01 * r_m * x ^ 5 -
      16 * r_01 * r_0m1 * x ^ 5 - 16 * r_01 * r_1 * x ^ 5 - 16 * r_01 * r_m * x ^ 8 -
      16 * r_1 * r_m * x ^ 5 - 12 * r_1 * r_m * x ^ 8 - 6 * r_1 * r_m * x ^ 7 -
      4 * r_01 * r_m * x ^ 9 - 2 * r_1 * r_m * x ^ 9 + 4 * r_01 * r_1 * x ^ 9 +
      8 * r_01 * r_m * x ^ 6 + 8 * r_01 * r_m1 * x ^ 7 + 8 * r_01m * r_1 * x ^ 7 +
      8 * r_0m1 * r_1 * x ^ 7 + 16 * r_01 * r_01m * x ^ 5 + 16 * r_01 * r_m1 * x ^ 4 +
      16 * r_01 * r_m1 * x ^ 6 + 16 * r_01m * r_1 * x ^ 4 + 16 * r_01m * r_1 * x ^ 6 +
      16 * r_0m1 * r_1 * x ^ 4 + 16 * r_0m1 * r_1 * x ^ 6 + 36 * r_1 * r_m * x ^ 6 +
      48 * r_01 * r_1 * x ^ 6 - 16 * r_01 * r_1 * r_m * x ^ 7 - 16 * r_01 * r_1 * r_m * x ^ 9 -
      8 * r_01 * r_1 * r_m * x ^ 10 + 40 * r_01 * r_1 * r_m * x ^ 8

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽135k0⁾`. -/
noncomputable def i8L4Q135k0_1 (x _r_0011 _r_0011m _r_00m11 _r_01 _r_0101m r_011 _r_01m _r_01m1
    _r_0m01 _r_0m011 _r_0m1 _r_0m101 r_0m11 r_1 _r_m _r_m1 r_m11 : ℝ) : ℝ :=
    x ^ 5 / 2 + 3 * x ^ 4 + 4 * x + 6 * x ^ 2 + 11 / 2 * x ^ 3 - 24 * r_m11 * x ^ 2 -
      16 * r_m11 * x - 16 * r_m11 * x ^ 3 - 14 * r_1 * x ^ 2 - 8 * r_m11 * x ^ 4 -
      6 * r_1 ^ 2 * x ^ 5 + 2 * r_1 * x ^ 6 + 2 * r_1 ^ 2 * x ^ 7 + 4 * r_1 * x ^ 4 +
      4 * r_1 ^ 2 * x ^ 6 + 8 * r_1 * x ^ 5 + 16 * r_011 * x ^ 2 + 16 * r_0m11 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽135k0⁾`. -/
noncomputable def i8L4Q135k0_2 (_x _r_0011 _r_0011m _r_00m11 _r_01 _r_0101m _r_011 _r_01m _r_01m1
    _r_0m01 _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽135k0⁾`. -/
noncomputable def i8L4Q135k0_3 (_x _r_0011 _r_0011m _r_00m11 _r_01 _r_0101m _r_011 _r_01m _r_01m1
    _r_0m01 _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽135k0⁾`. -/
noncomputable def i8L4Q135k0_4 (_x _r_0011 _r_0011m _r_00m11 _r_01 _r_0101m _r_011 _r_01m _r_01m1
    _r_0m01 _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

theorem i8L4_135k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s135k0 x = i8L4S135k0 x + x * (i8L4Q135k0_0 x (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne, zero, one] x)
      (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x * i8L4Q135k0_1 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one,
      negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      one, zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero,
      one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)
      (i13Rho [negOne, one, one] x) + Real.log x ^ 2 * i8L4Q135k0_2 x (i13Rho [zero, zero, one, one]
      x) (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne, zero, one]
      x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 3 * i8L4Q135k0_3 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      one, negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 4 * i8L4Q135k0_4 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      one, negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, one, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s135k0 i8Psi4s135k0N0 i8Psi4s135k0N1 i8Psi4s135k0N2 i8Psi4s135k0N3 i8Psi4s135k0N4
    i8Psi4s135k0W
  simp only [hpl_zero, i13hw_0101 hx, i13hw_0110 hx, i13hw_01m01 hx, i13hw_0m110 hx, i13hw_10 hx,
    i13hw_101 hx, i13hw_11 hx, i13hw_110 hx, i13hw_1m01 hx, i13hw_m01 hx, i13hw_m011 hx, i13hw_m101
    hx, i13hw_m110 hx]
  simp only [i13hpl_rho_0011 h0, i8hpl_rho_0011m h0, i8hpl_rho_00m11 h0, i13hpl_rho_01 h0,
    i8hpl_rho_0101m h0, i13hpl_rho_011 h0, i13hpl_rho_01m h0, i13hpl_rho_01m1 h0, i13hpl_rho_0m01
    h0, i13hpl_rho_0m011 h0, i13hpl_rho_0m1 h0, i8hpl_rho_0m101 h0, i13hpl_rho_0m11 h0, i13hpl_rho_1
    h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0, i8hpl_rho_m11 h0]
  unfold i8L4S135k0 i8L4Q135k0_0 i8L4Q135k0_1 i8L4Q135k0_2 i8L4Q135k0_3 i8L4Q135k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽135k0⁾`. -/
noncomputable def i8L4R135k0 (x : ℝ) : ℝ :=
  x * (i8L4Q135k0_0 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one, negOne] x)
    (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero, one,
    negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne,
    one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one,
    one] x) + Real.log x * i8L4Q135k0_1 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
    one, one, negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
    zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
    x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 2 * i8L4Q135k0_2 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one,
    negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    one, negOne, one] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one]
    x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero,
    negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
    [negOne, one, one] x) + Real.log x ^ 3 * i8L4Q135k0_3 x (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 4 * i8L4Q135k0_4 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one,
    negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    one, negOne, one] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one]
    x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero,
    negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
    [negOne, one, one] x))

theorem tendsto_i8L4R135k0 : Tendsto i8L4R135k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q135k0_0 (v 0) (v 12) (v 14) (v 22) (v 27) (v 28) (v 29) (v 36)
      (v 37) (v 44) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q135k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q135k0_1 (v 0) (v 12) (v 14) (v 22) (v 27) (v 28) (v 29) (v 36)
      (v 37) (v 44) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q135k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q135k0_0 x (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, negOne, one,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho [zero, one,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q135k0_1 x (i13Rho [zero, zero, one,
      one] x) (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, negOne, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R135k0
  unfold i8L4Q135k0_2 i8L4Q135k0_3 i8L4Q135k0_4
  ring

/-- The singular part of `Ψ₄⁽135k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S135k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽135k1⁾`. -/
noncomputable def i8L4Q135k1_0 (x r_0011m r_00m11 r_01 r_0101m r_011 _r_011m r_01m r_01m1 r_0m
    r_0m011 r_0m1 r_0m101 r_0m11 r_1 r_m r_m1 _r_m11 : ℝ) : ℝ :=
    -8 * x - 8 * x ^ 2 + 2 * x ^ 3 - 7 / 2 * x ^ 6 - 3 / 4 * x ^ 7 + 3 / 4 * x ^ 5 +
      21 / 2 * x ^ 4 + r_0m * x ^ 8 + r_m * x ^ 4 + r_m * x ^ 8 - r_1 ^ 2 * x ^ 9 -
      40 * r_01m1 * x ^ 2 - 40 * r_0m11 * x ^ 2 - 36 * r_01m * x ^ 2 - 32 * r_00m11 * x ^ 2 -
      29 * r_1 * x ^ 4 - 22 * r_1 ^ 2 * x ^ 6 - 16 * r_011 * x ^ 3 - 16 * r_01m * x ^ 5 -
      16 * r_0m011 * x ^ 2 - 16 * r_0m1 * x ^ 5 - 16 * r_0m101 * x ^ 2 - 16 * r_m1 * x ^ 2 -
      12 * r_m1 * x ^ 5 - 8 * r_01 * x ^ 3 - 8 * r_01m * x ^ 3 - 8 * r_0m * x ^ 3 -
      8 * r_0m * x ^ 4 - 6 * r_m1 * x ^ 4 - 4 * r_01 * x ^ 4 - 4 * r_01 * x ^ 5 -
      4 * r_01 * x ^ 7 - 4 * r_01m * x ^ 4 - 4 * r_01m * x ^ 6 - 4 * r_0m1 * x ^ 6 -
      4 * r_1 * x ^ 3 - 4 * r_1 * x ^ 7 - 2 * r_01 * x ^ 8 - 2 * r_1 * x ^ 8 - 2 * r_m * x ^ 5 -
      2 * r_m1 * x ^ 6 + 2 * r_1 ^ 2 * x ^ 8 + 4 * r_011 * x ^ 4 + 4 * r_0m1 * x ^ 4 +
      6 * r_0m * x ^ 5 + 6 * r_0m * x ^ 7 + 8 * r_01m1 * x ^ 4 + 8 * r_0m11 * x ^ 4 +
      8 * r_m * x ^ 7 + 8 * r_1 ^ 2 * x ^ 5 + 9 * r_0m * x ^ 6 + 12 * r_01 * x ^ 6 +
      12 * r_0m1 * x ^ 2 + 13 * r_1 ^ 2 * x ^ 7 + 16 * r_01m1 * x + 16 * r_01m1 * x ^ 3 +
      16 * r_0m11 * x + 16 * r_0m11 * x ^ 3 + 16 * r_m * x ^ 6 + 18 * r_1 * x ^ 5 +
      21 * r_1 * x ^ 6 + 22 * r_01 * x ^ 2 + 24 * r_0m1 * x ^ 3 + 26 * r_0m * x ^ 2 +
      32 * r_0101m * x ^ 2 + 36 * r_m * x ^ 3 + 36 * r_m1 * x ^ 3 + 64 * r_0011m * x ^ 2 -
      48 * r_01 * r_1 * x ^ 6 - 36 * r_1 * r_m * x ^ 6 - 20 * r_0m * r_1 ^ 2 * x ^ 8 -
      16 * r_01 * r_01m * x ^ 5 - 16 * r_01 * r_0m * x ^ 5 - 16 * r_01 * r_m1 * x ^ 4 -
      16 * r_01 * r_m1 * x ^ 6 - 16 * r_011 * r_0m * x ^ 5 - 16 * r_01m * r_1 * x ^ 4 -
      16 * r_01m * r_1 * x ^ 6 - 16 * r_0m1 * r_1 * x ^ 4 - 16 * r_0m1 * r_1 * x ^ 6 -
      12 * r_0m * r_1 * x ^ 5 - 8 * r_01 * r_m * x ^ 6 - 8 * r_01 * r_m1 * x ^ 7 -
      8 * r_01m * r_1 * x ^ 7 - 8 * r_0m * r_1 * x ^ 6 - 8 * r_0m1 * r_1 * x ^ 7 -
      4 * r_01 * r_1 * x ^ 9 + 2 * r_1 * r_m * x ^ 9 + 4 * r_01 * r_m * x ^ 9 +
      4 * r_0m * r_1 * x ^ 9 + 4 * r_0m * r_1 ^ 2 * x ^ 10 + 6 * r_1 * r_m * x ^ 7 +
      8 * r_0m * r_1 ^ 2 * x ^ 7 + 8 * r_0m * r_1 ^ 2 * x ^ 9 + 12 * r_1 * r_m * x ^ 8 +
      16 * r_01 * r_0m1 * x ^ 5 + 16 * r_01 * r_1 * x ^ 5 + 16 * r_01 * r_m * x ^ 8 +
      16 * r_0m * r_1 * x ^ 8 + 16 * r_1 * r_m * x ^ 5 + 36 * r_01 * r_1 * x ^ 7 +
      36 * r_01 * r_m * x ^ 5 + 40 * r_01 * r_m1 * x ^ 5 + 40 * r_01m * r_1 * x ^ 5 +
      40 * r_0m1 * r_1 * x ^ 5 - 40 * r_01 * r_1 * r_m * x ^ 8 + 8 * r_01 * r_1 * r_m * x ^ 10 +
      16 * r_01 * r_1 * r_m * x ^ 7 + 16 * r_01 * r_1 * r_m * x ^ 9

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽135k1⁾`. -/
noncomputable def i8L4Q135k1_1 (x _r_0011m _r_00m11 _r_01 _r_0101m _r_011 r_011m r_01m r_01m1 _r_0m
    _r_0m011 r_0m1 _r_0m101 _r_0m11 r_1 r_m r_m1 r_m11 : ℝ) : ℝ :=
    x ^ 7 / 2 - 6 * x ^ 4 - 5 * x ^ 3 + 2 * x ^ 6 + 16 * x ^ 2 - 3 / 2 * x ^ 5 - r_m * x ^ 8 -
      48 * r_m1 * x ^ 2 - 40 * r_m11 * x ^ 2 - 26 * r_m * x ^ 2 - 22 * r_1 * x ^ 2 -
      18 * r_1 ^ 2 * x ^ 7 - 16 * r_1 * x ^ 6 - 9 * r_m * x ^ 6 - 8 * r_m * x ^ 3 -
      8 * r_1 ^ 2 * x ^ 5 - 6 * r_m * x ^ 5 - 6 * r_m * x ^ 7 - 4 * r_1 * x ^ 5 +
      2 * r_1 * x ^ 8 + 2 * r_1 ^ 2 * x ^ 9 + 4 * r_1 * x ^ 4 + 4 * r_1 * x ^ 7 +
      8 * r_m11 * x ^ 4 + 16 * r_011m * x ^ 2 + 16 * r_01m * x ^ 2 + 16 * r_01m1 * x ^ 2 +
      16 * r_0m1 * x ^ 2 + 16 * r_m11 * x + 16 * r_m11 * x ^ 3 + 24 * r_1 ^ 2 * x ^ 6 +
      32 * r_1 * x ^ 3 - 16 * r_1 * r_m * x ^ 8 - 8 * r_m * r_1 ^ 2 * x ^ 7 -
      8 * r_m * r_1 ^ 2 * x ^ 9 - 4 * r_1 * r_m * x ^ 9 - 4 * r_m * r_1 ^ 2 * x ^ 10 +
      8 * r_1 * r_m * x ^ 6 + 12 * r_1 * r_m * x ^ 5 + 20 * r_m * r_1 ^ 2 * x ^ 8

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽135k1⁾`. -/
noncomputable def i8L4Q135k1_2 (_x _r_0011m _r_00m11 _r_01 _r_0101m _r_011 _r_011m _r_01m _r_01m1
    _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽135k1⁾`. -/
noncomputable def i8L4Q135k1_3 (_x _r_0011m _r_00m11 _r_01 _r_0101m _r_011 _r_011m _r_01m _r_01m1
    _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽135k1⁾`. -/
noncomputable def i8L4Q135k1_4 (_x _r_0011m _r_00m11 _r_01 _r_0101m _r_011 _r_011m _r_01m _r_01m1
    _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

theorem i8L4_135k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s135k1 x = i8L4S135k1 x + x * (i8L4Q135k1_0 x (i13Rho [zero, zero, one, one, negOne] x)
      (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero,
      one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x * i8L4Q135k1_1 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
      negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho
      [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one]
      x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
      [negOne, one, one] x) + Real.log x ^ 2 * i8L4Q135k1_2 x (i13Rho [zero, zero, one, one, negOne]
      x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero,
      one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 3 * i8L4Q135k1_3 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
      negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho
      [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one]
      x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
      [negOne, one, one] x) + Real.log x ^ 4 * i8L4Q135k1_4 x (i13Rho [zero, zero, one, one, negOne]
      x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero,
      one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, one, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s135k1 i8Psi4s135k1N0 i8Psi4s135k1N1 i8Psi4s135k1N2 i8Psi4s135k1N3 i8Psi4s135k1N4
    i8Psi4s135k1W
  simp only [hpl_zero, i13hw_011m0 hx, i13hw_01m0 hx, i13hw_01m10 hx, i13hw_0m10 hx, i13hw_10 hx,
    i13hw_11m0 hx, i13hw_1m0 hx, i13hw_1m10 hx, i13hw_m0 hx, i13hw_m10 hx]
  simp only [i8hpl_rho_0011m h0, i8hpl_rho_00m11 h0, i13hpl_rho_01 h0, i8hpl_rho_0101m h0,
    i13hpl_rho_011 h0, i13hpl_rho_011m h0, i13hpl_rho_01m h0, i13hpl_rho_01m1 h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m011 h0, i13hpl_rho_0m1 h0, i8hpl_rho_0m101 h0, i13hpl_rho_0m11 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0, i13hpl_rho_m1 h0, i8hpl_rho_m11 h0]
  unfold i8L4S135k1 i8L4Q135k1_0 i8L4Q135k1_1 i8L4Q135k1_2 i8L4Q135k1_3 i8L4Q135k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽135k1⁾`. -/
noncomputable def i8L4R135k1 (x : ℝ) : ℝ :=
  x * (i8L4Q135k1_0 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, negOne, one,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho [zero, one,
    one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one]
    x) + Real.log x * i8L4Q135k1_1 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
    negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho
    [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne,
    one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one,
    one] x) + Real.log x ^ 2 * i8L4Q135k1_2 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho
    [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero, one, negOne]
    x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne]
    x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho
    [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)
    (i13Rho [negOne, one, one] x) + Real.log x ^ 3 * i8L4Q135k1_3 x (i13Rho [zero, zero, one, one,
    negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one,
    zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 4 * i8L4Q135k1_4 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
    negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, zero, one, negOne] x) (i13Rho
    [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne,
    one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one,
    one] x))

theorem tendsto_i8L4R135k1 : Tendsto i8L4R135k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q135k1_0 (v 0) (v 14) (v 22) (v 27) (v 28) (v 29) (v 33) (v 36)
      (v 37) (v 43) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q135k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q135k1_1 (v 0) (v 14) (v 22) (v 27) (v 28) (v 29) (v 33) (v 36)
      (v 37) (v 43) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q135k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q135k1_0 x (i13Rho [zero,
    zero, one, one, negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q135k1_1 x (i13Rho [zero, zero, one,
      one, negOne] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, zero, one, negOne] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R135k1
  unfold i8L4Q135k1_2 i8L4Q135k1_3 i8L4Q135k1_4
  ring

/-- The singular part of `Ψ₄⁽136k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S136k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽136k0⁾`. -/
noncomputable def i8L4Q136k0_0 (x r_0001 r_00011 r_001 r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -1 - 3 / 2 * x + x ^ 5 / 4 + 13 / 4 * x ^ 4 + 23 / 4 * x ^ 2 + 27 / 4 * x ^ 3 +
      r_1 * x ^ 6 + r_1 ^ 2 * x ^ 7 / 2 - r_01 * x ^ 6 - r_1 * x ^ 3 - 27 * r_01 * x ^ 2 -
      12 * r_001 * x ^ 3 - 8 * r_0001 * x ^ 2 - 8 * r_0011 * x - 8 * r_0011 * x ^ 3 -
      6 * r_01 * x ^ 5 - 5 * r_01 * x ^ 4 - 4 * r_0011 * x ^ 4 - 4 * r_01 ^ 2 * x ^ 4 -
      4 * r_01 ^ 2 * x ^ 6 - 2 * r_001 * x ^ 4 - 2 * r_01 * x ^ 3 - 2 * r_011 * x ^ 2 -
      2 * r_01 ^ 2 * x ^ 7 + 2 * r_001 * x ^ 6 + 4 * r_1 ^ 2 * x ^ 4 + 4 * r_1 ^ 2 * x ^ 6 +
      8 * r_001 * x ^ 5 + 10 * r_1 * x ^ 5 + 10 * r_01 ^ 2 * x ^ 5 + 16 * r_001 * x ^ 2 +
      24 * r_00101 * x ^ 2 + 64 * r_00011 * x ^ 2 - 33 / 2 * r_1 * x ^ 2 -
      17 / 2 * r_1 ^ 2 * x ^ 5 + 13 / 2 * r_1 * x ^ 4 - 20 * r_001 * r_1 * x ^ 5 -
      8 * r_001 * r_01 * x ^ 5 + 4 * r_001 * r_1 * x ^ 7 + 8 * r_001 * r_1 * x ^ 4 +
      8 * r_001 * r_1 * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽136k0⁾`. -/
noncomputable def i8L4Q136k0_1 (x _r_0001 _r_00011 _r_001 _r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -2 - 6 * x ^ 2 - 3 * x - 2 * x ^ 4 - 17 / 4 * x ^ 3 - x ^ 5 / 4 + r_1 ^ 2 * x ^ 5 -
      r_1 * x ^ 6 - r_1 ^ 2 * x ^ 7 - 8 * r_0011 * x ^ 2 - 8 * r_01 * x ^ 2 - 8 * r_1 * x ^ 4 -
      6 * r_1 * x ^ 5 - 4 * r_1 * x ^ 3 - 4 * r_1 ^ 2 * x ^ 6 + 4 * r_011 * x ^ 4 +
      4 * r_1 ^ 2 * x ^ 4 + 8 * r_011 * x + 8 * r_011 * x ^ 3 + 19 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽136k0⁾`. -/
noncomputable def i8L4Q136k0_2 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽136k0⁾`. -/
noncomputable def i8L4Q136k0_3 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽136k0⁾`. -/
noncomputable def i8L4Q136k0_4 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

theorem i8L4_136k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s136k0 x = i8L4S136k0 x + x * (i8L4Q136k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x * i8L4Q136k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q136k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q136k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q136k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s136k0 i8Psi4s136k0N0 i8Psi4s136k0N1 i8Psi4s136k0N2 i8Psi4s136k0N3 i8Psi4s136k0N4
    i8Psi4s136k0W
  simp only [hpl_zero, i13hw_00110 hx, i13hw_010 hx, i13hw_01001 hx, i13hw_0101 hx, i13hw_0110 hx,
    i13hw_10 hx, i13hw_1001 hx, i13hw_101 hx, i13hw_11 hx, i13hw_110 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_00011 h0, i13hpl_rho_001 h0, i8hpl_rho_00101 h0,
    i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S136k0 i8L4Q136k0_0 i8L4Q136k0_1 i8L4Q136k0_2 i8L4Q136k0_3 i8L4Q136k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽136k0⁾`. -/
noncomputable def i8L4R136k0 (x : ℝ) : ℝ :=
  x * (i8L4Q136k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q136k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q136k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q136k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q136k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R136k0 : Tendsto i8L4R136k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q136k0_0 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q136k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q136k0_1 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q136k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q136k0_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q136k0_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R136k0
  unfold i8L4Q136k0_2 i8L4Q136k0_3 i8L4Q136k0_4
  ring

/-- The singular part of `Ψ₄⁽136k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S136k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽136k1⁾`. -/
noncomputable def i8L4Q136k1_0 (x r_00011 r_001 r_00101 r_0011 r_01 _r_011 r_1 : ℝ) : ℝ :=
    -3 + x / 2 - 29 / 8 * x ^ 3 - 7 / 4 * x ^ 4 - x ^ 5 / 8 + 31 / 4 * x ^ 2 + r_01 * x ^ 6 -
      72 * r_00011 * x ^ 2 - 24 * r_00101 * x ^ 2 - 22 * r_001 * x ^ 2 - 20 * r_0011 * x ^ 2 -
      10 * r_01 ^ 2 * x ^ 5 - 8 * r_001 * x ^ 5 - 8 * r_1 * x ^ 2 - 5 * r_01 * x ^ 2 -
      5 * r_1 * x ^ 5 - 2 * r_001 * x ^ 6 + 2 * r_001 * x ^ 4 + 2 * r_01 * x ^ 3 +
      2 * r_01 ^ 2 * x ^ 7 + 4 * r_0011 * x ^ 4 + 4 * r_01 ^ 2 * x ^ 4 + 4 * r_01 ^ 2 * x ^ 6 +
      5 * r_01 * x ^ 4 + 6 * r_01 * x ^ 5 + 8 * r_0011 * x + 8 * r_0011 * x ^ 3 +
      12 * r_001 * x ^ 3 + 19 * r_1 * x ^ 3 - 11 / 2 * r_1 * x ^ 4 - r_1 * x ^ 6 / 2 -
      8 * r_001 * r_1 * x ^ 4 - 8 * r_001 * r_1 * x ^ 6 - 4 * r_001 * r_1 * x ^ 7 +
      8 * r_001 * r_01 * x ^ 5 + 20 * r_001 * r_1 * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽136k1⁾`. -/
noncomputable def i8L4Q136k1_1 (x _r_00011 r_001 _r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    6 - 9 * x ^ 2 + 5 * x - 3 / 2 * x ^ 3 - r_1 * x ^ 4 - 12 * r_1 * x ^ 3 - 8 * r_011 * x -
      8 * r_011 * x ^ 3 - 4 * r_011 * x ^ 4 + 8 * r_001 * x ^ 2 + 13 * r_1 * x ^ 2 +
      14 * r_01 * x ^ 2 + 16 * r_0011 * x ^ 2 + 20 * r_011 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽136k1⁾`. -/
noncomputable def i8L4Q136k1_2 (x _r_00011 _r_001 _r_00101 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -2 - 2 * x + x ^ 5 / 4 + 3 / 2 * x ^ 2 + 3 / 2 * x ^ 4 + 9 / 4 * x ^ 3 + r_1 * x ^ 6 +
      r_1 ^ 2 * x ^ 7 - 5 * r_1 ^ 2 * x ^ 5 - 4 * r_01 * x ^ 2 - 4 * r_011 * x ^ 2 -
      3 * r_1 * x ^ 2 - 2 * r_1 * x ^ 3 + 2 * r_1 ^ 2 * x ^ 4 + 2 * r_1 ^ 2 * x ^ 6 +
      4 * r_1 * x ^ 5

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽136k1⁾`. -/
noncomputable def i8L4Q136k1_3 (_x _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽136k1⁾`. -/
noncomputable def i8L4Q136k1_4 (_x _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_136k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s136k1 x = i8L4S136k1 x + x * (i8L4Q136k1_0 x (i13Rho [zero, zero, zero, one, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q136k1_1 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q136k1_2 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q136k1_3 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q136k1_4 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s136k1 i8Psi4s136k1N0 i8Psi4s136k1N1 i8Psi4s136k1N2 i8Psi4s136k1N3 i8Psi4s136k1N4
    i8Psi4s136k1W
  simp only [hpl_zero, i13hw_00, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01010 hx,
    i13hw_01100 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1010 hx, i13hw_1100 hx]
  simp only [i13hpl_rho_00011 h0, i13hpl_rho_001 h0, i8hpl_rho_00101 h0, i13hpl_rho_0011 h0,
    i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S136k1 i8L4Q136k1_0 i8L4Q136k1_1 i8L4Q136k1_2 i8L4Q136k1_3 i8L4Q136k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽136k1⁾`. -/
noncomputable def i8L4R136k1 (x : ℝ) : ℝ :=
  x * (i8L4Q136k1_0 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q136k1_1 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q136k1_2 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q136k1_3 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q136k1_4 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R136k1 : Tendsto i8L4R136k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q136k1_0 (v 0) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v 65))
      (by
      unfold i8L4Q136k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q136k1_1 (v 0) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v 65))
      (by
      unfold i8L4Q136k1_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q136k1_2 (v 0) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v 65))
      (by
      unfold i8L4Q136k1_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q136k1_0 x (i13Rho [zero,
    zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x)
    (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
    [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q136k1_1 x (i13Rho [zero, zero, zero,
      one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho
      [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q136k1_2 x (i13Rho [zero, zero, zero,
      one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho
      [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R136k1
  unfold i8L4Q136k1_3 i8L4Q136k1_4
  ring

/-- The singular part of `Ψ₄⁽137⁾` at `ξ = 0`. -/
noncomputable def i8L4S137 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽137⁾`. -/
noncomputable def i8L4Q137_0 (x r_001 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    8 - 30 * x ^ 2 - 4 * x ^ 4 + 4 * x - 23 / 2 * x ^ 3 - x ^ 5 / 2 - 32 * r_1 * x ^ 3 -
      18 * r_1 * x ^ 4 - 12 * r_1 * x ^ 5 - 8 * r_1 ^ 2 * x ^ 6 - 2 * r_1 * x ^ 6 -
      2 * r_1 ^ 2 * x ^ 7 + 2 * r_1 ^ 2 * x ^ 5 + 8 * r_1 ^ 2 * x ^ 4 + 12 * r_01 * x ^ 2 +
      16 * r_001 * x ^ 2 + 16 * r_0011 * x ^ 2 + 40 * r_011 * x ^ 2 + 64 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽137⁾`. -/
noncomputable def i8L4Q137_1 (x _r_001 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -8 + x ^ 5 - 8 * x + 6 * x ^ 2 + 6 * x ^ 4 + 9 * x ^ 3 - 20 * r_1 ^ 2 * x ^ 5 -
      16 * r_01 * x ^ 2 - 16 * r_011 * x ^ 2 - 12 * r_1 * x ^ 2 - 8 * r_1 * x ^ 3 +
      4 * r_1 * x ^ 6 + 4 * r_1 ^ 2 * x ^ 7 + 8 * r_1 ^ 2 * x ^ 4 + 8 * r_1 ^ 2 * x ^ 6 +
      16 * r_1 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽137⁾`. -/
noncomputable def i8L4Q137_2 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽137⁾`. -/
noncomputable def i8L4Q137_3 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽137⁾`. -/
noncomputable def i8L4Q137_4 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_137_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s137 x = i8L4S137 x + x * (i8L4Q137_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
      one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q137_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q137_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q137_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q137_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s137 i8Psi4s137N0 i8Psi4s137N1 i8Psi4s137N2 i8Psi4s137N3 i8Psi4s137N4 i8Psi4s137W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0101 hx, i13hw_0110 hx, i13hw_10 hx, i13hw_101 hx,
    i13hw_11 hx, i13hw_110 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S137 i8L4Q137_0 i8L4Q137_1 i8L4Q137_2 i8L4Q137_3 i8L4Q137_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽137⁾`. -/
noncomputable def i8L4R137 (x : ℝ) : ℝ :=
  x * (i8L4Q137_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q137_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q137_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q137_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q137_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R137 : Tendsto i8L4R137 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q137_0 (v 0) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q137_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q137_1 (v 0) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q137_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q137_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q137_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R137
  unfold i8L4Q137_2 i8L4Q137_3 i8L4Q137_4
  ring

/-- The singular part of `Ψ₄⁽138⁾` at `ξ = 0`. -/
noncomputable def i8L4S138 (x : ℝ) : ℝ :=
    (28 + Real.log x ^ 4 / 2 + 4 * Real.log x ^ 3 + 14 * Real.log x ^ 2 + 28 * Real.log x -
      3 / 10 * x * Real.log x ^ 5 - x * Real.log x ^ 4 / 2 + 2 / 3 * x * Real.log x ^ 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽138⁾`. -/
noncomputable def i8L4Q138_0 (x : ℝ) : ℝ :=
    -44 - 13 / 8 * x

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽138⁾`. -/
noncomputable def i8L4Q138_1 (x : ℝ) : ℝ :=
    44 + 13 / 4 * x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽138⁾`. -/
noncomputable def i8L4Q138_2 (x : ℝ) : ℝ :=
    -22 - 13 / 4 * x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽138⁾`. -/
noncomputable def i8L4Q138_3 (x : ℝ) : ℝ :=
    8 + 3 / 2 * x

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽138⁾`. -/
noncomputable def i8L4Q138_4 (x : ℝ) : ℝ :=
    -3 / 2 - x / 4

theorem i8L4_138_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s138 x = i8L4S138 x + x * (i8L4Q138_0 x + Real.log x * i8L4Q138_1 x +
      Real.log x ^ 2 * i8L4Q138_2 x + Real.log x ^ 3 * i8L4Q138_3 x +
      Real.log x ^ 4 * i8L4Q138_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s138 i8Psi4s138N0 i8Psi4s138N1 i8Psi4s138N2 i8Psi4s138N3 i8Psi4s138N4 i8Psi4s138W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00000]

  unfold i8L4S138 i8L4Q138_0 i8L4Q138_1 i8L4Q138_2 i8L4Q138_3 i8L4Q138_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽138⁾`. -/
noncomputable def i8L4R138 (x : ℝ) : ℝ :=
  x * (i8L4Q138_0 x + Real.log x * i8L4Q138_1 x + Real.log x ^ 2 * i8L4Q138_2 x +
    Real.log x ^ 3 * i8L4Q138_3 x + Real.log x ^ 4 * i8L4Q138_4 x)

theorem tendsto_i8L4R138 : Tendsto i8L4R138 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q138_0 (v 0)) (by
      unfold i8L4Q138_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q138_1 (v 0)) (by
      unfold i8L4Q138_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q138_2 (v 0)) (by
      unfold i8L4Q138_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q138_3 (v 0)) (by
      unfold i8L4Q138_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q138_4 (v 0)) (by
      unfold i8L4Q138_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q138_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q138_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q138_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q138_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4Q138_4 x)
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R138
  ring

/-- The singular part of `Ψ₄⁽139⁾` at `ξ = 0`. -/
noncomputable def i8L4S139 (x : ℝ) : ℝ :=
    36 - 4 * Real.log x ^ 2 - 8 / 3 * Real.log x ^ 3 - Real.log x ^ 4 / 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽139⁾`. -/
noncomputable def i8L4Q139_0 (x r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    14 - 83 / 8 * x + 19 / 8 * x ^ 3 + 107 / 4 * x ^ 2 - 99 * r_001 * x ^ 2 -
      46 * r_0001 * x ^ 2 + 36 * r_00001 * x ^ 2 + 36 * r_1 * x + 44 * r_1 * x ^ 3 -
      339 / 4 * r_1 * x ^ 2 - 35 / 2 * r_01 * x ^ 2 + 19 / 4 * r_1 * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽139⁾`. -/
noncomputable def i8L4Q139_1 (x _r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -14 - 63 / 2 * x ^ 2 - 61 / 4 * x - 19 / 4 * x ^ 3 - 44 * r_1 * x ^ 3 - 36 * r_0001 * x ^ 2 +
      36 * r_1 * x + 46 * r_001 * x ^ 2 + 99 * r_01 * x ^ 2 - 19 / 2 * r_1 * x ^ 4 +
      35 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽139⁾`. -/
noncomputable def i8L4Q139_2 (x _r_00001 _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    9 + 11 / 4 * x ^ 3 + 13 / 4 * x + 37 / 2 * x ^ 2 - 23 * r_01 * x ^ 2 + 14 * r_1 * x +
      18 * r_001 * x ^ 2 + 26 * r_1 * x ^ 3 - 91 / 2 * r_1 * x ^ 2 + 11 / 2 * r_1 * x ^ 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽139⁾`. -/
noncomputable def i8L4Q139_3 (x _r_00001 _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    -7 - 4 * x ^ 2 - 11 / 2 * x - x ^ 3 / 2 - r_1 * x ^ 4 - 6 * r_01 * x ^ 2 - 6 * r_1 * x ^ 3 +
      2 * r_1 * x + 5 * r_1 * x ^ 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽139⁾`. -/
noncomputable def i8L4Q139_4 (_x _r_00001 _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_139_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s139 x = i8L4S139 x + x * (i8L4Q139_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one]
      x) + Real.log x * i8L4Q139_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q139_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q139_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q139_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s139 i8Psi4s139N0 i8Psi4s139N1 i8Psi4s139N2 i8Psi4s139N3 i8Psi4s139N4 i8Psi4s139W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00010 hx, i13hw_0010 hx, i13hw_00100
    hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01000 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1000 hx]
  simp only [i13hpl_rho_00001 h0, i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S139 i8L4Q139_0 i8L4Q139_1 i8L4Q139_2 i8L4Q139_3 i8L4Q139_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽139⁾`. -/
noncomputable def i8L4R139 (x : ℝ) : ℝ :=
  x * (i8L4Q139_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q139_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q139_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q139_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q139_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R139 : Tendsto i8L4R139 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q139_0 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q139_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q139_1 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q139_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q139_2 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q139_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q139_3 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q139_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q139_0 x (i13Rho [zero,
    zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q139_1 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q139_2 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q139_3 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R139
  unfold i8L4Q139_4
  ring

/-- The singular part of `Ψ₄⁽140k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S140k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽140k0⁾`. -/
noncomputable def i8L4Q140k0_0 (x r_001 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -32 * x ^ 2 - 6 * x ^ 4 + 4 * x - 25 / 2 * x ^ 3 - 3 / 2 * x ^ 5 - 40 * r_1 * x ^ 3 -
      18 * r_1 * x ^ 4 - 12 * r_1 * x ^ 5 - 10 * r_1 ^ 2 * x ^ 5 - 6 * r_1 * x ^ 6 -
      6 * r_1 ^ 2 * x ^ 7 - 4 * r_01 * x ^ 2 + 16 * r_001 * x ^ 2 + 16 * r_0011 * x ^ 2 +
      16 * r_1 ^ 2 * x ^ 4 + 56 * r_011 * x ^ 2 + 76 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽140k0⁾`. -/
noncomputable def i8L4Q140k0_1 (x _r_001 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -8 + x ^ 5 - 8 * x + 6 * x ^ 2 + 6 * x ^ 4 + 9 * x ^ 3 - 20 * r_1 ^ 2 * x ^ 5 -
      16 * r_01 * x ^ 2 - 16 * r_011 * x ^ 2 - 12 * r_1 * x ^ 2 - 8 * r_1 * x ^ 3 +
      4 * r_1 * x ^ 6 + 4 * r_1 ^ 2 * x ^ 7 + 8 * r_1 ^ 2 * x ^ 4 + 8 * r_1 ^ 2 * x ^ 6 +
      16 * r_1 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽140k0⁾`. -/
noncomputable def i8L4Q140k0_2 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽140k0⁾`. -/
noncomputable def i8L4Q140k0_3 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽140k0⁾`. -/
noncomputable def i8L4Q140k0_4 (_x _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_140k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s140k0 x = i8L4S140k0 x + x * (i8L4Q140k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q140k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q140k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q140k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q140k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s140k0 i8Psi4s140k0N0 i8Psi4s140k0N1 i8Psi4s140k0N2 i8Psi4s140k0N3 i8Psi4s140k0N4
    i8Psi4s140k0W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0101 hx, i13hw_0110 hx, i13hw_10 hx, i13hw_101 hx,
    i13hw_11 hx, i13hw_110 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S140k0 i8L4Q140k0_0 i8L4Q140k0_1 i8L4Q140k0_2 i8L4Q140k0_3 i8L4Q140k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽140k0⁾`. -/
noncomputable def i8L4R140k0 (x : ℝ) : ℝ :=
  x * (i8L4Q140k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q140k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q140k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q140k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q140k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R140k0 : Tendsto i8L4R140k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q140k0_0 (v 0) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q140k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q140k0_1 (v 0) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q140k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q140k0_0 x (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one]
    x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q140k0_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R140k0
  unfold i8L4Q140k0_2 i8L4Q140k0_3 i8L4Q140k0_4
  ring

/-- The singular part of `Ψ₄⁽140k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S140k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽140k1⁾`. -/
noncomputable def i8L4Q140k1_0 (x r_0001 r_00011 r_001 r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -1 - 205 / 4 * x ^ 2 - 87 / 4 * x ^ 3 - 23 / 4 * x ^ 4 - 7 / 2 * x - x ^ 5 / 4 +
      r_01 * x ^ 6 - r_1 * x ^ 6 - 37 * r_1 * x ^ 3 - 28 * r_001 * x ^ 3 - 22 * r_001 * x ^ 4 -
      20 * r_1 * x ^ 5 - 18 * r_01 * x ^ 3 - 16 * r_001 * x ^ 5 - 12 * r_1 ^ 2 * x ^ 6 -
      10 * r_01 ^ 2 * x ^ 5 - 8 * r_0001 * x ^ 2 - 8 * r_0011 * x - 4 * r_01 ^ 2 * x ^ 4 -
      2 * r_001 * x ^ 6 + 2 * r_01 ^ 2 * x ^ 7 + 4 * r_0011 * x ^ 4 + 4 * r_1 ^ 2 * x ^ 4 +
      10 * r_01 * x ^ 5 + 11 * r_01 * x ^ 2 + 12 * r_01 ^ 2 * x ^ 6 + 16 * r_001 * x ^ 2 +
      17 * r_01 * x ^ 4 + 24 * r_0011 * x ^ 3 + 34 * r_011 * x ^ 2 + 72 * r_00101 * x ^ 2 +
      192 * r_00011 * x ^ 2 - 77 / 2 * r_1 * x ^ 4 - r_1 ^ 2 * x ^ 7 / 2 +
      17 / 2 * r_1 ^ 2 * x ^ 5 + 193 / 2 * r_1 * x ^ 2 - 24 * r_001 * r_01 * x ^ 5 -
      24 * r_001 * r_1 * x ^ 6 - 4 * r_001 * r_1 * x ^ 7 + 8 * r_001 * r_1 * x ^ 4 +
      20 * r_001 * r_1 * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽140k1⁾`. -/
noncomputable def i8L4Q140k1_1 (x _r_0001 _r_00011 _r_001 _r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -2 - 5 * x + 4 * x ^ 2 + 4 * x ^ 4 + x ^ 5 / 4 + 33 / 4 * x ^ 3 + r_1 * x ^ 6 +
      r_1 ^ 2 * x ^ 7 - 24 * r_0011 * x ^ 2 - 24 * r_011 * x ^ 3 - 19 * r_1 * x ^ 2 -
      17 * r_1 ^ 2 * x ^ 5 - 8 * r_01 * x ^ 2 - 4 * r_011 * x ^ 4 - 4 * r_1 * x ^ 3 +
      4 * r_1 ^ 2 * x ^ 4 + 8 * r_011 * x + 8 * r_1 * x ^ 4 + 12 * r_1 ^ 2 * x ^ 6 +
      14 * r_1 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽140k1⁾`. -/
noncomputable def i8L4Q140k1_2 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽140k1⁾`. -/
noncomputable def i8L4Q140k1_3 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽140k1⁾`. -/
noncomputable def i8L4Q140k1_4 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

theorem i8L4_140k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s140k1 x = i8L4S140k1 x + x * (i8L4Q140k1_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x * i8L4Q140k1_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q140k1_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q140k1_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q140k1_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s140k1 i8Psi4s140k1N0 i8Psi4s140k1N1 i8Psi4s140k1N2 i8Psi4s140k1N3 i8Psi4s140k1N4
    i8Psi4s140k1W
  simp only [hpl_zero, i13hw_00110 hx, i13hw_010 hx, i13hw_01001 hx, i13hw_0101 hx, i13hw_0110 hx,
    i13hw_10 hx, i13hw_1001 hx, i13hw_101 hx, i13hw_11 hx, i13hw_110 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_00011 h0, i13hpl_rho_001 h0, i8hpl_rho_00101 h0,
    i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S140k1 i8L4Q140k1_0 i8L4Q140k1_1 i8L4Q140k1_2 i8L4Q140k1_3 i8L4Q140k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽140k1⁾`. -/
noncomputable def i8L4R140k1 (x : ℝ) : ℝ :=
  x * (i8L4Q140k1_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q140k1_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q140k1_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q140k1_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q140k1_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R140k1 : Tendsto i8L4R140k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q140k1_0 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q140k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q140k1_1 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q140k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q140k1_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q140k1_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R140k1
  unfold i8L4Q140k1_2 i8L4Q140k1_3 i8L4Q140k1_4
  ring

/-- The regular parts of group 14. -/
noncomputable def i8L4RG14 (x : ℝ) : ℝ :=
  i8L4R134 x + i8L4R135k0 x + i8L4R135k1 x + i8L4R136k0 x + i8L4R136k1 x + i8L4R137 x +
    i8L4R138 x + i8L4R139 x + i8L4R140k0 x + i8L4R140k1 x

theorem tendsto_i8L4RG14 : Tendsto i8L4RG14 (𝓝[>] 0) (𝓝 0) := by
  have H := (((((((((tendsto_i8L4R134.add tendsto_i8L4R135k0).add tendsto_i8L4R135k1).add
    tendsto_i8L4R136k0).add tendsto_i8L4R136k1).add tendsto_i8L4R137).add tendsto_i8L4R138).add
    tendsto_i8L4R139).add tendsto_i8L4R140k0).add tendsto_i8L4R140k1)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
