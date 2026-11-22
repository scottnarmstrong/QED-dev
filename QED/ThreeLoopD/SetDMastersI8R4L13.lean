/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L12
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 13

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_127_eq`, `QED.ThreeLoopD.tendsto_i8L4RG13` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽127⁾` at `ξ = 0`. -/
noncomputable def i8L4S127 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽127⁾`. -/
noncomputable def i8L4Q127_0 (x r_01 r_011 r_011m r_01m r_01m1 r_0m r_0m1 r_0m11 r_1 r_m : ℝ) : ℝ :=
    8 + x ^ 4 + x ^ 5 / 2 - x ^ 6 + 2 * x + 5 * x ^ 3 + 8 * x ^ 2 - x ^ 7 / 2 + r_m * x ^ 8 -
      32 * r_011m * x ^ 2 - 32 * r_01m1 * x ^ 2 - 32 * r_0m11 * x ^ 2 - 20 * r_1 * x ^ 2 -
      8 * r_011 * x ^ 2 - 8 * r_1 ^ 2 * x ^ 4 - 2 * r_1 * x ^ 8 - 2 * r_m * x ^ 2 -
      2 * r_1 ^ 2 * x ^ 7 - 2 * r_1 ^ 2 * x ^ 9 + 4 * r_1 * x ^ 6 + 4 * r_m * x ^ 7 +
      4 * r_1 ^ 2 * x ^ 5 + 4 * r_1 ^ 2 * x ^ 6 + 4 * r_1 ^ 2 * x ^ 8 + 6 * r_m * x ^ 6 +
      7 * r_m * x ^ 4 + 8 * r_01m * x ^ 2 + 8 * r_0m * x ^ 2 + 8 * r_0m1 * x ^ 2 +
      8 * r_m * x ^ 5 + 16 * r_01 * x ^ 2 + 18 * r_1 * x ^ 4 - 16 * r_1 * r_m * x ^ 4 -
      8 * r_1 * r_m * x ^ 5 - 4 * r_m * r_1 ^ 2 * x ^ 6 + 4 * r_1 * r_m * x ^ 7 +
      4 * r_1 * r_m * x ^ 9 + 4 * r_m * r_1 ^ 2 * x ^ 10 + 8 * r_1 * r_m * x ^ 6 +
      8 * r_1 * r_m * x ^ 8

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽127⁾`. -/
noncomputable def i8L4Q127_1 (_x _r_01 _r_011 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11 _r_1 _r_m
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽127⁾`. -/
noncomputable def i8L4Q127_2 (_x _r_01 _r_011 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11 _r_1 _r_m
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽127⁾`. -/
noncomputable def i8L4Q127_3 (_x _r_01 _r_011 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11 _r_1 _r_m
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽127⁾`. -/
noncomputable def i8L4Q127_4 (_x _r_01 _r_011 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11 _r_1 _r_m
    : ℝ) : ℝ :=
    0

theorem i8L4_127_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s127 x = i8L4S127 x + x * (i8L4Q127_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
      one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x * i8L4Q127_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 2 * i8L4Q127_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q127_3 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) +
      Real.log x ^ 4 * i8L4Q127_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s127 i8Psi4s127N0 i8Psi4s127N1 i8Psi4s127N2 i8Psi4s127N3 i8Psi4s127N4 i8Psi4s127W
  simp only [i13hw_11 hx, i13hw_11m hx, i13hw_1m hx, i13hw_1m1 hx]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_011m h0, i13hpl_rho_01m h0,
    i13hpl_rho_01m1 h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_0m11 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0]
  unfold i8L4S127 i8L4Q127_0 i8L4Q127_1 i8L4Q127_2 i8L4Q127_3 i8L4Q127_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽127⁾`. -/
noncomputable def i8L4R127 (x : ℝ) : ℝ :=
  x * (i8L4Q127_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) + Real.log x * i8L4Q127_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, one]
    x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q127_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
    one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) + Real.log x ^ 3 * i8L4Q127_3 x (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q127_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
    one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R127 : Tendsto i8L4R127 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q127_0 (v 0) (v 27) (v 29) (v 33) (v 36) (v 37) (v 43) (v 49) (v
      51) (v 65) (v 66)) (by
      unfold i8L4Q127_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q127_0 x (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R127
  unfold i8L4Q127_1 i8L4Q127_2 i8L4Q127_3 i8L4Q127_4
  ring

/-- The singular part of `Ψ₄⁽128k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S128k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽128k0⁾`. -/
noncomputable def i8L4Q128k0_0 (x r_001 r_0011 r_01 r_011 r_0m11 r_1 r_m11 : ℝ) : ℝ :=
    -1 - 2 * r_m11 + 2 * x - 77 / 4 * x ^ 2 - 21 / 2 * x ^ 3 - 17 / 4 * x ^ 4 - x ^ 5 / 4 -
      r_1 * x ^ 6 - r_1 ^ 2 * x ^ 7 - 16 * r_m11 * x - 15 * r_1 * x ^ 5 - 13 * r_1 ^ 2 * x ^ 6 -
      12 * r_0011 * x ^ 2 - 11 * r_1 * x ^ 3 - 4 * r_001 * x ^ 2 - 3 * r_1 ^ 2 * x ^ 4 +
      2 * r_m11 * x ^ 4 + 16 * r_m11 * x ^ 3 + 17 * r_1 ^ 2 * x ^ 5 + 21 * r_01 * x ^ 2 +
      24 * r_011 * x ^ 2 + 24 * r_0m11 * x ^ 2 - 21 / 2 * r_1 * x ^ 4 + 75 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽128k0⁾`. -/
noncomputable def i8L4Q128k0_1 (x _r_001 _r_0011 r_01 r_011 _r_0m11 r_1 r_m11 : ℝ) : ℝ :=
    2 - 4 * r_m11 + 4 * x + x ^ 5 / 4 + 5 / 2 * x ^ 4 + 17 / 2 * x ^ 2 + 25 / 4 * x ^ 3 +
      r_1 * x ^ 6 + r_1 ^ 2 * x ^ 7 - 24 * r_m11 * x ^ 2 - 19 * r_1 * x ^ 2 - 16 * r_m11 * x -
      16 * r_m11 * x ^ 3 - 5 * r_1 ^ 2 * x ^ 5 - 4 * r_m11 * x ^ 4 - 2 * r_1 ^ 2 * x ^ 4 +
      2 * r_1 * x ^ 3 + 4 * r_01 * x ^ 2 + 6 * r_1 ^ 2 * x ^ 6 + 8 * r_1 * x ^ 4 +
      8 * r_1 * x ^ 5 + 12 * r_011 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽128k0⁾`. -/
noncomputable def i8L4Q128k0_2 (_x _r_001 _r_0011 _r_01 _r_011 _r_0m11 _r_1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽128k0⁾`. -/
noncomputable def i8L4Q128k0_3 (_x _r_001 _r_0011 _r_01 _r_011 _r_0m11 _r_1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽128k0⁾`. -/
noncomputable def i8L4Q128k0_4 (_x _r_001 _r_0011 _r_01 _r_011 _r_0m11 _r_1 _r_m11 : ℝ) : ℝ :=
    0

theorem i8L4_128k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s128k0 x = i8L4S128k0 x + x * (i8L4Q128k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x) +
      Real.log x * i8L4Q128k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 2 * i8L4Q128k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 3 * i8L4Q128k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 4 * i8L4Q128k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne, one, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s128k0 i8Psi4s128k0N0 i8Psi4s128k0N1 i8Psi4s128k0N2 i8Psi4s128k0N3 i8Psi4s128k0N4
    i8Psi4s128k0W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0101 hx, i13hw_0110 hx, i13hw_10 hx, i13hw_101 hx,
    i13hw_11 hx, i13hw_110 hx, i13hw_m011 hx, i13hw_m101 hx, i13hw_m110 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0,
    i13hpl_rho_0m11 h0, i13hpl_rho_1 h0, i8hpl_rho_m11 h0]
  unfold i8L4S128k0 i8L4Q128k0_0 i8L4Q128k0_1 i8L4Q128k0_2 i8L4Q128k0_3 i8L4Q128k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽128k0⁾`. -/
noncomputable def i8L4R128k0 (x : ℝ) : ℝ :=
  x * (i8L4Q128k0_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne, one, one] x) + Real.log x * i8L4Q128k0_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne,
    one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 2 * i8L4Q128k0_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 3 * i8L4Q128k0_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 4 * i8L4Q128k0_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne, one, one] x))

theorem tendsto_i8L4R128k0 : Tendsto i8L4R128k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q128k0_0 (v 0) (v 9) (v 12) (v 27) (v 29) (v 51) (v 65) (v 68))
      (by
      unfold i8L4Q128k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q128k0_1 (v 0) (v 9) (v 12) (v 27) (v 29) (v 51) (v 65) (v 68))
      (by
      unfold i8L4Q128k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q128k0_0 x (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one]
    x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q128k0_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne, one, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R128k0
  unfold i8L4Q128k0_2 i8L4Q128k0_3 i8L4Q128k0_4
  ring

/-- The singular part of `Ψ₄⁽128k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S128k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽128k1⁾`. -/
noncomputable def i8L4Q128k1_0 (x r_001 r_00m1 r_01 r_011m r_01m r_01m1 r_0m r_0m1 r_0m11 r_1 r_m
    r_m1 r_m11 : ℝ) : ℝ :=
    -1 + x / 2 - 8 * r_0m11 - 4 * r_011m - 4 * r_01m1 + 2 * r_m11 - 63 / 4 * x ^ 2 -
      5 / 4 * x ^ 5 - 5 / 4 * x ^ 6 - x ^ 7 / 8 + 9 / 2 * x ^ 4 + 113 / 8 * x ^ 3 -
      r_1 ^ 2 * x ^ 4 - 63 * r_1 * x ^ 3 - 40 * r_00m1 * x ^ 2 - 32 * r_0m11 * x -
      32 * r_0m11 * x ^ 3 - 16 * r_011m * x - 16 * r_011m * x ^ 3 - 16 * r_01m1 * x -
      16 * r_01m1 * x ^ 3 - 16 * r_m11 * x ^ 3 - 12 * r_0m1 * x ^ 3 - 8 * r_0m11 * x ^ 4 -
      8 * r_m * x ^ 3 - 4 * r_001 * x ^ 2 - 4 * r_011m * x ^ 4 - 4 * r_01m1 * x ^ 4 -
      4 * r_1 * x ^ 7 - 3 * r_1 ^ 2 * x ^ 8 - 2 * r_0m1 * x ^ 4 - 2 * r_m11 * x ^ 4 +
      2 * r_0m * x ^ 2 + 2 * r_0m1 * x ^ 6 + 3 * r_m * x ^ 7 + 4 * r_1 ^ 2 * x ^ 6 +
      8 * r_0m1 * x + 8 * r_1 ^ 2 * x ^ 7 + 12 * r_0m1 * x ^ 5 + 16 * r_1 * x ^ 4 +
      16 * r_1 * x ^ 5 + 16 * r_m * x ^ 5 + 16 * r_m11 * x + 18 * r_01m * x ^ 2 +
      21 * r_01 * x ^ 2 + 32 * r_m1 * x ^ 2 + 33 * r_1 * x ^ 2 + 58 * r_0m1 * x ^ 2 +
      80 * r_0m11 * x ^ 2 - 15 / 2 * r_1 ^ 2 * x ^ 5 - r_1 * x ^ 8 / 2 - r_1 ^ 2 * x ^ 9 / 2 +
      r_m * x ^ 8 / 4 + 5 / 2 * r_1 * x ^ 6 + 7 / 4 * r_m * x ^ 4 + 19 / 2 * r_m * x ^ 6 +
      31 / 2 * r_m * x ^ 2 + r_1 * r_m * x ^ 9 + r_m * r_1 ^ 2 * x ^ 10 - r_m * r_1 ^ 2 * x ^ 6 -
      40 * r_0m1 * r_1 * x ^ 5 - 34 * r_1 * r_m * x ^ 5 - 8 * r_m * r_1 ^ 2 * x ^ 7 -
      4 * r_1 * r_m * x ^ 4 + 4 * r_0m1 * r_1 * x ^ 3 + 4 * r_0m1 * r_1 * x ^ 7 +
      8 * r_m * r_1 ^ 2 * x ^ 9 + 10 * r_1 * r_m * x ^ 6 + 10 * r_1 * r_m * x ^ 8 +
      16 * r_0m1 * r_1 * x ^ 4 + 16 * r_0m1 * r_1 * x ^ 6 + 17 * r_1 * r_m * x ^ 7

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽128k1⁾`. -/
noncomputable def i8L4Q128k1_1 (x _r_001 _r_00m1 r_01 _r_011m _r_01m _r_01m1 _r_0m r_0m1 _r_0m11 r_1
    _r_m r_m1 r_m11 : ℝ) : ℝ :=
    -x ^ 5 - 6 * x ^ 4 - 5 * x + 8 * r_m11 + 16 * x ^ 2 + 3 / 2 * x ^ 3 - 80 * r_m11 * x ^ 2 -
      40 * r_m1 * x ^ 2 - 21 * r_1 * x ^ 2 - 12 * r_m1 * x ^ 5 - 8 * r_1 * x ^ 5 - 8 * r_m1 * x -
      2 * r_1 * x ^ 6 - 2 * r_m1 * x ^ 6 + 2 * r_m1 * x ^ 4 + 4 * r_01 * x ^ 2 +
      8 * r_m11 * x ^ 4 + 10 * r_1 * x ^ 3 + 12 * r_m1 * x ^ 3 + 20 * r_0m1 * x ^ 2 +
      21 * r_1 * x ^ 4 + 32 * r_m11 * x + 32 * r_m11 * x ^ 3 - 16 * r_1 * r_m1 * x ^ 4 -
      16 * r_1 * r_m1 * x ^ 6 - 4 * r_1 * r_m1 * x ^ 3 - 4 * r_1 * r_m1 * x ^ 7 +
      40 * r_1 * r_m1 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽128k1⁾`. -/
noncomputable def i8L4Q128k1_2 (_x _r_001 _r_00m1 _r_01 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11
    _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽128k1⁾`. -/
noncomputable def i8L4Q128k1_3 (_x _r_001 _r_00m1 _r_01 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11
    _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽128k1⁾`. -/
noncomputable def i8L4Q128k1_4 (_x _r_001 _r_00m1 _r_01 _r_011m _r_01m _r_01m1 _r_0m _r_0m1 _r_0m11
    _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

theorem i8L4_128k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s128k1 x = i8L4S128k1 x + x * (i8L4Q128k1_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x * i8L4Q128k1_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
      x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 2 * i8L4Q128k1_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
      x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 3 * i8L4Q128k1_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
      x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 4 * i8L4Q128k1_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
      x) (i13Rho [negOne, one, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s128k1 i8Psi4s128k1N0 i8Psi4s128k1N1 i8Psi4s128k1N2 i8Psi4s128k1N3 i8Psi4s128k1N4
    i8Psi4s128k1W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0m10 hx, i13hw_10 hx, i13hw_11m hx, i13hw_1m hx,
    i13hw_1m01 hx, i13hw_1m1 hx, i13hw_1m10 hx, i13hw_m01 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_011m h0,
    i13hpl_rho_01m h0, i13hpl_rho_01m1 h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_0m11 h0,
    i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0, i8hpl_rho_m11 h0]
  unfold i8L4S128k1 i8L4Q128k1_0 i8L4Q128k1_1 i8L4Q128k1_2 i8L4Q128k1_3 i8L4Q128k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽128k1⁾`. -/
noncomputable def i8L4R128k1 (x : ℝ) : ℝ :=
  x * (i8L4Q128k1_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
    negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
    [negOne, one, one] x) + Real.log x * i8L4Q128k1_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
    zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 2 * i8L4Q128k1_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
    x) (i13Rho [negOne, one, one] x) + Real.log x ^ 3 * i8L4Q128k1_3 x (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 4 * i8L4Q128k1_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
    x) (i13Rho [negOne, one, one] x))

theorem tendsto_i8L4R128k1 : Tendsto i8L4R128k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q128k1_0 (v 0) (v 9) (v 21) (v 27) (v 33) (v 36) (v 37) (v 43)
      (v 49) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q128k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q128k1_1 (v 0) (v 9) (v 21) (v 27) (v 33) (v 36) (v 37) (v 43)
      (v 49) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q128k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q128k1_0 x (i13Rho [zero,
    zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q128k1_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne]
      x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R128k1
  unfold i8L4Q128k1_2 i8L4Q128k1_3 i8L4Q128k1_4
  ring

/-- The singular part of `Ψ₄⁽128k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S128k2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽128k2⁾`. -/
noncomputable def i8L4Q128k2_0 (x r_001m r_00m r_00m1 r_01 r_011m r_01m r_01m1 r_0m r_0m1 r_0m11 r_1
    r_m r_m1 _r_m11 : ℝ) : ℝ :=
    -2 - 8 * x ^ 4 - 5 * x + 4 * r_011m + 4 * r_01m1 + 5 * x ^ 3 + 8 * r_0m11 - 13 / 2 * x ^ 2 -
      3 / 4 * x ^ 5 + r_m * x ^ 6 / 2 - 80 * r_0m11 * x ^ 2 - 40 * r_011m * x ^ 2 -
      40 * r_01m1 * x ^ 2 - 38 * r_1 * x ^ 3 - 26 * r_01m * x ^ 2 - 20 * r_001m * x ^ 2 -
      18 * r_0m1 * x ^ 2 - 13 * r_1 * x ^ 5 - 12 * r_0m1 * x ^ 5 - 8 * r_0m1 * x -
      4 * r_00m * x ^ 2 - 2 * r_0m1 * x ^ 6 + 2 * r_0m1 * x ^ 4 + 4 * r_01 * x ^ 2 +
      4 * r_011m * x ^ 4 + 4 * r_01m1 * x ^ 4 + 8 * r_0m11 * x ^ 4 + 11 * r_m * x ^ 5 +
      12 * r_0m1 * x ^ 3 + 16 * r_011m * x + 16 * r_011m * x ^ 3 + 16 * r_01m1 * x +
      16 * r_01m1 * x ^ 3 + 20 * r_00m1 * x ^ 2 + 24 * r_m * x ^ 3 + 25 * r_0m * x ^ 2 +
      32 * r_0m11 * x + 32 * r_0m11 * x ^ 3 + 32 * r_m1 * x ^ 2 + 38 * r_1 * x ^ 4 +
      38 * r_m * x ^ 2 - 3 / 2 * r_1 * x ^ 6 + 25 / 2 * r_m * x ^ 4 + 29 / 2 * r_1 * x ^ 2 +
      r_1 * r_m * x ^ 7 - 17 * r_1 * r_m * x ^ 5 - 16 * r_0m1 * r_1 * x ^ 4 -
      16 * r_0m1 * r_1 * x ^ 6 - 4 * r_0m1 * r_1 * x ^ 3 - 4 * r_0m1 * r_1 * x ^ 7 -
      4 * r_1 * r_m * x ^ 4 + 20 * r_1 * r_m * x ^ 6 + 40 * r_0m1 * r_1 * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽128k2⁾`. -/
noncomputable def i8L4Q128k2_1 (x _r_001m _r_00m _r_00m1 _r_01 _r_011m r_01m _r_01m1 r_0m _r_0m1
    _r_0m11 r_1 r_m r_m1 r_m11 : ℝ) : ℝ :=
    2 + x ^ 4 - 4 * r_m11 + 6 * x - 19 / 4 * x ^ 3 + x ^ 7 / 4 + 3 / 2 * x ^ 2 + 3 / 2 * x ^ 6 +
      r_1 * x ^ 8 + r_1 ^ 2 * x ^ 9 - 27 * r_m * x ^ 2 - 18 * r_1 ^ 2 * x ^ 7 - 16 * r_m11 * x -
      16 * r_m11 * x ^ 3 - 12 * r_1 * x ^ 4 - 12 * r_m1 * x ^ 3 - 11 * r_1 * x ^ 6 -
      8 * r_m * x ^ 3 - 8 * r_m1 * x ^ 2 - 7 * r_1 ^ 2 * x ^ 5 - 6 * r_1 * x ^ 2 -
      6 * r_m * x ^ 6 - 4 * r_m * x ^ 7 - 4 * r_m11 * x ^ 4 - 2 * r_m * x ^ 5 - 2 * r_m1 * x ^ 4 -
      2 * r_1 ^ 2 * x ^ 4 + 2 * r_m1 * x ^ 6 + 2 * r_1 ^ 2 * x ^ 8 + 4 * r_0m * x ^ 2 +
      4 * r_1 * x ^ 5 + 4 * r_1 * x ^ 7 + 8 * r_m1 * x + 12 * r_m1 * x ^ 5 + 20 * r_01m * x ^ 2 +
      20 * r_1 * x ^ 3 + 24 * r_1 ^ 2 * x ^ 6 + 40 * r_m11 * x ^ 2 - r_m * x ^ 8 / 2 +
      7 / 2 * r_m * x ^ 4 - 40 * r_1 * r_m1 * x ^ 5 - 12 * r_1 * r_m * x ^ 8 -
      8 * r_1 * r_m * x ^ 4 - 8 * r_m * r_1 ^ 2 * x ^ 7 - 8 * r_m * r_1 ^ 2 * x ^ 9 -
      2 * r_1 * r_m * x ^ 9 - 2 * r_m * r_1 ^ 2 * x ^ 6 - 2 * r_m * r_1 ^ 2 * x ^ 10 +
      2 * r_1 * r_m * x ^ 7 + 4 * r_1 * r_m1 * x ^ 3 + 4 * r_1 * r_m1 * x ^ 7 +
      8 * r_1 * r_m * x ^ 5 + 12 * r_1 * r_m * x ^ 6 + 16 * r_1 * r_m1 * x ^ 4 +
      16 * r_1 * r_m1 * x ^ 6 + 20 * r_m * r_1 ^ 2 * x ^ 8

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽128k2⁾`. -/
noncomputable def i8L4Q128k2_2 (_x _r_001m _r_00m _r_00m1 _r_01 _r_011m _r_01m _r_01m1 _r_0m _r_0m1
    _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽128k2⁾`. -/
noncomputable def i8L4Q128k2_3 (_x _r_001m _r_00m _r_00m1 _r_01 _r_011m _r_01m _r_01m1 _r_0m _r_0m1
    _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽128k2⁾`. -/
noncomputable def i8L4Q128k2_4 (_x _r_001m _r_00m _r_00m1 _r_01 _r_011m _r_01m _r_01m1 _r_0m _r_0m1
    _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

theorem i8L4_128k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s128k2 x = i8L4S128k2 x + x * (i8L4Q128k2_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x * i8L4Q128k2_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
      negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 2 * i8L4Q128k2_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 3 * i8L4Q128k2_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 4 * i8L4Q128k2_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s128k2 i8Psi4s128k2N0 i8Psi4s128k2N1 i8Psi4s128k2N2 i8Psi4s128k2N3 i8Psi4s128k2N4
    i8Psi4s128k2W
  simp only [hpl_zero, i13hw_010m hx, i13hw_01m0 hx, i13hw_0m0 hx, i13hw_101m hx, i13hw_10m hx,
    i13hw_10m1 hx, i13hw_110m hx, i13hw_11m0 hx, i13hw_1m hx, i13hw_1m0 hx, i13hw_m0 hx]
  simp only [i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0,
    i13hpl_rho_011m h0, i13hpl_rho_01m h0, i13hpl_rho_01m1 h0, i13hpl_rho_0m h0, i13hpl_rho_0m1 h0,
    i13hpl_rho_0m11 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0, i8hpl_rho_m11 h0]
  unfold i8L4S128k2 i8L4Q128k2_0 i8L4Q128k2_1 i8L4Q128k2_2 i8L4Q128k2_3 i8L4Q128k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽128k2⁾`. -/
noncomputable def i8L4R128k2 (x : ℝ) : ℝ :=
  x * (i8L4Q128k2_0 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho
    [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x * i8L4Q128k2_1 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 2 * i8L4Q128k2_2 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 3 * i8L4Q128k2_3 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 4 * i8L4Q128k2_4 x (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one,
    negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))

theorem tendsto_i8L4R128k2 : Tendsto i8L4R128k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q128k2_0 (v 0) (v 15) (v 18) (v 21) (v 27) (v 33) (v 36) (v 37)
      (v 43) (v 49) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q128k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q128k2_1 (v 0) (v 15) (v 18) (v 21) (v 27) (v 33) (v 36) (v 37)
      (v 43) (v 49) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q128k2_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q128k2_0 x (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one]
    x) (i13Rho [negOne, one, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q128k2_1 x (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
      [negOne, one, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R128k2
  unfold i8L4Q128k2_2 i8L4Q128k2_3 i8L4Q128k2_4
  ring

/-- The singular part of `Ψ₄⁽129⁾` at `ξ = 0`. -/
noncomputable def i8L4S129 (x : ℝ) : ℝ :=
    (32 + Real.log x ^ 4 / 2 + 4 * x + 4 * Real.log x ^ 3 + 16 * Real.log x ^ 2 +
      32 * Real.log x - π ^ 2 / 3 - Real.log x * π ^ 2 / 3 - π ^ 2 * Real.log x ^ 2 / 6 -
      x * Real.log x ^ 5 / 10 + 2 / 3 * x * Real.log x ^ 3 +
      π ^ 2 * x * Real.log x ^ 3 / 18) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽129⁾`. -/
noncomputable def i8L4Q129_0 (x r_0000m r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    -1 - 3 / 8 * x - x ^ 2 / 2 - π ^ 2 / 3 - x ^ 3 / 8 + r_0m * x ^ 4 / 2 - 16 * r_0000m * x ^ 2 -
      2 * r_00m * x ^ 2 + 4 * r_0m * x + 4 * r_0m * x ^ 3 + 18 * r_000m * x ^ 2 -
      π ^ 2 * x / 24 + 15 / 2 * r_0m * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽129⁾`. -/
noncomputable def i8L4Q129_1 (x _r_0000m r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    1 + x ^ 3 / 2 + π ^ 2 / 3 + 3 / 2 * x ^ 2 + 3 / 4 * x - r_0m * x ^ 4 - 18 * r_00m * x ^ 2 -
      4 * r_0m * x ^ 3 - 4 * r_m * x - 4 * r_m * x ^ 3 + 2 * r_0m * x ^ 2 + 4 * r_0m * x +
      16 * r_000m * x ^ 2 - 15 / 2 * r_m * x ^ 2 - r_m * x ^ 4 / 2 + π ^ 2 * x / 12

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽129⁾`. -/
noncomputable def i8L4Q129_2 (x _r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -1 / 2 - 3 / 4 * x ^ 3 - x ^ 2 / 2 - π ^ 2 / 6 + 5 / 4 * x + r_0m * x ^ 4 + r_m * x ^ 4 -
      r_m * x ^ 2 - 8 * r_00m * x ^ 2 - 4 * r_m * x + 2 * r_0m * x + 2 * r_0m * x ^ 3 +
      4 * r_m * x ^ 3 + 9 * r_0m * x ^ 2 - π ^ 2 * x / 12

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽129⁾`. -/
noncomputable def i8L4Q129_3 (x _r_0000m _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    1 + x ^ 3 / 2 - r_m * x ^ 4 - 3 * r_m * x ^ 2 - 2 * r_m * x - 2 * r_m * x ^ 3 + 2 * r_0m * x ^ 2

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽129⁾`. -/
noncomputable def i8L4Q129_4 (x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    1 / 2 + x / 4

theorem i8L4_129_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s129 x = i8L4S129 x + x * (i8L4Q129_0 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x * i8L4Q129_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q129_2 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q129_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)
      + Real.log x ^ 4 * i8L4Q129_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s129 i8Psi4s129N0 i8Psi4s129N1 i8Psi4s129N2 i8Psi4s129N3 i8Psi4s129N4 i8Psi4s129W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00000, i13hw_000m0 hx, i13hw_00m0 hx,
    i13hw_00m00 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_0m000 hx, i13hw_m0 hx, i13hw_m00 hx,
    i13hw_m000 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S129 i8L4Q129_0 i8L4Q129_1 i8L4Q129_2 i8L4Q129_3 i8L4Q129_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽129⁾`. -/
noncomputable def i8L4R129 (x : ℝ) : ℝ :=
  x * (i8L4Q129_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q129_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q129_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q129_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q129_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R129 : Tendsto i8L4R129 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q129_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q129_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q129_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q129_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q129_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q129_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q129_3 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q129_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q129_4 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q129_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q129_0 x (i13Rho [zero,
    zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q129_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q129_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q129_3 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4Q129_4 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R129
  ring

/-- The singular part of `Ψ₄⁽130⁾` at `ξ = 0`. -/
noncomputable def i8L4S130 (x : ℝ) : ℝ :=
    16 - 8 * Real.log x ^ 2 - 2 / 3 * π ^ 2 + π ^ 2 * Real.log x ^ 2 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽130⁾`. -/
noncomputable def i8L4Q130_0 (x r_001 r_01 r_1 : ℝ) : ℝ :=
    -8 - π ^ 2 - 10 * x - 4 * x ^ 2 + 2 * x ^ 3 + π ^ 2 * x ^ 2 / 2 - 16 * r_001 * x ^ 2 -
      16 * r_1 * x ^ 3 - 4 * r_1 * x ^ 2 + 4 * r_1 * x ^ 4 + 16 * r_1 * x + 24 * r_01 * x ^ 2 +
      π ^ 2 * x / 4 + π ^ 2 * x ^ 3 / 12 - 5 / 3 * π ^ 2 * r_01 * x ^ 2 -
      2 / 3 * π ^ 2 * r_001 * x ^ 2 - 2 / 3 * π ^ 2 * r_1 * x - π ^ 2 * r_1 * x ^ 2 / 6 +
      π ^ 2 * r_1 * x ^ 4 / 6 + 2 / 3 * π ^ 2 * r_1 * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽130⁾`. -/
noncomputable def i8L4Q130_1 (x _r_001 r_01 r_1 : ℝ) : ℝ :=
    8 + π ^ 2 - 4 * x ^ 3 + 4 * x - 24 * r_1 * x ^ 2 - 8 * r_1 * x ^ 4 + 16 * r_01 * x ^ 2 +
      16 * r_1 * x + 16 * r_1 * x ^ 3 - 2 / 3 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 6 +
      π ^ 2 * x / 6 - 2 / 3 * π ^ 2 * r_1 * x - 2 / 3 * π ^ 2 * r_1 * x ^ 3 -
      π ^ 2 * r_1 * x ^ 4 / 3 + 2 / 3 * π ^ 2 * r_01 * x ^ 2 + 5 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽130⁾`. -/
noncomputable def i8L4Q130_2 (_x _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽130⁾`. -/
noncomputable def i8L4Q130_3 (_x _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽130⁾`. -/
noncomputable def i8L4Q130_4 (_x _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_130_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s130 x = i8L4S130 x + x * (i8L4Q130_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one]
      x) (i13Rho [one] x) + Real.log x * i8L4Q130_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q130_2 x (i13Rho [zero, zero, one] x) (i13Rho
      [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q130_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
      [one] x) + Real.log x ^ 4 * i8L4Q130_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s130 i8Psi4s130N0 i8Psi4s130N1 i8Psi4s130N2 i8Psi4s130N3 i8Psi4s130N4 i8Psi4s130W
  simp only [hpl_zero, i13hw_00, i13hw_010 hx, i13hw_10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S130 i8L4Q130_0 i8L4Q130_1 i8L4Q130_2 i8L4Q130_3 i8L4Q130_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽130⁾`. -/
noncomputable def i8L4R130 (x : ℝ) : ℝ :=
  x * (i8L4Q130_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q130_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q130_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one]
    x) + Real.log x ^ 3 * i8L4Q130_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho
    [one] x) + Real.log x ^ 4 * i8L4Q130_4 x (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x)
    (i13Rho [one] x))

theorem tendsto_i8L4R130 : Tendsto i8L4R130 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q130_0 (v 0) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q130_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q130_1 (v 0) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q130_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q130_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q130_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R130
  unfold i8L4Q130_2 i8L4Q130_3 i8L4Q130_4
  ring

/-- The singular part of `Ψ₄⁽131k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S131k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽131k0⁾`. -/
noncomputable def i8L4Q131k0_0 (x r_0001 r_000m1 r_001 r_00m01 r_00m1 r_01 r_01m r_0m01 r_0m1 r_1
    r_m _r_m1 : ℝ) : ℝ :=
    16 + 2 * x - 9 / 4 * x ^ 3 - 3 / 2 * x ^ 4 - x ^ 5 / 4 + 15 / 2 * x ^ 2 + r_m * x ^ 6 / 2 -
      r_01 * x ^ 6 - 24 * r_00m1 * x ^ 2 - 18 * r_01 * x ^ 2 - 16 * r_00m1 * x -
      16 * r_00m1 * x ^ 3 - 8 * r_00m1 * x ^ 4 - 8 * r_01m * x ^ 3 - 8 * r_0m01 * x -
      8 * r_0m01 * x ^ 3 - 8 * r_0m1 * x ^ 3 - 8 * r_m * x ^ 2 - 4 * r_001 * x ^ 2 -
      4 * r_01 * x ^ 3 - 4 * r_0m01 * x ^ 4 - 4 * r_m * x ^ 3 - 2 * r_01 * x ^ 5 -
      2 * r_01m * x ^ 4 - 2 * r_0m1 * x ^ 4 + 2 * r_01m * x ^ 2 + 2 * r_0m1 * x ^ 2 +
      4 * r_m * x ^ 5 + 8 * r_00m01 * x ^ 2 + 8 * r_01 * x ^ 4 + 8 * r_01m * x + 8 * r_0m1 * x +
      14 * r_1 * x ^ 3 + 16 * r_0001 * x ^ 2 + 48 * r_000m1 * x ^ 2 - 31 / 2 * r_1 * x ^ 2 +
      3 / 2 * r_1 * x ^ 4 + 15 / 2 * r_m * x ^ 4 - 8 * r_01 * r_m * x ^ 4 -
      2 * r_01 * r_m * x ^ 5 + 2 * r_01 * r_m * x ^ 7 + 8 * r_01 * r_m * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽131k0⁾`. -/
noncomputable def i8L4Q131k0_1 (x _r_0001 _r_000m1 r_001 _r_00m01 r_00m1 r_01 _r_01m _r_0m01 r_0m1
    r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -12 + x ^ 3 - 2 * x - 2 * x ^ 2 - 32 * r_00m1 * x ^ 2 - 16 * r_001 * x ^ 2 - 8 * r_1 * x ^ 3 -
      2 * r_1 * x ^ 4 + 8 * r_0m1 * x ^ 4 + 10 * r_1 * x ^ 2 + 12 * r_01 * x ^ 2 +
      16 * r_0m1 * x + 16 * r_0m1 * x ^ 3 + 24 * r_0m1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽131k0⁾`. -/
noncomputable def i8L4Q131k0_2 (x _r_0001 _r_000m1 _r_001 _r_00m01 _r_00m1 r_01 _r_01m _r_0m01 r_0m1
    r_1 _r_m r_m1 : ℝ) : ℝ :=
    4 - x ^ 3 - 12 * r_m1 * x ^ 2 - 8 * r_m1 * x - 8 * r_m1 * x ^ 3 - 6 * r_1 * x ^ 2 -
      4 * r_m1 * x ^ 4 + 2 * r_1 * x ^ 4 + 4 * r_1 * x ^ 3 + 8 * r_01 * x ^ 2 + 8 * r_0m1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽131k0⁾`. -/
noncomputable def i8L4Q131k0_3 (_x _r_0001 _r_000m1 _r_001 _r_00m01 _r_00m1 _r_01 _r_01m _r_0m01
    _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽131k0⁾`. -/
noncomputable def i8L4Q131k0_4 (_x _r_0001 _r_000m1 _r_001 _r_00m01 _r_00m1 _r_01 _r_01m _r_0m01
    _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_131k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s131k0 x = i8L4S131k0 x + x * (i8L4Q131k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne,
      zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q131k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q131k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q131k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q131k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s131k0 i8Psi4s131k0N0 i8Psi4s131k0N1 i8Psi4s131k0N2 i8Psi4s131k0N3 i8Psi4s131k0N4
    i8Psi4s131k0W
  simp only [hpl_zero, i13hw_00, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_0m001 hx,
    i13hw_0m010 hx, i13hw_0m100 hx, i13hw_10 hx, i13hw_100 hx, i13hw_m001 hx, i13hw_m01 hx,
    i13hw_m010 hx, i13hw_m100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0, i13hpl_rho_00m01 h0,
    i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0,
    i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S131k0 i8L4Q131k0_0 i8L4Q131k0_1 i8L4Q131k0_2 i8L4Q131k0_3 i8L4Q131k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽131k0⁾`. -/
noncomputable def i8L4R131k0 (x : ℝ) : ℝ :=
  x * (i8L4Q131k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne,
    zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x * i8L4Q131k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
    zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q131k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q131k0_3 x (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q131k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x))

theorem tendsto_i8L4R131k0 : Tendsto i8L4R131k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q131k0_0 (v 0) (v 3) (v 7) (v 9) (v 19) (v 21) (v 27) (v 36) (v
      44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q131k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q131k0_1 (v 0) (v 3) (v 7) (v 9) (v 19) (v 21) (v 27) (v 36) (v
      44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q131k0_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q131k0_2 (v 0) (v 3) (v 7) (v 9) (v 19) (v 21) (v 27) (v 36) (v
      44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q131k0_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q131k0_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q131k0_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q131k0_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R131k0
  unfold i8L4Q131k0_3 i8L4Q131k0_4
  ring

/-- The singular part of `Ψ₄⁽131k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S131k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽131k1⁾`. -/
noncomputable def i8L4Q131k1_0 (x r_0001m r_000m r_000m1 r_001 r_0010m _r_001m r_00m r_00m01 r_00m1
    r_01 r_01m r_0m r_0m01 r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ :=
    8 + x ^ 5 / 2 - 4 * x ^ 2 - 2 * x ^ 3 + 2 * x ^ 4 + 5 / 2 * x + r_01 * x ^ 2 +
      r_01 * x ^ 6 + r_1 * x ^ 6 / 2 - r_0m * x ^ 6 - 40 * r_00m1 * x ^ 2 - 36 * r_00m * x ^ 2 -
      24 * r_000m1 * x ^ 2 - 20 * r_0m01 * x ^ 2 - 16 * r_001 * x ^ 2 - 13 * r_01 * x ^ 4 -
      12 * r_0m * x ^ 2 - 8 * r_00m01 * x ^ 2 - 8 * r_01m * x - 8 * r_0m1 * x - 6 * r_0m * x ^ 5 -
      4 * r_0m * x ^ 4 - 4 * r_m * x ^ 5 - 2 * r_01m * x ^ 2 - 2 * r_0m1 * x ^ 2 +
      2 * r_01 * x ^ 5 + 2 * r_01m * x ^ 4 + 2 * r_0m1 * x ^ 4 + 4 * r_0m * x ^ 3 +
      4 * r_0m01 * x ^ 4 + 4 * r_m * x ^ 3 + 8 * r_0010m * x ^ 2 + 8 * r_00m1 * x ^ 4 +
      8 * r_01m * x ^ 3 + 8 * r_0m01 * x + 8 * r_0m01 * x ^ 3 + 8 * r_0m1 * x ^ 3 +
      8 * r_1 * x ^ 2 + 8 * r_m * x ^ 2 + 16 * r_00m1 * x + 16 * r_00m1 * x ^ 3 +
      24 * r_0001m * x ^ 2 + 24 * r_000m * x ^ 2 + 24 * r_01 * x ^ 3 - 17 / 2 * r_1 * x ^ 4 -
      15 / 2 * r_m * x ^ 4 - r_m * x ^ 6 / 2 - 8 * r_01 * r_m * x ^ 6 - 8 * r_0m * r_1 * x ^ 6 -
      2 * r_01 * r_m * x ^ 7 - 2 * r_0m * r_1 * x ^ 7 + 2 * r_01 * r_m * x ^ 5 +
      2 * r_0m * r_1 * x ^ 5 + 8 * r_01 * r_m * x ^ 4 + 8 * r_0m * r_1 * x ^ 4 +
      20 * r_01 * r_0m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽131k1⁾`. -/
noncomputable def i8L4Q131k1_1 (x _r_0001m _r_000m _r_000m1 _r_001 _r_0010m r_001m r_00m _r_00m01
    r_00m1 r_01 r_01m r_0m r_0m01 r_0m1 r_1 r_m _r_m1 : ℝ) : ℝ :=
    -12 - x ^ 5 - 7 * x - 6 * x ^ 2 - 2 * x ^ 4 + 15 / 2 * x ^ 3 + r_m * x ^ 6 -
      26 * r_1 * x ^ 3 - 24 * r_00m * x ^ 2 - 20 * r_01m * x ^ 2 - 16 * r_0m1 * x -
      16 * r_0m1 * x ^ 3 - 12 * r_0m * x ^ 3 - 8 * r_001m * x ^ 2 - 8 * r_01 * x ^ 3 -
      8 * r_0m1 * x ^ 4 - 2 * r_0m * x ^ 4 - 2 * r_1 * x ^ 6 + 2 * r_01 * x ^ 4 +
      2 * r_0m * x ^ 6 + 6 * r_m * x ^ 5 + 7 * r_1 * x ^ 2 + 8 * r_01 * x ^ 2 + 8 * r_0m * x ^ 5 +
      8 * r_0m01 * x ^ 2 + 9 * r_m * x ^ 4 + 12 * r_m * x ^ 2 + 16 * r_m * x ^ 3 +
      20 * r_0m1 * x ^ 2 + 21 * r_1 * x ^ 4 + 24 * r_00m1 * x ^ 2 + 36 * r_0m * x ^ 2 -
      20 * r_0m * r_1 * x ^ 5 - 8 * r_01 * r_0m * x ^ 5 - 8 * r_1 * r_m * x ^ 4 -
      2 * r_1 * r_m * x ^ 5 + 2 * r_1 * r_m * x ^ 7 + 4 * r_0m * r_1 * x ^ 7 +
      8 * r_0m * r_1 * x ^ 4 + 8 * r_0m * r_1 * x ^ 6 + 8 * r_1 * r_m * x ^ 6

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽131k1⁾`. -/
noncomputable def i8L4Q131k1_2 (x _r_0001m _r_000m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m01
    _r_00m1 _r_01 r_01m r_0m _r_0m01 _r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    4 + x ^ 5 - 6 * x ^ 3 + 2 * x ^ 2 + 2 * x ^ 4 + 4 * x - 20 * r_m1 * x ^ 2 -
      18 * r_1 * x ^ 4 - 18 * r_m * x ^ 2 - 8 * r_1 * x ^ 2 - 8 * r_m * x ^ 5 - 2 * r_m * x ^ 6 +
      2 * r_1 * x ^ 6 + 4 * r_m * x ^ 3 + 4 * r_m1 * x ^ 4 + 8 * r_01m * x ^ 2 +
      8 * r_0m * x ^ 2 + 8 * r_m1 * x + 8 * r_m1 * x ^ 3 + 24 * r_1 * x ^ 3 -
      8 * r_1 * r_m * x ^ 4 - 8 * r_1 * r_m * x ^ 6 - 4 * r_1 * r_m * x ^ 7 + 20 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽131k1⁾`. -/
noncomputable def i8L4Q131k1_3 (_x _r_0001m _r_000m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m01
    _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽131k1⁾`. -/
noncomputable def i8L4Q131k1_4 (_x _r_0001m _r_000m _r_000m1 _r_001 _r_0010m _r_001m _r_00m _r_00m01
    _r_00m1 _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_131k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s131k1 x = i8L4S131k1 x + x * (i8L4Q131k1_0 x (i13Rho [zero, zero, zero, one, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho
      [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q131k1_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x) + Real.log x ^ 2 * i8L4Q131k1_2 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q131k1_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x) + Real.log x ^ 4 * i8L4Q131k1_4 x (i13Rho [zero, zero, zero, one,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s131k1 i8Psi4s131k1N0 i8Psi4s131k1N1 i8Psi4s131k1N2 i8Psi4s131k1N3 i8Psi4s131k1N4
    i8Psi4s131k1W
  simp only [hpl_zero, i13hw_00, i13hw_001m0 hx, i13hw_00m0 hx, i13hw_00m10 hx, i13hw_010 hx,
    i13hw_010m0 hx, i13hw_01m0 hx, i13hw_01m00 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_0m10 hx,
    i13hw_10 hx, i13hw_10m0 hx, i13hw_1m0 hx, i13hw_1m00 hx, i13hw_m0 hx, i13hw_m00 hx, i13hw_m10
    hx]
  simp only [i13hpl_rho_0001m h0, i13hpl_rho_000m h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0,
    i13hpl_rho_0010m h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m01 h0, i13hpl_rho_00m1
    h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1
    h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S131k1 i8L4Q131k1_0 i8L4Q131k1_1 i8L4Q131k1_2 i8L4Q131k1_3 i8L4Q131k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽131k1⁾`. -/
noncomputable def i8L4R131k1 (x : ℝ) : ℝ :=
  x * (i8L4Q131k1_0 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) + Real.log x * i8L4Q131k1_1 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero,
    zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 2 * i8L4Q131k1_2 x (i13Rho [zero, zero, zero, one,
    negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q131k1_3 x (i13Rho [zero, zero, zero, one, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 4 * i8L4Q131k1_4 x (i13Rho [zero, zero, zero, one,
    negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R131k1 : Tendsto i8L4R131k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q131k1_0 (v 0) (v 5) (v 6) (v 7) (v 9) (v 11) (v 15) (v 18) (v
      19) (v 21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q131k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q131k1_1 (v 0) (v 5) (v 6) (v 7) (v 9) (v 11) (v 15) (v 18) (v
      19) (v 21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q131k1_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q131k1_2 (v 0) (v 5) (v 6) (v 7) (v 9) (v 11) (v 15) (v 18) (v
      19) (v 21) (v 27) (v 36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q131k1_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q131k1_0 x (i13Rho [zero,
    zero, zero, one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho
    [zero, zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero,
    one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q131k1_1 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q131k1_2 x (i13Rho [zero, zero, zero,
      one, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne, one]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, negOne] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one]
      x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R131k1
  unfold i8L4Q131k1_3 i8L4Q131k1_4
  ring

/-- The singular part of `Ψ₄⁽132⁾` at `ξ = 0`. -/
noncomputable def i8L4S132 (x : ℝ) : ℝ :=
    12 - Real.log x ^ 4 / 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽132⁾`. -/
noncomputable def i8L4Q132_0 (x r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    18 - 33 / 8 * x - 27 / 4 * x ^ 2 - 3 / 8 * x ^ 3 - 12 * r_1 * x ^ 3 + 3 * r_001 * x ^ 2 +
      12 * r_00001 * x ^ 2 + 12 * r_1 * x + 30 * r_0001 * x ^ 2 - 3 / 4 * r_1 * x ^ 4 +
      3 / 4 * r_1 * x ^ 2 + 51 / 2 * r_01 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽132⁾`. -/
noncomputable def i8L4Q132_1 (x _r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -18 - 15 / 4 * x + 3 / 4 * x ^ 3 + 15 / 2 * x ^ 2 - 30 * r_001 * x ^ 2 - 12 * r_0001 * x ^ 2 -
      3 * r_01 * x ^ 2 + 12 * r_1 * x + 12 * r_1 * x ^ 3 - 51 / 2 * r_1 * x ^ 2 +
      3 / 2 * r_1 * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽132⁾`. -/
noncomputable def i8L4Q132_2 (x _r_00001 _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    9 - 9 / 2 * x ^ 2 - 9 / 4 * x - 3 / 4 * x ^ 3 - 6 * r_1 * x ^ 3 + 6 * r_001 * x ^ 2 +
      6 * r_1 * x + 15 * r_01 * x ^ 2 - 3 / 2 * r_1 * x ^ 4 + 3 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽132⁾`. -/
noncomputable def i8L4Q132_3 (x _r_00001 _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    -3 + x ^ 3 / 2 + 2 * x ^ 2 - x / 2 + r_1 * x ^ 4 - 5 * r_1 * x ^ 2 - 2 * r_01 * x ^ 2 +
      2 * r_1 * x + 2 * r_1 * x ^ 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽132⁾`. -/
noncomputable def i8L4Q132_4 (_x _r_00001 _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_132_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s132 x = i8L4S132 x + x * (i8L4Q132_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one]
      x) + Real.log x * i8L4Q132_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q132_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q132_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q132_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s132 i8Psi4s132N0 i8Psi4s132N1 i8Psi4s132N2 i8Psi4s132N3 i8Psi4s132N4 i8Psi4s132W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00010 hx, i13hw_0010 hx, i13hw_00100
    hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01000 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1000 hx]
  simp only [i13hpl_rho_00001 h0, i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S132 i8L4Q132_0 i8L4Q132_1 i8L4Q132_2 i8L4Q132_3 i8L4Q132_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽132⁾`. -/
noncomputable def i8L4R132 (x : ℝ) : ℝ :=
  x * (i8L4Q132_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q132_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q132_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q132_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q132_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R132 : Tendsto i8L4R132 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q132_0 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q132_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q132_1 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q132_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q132_2 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q132_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q132_3 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q132_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q132_0 x (i13Rho [zero,
    zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q132_1 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q132_2 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q132_3 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R132
  unfold i8L4Q132_4
  ring

/-- The singular part of `Ψ₄⁽133⁾` at `ξ = 0`. -/
noncomputable def i8L4S133 (x : ℝ) : ℝ :=
    16 - 8 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽133⁾`. -/
noncomputable def i8L4Q133_0 (x r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -24 + x ^ 3 - 5 * x + 10 * x ^ 2 - 40 * r_001 * x ^ 2 - 34 * r_1 * x ^ 2 -
      16 * r_0001 * x ^ 2 - 4 * r_01 * x ^ 2 + 2 * r_1 * x ^ 4 + 16 * r_1 * x + 16 * r_1 * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽133⁾`. -/
noncomputable def i8L4Q133_1 (x _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    24 - 12 * x ^ 2 - 6 * x - 2 * x ^ 3 - 16 * r_1 * x ^ 3 - 4 * r_1 * x ^ 4 + 4 * r_1 * x ^ 2 +
      16 * r_001 * x ^ 2 + 16 * r_1 * x + 40 * r_01 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽133⁾`. -/
noncomputable def i8L4Q133_2 (x _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    -12 - 2 * x + 2 * x ^ 3 + 8 * x ^ 2 - 20 * r_1 * x ^ 2 - 8 * r_01 * x ^ 2 + 4 * r_1 * x ^ 4 +
      8 * r_1 * x + 8 * r_1 * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽133⁾`. -/
noncomputable def i8L4Q133_3 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽133⁾`. -/
noncomputable def i8L4Q133_4 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_133_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s133 x = i8L4S133 x + x * (i8L4Q133_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q133_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q133_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q133_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q133_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s133 i8Psi4s133N0 i8Psi4s133N1 i8Psi4s133N2 i8Psi4s133N3 i8Psi4s133N4 i8Psi4s133W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_10 hx,
    i13hw_100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S133 i8L4Q133_0 i8L4Q133_1 i8L4Q133_2 i8L4Q133_3 i8L4Q133_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽133⁾`. -/
noncomputable def i8L4R133 (x : ℝ) : ℝ :=
  x * (i8L4Q133_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    one] x) (i13Rho [one] x) + Real.log x * i8L4Q133_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q133_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q133_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q133_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R133 : Tendsto i8L4R133 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q133_0 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q133_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q133_1 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q133_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q133_2 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q133_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q133_0 x (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q133_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q133_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R133
  unfold i8L4Q133_3 i8L4Q133_4
  ring

/-- The regular parts of group 13. -/
noncomputable def i8L4RG13 (x : ℝ) : ℝ :=
  i8L4R127 x + i8L4R128k0 x + i8L4R128k1 x + i8L4R128k2 x + i8L4R129 x + i8L4R130 x +
    i8L4R131k0 x + i8L4R131k1 x + i8L4R132 x + i8L4R133 x

theorem tendsto_i8L4RG13 : Tendsto i8L4RG13 (𝓝[>] 0) (𝓝 0) := by
  have H := (((((((((tendsto_i8L4R127.add tendsto_i8L4R128k0).add tendsto_i8L4R128k1).add
    tendsto_i8L4R128k2).add tendsto_i8L4R129).add tendsto_i8L4R130).add tendsto_i8L4R131k0).add
    tendsto_i8L4R131k1).add tendsto_i8L4R132).add tendsto_i8L4R133)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
