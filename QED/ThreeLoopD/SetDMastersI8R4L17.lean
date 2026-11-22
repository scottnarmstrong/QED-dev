/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L16
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 17

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_155k0_eq`, `QED.ThreeLoopD.tendsto_i8L4RG17` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽155k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S155k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽155k0⁾`. -/
noncomputable def i8L4Q155k0_0 (x r_0001 r_00011 r_001 r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -1 / 2 - 3 / 8 * x ^ 4 - x ^ 5 / 8 + x / 4 + 9 / 8 * x ^ 3 + 19 / 8 * x ^ 2 +
      r_001 * x ^ 4 + r_01 * x ^ 5 + r_011 * x ^ 2 + r_01 ^ 2 * x ^ 7 + r_01 * x ^ 6 / 2 -
      r_001 * x ^ 6 - 32 * r_00011 * x ^ 2 - 12 * r_00101 * x ^ 2 - 4 * r_0001 * x ^ 2 -
      4 * r_0011 * x - 4 * r_0011 * x ^ 3 - 2 * r_01 ^ 2 * x ^ 4 - 2 * r_01 ^ 2 * x ^ 6 +
      2 * r_001 * x ^ 3 + 2 * r_0011 * x ^ 4 + 2 * r_1 ^ 2 * x ^ 4 + 2 * r_1 ^ 2 * x ^ 6 +
      3 * r_01 ^ 2 * x ^ 5 + 7 * r_01 * x ^ 3 + 8 * r_001 * x ^ 2 - 21 / 2 * r_01 * x ^ 2 -
      15 / 4 * r_1 ^ 2 * x ^ 5 - 5 / 2 * r_1 * x ^ 3 - 3 / 2 * r_01 * x ^ 4 - r_1 * x ^ 6 / 2 -
      r_1 ^ 2 * x ^ 7 / 4 + r_1 * x ^ 2 / 4 + 11 / 4 * r_1 * x ^ 4 - 6 * r_001 * r_1 * x ^ 5 -
      2 * r_001 * r_1 * x ^ 7 + 4 * r_001 * r_01 * x ^ 5 + 4 * r_001 * r_1 * x ^ 4 +
      4 * r_001 * r_1 * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽155k0⁾`. -/
noncomputable def i8L4Q155k0_1 (x _r_0001 _r_00011 _r_001 _r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -1 - 2 * x ^ 2 - 15 / 8 * x ^ 3 - x / 2 + x ^ 5 / 8 + r_1 * x ^ 6 / 2 +
      r_1 ^ 2 * x ^ 7 / 2 - r_1 * x ^ 5 - 4 * r_01 * x ^ 2 - 4 * r_1 * x ^ 4 - 2 * r_011 * x ^ 4 -
      2 * r_1 * x ^ 3 - 2 * r_1 ^ 2 * x ^ 6 + 2 * r_1 ^ 2 * x ^ 4 + 4 * r_0011 * x ^ 2 +
      4 * r_011 * x + 4 * r_011 * x ^ 3 - r_1 ^ 2 * x ^ 5 / 2 + 13 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽155k0⁾`. -/
noncomputable def i8L4Q155k0_2 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽155k0⁾`. -/
noncomputable def i8L4Q155k0_3 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽155k0⁾`. -/
noncomputable def i8L4Q155k0_4 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

theorem i8L4_155k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s155k0 x = i8L4S155k0 x + x * (i8L4Q155k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x * i8L4Q155k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q155k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q155k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q155k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s155k0 i8Psi4s155k0N0 i8Psi4s155k0N1 i8Psi4s155k0N2 i8Psi4s155k0N3 i8Psi4s155k0N4
    i8Psi4s155k0W
  simp only [hpl_zero, i13hw_00110 hx, i13hw_010 hx, i13hw_01001 hx, i13hw_0101 hx, i13hw_0110 hx,
    i13hw_10 hx, i13hw_1001 hx, i13hw_101 hx, i13hw_11 hx, i13hw_110 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_00011 h0, i13hpl_rho_001 h0, i8hpl_rho_00101 h0,
    i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S155k0 i8L4Q155k0_0 i8L4Q155k0_1 i8L4Q155k0_2 i8L4Q155k0_3 i8L4Q155k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽155k0⁾`. -/
noncomputable def i8L4R155k0 (x : ℝ) : ℝ :=
  x * (i8L4Q155k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q155k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q155k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q155k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q155k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R155k0 : Tendsto i8L4R155k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q155k0_0 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q155k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q155k0_1 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q155k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q155k0_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q155k0_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R155k0
  unfold i8L4Q155k0_2 i8L4Q155k0_3 i8L4Q155k0_4
  ring

/-- The singular part of `Ψ₄⁽155k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S155k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽155k1⁾`. -/
noncomputable def i8L4Q155k1_0 (x r_00011 r_001 r_00101 r_0011 r_01 _r_011 r_1 : ℝ) : ℝ :=
    -3 / 2 - 11 / 16 * x ^ 3 - x / 4 - x ^ 2 / 8 + x ^ 5 / 16 + 5 / 8 * x ^ 4 +
      r_001 * x ^ 6 - r_001 * x ^ 4 - r_01 * x ^ 5 - r_01 ^ 2 * x ^ 7 - 7 * r_01 * x ^ 3 -
      6 * r_0011 * x ^ 2 - 5 * r_001 * x ^ 2 - 4 * r_1 * x ^ 2 - 3 * r_01 ^ 2 * x ^ 5 -
      2 * r_001 * x ^ 3 - 2 * r_0011 * x ^ 4 + 2 * r_01 ^ 2 * x ^ 4 + 2 * r_01 ^ 2 * x ^ 6 +
      4 * r_0011 * x + 4 * r_0011 * x ^ 3 + 12 * r_00101 * x ^ 2 + 36 * r_00011 * x ^ 2 -
      13 / 4 * r_1 * x ^ 4 - r_01 * x ^ 6 / 2 + r_1 * x ^ 6 / 4 + 3 / 2 * r_01 * x ^ 4 +
      3 / 2 * r_1 * x ^ 5 + 5 / 2 * r_01 * x ^ 2 + 11 / 2 * r_1 * x ^ 3 -
      4 * r_001 * r_01 * x ^ 5 - 4 * r_001 * r_1 * x ^ 4 - 4 * r_001 * r_1 * x ^ 6 +
      2 * r_001 * r_1 * x ^ 7 + 6 * r_001 * r_1 * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽155k1⁾`. -/
noncomputable def i8L4Q155k1_1 (x _r_00011 r_001 _r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    3 + x / 2 - 3 / 2 * x ^ 2 + 3 / 4 * x ^ 3 + r_01 * x ^ 2 + r_1 * x ^ 4 / 2 -
      8 * r_0011 * x ^ 2 - 4 * r_011 * x - 4 * r_011 * x ^ 3 - 2 * r_1 * x ^ 3 +
      2 * r_011 * x ^ 4 + 4 * r_001 * x ^ 2 + 6 * r_011 * x ^ 2 + 3 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽155k1⁾`. -/
noncomputable def i8L4Q155k1_2 (x _r_00011 _r_001 _r_00101 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -1 - x ^ 2 / 4 - x ^ 4 / 4 - x ^ 3 / 8 - x ^ 5 / 8 + r_1 ^ 2 * x ^ 4 + r_1 ^ 2 * x ^ 6 -
      r_1 * x ^ 3 - 2 * r_01 * x ^ 2 + 2 * r_011 * x ^ 2 - 3 / 2 * r_1 ^ 2 * x ^ 5 -
      r_1 * x ^ 6 / 2 - r_1 ^ 2 * x ^ 7 / 2 + 3 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽155k1⁾`. -/
noncomputable def i8L4Q155k1_3 (_x _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽155k1⁾`. -/
noncomputable def i8L4Q155k1_4 (_x _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_155k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s155k1 x = i8L4S155k1 x + x * (i8L4Q155k1_0 x (i13Rho [zero, zero, zero, one, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q155k1_1 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q155k1_2 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q155k1_3 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q155k1_4 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s155k1 i8Psi4s155k1N0 i8Psi4s155k1N1 i8Psi4s155k1N2 i8Psi4s155k1N3 i8Psi4s155k1N4
    i8Psi4s155k1W
  simp only [hpl_zero, i13hw_00, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01010 hx,
    i13hw_01100 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1010 hx, i13hw_1100 hx]
  simp only [i13hpl_rho_00011 h0, i13hpl_rho_001 h0, i8hpl_rho_00101 h0, i13hpl_rho_0011 h0,
    i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S155k1 i8L4Q155k1_0 i8L4Q155k1_1 i8L4Q155k1_2 i8L4Q155k1_3 i8L4Q155k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽155k1⁾`. -/
noncomputable def i8L4R155k1 (x : ℝ) : ℝ :=
  x * (i8L4Q155k1_0 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q155k1_1 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q155k1_2 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q155k1_3 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q155k1_4 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R155k1 : Tendsto i8L4R155k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q155k1_0 (v 0) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v 65))
      (by
      unfold i8L4Q155k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q155k1_1 (v 0) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v 65))
      (by
      unfold i8L4Q155k1_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q155k1_2 (v 0) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v 65))
      (by
      unfold i8L4Q155k1_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q155k1_0 x (i13Rho [zero,
    zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x)
    (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
    [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q155k1_1 x (i13Rho [zero, zero, zero,
      one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho
      [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q155k1_2 x (i13Rho [zero, zero, zero,
      one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho
      [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R155k1
  unfold i8L4Q155k1_3 i8L4Q155k1_4
  ring

/-- The singular part of `Ψ₄⁽156⁾` at `ξ = 0`. -/
noncomputable def i8L4S156 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽156⁾`. -/
noncomputable def i8L4Q156_0 (x r_0011 r_00111 r_01 r_011 r_0111 r_1 : ℝ) : ℝ :=
    -2 * x ^ 4 - 37 / 12 * x ^ 3 - 17 / 6 * x ^ 2 - 7 / 24 * x ^ 5 + x / 3 + x ^ 6 / 12 +
      x ^ 7 / 24 + r_01 * x ^ 2 + r_1 ^ 2 * x ^ 9 / 2 - r_1 ^ 2 * x ^ 8 - 8 * r_00111 * x ^ 2 -
      7 * r_1 * x ^ 5 - 6 * r_011 * x ^ 2 - 4 * r_1 ^ 2 * x ^ 6 + 2 * r_1 * x ^ 3 +
      8 * r_0011 * x ^ 2 + 8 * r_1 ^ 2 * x ^ 5 + 12 * r_0111 * x ^ 2 - 9 / 4 * r_1 * x ^ 6 -
      7 / 2 * r_1 ^ 2 * x ^ 7 - 4 / 3 * r_1 ^ 3 * x ^ 9 - 3 / 2 * r_1 * x ^ 4 -
      r_1 ^ 3 * x ^ 8 / 3 + r_1 ^ 3 * x ^ 10 / 3 + r_1 * x ^ 8 / 4 + 4 / 3 * r_1 ^ 3 * x ^ 7 +
      17 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽156⁾`. -/
noncomputable def i8L4Q156_1 (x _r_0011 _r_00111 _r_01 r_011 r_0111 r_1 : ℝ) : ℝ :=
    x ^ 2 - 5 / 12 * x ^ 3 - 2 / 3 * x - x ^ 4 / 2 - x ^ 5 / 2 - x ^ 6 / 3 - x ^ 7 / 12 -
      r_1 * x ^ 2 - r_1 * x ^ 5 - r_1 * x ^ 7 - r_1 ^ 2 * x ^ 9 - 8 * r_011 * x ^ 2 -
      2 * r_1 ^ 2 * x ^ 6 - 2 * r_1 ^ 3 * x ^ 8 + 3 * r_1 ^ 2 * x ^ 5 + 4 * r_1 * x ^ 3 +
      8 * r_0111 * x ^ 2 - 2 / 3 * r_1 ^ 3 * x ^ 10 - r_1 * x ^ 6 / 2 - r_1 * x ^ 8 / 2 +
      4 / 3 * r_1 ^ 3 * x ^ 7 + 4 / 3 * r_1 ^ 3 * x ^ 9

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽156⁾`. -/
noncomputable def i8L4Q156_2 (_x _r_0011 _r_00111 _r_01 _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽156⁾`. -/
noncomputable def i8L4Q156_3 (_x _r_0011 _r_00111 _r_01 _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽156⁾`. -/
noncomputable def i8L4Q156_4 (_x _r_0011 _r_00111 _r_01 _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_156_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s156 x = i8L4S156 x + x * (i8L4Q156_0 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one,
      one, one] x) (i13Rho [one] x) + Real.log x * i8L4Q156_1 x (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q156_2 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q156_3 x (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q156_4 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s156 i8Psi4s156N0 i8Psi4s156N1 i8Psi4s156N2 i8Psi4s156N3 i8Psi4s156N4 i8Psi4s156W
  simp only [hpl_zero, i13hw_0101 hx, i13hw_0110 hx, i13hw_01101 hx, i13hw_01110 hx, i13hw_10 hx,
    i13hw_101 hx, i13hw_1011 hx, i13hw_11 hx, i13hw_110 hx, i13hw_1101 hx, i13hw_111 hx, i13hw_1110
    hx]
  simp only [i13hpl_rho_0011 h0, i13hpl_rho_00111 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0,
    i13hpl_rho_0111 h0, i13hpl_rho_1 h0]
  unfold i8L4S156 i8L4Q156_0 i8L4Q156_1 i8L4Q156_2 i8L4Q156_3 i8L4Q156_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽156⁾`. -/
noncomputable def i8L4R156 (x : ℝ) : ℝ :=
  x * (i8L4Q156_0 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q156_1 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one, one]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x) (i13Rho
    [one] x) + Real.log x ^ 2 * i8L4Q156_2 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
    one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
    one] x) (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q156_3 x (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [zero, one, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q156_4 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
    (i13Rho [one] x))

theorem tendsto_i8L4R156 : Tendsto i8L4R156 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q156_0 (v 0) (v 12) (v 13) (v 27) (v 29) (v 30) (v 65)) (by
      unfold i8L4Q156_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q156_1 (v 0) (v 12) (v 13) (v 27) (v 29) (v 30) (v 65)) (by
      unfold i8L4Q156_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q156_0 x (i13Rho [zero, zero,
    one, one] x) (i13Rho [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    one] x) (i13Rho [zero, one, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q156_1 x (i13Rho [zero, zero, one, one]
      x) (i13Rho [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R156
  unfold i8L4Q156_2 i8L4Q156_3 i8L4Q156_4
  ring

/-- The singular part of `Ψ₄⁽157⁾` at `ξ = 0`. -/
noncomputable def i8L4S157 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽157⁾`. -/
noncomputable def i8L4Q157_0 (x r_0111 r_01111 r_1 : ℝ) : ℝ :=
    x ^ 2 - 11 / 24 * x ^ 6 - 5 / 16 * x ^ 7 - x ^ 5 / 2 - x ^ 8 / 8 - x ^ 9 / 48 +
      11 / 12 * x ^ 3 - r_1 * x ^ 2 - r_1 * x ^ 7 - r_1 * x ^ 8 - r_1 ^ 2 * x ^ 5 -
      r_1 ^ 2 * x ^ 8 - r_1 ^ 2 * x ^ 10 - r_1 ^ 4 * x ^ 11 - 16 * r_0111 * x ^ 2 +
      2 * r_1 * x ^ 5 + 2 * r_1 ^ 3 * x ^ 8 + 4 * r_1 ^ 2 * x ^ 6 + 16 * r_01111 * x ^ 2 -
      5 / 6 * r_1 * x ^ 6 - 4 / 3 * r_1 ^ 3 * x ^ 9 - 2 / 3 * r_1 * x ^ 9 -
      2 / 3 * r_1 ^ 3 * x ^ 12 - r_1 ^ 2 * x ^ 9 / 2 - r_1 ^ 2 * x ^ 11 / 2 -
      r_1 ^ 4 * x ^ 13 / 3 - r_1 * x ^ 10 / 6 + 2 / 3 * r_1 ^ 4 * x ^ 10 +
      2 / 3 * r_1 ^ 4 * x ^ 12 + 8 / 3 * r_1 * x ^ 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽157⁾`. -/
noncomputable def i8L4Q157_1 (_x _r_0111 _r_01111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽157⁾`. -/
noncomputable def i8L4Q157_2 (_x _r_0111 _r_01111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽157⁾`. -/
noncomputable def i8L4Q157_3 (_x _r_0111 _r_01111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽157⁾`. -/
noncomputable def i8L4Q157_4 (_x _r_0111 _r_01111 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_157_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s157 x = i8L4S157 x + x * (i8L4Q157_0 x (i13Rho [zero, one, one, one] x) (i13Rho [zero,
      one, one, one, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q157_1 x (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, one, one]
      x) (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q157_2 x (i13Rho [zero, one, one, one] x) (i13Rho
      [zero, one, one, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q157_3 x (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, one,
      one] x) (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q157_4 x (i13Rho [zero, one, one, one] x)
      (i13Rho [zero, one, one, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s157 i8Psi4s157N0 i8Psi4s157N1 i8Psi4s157N2 i8Psi4s157N3 i8Psi4s157N4 i8Psi4s157W
  simp only [i13hw_11 hx, i13hw_111 hx, i13hw_1111 hx]
  simp only [i13hpl_rho_0111 h0, i8hpl_rho_01111 h0, i13hpl_rho_1 h0]
  unfold i8L4S157 i8L4Q157_0 i8L4Q157_1 i8L4Q157_2 i8L4Q157_3 i8L4Q157_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽157⁾`. -/
noncomputable def i8L4R157 (x : ℝ) : ℝ :=
  x * (i8L4Q157_0 x (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, one, one] x) (i13Rho
    [one] x) + Real.log x * i8L4Q157_1 x (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one,
    one, one] x) (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q157_2 x (i13Rho [zero, one, one, one] x)
    (i13Rho [zero, one, one, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q157_3 x (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, one,
    one] x) (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q157_4 x (i13Rho [zero, one, one, one] x)
    (i13Rho [zero, one, one, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R157 : Tendsto i8L4R157 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q157_0 (v 0) (v 30) (v 31) (v 65)) (by
      unfold i8L4Q157_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q157_0 x (i13Rho [zero, one,
    one, one] x) (i13Rho [zero, one, one, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R157
  unfold i8L4Q157_1 i8L4Q157_2 i8L4Q157_3 i8L4Q157_4
  ring

/-- The singular part of `-A₄` at `ξ = 0`. -/
noncomputable def i8L4SP (x : ℝ) : ℝ :=
    (-473 - 393 * Real.log x + 11 * π ^ 2 + 28 * zeta3 + 160 * x - 297 / 2 * Real.log x ^ 2 -
      63 / 2 * Real.log x ^ 3 - 27 / 8 * Real.log x ^ 4 + π ^ 2 ^ 2 / 45 - 32 * x * zeta3 -
      8 * π ^ 2 * x + 7 * Real.log x * π ^ 2 + 12 * Real.log x * zeta3 - 2 / 45 * x * π ^ 2 ^ 2 +
      3 / 2 * π ^ 2 * Real.log x ^ 2 + 107 / 16 * x * Real.log x ^ 4 +
      179 / 120 * x * Real.log x ^ 5 + 479 / 24 * x * Real.log x ^ 3 +
      519 / 16 * Real.log x * x + 597 / 16 * x * Real.log x ^ 2 - 14 * Real.log x * x * zeta3 -
      10 * x * zeta3 * Real.log x ^ 2 - 47 / 12 * Real.log x * π ^ 2 * x -
      19 / 18 * π ^ 2 * x * Real.log x ^ 3 - 11 / 4 * π ^ 2 * x * Real.log x ^ 2 +
      Real.log x * x * π ^ 2 ^ 2 / 30) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `-A₄`. -/
noncomputable def i8L4QP_0 (x r_1 : ℝ) : ℝ :=
    -1657 / 8 + 12 * zeta3 - 8971 / 60 * x ^ 4 - 3939 / 16 * x ^ 3 - 3439 / 12 * x ^ 2 -
      1605 / 16 * x + 4 / 45 * π ^ 2 ^ 2 + 25 / 6 * π ^ 2 + 67 / 24 * x ^ 5 +
      179 / 120 * x ^ 9 + 277 / 24 * x ^ 8 + 1367 / 24 * x ^ 6 + 1889 / 48 * x ^ 7 -
      786 * r_1 * x - 594 * r_1 ^ 2 * x ^ 4 - 308 * r_1 * x ^ 5 - 252 * r_1 ^ 3 * x ^ 7 -
      169 * r_1 ^ 2 * x ^ 6 - 54 * r_1 ^ 4 * x ^ 10 - 30 * x * zeta3 - 28 * zeta3 * x ^ 2 -
      10 * zeta3 * x ^ 3 + 68 * r_1 ^ 3 * x ^ 9 + 107 * r_1 ^ 4 * x ^ 11 +
      277 * r_1 ^ 2 * x ^ 10 - 651 / 2 * r_1 * x ^ 3 - 511 / 4 * r_1 * x ^ 4 -
      113 / 12 * π ^ 2 * x ^ 3 - 89 / 18 * π ^ 2 * x ^ 2 - 29 / 6 * π ^ 2 * x ^ 4 -
      19 / 18 * π ^ 2 * x ^ 5 - 11 / 12 * π ^ 2 * x + x * π ^ 2 ^ 2 / 30 +
      179 / 3 * r_1 ^ 2 * x ^ 11 + 179 / 12 * r_1 * x ^ 10 + 251 / 2 * r_1 ^ 2 * x ^ 7 +
      277 / 3 * r_1 * x ^ 9 + 341 / 12 * r_1 * x ^ 6 + 358 / 3 * r_1 ^ 3 * x ^ 12 +
      358 / 3 * r_1 ^ 4 * x ^ 13 + 479 / 3 * r_1 ^ 3 * x ^ 8 + 499 / 2 * r_1 * x ^ 8 +
      519 / 8 * r_1 * x ^ 2 + 554 / 3 * r_1 ^ 4 * x ^ 12 + 597 / 4 * r_1 ^ 2 * x ^ 5 +
      716 / 15 * r_1 ^ 5 * x ^ 14 + 775 / 3 * r_1 * x ^ 7 + 1009 / 3 * r_1 ^ 2 * x ^ 8 +
      1105 / 2 * r_1 ^ 2 * x ^ 9 + 1108 / 3 * r_1 ^ 3 * x ^ 11 + 1426 / 3 * r_1 ^ 3 * x ^ 10 -
      56 * r_1 * zeta3 * x ^ 3 - 40 * r_1 * zeta3 * x ^ 4 - 40 * zeta3 * r_1 ^ 2 * x ^ 5 -
      28 * r_1 * zeta3 * x ^ 2 - 11 * π ^ 2 * r_1 ^ 2 * x ^ 5 - 2 * π ^ 2 * r_1 * x ^ 3 +
      6 * π ^ 2 * r_1 ^ 2 * x ^ 4 + 14 * π ^ 2 * r_1 * x + 24 * r_1 * x * zeta3 -
      76 / 9 * π ^ 2 * r_1 ^ 3 * x ^ 8 - 73 / 3 * π ^ 2 * r_1 * x ^ 4 -
      58 / 3 * π ^ 2 * r_1 * x ^ 5 - 58 / 3 * π ^ 2 * r_1 ^ 2 * x ^ 6 -
      47 / 6 * π ^ 2 * r_1 * x ^ 2 - 38 / 3 * π ^ 2 * r_1 ^ 2 * x ^ 7 -
      19 / 3 * π ^ 2 * r_1 * x ^ 6 + r_1 * π ^ 2 ^ 2 * x ^ 2 / 15

/-- The coefficient of `ξ log^1 ξ` in the regular part of `-A₄`. -/
noncomputable def i8L4QP_1 (x r_1 : ℝ) : ℝ :=
    -651 / 4 - π ^ 2 - 154 * x ^ 2 - 28 * zeta3 - 511 / 8 * x + 179 / 24 * x ^ 7 +
      277 / 6 * x ^ 6 + 341 / 24 * x ^ 3 + 499 / 4 * x ^ 5 + 775 / 6 * x ^ 4 - 594 * r_1 * x -
      378 * r_1 ^ 2 * x ^ 4 - 169 * r_1 * x ^ 3 - 108 * r_1 ^ 3 * x ^ 7 - 20 * x * zeta3 +
      102 * r_1 ^ 2 * x ^ 6 + 179 * r_1 ^ 2 * x ^ 9 + 214 * r_1 ^ 3 * x ^ 8 +
      277 * r_1 * x ^ 7 + 554 * r_1 ^ 2 * x ^ 8 + 713 * r_1 ^ 2 * x ^ 7 - 73 / 6 * π ^ 2 * x -
      29 / 3 * π ^ 2 * x ^ 2 - 19 / 6 * π ^ 2 * x ^ 3 + 179 / 3 * r_1 * x ^ 8 +
      251 / 2 * r_1 * x ^ 4 + 358 / 3 * r_1 ^ 4 * x ^ 11 + 479 / 2 * r_1 ^ 2 * x ^ 5 +
      597 / 4 * r_1 * x ^ 2 + 716 / 3 * r_1 ^ 3 * x ^ 10 + 1009 / 3 * r_1 * x ^ 5 +
      1105 / 2 * r_1 * x ^ 6 + 1108 / 3 * r_1 ^ 3 * x ^ 9 - 40 * r_1 * zeta3 * x ^ 2 -
      11 * π ^ 2 * r_1 * x ^ 2 + 6 * π ^ 2 * r_1 * x - 58 / 3 * π ^ 2 * r_1 * x ^ 3 -
      38 / 3 * π ^ 2 * r_1 * x ^ 4 - 38 / 3 * π ^ 2 * r_1 ^ 2 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `-A₄`. -/
noncomputable def i8L4QP_2 (x r_1 : ℝ) : ℝ :=
    -169 / 4 - 29 / 6 * π ^ 2 + 179 / 12 * x ^ 5 + 251 / 8 * x + 277 / 4 * x ^ 4 +
      1009 / 12 * x ^ 2 + 1105 / 8 * x ^ 3 - 189 * r_1 * x - 81 * r_1 ^ 2 * x ^ 4 +
      51 * r_1 * x ^ 3 + 179 * r_1 ^ 2 * x ^ 7 + 277 * r_1 * x ^ 5 + 277 * r_1 ^ 2 * x ^ 6 -
      19 / 6 * π ^ 2 * x + 179 / 2 * r_1 * x ^ 6 + 321 / 2 * r_1 ^ 2 * x ^ 5 +
      358 / 3 * r_1 ^ 3 * x ^ 8 + 479 / 4 * r_1 * x ^ 2 + 713 / 2 * r_1 * x ^ 4 -
      19 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `-A₄`. -/
noncomputable def i8L4QP_3 (x r_1 : ℝ) : ℝ :=
    17 / 2 + 179 / 12 * x ^ 3 + 277 / 6 * x ^ 2 + 713 / 12 * x - 27 * r_1 * x +
      107 / 2 * r_1 * x ^ 2 + 179 / 3 * r_1 * x ^ 4 + 179 / 3 * r_1 ^ 2 * x ^ 5 +
      277 / 3 * r_1 * x ^ 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `-A₄`. -/
noncomputable def i8L4QP_4 (x r_1 : ℝ) : ℝ :=
    277 / 24 + 179 / 24 * x + 179 / 12 * r_1 * x ^ 2

theorem i8L4_P_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    -i8Prim4x x = i8L4SP x + x * (i8L4QP_0 x (i13Rho [one] x) +
      Real.log x * i8L4QP_1 x (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4QP_2 x (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4QP_3 x (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4QP_4 x (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Prim4x
  simp only [i13_log_one_sub_eq hx]
  simp only [i13hpl_rho_1 h0]
  unfold i8L4SP i8L4QP_0 i8L4QP_1 i8L4QP_2 i8L4QP_3 i8L4QP_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `-A₄`. -/
noncomputable def i8L4RP (x : ℝ) : ℝ :=
  x * (i8L4QP_0 x (i13Rho [one] x) + Real.log x * i8L4QP_1 x (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4QP_2 x (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4QP_3 x (i13Rho [one] x) + Real.log x ^ 4 * i8L4QP_4 x (i13Rho [one] x))

theorem tendsto_i8L4RP : Tendsto i8L4RP (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4QP_0 (v 0) (v 65)) (by
      unfold i8L4QP_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4QP_1 (v 0) (v 65)) (by
      unfold i8L4QP_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4QP_2 (v 0) (v 65)) (by
      unfold i8L4QP_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4QP_3 (v 0) (v 65)) (by
      unfold i8L4QP_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4QP_4 (v 0) (v 65)) (by
      unfold i8L4QP_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4QP_0 x (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4QP_1 x (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4QP_2 x (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4QP_3 x (i13Rho [one] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4QP_4 x (i13Rho [one] x))
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4RP
  ring

/-- The regular parts of group 17. -/
noncomputable def i8L4RG17 (x : ℝ) : ℝ :=
  i8L4R155k0 x + i8L4R155k1 x + i8L4R156 x + i8L4R157 x + i8L4RP x

theorem tendsto_i8L4RG17 : Tendsto i8L4RG17 (𝓝[>] 0) (𝓝 0) := by
  have H := ((((tendsto_i8L4R155k0.add tendsto_i8L4R155k1).add tendsto_i8L4R156).add
    tendsto_i8L4R157).add tendsto_i8L4RP)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
