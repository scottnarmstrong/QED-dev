/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L15
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 16

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_146k2_eq`, `QED.ThreeLoopD.tendsto_i8L4RG16` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽146k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S146k2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽146k2⁾`. -/
noncomputable def i8L4Q146k2_0 (x r_0011m r_001m r_001m1 r_00m r_00m1 r_00m11 r_01 r_011m r_01m
    r_01m1 r_0m r_0m011 r_0m1 r_0m101 r_0m11 r_1 r_m r_m1 _r_m11 : ℝ) : ℝ :=
    -1 + x ^ 4 + 2 * r_011m + 2 * r_01m1 + 4 * r_0m11 - 3 / 2 * x ^ 3 - x / 2 + x ^ 2 / 4 +
      3 / 8 * x ^ 5 + r_01m * x ^ 2 + r_0m1 * x ^ 6 + r_1 * x ^ 5 / 2 - r_0m1 * x ^ 2 -
      r_0m1 * x ^ 4 - 8 * r_m1 * x ^ 2 - 7 * r_m * x ^ 2 - 6 * r_0m1 * x ^ 3 - 4 * r_0m1 * x -
      4 * r_0m11 * x ^ 4 - 4 * r_1 * x ^ 4 - 2 * r_001m * x ^ 2 - 2 * r_00m * x ^ 2 -
      2 * r_01 * x ^ 4 - 2 * r_011m * x ^ 4 - 2 * r_01m1 * x ^ 4 - 2 * r_m * x ^ 3 +
      2 * r_00m1 * x ^ 2 + 2 * r_01 * x ^ 2 + 2 * r_0m1 * x ^ 5 + 7 * r_1 * x ^ 3 +
      8 * r_0m101 * x ^ 2 + 16 * r_0011m * x ^ 2 + 16 * r_001m1 * x ^ 2 + 16 * r_0m011 * x ^ 2 +
      32 * r_00m11 * x ^ 2 - 17 / 4 * r_1 * x ^ 2 - 3 / 2 * r_m * x ^ 5 - r_0m * x ^ 2 / 2 -
      r_m * x ^ 4 / 4 - r_m * x ^ 6 / 4 + 3 / 4 * r_1 * x ^ 6 - 8 * r_01 * r_0m1 * x ^ 5 -
      2 * r_0m1 * r_1 * x ^ 3 - 2 * r_1 * r_m * x ^ 4 - 2 * r_1 * r_m * x ^ 6 +
      2 * r_0m1 * r_1 * x ^ 7 - r_1 * r_m * x ^ 7 / 2 + 9 / 2 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽146k2⁾`. -/
noncomputable def i8L4Q146k2_1 (x _r_0011m _r_001m _r_001m1 _r_00m _r_00m1 _r_00m11 _r_01 r_011m
    r_01m _r_01m1 r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 r_1 r_m r_m1 r_m11 : ℝ) : ℝ :=
    1 + x - 2 * r_m11 - x ^ 4 / 2 - x ^ 5 / 4 - x ^ 6 / 4 - x ^ 7 / 8 + 3 / 4 * x ^ 2 +
      5 / 8 * x ^ 3 + r_m * x ^ 7 + r_1 ^ 2 * x ^ 8 + r_1 * x ^ 6 / 2 + r_1 ^ 2 * x ^ 5 / 2 -
      r_m1 * x ^ 4 - r_m1 * x ^ 6 - r_1 ^ 2 * x ^ 4 - 8 * r_011m * x ^ 2 - 3 * r_1 * x ^ 2 -
      2 * r_m1 * x ^ 3 - 2 * r_m1 * x ^ 5 + 2 * r_01m * x ^ 2 + 2 * r_0m * x ^ 2 +
      2 * r_m * x ^ 5 + 2 * r_m1 * x ^ 2 + 2 * r_m11 * x ^ 4 + 3 * r_1 * x ^ 4 + 4 * r_m1 * x -
      r_1 * x ^ 8 / 2 - r_m * x ^ 2 / 2 - r_1 ^ 2 * x ^ 9 / 2 + r_m * x ^ 8 / 4 +
      3 / 2 * r_m * x ^ 6 + 7 / 4 * r_m * x ^ 4 + r_1 * r_m * x ^ 7 + r_1 * r_m * x ^ 9 +
      r_m * r_1 ^ 2 * x ^ 10 - r_m * r_1 ^ 2 * x ^ 6 - 4 * r_1 * r_m * x ^ 4 -
      2 * r_1 * r_m * x ^ 5 - 2 * r_1 * r_m1 * x ^ 7 + 2 * r_1 * r_m * x ^ 6 +
      2 * r_1 * r_m * x ^ 8 + 2 * r_1 * r_m1 * x ^ 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽146k2⁾`. -/
noncomputable def i8L4Q146k2_2 (_x _r_0011m _r_001m _r_001m1 _r_00m _r_00m1 _r_00m11 _r_01 _r_011m
    _r_01m _r_01m1 _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽146k2⁾`. -/
noncomputable def i8L4Q146k2_3 (_x _r_0011m _r_001m _r_001m1 _r_00m _r_00m1 _r_00m11 _r_01 _r_011m
    _r_01m _r_01m1 _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽146k2⁾`. -/
noncomputable def i8L4Q146k2_4 (_x _r_0011m _r_001m _r_001m1 _r_00m _r_00m1 _r_00m11 _r_01 _r_011m
    _r_01m _r_01m1 _r_0m _r_0m011 _r_0m1 _r_0m101 _r_0m11 _r_1 _r_m _r_m1 _r_m11 : ℝ) : ℝ :=
    0

theorem i8L4_146k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s146k2 x = i8L4S146k2 x + x * (i8L4Q146k2_0 x (i13Rho [zero, zero, one, one, negOne] x)
      (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)
      (i13Rho [negOne, one, one] x) +
      Real.log x * i8L4Q146k2_1 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one,
      one] x) + Real.log x ^ 2 * i8L4Q146k2_2 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho
      [zero, zero, one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero,
      one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)
      (i13Rho [negOne, one, one] x) + Real.log x ^ 3 * i8L4Q146k2_3 x (i13Rho [zero, zero, one, one,
      negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
      negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, one, one] x) +
      Real.log x ^ 4 * i8L4Q146k2_4 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one,
      one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one,
      one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s146k2 i8Psi4s146k2N0 i8Psi4s146k2N1 i8Psi4s146k2N2 i8Psi4s146k2N3 i8Psi4s146k2N4
    i8Psi4s146k2W
  simp only [hpl_zero, i13hw_010m hx, i13hw_011m0 hx, i13hw_01m0 hx, i13hw_0m0 hx, i13hw_101m hx,
    i13hw_10m hx, i13hw_10m1 hx, i13hw_110m hx, i13hw_11m0 hx, i13hw_1m hx, i13hw_1m0 hx, i13hw_m0
    hx, i8hw_010m1 hx, i8hw_0110m hx]
  simp only [i8hpl_rho_0011m h0, i13hpl_rho_001m h0, i8hpl_rho_001m1 h0, i13hpl_rho_00m h0,
    i13hpl_rho_00m1 h0, i8hpl_rho_00m11 h0, i13hpl_rho_01 h0, i13hpl_rho_011m h0, i13hpl_rho_01m h0,
    i13hpl_rho_01m1 h0, i13hpl_rho_0m h0, i13hpl_rho_0m011 h0, i13hpl_rho_0m1 h0, i8hpl_rho_0m101
    h0, i13hpl_rho_0m11 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0, i8hpl_rho_m11 h0]
  unfold i8L4S146k2 i8L4Q146k2_0 i8L4Q146k2_1 i8L4Q146k2_2 i8L4Q146k2_3 i8L4Q146k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽146k2⁾`. -/
noncomputable def i8L4R146k2 (x : ℝ) : ℝ :=
  x * (i8L4Q146k2_0 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, one, negOne] x)
    (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x * i8L4Q146k2_1 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero, one,
    negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne,
    one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x) +
    Real.log x ^ 2 * i8L4Q146k2_2 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero, zero,
    one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one]
    x) + Real.log x ^ 3 * i8L4Q146k2_3 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one]
    x) + Real.log x ^ 4 * i8L4Q146k2_4 x (i13Rho [zero, zero, one, one, negOne] x) (i13Rho [zero,
    zero, one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero, negOne, one, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero, one] x) (i13Rho [zero, negOne, one,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, one, one]
    x))

theorem tendsto_i8L4R146k2 : Tendsto i8L4R146k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q146k2_0 (v 0) (v 14) (v 15) (v 16) (v 18) (v 21) (v 22) (v 27)
      (v 33) (v 36) (v 37) (v 43) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q146k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q146k2_1 (v 0) (v 14) (v 15) (v 16) (v 18) (v 21) (v 22) (v 27)
      (v 33) (v 36) (v 37) (v 43) (v 45) (v 49) (v 50) (v 51) (v 65) (v 66) (v 67) (v 68)) (by
      unfold i8L4Q146k2_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q146k2_0 x (i13Rho [zero,
    zero, one, one, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, one,
    negOne, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
    [zero, zero, negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    one, zero, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) (i13Rho [negOne, one, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q146k2_1 x (i13Rho [zero, zero, one,
      one, negOne] x) (i13Rho [zero, zero, one, negOne] x) (i13Rho [zero, zero, one, negOne, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
      negOne, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, zero,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) (i13Rho [negOne, one, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R146k2
  unfold i8L4Q146k2_2 i8L4Q146k2_3 i8L4Q146k2_4
  ring

/-- The singular part of `Ψ₄⁽147⁾` at `ξ = 0`. -/
noncomputable def i8L4S147 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽147⁾`. -/
noncomputable def i8L4Q147_0 (x r_011 r_0111 r_1 : ℝ) : ℝ :=
    x ^ 2 - 5 / 12 * x ^ 3 - 2 / 3 * x - x ^ 4 / 2 - x ^ 5 / 2 - x ^ 6 / 3 - x ^ 7 / 12 -
      r_1 * x ^ 2 - r_1 * x ^ 5 - r_1 * x ^ 7 - r_1 ^ 2 * x ^ 9 - 8 * r_011 * x ^ 2 -
      2 * r_1 ^ 2 * x ^ 6 - 2 * r_1 ^ 3 * x ^ 8 + 3 * r_1 ^ 2 * x ^ 5 + 4 * r_1 * x ^ 3 +
      8 * r_0111 * x ^ 2 - 2 / 3 * r_1 ^ 3 * x ^ 10 - r_1 * x ^ 6 / 2 - r_1 * x ^ 8 / 2 +
      4 / 3 * r_1 ^ 3 * x ^ 7 + 4 / 3 * r_1 ^ 3 * x ^ 9

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽147⁾`. -/
noncomputable def i8L4Q147_1 (_x _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽147⁾`. -/
noncomputable def i8L4Q147_2 (_x _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽147⁾`. -/
noncomputable def i8L4Q147_3 (_x _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽147⁾`. -/
noncomputable def i8L4Q147_4 (_x _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_147_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s147 x = i8L4S147 x + x * (i8L4Q147_0 x (i13Rho [zero, one, one] x) (i13Rho [zero, one,
      one, one] x) (i13Rho [one] x) + Real.log x * i8L4Q147_1 x (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q147_2 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q147_3 x (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q147_4 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s147 i8Psi4s147N0 i8Psi4s147N1 i8Psi4s147N2 i8Psi4s147N3 i8Psi4s147N4 i8Psi4s147W
  simp only [i13hw_11 hx, i13hw_111 hx]
  simp only [i13hpl_rho_011 h0, i13hpl_rho_0111 h0, i13hpl_rho_1 h0]
  unfold i8L4S147 i8L4Q147_0 i8L4Q147_1 i8L4Q147_2 i8L4Q147_3 i8L4Q147_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽147⁾`. -/
noncomputable def i8L4R147 (x : ℝ) : ℝ :=
  x * (i8L4Q147_0 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q147_1 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x) (i13Rho
    [one] x) + Real.log x ^ 2 * i8L4Q147_2 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
    one] x) (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q147_3 x (i13Rho [zero, one, one] x) (i13Rho
    [zero, one, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q147_4 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
    (i13Rho [one] x))

theorem tendsto_i8L4R147 : Tendsto i8L4R147 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q147_0 (v 0) (v 29) (v 30) (v 65)) (by
      unfold i8L4Q147_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q147_0 x (i13Rho [zero, one,
    one] x) (i13Rho [zero, one, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R147
  unfold i8L4Q147_1 i8L4Q147_2 i8L4Q147_3 i8L4Q147_4
  ring

/-- The singular part of `Ψ₄⁽148k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S148k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽148k0⁾`. -/
noncomputable def i8L4Q148k0_0 (x r_011 r_0111 r_0111m r_011m r_011m1 r_01m r_01m1 r_01m11 r_0m1
    r_0m11 r_0m111 r_1 r_m r_m1 : ℝ) : ℝ :=
    x ^ 4 - 13 / 3 * x ^ 2 - x ^ 7 / 6 - x ^ 8 / 6 - x ^ 9 / 24 + 2 / 3 * x + 3 / 8 * x ^ 5 +
      11 / 3 * x ^ 3 + r_1 ^ 2 * x ^ 9 + r_1 * x ^ 7 / 2 + r_m * x ^ 9 / 2 - r_m * x ^ 4 -
      20 * r_1 * x ^ 3 - 16 * r_0111m * x ^ 2 - 16 * r_011m1 * x ^ 2 - 16 * r_01m11 * x ^ 2 -
      16 * r_0m111 * x ^ 2 - 5 * r_1 ^ 2 * x ^ 5 - 4 * r_0111 * x ^ 2 + 4 * r_011m * x ^ 2 +
      4 * r_01m * x ^ 2 + 4 * r_01m1 * x ^ 2 + 4 * r_0m1 * x ^ 2 + 4 * r_0m11 * x ^ 2 +
      4 * r_1 * x ^ 5 + 4 * r_m * x ^ 5 + 5 * r_1 * x ^ 4 + 8 * r_011 * x ^ 2 +
      12 * r_m1 * x ^ 2 - 8 / 3 * r_m * x ^ 3 - 4 / 3 * r_1 ^ 3 * x ^ 7 - r_1 * x ^ 9 / 2 -
      r_1 ^ 2 * x ^ 11 / 2 - r_1 ^ 3 * x ^ 10 / 3 - r_1 ^ 3 * x ^ 12 / 3 - r_1 * x ^ 10 / 4 +
      r_1 * x ^ 8 / 4 + r_m * x ^ 10 / 12 + 2 / 3 * r_1 ^ 3 * x ^ 8 + 2 / 3 * r_1 ^ 3 * x ^ 9 +
      2 / 3 * r_1 ^ 3 * x ^ 11 + 5 / 2 * r_1 * x ^ 6 + 5 / 4 * r_m * x ^ 8 +
      9 / 2 * r_1 ^ 2 * x ^ 7 + 13 / 2 * r_m * x ^ 2 + 13 / 6 * r_m * x ^ 7 +
      17 / 2 * r_1 * x ^ 2 + 19 / 6 * r_m * x ^ 6 + r_m * r_1 ^ 2 * x ^ 10 +
      r_m * r_1 ^ 2 * x ^ 12 + r_1 * r_m * x ^ 11 / 2 - 13 * r_1 * r_m * x ^ 5 -
      4 * r_m * r_1 ^ 2 * x ^ 7 - 2 * r_m * r_1 ^ 2 * x ^ 8 + 2 * r_1 * r_m * x ^ 10 +
      2 * r_m * r_1 ^ 2 * x ^ 9 + 2 * r_m * r_1 ^ 2 * x ^ 11 + 3 * r_1 * r_m * x ^ 9 +
      4 * r_1 * r_m * x ^ 8 - 2 / 3 * r_m * r_1 ^ 3 * x ^ 9 + 2 / 3 * r_m * r_1 ^ 3 * x ^ 13 +
      7 / 2 * r_1 * r_m * x ^ 7

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽148k0⁾`. -/
noncomputable def i8L4Q148k0_1 (_x _r_011 _r_0111 _r_0111m _r_011m _r_011m1 _r_01m _r_01m1 _r_01m11
    _r_0m1 _r_0m11 _r_0m111 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽148k0⁾`. -/
noncomputable def i8L4Q148k0_2 (_x _r_011 _r_0111 _r_0111m _r_011m _r_011m1 _r_01m _r_01m1 _r_01m11
    _r_0m1 _r_0m11 _r_0m111 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽148k0⁾`. -/
noncomputable def i8L4Q148k0_3 (_x _r_011 _r_0111 _r_0111m _r_011m _r_011m1 _r_01m _r_01m1 _r_01m11
    _r_0m1 _r_0m11 _r_0m111 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽148k0⁾`. -/
noncomputable def i8L4Q148k0_4 (_x _r_011 _r_0111 _r_0111m _r_011m _r_011m1 _r_01m _r_01m1 _r_01m11
    _r_0m1 _r_0m11 _r_0m111 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_148k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s148k0 x = i8L4S148k0 x + x * (i8L4Q148k0_0 x (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, one, negOne] x) (i13Rho [zero, one, one, negOne] x)
      (i13Rho [zero, one, one, negOne, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, one] x) (i13Rho [zero, one, negOne, one, one] x) (i13Rho [zero, negOne, one] x)
      (i13Rho [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, one, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q148k0_1 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
      (i13Rho [zero, one, one, one, negOne] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
      one, one, negOne, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, one, negOne, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 2 * i8L4Q148k0_2 x (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, one, negOne] x) (i13Rho [zero, one, one,
      negOne] x) (i13Rho [zero, one, one, negOne, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, one, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q148k0_3 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
      (i13Rho [zero, one, one, one, negOne] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero,
      one, one, negOne, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x)
      (i13Rho [zero, one, negOne, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 4 * i8L4Q148k0_4 x (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, one, negOne] x) (i13Rho [zero, one, one,
      negOne] x) (i13Rho [zero, one, one, negOne, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, one, one] x) (i13Rho [zero, negOne,
      one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, one, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s148k0 i8Psi4s148k0N0 i8Psi4s148k0N1 i8Psi4s148k0N2 i8Psi4s148k0N3 i8Psi4s148k0N4
    i8Psi4s148k0W
  simp only [i13hw_11 hx, i13hw_111 hx, i13hw_11m hx, i13hw_1m hx, i13hw_1m1 hx, i8hw_111m
    hx, i8hw_11m1 hx, i8hw_1m11 hx]
  simp only [i13hpl_rho_011 h0, i13hpl_rho_0111 h0, i8hpl_rho_0111m h0, i13hpl_rho_011m h0,
    i8hpl_rho_011m1 h0, i13hpl_rho_01m h0, i13hpl_rho_01m1 h0, i8hpl_rho_01m11 h0, i13hpl_rho_0m1
    h0, i13hpl_rho_0m11 h0, i8hpl_rho_0m111 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S148k0 i8L4Q148k0_0 i8L4Q148k0_1 i8L4Q148k0_2 i8L4Q148k0_3 i8L4Q148k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽148k0⁾`. -/
noncomputable def i8L4R148k0 (x : ℝ) : ℝ :=
  x * (i8L4Q148k0_0 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x) (i13Rho [zero,
    one, one, one, negOne] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, one, negOne,
    one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one,
    negOne, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho
    [zero, negOne, one, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q148k0_1 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x) (i13Rho
    [zero, one, one, one, negOne] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, one,
    negOne, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
    [zero, one, negOne, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one]
    x) (i13Rho [zero, negOne, one, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x ^ 2 * i8L4Q148k0_2 x (i13Rho [zero, one, one] x) (i13Rho [zero,
    one, one, one] x) (i13Rho [zero, one, one, one, negOne] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, one, negOne, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, one, negOne, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q148k0_3 x (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
    (i13Rho [zero, one, one, one, negOne] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
    one, negOne, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho
    [zero, one, negOne, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one]
    x) (i13Rho [zero, negOne, one, one, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x ^ 4 * i8L4Q148k0_4 x (i13Rho [zero, one, one] x) (i13Rho [zero,
    one, one, one] x) (i13Rho [zero, one, one, one, negOne] x) (i13Rho [zero, one, one, negOne] x)
    (i13Rho [zero, one, one, negOne, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, one] x) (i13Rho [zero, one, negOne, one, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, one, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R148k0 : Tendsto i8L4R148k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q148k0_0 (v 0) (v 29) (v 30) (v 32) (v 33) (v 34) (v 36) (v 37)
      (v 38) (v 49) (v 51) (v 52) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q148k0_0
      fun_prop)
  have H := (i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q148k0_0 x (i13Rho [zero, one,
    one] x) (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, one, negOne] x) (i13Rho [zero,
    one, one, negOne] x) (i13Rho [zero, one, one, negOne, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, one, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, one, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩)
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R148k0
  unfold i8L4Q148k0_1 i8L4Q148k0_2 i8L4Q148k0_3 i8L4Q148k0_4
  ring

/-- The singular part of `Ψ₄⁽149⁾` at `ξ = 0`. -/
noncomputable def i8L4S149 (x : ℝ) : ℝ :=
    (12 + 2 * Real.log x ^ 3 + 6 * Real.log x ^ 2 + 12 * Real.log x + Real.log x ^ 4 / 3 -
      x * Real.log x ^ 5 / 15 + x * Real.log x ^ 4 / 6) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽149⁾`. -/
noncomputable def i8L4Q149_0 (x : ℝ) : ℝ :=
    4 + x / 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽149⁾`. -/
noncomputable def i8L4Q149_1 (x : ℝ) : ℝ :=
    -4 - x

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽149⁾`. -/
noncomputable def i8L4Q149_2 (x : ℝ) : ℝ :=
    2 + x

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽149⁾`. -/
noncomputable def i8L4Q149_3 (x : ℝ) : ℝ :=
    -2 / 3 - 2 / 3 * x

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽149⁾`. -/
noncomputable def i8L4Q149_4 (x : ℝ) : ℝ :=
    1 / 3 + x / 6

theorem i8L4_149_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s149 x = i8L4S149 x + x * (i8L4Q149_0 x + Real.log x * i8L4Q149_1 x +
      Real.log x ^ 2 * i8L4Q149_2 x + Real.log x ^ 3 * i8L4Q149_3 x +
      Real.log x ^ 4 * i8L4Q149_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s149 i8Psi4s149N0 i8Psi4s149N1 i8Psi4s149N2 i8Psi4s149N3 i8Psi4s149N4 i8Psi4s149W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00000]

  unfold i8L4S149 i8L4Q149_0 i8L4Q149_1 i8L4Q149_2 i8L4Q149_3 i8L4Q149_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽149⁾`. -/
noncomputable def i8L4R149 (x : ℝ) : ℝ :=
  x * (i8L4Q149_0 x + Real.log x * i8L4Q149_1 x + Real.log x ^ 2 * i8L4Q149_2 x +
    Real.log x ^ 3 * i8L4Q149_3 x + Real.log x ^ 4 * i8L4Q149_4 x)

theorem tendsto_i8L4R149 : Tendsto i8L4R149 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q149_0 (v 0)) (by
      unfold i8L4Q149_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q149_1 (v 0)) (by
      unfold i8L4Q149_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q149_2 (v 0)) (by
      unfold i8L4Q149_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q149_3 (v 0)) (by
      unfold i8L4Q149_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q149_4 (v 0)) (by
      unfold i8L4Q149_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q149_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q149_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q149_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q149_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4Q149_4 x)
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R149
  ring

/-- The singular part of `Ψ₄⁽150⁾` at `ξ = 0`. -/
noncomputable def i8L4S150 (x : ℝ) : ℝ :=
    20 - 4 / 3 * Real.log x ^ 3 - Real.log x ^ 4 / 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽150⁾`. -/
noncomputable def i8L4Q150_0 (x r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    22 - 45 / 8 * x - 15 / 4 * x ^ 2 - 7 / 8 * x ^ 3 - 9 * r_001 * x ^ 2 - 4 * r_1 * x ^ 3 +
      12 * r_00001 * x ^ 2 + 20 * r_1 * x + 38 * r_0001 * x ^ 2 - 57 / 4 * r_1 * x ^ 2 -
      7 / 4 * r_1 * x ^ 4 + 55 / 2 * r_01 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽150⁾`. -/
noncomputable def i8L4Q150_1 (x _r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -22 - 35 / 4 * x + 7 / 4 * x ^ 3 + 11 / 2 * x ^ 2 - 38 * r_001 * x ^ 2 - 12 * r_0001 * x ^ 2 +
      4 * r_1 * x ^ 3 + 9 * r_01 * x ^ 2 + 20 * r_1 * x - 55 / 2 * r_1 * x ^ 2 + 7 / 2 * r_1 * x ^ 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽150⁾`. -/
noncomputable def i8L4Q150_2 (x _r_00001 _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    11 - 9 / 2 * x ^ 2 - 7 / 4 * x ^ 3 - 5 / 4 * x - 2 * r_1 * x ^ 3 + 6 * r_001 * x ^ 2 +
      10 * r_1 * x + 19 * r_01 * x ^ 2 - 9 / 2 * r_1 * x ^ 2 - 7 / 2 * r_1 * x ^ 4

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽150⁾`. -/
noncomputable def i8L4Q150_3 (x _r_00001 _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    -3 + x ^ 3 / 2 + 2 * x ^ 2 - x / 2 + r_1 * x ^ 4 - 5 * r_1 * x ^ 2 - 2 * r_01 * x ^ 2 +
      2 * r_1 * x + 2 * r_1 * x ^ 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽150⁾`. -/
noncomputable def i8L4Q150_4 (_x _r_00001 _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_150_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s150 x = i8L4S150 x + x * (i8L4Q150_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one]
      x) + Real.log x * i8L4Q150_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q150_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q150_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q150_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s150 i8Psi4s150N0 i8Psi4s150N1 i8Psi4s150N2 i8Psi4s150N3 i8Psi4s150N4 i8Psi4s150W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00010 hx, i13hw_0010 hx, i13hw_00100
    hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01000 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1000 hx]
  simp only [i13hpl_rho_00001 h0, i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S150 i8L4Q150_0 i8L4Q150_1 i8L4Q150_2 i8L4Q150_3 i8L4Q150_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽150⁾`. -/
noncomputable def i8L4R150 (x : ℝ) : ℝ :=
  x * (i8L4Q150_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q150_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q150_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q150_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q150_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R150 : Tendsto i8L4R150 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q150_0 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q150_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q150_1 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q150_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q150_2 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q150_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q150_3 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q150_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q150_0 x (i13Rho [zero,
    zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q150_1 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q150_2 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q150_3 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R150
  unfold i8L4Q150_4
  ring

/-- The singular part of `Ψ₄⁽151k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S151k0 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽151k0⁾`. -/
noncomputable def i8L4Q151k0_0 (x r_00011 r_001 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    6 - 13 * x ^ 2 - 5 * x + 3 * x ^ 4 + 3 / 4 * x ^ 3 + 3 / 4 * x ^ 5 - 28 * r_01 * x ^ 2 -
      24 * r_1 * x ^ 3 - 19 * r_1 ^ 2 * x ^ 5 - 16 * r_00011 * x ^ 2 - 16 * r_0011 * x ^ 2 -
      16 * r_011 * x ^ 3 - 14 * r_1 * x ^ 4 - 4 * r_011 * x ^ 4 + 3 * r_1 * x ^ 6 +
      3 * r_1 ^ 2 * x ^ 7 + 6 * r_1 * x ^ 5 + 8 * r_0011 * x ^ 4 + 16 * r_001 * x ^ 2 +
      16 * r_0011 * x + 16 * r_0011 * x ^ 3 + 16 * r_011 * x + 16 * r_1 ^ 2 * x ^ 4 +
      24 * r_011 * x ^ 2 + 29 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽151k0⁾`. -/
noncomputable def i8L4Q151k0_1 (x _r_00011 _r_001 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -8 - x ^ 3 - x ^ 5 - 2 * x ^ 2 - 2 * x ^ 4 - 16 * r_01 * x ^ 2 - 12 * r_1 ^ 2 * x ^ 5 -
      8 * r_1 * x ^ 3 - 4 * r_1 * x ^ 6 - 4 * r_1 ^ 2 * x ^ 7 + 8 * r_1 ^ 2 * x ^ 4 +
      8 * r_1 ^ 2 * x ^ 6 + 12 * r_1 * x ^ 2 + 16 * r_011 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽151k0⁾`. -/
noncomputable def i8L4Q151k0_2 (_x _r_00011 _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽151k0⁾`. -/
noncomputable def i8L4Q151k0_3 (_x _r_00011 _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽151k0⁾`. -/
noncomputable def i8L4Q151k0_4 (_x _r_00011 _r_001 _r_0011 _r_01 _r_011 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_151k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s151k0 x = i8L4S151k0 x + x * (i8L4Q151k0_0 x (i13Rho [zero, zero, zero, one, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q151k0_1 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q151k0_2 x (i13Rho [zero, zero, zero, one, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q151k0_3 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q151k0_4 x (i13Rho [zero, zero, zero, one, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s151k0 i8Psi4s151k0N0 i8Psi4s151k0N1 i8Psi4s151k0N2 i8Psi4s151k0N3 i8Psi4s151k0N4
    i8Psi4s151k0W
  simp only [hpl_zero, i13hw_010 hx, i13hw_0101 hx, i13hw_0110 hx, i13hw_10 hx, i13hw_101 hx,
    i13hw_11 hx, i13hw_110 hx]
  simp only [i13hpl_rho_00011 h0, i13hpl_rho_001 h0, i13hpl_rho_0011 h0, i13hpl_rho_01 h0,
    i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S151k0 i8L4Q151k0_0 i8L4Q151k0_1 i8L4Q151k0_2 i8L4Q151k0_3 i8L4Q151k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽151k0⁾`. -/
noncomputable def i8L4R151k0 (x : ℝ) : ℝ :=
  x * (i8L4Q151k0_0 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q151k0_1 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
    [one] x) + Real.log x ^ 2 * i8L4Q151k0_2 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, one] x) (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q151k0_3 x (i13Rho [zero, zero, zero, one,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q151k0_4 x (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [one] x))

theorem tendsto_i8L4R151k0 : Tendsto i8L4R151k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q151k0_0 (v 0) (v 4) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q151k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q151k0_1 (v 0) (v 4) (v 9) (v 12) (v 27) (v 29) (v 65)) (by
      unfold i8L4Q151k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q151k0_0 x (i13Rho [zero,
    zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q151k0_1 x (i13Rho [zero, zero, zero,
      one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R151k0
  unfold i8L4Q151k0_2 i8L4Q151k0_3 i8L4Q151k0_4
  ring

/-- The singular part of `Ψ₄⁽151k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S151k1 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽151k1⁾`. -/
noncomputable def i8L4Q151k1_0 (x r_0001 r_00011 r_001 r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    28 - 6 * x ^ 4 + 21 * x + 35 * x ^ 2 - 27 / 2 * x ^ 3 - x ^ 5 / 2 - r_1 * x ^ 6 -
      80 * r_0011 * x ^ 2 - 62 * r_1 * x ^ 2 - 48 * r_00011 * x ^ 2 - 48 * r_01 * x ^ 2 -
      16 * r_001 * x ^ 5 - 16 * r_00101 * x ^ 2 - 16 * r_011 * x - 10 * r_1 * x ^ 5 -
      9 * r_1 * x ^ 4 - 4 * r_001 * x ^ 6 - 4 * r_011 * x ^ 2 + 2 * r_01 * x ^ 4 +
      4 * r_001 * x ^ 4 + 4 * r_011 * x ^ 4 + 16 * r_01 * x ^ 3 + 16 * r_011 * x ^ 3 +
      24 * r_001 * x ^ 3 + 32 * r_0001 * x ^ 2 + 82 * r_1 * x ^ 3 - 16 * r_001 * r_1 * x ^ 4 -
      16 * r_001 * r_1 * x ^ 6 - 8 * r_001 * r_1 * x ^ 7 + 16 * r_001 * r_01 * x ^ 5 +
      40 * r_001 * r_1 * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽151k1⁾`. -/
noncomputable def i8L4Q151k1_1 (x _r_0001 _r_00011 r_001 _r_00101 r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    -12 + x ^ 5 / 2 - 40 * x ^ 2 - 8 * x + 2 * x ^ 3 + 4 * x ^ 4 - 68 * r_1 * x ^ 3 -
      24 * r_01 * x ^ 3 - 16 * r_001 * x ^ 2 - 16 * r_011 * x - 16 * r_011 * x ^ 3 -
      12 * r_1 * x ^ 4 - 8 * r_011 * x ^ 4 - 8 * r_01 ^ 2 * x ^ 5 - 8 * r_1 ^ 2 * x ^ 6 -
      4 * r_01 * x ^ 4 - 2 * r_1 ^ 2 * x ^ 7 + 2 * r_1 ^ 2 * x ^ 5 + 4 * r_01 * x ^ 6 +
      8 * r_1 ^ 2 * x ^ 4 + 16 * r_0011 * x ^ 2 + 16 * r_01 * x ^ 5 + 80 * r_011 * x ^ 2 +
      80 * r_1 * x ^ 2 - 40 * r_01 * r_1 * x ^ 5 + 8 * r_01 * r_1 * x ^ 7 +
      16 * r_01 * r_1 * x ^ 4 + 16 * r_01 * r_1 * x ^ 6

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽151k1⁾`. -/
noncomputable def i8L4Q151k1_2 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽151k1⁾`. -/
noncomputable def i8L4Q151k1_3 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽151k1⁾`. -/
noncomputable def i8L4Q151k1_4 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

theorem i8L4_151k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s151k1 x = i8L4S151k1 x + x * (i8L4Q151k1_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x * i8L4Q151k1_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q151k1_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q151k1_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q151k1_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s151k1 i8Psi4s151k1N0 i8Psi4s151k1N1 i8Psi4s151k1N2 i8Psi4s151k1N3 i8Psi4s151k1N4
    i8Psi4s151k1W
  simp only [hpl_zero, i13hw_0010 hx, i13hw_00110 hx, i13hw_010 hx, i13hw_01001 hx, i13hw_0101 hx,
    i13hw_01010 hx, i13hw_0110 hx, i13hw_10 hx, i13hw_1001 hx, i13hw_101 hx, i13hw_1010 hx,
    i13hw_110 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_00011 h0, i13hpl_rho_001 h0, i8hpl_rho_00101 h0,
    i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S151k1 i8L4Q151k1_0 i8L4Q151k1_1 i8L4Q151k1_2 i8L4Q151k1_3 i8L4Q151k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽151k1⁾`. -/
noncomputable def i8L4R151k1 (x : ℝ) : ℝ :=
  x * (i8L4Q151k1_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q151k1_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q151k1_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q151k1_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q151k1_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R151k1 : Tendsto i8L4R151k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q151k1_0 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q151k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q151k1_1 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q151k1_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q151k1_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q151k1_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R151k1
  unfold i8L4Q151k1_2 i8L4Q151k1_3 i8L4Q151k1_4
  ring

/-- The singular part of `Ψ₄⁽151k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S151k2 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽151k2⁾`. -/
noncomputable def i8L4Q151k2_0 (x r_0001 r_00011 r_001 r_00101 r_0011 r_01 _r_011 r_1 : ℝ) : ℝ :=
    -34 + x ^ 5 / 2 - 18 * x - 9 * x ^ 2 + 6 * x ^ 4 + 29 / 2 * x ^ 3 + r_1 * x ^ 6 -
      48 * r_0001 * x ^ 2 - 38 * r_1 * x ^ 3 - 24 * r_001 * x ^ 3 - 16 * r_0011 * x -
      16 * r_0011 * x ^ 3 - 16 * r_01 * x ^ 3 - 12 * r_001 * x ^ 2 - 8 * r_0011 * x ^ 4 -
      4 * r_001 * x ^ 4 - 2 * r_01 * x ^ 4 + 4 * r_001 * x ^ 6 + 10 * r_1 * x ^ 5 +
      11 * r_1 * x ^ 4 + 16 * r_001 * x ^ 5 + 16 * r_00101 * x ^ 2 + 16 * r_1 * x ^ 2 +
      40 * r_0011 * x ^ 2 + 48 * r_00011 * x ^ 2 - 40 * r_001 * r_1 * x ^ 5 -
      16 * r_001 * r_01 * x ^ 5 + 8 * r_001 * r_1 * x ^ 7 + 16 * r_001 * r_1 * x ^ 4 +
      16 * r_001 * r_1 * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽151k2⁾`. -/
noncomputable def i8L4Q151k2_1 (x _r_0001 _r_00011 r_001 _r_00101 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ :=
    20 - x ^ 5 - 8 * x ^ 4 + 10 * x ^ 2 + 12 * x - 27 / 2 * x ^ 3 - 40 * r_011 * x ^ 2 -
      16 * r_01 * x ^ 5 - 16 * r_1 * x ^ 2 - 12 * r_1 * x ^ 5 - 6 * r_1 * x ^ 4 -
      4 * r_01 * x ^ 6 - 2 * r_1 * x ^ 6 + 4 * r_01 * x ^ 4 + 8 * r_011 * x ^ 4 +
      8 * r_01 ^ 2 * x ^ 5 + 12 * r_01 * x ^ 2 + 16 * r_011 * x + 16 * r_011 * x ^ 3 +
      24 * r_01 * x ^ 3 + 32 * r_001 * x ^ 2 + 36 * r_1 * x ^ 3 - 16 * r_01 * r_1 * x ^ 4 -
      16 * r_01 * r_1 * x ^ 6 - 8 * r_01 * r_1 * x ^ 7 + 40 * r_01 * r_1 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽151k2⁾`. -/
noncomputable def i8L4Q151k2_2 (x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 r_01 r_011 r_1 : ℝ) : ℝ
    :=
    -4 + x ^ 5 / 2 - 4 * x + 3 * x ^ 2 + 3 * x ^ 4 + 9 / 2 * x ^ 3 - 10 * r_1 ^ 2 * x ^ 5 -
      8 * r_01 * x ^ 2 - 8 * r_011 * x ^ 2 - 6 * r_1 * x ^ 2 - 4 * r_1 * x ^ 3 + 2 * r_1 * x ^ 6 +
      2 * r_1 ^ 2 * x ^ 7 + 4 * r_1 ^ 2 * x ^ 4 + 4 * r_1 ^ 2 * x ^ 6 + 8 * r_1 * x ^ 5

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽151k2⁾`. -/
noncomputable def i8L4Q151k2_3 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽151k2⁾`. -/
noncomputable def i8L4Q151k2_4 (_x _r_0001 _r_00011 _r_001 _r_00101 _r_0011 _r_01 _r_011 _r_1 : ℝ) :
    ℝ :=
    0

theorem i8L4_151k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s151k2 x = i8L4S151k2 x + x * (i8L4Q151k2_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x * i8L4Q151k2_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 2 * i8L4Q151k2_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q151k2_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 4 * i8L4Q151k2_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero,
      one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s151k2 i8Psi4s151k2N0 i8Psi4s151k2N1 i8Psi4s151k2N2 i8Psi4s151k2N3 i8Psi4s151k2N4
    i8Psi4s151k2W
  simp only [hpl_zero, i13hw_00, i13hw_0100 hx, i13hw_01100 hx, i13hw_100 hx, i13hw_1100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_00011 h0, i13hpl_rho_001 h0, i8hpl_rho_00101 h0,
    i13hpl_rho_0011 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L4S151k2 i8L4Q151k2_0 i8L4Q151k2_1 i8L4Q151k2_2 i8L4Q151k2_3 i8L4Q151k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽151k2⁾`. -/
noncomputable def i8L4R151k2 (x : ℝ) : ℝ :=
  x * (i8L4Q151k2_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q151k2_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q151k2_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q151k2_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q151k2_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, zero, one] x) (i13Rho [zero,
    zero, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R151k2 : Tendsto i8L4R151k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q151k2_0 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q151k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q151k2_1 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q151k2_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q151k2_2 (v 0) (v 3) (v 4) (v 9) (v 10) (v 12) (v 27) (v 29) (v
      65)) (by
      unfold i8L4Q151k2_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q151k2_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q151k2_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q151k2_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, one, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, one, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R151k2
  unfold i8L4Q151k2_3 i8L4Q151k2_4
  ring

/-- The singular part of `Ψ₄⁽152⁾` at `ξ = 0`. -/
noncomputable def i8L4S152 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽152⁾`. -/
noncomputable def i8L4Q152_0 (x r_0011 r_00111 r_01 r_011 r_0111 r_1 : ℝ) : ℝ :=
    -2 * x - 125 / 6 * x ^ 3 - 91 / 3 * x ^ 2 - 65 / 12 * x ^ 5 - 40 / 3 * x ^ 4 -
      13 / 6 * x ^ 6 - 5 / 12 * x ^ 7 - 34 * r_1 * x ^ 5 - 24 * r_1 ^ 2 * x ^ 6 -
      20 * r_011 * x ^ 2 - 13 * r_1 * x ^ 4 - 9 * r_1 ^ 2 * x ^ 7 - 8 * r_1 * x ^ 7 -
      6 * r_1 ^ 2 * x ^ 8 - 5 * r_1 ^ 2 * x ^ 9 - 4 * r_1 * x ^ 3 + 8 * r_1 ^ 3 * x ^ 7 +
      16 * r_0011 * x ^ 2 + 16 * r_00111 * x ^ 2 + 30 * r_01 * x ^ 2 + 44 * r_1 ^ 2 * x ^ 5 +
      72 * r_0111 * x ^ 2 + 75 * r_1 * x ^ 2 - 27 / 2 * r_1 * x ^ 6 - 22 / 3 * r_1 ^ 3 * x ^ 8 -
      10 / 3 * r_1 ^ 3 * x ^ 10 - 5 / 2 * r_1 * x ^ 8 + 8 / 3 * r_1 ^ 3 * x ^ 9

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽152⁾`. -/
noncomputable def i8L4Q152_1 (x _r_0011 _r_00111 _r_01 r_011 r_0111 r_1 : ℝ) : ℝ :=
    -4 / 3 * x + x ^ 7 / 6 + 4 / 3 * x ^ 6 + 11 / 3 * x ^ 5 + 17 / 3 * x ^ 4 + 34 / 3 * x ^ 2 +
      37 / 6 * x ^ 3 + r_1 * x ^ 8 - 30 * r_1 * x ^ 2 - 16 * r_011 * x ^ 2 - 16 * r_0111 * x ^ 2 -
      6 * r_1 ^ 2 * x ^ 5 - 4 * r_1 ^ 2 * x ^ 6 + 2 * r_1 ^ 2 * x ^ 9 + 6 * r_1 * x ^ 5 +
      6 * r_1 * x ^ 7 + 8 * r_1 * x ^ 3 + 8 * r_1 ^ 2 * x ^ 8 + 9 * r_1 * x ^ 6 -
      20 / 3 * r_1 ^ 3 * x ^ 8 + 4 / 3 * r_1 ^ 3 * x ^ 10 + 8 / 3 * r_1 ^ 3 * x ^ 7 +
      8 / 3 * r_1 ^ 3 * x ^ 9

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽152⁾`. -/
noncomputable def i8L4Q152_2 (_x _r_0011 _r_00111 _r_01 _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽152⁾`. -/
noncomputable def i8L4Q152_3 (_x _r_0011 _r_00111 _r_01 _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽152⁾`. -/
noncomputable def i8L4Q152_4 (_x _r_0011 _r_00111 _r_01 _r_011 _r_0111 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_152_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s152 x = i8L4S152 x + x * (i8L4Q152_0 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one,
      one, one] x) (i13Rho [one] x) + Real.log x * i8L4Q152_1 x (i13Rho [zero, zero, one, one] x)
      (i13Rho [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q152_2 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
      (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q152_3 x (i13Rho [zero, zero, one, one] x) (i13Rho
      [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q152_4 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
      (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s152 i8Psi4s152N0 i8Psi4s152N1 i8Psi4s152N2 i8Psi4s152N3 i8Psi4s152N4 i8Psi4s152W
  simp only [hpl_zero, i13hw_0101 hx, i13hw_0110 hx, i13hw_01101 hx, i13hw_01110 hx, i13hw_10 hx,
    i13hw_101 hx, i13hw_1011 hx, i13hw_11 hx, i13hw_110 hx, i13hw_1101 hx, i13hw_111 hx, i13hw_1110
    hx]
  simp only [i13hpl_rho_0011 h0, i13hpl_rho_00111 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0,
    i13hpl_rho_0111 h0, i13hpl_rho_1 h0]
  unfold i8L4S152 i8L4Q152_0 i8L4Q152_1 i8L4Q152_2 i8L4Q152_3 i8L4Q152_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽152⁾`. -/
noncomputable def i8L4R152 (x : ℝ) : ℝ :=
  x * (i8L4Q152_0 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one, one] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q152_1 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one, one]
    x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x) (i13Rho
    [one] x) + Real.log x ^ 2 * i8L4Q152_2 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
    one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
    one] x) (i13Rho [one] x) + Real.log x ^ 3 * i8L4Q152_3 x (i13Rho [zero, zero, one, one] x)
    (i13Rho [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
    (i13Rho [zero, one, one, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q152_4 x (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, one,
    one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one, one] x)
    (i13Rho [one] x))

theorem tendsto_i8L4R152 : Tendsto i8L4R152 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q152_0 (v 0) (v 12) (v 13) (v 27) (v 29) (v 30) (v 65)) (by
      unfold i8L4Q152_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q152_1 (v 0) (v 12) (v 13) (v 27) (v 29) (v 30) (v 65)) (by
      unfold i8L4Q152_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q152_0 x (i13Rho [zero, zero,
    one, one] x) (i13Rho [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    one] x) (i13Rho [zero, one, one, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q152_1 x (i13Rho [zero, zero, one, one]
      x) (i13Rho [zero, zero, one, one, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R152
  unfold i8L4Q152_2 i8L4Q152_3 i8L4Q152_4
  ring

/-- The singular part of `Ψ₄⁽153⁾` at `ξ = 0`. -/
noncomputable def i8L4S153 (x : ℝ) : ℝ :=
    (1 + Real.log x + Real.log x ^ 2 / 2 + Real.log x ^ 3 / 6 + Real.log x ^ 4 / 24 +
      x * Real.log x ^ 5 / 120) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽153⁾`. -/
noncomputable def i8L4Q153_0 (x : ℝ) : ℝ :=
    1 - x / 32

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽153⁾`. -/
noncomputable def i8L4Q153_1 (x : ℝ) : ℝ :=
    -1 + x / 16

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽153⁾`. -/
noncomputable def i8L4Q153_2 (x : ℝ) : ℝ :=
    1 / 2 - x / 16

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽153⁾`. -/
noncomputable def i8L4Q153_3 (x : ℝ) : ℝ :=
    -1 / 6 + x / 24

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽153⁾`. -/
noncomputable def i8L4Q153_4 (x : ℝ) : ℝ :=
    1 / 24 - x / 48

theorem i8L4_153_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s153 x = i8L4S153 x + x * (i8L4Q153_0 x + Real.log x * i8L4Q153_1 x +
      Real.log x ^ 2 * i8L4Q153_2 x + Real.log x ^ 3 * i8L4Q153_3 x +
      Real.log x ^ 4 * i8L4Q153_4 x) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s153 i8Psi4s153N0 i8Psi4s153N1 i8Psi4s153N2 i8Psi4s153N3 i8Psi4s153N4 i8Psi4s153W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00000]

  unfold i8L4S153 i8L4Q153_0 i8L4Q153_1 i8L4Q153_2 i8L4Q153_3 i8L4Q153_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽153⁾`. -/
noncomputable def i8L4R153 (x : ℝ) : ℝ :=
  x * (i8L4Q153_0 x + Real.log x * i8L4Q153_1 x + Real.log x ^ 2 * i8L4Q153_2 x +
    Real.log x ^ 3 * i8L4Q153_3 x + Real.log x ^ 4 * i8L4Q153_4 x)

theorem tendsto_i8L4R153 : Tendsto i8L4R153 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q153_0 (v 0)) (by
      unfold i8L4Q153_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q153_1 (v 0)) (by
      unfold i8L4Q153_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q153_2 (v 0)) (by
      unfold i8L4Q153_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q153_3 (v 0)) (by
      unfold i8L4Q153_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q153_4 (v 0)) (by
      unfold i8L4Q153_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q153_0 x)
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q153_1 x)
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q153_2 x)
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q153_3 x)
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4Q153_4 x)
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R153
  ring

/-- The singular part of `Ψ₄⁽154⁾` at `ξ = 0`. -/
noncomputable def i8L4S154 (x : ℝ) : ℝ :=
    2 - Real.log x ^ 4 / 12

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽154⁾`. -/
noncomputable def i8L4Q154_0 (x r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -1 - 13 / 16 * x - 7 / 8 * x ^ 2 + x ^ 3 / 16 - 2 * r_00001 * x ^ 2 - 2 * r_1 * x ^ 3 +
      2 * r_1 * x + 3 * r_0001 * x ^ 2 - r_001 * x ^ 2 / 2 - r_1 * x ^ 2 / 8 + r_1 * x ^ 4 / 8 +
      15 / 4 * r_01 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽154⁾`. -/
noncomputable def i8L4Q154_1 (x _r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    1 - 3 / 8 * x - x ^ 3 / 8 + 3 / 4 * x ^ 2 + r_01 * x ^ 2 / 2 - 3 * r_001 * x ^ 2 +
      2 * r_0001 * x ^ 2 + 2 * r_1 * x + 2 * r_1 * x ^ 3 - 15 / 4 * r_1 * x ^ 2 - r_1 * x ^ 4 / 4

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽154⁾`. -/
noncomputable def i8L4Q154_2 (x _r_00001 _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -1 / 2 - 5 / 8 * x - x ^ 2 / 4 + x ^ 3 / 8 + r_1 * x - r_001 * x ^ 2 - r_1 * x ^ 3 -
      r_1 * x ^ 2 / 4 + r_1 * x ^ 4 / 4 + 3 / 2 * r_01 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽154⁾`. -/
noncomputable def i8L4Q154_3 (x _r_00001 _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    1 / 6 - x ^ 3 / 12 + x / 12 - r_1 * x ^ 2 / 2 - r_1 * x ^ 4 / 6 + r_01 * x ^ 2 / 3 +
      r_1 * x / 3 + r_1 * x ^ 3 / 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽154⁾`. -/
noncomputable def i8L4Q154_4 (_x _r_00001 _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_154_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s154 x = i8L4S154 x + x * (i8L4Q154_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one]
      x) + Real.log x * i8L4Q154_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q154_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q154_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q154_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s154 i8Psi4s154N0 i8Psi4s154N1 i8Psi4s154N2 i8Psi4s154N3 i8Psi4s154N4 i8Psi4s154W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00010 hx, i13hw_0010 hx, i13hw_00100
    hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01000 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1000 hx]
  simp only [i13hpl_rho_00001 h0, i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S154 i8L4Q154_0 i8L4Q154_1 i8L4Q154_2 i8L4Q154_3 i8L4Q154_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽154⁾`. -/
noncomputable def i8L4R154 (x : ℝ) : ℝ :=
  x * (i8L4Q154_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q154_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q154_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q154_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q154_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R154 : Tendsto i8L4R154 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q154_0 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q154_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q154_1 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q154_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q154_2 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q154_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q154_3 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q154_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q154_0 x (i13Rho [zero,
    zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q154_1 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q154_2 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q154_3 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R154
  unfold i8L4Q154_4
  ring

/-- The regular parts of group 16. -/
noncomputable def i8L4RG16 (x : ℝ) : ℝ :=
  i8L4R146k2 x + i8L4R147 x + i8L4R148k0 x + i8L4R149 x + i8L4R150 x + i8L4R151k0 x +
    i8L4R151k1 x + i8L4R151k2 x + i8L4R152 x + i8L4R153 x + i8L4R154 x

theorem tendsto_i8L4RG16 : Tendsto i8L4RG16 (𝓝[>] 0) (𝓝 0) := by
  have H := ((((((((((tendsto_i8L4R146k2.add tendsto_i8L4R147).add tendsto_i8L4R148k0).add
    tendsto_i8L4R149).add tendsto_i8L4R150).add tendsto_i8L4R151k0).add tendsto_i8L4R151k1).add
    tendsto_i8L4R151k2).add tendsto_i8L4R152).add tendsto_i8L4R153).add tendsto_i8L4R154)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
