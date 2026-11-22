/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L8
public import QED.ThreeLoopD.SetDMastersI13R4L

/-!
# Set (d), master `I₈`: the expansion of `F₄ - A₄` at infinity, part 9

As `t → ∞`, `ξ(t) → 0⁺`. Writing every word in the Lyndon basis and every basis function other
than `log ξ` as `c₁ ξ + c₂ ξ² + ξ³ ρ_w(ξ)`, each sub-piece of `Ψ₄` and `-A₄(t(ξ))` becomes a
singular part `S` (a polynomial in `1/ξ` and `log ξ`) plus a regular part
`ξ ∑ⱼ log^j ξ Qⱼ`, with polynomials `Qⱼ` in `ξ` and the bounded `ρ_w(ξ)`; the regular parts
tend to `0`.

## Main results

* `QED.ThreeLoopD.i8L4_101_eq`, `QED.ThreeLoopD.tendsto_i8L4RG9` and their companions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular part of `Ψ₄⁽101⁾` at `ξ = 0`. -/
noncomputable def i8L4S101 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽101⁾`. -/
noncomputable def i8L4Q101_0 (x r_01 r_01m _r_01mm r_0m r_0m01 r_0m1 _r_0m1m r_0mm r_0mm01 r_0mm1
    r_1 r_m r_m1 _r_mm1 : ℝ) : ℝ :=
    x ^ 6 - x ^ 2 - 11 * x ^ 4 + 8 * x - x ^ 7 / 2 + 17 / 2 * x ^ 5 + r_m * x ^ 8 - r_1 * x ^ 8 -
      64 * r_m1 * x ^ 3 - 42 * r_1 * x ^ 5 - 36 * r_m * x ^ 3 - 28 * r_1 * x ^ 3 -
      24 * r_0mm * x ^ 3 - 16 * r_0m01 * x ^ 2 - 16 * r_m * x ^ 6 - 14 * r_0m * x ^ 6 -
      8 * r_01 * x ^ 4 - 4 * r_01m * x ^ 4 - 4 * r_0m1 * x ^ 4 - 4 * r_0mm * x ^ 4 -
      2 * r_m * x ^ 5 + 2 * r_0m * x ^ 8 + 4 * r_0m * x ^ 5 + 4 * r_0m * x ^ 7 +
      4 * r_0mm * x ^ 6 + 4 * r_1 * x ^ 7 + 5 * r_1 * x ^ 2 + 6 * r_01 * x ^ 2 +
      8 * r_0m * x ^ 4 + 8 * r_0m ^ 2 * x ^ 5 + 10 * r_1 * x ^ 6 + 16 * r_01 * x ^ 3 +
      16 * r_01m * x ^ 3 + 16 * r_0m * x ^ 3 + 16 * r_0m1 * x ^ 2 + 16 * r_0m1 * x ^ 3 +
      16 * r_0mm * x ^ 5 + 16 * r_0mm01 * x ^ 2 + 16 * r_m1 * x ^ 4 + 17 * r_m * x ^ 4 +
      28 * r_0m * x ^ 2 + 36 * r_0mm * x ^ 2 + 52 * r_1 * x ^ 4 + 64 * r_0mm1 * x ^ 2 -
      64 * r_0m * r_m1 * x ^ 5 - 40 * r_0mm * r_1 * x ^ 5 - 36 * r_0m * r_m * x ^ 5 -
      32 * r_0m * r_1 * x ^ 7 - 28 * r_0m * r_1 * x ^ 5 - 26 * r_1 * r_m * x ^ 7 -
      16 * r_01 * r_0mm * x ^ 5 - 16 * r_0m * r_m * x ^ 8 - 16 * r_1 * r_m * x ^ 5 -
      4 * r_0m * r_m * x ^ 9 - 4 * r_1 * r_m * x ^ 8 + 2 * r_1 * r_m * x ^ 9 +
      4 * r_0m * r_1 * x ^ 9 + 8 * r_0m * r_m * x ^ 6 + 8 * r_0mm * r_1 * x ^ 7 +
      16 * r_01 * r_0m * x ^ 5 + 16 * r_01m * r_0m * x ^ 5 + 16 * r_0m * r_0m1 * x ^ 5 +
      16 * r_0mm * r_1 * x ^ 4 + 16 * r_0mm * r_1 * x ^ 6 + 44 * r_1 * r_m * x ^ 6 +
      56 * r_0m * r_1 * x ^ 6 - 16 * r_0m * r_1 * r_m * x ^ 7 - 16 * r_0m * r_1 * r_m * x ^ 9 -
      8 * r_0m * r_1 * r_m * x ^ 10 + 40 * r_0m * r_1 * r_m * x ^ 8

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽101⁾`. -/
noncomputable def i8L4Q101_1 (x _r_01 r_01m r_01mm _r_0m _r_0m01 r_0m1 r_0m1m r_0mm _r_0mm01 r_0mm1
    r_1 r_m r_m1 r_mm1 : ℝ) : ℝ :=
    x ^ 7 / 2 - 5 * x ^ 5 - 4 * x + 9 * x ^ 4 + 18 * x ^ 2 - 23 / 2 * x ^ 3 + r_1 * x ^ 8 -
      64 * r_mm1 * x ^ 2 - 40 * r_1 * x ^ 4 - 32 * r_m1 * x ^ 4 - 28 * r_m * x ^ 2 -
      16 * r_01m * x ^ 2 - 16 * r_01mm * x ^ 2 - 16 * r_0m1 * x ^ 2 - 16 * r_0m1m * x ^ 2 -
      16 * r_0mm * x ^ 2 - 16 * r_0mm1 * x ^ 2 - 16 * r_m1 * x ^ 2 - 7 * r_1 * x ^ 6 -
      6 * r_1 * x ^ 2 - 4 * r_m * x ^ 5 - 4 * r_m * x ^ 7 - 4 * r_m ^ 2 * x ^ 6 -
      2 * r_1 * x ^ 7 - 2 * r_m * x ^ 8 + 2 * r_m ^ 2 * x ^ 9 + 8 * r_m ^ 2 * x ^ 8 +
      14 * r_m * x ^ 6 + 16 * r_m * x ^ 3 + 18 * r_m ^ 2 * x ^ 5 + 24 * r_1 * x ^ 3 +
      30 * r_1 * x ^ 5 + 64 * r_m1 * x ^ 3 - 56 * r_1 * r_m * x ^ 6 - 20 * r_1 * r_m ^ 2 * x ^ 8 -
      4 * r_1 * r_m * x ^ 9 + 4 * r_1 * r_m ^ 2 * x ^ 10 + 8 * r_1 * r_m ^ 2 * x ^ 7 +
      8 * r_1 * r_m ^ 2 * x ^ 9 + 28 * r_1 * r_m * x ^ 5 + 32 * r_1 * r_m * x ^ 7 +
      64 * r_m * r_m1 * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽101⁾`. -/
noncomputable def i8L4Q101_2 (_x _r_01 _r_01m _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m1m _r_0mm _r_0mm01
    _r_0mm1 _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽101⁾`. -/
noncomputable def i8L4Q101_3 (_x _r_01 _r_01m _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m1m _r_0mm _r_0mm01
    _r_0mm1 _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽101⁾`. -/
noncomputable def i8L4Q101_4 (_x _r_01 _r_01m _r_01mm _r_0m _r_0m01 _r_0m1 _r_0m1m _r_0mm _r_0mm01
    _r_0mm1 _r_1 _r_m _r_m1 _r_mm1 : ℝ) : ℝ :=
    0

theorem i8L4_101_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s101 x = i8L4S101 x + x * (i8L4Q101_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne]
      x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x * i8L4Q101_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne]
      x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho
      [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [zero, negOne,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne,
      negOne, one] x) + Real.log x ^ 2 * i8L4Q101_2 x (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x)
      (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho
      [negOne, negOne, one] x) + Real.log x ^ 3 * i8L4Q101_3 x (i13Rho [zero, one] x) (i13Rho [zero,
      one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one,
      negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) (i13Rho [negOne, negOne, one] x) +
      Real.log x ^ 4 * i8L4Q101_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [zero, negOne, negOne, one] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one]
      x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s101 i8Psi4s101N0 i8Psi4s101N1 i8Psi4s101N2 i8Psi4s101N3 i8Psi4s101N4 i8Psi4s101W
  simp only [hpl_zero, i13hw_01m0 hx, i13hw_01mm0 hx, i13hw_0m10 hx, i13hw_0m1m0 hx, i13hw_0mm0 hx,
    i13hw_0mm10 hx, i13hw_10 hx, i13hw_1m0 hx, i13hw_1mm0 hx, i13hw_m0 hx, i13hw_m01 hx, i13hw_m10
    hx, i13hw_m1m0 hx, i13hw_mm0 hx, i13hw_mm01 hx, i13hw_mm10 hx]
  simp only [i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_01mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_0m1m h0, i13hpl_rho_0mm h0, i13hpl_rho_0mm01
    h0, i13hpl_rho_0mm1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0, i8hpl_rho_mm1 h0]
  unfold i8L4S101 i8L4Q101_0 i8L4Q101_1 i8L4Q101_2 i8L4Q101_3 i8L4Q101_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽101⁾`. -/
noncomputable def i8L4R101 (x : ℝ) : ℝ :=
  x * (i8L4Q101_0 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
    negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
    [zero, negOne, negOne, zero, one] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x * i8L4Q101_1 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
    (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 2 * i8L4Q101_2 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [zero, negOne, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 3 * i8L4Q101_3 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [zero, negOne, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x) +
    Real.log x ^ 4 * i8L4Q101_4 x (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
    negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x) (i13Rho [zero, negOne, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) (i13Rho [negOne, negOne, one] x))

theorem tendsto_i8L4R101 : Tendsto i8L4R101 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q101_0 (v 0) (v 27) (v 36) (v 40) (v 43) (v 44) (v 49) (v 54) (v
      57) (v 58) (v 59) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q101_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q101_1 (v 0) (v 27) (v 36) (v 40) (v 43) (v 44) (v 49) (v 54) (v
      57) (v 58) (v 59) (v 65) (v 66) (v 67) (v 69)) (by
      unfold i8L4Q101_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q101_0 x (i13Rho [zero, one]
    x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne]
    x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
    one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x)
    (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
    one] x) (i13Rho [negOne, negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q101_1 x (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero, negOne, negOne, zero, one] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne,
      one] x) (i13Rho [negOne, negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R101
  unfold i8L4Q101_2 i8L4Q101_3 i8L4Q101_4
  ring

/-- The singular part of `Ψ₄⁽102⁾` at `ξ = 0`. -/
noncomputable def i8L4S102 (x : ℝ) : ℝ :=
    4 - Real.log x ^ 4 / 6

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽102⁾`. -/
noncomputable def i8L4Q102_0 (x r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    6 - 11 / 8 * x - 9 / 4 * x ^ 2 - x ^ 3 / 8 + r_001 * x ^ 2 - 4 * r_1 * x ^ 3 +
      4 * r_00001 * x ^ 2 + 4 * r_1 * x + 10 * r_0001 * x ^ 2 - r_1 * x ^ 4 / 4 +
      r_1 * x ^ 2 / 4 + 17 / 2 * r_01 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽102⁾`. -/
noncomputable def i8L4Q102_1 (x _r_00001 r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -6 - 5 / 4 * x + x ^ 3 / 4 + 5 / 2 * x ^ 2 + r_1 * x ^ 4 / 2 - r_01 * x ^ 2 -
      10 * r_001 * x ^ 2 - 4 * r_0001 * x ^ 2 + 4 * r_1 * x + 4 * r_1 * x ^ 3 - 17 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽102⁾`. -/
noncomputable def i8L4Q102_2 (x _r_00001 _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    3 - 3 / 2 * x ^ 2 - 3 / 4 * x - x ^ 3 / 4 + r_1 * x ^ 2 / 2 - 2 * r_1 * x ^ 3 +
      2 * r_001 * x ^ 2 + 2 * r_1 * x + 5 * r_01 * x ^ 2 - r_1 * x ^ 4 / 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽102⁾`. -/
noncomputable def i8L4Q102_3 (x _r_00001 _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    -1 - x / 6 + x ^ 3 / 6 + 2 / 3 * x ^ 2 - 5 / 3 * r_1 * x ^ 2 - 2 / 3 * r_01 * x ^ 2 +
      r_1 * x ^ 4 / 3 + 2 / 3 * r_1 * x + 2 / 3 * r_1 * x ^ 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽102⁾`. -/
noncomputable def i8L4Q102_4 (_x _r_00001 _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_102_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s102 x = i8L4S102 x + x * (i8L4Q102_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one]
      x) + Real.log x * i8L4Q102_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q102_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q102_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q102_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s102 i8Psi4s102N0 i8Psi4s102N1 i8Psi4s102N2 i8Psi4s102N3 i8Psi4s102N4 i8Psi4s102W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00010 hx, i13hw_0010 hx, i13hw_00100
    hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01000 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1000 hx]
  simp only [i13hpl_rho_00001 h0, i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0,
    i13hpl_rho_1 h0]
  unfold i8L4S102 i8L4Q102_0 i8L4Q102_1 i8L4Q102_2 i8L4Q102_3 i8L4Q102_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽102⁾`. -/
noncomputable def i8L4R102 (x : ℝ) : ℝ :=
  x * (i8L4Q102_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x * i8L4Q102_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q102_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q102_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q102_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R102 : Tendsto i8L4R102 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q102_0 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q102_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q102_1 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q102_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q102_2 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q102_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q102_3 (v 0) (v 1) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q102_3
      fun_prop)
  have H := ((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q102_0 x (i13Rho [zero,
    zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q102_1 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q102_2 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q102_3 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      one] x) (i13Rho [one] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R102
  unfold i8L4Q102_4
  ring

/-- The singular part of `Ψ₄⁽103⁾` at `ξ = 0`. -/
noncomputable def i8L4S103 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽103⁾`. -/
noncomputable def i8L4Q103_0 (x r_0001 r_000m r_001 r_00m r_00m01 r_00m1 r_01 _r_01m _r_0m _r_0m01
    _r_0m1 r_1 _r_m _r_m1 : ℝ) : ℝ :=
    24 - x ^ 4 - 8 * x ^ 3 + 3 * x ^ 2 + 9 * x + x ^ 5 / 4 + r_1 * x ^ 6 / 2 - r_01 * x ^ 4 -
      32 * r_00m1 * x ^ 2 - 18 * r_00m * x ^ 2 - 10 * r_1 * x ^ 4 - 8 * r_00m * x ^ 5 -
      8 * r_00m01 * x ^ 2 - 6 * r_001 * x ^ 2 - 5 * r_01 * x ^ 2 - 3 * r_1 * x ^ 5 -
      2 * r_00m * x ^ 6 + 2 * r_00m * x ^ 4 + 8 * r_0001 * x ^ 2 + 8 * r_01 * x ^ 3 +
      12 * r_00m * x ^ 3 + 24 * r_000m * x ^ 2 + 25 * r_1 * x ^ 3 - 25 / 2 * r_1 * x ^ 2 -
      8 * r_00m * r_1 * x ^ 4 - 8 * r_00m * r_1 * x ^ 6 - 4 * r_00m * r_1 * x ^ 7 +
      8 * r_00m * r_01 * x ^ 5 + 20 * r_00m * r_1 * x ^ 5

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽103⁾`. -/
noncomputable def i8L4Q103_1 (x _r_0001 _r_000m r_001 r_00m _r_00m01 _r_00m1 r_01 _r_01m r_0m r_0m01
    r_0m1 r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -16 - 7 * x - 2 * x ^ 2 + 8 * x ^ 3 - x ^ 5 / 2 - r_1 * x ^ 6 - 26 * r_1 * x ^ 3 -
      16 * r_00m * x ^ 2 - 12 * r_0m * x ^ 3 - 8 * r_001 * x ^ 2 - 8 * r_01 * x ^ 3 -
      2 * r_0m * x ^ 4 + 2 * r_01 * x ^ 4 + 2 * r_0m * x ^ 6 + 2 * r_1 * x ^ 5 +
      6 * r_01 * x ^ 2 + 8 * r_0m * x ^ 5 + 8 * r_0m01 * x ^ 2 + 12 * r_1 * x ^ 4 +
      13 * r_1 * x ^ 2 + 18 * r_0m * x ^ 2 + 32 * r_0m1 * x ^ 2 - 20 * r_0m * r_1 * x ^ 5 -
      8 * r_01 * r_0m * x ^ 5 + 4 * r_0m * r_1 * x ^ 7 + 8 * r_0m * r_1 * x ^ 4 +
      8 * r_0m * r_1 * x ^ 6

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽103⁾`. -/
noncomputable def i8L4Q103_2 (x _r_0001 _r_000m _r_001 _r_00m _r_00m01 _r_00m1 r_01 r_01m r_0m
    _r_0m01 r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    4 + x ^ 2 + x ^ 4 + x ^ 5 / 2 + 2 * x - 7 / 2 * x ^ 3 + r_1 * x ^ 6 - r_m * x ^ 6 -
      16 * r_m1 * x ^ 2 - 9 * r_m * x ^ 2 - 8 * r_1 * x ^ 4 - 7 * r_1 * x ^ 2 - 4 * r_m * x ^ 5 +
      2 * r_m * x ^ 3 + 4 * r_01 * x ^ 2 + 4 * r_01m * x ^ 2 + 4 * r_0m * x ^ 2 +
      4 * r_0m1 * x ^ 2 + 14 * r_1 * x ^ 3 - 4 * r_1 * r_m * x ^ 4 - 4 * r_1 * r_m * x ^ 6 -
      2 * r_1 * r_m * x ^ 7 + 10 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽103⁾`. -/
noncomputable def i8L4Q103_3 (_x _r_0001 _r_000m _r_001 _r_00m _r_00m01 _r_00m1 _r_01 _r_01m _r_0m
    _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽103⁾`. -/
noncomputable def i8L4Q103_4 (_x _r_0001 _r_000m _r_001 _r_00m _r_00m01 _r_00m1 _r_01 _r_01m _r_0m
    _r_0m01 _r_0m1 _r_1 _r_m _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_103_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s103 x = i8L4S103 x + x * (i8L4Q103_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q103_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q103_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q103_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q103_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
      negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
      [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho
      [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s103 i8Psi4s103N0 i8Psi4s103N1 i8Psi4s103N2 i8Psi4s103N3 i8Psi4s103N4 i8Psi4s103W
  simp only [hpl_zero, i13hw_00, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01m00 hx,
    i13hw_0m00 hx, i13hw_0m001 hx, i13hw_0m010 hx, i13hw_0m100 hx, i13hw_10 hx, i13hw_100 hx,
    i13hw_1m00 hx, i13hw_m00 hx, i13hw_m001 hx, i13hw_m010 hx, i13hw_m100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_000m h0, i13hpl_rho_001 h0, i13hpl_rho_00m h0,
    i13hpl_rho_00m01 h0, i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S103 i8L4Q103_0 i8L4Q103_1 i8L4Q103_2 i8L4Q103_3 i8L4Q103_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽103⁾`. -/
noncomputable def i8L4R103 (x : ℝ) : ℝ :=
  x * (i8L4Q103_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q103_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne,
    zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
    negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne,
    one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q103_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q103_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q103_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero,
    negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R103 : Tendsto i8L4R103 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q103_0 (v 0) (v 3) (v 6) (v 9) (v 18) (v 19) (v 21) (v 27) (v
      36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q103_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q103_1 (v 0) (v 3) (v 6) (v 9) (v 18) (v 19) (v 21) (v 27) (v
      36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q103_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q103_2 (v 0) (v 3) (v 6) (v 9) (v 18) (v 19) (v 21) (v 27) (v
      36) (v 43) (v 44) (v 49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q103_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q103_0 x (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q103_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q103_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne, zero, one] x) (i13Rho [zero, zero, negOne, one]
      x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne]
      x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R103
  unfold i8L4Q103_3 i8L4Q103_4
  ring

/-- The singular part of `Ψ₄⁽104⁾` at `ξ = 0`. -/
noncomputable def i8L4S104 (_x : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽104⁾`. -/
noncomputable def i8L4Q104_0 (x r_001 r_00m r_01 _r_01m r_0m r_0m01 r_0m1 r_1 _r_m _r_m1 : ℝ) : ℝ :=
    -32 - x ^ 5 - 14 * x - 4 * x ^ 2 + 16 * x ^ 3 - 52 * r_1 * x ^ 3 - 32 * r_00m * x ^ 2 -
      24 * r_0m * x ^ 3 - 16 * r_001 * x ^ 2 - 16 * r_01 * x ^ 3 - 4 * r_0m * x ^ 4 -
      2 * r_1 * x ^ 6 + 4 * r_01 * x ^ 4 + 4 * r_0m * x ^ 6 + 4 * r_1 * x ^ 5 +
      12 * r_01 * x ^ 2 + 16 * r_0m * x ^ 5 + 16 * r_0m01 * x ^ 2 + 24 * r_1 * x ^ 4 +
      26 * r_1 * x ^ 2 + 36 * r_0m * x ^ 2 + 64 * r_0m1 * x ^ 2 - 40 * r_0m * r_1 * x ^ 5 -
      16 * r_01 * r_0m * x ^ 5 + 8 * r_0m * r_1 * x ^ 7 + 16 * r_0m * r_1 * x ^ 4 +
      16 * r_0m * r_1 * x ^ 6

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽104⁾`. -/
noncomputable def i8L4Q104_1 (x _r_001 _r_00m r_01 r_01m r_0m _r_0m01 r_0m1 r_1 r_m r_m1 : ℝ) : ℝ :=
    16 - 14 * x ^ 3 + 2 * x ^ 5 + 4 * x ^ 2 + 4 * x ^ 4 + 8 * x - 64 * r_m1 * x ^ 2 -
      36 * r_m * x ^ 2 - 32 * r_1 * x ^ 4 - 28 * r_1 * x ^ 2 - 16 * r_m * x ^ 5 -
      4 * r_m * x ^ 6 + 4 * r_1 * x ^ 6 + 8 * r_m * x ^ 3 + 16 * r_01 * x ^ 2 +
      16 * r_01m * x ^ 2 + 16 * r_0m * x ^ 2 + 16 * r_0m1 * x ^ 2 + 56 * r_1 * x ^ 3 -
      16 * r_1 * r_m * x ^ 4 - 16 * r_1 * r_m * x ^ 6 - 8 * r_1 * r_m * x ^ 7 +
      40 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽104⁾`. -/
noncomputable def i8L4Q104_2 (_x _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 :
    ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽104⁾`. -/
noncomputable def i8L4Q104_3 (_x _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 :
    ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽104⁾`. -/
noncomputable def i8L4Q104_4 (_x _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m _r_m1 :
    ℝ) : ℝ :=
    0

theorem i8L4_104_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s104 x = i8L4S104 x + x * (i8L4Q104_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
      negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q104_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
      zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 2 * i8L4Q104_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q104_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
      (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
      negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
      (i13Rho [negOne, one] x) + Real.log x ^ 4 * i8L4Q104_4 x (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s104 i8Psi4s104N0 i8Psi4s104N1 i8Psi4s104N2 i8Psi4s104N3 i8Psi4s104N4 i8Psi4s104W
  simp only [hpl_zero, i13hw_010 hx, i13hw_01m0 hx, i13hw_0m0 hx, i13hw_0m10 hx, i13hw_10 hx,
    i13hw_1m0 hx, i13hw_m0 hx, i13hw_m01 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_00m h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0,
    i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0,
    i13hpl_rho_m1 h0]
  unfold i8L4S104 i8L4Q104_0 i8L4Q104_1 i8L4Q104_2 i8L4Q104_3 i8L4Q104_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽104⁾`. -/
noncomputable def i8L4R104 (x : ℝ) : ℝ :=
  x * (i8L4Q104_0 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one]
    x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q104_1 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho
    [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne,
    zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho
    [negOne, one] x) + Real.log x ^ 2 * i8L4Q104_2 x (i13Rho [zero, zero, one] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q104_3 x (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x)
    (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero,
    negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x)
    (i13Rho [negOne, one] x) + Real.log x ^ 4 * i8L4Q104_4 x (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero,
    negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
    (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R104 : Tendsto i8L4R104 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q104_0 (v 0) (v 9) (v 18) (v 27) (v 36) (v 43) (v 44) (v 49) (v
      65) (v 66) (v 67)) (by
      unfold i8L4Q104_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q104_1 (v 0) (v 9) (v 18) (v 27) (v 36) (v 43) (v 44) (v 49) (v
      65) (v 66) (v 67)) (by
      unfold i8L4Q104_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q104_0 x (i13Rho [zero, zero,
    one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x)
    (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q104_1 x (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R104
  unfold i8L4Q104_2 i8L4Q104_3 i8L4Q104_4
  ring

/-- The singular part of `Ψ₄⁽105⁾` at `ξ = 0`. -/
noncomputable def i8L4S105 (x : ℝ) : ℝ :=
    8 - 4 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽105⁾`. -/
noncomputable def i8L4Q105_0 (x r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -12 + x ^ 3 / 2 + 5 * x ^ 2 - 5 / 2 * x + r_1 * x ^ 4 - 20 * r_001 * x ^ 2 -
      17 * r_1 * x ^ 2 - 8 * r_0001 * x ^ 2 - 2 * r_01 * x ^ 2 + 8 * r_1 * x + 8 * r_1 * x ^ 3

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽105⁾`. -/
noncomputable def i8L4Q105_1 (x _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    12 - x ^ 3 - 6 * x ^ 2 - 3 * x - 8 * r_1 * x ^ 3 - 2 * r_1 * x ^ 4 + 2 * r_1 * x ^ 2 +
      8 * r_001 * x ^ 2 + 8 * r_1 * x + 20 * r_01 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽105⁾`. -/
noncomputable def i8L4Q105_2 (x _r_0001 _r_001 r_01 r_1 : ℝ) : ℝ :=
    -6 + x ^ 3 - x + 4 * x ^ 2 - 10 * r_1 * x ^ 2 - 4 * r_01 * x ^ 2 + 2 * r_1 * x ^ 4 +
      4 * r_1 * x + 4 * r_1 * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽105⁾`. -/
noncomputable def i8L4Q105_3 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽105⁾`. -/
noncomputable def i8L4Q105_4 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_105_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s105 x = i8L4S105 x + x * (i8L4Q105_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q105_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q105_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q105_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q105_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s105 i8Psi4s105N0 i8Psi4s105N1 i8Psi4s105N2 i8Psi4s105N3 i8Psi4s105N4 i8Psi4s105W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_10 hx,
    i13hw_100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S105 i8L4Q105_0 i8L4Q105_1 i8L4Q105_2 i8L4Q105_3 i8L4Q105_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽105⁾`. -/
noncomputable def i8L4R105 (x : ℝ) : ℝ :=
  x * (i8L4Q105_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    one] x) (i13Rho [one] x) + Real.log x * i8L4Q105_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q105_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q105_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q105_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R105 : Tendsto i8L4R105 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q105_0 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q105_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q105_1 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q105_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q105_2 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q105_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q105_0 x (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q105_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q105_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R105
  unfold i8L4Q105_3 i8L4Q105_4
  ring

/-- The singular part of `Ψ₄⁽106⁾` at `ξ = 0`. -/
noncomputable def i8L4S106 (x : ℝ) : ℝ :=
    (108 + Real.log x ^ 4 + 10 * Real.log x ^ 3 + 16 * x + 46 * Real.log x ^ 2 +
      108 * Real.log x - 4 / 3 * π ^ 2 - 4 * x * Real.log x ^ 3 + 4 * x * Real.log x ^ 2 -
      5 / 2 * x * Real.log x ^ 4 - 4 / 3 * Real.log x * π ^ 2 - 3 / 5 * x * Real.log x ^ 5 -
      π ^ 2 * Real.log x ^ 2 / 3 + π ^ 2 * x * Real.log x ^ 2 / 3 +
      π ^ 2 * x * Real.log x ^ 3 / 3) / x ^ 1

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽106⁾`. -/
noncomputable def i8L4Q106_0 (x r_0000m r_000m r_00m r_0m _r_m : ℝ) : ℝ :=
    -64 + 5 * x ^ 2 - 7 / 2 * x + 3 / 4 * x ^ 3 + 8 / 3 * π ^ 2 - 96 * r_0000m * x ^ 2 -
      84 * r_00m * x ^ 2 - 32 * r_0m * x ^ 3 - 13 * r_0m * x ^ 2 - 12 * r_000m * x ^ 2 -
      3 * r_0m * x ^ 4 + 16 * r_0m * x + π ^ 2 * x / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽106⁾`. -/
noncomputable def i8L4Q106_1 (x _r_0000m r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    64 - 15 * x ^ 2 - 3 * x ^ 3 + 7 * x - 8 / 3 * π ^ 2 - 16 * r_m * x + 3 * r_m * x ^ 4 +
      6 * r_0m * x ^ 4 + 12 * r_00m * x ^ 2 + 13 * r_m * x ^ 2 + 16 * r_0m * x +
      32 * r_0m * x ^ 3 + 32 * r_m * x ^ 3 + 84 * r_0m * x ^ 2 + 96 * r_000m * x ^ 2 - π ^ 2 * x / 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽106⁾`. -/
noncomputable def i8L4Q106_2 (x _r_0000m _r_000m r_00m r_0m r_m : ℝ) : ℝ :=
    -27 + π ^ 2 - 2 * x + 11 * x ^ 2 + 7 / 2 * x ^ 3 - 48 * r_00m * x ^ 2 - 42 * r_m * x ^ 2 -
      32 * r_m * x ^ 3 - 16 * r_m * x - 12 * r_0m * x ^ 3 - 10 * r_0m * x ^ 2 - 6 * r_m * x ^ 4 -
      2 * r_0m * x ^ 4 + 4 * r_0m * x + π ^ 2 * x / 6

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽106⁾`. -/
noncomputable def i8L4Q106_3 (x _r_0000m _r_000m _r_00m r_0m r_m : ℝ) : ℝ :=
    12 - x ^ 3 - 4 * x ^ 2 + 5 * x - 4 * r_m * x + 2 * r_m * x ^ 4 + 6 * r_m * x ^ 2 +
      12 * r_0m * x ^ 2 + 12 * r_m * x ^ 3

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽106⁾`. -/
noncomputable def i8L4Q106_4 (x _r_0000m _r_000m _r_00m _r_0m _r_m : ℝ) : ℝ :=
    -3 - x / 2

theorem i8L4_106_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s106 x = i8L4S106 x + x * (i8L4Q106_0 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x * i8L4Q106_1 x (i13Rho [zero, zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne]
      x) (i13Rho [negOne] x) + Real.log x ^ 2 * i8L4Q106_2 x (i13Rho [zero, zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x) +
      Real.log x ^ 3 * i8L4Q106_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x)
      + Real.log x ^ 4 * i8L4Q106_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero,
      zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [negOne] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s106 i8Psi4s106N0 i8Psi4s106N1 i8Psi4s106N2 i8Psi4s106N3 i8Psi4s106N4 i8Psi4s106W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0000, i13hw_00000, i13hw_000m0 hx, i13hw_00m0 hx,
    i13hw_00m00 hx, i13hw_0m0 hx, i13hw_0m00 hx, i13hw_0m000 hx, i13hw_m0 hx, i13hw_m00 hx,
    i13hw_m000 hx]
  simp only [i13hpl_rho_0000m h0, i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_0m h0,
    i13hpl_rho_m h0]
  unfold i8L4S106 i8L4Q106_0 i8L4Q106_1 i8L4Q106_2 i8L4Q106_3 i8L4Q106_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽106⁾`. -/
noncomputable def i8L4R106 (x : ℝ) : ℝ :=
  x * (i8L4Q106_0 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne]
    x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x * i8L4Q106_1 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero,
    negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 2 * i8L4Q106_2 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 3 * i8L4Q106_3 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x) +
    Real.log x ^ 4 * i8L4Q106_4 x (i13Rho [zero, zero, zero, zero, negOne] x) (i13Rho [zero, zero,
    zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))

theorem tendsto_i8L4R106 : Tendsto i8L4R106 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q106_0 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q106_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q106_1 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q106_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q106_2 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q106_2
      fun_prop)
  obtain ⟨M3, hM3⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q106_3 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q106_3
      fun_prop)
  obtain ⟨M4, hM4⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q106_4 (v 0) (v 2) (v 6) (v 18) (v 43) (v 66)) (by
      unfold i8L4Q106_4
      fun_prop)
  have H := (((((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q106_0 x (i13Rho [zero,
    zero, zero, zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne]
    x) (i13Rho [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q106_1 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q106_2 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) (f := fun x => i8L4Q106_3 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M3, fun x hx => hM3 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 4) (f := fun x => i8L4Q106_4 x (i13Rho [zero, zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [negOne] x))
      ⟨M4, fun x hx => hM4 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R106
  ring

/-- The singular part of `Ψ₄⁽107⁾` at `ξ = 0`. -/
noncomputable def i8L4S107 (x : ℝ) : ℝ :=
    56 - 32 * Real.log x - 8 * Real.log x ^ 2 - 4 / 3 * π ^ 2 - 4 / 3 * Real.log x ^ 3 +
      4 / 3 * Real.log x * π ^ 2

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽107⁾`. -/
noncomputable def i8L4Q107_0 (x r_0001 r_001 r_00m r_01 _r_01m r_0m r_0m01 r_0m1 r_1 _r_m _r_m1 : ℝ)
    : ℝ :=
    -4 - x ^ 5 - 11 * x ^ 2 + 2 * π ^ 2 - 29 / 2 * x + 13 / 2 * x ^ 3 - 35 * r_1 * x ^ 2 -
      32 * r_00m * x ^ 2 - 28 * r_1 * x ^ 3 - 24 * r_0m * x ^ 3 - 20 * r_001 * x ^ 2 -
      16 * r_01 * x ^ 3 - 8 * r_0001 * x ^ 2 - 4 * r_0m * x ^ 4 - 2 * r_1 * x ^ 6 +
      4 * r_01 * x ^ 4 + 4 * r_0m * x ^ 6 + 4 * r_1 * x ^ 5 + 5 * r_1 * x ^ 4 +
      16 * r_0m * x ^ 5 + 16 * r_0m01 * x ^ 2 + 36 * r_0m * x ^ 2 + 56 * r_1 * x +
      64 * r_0m1 * x ^ 2 + 82 * r_01 * x ^ 2 - 4 / 3 * π ^ 2 * x ^ 2 - π ^ 2 * x ^ 3 / 3 +
      π ^ 2 * x / 3 - 40 * r_0m * r_1 * x ^ 5 - 16 * r_01 * r_0m * x ^ 5 +
      8 * r_0m * r_1 * x ^ 7 + 16 * r_0m * r_1 * x ^ 4 + 16 * r_0m * r_1 * x ^ 6 -
      4 / 3 * π ^ 2 * r_1 * x - 4 / 3 * π ^ 2 * r_1 * x ^ 3 - 2 / 3 * π ^ 2 * r_1 * x ^ 4 +
      4 / 3 * π ^ 2 * r_01 * x ^ 2 + 10 / 3 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽107⁾`. -/
noncomputable def i8L4Q107_1 (x _r_0001 r_001 _r_00m r_01 r_01m r_0m _r_0m01 r_0m1 r_1 r_m r_m1 : ℝ)
    : ℝ :=
    4 + x - 11 * x ^ 3 + 2 * x ^ 5 + 4 * x ^ 4 + 14 * x ^ 2 - 66 * r_1 * x ^ 2 -
      64 * r_m1 * x ^ 2 - 36 * r_m * x ^ 2 - 26 * r_1 * x ^ 4 - 16 * r_m * x ^ 5 -
      4 * r_m * x ^ 6 + 4 * r_1 * x ^ 6 + 8 * r_001 * x ^ 2 + 8 * r_m * x ^ 3 +
      16 * r_01m * x ^ 2 + 16 * r_0m * x ^ 2 + 16 * r_0m1 * x ^ 2 + 20 * r_01 * x ^ 2 +
      24 * r_1 * x + 64 * r_1 * x ^ 3 - 16 * r_1 * r_m * x ^ 4 - 16 * r_1 * r_m * x ^ 6 -
      8 * r_1 * r_m * x ^ 7 + 40 * r_1 * r_m * x ^ 5

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽107⁾`. -/
noncomputable def i8L4Q107_2 (x _r_0001 _r_001 _r_00m r_01 _r_01m _r_0m _r_0m01 _r_0m1 r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    -6 + x ^ 3 - x + 4 * x ^ 2 - 10 * r_1 * x ^ 2 - 4 * r_01 * x ^ 2 + 2 * r_1 * x ^ 4 +
      4 * r_1 * x + 4 * r_1 * x ^ 3

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽107⁾`. -/
noncomputable def i8L4Q107_3 (_x _r_0001 _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽107⁾`. -/
noncomputable def i8L4Q107_4 (_x _r_0001 _r_001 _r_00m _r_01 _r_01m _r_0m _r_0m01 _r_0m1 _r_1 _r_m
    _r_m1 : ℝ) : ℝ :=
    0

theorem i8L4_107_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s107 x = i8L4S107 x + x * (i8L4Q107_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q107_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q107_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q107_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q107_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s107 i8Psi4s107N0 i8Psi4s107N1 i8Psi4s107N2 i8Psi4s107N3 i8Psi4s107N4 i8Psi4s107W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_01m0
    hx, i13hw_0m0 hx, i13hw_0m10 hx, i13hw_10 hx, i13hw_100 hx, i13hw_1m0 hx, i13hw_m0 hx, i13hw_m01
    hx, i13hw_m10 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_00m h0, i13hpl_rho_01 h0,
    i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0,
    i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L4S107 i8L4Q107_0 i8L4Q107_1 i8L4Q107_2 i8L4Q107_3 i8L4Q107_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽107⁾`. -/
noncomputable def i8L4R107 (x : ℝ) : ℝ :=
  x * (i8L4Q107_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x)
    (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q107_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q107_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q107_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q107_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, negOne] x) (i13Rho
    [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
    [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R107 : Tendsto i8L4R107 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q107_0 (v 0) (v 3) (v 9) (v 18) (v 27) (v 36) (v 43) (v 44) (v
      49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q107_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q107_1 (v 0) (v 3) (v 9) (v 18) (v 27) (v 36) (v 43) (v 44) (v
      49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q107_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q107_2 (v 0) (v 3) (v 9) (v 18) (v 27) (v 36) (v 43) (v 44) (v
      49) (v 65) (v 66) (v 67)) (by
      unfold i8L4Q107_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q107_0 x (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one]
    x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q107_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q107_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, one] x)
      (i13Rho [zero, one, negOne] x) (i13Rho [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R107
  unfold i8L4Q107_3 i8L4Q107_4
  ring

/-- The singular part of `Ψ₄⁽108k0⁾` at `ξ = 0`. -/
noncomputable def i8L4S108k0 (x : ℝ) : ℝ :=
    16 - 16 * Real.log x ^ 2 + 16 * Real.log x - 2 / 3 * π ^ 2 + π ^ 2 * Real.log x ^ 2 / 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽108k0⁾`. -/
noncomputable def i8L4Q108k0_0 (x r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    126 - 24 * x ^ 2 - 2 * x ^ 3 + 32 * x - 7 / 3 * π ^ 2 - 64 * r_1 * x ^ 3 - 16 * r_001 * x -
      6 * r_1 * x ^ 4 + 8 * r_001 * x ^ 4 + 16 * r_001 * x ^ 2 + 32 * r_1 * x +
      38 * r_1 * x ^ 2 + 48 * r_001 * x ^ 3 + 96 * r_0001 * x ^ 2 + 108 * r_01 * x ^ 2 -
      7 / 6 * π ^ 2 * x ^ 2 - 7 / 12 * π ^ 2 * x - π ^ 2 * x ^ 3 / 12 -
      2 * π ^ 2 * r_001 * x ^ 2 - 2 * π ^ 2 * r_1 * x ^ 3 - 2 / 3 * π ^ 2 * r_1 * x -
      π ^ 2 * r_1 * x ^ 4 / 6 + 5 / 3 * π ^ 2 * r_01 * x ^ 2 + 17 / 6 * π ^ 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽108k0⁾`. -/
noncomputable def i8L4Q108k0_1 (x _r_0001 r_001 r_01 r_1 : ℝ) : ℝ :=
    -76 - 42 * x + 4 * x ^ 3 + 24 * x ^ 2 + 7 / 3 * π ^ 2 - 108 * r_1 * x ^ 2 -
      48 * r_001 * x ^ 2 - 48 * r_01 * x ^ 3 - 16 * r_01 * x ^ 2 - 8 * r_01 * x ^ 4 +
      12 * r_1 * x ^ 4 + 16 * r_01 * x + 32 * r_1 * x + 64 * r_1 * x ^ 3 + π ^ 2 * x ^ 3 / 6 +
      4 / 3 * π ^ 2 * x ^ 2 + 11 / 6 * π ^ 2 * x + 2 * π ^ 2 * r_01 * x ^ 2 +
      2 * π ^ 2 * r_1 * x ^ 3 - 5 / 3 * π ^ 2 * r_1 * x ^ 2 - 2 / 3 * π ^ 2 * r_1 * x +
      π ^ 2 * r_1 * x ^ 4 / 3

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽108k0⁾`. -/
noncomputable def i8L4Q108k0_2 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽108k0⁾`. -/
noncomputable def i8L4Q108k0_3 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽108k0⁾`. -/
noncomputable def i8L4Q108k0_4 (_x _r_0001 _r_001 _r_01 _r_1 : ℝ) : ℝ :=
    0

theorem i8L4_108k0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k0 x = i8L4S108k0 x + x * (i8L4Q108k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x * i8L4Q108k0_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
      (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 2 * i8L4Q108k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 3 * i8L4Q108k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, one] x) (i13Rho [one] x) +
      Real.log x ^ 4 * i8L4Q108k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one]
      x) (i13Rho [zero, one] x) (i13Rho [one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s108k0 i8Psi4s108k0N0 i8Psi4s108k0N1 i8Psi4s108k0N2 i8Psi4s108k0N3 i8Psi4s108k0N4
    i8Psi4s108k0W
  simp only [hpl_zero, i13hw_00, i13hw_0010 hx, i13hw_010 hx, i13hw_10 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_01 h0, i13hpl_rho_1 h0]
  unfold i8L4S108k0 i8L4Q108k0_0 i8L4Q108k0_1 i8L4Q108k0_2 i8L4Q108k0_3 i8L4Q108k0_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽108k0⁾`. -/
noncomputable def i8L4R108k0 (x : ℝ) : ℝ :=
  x * (i8L4Q108k0_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
    one] x) (i13Rho [one] x) + Real.log x * i8L4Q108k0_1 x (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 2 * i8L4Q108k0_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 3 * i8L4Q108k0_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x) +
    Real.log x ^ 4 * i8L4Q108k0_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, one] x) (i13Rho [one] x))

theorem tendsto_i8L4R108k0 : Tendsto i8L4R108k0 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k0_0 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q108k0_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k0_1 (v 0) (v 3) (v 9) (v 27) (v 65)) (by
      unfold i8L4Q108k0_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q108k0_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q108k0_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, one] x) (i13Rho [one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R108k0
  unfold i8L4Q108k0_2 i8L4Q108k0_3 i8L4Q108k0_4
  ring

/-- The singular part of `Ψ₄⁽108k1⁾` at `ξ = 0`. -/
noncomputable def i8L4S108k1 (x : ℝ) : ℝ :=
    16 - 16 * Real.log x + 8 * Real.log x ^ 2 - 8 / 3 * Real.log x ^ 3

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽108k1⁾`. -/
noncomputable def i8L4Q108k1_0 (x r_0001 r_000m1 r_001 r_00m1 r_01 _r_0m1 r_1 _r_m1 : ℝ) : ℝ :=
    -144 - 45 * x - 29 * x ^ 2 - x ^ 3 / 2 - r_1 * x ^ 4 - 128 * r_0001 * x ^ 2 -
      48 * r_001 * x ^ 3 - 40 * r_1 * x ^ 3 - 16 * r_00m1 * x - 8 * r_001 * x ^ 4 +
      8 * r_00m1 * x ^ 4 + 16 * r_001 * x + 24 * r_00m1 * x ^ 2 + 41 * r_1 * x ^ 2 +
      42 * r_01 * x ^ 2 + 48 * r_00m1 * x ^ 3 + 84 * r_001 * x ^ 2 + 144 * r_000m1 * x ^ 2

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽108k1⁾`. -/
noncomputable def i8L4Q108k1_1 (x _r_0001 _r_000m1 r_001 r_00m1 r_01 r_0m1 r_1 _r_m1 : ℝ) : ℝ :=
    96 + x ^ 3 + 30 * x ^ 2 + 42 * x - 96 * r_00m1 * x ^ 2 - 84 * r_01 * x ^ 2 -
      48 * r_0m1 * x ^ 3 - 42 * r_1 * x ^ 2 - 24 * r_0m1 * x ^ 2 - 16 * r_01 * x -
      8 * r_0m1 * x ^ 4 + 2 * r_1 * x ^ 4 + 8 * r_01 * x ^ 4 + 16 * r_0m1 * x +
      40 * r_1 * x ^ 3 + 48 * r_01 * x ^ 3 + 80 * r_001 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽108k1⁾`. -/
noncomputable def i8L4Q108k1_2 (x _r_0001 _r_000m1 _r_001 _r_00m1 r_01 r_0m1 r_1 r_m1 : ℝ) : ℝ :=
    -24 - x ^ 3 - 18 * x - 16 * x ^ 2 - 44 * r_1 * x ^ 3 - 16 * r_01 * x ^ 2 - 8 * r_m1 * x -
      6 * r_1 * x ^ 4 + 4 * r_m1 * x ^ 4 + 8 * r_1 * x + 12 * r_m1 * x ^ 2 + 24 * r_0m1 * x ^ 2 +
      24 * r_m1 * x ^ 3 + 42 * r_1 * x ^ 2

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽108k1⁾`. -/
noncomputable def i8L4Q108k1_3 (_x _r_0001 _r_000m1 _r_001 _r_00m1 _r_01 _r_0m1 _r_1 _r_m1 : ℝ) : ℝ
    :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽108k1⁾`. -/
noncomputable def i8L4Q108k1_4 (_x _r_0001 _r_000m1 _r_001 _r_00m1 _r_01 _r_0m1 _r_1 _r_m1 : ℝ) : ℝ
    :=
    0

theorem i8L4_108k1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k1 x = i8L4S108k1 x + x * (i8L4Q108k1_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne, one] x) + Real.log x * i8L4Q108k1_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 2 * i8L4Q108k1_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 3 * i8L4Q108k1_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne, one] x) + Real.log x ^ 4 * i8L4Q108k1_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho
      [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne,
      one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
      [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s108k1 i8Psi4s108k1N0 i8Psi4s108k1N1 i8Psi4s108k1N2 i8Psi4s108k1N3 i8Psi4s108k1N4
    i8Psi4s108k1W
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0010 hx, i13hw_010 hx, i13hw_0100 hx, i13hw_0m001
    hx, i13hw_0m010 hx, i13hw_0m100 hx, i13hw_10 hx, i13hw_100 hx, i13hw_m001 hx, i13hw_m010 hx,
    i13hw_m100 hx]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0, i13hpl_rho_00m1 h0,
    i13hpl_rho_01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m1 h0]
  unfold i8L4S108k1 i8L4Q108k1_0 i8L4Q108k1_1 i8L4Q108k1_2 i8L4Q108k1_3 i8L4Q108k1_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽108k1⁾`. -/
noncomputable def i8L4R108k1 (x : ℝ) : ℝ :=
  x * (i8L4Q108k1_0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x)
    (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho
    [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne, one] x) +
    Real.log x * i8L4Q108k1_1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q108k1_2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 3 * i8L4Q108k1_3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q108k1_4 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
    negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
    one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R108k1 : Tendsto i8L4R108k1 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k1_0 (v 0) (v 3) (v 7) (v 9) (v 21) (v 27) (v 49) (v 65) (v
      67)) (by
      unfold i8L4Q108k1_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k1_1 (v 0) (v 3) (v 7) (v 9) (v 21) (v 27) (v 49) (v 65) (v
      67)) (by
      unfold i8L4Q108k1_1
      fun_prop)
  obtain ⟨M2, hM2⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k1_2 (v 0) (v 3) (v 7) (v 9) (v 21) (v 27) (v 49) (v 65) (v
      67)) (by
      unfold i8L4Q108k1_2
      fun_prop)
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q108k1_0 x (i13Rho [zero,
    zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x)
    (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q108k1_1 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) (f := fun x => i8L4Q108k1_2 x (i13Rho [zero, zero, zero,
      one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero,
      zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x)
      (i13Rho [negOne, one] x))
      ⟨M2, fun x hx => hM2 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R108k1
  unfold i8L4Q108k1_3 i8L4Q108k1_4
  ring

/-- The singular part of `Ψ₄⁽108k2⁾` at `ξ = 0`. -/
noncomputable def i8L4S108k2 (x : ℝ) : ℝ :=
    -24 - 6 * Real.log x ^ 2 + 24 * Real.log x

/-- The coefficient of `ξ log^0 ξ` in the regular part of `Ψ₄⁽108k2⁾`. -/
noncomputable def i8L4Q108k2_0 (x r_00001 r_0001 r_000m1 r_001 r_00m1 r_01 r_0m1 r_1 _r_m1 : ℝ) : ℝ
    :=
    107 + 65 / 4 * x ^ 2 + 335 / 8 * x - 72 * r_000m1 * x ^ 2 - 48 * r_00m1 * x ^ 3 -
      36 * r_001 * x ^ 3 - 24 * r_0001 * x - 12 * r_001 * x - 8 * r_001 * x ^ 2 -
      8 * r_00m1 * x ^ 4 - 3 * r_001 * x ^ 4 + 2 * r_0m1 * x ^ 4 + 8 * r_0m1 * x +
      12 * r_0001 * x ^ 4 + 12 * r_1 * x + 14 * r_1 * x ^ 3 + 16 * r_00m1 * x +
      24 * r_0m1 * x ^ 3 + 30 * r_0m1 * x ^ 2 + 72 * r_0001 * x ^ 3 + 108 * r_00001 * x ^ 2 -
      105 / 4 * r_1 * x ^ 2 - 5 / 2 * r_01 * x ^ 2 + r_1 * x ^ 4 / 4

/-- The coefficient of `ξ log^1 ξ` in the regular part of `Ψ₄⁽108k2⁾`. -/
noncomputable def i8L4Q108k2_1 (x _r_00001 r_0001 _r_000m1 r_001 r_00m1 r_01 r_0m1 r_1 r_m1 : ℝ) : ℝ
    :=
    -71 / 2 - 12 * x ^ 2 - 101 / 4 * x - x ^ 3 / 4 - 36 * r_0001 * x ^ 2 - 36 * r_001 * x ^ 3 -
      30 * r_m1 * x ^ 2 - 24 * r_m1 * x ^ 3 - 14 * r_1 * x ^ 3 - 8 * r_0m1 * x - 8 * r_m1 * x -
      6 * r_001 * x ^ 4 - 2 * r_m1 * x ^ 4 + 3 * r_01 * x ^ 4 + 4 * r_0m1 * x ^ 4 +
      8 * r_01 * x ^ 2 + 12 * r_001 * x + 12 * r_01 * x + 12 * r_1 * x + 24 * r_00m1 * x ^ 2 +
      24 * r_0m1 * x ^ 3 + 36 * r_01 * x ^ 3 - r_1 * x ^ 4 / 2 + 5 / 2 * r_1 * x ^ 2

/-- The coefficient of `ξ log^2 ξ` in the regular part of `Ψ₄⁽108k2⁾`. -/
noncomputable def i8L4Q108k2_2 (_x _r_00001 _r_0001 _r_000m1 _r_001 _r_00m1 _r_01 _r_0m1 _r_1 _r_m1
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^3 ξ` in the regular part of `Ψ₄⁽108k2⁾`. -/
noncomputable def i8L4Q108k2_3 (_x _r_00001 _r_0001 _r_000m1 _r_001 _r_00m1 _r_01 _r_0m1 _r_1 _r_m1
    : ℝ) : ℝ :=
    0

/-- The coefficient of `ξ log^4 ξ` in the regular part of `Ψ₄⁽108k2⁾`. -/
noncomputable def i8L4Q108k2_4 (_x _r_00001 _r_0001 _r_000m1 _r_001 _r_00m1 _r_01 _r_0m1 _r_1 _r_m1
    : ℝ) : ℝ :=
    0

theorem i8L4_108k2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k2 x = i8L4S108k2 x + x * (i8L4Q108k2_0 x (i13Rho [zero, zero, zero, zero, one] x)
      (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero,
      zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
      negOne, one] x) (i13Rho [one] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L4Q108k2_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L4Q108k2_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L4Q108k2_3 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 4 * i8L4Q108k2_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
      [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [one] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi4s108k2 i8Psi4s108k2N0 i8Psi4s108k2N1 i8Psi4s108k2N2 i8Psi4s108k2N3 i8Psi4s108k2N4
    i8Psi4s108k2W
  simp only [hpl_zero, i13hw_00, i13hw_00010 hx, i13hw_0010 hx, i13hw_00m10 hx, i13hw_010 hx,
    i13hw_0m10 hx, i13hw_10 hx, i13hw_m01 hx, i13hw_m10 hx]
  simp only [i13hpl_rho_00001 h0, i13hpl_rho_0001 h0, i13hpl_rho_000m1 h0, i13hpl_rho_001 h0,
    i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m1 h0]
  unfold i8L4S108k2 i8L4Q108k2_0 i8L4Q108k2_1 i8L4Q108k2_2 i8L4Q108k2_3 i8L4Q108k2_4
  field_simp
  ring

/-- The regular part `ξ ∑ⱼ log^j ξ Qⱼ` of `Ψ₄⁽108k2⁾`. -/
noncomputable def i8L4R108k2 (x : ℝ) : ℝ :=
  x * (i8L4Q108k2_0 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x)
    (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero,
    negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho
    [negOne, one] x) + Real.log x * i8L4Q108k2_1 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho
    [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one]
    x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x)
    (i13Rho [one] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 2 * i8L4Q108k2_2 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
    x) (i13Rho [negOne, one] x) + Real.log x ^ 3 * i8L4Q108k2_3 x (i13Rho [zero, zero, zero, zero,
    one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho
    [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero,
    negOne, one] x) (i13Rho [one] x) (i13Rho [negOne, one] x) +
    Real.log x ^ 4 * i8L4Q108k2_4 x (i13Rho [zero, zero, zero, zero, one] x) (i13Rho [zero, zero,
    zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x) (i13Rho [zero, zero, one] x) (i13Rho
    [zero, zero, negOne, one] x) (i13Rho [zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [one]
    x) (i13Rho [negOne, one] x))

theorem tendsto_i8L4R108k2 : Tendsto i8L4R108k2 (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M0, hM0⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k2_0 (v 0) (v 1) (v 3) (v 7) (v 9) (v 21) (v 27) (v 49) (v
      65) (v 67)) (by
      unfold i8L4Q108k2_0
      fun_prop)
  obtain ⟨M1, hM1⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 71 → ℝ => i8L4Q108k2_1 (v 0) (v 1) (v 3) (v 7) (v 9) (v 21) (v 27) (v 49) (v
      65) (v 67)) (by
      unfold i8L4Q108k2_1
      fun_prop)
  have H := ((i13_tendsto_mul_log_pow_mul (j := 0) (f := fun x => i8L4Q108k2_0 x (i13Rho [zero,
    zero, zero, zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne,
    one] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
    (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne, one] x))
      ⟨M0, fun x hx => hM0 (i8L4V x) (norm_i8L4V_le hx)⟩).add
    (i13_tendsto_mul_log_pow_mul (j := 1) (f := fun x => i8L4Q108k2_1 x (i13Rho [zero, zero, zero,
      zero, one] x) (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne, one] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, one] x)
      (i13Rho [zero, negOne, one] x) (i13Rho [one] x) (i13Rho [negOne, one] x))
      ⟨M1, fun x hx => hM1 (i8L4V x) (norm_i8L4V_le hx)⟩))
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards with x
  unfold i8L4R108k2
  unfold i8L4Q108k2_2 i8L4Q108k2_3 i8L4Q108k2_4
  ring

/-- The regular parts of group 9. -/
noncomputable def i8L4RG9 (x : ℝ) : ℝ :=
  i8L4R101 x + i8L4R102 x + i8L4R103 x + i8L4R104 x + i8L4R105 x + i8L4R106 x +
    i8L4R107 x + i8L4R108k0 x + i8L4R108k1 x + i8L4R108k2 x

theorem tendsto_i8L4RG9 : Tendsto i8L4RG9 (𝓝[>] 0) (𝓝 0) := by
  have H := (((((((((tendsto_i8L4R101.add tendsto_i8L4R102).add tendsto_i8L4R103).add
    tendsto_i8L4R104).add tendsto_i8L4R105).add tendsto_i8L4R106).add tendsto_i8L4R107).add
    tendsto_i8L4R108k0).add tendsto_i8L4R108k1).add tendsto_i8L4R108k2)
  simp only [add_zero] at H
  exact H

end QED.ThreeLoopD
