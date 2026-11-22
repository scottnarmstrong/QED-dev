/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3LD

/-!
# Set (d), master `I₈`: the expansions at `ξ = 0` of the pieces `a`, `b`, `d`, `e` of `Ψ₃`

Each piece equals its singular part plus `ξ ∑ⱼ log^j ξ Qⱼ` (see `QED.ThreeLoopD.SetDMastersI8R3LD`).

## Main results

* `QED.ThreeLoopD.i8L3_a_eq`, `QED.ThreeLoopD.i8L3_b_eq`, `QED.ThreeLoopD.i8L3_d_eq`,
  `QED.ThreeLoopD.i8L3_e_eq`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

theorem i8L3_a_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3a x = i8L3Sa x + x * (i8L3Qa0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L3Qa1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L3Qa2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L3Qa3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi3a i8Psi3aN0 i8Psi3aN1 i8Psi3aN2 i8Psi3aN3 i8Psi3aN4 i8Psi3aW
  simp only [hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_mm hx, i13hw_000, i13hw_0m0 hx, i13hw_m00 hx,
    i13hw_m0m hx, i13hw_mm0 hx, i8hw_mmm hx, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_0mm0 hx, i8hw_0m0m
    hx, i8hw_0000]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_00m h0, i13hpl_rho_00mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0mm h0, i13hpl_rho_0mmm h0, i13hpl_rho_m h0]
  unfold i8L3Sa i8L3Qa0 i8L3Qa1 i8L3Qa2 i8L3Qa3
  field_simp
  ring

theorem i8L3_b_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3b x = i8L3Sb x + x * (i8L3Qb0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L3Qb1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L3Qb2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L3Qb3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi3b i8Psi3bN0 i8Psi3bN1 i8Psi3bN2 i8Psi3bN3 i8Psi3bN4 i8Psi3bW
  simp only [hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_10 hx, i13hw_000, i13hw_0m0 hx, i13hw_010 hx,
    i13hw_m00 hx, i13hw_m01 hx, i13hw_m10 hx, i13hw_100 hx, i13hw_1m0 hx, i13hw_00m0 hx, i13hw_0010
    hx, i13hw_0m00 hx, i13hw_0m10 hx, i13hw_0100 hx, i13hw_01m0 hx, i8hw_0000]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_000m h0, i13hpl_rho_001 h0, i13hpl_rho_00m h0,
    i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0,
    i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L3Sb i8L3Qb0 i8L3Qb1 i8L3Qb2 i8L3Qb3
  field_simp
  ring

theorem i8L3_d_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3d x = i8L3Sd x + x * (i8L3Qd0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L3Qd1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L3Qd2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L3Qd3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi3d i8Psi3dN0 i8Psi3dN1 i8Psi3dN2 i8Psi3dN3 i8Psi3dN4 i8Psi3dW
  simp only [hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_10 hx, i13hw_1m hx, i13hw_000, i13hw_0m0 hx,
    i13hw_010 hx, i13hw_m00 hx, i13hw_m01 hx, i13hw_m10 hx, i13hw_10m hx, i13hw_1m0 hx]
  simp only [i13hpl_rho_001 h0, i13hpl_rho_00m h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0,
    i13hpl_rho_0m h0, i13hpl_rho_0m1 h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L3Sd i8L3Qd0 i8L3Qd1 i8L3Qd2 i8L3Qd3
  field_simp
  ring

theorem i8L3_e_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3e x = i8L3Se x + x * (i8L3Qe0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L3Qe1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L3Qe2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L3Qe3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x)) := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  unfold i8Psi3e i8Psi3eN0 i8Psi3eN1 i8Psi3eN2 i8Psi3eN3 i8Psi3eN4 i8Psi3eW
  simp only [hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_mm hx, i13hw_1m hx, i13hw_0m0 hx, i13hw_m0m hx,
    i13hw_mm0 hx, i13hw_10m hx, i8hw_m1m hx, i8hw_1mm hx, i13hw_00m0 hx, i13hw_0mm0 hx, i8hw_0m0m
    hx, i8hw_010m hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0, i13hpl_rho_00m1 h0,
    i13hpl_rho_00mm h0, i13hpl_rho_01 h0, i13hpl_rho_01m h0, i13hpl_rho_01mm h0, i13hpl_rho_0m h0,
    i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_0m1m h0, i13hpl_rho_0mm h0, i13hpl_rho_0mm1
    h0, i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L3Se i8L3Qe0 i8L3Qe1 i8L3Qe2 i8L3Qe3
  field_simp
  ring

end QED.ThreeLoopD
