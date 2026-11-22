/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3La

/-!
# Set (d), master `I₈`: the expansions at `ξ = 0` of the pieces `f`, `g`, `h` of `Ψ₃` and of `-A₃`

Each piece equals its singular part plus `ξ ∑ⱼ log^j ξ Qⱼ` (see `QED.ThreeLoopD.SetDMastersI8R3LD`).

## Main results

* `QED.ThreeLoopD.i8L3_f_eq`, `QED.ThreeLoopD.i8L3_g_eq`, `QED.ThreeLoopD.i8L3_h_eq`,
  `QED.ThreeLoopD.i8L3_P_eq`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

theorem i8L3_f_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3f x = i8L3Sf x + x * (i8L3Qf0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L3Qf1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L3Qf2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L3Qf3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
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
  unfold i8Psi3f i8Psi3fN0 i8Psi3fN1 i8Psi3fN2 i8Psi3fN3 i8Psi3fN4 i8Psi3fW
  simp only [hpl_zero, i13hw_00, i13hw_10 hx, i13hw_11 hx, i13hw_000, i13hw_010 hx, i13hw_100 hx,
    i13hw_101 hx, i13hw_110 hx, i13hw_0010 hx, i13hw_0100 hx, i13hw_0101 hx, i13hw_0110 hx,
    i8hw_0000]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_0011 h0, i13hpl_rho_01 h0,
    i13hpl_rho_011 h0, i13hpl_rho_1 h0]
  unfold i8L3Sf i8L3Qf0 i8L3Qf1 i8L3Qf2 i8L3Qf3
  field_simp
  ring

theorem i8L3_g_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3g x = i8L3Sg x + x * (i8L3Qg0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L3Qg1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L3Qg2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L3Qg3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
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
  unfold i8Psi3g i8Psi3gN0 i8Psi3gN1 i8Psi3gN2 i8Psi3gN3 i8Psi3gN4 i8Psi3gW
  simp only [hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_10 hx, i13hw_1m hx, i13hw_11 hx, i13hw_000,
    i13hw_0m0 hx, i13hw_010 hx, i13hw_m00 hx, i13hw_m01 hx, i13hw_m10 hx, i13hw_10m hx, i13hw_1m0
    hx, i8hw_1m1 hx, i8hw_11m hx, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_0m10 hx, i13hw_01m0 hx,
    i8hw_010m hx]
  simp only [i13hpl_rho_000m h0, i13hpl_rho_001 h0, i13hpl_rho_001m h0, i13hpl_rho_00m h0,
    i13hpl_rho_00m1 h0, i13hpl_rho_01 h0, i13hpl_rho_011 h0, i13hpl_rho_011m h0, i13hpl_rho_01m h0,
    i13hpl_rho_01m1 h0, i13hpl_rho_0m h0, i13hpl_rho_0m01 h0, i13hpl_rho_0m1 h0, i13hpl_rho_0m11 h0,
    i13hpl_rho_1 h0, i13hpl_rho_m h0, i13hpl_rho_m1 h0]
  unfold i8L3Sg i8L3Qg0 i8L3Qg1 i8L3Qg2 i8L3Qg3
  field_simp
  ring

theorem i8L3_h_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3h x = i8L3Sh x + x * (i8L3Qh0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L3Qh1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L3Qh2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L3Qh3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
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
  unfold i8Psi3h i8Psi3hN0 i8Psi3hN1 i8Psi3hN2 i8Psi3hN3 i8Psi3hN4 i8Psi3hW
  simp only [hpl_zero, i13hw_00, i13hw_10 hx, i13hw_11 hx, i13hw_000, i13hw_010 hx, i13hw_100 hx,
    i13hw_101 hx, i13hw_110 hx, i13hw_111 hx, i13hw_0010 hx, i13hw_0100 hx, i13hw_0101 hx,
    i13hw_0110 hx, i8hw_0000]
  simp only [i13hpl_rho_0001 h0, i13hpl_rho_001 h0, i13hpl_rho_0011 h0, i13hpl_rho_01 h0,
    i13hpl_rho_011 h0, i13hpl_rho_0111 h0, i13hpl_rho_1 h0]
  unfold i8L3Sh i8L3Qh0 i8L3Qh1 i8L3Qh2 i8L3Qh3
  field_simp
  ring

theorem i8L3_P_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    -i8Prim3x x = i8L3SP x + x * (i8L3QP0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero,
      zero, negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero,
      zero, one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x)
      (i13Rho [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x)
      (i13Rho [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one,
      negOne] x) (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho
      [zero, negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho
      [zero, negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne,
      negOne] x) (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x)
      (i13Rho [one] x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L3QP1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne]
      x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L3QP2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L3QP3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
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
  unfold i8Prim3x
  simp only [i13_log_one_sub_eq hx]
  simp only [i13hpl_rho_1 h0]
  unfold i8L3SP i8L3QP0 i8L3QP1 i8L3QP2 i8L3QP3
  field_simp
  ring

end QED.ThreeLoopD
