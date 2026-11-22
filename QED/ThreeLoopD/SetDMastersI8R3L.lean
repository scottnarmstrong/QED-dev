/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Lb

/-!
# Set (d), master `I₈`: the limit of `F₃ - A₃` at infinity

The singular parts of the pieces of `Ψ₃` and of `-A₃` add up to the constant
`2003/16 - 25π²/12 - 8ζ(3)`, so (`QED.ThreeLoopD.i8D3_eq`)

  `F₃ - A₃ = 2003/16 - 25π²/12 - 8ζ(3) + ξ (Q₀ + Q₁ log ξ + Q₂ log² ξ + Q₃ log³ ξ)`

with bounded `Qⱼ`; hence `F₃ - A₃ → 2003/16 - 25π²/12 - 8ζ(3)` as `t → ∞`.

## Main results

* `QED.ThreeLoopD.i8D3_eq`.
* `QED.ThreeLoopD.tendsto_i8F3_sub_prim3`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The coefficient `Q0` of `ξ log^0 ξ` in `F₃ - A₃`. -/
noncomputable def i8L3Q0 (x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111
    r_011m r_01m r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 : ℝ)
    : ℝ :=
    i8L3Qa0 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qb0 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qd0 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qe0 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qf0 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qg0 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qh0 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3QP0 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1

/-- The coefficient `Q1` of `ξ log^1 ξ` in `F₃ - A₃`. -/
noncomputable def i8L3Q1 (x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111
    r_011m r_01m r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 : ℝ)
    : ℝ :=
    i8L3Qa1 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qb1 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qd1 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qe1 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qf1 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qg1 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qh1 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3QP1 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1

/-- The coefficient `Q2` of `ξ log^2 ξ` in `F₃ - A₃`. -/
noncomputable def i8L3Q2 (x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111
    r_011m r_01m r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 : ℝ)
    : ℝ :=
    i8L3Qa2 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qb2 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qd2 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qe2 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qf2 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qg2 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qh2 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3QP2 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1

/-- The coefficient `Q3` of `ξ log^3 ξ` in `F₃ - A₃`. -/
noncomputable def i8L3Q3 (x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111
    r_011m r_01m r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 : ℝ)
    : ℝ :=
    i8L3Qa3 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qb3 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qd3 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qe3 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qf3 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qg3 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3Qh3 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1 +
      i8L3QP3 x r_0001 r_000m r_001 r_0011 r_001m r_00m r_00m1 r_00mm r_01 r_011 r_0111 r_011m r_01m
      r_01m1 r_01mm r_0m r_0m01 r_0m1 r_0m11 r_0m1m r_0mm r_0mm1 r_0mmm r_1 r_m r_m1

theorem i8D3_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8D3 x = 2003 / 16 - 8 * zeta3 - 25 / 12 * π ^ 2 +
      x * (i8L3Q0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
      one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one]
      x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x * i8L3Q1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x)
      (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one,
      negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero,
      zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero,
      one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho
      [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x)
      (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne,
      one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho
      [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x)
      (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 2 * i8L3Q2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
      negOne] x) (i13Rho [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero,
      one, negOne] x) (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho
      [zero, zero, negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho
      [zero, one, one, one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x)
      (i13Rho [zero, one, negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero,
      negOne] x) (i13Rho [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero,
      negOne, one, one] x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x)
      (i13Rho [zero, negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one]
      x) (i13Rho [negOne] x) (i13Rho [negOne, one] x) +
      Real.log x ^ 3 * i8L3Q3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero,
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
  unfold i8D3 i8Psi3
  rw [sub_eq_add_neg, i8L3_a_eq hx, i8L3_b_eq hx, i8L3_d_eq hx, i8L3_e_eq hx, i8L3_f_eq hx,
    i8L3_g_eq hx, i8L3_h_eq hx, i8L3_P_eq hx]
  unfold i8L3Sa i8L3Sb i8L3Sd i8L3Se i8L3Sf i8L3Sg i8L3Sh i8L3SP i8L3Q0 i8L3Q1 i8L3Q2 i8L3Q3
  field_simp
  ring

/-! ### Boundedness of the polynomials -/

/-- The vector of the arguments `ξ, ρ_w(ξ)` of the polynomials `Qⱼ`. -/
noncomputable def i8L3V (x : ℝ) : Fin 27 → ℝ :=
  ![x, i13Rho [zero, zero, zero, one] x, i13Rho [zero, zero, zero, negOne] x, i13Rho [zero, zero,
    one] x, i13Rho [zero, zero, one, one] x, i13Rho [zero, zero, one, negOne] x, i13Rho [zero, zero,
    negOne] x, i13Rho [zero, zero, negOne, one] x, i13Rho [zero, zero, negOne, negOne] x, i13Rho
    [zero, one] x, i13Rho [zero, one, one] x, i13Rho [zero, one, one, one] x, i13Rho [zero, one,
    one, negOne] x, i13Rho [zero, one, negOne] x, i13Rho [zero, one, negOne, one] x, i13Rho [zero,
    one, negOne, negOne] x, i13Rho [zero, negOne] x, i13Rho [zero, negOne, zero, one] x, i13Rho
    [zero, negOne, one] x, i13Rho [zero, negOne, one, one] x, i13Rho [zero, negOne, one, negOne] x,
    i13Rho [zero, negOne, negOne] x, i13Rho [zero, negOne, negOne, one] x, i13Rho [zero, negOne,
    negOne, negOne] x, i13Rho [one] x, i13Rho [negOne] x, i13Rho [negOne, one] x]

theorem norm_i8L3V_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : ‖i8L3V x‖ ≤ 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  fin_cases i
  · show ‖x‖ ≤ 2
    rw [Real.norm_eq_abs, abs_of_pos hx.1]
    linarith [hx.2]
  · show ‖i13Rho [zero, zero, zero, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, zero, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, one, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, one, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, negOne, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, zero, negOne, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one, one, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one, one, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one, negOne, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, one, negOne, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne, zero, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne, one, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne, one, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne, negOne, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [zero, negOne, negOne, negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [negOne] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx
  · show ‖i13Rho [negOne, one] x‖ ≤ 2
    rw [Real.norm_eq_abs]
    exact abs_i13Rho_le (by decide) (by decide) hx

theorem i8L3Q0_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i8L3Q0 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
      one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one]
      x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)| ≤ M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 27 → ℝ => i8L3Q0 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
      (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21) (v 22) (v
      23) (v 24) (v 25) (v 26)) (by
      unfold i8L3Q0 i8L3Qa0 i8L3Qb0 i8L3Qd0 i8L3Qe0 i8L3Qf0 i8L3Qg0 i8L3Qh0 i8L3QP0
      fun_prop)
  exact ⟨M, fun x hx => hM (i8L3V x) (norm_i8L3V_le hx)⟩

theorem i8L3Q1_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i8L3Q1 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
      one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one]
      x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)| ≤ M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 27 → ℝ => i8L3Q1 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
      (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21) (v 22) (v
      23) (v 24) (v 25) (v 26)) (by
      unfold i8L3Q1 i8L3Qa1 i8L3Qb1 i8L3Qd1 i8L3Qe1 i8L3Qf1 i8L3Qg1 i8L3Qh1 i8L3QP1
      fun_prop)
  exact ⟨M, fun x hx => hM (i8L3V x) (norm_i8L3V_le hx)⟩

theorem i8L3Q2_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i8L3Q2 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
      one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one]
      x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)| ≤ M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 27 → ℝ => i8L3Q2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
      (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21) (v 22) (v
      23) (v 24) (v 25) (v 26)) (by
      unfold i8L3Q2 i8L3Qa2 i8L3Qb2 i8L3Qd2 i8L3Qe2 i8L3Qf2 i8L3Qg2 i8L3Qh2 i8L3QP2
      fun_prop)
  exact ⟨M, fun x hx => hM (i8L3V x) (norm_i8L3V_le hx)⟩

theorem i8L3Q3_bdd : ∃ M, ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
    |i8L3Q3 x (i13Rho [zero, zero, zero, one] x) (i13Rho [zero, zero, zero, negOne] x) (i13Rho
      [zero, zero, one] x) (i13Rho [zero, zero, one, one] x) (i13Rho [zero, zero, one, negOne] x)
      (i13Rho [zero, zero, negOne] x) (i13Rho [zero, zero, negOne, one] x) (i13Rho [zero, zero,
      negOne, negOne] x) (i13Rho [zero, one] x) (i13Rho [zero, one, one] x) (i13Rho [zero, one, one,
      one] x) (i13Rho [zero, one, one, negOne] x) (i13Rho [zero, one, negOne] x) (i13Rho [zero, one,
      negOne, one] x) (i13Rho [zero, one, negOne, negOne] x) (i13Rho [zero, negOne] x) (i13Rho
      [zero, negOne, zero, one] x) (i13Rho [zero, negOne, one] x) (i13Rho [zero, negOne, one, one]
      x) (i13Rho [zero, negOne, one, negOne] x) (i13Rho [zero, negOne, negOne] x) (i13Rho [zero,
      negOne, negOne, one] x) (i13Rho [zero, negOne, negOne, negOne] x) (i13Rho [one] x) (i13Rho
      [negOne] x) (i13Rho [negOne, one] x)| ≤ M := by
  obtain ⟨M, hM⟩ := i13_bdd_of_continuous
    (F := fun v : Fin 27 → ℝ => i8L3Q3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
      (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) (v 20) (v 21) (v 22) (v
      23) (v 24) (v 25) (v 26)) (by
      unfold i8L3Q3 i8L3Qa3 i8L3Qb3 i8L3Qd3 i8L3Qe3 i8L3Qf3 i8L3Qg3 i8L3Qh3 i8L3QP3
      fun_prop)
  exact ⟨M, fun x hx => hM (i8L3V x) (norm_i8L3V_le hx)⟩

/-! ### The limit -/

theorem tendsto_i8D3 : Tendsto i8D3 (𝓝[>] 0) (𝓝 (2003 / 16 - 8 * zeta3 - 25 / 12 * π ^ 2)) := by
  have H := (((i13_tendsto_mul_log_pow_mul (j := 0) i8L3Q0_bdd).add
    (i13_tendsto_mul_log_pow_mul (j := 1) i8L3Q1_bdd)).add
    (i13_tendsto_mul_log_pow_mul (j := 2) i8L3Q2_bdd)).add
    (i13_tendsto_mul_log_pow_mul (j := 3) i8L3Q3_bdd) |>.const_add (2003 / 16 - 8 * zeta3 -
      25 / 12 * π ^ 2)
  rw [add_zero, add_zero, add_zero, add_zero] at H
  refine H.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
  rw [i8D3_eq hx]
  ring

/-- **The limit** `F₃ - A₃ → 2003/16 - 25π²/12 - 8ζ(3)` as `t → ∞`. -/
theorem tendsto_i8F3_sub_prim3 :
    Tendsto (fun t => i8F3 t - i8Prim3 t) atTop (𝓝 (2003 / 16 - 8 * zeta3 - 25 / 12 * π ^ 2)) :=
  (tendsto_i8D3.comp tendsto_i13Xi_atTop).congr'
    (eventually_atTop.2 ⟨1, fun t ht => (i8F3_sub_prim3 (by linarith)).symm⟩)

end QED.ThreeLoopD
