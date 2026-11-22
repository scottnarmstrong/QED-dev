/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4V12

/-!
# Set (d), master `I₈`: the parts of `Ψ₄` by `(i, j, l)`

The sub-pieces of `Ψ₄` are summed into the parts with given `(i, j, l)` (from
`t Bᵢ Aⱼ (-λ)^l/l!`), through chunks of at most ten. For each part: its derivative, the identity
`Ψ' ξ' = p`, continuity on `(0, 1]` and the value at `ξ = 1`.

## Main results

* `QED.ThreeLoopD.i8Psi4X400D_mul` and its companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The `(i, j, l) = (0, 4, 0)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X040 (x : ℝ) : ℝ :=
  i8Psi4s0 x

/-- The derivative of `i8Psi4X040`. -/
noncomputable def i8Psi4X040D (x : ℝ) : ℝ :=
  i8Psi4s0D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X040`. -/
noncomputable def i8P4X040 (x : ℝ) : ℝ :=
  i8P4s0 x

theorem hasDerivAt_i8Psi4X040 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X040 (i8Psi4X040D
    x) x := by
  unfold i8Psi4X040 i8Psi4X040D
  exact (hasDerivAt_i8Psi4s0 hx)

theorem i8Psi4X040D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X040D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X040 x := by
  unfold i8Psi4X040D i8P4X040
  rw [← i8Psi4s0D_mul hx]

theorem continuousOn_i8Psi4X040 : ContinuousOn i8Psi4X040 (Ioc 0 1) := by
  unfold i8Psi4X040
  exact continuousOn_i8Psi4s0

theorem i8Psi4X040_one : i8Psi4X040 1 = 509 / 32 - zeta5 - zeta3 / 4 - π ^ 2 / 48 -
    π ^ 4 / 180 := by
  unfold i8Psi4X040
  rw [i8Psi4s0_one]

/-- The `(i, j, l) = (1, 3, 0)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X130 (x : ℝ) : ℝ :=
  i8Psi4s1 x

/-- The derivative of `i8Psi4X130`. -/
noncomputable def i8Psi4X130D (x : ℝ) : ℝ :=
  i8Psi4s1D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X130`. -/
noncomputable def i8P4X130 (x : ℝ) : ℝ :=
  i8P4s1 x

theorem hasDerivAt_i8Psi4X130 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X130 (i8Psi4X130D
    x) x := by
  unfold i8Psi4X130 i8Psi4X130D
  exact (hasDerivAt_i8Psi4s1 hx)

theorem i8Psi4X130D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X130D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X130 x := by
  unfold i8Psi4X130D i8P4X130
  rw [← i8Psi4s1D_mul hx]

theorem continuousOn_i8Psi4X130 : ContinuousOn i8Psi4X130 (Ioc 0 1) := by
  unfold i8Psi4X130
  exact continuousOn_i8Psi4s1

theorem i8Psi4X130_one : i8Psi4X130 1 = -11 / 8 - zeta3 - π ^ 2 / 8 - π ^ 4 / 90 := by
  unfold i8Psi4X130
  rw [i8Psi4s1_one]

/-- The `(i, j, l) = (2, 2, 0)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X220 (x : ℝ) : ℝ :=
  i8Psi4s2 x + i8Psi4s3 x + i8Psi4s4 x + i8Psi4s5 x + i8Psi4s6 x + i8Psi4s7 x +
    i8Psi4s8 x + i8Psi4s9 x

/-- The derivative of `i8Psi4X220`. -/
noncomputable def i8Psi4X220D (x : ℝ) : ℝ :=
  i8Psi4s2D x + i8Psi4s3D x + i8Psi4s4D x + i8Psi4s5D x + i8Psi4s6D x + i8Psi4s7D x +
    i8Psi4s8D x + i8Psi4s9D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X220`. -/
noncomputable def i8P4X220 (x : ℝ) : ℝ :=
  i8P4s2 x + i8P4s3 x + i8P4s4 x + i8P4s5 x + i8P4s6 x + i8P4s7 x + i8P4s8 x + i8P4s9 x

theorem hasDerivAt_i8Psi4X220 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X220 (i8Psi4X220D
    x) x := by
  unfold i8Psi4X220 i8Psi4X220D
  exact ((((((((hasDerivAt_i8Psi4s2 hx).add (hasDerivAt_i8Psi4s3 hx)).add (hasDerivAt_i8Psi4s4
    hx)).add (hasDerivAt_i8Psi4s5 hx)).add (hasDerivAt_i8Psi4s6 hx)).add (hasDerivAt_i8Psi4s7
    hx)).add (hasDerivAt_i8Psi4s8 hx)).add (hasDerivAt_i8Psi4s9 hx))

theorem i8Psi4X220D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X220D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X220 x := by
  unfold i8Psi4X220D i8P4X220
  rw [← i8Psi4s2D_mul hx, ← i8Psi4s3D_mul hx, ← i8Psi4s4D_mul hx, ← i8Psi4s5D_mul hx, ←
    i8Psi4s6D_mul hx, ← i8Psi4s7D_mul hx, ← i8Psi4s8D_mul hx, ← i8Psi4s9D_mul hx]
  ring

theorem continuousOn_i8Psi4X220 : ContinuousOn i8Psi4X220 (Ioc 0 1) := by
  unfold i8Psi4X220
  exact (((((((continuousOn_i8Psi4s2.add continuousOn_i8Psi4s3).add continuousOn_i8Psi4s4).add
    continuousOn_i8Psi4s5).add continuousOn_i8Psi4s6).add continuousOn_i8Psi4s7).add
    continuousOn_i8Psi4s8).add continuousOn_i8Psi4s9)

theorem i8Psi4X220_one : i8Psi4X220 1 = -108 + 33 * zeta5 - 7 / 360 * π ^ 4 + 21 / 2 * zeta3 +
    79 / 24 * π ^ 2 - 2 * π ^ 2 * zeta3 := by
  unfold i8Psi4X220
  rw [i8Psi4s2_one, i8Psi4s3_one, i8Psi4s4_one, i8Psi4s5_one, i8Psi4s6_one, i8Psi4s7_one,
    i8Psi4s8_one, i8Psi4s9_one]
  ring

/-- Chunk 0 of the `(i, j, l) = (3, 1, 0)` part of `Ψ₄`. -/
noncomputable def i8Psi4X310c0 (x : ℝ) : ℝ :=
  i8Psi4s10 x + i8Psi4s11 x + i8Psi4s12 x + i8Psi4s13 x + i8Psi4s14 x + i8Psi4s15 x +
    i8Psi4s16 x + i8Psi4s17 x + i8Psi4s18 x + i8Psi4s19 x

/-- The derivative of `i8Psi4X310c0`. -/
noncomputable def i8Psi4X310c0D (x : ℝ) : ℝ :=
  i8Psi4s10D x + i8Psi4s11D x + i8Psi4s12D x + i8Psi4s13D x + i8Psi4s14D x +
    i8Psi4s15D x + i8Psi4s16D x + i8Psi4s17D x + i8Psi4s18D x + i8Psi4s19D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X310c0`. -/
noncomputable def i8P4X310c0 (x : ℝ) : ℝ :=
  i8P4s10 x + i8P4s11 x + i8P4s12 x + i8P4s13 x + i8P4s14 x + i8P4s15 x + i8P4s16 x +
    i8P4s17 x + i8P4s18 x + i8P4s19 x

theorem hasDerivAt_i8Psi4X310c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X310c0
    (i8Psi4X310c0D x) x := by
  unfold i8Psi4X310c0 i8Psi4X310c0D
  exact ((((((((((hasDerivAt_i8Psi4s10 hx).add (hasDerivAt_i8Psi4s11 hx)).add (hasDerivAt_i8Psi4s12
    hx)).add (hasDerivAt_i8Psi4s13 hx)).add (hasDerivAt_i8Psi4s14 hx)).add (hasDerivAt_i8Psi4s15
    hx)).add (hasDerivAt_i8Psi4s16 hx)).add (hasDerivAt_i8Psi4s17 hx)).add (hasDerivAt_i8Psi4s18
    hx)).add (hasDerivAt_i8Psi4s19 hx))

theorem i8Psi4X310c0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X310c0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X310c0 x := by
  unfold i8Psi4X310c0D i8P4X310c0
  rw [← i8Psi4s10D_mul hx, ← i8Psi4s11D_mul hx, ← i8Psi4s12D_mul hx, ← i8Psi4s13D_mul hx, ←
    i8Psi4s14D_mul hx, ← i8Psi4s15D_mul hx, ← i8Psi4s16D_mul hx, ← i8Psi4s17D_mul hx, ←
    i8Psi4s18D_mul hx, ← i8Psi4s19D_mul hx]
  ring

theorem continuousOn_i8Psi4X310c0 : ContinuousOn i8Psi4X310c0 (Ioc 0 1) := by
  unfold i8Psi4X310c0
  exact (((((((((continuousOn_i8Psi4s10.add continuousOn_i8Psi4s11).add continuousOn_i8Psi4s12).add
    continuousOn_i8Psi4s13).add continuousOn_i8Psi4s14).add continuousOn_i8Psi4s15).add
    continuousOn_i8Psi4s16).add continuousOn_i8Psi4s17).add continuousOn_i8Psi4s18).add
    continuousOn_i8Psi4s19)

theorem i8Psi4X310c0_one : i8Psi4X310c0 1 = -245 / 8 + 12 * zeta3 + π ^ 4 / 72 +
    47 / 24 * π ^ 2 := by
  unfold i8Psi4X310c0
  rw [i8Psi4s10_one, i8Psi4s11_one, i8Psi4s12_one, i8Psi4s13_one, i8Psi4s14_one, i8Psi4s15_one,
    i8Psi4s16_one, i8Psi4s17_one, i8Psi4s18_one, i8Psi4s19_one]
  ring

/-- Chunk 1 of the `(i, j, l) = (3, 1, 0)` part of `Ψ₄`. -/
noncomputable def i8Psi4X310c1 (x : ℝ) : ℝ :=
  i8Psi4s20 x + i8Psi4s21 x

/-- The derivative of `i8Psi4X310c1`. -/
noncomputable def i8Psi4X310c1D (x : ℝ) : ℝ :=
  i8Psi4s20D x + i8Psi4s21D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X310c1`. -/
noncomputable def i8P4X310c1 (x : ℝ) : ℝ :=
  i8P4s20 x + i8P4s21 x

theorem hasDerivAt_i8Psi4X310c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X310c1
    (i8Psi4X310c1D x) x := by
  unfold i8Psi4X310c1 i8Psi4X310c1D
  exact ((hasDerivAt_i8Psi4s20 hx).add (hasDerivAt_i8Psi4s21 hx))

theorem i8Psi4X310c1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X310c1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X310c1 x := by
  unfold i8Psi4X310c1D i8P4X310c1
  rw [← i8Psi4s20D_mul hx, ← i8Psi4s21D_mul hx]
  ring

theorem continuousOn_i8Psi4X310c1 : ContinuousOn i8Psi4X310c1 (Ioc 0 1) := by
  unfold i8Psi4X310c1
  exact (continuousOn_i8Psi4s20.add continuousOn_i8Psi4s21)

theorem i8Psi4X310c1_one : i8Psi4X310c1 1 = -2119 / 8 + 60 * zeta3 + 66 * zeta5 +
    49 / 360 * π ^ 4 + 353 / 24 * π ^ 2 - 8 * π ^ 2 * zeta3 := by
  unfold i8Psi4X310c1
  rw [i8Psi4s20_one, i8Psi4s21_one]
  ring

/-- The `(i, j, l) = (3, 1, 0)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X310 (x : ℝ) : ℝ :=
  i8Psi4X310c0 x + i8Psi4X310c1 x

/-- The derivative of `i8Psi4X310`. -/
noncomputable def i8Psi4X310D (x : ℝ) : ℝ :=
  i8Psi4X310c0D x + i8Psi4X310c1D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X310`. -/
noncomputable def i8P4X310 (x : ℝ) : ℝ :=
  i8P4X310c0 x + i8P4X310c1 x

theorem hasDerivAt_i8Psi4X310 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X310 (i8Psi4X310D
    x) x := by
  unfold i8Psi4X310 i8Psi4X310D
  exact ((hasDerivAt_i8Psi4X310c0 hx).add (hasDerivAt_i8Psi4X310c1 hx))

theorem i8Psi4X310D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X310D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X310 x := by
  unfold i8Psi4X310D i8P4X310
  rw [← i8Psi4X310c0D_mul hx, ← i8Psi4X310c1D_mul hx]
  ring

theorem continuousOn_i8Psi4X310 : ContinuousOn i8Psi4X310 (Ioc 0 1) := by
  unfold i8Psi4X310
  exact (continuousOn_i8Psi4X310c0.add continuousOn_i8Psi4X310c1)

theorem i8Psi4X310_one : i8Psi4X310 1 = -591 / 2 + 66 * zeta5 + 72 * zeta3 + 3 / 20 * π ^ 4 +
    50 / 3 * π ^ 2 - 8 * π ^ 2 * zeta3 := by
  unfold i8Psi4X310
  rw [i8Psi4X310c0_one, i8Psi4X310c1_one]
  ring

/-- Chunk 0 of the `(i, j, l) = (4, 0, 0)` part of `Ψ₄`. -/
noncomputable def i8Psi4X400c0 (x : ℝ) : ℝ :=
  i8Psi4s22 x + i8Psi4s23 x + i8Psi4s24 x + i8Psi4s25 x + i8Psi4s26 x + i8Psi4s27 x +
    i8Psi4s28 x + i8Psi4s29 x + i8Psi4s30 x + i8Psi4s31 x

/-- The derivative of `i8Psi4X400c0`. -/
noncomputable def i8Psi4X400c0D (x : ℝ) : ℝ :=
  i8Psi4s22D x + i8Psi4s23D x + i8Psi4s24D x + i8Psi4s25D x + i8Psi4s26D x +
    i8Psi4s27D x + i8Psi4s28D x + i8Psi4s29D x + i8Psi4s30D x + i8Psi4s31D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X400c0`. -/
noncomputable def i8P4X400c0 (x : ℝ) : ℝ :=
  i8P4s22 x + i8P4s23 x + i8P4s24 x + i8P4s25 x + i8P4s26 x + i8P4s27 x + i8P4s28 x +
    i8P4s29 x + i8P4s30 x + i8P4s31 x

theorem hasDerivAt_i8Psi4X400c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X400c0
    (i8Psi4X400c0D x) x := by
  unfold i8Psi4X400c0 i8Psi4X400c0D
  exact ((((((((((hasDerivAt_i8Psi4s22 hx).add (hasDerivAt_i8Psi4s23 hx)).add (hasDerivAt_i8Psi4s24
    hx)).add (hasDerivAt_i8Psi4s25 hx)).add (hasDerivAt_i8Psi4s26 hx)).add (hasDerivAt_i8Psi4s27
    hx)).add (hasDerivAt_i8Psi4s28 hx)).add (hasDerivAt_i8Psi4s29 hx)).add (hasDerivAt_i8Psi4s30
    hx)).add (hasDerivAt_i8Psi4s31 hx))

theorem i8Psi4X400c0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X400c0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X400c0 x := by
  unfold i8Psi4X400c0D i8P4X400c0
  rw [← i8Psi4s22D_mul hx, ← i8Psi4s23D_mul hx, ← i8Psi4s24D_mul hx, ← i8Psi4s25D_mul hx, ←
    i8Psi4s26D_mul hx, ← i8Psi4s27D_mul hx, ← i8Psi4s28D_mul hx, ← i8Psi4s29D_mul hx, ←
    i8Psi4s30D_mul hx, ← i8Psi4s31D_mul hx]
  ring

theorem continuousOn_i8Psi4X400c0 : ContinuousOn i8Psi4X400c0 (Ioc 0 1) := by
  unfold i8Psi4X400c0
  exact (((((((((continuousOn_i8Psi4s22.add continuousOn_i8Psi4s23).add continuousOn_i8Psi4s24).add
    continuousOn_i8Psi4s25).add continuousOn_i8Psi4s26).add continuousOn_i8Psi4s27).add
    continuousOn_i8Psi4s28).add continuousOn_i8Psi4s29).add continuousOn_i8Psi4s30).add
    continuousOn_i8Psi4s31)

theorem i8Psi4X400c0_one : i8Psi4X400c0 1 = 385 / 8 + 64 * Li 4 (1 / 2) - 79 / 2 * zeta3 -
    π ^ 4 / 4 + 3 / 2 * zeta5 + 8 / 3 * Real.log 2 ^ 4 + 55 / 24 * π ^ 2 +
    32 * Real.log 2 * zeta3 - 8 / 3 * π ^ 2 * Real.log 2 ^ 2 - 7 / 6 * π ^ 2 * zeta3 +
    16 / 3 * Real.log 2 * π ^ 2 := by
  unfold i8Psi4X400c0
  rw [i8Psi4s22_one, i8Psi4s23_one, i8Psi4s24_one, i8Psi4s25_one, i8Psi4s26_one, i8Psi4s27_one,
    i8Psi4s28_one, i8Psi4s29_one, i8Psi4s30_one, i8Psi4s31_one]
  ring

/-- Chunk 1 of the `(i, j, l) = (4, 0, 0)` part of `Ψ₄`. -/
noncomputable def i8Psi4X400c1 (x : ℝ) : ℝ :=
  i8Psi4s32 x + i8Psi4s33 x + i8Psi4s34 x + i8Psi4s35 x + i8Psi4s36 x + i8Psi4s37 x +
    i8Psi4s38 x + i8Psi4s39 x + i8Psi4s40 x + i8Psi4s41 x

/-- The derivative of `i8Psi4X400c1`. -/
noncomputable def i8Psi4X400c1D (x : ℝ) : ℝ :=
  i8Psi4s32D x + i8Psi4s33D x + i8Psi4s34D x + i8Psi4s35D x + i8Psi4s36D x +
    i8Psi4s37D x + i8Psi4s38D x + i8Psi4s39D x + i8Psi4s40D x + i8Psi4s41D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X400c1`. -/
noncomputable def i8P4X400c1 (x : ℝ) : ℝ :=
  i8P4s32 x + i8P4s33 x + i8P4s34 x + i8P4s35 x + i8P4s36 x + i8P4s37 x + i8P4s38 x +
    i8P4s39 x + i8P4s40 x + i8P4s41 x

theorem hasDerivAt_i8Psi4X400c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X400c1
    (i8Psi4X400c1D x) x := by
  unfold i8Psi4X400c1 i8Psi4X400c1D
  exact ((((((((((hasDerivAt_i8Psi4s32 hx).add (hasDerivAt_i8Psi4s33 hx)).add (hasDerivAt_i8Psi4s34
    hx)).add (hasDerivAt_i8Psi4s35 hx)).add (hasDerivAt_i8Psi4s36 hx)).add (hasDerivAt_i8Psi4s37
    hx)).add (hasDerivAt_i8Psi4s38 hx)).add (hasDerivAt_i8Psi4s39 hx)).add (hasDerivAt_i8Psi4s40
    hx)).add (hasDerivAt_i8Psi4s41 hx))

theorem i8Psi4X400c1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X400c1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X400c1 x := by
  unfold i8Psi4X400c1D i8P4X400c1
  rw [← i8Psi4s32D_mul hx, ← i8Psi4s33D_mul hx, ← i8Psi4s34D_mul hx, ← i8Psi4s35D_mul hx, ←
    i8Psi4s36D_mul hx, ← i8Psi4s37D_mul hx, ← i8Psi4s38D_mul hx, ← i8Psi4s39D_mul hx, ←
    i8Psi4s40D_mul hx, ← i8Psi4s41D_mul hx]
  ring

theorem continuousOn_i8Psi4X400c1 : ContinuousOn i8Psi4X400c1 (Ioc 0 1) := by
  unfold i8Psi4X400c1
  exact (((((((((continuousOn_i8Psi4s32.add continuousOn_i8Psi4s33).add continuousOn_i8Psi4s34).add
    continuousOn_i8Psi4s35).add continuousOn_i8Psi4s36).add continuousOn_i8Psi4s37).add
    continuousOn_i8Psi4s38).add continuousOn_i8Psi4s39).add continuousOn_i8Psi4s40).add
    continuousOn_i8Psi4s41)

theorem i8Psi4X400c1_one : i8Psi4X400c1 1 = 897 / 16 - 64 * Li 4 (1 / 2) + 7 * zeta3 -
    35 / 6 * π ^ 2 - 31 / 2 * zeta5 - 8 / 3 * Real.log 2 ^ 4 + 17 / 60 * π ^ 4 -
    32 * Real.log 2 * zeta3 - 16 / 3 * Real.log 2 * π ^ 2 + 8 / 3 * π ^ 2 * Real.log 2 ^ 2 +
    11 / 6 * π ^ 2 * zeta3 := by
  unfold i8Psi4X400c1
  rw [i8Psi4s32_one, i8Psi4s33_one, i8Psi4s34_one, i8Psi4s35_one, i8Psi4s36_one, i8Psi4s37_one,
    i8Psi4s38_one, i8Psi4s39_one, i8Psi4s40_one, i8Psi4s41_one]
  ring

/-- Chunk 2 of the `(i, j, l) = (4, 0, 0)` part of `Ψ₄`. -/
noncomputable def i8Psi4X400c2 (x : ℝ) : ℝ :=
  i8Psi4s42 x + i8Psi4s43 x + i8Psi4s44 x + i8Psi4s45 x + i8Psi4s46 x + i8Psi4s47 x +
    i8Psi4s48 x + i8Psi4s49 x + i8Psi4s50 x

/-- The derivative of `i8Psi4X400c2`. -/
noncomputable def i8Psi4X400c2D (x : ℝ) : ℝ :=
  i8Psi4s42D x + i8Psi4s43D x + i8Psi4s44D x + i8Psi4s45D x + i8Psi4s46D x +
    i8Psi4s47D x + i8Psi4s48D x + i8Psi4s49D x + i8Psi4s50D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X400c2`. -/
noncomputable def i8P4X400c2 (x : ℝ) : ℝ :=
  i8P4s42 x + i8P4s43 x + i8P4s44 x + i8P4s45 x + i8P4s46 x + i8P4s47 x + i8P4s48 x +
    i8P4s49 x + i8P4s50 x

theorem hasDerivAt_i8Psi4X400c2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X400c2
    (i8Psi4X400c2D x) x := by
  unfold i8Psi4X400c2 i8Psi4X400c2D
  exact (((((((((hasDerivAt_i8Psi4s42 hx).add (hasDerivAt_i8Psi4s43 hx)).add (hasDerivAt_i8Psi4s44
    hx)).add (hasDerivAt_i8Psi4s45 hx)).add (hasDerivAt_i8Psi4s46 hx)).add (hasDerivAt_i8Psi4s47
    hx)).add (hasDerivAt_i8Psi4s48 hx)).add (hasDerivAt_i8Psi4s49 hx)).add (hasDerivAt_i8Psi4s50
    hx))

theorem i8Psi4X400c2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X400c2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X400c2 x := by
  unfold i8Psi4X400c2D i8P4X400c2
  rw [← i8Psi4s42D_mul hx, ← i8Psi4s43D_mul hx, ← i8Psi4s44D_mul hx, ← i8Psi4s45D_mul hx, ←
    i8Psi4s46D_mul hx, ← i8Psi4s47D_mul hx, ← i8Psi4s48D_mul hx, ← i8Psi4s49D_mul hx, ←
    i8Psi4s50D_mul hx]
  ring

theorem continuousOn_i8Psi4X400c2 : ContinuousOn i8Psi4X400c2 (Ioc 0 1) := by
  unfold i8Psi4X400c2
  exact ((((((((continuousOn_i8Psi4s42.add continuousOn_i8Psi4s43).add continuousOn_i8Psi4s44).add
    continuousOn_i8Psi4s45).add continuousOn_i8Psi4s46).add continuousOn_i8Psi4s47).add
    continuousOn_i8Psi4s48).add continuousOn_i8Psi4s49).add continuousOn_i8Psi4s50)

theorem i8Psi4X400c2_one : i8Psi4X400c2 1 = -875 / 16 + 36 * zeta5 + 11 / 18 * π ^ 4 +
    113 / 2 * zeta3 + 449 / 24 * π ^ 2 - 6 * π ^ 2 * zeta3 := by
  unfold i8Psi4X400c2
  rw [i8Psi4s42_one, i8Psi4s43_one, i8Psi4s44_one, i8Psi4s45_one, i8Psi4s46_one, i8Psi4s47_one,
    i8Psi4s48_one, i8Psi4s49_one, i8Psi4s50_one]
  ring

/-- The `(i, j, l) = (4, 0, 0)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X400 (x : ℝ) : ℝ :=
  i8Psi4X400c0 x + i8Psi4X400c1 x + i8Psi4X400c2 x

/-- The derivative of `i8Psi4X400`. -/
noncomputable def i8Psi4X400D (x : ℝ) : ℝ :=
  i8Psi4X400c0D x + i8Psi4X400c1D x + i8Psi4X400c2D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X400`. -/
noncomputable def i8P4X400 (x : ℝ) : ℝ :=
  i8P4X400c0 x + i8P4X400c1 x + i8P4X400c2 x

theorem hasDerivAt_i8Psi4X400 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X400 (i8Psi4X400D
    x) x := by
  unfold i8Psi4X400 i8Psi4X400D
  exact (((hasDerivAt_i8Psi4X400c0 hx).add (hasDerivAt_i8Psi4X400c1 hx)).add
    (hasDerivAt_i8Psi4X400c2 hx))

theorem i8Psi4X400D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X400D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X400 x := by
  unfold i8Psi4X400D i8P4X400
  rw [← i8Psi4X400c0D_mul hx, ← i8Psi4X400c1D_mul hx, ← i8Psi4X400c2D_mul hx]
  ring

theorem continuousOn_i8Psi4X400 : ContinuousOn i8Psi4X400 (Ioc 0 1) := by
  unfold i8Psi4X400
  exact ((continuousOn_i8Psi4X400c0.add continuousOn_i8Psi4X400c1).add continuousOn_i8Psi4X400c2)

theorem i8Psi4X400_one : i8Psi4X400 1 = 99 / 2 + 22 * zeta5 + 24 * zeta3 + 29 / 45 * π ^ 4 +
    91 / 6 * π ^ 2 - 16 / 3 * π ^ 2 * zeta3 := by
  unfold i8Psi4X400
  rw [i8Psi4X400c0_one, i8Psi4X400c1_one, i8Psi4X400c2_one]
  ring

/-- Chunk 0 of the `(i, j, l) = (0, 3, 1)` part of `Ψ₄`. -/
noncomputable def i8Psi4X031c0 (x : ℝ) : ℝ :=
  i8Psi4s51 x + i8Psi4s52 x + i8Psi4s53 x + i8Psi4s54 x + i8Psi4s55 x + i8Psi4s56 x +
    i8Psi4s57 x + i8Psi4s58 x + i8Psi4s59 x + i8Psi4s60 x

/-- The derivative of `i8Psi4X031c0`. -/
noncomputable def i8Psi4X031c0D (x : ℝ) : ℝ :=
  i8Psi4s51D x + i8Psi4s52D x + i8Psi4s53D x + i8Psi4s54D x + i8Psi4s55D x +
    i8Psi4s56D x + i8Psi4s57D x + i8Psi4s58D x + i8Psi4s59D x + i8Psi4s60D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X031c0`. -/
noncomputable def i8P4X031c0 (x : ℝ) : ℝ :=
  i8P4s51 x + i8P4s52 x + i8P4s53 x + i8P4s54 x + i8P4s55 x + i8P4s56 x + i8P4s57 x +
    i8P4s58 x + i8P4s59 x + i8P4s60 x

theorem hasDerivAt_i8Psi4X031c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X031c0
    (i8Psi4X031c0D x) x := by
  unfold i8Psi4X031c0 i8Psi4X031c0D
  exact ((((((((((hasDerivAt_i8Psi4s51 hx).add (hasDerivAt_i8Psi4s52 hx)).add (hasDerivAt_i8Psi4s53
    hx)).add (hasDerivAt_i8Psi4s54 hx)).add (hasDerivAt_i8Psi4s55 hx)).add (hasDerivAt_i8Psi4s56
    hx)).add (hasDerivAt_i8Psi4s57 hx)).add (hasDerivAt_i8Psi4s58 hx)).add (hasDerivAt_i8Psi4s59
    hx)).add (hasDerivAt_i8Psi4s60 hx))

theorem i8Psi4X031c0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X031c0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X031c0 x := by
  unfold i8Psi4X031c0D i8P4X031c0
  rw [← i8Psi4s51D_mul hx, ← i8Psi4s52D_mul hx, ← i8Psi4s53D_mul hx, ← i8Psi4s54D_mul hx, ←
    i8Psi4s55D_mul hx, ← i8Psi4s56D_mul hx, ← i8Psi4s57D_mul hx, ← i8Psi4s58D_mul hx, ←
    i8Psi4s59D_mul hx, ← i8Psi4s60D_mul hx]
  ring

theorem continuousOn_i8Psi4X031c0 : ContinuousOn i8Psi4X031c0 (Ioc 0 1) := by
  unfold i8Psi4X031c0
  exact (((((((((continuousOn_i8Psi4s51.add continuousOn_i8Psi4s52).add continuousOn_i8Psi4s53).add
    continuousOn_i8Psi4s54).add continuousOn_i8Psi4s55).add continuousOn_i8Psi4s56).add
    continuousOn_i8Psi4s57).add continuousOn_i8Psi4s58).add continuousOn_i8Psi4s59).add
    continuousOn_i8Psi4s60)

theorem i8Psi4X031c0_one : i8Psi4X031c0 1 = -149 / 16 - 6 * Real.log 2 ^ 2 - 4 * Li 4 (1 / 2) +
    16 * Li 5 (1 / 2) + 20 * Real.log 2 - 63 / 8 * zeta5 - 37 / 8 * zeta3 - Real.log 2 ^ 4 / 6 +
    5 / 3 * π ^ 2 + 8 / 15 * Real.log 2 ^ 5 + 37 / 720 * π ^ 4 + 7 * zeta3 * Real.log 2 ^ 2 +
    16 * Real.log 2 * Li 4 (1 / 2) - 7 / 2 * Real.log 2 * zeta3 - 7 / 12 * π ^ 2 * zeta3 -
    4 / 9 * π ^ 2 * Real.log 2 ^ 3 + π ^ 2 * Real.log 2 ^ 2 / 6 := by
  unfold i8Psi4X031c0
  rw [i8Psi4s51_one, i8Psi4s52_one, i8Psi4s53_one, i8Psi4s54_one, i8Psi4s55_one, i8Psi4s56_one,
    i8Psi4s57_one, i8Psi4s58_one, i8Psi4s59_one, i8Psi4s60_one]
  ring

/-- Chunk 1 of the `(i, j, l) = (0, 3, 1)` part of `Ψ₄`. -/
noncomputable def i8Psi4X031c1 (x : ℝ) : ℝ :=
  i8Psi4s61 x + i8Psi4s62 x + i8Psi4s63 x + i8Psi4s64 x + i8Psi4s65 x + i8Psi4s66 x

/-- The derivative of `i8Psi4X031c1`. -/
noncomputable def i8Psi4X031c1D (x : ℝ) : ℝ :=
  i8Psi4s61D x + i8Psi4s62D x + i8Psi4s63D x + i8Psi4s64D x + i8Psi4s65D x + i8Psi4s66D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X031c1`. -/
noncomputable def i8P4X031c1 (x : ℝ) : ℝ :=
  i8P4s61 x + i8P4s62 x + i8P4s63 x + i8P4s64 x + i8P4s65 x + i8P4s66 x

theorem hasDerivAt_i8Psi4X031c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X031c1
    (i8Psi4X031c1D x) x := by
  unfold i8Psi4X031c1 i8Psi4X031c1D
  exact ((((((hasDerivAt_i8Psi4s61 hx).add (hasDerivAt_i8Psi4s62 hx)).add (hasDerivAt_i8Psi4s63
    hx)).add (hasDerivAt_i8Psi4s64 hx)).add (hasDerivAt_i8Psi4s65 hx)).add (hasDerivAt_i8Psi4s66
    hx))

theorem i8Psi4X031c1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X031c1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X031c1 x := by
  unfold i8Psi4X031c1D i8P4X031c1
  rw [← i8Psi4s61D_mul hx, ← i8Psi4s62D_mul hx, ← i8Psi4s63D_mul hx, ← i8Psi4s64D_mul hx, ←
    i8Psi4s65D_mul hx, ← i8Psi4s66D_mul hx]
  ring

theorem continuousOn_i8Psi4X031c1 : ContinuousOn i8Psi4X031c1 (Ioc 0 1) := by
  unfold i8Psi4X031c1
  exact (((((continuousOn_i8Psi4s61.add continuousOn_i8Psi4s62).add continuousOn_i8Psi4s63).add
    continuousOn_i8Psi4s64).add continuousOn_i8Psi4s65).add continuousOn_i8Psi4s66)

theorem i8Psi4X031c1_one : i8Psi4X031c1 1 = 99 / 8 - 20 * Real.log 2 - 16 * Li 5 (1 / 2) +
    4 * Li 4 (1 / 2) + 6 * Real.log 2 ^ 2 - 91 / 48 * π ^ 2 - 17 / 360 * π ^ 4 -
    8 / 15 * Real.log 2 ^ 5 + Real.log 2 ^ 4 / 6 + 27 / 8 * zeta3 + 47 / 8 * zeta5 -
    16 * Real.log 2 * Li 4 (1 / 2) - 7 * zeta3 * Real.log 2 ^ 2 - π ^ 2 * Real.log 2 ^ 2 / 6 +
    3 / 4 * π ^ 2 * zeta3 + 4 / 9 * π ^ 2 * Real.log 2 ^ 3 + 7 / 2 * Real.log 2 * zeta3 := by
  unfold i8Psi4X031c1
  rw [i8Psi4s61_one, i8Psi4s62_one, i8Psi4s63_one, i8Psi4s64_one, i8Psi4s65_one, i8Psi4s66_one]
  ring

/-- The `(i, j, l) = (0, 3, 1)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X031 (x : ℝ) : ℝ :=
  i8Psi4X031c0 x + i8Psi4X031c1 x

/-- The derivative of `i8Psi4X031`. -/
noncomputable def i8Psi4X031D (x : ℝ) : ℝ :=
  i8Psi4X031c0D x + i8Psi4X031c1D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X031`. -/
noncomputable def i8P4X031 (x : ℝ) : ℝ :=
  i8P4X031c0 x + i8P4X031c1 x

theorem hasDerivAt_i8Psi4X031 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X031 (i8Psi4X031D
    x) x := by
  unfold i8Psi4X031 i8Psi4X031D
  exact ((hasDerivAt_i8Psi4X031c0 hx).add (hasDerivAt_i8Psi4X031c1 hx))

theorem i8Psi4X031D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X031D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X031 x := by
  unfold i8Psi4X031D i8P4X031
  rw [← i8Psi4X031c0D_mul hx, ← i8Psi4X031c1D_mul hx]
  ring

theorem continuousOn_i8Psi4X031 : ContinuousOn i8Psi4X031 (Ioc 0 1) := by
  unfold i8Psi4X031
  exact (continuousOn_i8Psi4X031c0.add continuousOn_i8Psi4X031c1)

theorem i8Psi4X031_one : i8Psi4X031 1 = 49 / 16 - 2 * zeta5 - 11 / 48 * π ^ 2 - 5 / 4 * zeta3 +
    π ^ 4 / 240 + π ^ 2 * zeta3 / 6 := by
  unfold i8Psi4X031
  rw [i8Psi4X031c0_one, i8Psi4X031c1_one]
  ring

/-- The `(i, j, l) = (1, 2, 1)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X121 (x : ℝ) : ℝ :=
  i8Psi4s67 x + i8Psi4s68 x + i8Psi4s69 x + i8Psi4s70 x + i8Psi4s71 x + i8Psi4s72 x +
    i8Psi4s73 x + i8Psi4s74 x + i8Psi4s75 x

/-- The derivative of `i8Psi4X121`. -/
noncomputable def i8Psi4X121D (x : ℝ) : ℝ :=
  i8Psi4s67D x + i8Psi4s68D x + i8Psi4s69D x + i8Psi4s70D x + i8Psi4s71D x +
    i8Psi4s72D x + i8Psi4s73D x + i8Psi4s74D x + i8Psi4s75D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X121`. -/
noncomputable def i8P4X121 (x : ℝ) : ℝ :=
  i8P4s67 x + i8P4s68 x + i8P4s69 x + i8P4s70 x + i8P4s71 x + i8P4s72 x + i8P4s73 x +
    i8P4s74 x + i8P4s75 x

theorem hasDerivAt_i8Psi4X121 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X121 (i8Psi4X121D
    x) x := by
  unfold i8Psi4X121 i8Psi4X121D
  exact (((((((((hasDerivAt_i8Psi4s67 hx).add (hasDerivAt_i8Psi4s68 hx)).add (hasDerivAt_i8Psi4s69
    hx)).add (hasDerivAt_i8Psi4s70 hx)).add (hasDerivAt_i8Psi4s71 hx)).add (hasDerivAt_i8Psi4s72
    hx)).add (hasDerivAt_i8Psi4s73 hx)).add (hasDerivAt_i8Psi4s74 hx)).add (hasDerivAt_i8Psi4s75
    hx))

theorem i8Psi4X121D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X121D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X121 x := by
  unfold i8Psi4X121D i8P4X121
  rw [← i8Psi4s67D_mul hx, ← i8Psi4s68D_mul hx, ← i8Psi4s69D_mul hx, ← i8Psi4s70D_mul hx, ←
    i8Psi4s71D_mul hx, ← i8Psi4s72D_mul hx, ← i8Psi4s73D_mul hx, ← i8Psi4s74D_mul hx, ←
    i8Psi4s75D_mul hx]
  ring

theorem continuousOn_i8Psi4X121 : ContinuousOn i8Psi4X121 (Ioc 0 1) := by
  unfold i8Psi4X121
  exact ((((((((continuousOn_i8Psi4s67.add continuousOn_i8Psi4s68).add continuousOn_i8Psi4s69).add
    continuousOn_i8Psi4s70).add continuousOn_i8Psi4s71).add continuousOn_i8Psi4s72).add
    continuousOn_i8Psi4s73).add continuousOn_i8Psi4s74).add continuousOn_i8Psi4s75)

theorem i8Psi4X121_one : i8Psi4X121 1 = -161 / 2 + 9 * π ^ 2 + 40 * zeta3 + 64 * Li 4 (1 / 2) -
    61 / 72 * π ^ 4 + 8 / 3 * Real.log 2 ^ 4 - 12 * Real.log 2 * π ^ 2 +
    16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4X121
  rw [i8Psi4s67_one, i8Psi4s68_one, i8Psi4s69_one, i8Psi4s70_one, i8Psi4s71_one, i8Psi4s72_one,
    i8Psi4s73_one, i8Psi4s74_one, i8Psi4s75_one]
  ring

/-- Chunk 0 of the `(i, j, l) = (2, 1, 1)` part of `Ψ₄`. -/
noncomputable def i8Psi4X211c0 (x : ℝ) : ℝ :=
  i8Psi4s76 x + i8Psi4s77 x + i8Psi4s78 x + i8Psi4s79 x + i8Psi4s80 x + i8Psi4s81 x +
    i8Psi4s82 x + i8Psi4s83 x + i8Psi4s84 x + i8Psi4s85 x

/-- The derivative of `i8Psi4X211c0`. -/
noncomputable def i8Psi4X211c0D (x : ℝ) : ℝ :=
  i8Psi4s76D x + i8Psi4s77D x + i8Psi4s78D x + i8Psi4s79D x + i8Psi4s80D x +
    i8Psi4s81D x + i8Psi4s82D x + i8Psi4s83D x + i8Psi4s84D x + i8Psi4s85D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X211c0`. -/
noncomputable def i8P4X211c0 (x : ℝ) : ℝ :=
  i8P4s76 x + i8P4s77 x + i8P4s78 x + i8P4s79 x + i8P4s80 x + i8P4s81 x + i8P4s82 x +
    i8P4s83 x + i8P4s84 x + i8P4s85 x

theorem hasDerivAt_i8Psi4X211c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X211c0
    (i8Psi4X211c0D x) x := by
  unfold i8Psi4X211c0 i8Psi4X211c0D
  exact ((((((((((hasDerivAt_i8Psi4s76 hx).add (hasDerivAt_i8Psi4s77 hx)).add (hasDerivAt_i8Psi4s78
    hx)).add (hasDerivAt_i8Psi4s79 hx)).add (hasDerivAt_i8Psi4s80 hx)).add (hasDerivAt_i8Psi4s81
    hx)).add (hasDerivAt_i8Psi4s82 hx)).add (hasDerivAt_i8Psi4s83 hx)).add (hasDerivAt_i8Psi4s84
    hx)).add (hasDerivAt_i8Psi4s85 hx))

theorem i8Psi4X211c0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X211c0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X211c0 x := by
  unfold i8Psi4X211c0D i8P4X211c0
  rw [← i8Psi4s76D_mul hx, ← i8Psi4s77D_mul hx, ← i8Psi4s78D_mul hx, ← i8Psi4s79D_mul hx, ←
    i8Psi4s80D_mul hx, ← i8Psi4s81D_mul hx, ← i8Psi4s82D_mul hx, ← i8Psi4s83D_mul hx, ←
    i8Psi4s84D_mul hx, ← i8Psi4s85D_mul hx]
  ring

theorem continuousOn_i8Psi4X211c0 : ContinuousOn i8Psi4X211c0 (Ioc 0 1) := by
  unfold i8Psi4X211c0
  exact (((((((((continuousOn_i8Psi4s76.add continuousOn_i8Psi4s77).add continuousOn_i8Psi4s78).add
    continuousOn_i8Psi4s79).add continuousOn_i8Psi4s80).add continuousOn_i8Psi4s81).add
    continuousOn_i8Psi4s82).add continuousOn_i8Psi4s83).add continuousOn_i8Psi4s84).add
    continuousOn_i8Psi4s85)

theorem i8Psi4X211c0_one : i8Psi4X211c0 1 = -97 / 4 - 160 * Real.log 2 + 128 * Li 4 (1 / 2) -
    135 / 4 * zeta5 - 19 / 15 * π ^ 4 + 16 / 3 * Real.log 2 ^ 4 + 283 / 4 * zeta3 +
    629 / 24 * π ^ 2 - 32 * Real.log 2 * π ^ 2 + 32 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4X211c0
  rw [i8Psi4s76_one, i8Psi4s77_one, i8Psi4s78_one, i8Psi4s79_one, i8Psi4s80_one, i8Psi4s81_one,
    i8Psi4s82_one, i8Psi4s83_one, i8Psi4s84_one, i8Psi4s85_one]
  ring

/-- Chunk 1 of the `(i, j, l) = (2, 1, 1)` part of `Ψ₄`. -/
noncomputable def i8Psi4X211c1 (x : ℝ) : ℝ :=
  i8Psi4s86 x + i8Psi4s87 x

/-- The derivative of `i8Psi4X211c1`. -/
noncomputable def i8Psi4X211c1D (x : ℝ) : ℝ :=
  i8Psi4s86D x + i8Psi4s87D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X211c1`. -/
noncomputable def i8P4X211c1 (x : ℝ) : ℝ :=
  i8P4s86 x + i8P4s87 x

theorem hasDerivAt_i8Psi4X211c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X211c1
    (i8Psi4X211c1D x) x := by
  unfold i8Psi4X211c1 i8Psi4X211c1D
  exact ((hasDerivAt_i8Psi4s86 hx).add (hasDerivAt_i8Psi4s87 hx))

theorem i8Psi4X211c1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X211c1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X211c1 x := by
  unfold i8Psi4X211c1D i8P4X211c1
  rw [← i8Psi4s86D_mul hx, ← i8Psi4s87D_mul hx]
  ring

theorem continuousOn_i8Psi4X211c1 : ContinuousOn i8Psi4X211c1 (Ioc 0 1) := by
  unfold i8Psi4X211c1
  exact (continuousOn_i8Psi4s86.add continuousOn_i8Psi4s87)

theorem i8Psi4X211c1_one : i8Psi4X211c1 1 = -589 / 2 + 160 * Real.log 2 + 81 / 4 * zeta5 +
    119 / 360 * π ^ 4 + 445 / 24 * π ^ 2 + 501 / 4 * zeta3 - 32 * Real.log 2 * π ^ 2 -
    3 / 2 * π ^ 2 * zeta3 := by
  unfold i8Psi4X211c1
  rw [i8Psi4s86_one, i8Psi4s87_one]
  ring

/-- The `(i, j, l) = (2, 1, 1)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X211 (x : ℝ) : ℝ :=
  i8Psi4X211c0 x + i8Psi4X211c1 x

/-- The derivative of `i8Psi4X211`. -/
noncomputable def i8Psi4X211D (x : ℝ) : ℝ :=
  i8Psi4X211c0D x + i8Psi4X211c1D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X211`. -/
noncomputable def i8P4X211 (x : ℝ) : ℝ :=
  i8P4X211c0 x + i8P4X211c1 x

theorem hasDerivAt_i8Psi4X211 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X211 (i8Psi4X211D
    x) x := by
  unfold i8Psi4X211 i8Psi4X211D
  exact ((hasDerivAt_i8Psi4X211c0 hx).add (hasDerivAt_i8Psi4X211c1 hx))

theorem i8Psi4X211D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X211D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X211 x := by
  unfold i8Psi4X211D i8P4X211
  rw [← i8Psi4X211c0D_mul hx, ← i8Psi4X211c1D_mul hx]
  ring

theorem continuousOn_i8Psi4X211 : ContinuousOn i8Psi4X211 (Ioc 0 1) := by
  unfold i8Psi4X211
  exact (continuousOn_i8Psi4X211c0.add continuousOn_i8Psi4X211c1)

theorem i8Psi4X211_one : i8Psi4X211 1 = -1275 / 4 + 128 * Li 4 (1 / 2) + 196 * zeta3 -
    337 / 360 * π ^ 4 - 27 / 2 * zeta5 + 16 / 3 * Real.log 2 ^ 4 + 179 / 4 * π ^ 2 -
    64 * Real.log 2 * π ^ 2 - 3 / 2 * π ^ 2 * zeta3 + 32 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4X211
  rw [i8Psi4X211c0_one, i8Psi4X211c1_one]
  ring

/-- Chunk 0 of the `(i, j, l) = (3, 0, 1)` part of `Ψ₄`. -/
noncomputable def i8Psi4X301c0 (x : ℝ) : ℝ :=
  i8Psi4s88 x + i8Psi4s89 x + i8Psi4s90 x + i8Psi4s91 x + i8Psi4s92 x + i8Psi4s93 x +
    i8Psi4s94 x + i8Psi4s95 x + i8Psi4s96 x + i8Psi4s97 x

/-- The derivative of `i8Psi4X301c0`. -/
noncomputable def i8Psi4X301c0D (x : ℝ) : ℝ :=
  i8Psi4s88D x + i8Psi4s89D x + i8Psi4s90D x + i8Psi4s91D x + i8Psi4s92D x +
    i8Psi4s93D x + i8Psi4s94D x + i8Psi4s95D x + i8Psi4s96D x + i8Psi4s97D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X301c0`. -/
noncomputable def i8P4X301c0 (x : ℝ) : ℝ :=
  i8P4s88 x + i8P4s89 x + i8P4s90 x + i8P4s91 x + i8P4s92 x + i8P4s93 x + i8P4s94 x +
    i8P4s95 x + i8P4s96 x + i8P4s97 x

theorem hasDerivAt_i8Psi4X301c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X301c0
    (i8Psi4X301c0D x) x := by
  unfold i8Psi4X301c0 i8Psi4X301c0D
  exact ((((((((((hasDerivAt_i8Psi4s88 hx).add (hasDerivAt_i8Psi4s89 hx)).add (hasDerivAt_i8Psi4s90
    hx)).add (hasDerivAt_i8Psi4s91 hx)).add (hasDerivAt_i8Psi4s92 hx)).add (hasDerivAt_i8Psi4s93
    hx)).add (hasDerivAt_i8Psi4s94 hx)).add (hasDerivAt_i8Psi4s95 hx)).add (hasDerivAt_i8Psi4s96
    hx)).add (hasDerivAt_i8Psi4s97 hx))

theorem i8Psi4X301c0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X301c0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X301c0 x := by
  unfold i8Psi4X301c0D i8P4X301c0
  rw [← i8Psi4s88D_mul hx, ← i8Psi4s89D_mul hx, ← i8Psi4s90D_mul hx, ← i8Psi4s91D_mul hx, ←
    i8Psi4s92D_mul hx, ← i8Psi4s93D_mul hx, ← i8Psi4s94D_mul hx, ← i8Psi4s95D_mul hx, ←
    i8Psi4s96D_mul hx, ← i8Psi4s97D_mul hx]
  ring

theorem continuousOn_i8Psi4X301c0 : ContinuousOn i8Psi4X301c0 (Ioc 0 1) := by
  unfold i8Psi4X301c0
  exact (((((((((continuousOn_i8Psi4s88.add continuousOn_i8Psi4s89).add continuousOn_i8Psi4s90).add
    continuousOn_i8Psi4s91).add continuousOn_i8Psi4s92).add continuousOn_i8Psi4s93).add
    continuousOn_i8Psi4s94).add continuousOn_i8Psi4s95).add continuousOn_i8Psi4s96).add
    continuousOn_i8Psi4s97)

theorem i8Psi4X301c0_one : i8Psi4X301c0 1 = 67 - 25 * zeta3 + 4 * zeta5 + 15 / 4 * π ^ 2 +
    16 / 45 * π ^ 4 + 2 / 3 * π ^ 2 * zeta3 := by
  unfold i8Psi4X301c0
  rw [i8Psi4s88_one, i8Psi4s89_one, i8Psi4s90_one, i8Psi4s91_one, i8Psi4s92_one, i8Psi4s93_one,
    i8Psi4s94_one, i8Psi4s95_one, i8Psi4s96_one, i8Psi4s97_one]
  ring

/-- Chunk 1 of the `(i, j, l) = (3, 0, 1)` part of `Ψ₄`. -/
noncomputable def i8Psi4X301c1 (x : ℝ) : ℝ :=
  i8Psi4s98 x + i8Psi4s99 x + i8Psi4s100 x + i8Psi4s101 x + i8Psi4s102 x + i8Psi4s103 x +
    i8Psi4s104 x + i8Psi4s105 x + i8Psi4s106 x + i8Psi4s107 x

/-- The derivative of `i8Psi4X301c1`. -/
noncomputable def i8Psi4X301c1D (x : ℝ) : ℝ :=
  i8Psi4s98D x + i8Psi4s99D x + i8Psi4s100D x + i8Psi4s101D x + i8Psi4s102D x +
    i8Psi4s103D x + i8Psi4s104D x + i8Psi4s105D x + i8Psi4s106D x + i8Psi4s107D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X301c1`. -/
noncomputable def i8P4X301c1 (x : ℝ) : ℝ :=
  i8P4s98 x + i8P4s99 x + i8P4s100 x + i8P4s101 x + i8P4s102 x + i8P4s103 x + i8P4s104 x +
    i8P4s105 x + i8P4s106 x + i8P4s107 x

theorem hasDerivAt_i8Psi4X301c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X301c1
    (i8Psi4X301c1D x) x := by
  unfold i8Psi4X301c1 i8Psi4X301c1D
  exact ((((((((((hasDerivAt_i8Psi4s98 hx).add (hasDerivAt_i8Psi4s99 hx)).add (hasDerivAt_i8Psi4s100
    hx)).add (hasDerivAt_i8Psi4s101 hx)).add (hasDerivAt_i8Psi4s102 hx)).add (hasDerivAt_i8Psi4s103
    hx)).add (hasDerivAt_i8Psi4s104 hx)).add (hasDerivAt_i8Psi4s105 hx)).add (hasDerivAt_i8Psi4s106
    hx)).add (hasDerivAt_i8Psi4s107 hx))

theorem i8Psi4X301c1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X301c1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X301c1 x := by
  unfold i8Psi4X301c1D i8P4X301c1
  rw [← i8Psi4s98D_mul hx, ← i8Psi4s99D_mul hx, ← i8Psi4s100D_mul hx, ← i8Psi4s101D_mul hx, ←
    i8Psi4s102D_mul hx, ← i8Psi4s103D_mul hx, ← i8Psi4s104D_mul hx, ← i8Psi4s105D_mul hx, ←
    i8Psi4s106D_mul hx, ← i8Psi4s107D_mul hx]
  ring

theorem continuousOn_i8Psi4X301c1 : ContinuousOn i8Psi4X301c1 (Ioc 0 1) := by
  unfold i8Psi4X301c1
  exact (((((((((continuousOn_i8Psi4s98.add continuousOn_i8Psi4s99).add continuousOn_i8Psi4s100).add
    continuousOn_i8Psi4s101).add continuousOn_i8Psi4s102).add continuousOn_i8Psi4s103).add
    continuousOn_i8Psi4s104).add continuousOn_i8Psi4s105).add continuousOn_i8Psi4s106).add
    continuousOn_i8Psi4s107)

theorem i8Psi4X301c1_one : i8Psi4X301c1 1 = 603 / 4 - 84 * zeta5 + 64 * Li 4 (1 / 2) +
    67 * zeta3 - 361 / 360 * π ^ 4 + 8 / 3 * Real.log 2 ^ 4 + 83 / 3 * π ^ 2 -
    36 * Real.log 2 * π ^ 2 - 5 / 3 * π ^ 2 * zeta3 + 16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4X301c1
  rw [i8Psi4s98_one, i8Psi4s99_one, i8Psi4s100_one, i8Psi4s101_one, i8Psi4s102_one, i8Psi4s103_one,
    i8Psi4s104_one, i8Psi4s105_one, i8Psi4s106_one, i8Psi4s107_one]
  ring

/-- Chunk 2 of the `(i, j, l) = (3, 0, 1)` part of `Ψ₄`. -/
noncomputable def i8Psi4X301c2 (x : ℝ) : ℝ :=
  i8Psi4s108 x

/-- The derivative of `i8Psi4X301c2`. -/
noncomputable def i8Psi4X301c2D (x : ℝ) : ℝ :=
  i8Psi4s108D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X301c2`. -/
noncomputable def i8P4X301c2 (x : ℝ) : ℝ :=
  i8P4s108 x

theorem hasDerivAt_i8Psi4X301c2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X301c2
    (i8Psi4X301c2D x) x := by
  unfold i8Psi4X301c2 i8Psi4X301c2D
  exact (hasDerivAt_i8Psi4s108 hx)

theorem i8Psi4X301c2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X301c2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X301c2 x := by
  unfold i8Psi4X301c2D i8P4X301c2
  rw [← i8Psi4s108D_mul hx]

theorem continuousOn_i8Psi4X301c2 : ContinuousOn i8Psi4X301c2 (Ioc 0 1) := by
  unfold i8Psi4X301c2
  exact continuousOn_i8Psi4s108

theorem i8Psi4X301c2_one : i8Psi4X301c2 1 = -1327 / 4 + 128 * Li 4 (1 / 2) + 172 * zeta3 -
    277 / 360 * π ^ 4 + 16 / 3 * Real.log 2 ^ 4 + 225 / 2 * zeta5 + 347 / 12 * π ^ 2 -
    16 * Real.log 2 * π ^ 2 - 16 / 3 * π ^ 2 * Real.log 2 ^ 2 - 15 / 2 * π ^ 2 * zeta3 := by
  unfold i8Psi4X301c2
  rw [i8Psi4s108_one]

/-- The `(i, j, l) = (3, 0, 1)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X301 (x : ℝ) : ℝ :=
  i8Psi4X301c0 x + i8Psi4X301c1 x + i8Psi4X301c2 x

/-- The derivative of `i8Psi4X301`. -/
noncomputable def i8Psi4X301D (x : ℝ) : ℝ :=
  i8Psi4X301c0D x + i8Psi4X301c1D x + i8Psi4X301c2D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X301`. -/
noncomputable def i8P4X301 (x : ℝ) : ℝ :=
  i8P4X301c0 x + i8P4X301c1 x + i8P4X301c2 x

theorem hasDerivAt_i8Psi4X301 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X301 (i8Psi4X301D
    x) x := by
  unfold i8Psi4X301 i8Psi4X301D
  exact (((hasDerivAt_i8Psi4X301c0 hx).add (hasDerivAt_i8Psi4X301c1 hx)).add
    (hasDerivAt_i8Psi4X301c2 hx))

theorem i8Psi4X301D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X301D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X301 x := by
  unfold i8Psi4X301D i8P4X301
  rw [← i8Psi4X301c0D_mul hx, ← i8Psi4X301c1D_mul hx, ← i8Psi4X301c2D_mul hx]
  ring

theorem continuousOn_i8Psi4X301 : ContinuousOn i8Psi4X301 (Ioc 0 1) := by
  unfold i8Psi4X301
  exact ((continuousOn_i8Psi4X301c0.add continuousOn_i8Psi4X301c1).add continuousOn_i8Psi4X301c2)

theorem i8Psi4X301_one : i8Psi4X301 1 = -114 + 8 * Real.log 2 ^ 4 + 192 * Li 4 (1 / 2) +
    214 * zeta3 - 17 / 12 * π ^ 4 + 65 / 2 * zeta5 + 181 / 3 * π ^ 2 - 52 * Real.log 2 * π ^ 2 -
    17 / 2 * π ^ 2 * zeta3 := by
  unfold i8Psi4X301
  rw [i8Psi4X301c0_one, i8Psi4X301c1_one, i8Psi4X301c2_one]
  ring

/-- Chunk 0 of the `(i, j, l) = (0, 2, 2)` part of `Ψ₄`. -/
noncomputable def i8Psi4X022c0 (x : ℝ) : ℝ :=
  i8Psi4s109 x + i8Psi4s110 x + i8Psi4s111 x + i8Psi4s112 x + i8Psi4s113 x +
    i8Psi4s114 x + i8Psi4s115 x + i8Psi4s116 x + i8Psi4s117 x + i8Psi4s118 x

/-- The derivative of `i8Psi4X022c0`. -/
noncomputable def i8Psi4X022c0D (x : ℝ) : ℝ :=
  i8Psi4s109D x + i8Psi4s110D x + i8Psi4s111D x + i8Psi4s112D x + i8Psi4s113D x +
    i8Psi4s114D x + i8Psi4s115D x + i8Psi4s116D x + i8Psi4s117D x + i8Psi4s118D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X022c0`. -/
noncomputable def i8P4X022c0 (x : ℝ) : ℝ :=
  i8P4s109 x + i8P4s110 x + i8P4s111 x + i8P4s112 x + i8P4s113 x + i8P4s114 x +
    i8P4s115 x + i8P4s116 x + i8P4s117 x + i8P4s118 x

theorem hasDerivAt_i8Psi4X022c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X022c0
    (i8Psi4X022c0D x) x := by
  unfold i8Psi4X022c0 i8Psi4X022c0D
  exact ((((((((((hasDerivAt_i8Psi4s109 hx).add (hasDerivAt_i8Psi4s110 hx)).add
    (hasDerivAt_i8Psi4s111 hx)).add (hasDerivAt_i8Psi4s112 hx)).add (hasDerivAt_i8Psi4s113 hx)).add
    (hasDerivAt_i8Psi4s114 hx)).add (hasDerivAt_i8Psi4s115 hx)).add (hasDerivAt_i8Psi4s116 hx)).add
    (hasDerivAt_i8Psi4s117 hx)).add (hasDerivAt_i8Psi4s118 hx))

theorem i8Psi4X022c0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X022c0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X022c0 x := by
  unfold i8Psi4X022c0D i8P4X022c0
  rw [← i8Psi4s109D_mul hx, ← i8Psi4s110D_mul hx, ← i8Psi4s111D_mul hx, ← i8Psi4s112D_mul hx, ←
    i8Psi4s113D_mul hx, ← i8Psi4s114D_mul hx, ← i8Psi4s115D_mul hx, ← i8Psi4s116D_mul hx, ←
    i8Psi4s117D_mul hx, ← i8Psi4s118D_mul hx]
  ring

theorem continuousOn_i8Psi4X022c0 : ContinuousOn i8Psi4X022c0 (Ioc 0 1) := by
  unfold i8Psi4X022c0
  exact (((((((((continuousOn_i8Psi4s109.add continuousOn_i8Psi4s110).add
    continuousOn_i8Psi4s111).add continuousOn_i8Psi4s112).add continuousOn_i8Psi4s113).add
    continuousOn_i8Psi4s114).add continuousOn_i8Psi4s115).add continuousOn_i8Psi4s116).add
    continuousOn_i8Psi4s117).add continuousOn_i8Psi4s118)

theorem i8Psi4X022c0_one : i8Psi4X022c0 1 = -49 / 4 - 17 / 240 * π ^ 4 + 17 / 2 * zeta3 +
    17 / 48 * π ^ 2 + 27 / 4 * zeta5 - 2 / 3 * π ^ 2 * zeta3 := by
  unfold i8Psi4X022c0
  rw [i8Psi4s109_one, i8Psi4s110_one, i8Psi4s111_one, i8Psi4s112_one, i8Psi4s113_one,
    i8Psi4s114_one, i8Psi4s115_one, i8Psi4s116_one, i8Psi4s117_one, i8Psi4s118_one]
  ring

/-- Chunk 1 of the `(i, j, l) = (0, 2, 2)` part of `Ψ₄`. -/
noncomputable def i8Psi4X022c1 (x : ℝ) : ℝ :=
  i8Psi4s119 x + i8Psi4s120 x

/-- The derivative of `i8Psi4X022c1`. -/
noncomputable def i8Psi4X022c1D (x : ℝ) : ℝ :=
  i8Psi4s119D x + i8Psi4s120D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X022c1`. -/
noncomputable def i8P4X022c1 (x : ℝ) : ℝ :=
  i8P4s119 x + i8P4s120 x

theorem hasDerivAt_i8Psi4X022c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X022c1
    (i8Psi4X022c1D x) x := by
  unfold i8Psi4X022c1 i8Psi4X022c1D
  exact ((hasDerivAt_i8Psi4s119 hx).add (hasDerivAt_i8Psi4s120 hx))

theorem i8Psi4X022c1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X022c1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X022c1 x := by
  unfold i8Psi4X022c1D i8P4X022c1
  rw [← i8Psi4s119D_mul hx, ← i8Psi4s120D_mul hx]
  ring

theorem continuousOn_i8Psi4X022c1 : ContinuousOn i8Psi4X022c1 (Ioc 0 1) := by
  unfold i8Psi4X022c1
  exact (continuousOn_i8Psi4s119.add continuousOn_i8Psi4s120)

theorem i8Psi4X022c1_one : i8Psi4X022c1 1 = 31 / 4 - 35 / 4 * zeta5 - 31 / 4 * zeta3 +
    5 / 24 * π ^ 2 + 7 / 180 * π ^ 4 + π ^ 2 * zeta3 / 2 := by
  unfold i8Psi4X022c1
  rw [i8Psi4s119_one, i8Psi4s120_one]
  ring

/-- The `(i, j, l) = (0, 2, 2)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X022 (x : ℝ) : ℝ :=
  i8Psi4X022c0 x + i8Psi4X022c1 x

/-- The derivative of `i8Psi4X022`. -/
noncomputable def i8Psi4X022D (x : ℝ) : ℝ :=
  i8Psi4X022c0D x + i8Psi4X022c1D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X022`. -/
noncomputable def i8P4X022 (x : ℝ) : ℝ :=
  i8P4X022c0 x + i8P4X022c1 x

theorem hasDerivAt_i8Psi4X022 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X022 (i8Psi4X022D
    x) x := by
  unfold i8Psi4X022 i8Psi4X022D
  exact ((hasDerivAt_i8Psi4X022c0 hx).add (hasDerivAt_i8Psi4X022c1 hx))

theorem i8Psi4X022D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X022D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X022 x := by
  unfold i8Psi4X022D i8P4X022
  rw [← i8Psi4X022c0D_mul hx, ← i8Psi4X022c1D_mul hx]
  ring

theorem continuousOn_i8Psi4X022 : ContinuousOn i8Psi4X022 (Ioc 0 1) := by
  unfold i8Psi4X022
  exact (continuousOn_i8Psi4X022c0.add continuousOn_i8Psi4X022c1)

theorem i8Psi4X022_one : i8Psi4X022 1 = -9 / 2 - 2 * zeta5 - 23 / 720 * π ^ 4 + 3 / 4 * zeta3 +
    9 / 16 * π ^ 2 - π ^ 2 * zeta3 / 6 := by
  unfold i8Psi4X022
  rw [i8Psi4X022c0_one, i8Psi4X022c1_one]
  ring

/-- The `(i, j, l) = (1, 1, 2)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X112 (x : ℝ) : ℝ :=
  i8Psi4s121 x + i8Psi4s122 x + i8Psi4s123 x + i8Psi4s124 x + i8Psi4s125 x +
    i8Psi4s126 x + i8Psi4s127 x + i8Psi4s128 x

/-- The derivative of `i8Psi4X112`. -/
noncomputable def i8Psi4X112D (x : ℝ) : ℝ :=
  i8Psi4s121D x + i8Psi4s122D x + i8Psi4s123D x + i8Psi4s124D x + i8Psi4s125D x +
    i8Psi4s126D x + i8Psi4s127D x + i8Psi4s128D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X112`. -/
noncomputable def i8P4X112 (x : ℝ) : ℝ :=
  i8P4s121 x + i8P4s122 x + i8P4s123 x + i8P4s124 x + i8P4s125 x + i8P4s126 x +
    i8P4s127 x + i8P4s128 x

theorem hasDerivAt_i8Psi4X112 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X112 (i8Psi4X112D
    x) x := by
  unfold i8Psi4X112 i8Psi4X112D
  exact ((((((((hasDerivAt_i8Psi4s121 hx).add (hasDerivAt_i8Psi4s122 hx)).add (hasDerivAt_i8Psi4s123
    hx)).add (hasDerivAt_i8Psi4s124 hx)).add (hasDerivAt_i8Psi4s125 hx)).add (hasDerivAt_i8Psi4s126
    hx)).add (hasDerivAt_i8Psi4s127 hx)).add (hasDerivAt_i8Psi4s128 hx))

theorem i8Psi4X112D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X112D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X112 x := by
  unfold i8Psi4X112D i8P4X112
  rw [← i8Psi4s121D_mul hx, ← i8Psi4s122D_mul hx, ← i8Psi4s123D_mul hx, ← i8Psi4s124D_mul hx, ←
    i8Psi4s125D_mul hx, ← i8Psi4s126D_mul hx, ← i8Psi4s127D_mul hx, ← i8Psi4s128D_mul hx]
  ring

theorem continuousOn_i8Psi4X112 : ContinuousOn i8Psi4X112 (Ioc 0 1) := by
  unfold i8Psi4X112
  exact (((((((continuousOn_i8Psi4s121.add continuousOn_i8Psi4s122).add continuousOn_i8Psi4s123).add
    continuousOn_i8Psi4s124).add continuousOn_i8Psi4s125).add continuousOn_i8Psi4s126).add
    continuousOn_i8Psi4s127).add continuousOn_i8Psi4s128)

theorem i8Psi4X112_one : i8Psi4X112 1 = -735 / 8 + 46 * zeta3 + 64 * Li 4 (1 / 2) -
    13 / 18 * π ^ 4 + 8 / 3 * Real.log 2 ^ 4 + 83 / 8 * π ^ 2 - 12 * Real.log 2 * π ^ 2 +
    16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4X112
  rw [i8Psi4s121_one, i8Psi4s122_one, i8Psi4s123_one, i8Psi4s124_one, i8Psi4s125_one,
    i8Psi4s126_one, i8Psi4s127_one, i8Psi4s128_one]
  ring

/-- Chunk 0 of the `(i, j, l) = (2, 0, 2)` part of `Ψ₄`. -/
noncomputable def i8Psi4X202c0 (x : ℝ) : ℝ :=
  i8Psi4s129 x + i8Psi4s130 x + i8Psi4s131 x + i8Psi4s132 x + i8Psi4s133 x +
    i8Psi4s134 x + i8Psi4s135 x + i8Psi4s136 x + i8Psi4s137 x + i8Psi4s138 x

/-- The derivative of `i8Psi4X202c0`. -/
noncomputable def i8Psi4X202c0D (x : ℝ) : ℝ :=
  i8Psi4s129D x + i8Psi4s130D x + i8Psi4s131D x + i8Psi4s132D x + i8Psi4s133D x +
    i8Psi4s134D x + i8Psi4s135D x + i8Psi4s136D x + i8Psi4s137D x + i8Psi4s138D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X202c0`. -/
noncomputable def i8P4X202c0 (x : ℝ) : ℝ :=
  i8P4s129 x + i8P4s130 x + i8P4s131 x + i8P4s132 x + i8P4s133 x + i8P4s134 x +
    i8P4s135 x + i8P4s136 x + i8P4s137 x + i8P4s138 x

theorem hasDerivAt_i8Psi4X202c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X202c0
    (i8Psi4X202c0D x) x := by
  unfold i8Psi4X202c0 i8Psi4X202c0D
  exact ((((((((((hasDerivAt_i8Psi4s129 hx).add (hasDerivAt_i8Psi4s130 hx)).add
    (hasDerivAt_i8Psi4s131 hx)).add (hasDerivAt_i8Psi4s132 hx)).add (hasDerivAt_i8Psi4s133 hx)).add
    (hasDerivAt_i8Psi4s134 hx)).add (hasDerivAt_i8Psi4s135 hx)).add (hasDerivAt_i8Psi4s136 hx)).add
    (hasDerivAt_i8Psi4s137 hx)).add (hasDerivAt_i8Psi4s138 hx))

theorem i8Psi4X202c0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X202c0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X202c0 x := by
  unfold i8Psi4X202c0D i8P4X202c0
  rw [← i8Psi4s129D_mul hx, ← i8Psi4s130D_mul hx, ← i8Psi4s131D_mul hx, ← i8Psi4s132D_mul hx, ←
    i8Psi4s133D_mul hx, ← i8Psi4s134D_mul hx, ← i8Psi4s135D_mul hx, ← i8Psi4s136D_mul hx, ←
    i8Psi4s137D_mul hx, ← i8Psi4s138D_mul hx]
  ring

theorem continuousOn_i8Psi4X202c0 : ContinuousOn i8Psi4X202c0 (Ioc 0 1) := by
  unfold i8Psi4X202c0
  exact (((((((((continuousOn_i8Psi4s129.add continuousOn_i8Psi4s130).add
    continuousOn_i8Psi4s131).add continuousOn_i8Psi4s132).add continuousOn_i8Psi4s133).add
    continuousOn_i8Psi4s134).add continuousOn_i8Psi4s135).add continuousOn_i8Psi4s136).add
    continuousOn_i8Psi4s137).add continuousOn_i8Psi4s138)

theorem i8Psi4X202c0_one : i8Psi4X202c0 1 = -65 / 2 - 14 * zeta5 + 64 * Li 4 (1 / 2) -
    π ^ 4 / 30 + 8 / 3 * Real.log 2 ^ 4 + 77 / 24 * π ^ 2 + 137 / 2 * zeta3 -
    12 * Real.log 2 * π ^ 2 + 2 / 3 * π ^ 2 * zeta3 + 16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4X202c0
  rw [i8Psi4s129_one, i8Psi4s130_one, i8Psi4s131_one, i8Psi4s132_one, i8Psi4s133_one,
    i8Psi4s134_one, i8Psi4s135_one, i8Psi4s136_one, i8Psi4s137_one, i8Psi4s138_one]
  ring

/-- Chunk 1 of the `(i, j, l) = (2, 0, 2)` part of `Ψ₄`. -/
noncomputable def i8Psi4X202c1 (x : ℝ) : ℝ :=
  i8Psi4s139 x + i8Psi4s140 x

/-- The derivative of `i8Psi4X202c1`. -/
noncomputable def i8Psi4X202c1D (x : ℝ) : ℝ :=
  i8Psi4s139D x + i8Psi4s140D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X202c1`. -/
noncomputable def i8P4X202c1 (x : ℝ) : ℝ :=
  i8P4s139 x + i8P4s140 x

theorem hasDerivAt_i8Psi4X202c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X202c1
    (i8Psi4X202c1D x) x := by
  unfold i8Psi4X202c1 i8Psi4X202c1D
  exact ((hasDerivAt_i8Psi4s139 hx).add (hasDerivAt_i8Psi4s140 hx))

theorem i8Psi4X202c1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X202c1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X202c1 x := by
  unfold i8Psi4X202c1D i8P4X202c1
  rw [← i8Psi4s139D_mul hx, ← i8Psi4s140D_mul hx]
  ring

theorem continuousOn_i8Psi4X202c1 : ContinuousOn i8Psi4X202c1 (Ioc 0 1) := by
  unfold i8Psi4X202c1
  exact (continuousOn_i8Psi4s139.add continuousOn_i8Psi4s140)

theorem i8Psi4X202c1_one : i8Psi4X202c1 1 = -125 / 4 - 12 * zeta5 + 45 * zeta3 - π ^ 4 / 2 +
    53 / 12 * π ^ 2 + 4 * π ^ 2 * zeta3 := by
  unfold i8Psi4X202c1
  rw [i8Psi4s139_one, i8Psi4s140_one]
  ring

/-- The `(i, j, l) = (2, 0, 2)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X202 (x : ℝ) : ℝ :=
  i8Psi4X202c0 x + i8Psi4X202c1 x

/-- The derivative of `i8Psi4X202`. -/
noncomputable def i8Psi4X202D (x : ℝ) : ℝ :=
  i8Psi4X202c0D x + i8Psi4X202c1D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X202`. -/
noncomputable def i8P4X202 (x : ℝ) : ℝ :=
  i8P4X202c0 x + i8P4X202c1 x

theorem hasDerivAt_i8Psi4X202 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X202 (i8Psi4X202D
    x) x := by
  unfold i8Psi4X202 i8Psi4X202D
  exact ((hasDerivAt_i8Psi4X202c0 hx).add (hasDerivAt_i8Psi4X202c1 hx))

theorem i8Psi4X202D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X202D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X202 x := by
  unfold i8Psi4X202D i8P4X202
  rw [← i8Psi4X202c0D_mul hx, ← i8Psi4X202c1D_mul hx]
  ring

theorem continuousOn_i8Psi4X202 : ContinuousOn i8Psi4X202 (Ioc 0 1) := by
  unfold i8Psi4X202
  exact (continuousOn_i8Psi4X202c0.add continuousOn_i8Psi4X202c1)

theorem i8Psi4X202_one : i8Psi4X202 1 = -255 / 4 - 26 * zeta5 + 64 * Li 4 (1 / 2) -
    8 / 15 * π ^ 4 + 8 / 3 * Real.log 2 ^ 4 + 61 / 8 * π ^ 2 + 227 / 2 * zeta3 -
    12 * Real.log 2 * π ^ 2 + 14 / 3 * π ^ 2 * zeta3 + 16 / 3 * π ^ 2 * Real.log 2 ^ 2 := by
  unfold i8Psi4X202
  rw [i8Psi4X202c0_one, i8Psi4X202c1_one]
  ring

/-- The `(i, j, l) = (0, 1, 3)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X013 (x : ℝ) : ℝ :=
  i8Psi4s141 x + i8Psi4s142 x + i8Psi4s143 x + i8Psi4s144 x + i8Psi4s145 x +
    i8Psi4s146 x + i8Psi4s147 x + i8Psi4s148 x

/-- The derivative of `i8Psi4X013`. -/
noncomputable def i8Psi4X013D (x : ℝ) : ℝ :=
  i8Psi4s141D x + i8Psi4s142D x + i8Psi4s143D x + i8Psi4s144D x + i8Psi4s145D x +
    i8Psi4s146D x + i8Psi4s147D x + i8Psi4s148D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X013`. -/
noncomputable def i8P4X013 (x : ℝ) : ℝ :=
  i8P4s141 x + i8P4s142 x + i8P4s143 x + i8P4s144 x + i8P4s145 x + i8P4s146 x +
    i8P4s147 x + i8P4s148 x

theorem hasDerivAt_i8Psi4X013 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X013 (i8Psi4X013D
    x) x := by
  unfold i8Psi4X013 i8Psi4X013D
  exact ((((((((hasDerivAt_i8Psi4s141 hx).add (hasDerivAt_i8Psi4s142 hx)).add (hasDerivAt_i8Psi4s143
    hx)).add (hasDerivAt_i8Psi4s144 hx)).add (hasDerivAt_i8Psi4s145 hx)).add (hasDerivAt_i8Psi4s146
    hx)).add (hasDerivAt_i8Psi4s147 hx)).add (hasDerivAt_i8Psi4s148 hx))

theorem i8Psi4X013D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X013D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X013 x := by
  unfold i8Psi4X013D i8P4X013
  rw [← i8Psi4s141D_mul hx, ← i8Psi4s142D_mul hx, ← i8Psi4s143D_mul hx, ← i8Psi4s144D_mul hx, ←
    i8Psi4s145D_mul hx, ← i8Psi4s146D_mul hx, ← i8Psi4s147D_mul hx, ← i8Psi4s148D_mul hx]
  ring

theorem continuousOn_i8Psi4X013 : ContinuousOn i8Psi4X013 (Ioc 0 1) := by
  unfold i8Psi4X013
  exact (((((((continuousOn_i8Psi4s141.add continuousOn_i8Psi4s142).add continuousOn_i8Psi4s143).add
    continuousOn_i8Psi4s144).add continuousOn_i8Psi4s145).add continuousOn_i8Psi4s146).add
    continuousOn_i8Psi4s147).add continuousOn_i8Psi4s148)

theorem i8Psi4X013_one : i8Psi4X013 1 = -89 / 16 - zeta5 + π ^ 4 / 12 + 11 / 48 * π ^ 2 +
    13 / 4 * zeta3 - 2 / 3 * π ^ 2 * zeta3 := by
  unfold i8Psi4X013
  rw [i8Psi4s141_one, i8Psi4s142_one, i8Psi4s143_one, i8Psi4s144_one, i8Psi4s145_one,
    i8Psi4s146_one, i8Psi4s147_one, i8Psi4s148_one]
  ring

/-- The `(i, j, l) = (1, 0, 3)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X103 (x : ℝ) : ℝ :=
  i8Psi4s149 x + i8Psi4s150 x + i8Psi4s151 x + i8Psi4s152 x

/-- The derivative of `i8Psi4X103`. -/
noncomputable def i8Psi4X103D (x : ℝ) : ℝ :=
  i8Psi4s149D x + i8Psi4s150D x + i8Psi4s151D x + i8Psi4s152D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X103`. -/
noncomputable def i8P4X103 (x : ℝ) : ℝ :=
  i8P4s149 x + i8P4s150 x + i8P4s151 x + i8P4s152 x

theorem hasDerivAt_i8Psi4X103 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X103 (i8Psi4X103D
    x) x := by
  unfold i8Psi4X103 i8Psi4X103D
  exact ((((hasDerivAt_i8Psi4s149 hx).add (hasDerivAt_i8Psi4s150 hx)).add (hasDerivAt_i8Psi4s151
    hx)).add (hasDerivAt_i8Psi4s152 hx))

theorem i8Psi4X103D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X103D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X103 x := by
  unfold i8Psi4X103D i8P4X103
  rw [← i8Psi4s149D_mul hx, ← i8Psi4s150D_mul hx, ← i8Psi4s151D_mul hx, ← i8Psi4s152D_mul hx]
  ring

theorem continuousOn_i8Psi4X103 : ContinuousOn i8Psi4X103 (Ioc 0 1) := by
  unfold i8Psi4X103
  exact (((continuousOn_i8Psi4s149.add continuousOn_i8Psi4s150).add continuousOn_i8Psi4s151).add
    continuousOn_i8Psi4s152)

theorem i8Psi4X103_one : i8Psi4X103 1 = -43 / 4 - 5 * zeta3 + 12 * zeta5 - 37 / 12 * π ^ 2 +
    14 / 15 * π ^ 4 := by
  unfold i8Psi4X103
  rw [i8Psi4s149_one, i8Psi4s150_one, i8Psi4s151_one, i8Psi4s152_one]
  ring

/-- The `(i, j, l) = (0, 0, 4)` part of `Ψ₄`: from `t Bᵢ Aⱼ (-λ)^l/l!`. -/
noncomputable def i8Psi4X004 (x : ℝ) : ℝ :=
  i8Psi4s153 x + i8Psi4s154 x + i8Psi4s155 x + i8Psi4s156 x + i8Psi4s157 x

/-- The derivative of `i8Psi4X004`. -/
noncomputable def i8Psi4X004D (x : ℝ) : ℝ :=
  i8Psi4s153D x + i8Psi4s154D x + i8Psi4s155D x + i8Psi4s156D x + i8Psi4s157D x

/-- The part of `p₄` in `ξ` matching `i8Psi4X004`. -/
noncomputable def i8P4X004 (x : ℝ) : ℝ :=
  i8P4s153 x + i8P4s154 x + i8P4s155 x + i8P4s156 x + i8P4s157 x

theorem hasDerivAt_i8Psi4X004 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt i8Psi4X004 (i8Psi4X004D
    x) x := by
  unfold i8Psi4X004 i8Psi4X004D
  exact (((((hasDerivAt_i8Psi4s153 hx).add (hasDerivAt_i8Psi4s154 hx)).add (hasDerivAt_i8Psi4s155
    hx)).add (hasDerivAt_i8Psi4s156 hx)).add (hasDerivAt_i8Psi4s157 hx))

theorem i8Psi4X004D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4X004D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4X004 x := by
  unfold i8Psi4X004D i8P4X004
  rw [← i8Psi4s153D_mul hx, ← i8Psi4s154D_mul hx, ← i8Psi4s155D_mul hx, ← i8Psi4s156D_mul hx, ←
    i8Psi4s157D_mul hx]
  ring

theorem continuousOn_i8Psi4X004 : ContinuousOn i8Psi4X004 (Ioc 0 1) := by
  unfold i8Psi4X004
  exact ((((continuousOn_i8Psi4s153.add continuousOn_i8Psi4s154).add continuousOn_i8Psi4s155).add
    continuousOn_i8Psi4s156).add continuousOn_i8Psi4s157)

theorem i8Psi4X004_one : i8Psi4X004 1 = 3 / 32 + 6 * zeta5 - 13 / 24 * π ^ 2 - 5 / 2 * zeta3 -
    π ^ 4 / 20 + 2 / 3 * π ^ 2 * zeta3 := by
  unfold i8Psi4X004
  rw [i8Psi4s153_one, i8Psi4s154_one, i8Psi4s155_one, i8Psi4s156_one, i8Psi4s157_one]
  ring

end QED.ThreeLoopD
