/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4L17

/-!
# Set (d), master `I₈`: the limit of `F₄ - A₄` at infinity

The singular parts of the sub-pieces of `Ψ₄` and of `-A₄` add up to the constant
`8339/32 - 2π⁴/45 - 59π²/24 - 25ζ(3)` (`QED.ThreeLoopD.i8D4_eq`), and the regular parts tend to
`0`; hence `F₄ - A₄ → 8339/32 - 2π⁴/45 - 59π²/24 - 25ζ(3)` as `t → ∞`.

## Main results

* `QED.ThreeLoopD.i8D4_eq`.
* `QED.ThreeLoopD.tendsto_i8F4_sub_prim4`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The singular parts of the sub-pieces of `Ψ₄` in group 0. -/
noncomputable def i8L4SG0 (x : ℝ) : ℝ :=
  (30 - π ^ 2 - 4 * zeta3 + 3 * Real.log x ^ 2 + 14 * Real.log x - 649 / 16 * x +
    Real.log x ^ 3 / 3 + 2 * π ^ 2 * x - Real.log x * π ^ 2 / 3 - x * Real.log x ^ 4 / 12 +
    x * Real.log x ^ 3 / 6 + 9 / 8 * x * Real.log x ^ 2 + 121 / 16 * Real.log x * x +
    4 * Real.log x * x * zeta3 - Real.log x * π ^ 2 * x / 12 +
    π ^ 2 * x * Real.log x ^ 2 / 6) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 0. -/
noncomputable def i8L4PG0 (x : ℝ) : ℝ :=
  i8Psi4s0 x + i8Psi4s1 x + i8Psi4s2 x + i8Psi4s3 x + i8Psi4s4 x + i8Psi4s5 x +
    i8Psi4s6 x + i8Psi4s7 x + i8Psi4s8 x + i8Psi4s9 x + i8Psi4s10 x

theorem i8L4PG0_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG0 x = i8L4SG0 x + (i8L4R0 x + i8L4R1 x + i8L4R2 x + i8L4R3 x + i8L4R4 x +
      i8L4R5 x + i8L4R6 x + i8L4R7 x + i8L4R8 x + i8L4R9 x + i8L4R10 x) := by
  unfold i8L4PG0
  rw [i8L4_0_eq hx, i8L4_1_eq hx, i8L4_2_eq hx, i8L4_3_eq hx, i8L4_4_eq hx, i8L4_5_eq hx, i8L4_6_eq
    hx, i8L4_7_eq hx, i8L4_8_eq hx, i8L4_9_eq hx, i8L4_10_eq hx]
  have hS : i8L4S0 x + i8L4S1 x + i8L4S2 x + i8L4S3 x + i8L4S4 x + i8L4S5 x + i8L4S6 x +
    i8L4S7 x + i8L4S8 x + i8L4S9 x + i8L4S10 x = i8L4SG0 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S0 i8L4S1 i8L4S2 i8L4S3 i8L4S4 i8L4S5 i8L4S6 i8L4S7 i8L4S8 i8L4S9 i8L4S10 i8L4SG0
    field_simp
    ring
  unfold i8L4R0 i8L4R1 i8L4R2 i8L4R3 i8L4R4 i8L4R5 i8L4R6 i8L4R7 i8L4R8 i8L4R9 i8L4R10
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 1. -/
noncomputable def i8L4SG1 (x : ℝ) : ℝ :=
  (26 + Real.log x ^ 2 - 8 * zeta3 + 10 * Real.log x - 383 / 4 * x - 4 / 3 * π ^ 2 -
    Real.log x ^ 3 / 3 - π ^ 4 / 20 - 4 * Real.log x * zeta3 + 6 * x * Real.log x ^ 2 +
    15 * x * zeta3 + 28 * Real.log x * x - 2 / 3 * Real.log x * π ^ 2 -
    π ^ 2 * Real.log x ^ 2 / 6 + x * Real.log x ^ 4 / 4 + 47 / 12 * π ^ 2 * x -
    6 * Real.log x * x * zeta3 + 2 * x * zeta3 * Real.log x ^ 2 - π ^ 2 * x * Real.log x ^ 2 / 3 +
    π ^ 2 * x * Real.log x ^ 3 / 18 + Real.log x * x * π ^ 4 / 20) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 1. -/
noncomputable def i8L4PG1 (x : ℝ) : ℝ :=
  i8Psi4s11 x + i8Psi4s12 x + i8Psi4s13 x + i8Psi4s14 x + i8Psi4s15 x + i8Psi4s16 x +
    i8Psi4s17 x + i8Psi4s18 x + i8Psi4s19 x + i8Psi4s20 x + i8Psi4s21 x + i8Psi4s22 x +
    i8Psi4s23 x + i8Psi4s24 x + i8Psi4s25 x + i8Psi4s26 x

theorem i8L4PG1_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG1 x = i8L4SG1 x + (i8L4R11 x + i8L4R12 x + i8L4R13 x + i8L4R14 x + i8L4R15 x +
      i8L4R16 x + i8L4R17 x + i8L4R18 x + i8L4R19 x + i8L4R20 x + i8L4R21 x + i8L4R22 x +
      i8L4R23 x + i8L4R24 x + i8L4R25 x + i8L4R26 x) := by
  unfold i8L4PG1
  rw [i8L4_11_eq hx, i8L4_12_eq hx, i8L4_13_eq hx, i8L4_14_eq hx, i8L4_15_eq hx, i8L4_16_eq hx,
    i8L4_17_eq hx, i8L4_18_eq hx, i8L4_19_eq hx, i8L4_20_eq hx, i8L4_21_eq hx, i8L4_22_eq hx,
    i8L4_23_eq hx, i8L4_24_eq hx, i8L4_25_eq hx, i8L4_26_eq hx]
  have hS : i8L4S11 x + i8L4S12 x + i8L4S13 x + i8L4S14 x + i8L4S15 x + i8L4S16 x +
    i8L4S17 x + i8L4S18 x + i8L4S19 x + i8L4S20 x + i8L4S21 x + i8L4S22 x + i8L4S23 x +
    i8L4S24 x + i8L4S25 x + i8L4S26 x = i8L4SG1 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S11 i8L4S12 i8L4S13 i8L4S14 i8L4S15 i8L4S16 i8L4S17 i8L4S18 i8L4S19 i8L4S20 i8L4S21
      i8L4S22 i8L4S23 i8L4S24 i8L4S25 i8L4S26 i8L4SG1
    field_simp
    ring
  unfold i8L4R11 i8L4R12 i8L4R13 i8L4R14 i8L4R15 i8L4R16 i8L4R17 i8L4R18 i8L4R19 i8L4R20 i8L4R21
    i8L4R22 i8L4R23 i8L4R24 i8L4R25 i8L4R26
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 2. -/
noncomputable def i8L4SG2 (x : ℝ) : ℝ :=
  (54 + Real.log x ^ 3 - 12 * zeta3 - 2 * π ^ 2 + 3 * Real.log x ^ 2 + 22 * Real.log x +
    28 * x + Real.log x ^ 4 / 12 - 8 * x * Real.log x ^ 2 - 4 * Real.log x * zeta3 +
    20 * Real.log x * x - 2 / 3 * Real.log x * π ^ 2 - x * Real.log x ^ 5 / 60 +
    4 / 3 * π ^ 2 * x + 4 / 3 * x * Real.log x ^ 3 + π ^ 2 * x * Real.log x ^ 2 +
    6 * x * zeta3 * Real.log x ^ 2 + 8 * Real.log x * x * zeta3 +
    2 / 3 * Real.log x * π ^ 2 * x) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 2. -/
noncomputable def i8L4PG2 (x : ℝ) : ℝ :=
  i8Psi4s27 x + i8Psi4s28 x + i8Psi4s29 x + i8Psi4s30 x + i8Psi4s31 x + i8Psi4s32 x +
    i8Psi4s33 x + i8Psi4s34 x + i8Psi4s35 x + i8Psi4s36 x + i8Psi4s37 x + i8Psi4s38 x +
    i8Psi4s39 x + i8Psi4s40 x + i8Psi4s41 x

theorem i8L4PG2_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG2 x = i8L4SG2 x + (i8L4R27 x + i8L4R28 x + i8L4R29 x + i8L4R30 x + i8L4R31 x +
      i8L4R32 x + i8L4R33 x + i8L4R34 x + i8L4R35 x + i8L4R36 x + i8L4R37 x + i8L4R38 x +
      i8L4R39 x + i8L4R40 x + i8L4R41 x) := by
  unfold i8L4PG2
  rw [i8L4_27_eq hx, i8L4_28_eq hx, i8L4_29_eq hx, i8L4_30_eq hx, i8L4_31_eq hx, i8L4_32_eq hx,
    i8L4_33_eq hx, i8L4_34_eq hx, i8L4_35_eq hx, i8L4_36_eq hx, i8L4_37_eq hx, i8L4_38_eq hx,
    i8L4_39_eq hx, i8L4_40_eq hx, i8L4_41_eq hx]
  have hS : i8L4S27 x + i8L4S28 x + i8L4S29 x + i8L4S30 x + i8L4S31 x + i8L4S32 x +
    i8L4S33 x + i8L4S34 x + i8L4S35 x + i8L4S36 x + i8L4S37 x + i8L4S38 x + i8L4S39 x +
    i8L4S40 x + i8L4S41 x = i8L4SG2 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S27 i8L4S28 i8L4S29 i8L4S30 i8L4S31 i8L4S32 i8L4S33 i8L4S34 i8L4S35 i8L4S36 i8L4S37
      i8L4S38 i8L4S39 i8L4S40 i8L4S41 i8L4SG2
    field_simp
    ring
  unfold i8L4R27 i8L4R28 i8L4R29 i8L4R30 i8L4R31 i8L4R32 i8L4R33 i8L4R34 i8L4R35 i8L4R36 i8L4R37
    i8L4R38 i8L4R39 i8L4R40 i8L4R41
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 3. -/
noncomputable def i8L4SG3 (x : ℝ) : ℝ :=
  (131 + 7 * Real.log x ^ 3 + 41 * Real.log x ^ 2 + 115 * Real.log x - 11 / 3 * π ^ 2 +
    π ^ 4 / 36 + 7 / 12 * Real.log x ^ 4 + 1315 / 16 * x - 24 * Real.log x * x -
    73 / 8 * x * Real.log x ^ 2 - 26 / 3 * x * Real.log x ^ 3 - 13 / 6 * x * Real.log x ^ 4 -
    7 / 3 * Real.log x * π ^ 2 - 7 / 20 * x * Real.log x ^ 5 - π ^ 2 * Real.log x ^ 2 / 2 +
    4 / 3 * π ^ 2 * x + π ^ 2 * x * Real.log x ^ 3 / 2 - Real.log x * x * π ^ 4 / 12 +
    2 / 3 * Real.log x * π ^ 2 * x + 2 / 3 * π ^ 2 * x * Real.log x ^ 2) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 3. -/
noncomputable def i8L4PG3 (x : ℝ) : ℝ :=
  i8Psi4s42 x + i8Psi4s43 x + i8Psi4s44 x + i8Psi4s45 x + i8Psi4s46 x + i8Psi4s47 x +
    i8Psi4s48 x + i8Psi4s49 x + i8Psi4s50 x + i8Psi4s51 x + i8Psi4s52 x + i8Psi4s53 x +
    i8Psi4s54 x + i8Psi4s55 x

theorem i8L4PG3_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG3 x = i8L4SG3 x + (i8L4R42 x + i8L4R43 x + i8L4R44 x + i8L4R45 x + i8L4R46 x +
      i8L4R47 x + i8L4R48 x + i8L4R49 x + i8L4R50 x + i8L4R51 x + i8L4R52 x + i8L4R53 x +
      i8L4R54 x + i8L4R55 x) := by
  unfold i8L4PG3
  rw [i8L4_42_eq hx, i8L4_43_eq hx, i8L4_44_eq hx, i8L4_45_eq hx, i8L4_46_eq hx, i8L4_47_eq hx,
    i8L4_48_eq hx, i8L4_49_eq hx, i8L4_50_eq hx, i8L4_51_eq hx, i8L4_52_eq hx, i8L4_53_eq hx,
    i8L4_54_eq hx, i8L4_55_eq hx]
  have hS : i8L4S42 x + i8L4S43 x + i8L4S44 x + i8L4S45 x + i8L4S46 x + i8L4S47 x +
    i8L4S48 x + i8L4S49 x + i8L4S50 x + i8L4S51 x + i8L4S52 x + i8L4S53 x + i8L4S54 x +
    i8L4S55 x = i8L4SG3 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S42 i8L4S43 i8L4S44 i8L4S45 i8L4S46 i8L4S47 i8L4S48 i8L4S49 i8L4S50 i8L4S51 i8L4S52
      i8L4S53 i8L4S54 i8L4S55 i8L4SG3
    field_simp
    ring
  unfold i8L4R42 i8L4R43 i8L4R44 i8L4R45 i8L4R46 i8L4R47 i8L4R48 i8L4R49 i8L4R50 i8L4R51 i8L4R52
    i8L4R53 i8L4R54 i8L4R55
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 4. -/
noncomputable def i8L4SG4 (x : ℝ) : ℝ :=
  (7 + 2 * Real.log x ^ 2 + 7 * Real.log x - 163 / 16 * x - x * Real.log x ^ 3 / 3 +
    35 / 16 * x * Real.log x ^ 2) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 4. -/
noncomputable def i8L4PG4 (x : ℝ) : ℝ :=
  i8Psi4s56 x + i8Psi4s57 x + i8Psi4s58 x + i8Psi4s59 x + i8Psi4s60 x + i8Psi4s61 x +
    i8Psi4s62 x + i8Psi4s63 x + i8Psi4s64 x + i8Psi4s65 x + i8Psi4s66 x + i8Psi4s67 x + i8Psi4s68 x

theorem i8L4PG4_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG4 x = i8L4SG4 x + (i8L4R56 x + i8L4R57 x + i8L4R58 x + i8L4R59 x + i8L4R60 x +
      i8L4R61 x + i8L4R62 x + i8L4R63 x + i8L4R64 x + i8L4R65 x + i8L4R66 x + i8L4R67 x +
      i8L4R68 x) := by
  unfold i8L4PG4
  rw [i8L4_56_eq hx, i8L4_57_eq hx, i8L4_58_eq hx, i8L4_59_eq hx, i8L4_60_eq hx, i8L4_61_eq hx,
    i8L4_62_eq hx, i8L4_63_eq hx, i8L4_64_eq hx, i8L4_65_eq hx, i8L4_66_eq hx, i8L4_67_eq hx,
    i8L4_68_eq hx]
  have hS : i8L4S56 x + i8L4S57 x + i8L4S58 x + i8L4S59 x + i8L4S60 x + i8L4S61 x +
    i8L4S62 x + i8L4S63 x + i8L4S64 x + i8L4S65 x + i8L4S66 x + i8L4S67 x +
    i8L4S68 x = i8L4SG4 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S56 i8L4S57 i8L4S58 i8L4S59 i8L4S60 i8L4S61 i8L4S62 i8L4S63 i8L4S64 i8L4S65 i8L4S66
      i8L4S67 i8L4S68 i8L4SG4
    field_simp
    ring
  unfold i8L4R56 i8L4R57 i8L4R58 i8L4R59 i8L4R60 i8L4R61 i8L4R62 i8L4R63 i8L4R64 i8L4R65 i8L4R66
    i8L4R67 i8L4R68
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 5. -/
noncomputable def i8L4SG5 (x : ℝ) : ℝ :=
  (14 + Real.log x ^ 3 + 5 * Real.log x ^ 2 + 14 * Real.log x - 157 / 4 * x - π ^ 2 / 3 +
    x * Real.log x ^ 3 / 2 - x * Real.log x ^ 2 / 2 - Real.log x * π ^ 2 / 3 -
    x * Real.log x ^ 4 / 4 + π ^ 2 * x * Real.log x ^ 2 / 6) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 5. -/
noncomputable def i8L4PG5 (x : ℝ) : ℝ :=
  i8Psi4s69 x + i8Psi4s70 x + i8Psi4s71 x + i8Psi4s72 x + i8Psi4s73 x + i8Psi4s74k0 x +
    i8Psi4s74k1 x + i8Psi4s74k2 x + i8Psi4s75k0 x + i8Psi4s75k1 x + i8Psi4s75k2 x + i8Psi4s76 x

theorem i8L4PG5_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG5 x = i8L4SG5 x + (i8L4R69 x + i8L4R70 x + i8L4R71 x + i8L4R72 x + i8L4R73 x +
      i8L4R74k0 x + i8L4R74k1 x + i8L4R74k2 x + i8L4R75k0 x + i8L4R75k1 x + i8L4R75k2 x +
      i8L4R76 x) := by
  unfold i8L4PG5
  rw [i8L4_69_eq hx, i8L4_70_eq hx, i8L4_71_eq hx, i8L4_72_eq hx, i8L4_73_eq hx, i8L4_74k0_eq hx,
    i8L4_74k1_eq hx, i8L4_74k2_eq hx, i8L4_75k0_eq hx, i8L4_75k1_eq hx, i8L4_75k2_eq hx, i8L4_76_eq
    hx]
  have hS : i8L4S69 x + i8L4S70 x + i8L4S71 x + i8L4S72 x + i8L4S73 x + i8L4S74k0 x +
    i8L4S74k1 x + i8L4S74k2 x + i8L4S75k0 x + i8L4S75k1 x + i8L4S75k2 x +
    i8L4S76 x = i8L4SG5 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S69 i8L4S70 i8L4S71 i8L4S72 i8L4S73 i8L4S74k0 i8L4S74k1 i8L4S74k2 i8L4S75k0 i8L4S75k1
      i8L4S75k2 i8L4S76 i8L4SG5
    field_simp
    ring
  unfold i8L4R69 i8L4R70 i8L4R71 i8L4R72 i8L4R73 i8L4R74k0 i8L4R74k1 i8L4R74k2 i8L4R75k0 i8L4R75k1
    i8L4R75k2 i8L4R76
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 6. -/
noncomputable def i8L4SG6 (x : ℝ) : ℝ :=
  (-22 - Real.log x ^ 3 - 22 * Real.log x - 7 * Real.log x ^ 2 - 685 / 16 * x + π ^ 2 / 3 +
    Real.log x * π ^ 2 / 3 + 2 / 3 * x * Real.log x ^ 3 + 3 / 8 * x * Real.log x ^ 4 +
    23 / 24 * π ^ 2 * x - π ^ 2 * x * Real.log x ^ 2 / 4) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 6. -/
noncomputable def i8L4PG6 (x : ℝ) : ℝ :=
  i8Psi4s77 x + i8Psi4s78 x + i8Psi4s79 x + i8Psi4s80k0 x + i8Psi4s80k1 x +
    i8Psi4s81k0 x + i8Psi4s81k1 x + i8Psi4s81k2 x + i8Psi4s82 x

theorem i8L4PG6_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG6 x = i8L4SG6 x + (i8L4R77 x + i8L4R78 x + i8L4R79 x + i8L4R80k0 x +
      i8L4R80k1 x + i8L4R81k0 x + i8L4R81k1 x + i8L4R81k2 x + i8L4R82 x) := by
  unfold i8L4PG6
  rw [i8L4_77_eq hx, i8L4_78_eq hx, i8L4_79_eq hx, i8L4_80k0_eq hx, i8L4_80k1_eq hx, i8L4_81k0_eq
    hx, i8L4_81k1_eq hx, i8L4_81k2_eq hx, i8L4_82_eq hx]
  have hS : i8L4S77 x + i8L4S78 x + i8L4S79 x + i8L4S80k0 x + i8L4S80k1 x + i8L4S81k0 x +
    i8L4S81k1 x + i8L4S81k2 x + i8L4S82 x = i8L4SG6 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S77 i8L4S78 i8L4S79 i8L4S80k0 i8L4S80k1 i8L4S81k0 i8L4S81k1 i8L4S81k2 i8L4S82 i8L4SG6
    field_simp
    ring
  unfold i8L4R77 i8L4R78 i8L4R79 i8L4R80k0 i8L4R80k1 i8L4R81k0 i8L4R81k1 i8L4R81k2 i8L4R82
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 7. -/
noncomputable def i8L4SG7 (x : ℝ) : ℝ :=
  (16 - 4 * zeta3 + 16 * Real.log x - 837 / 16 * x - 2 / 3 * π ^ 2 - 4 * Real.log x * zeta3 +
    9 * x * Real.log x ^ 2 - 2 / 3 * Real.log x * π ^ 2 + x * Real.log x ^ 4 / 8 +
    2 / 3 * x * Real.log x ^ 3 + 2 * x * zeta3 * Real.log x ^ 2 +
    π ^ 2 * x * Real.log x ^ 2 / 3) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 7. -/
noncomputable def i8L4PG7 (x : ℝ) : ℝ :=
  i8Psi4s83 x + i8Psi4s84 x + i8Psi4s85 x + i8Psi4s86 x + i8Psi4s87k0 x +
    i8Psi4s87k1 x + i8Psi4s87k2 x + i8Psi4s87k3 x + i8Psi4s87k4 x + i8Psi4s88 x

theorem i8L4PG7_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG7 x = i8L4SG7 x + (i8L4R83 x + i8L4R84 x + i8L4R85 x + i8L4R86 x + i8L4R87k0 x +
      i8L4R87k1 x + i8L4R87k2 x + i8L4R87k3 x + i8L4R87k4 x + i8L4R88 x) := by
  unfold i8L4PG7
  rw [i8L4_83_eq hx, i8L4_84_eq hx, i8L4_85_eq hx, i8L4_86_eq hx, i8L4_87k0_eq hx, i8L4_87k1_eq hx,
    i8L4_87k2_eq hx, i8L4_87k3_eq hx, i8L4_87k4_eq hx, i8L4_88_eq hx]
  have hS : i8L4S83 x + i8L4S84 x + i8L4S85 x + i8L4S86 x + i8L4S87k0 x + i8L4S87k1 x +
    i8L4S87k2 x + i8L4S87k3 x + i8L4S87k4 x + i8L4S88 x = i8L4SG7 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S83 i8L4S84 i8L4S85 i8L4S86 i8L4S87k0 i8L4S87k1 i8L4S87k2 i8L4S87k3 i8L4S87k4 i8L4S88
      i8L4SG7
    field_simp
    ring
  unfold i8L4R83 i8L4R84 i8L4R85 i8L4R86 i8L4R87k0 i8L4R87k1 i8L4R87k2 i8L4R87k3 i8L4R87k4 i8L4R88
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 8. -/
noncomputable def i8L4SG8 (x : ℝ) : ℝ :=
  (36 + 18 * Real.log x ^ 2 + 36 * Real.log x + 68 * x - 2 / 3 * π ^ 2 + Real.log x ^ 4 / 3 +
    10 / 3 * Real.log x ^ 3 - 32 * Real.log x * x - 14 * x * Real.log x ^ 2 - 8 * x * zeta3 -
    4 / 3 * π ^ 2 * x - 2 / 3 * Real.log x * π ^ 2 - π ^ 2 * Real.log x ^ 2 / 3 -
    x * Real.log x ^ 5 / 15 + 8 * Real.log x * x * zeta3 + π ^ 2 * x * Real.log x ^ 3 / 9 +
    4 / 3 * Real.log x * π ^ 2 * x) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 8. -/
noncomputable def i8L4PG8 (x : ℝ) : ℝ :=
  i8Psi4s89 x + i8Psi4s90 x + i8Psi4s91 x + i8Psi4s92 x + i8Psi4s93 x + i8Psi4s94 x +
    i8Psi4s95 x + i8Psi4s96 x + i8Psi4s97 x + i8Psi4s98 x + i8Psi4s99 x + i8Psi4s100 x

theorem i8L4PG8_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG8 x = i8L4SG8 x + (i8L4R89 x + i8L4R90 x + i8L4R91 x + i8L4R92 x + i8L4R93 x +
      i8L4R94 x + i8L4R95 x + i8L4R96 x + i8L4R97 x + i8L4R98 x + i8L4R99 x + i8L4R100 x) := by
  unfold i8L4PG8
  rw [i8L4_89_eq hx, i8L4_90_eq hx, i8L4_91_eq hx, i8L4_92_eq hx, i8L4_93_eq hx, i8L4_94_eq hx,
    i8L4_95_eq hx, i8L4_96_eq hx, i8L4_97_eq hx, i8L4_98_eq hx, i8L4_99_eq hx, i8L4_100_eq hx]
  have hS : i8L4S89 x + i8L4S90 x + i8L4S91 x + i8L4S92 x + i8L4S93 x + i8L4S94 x +
    i8L4S95 x + i8L4S96 x + i8L4S97 x + i8L4S98 x + i8L4S99 x + i8L4S100 x = i8L4SG8 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S89 i8L4S90 i8L4S91 i8L4S92 i8L4S93 i8L4S94 i8L4S95 i8L4S96 i8L4S97 i8L4S98 i8L4S99
      i8L4S100 i8L4SG8
    field_simp
    ring
  unfold i8L4R89 i8L4R90 i8L4R91 i8L4R92 i8L4R93 i8L4R94 i8L4R95 i8L4R96 i8L4R97 i8L4R98 i8L4R99
    i8L4R100
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 9. -/
noncomputable def i8L4SG9 (x : ℝ) : ℝ :=
  (108 + Real.log x ^ 4 + 10 * Real.log x ^ 3 + 46 * Real.log x ^ 2 + 92 * x + 108 * Real.log x -
    4 / 3 * π ^ 2 - 18 * x * Real.log x ^ 2 - 8 * Real.log x * x - 2 * π ^ 2 * x -
    28 / 3 * x * Real.log x ^ 3 - 8 / 3 * x * Real.log x ^ 4 - 4 / 3 * Real.log x * π ^ 2 -
    3 / 5 * x * Real.log x ^ 5 - π ^ 2 * Real.log x ^ 2 / 3 + π ^ 2 * x * Real.log x ^ 3 / 3 +
    2 / 3 * π ^ 2 * x * Real.log x ^ 2 + 4 / 3 * Real.log x * π ^ 2 * x) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 9. -/
noncomputable def i8L4PG9 (x : ℝ) : ℝ :=
  i8Psi4s101 x + i8Psi4s102 x + i8Psi4s103 x + i8Psi4s104 x + i8Psi4s105 x +
    i8Psi4s106 x + i8Psi4s107 x + i8Psi4s108k0 x + i8Psi4s108k1 x + i8Psi4s108k2 x

theorem i8L4PG9_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG9 x = i8L4SG9 x + (i8L4R101 x + i8L4R102 x + i8L4R103 x + i8L4R104 x +
      i8L4R105 x + i8L4R106 x + i8L4R107 x + i8L4R108k0 x + i8L4R108k1 x + i8L4R108k2 x) := by
  unfold i8L4PG9
  rw [i8L4_101_eq hx, i8L4_102_eq hx, i8L4_103_eq hx, i8L4_104_eq hx, i8L4_105_eq hx, i8L4_106_eq
    hx, i8L4_107_eq hx, i8L4_108k0_eq hx, i8L4_108k1_eq hx, i8L4_108k2_eq hx]
  have hS : i8L4S101 x + i8L4S102 x + i8L4S103 x + i8L4S104 x + i8L4S105 x + i8L4S106 x +
    i8L4S107 x + i8L4S108k0 x + i8L4S108k1 x + i8L4S108k2 x = i8L4SG9 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S101 i8L4S102 i8L4S103 i8L4S104 i8L4S105 i8L4S106 i8L4S107 i8L4S108k0 i8L4S108k1
      i8L4S108k2 i8L4SG9
    field_simp
    ring
  unfold i8L4R101 i8L4R102 i8L4R103 i8L4R104 i8L4R105 i8L4R106 i8L4R107 i8L4R108k0 i8L4R108k1
    i8L4R108k2
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 10. -/
noncomputable def i8L4SG10 (x : ℝ) : ℝ :=
  (617 / 16 - 24 * Real.log x + 5 * Real.log x ^ 2 - Real.log x ^ 4 / 2 + Real.log x ^ 3 / 24)

/-- The sub-pieces of `Ψ₄` in group 10. -/
noncomputable def i8L4PG10 (x : ℝ) : ℝ :=
  i8Psi4s108k3 x + i8Psi4s108k4 x + i8Psi4s109 x + i8Psi4s110 x + i8Psi4s111k0 x +
    i8Psi4s111k1 x + i8Psi4s112 x + i8Psi4s113 x + i8Psi4s114k0 x + i8Psi4s114k1 x + i8Psi4s115k0 x

theorem i8L4PG10_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG10 x = i8L4SG10 x + (i8L4R108k3 x + i8L4R108k4 x + i8L4R109 x + i8L4R110 x +
      i8L4R111k0 x + i8L4R111k1 x + i8L4R112 x + i8L4R113 x + i8L4R114k0 x +
      i8L4R114k1 x + i8L4R115k0 x) := by
  unfold i8L4PG10
  rw [i8L4_108k3_eq hx, i8L4_108k4_eq hx, i8L4_109_eq hx, i8L4_110_eq hx, i8L4_111k0_eq hx,
    i8L4_111k1_eq hx, i8L4_112_eq hx, i8L4_113_eq hx, i8L4_114k0_eq hx, i8L4_114k1_eq hx,
    i8L4_115k0_eq hx]
  have hS : i8L4S108k3 x + i8L4S108k4 x + i8L4S109 x + i8L4S110 x + i8L4S111k0 x +
    i8L4S111k1 x + i8L4S112 x + i8L4S113 x + i8L4S114k0 x + i8L4S114k1 x +
    i8L4S115k0 x = i8L4SG10 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S108k3 i8L4S108k4 i8L4S109 i8L4S110 i8L4S111k0 i8L4S111k1 i8L4S112 i8L4S113
      i8L4S114k0 i8L4S114k1 i8L4S115k0 i8L4SG10
    field_simp
    ring
  unfold i8L4R108k3 i8L4R108k4 i8L4R109 i8L4R110 i8L4R111k0 i8L4R111k1 i8L4R112 i8L4R113 i8L4R114k0
    i8L4R114k1 i8L4R115k0
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 11. -/
noncomputable def i8L4SG11 (x : ℝ) : ℝ :=
  (-7 + Real.log x ^ 2)

/-- The sub-pieces of `Ψ₄` in group 11. -/
noncomputable def i8L4PG11 (x : ℝ) : ℝ :=
  i8Psi4s115k1 x + i8Psi4s115k2 x + i8Psi4s116k0 x + i8Psi4s116k1 x + i8Psi4s117 x +
    i8Psi4s118 x + i8Psi4s119k0 x + i8Psi4s119k1 x + i8Psi4s120k0 x

theorem i8L4PG11_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG11 x = i8L4SG11 x + (i8L4R115k1 x + i8L4R115k2 x + i8L4R116k0 x + i8L4R116k1 x +
      i8L4R117 x + i8L4R118 x + i8L4R119k0 x + i8L4R119k1 x + i8L4R120k0 x) := by
  unfold i8L4PG11
  rw [i8L4_115k1_eq hx, i8L4_115k2_eq hx, i8L4_116k0_eq hx, i8L4_116k1_eq hx, i8L4_117_eq hx,
    i8L4_118_eq hx, i8L4_119k0_eq hx, i8L4_119k1_eq hx, i8L4_120k0_eq hx]
  have hS : i8L4S115k1 x + i8L4S115k2 x + i8L4S116k0 x + i8L4S116k1 x + i8L4S117 x +
    i8L4S118 x + i8L4S119k0 x + i8L4S119k1 x + i8L4S120k0 x = i8L4SG11 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S115k1 i8L4S115k2 i8L4S116k0 i8L4S116k1 i8L4S117 i8L4S118 i8L4S119k0 i8L4S119k1
      i8L4S120k0 i8L4SG11
    field_simp
    ring
  unfold i8L4R115k1 i8L4R115k2 i8L4R116k0 i8L4R116k1 i8L4R117 i8L4R118 i8L4R119k0 i8L4R119k1
    i8L4R120k0
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 12. -/
noncomputable def i8L4SG12 (x : ℝ) : ℝ :=
  (-393 / 16 + Real.log x ^ 3 / 3 + Real.log x ^ 4 / 8)

/-- The sub-pieces of `Ψ₄` in group 12. -/
noncomputable def i8L4PG12 (x : ℝ) : ℝ :=
  i8Psi4s120k1 x + i8Psi4s121 x + i8Psi4s122 x + i8Psi4s123 x + i8Psi4s124k0 x +
    i8Psi4s124k1 x + i8Psi4s125k0 x + i8Psi4s125k1 x + i8Psi4s125k2 x + i8Psi4s126 x

theorem i8L4PG12_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG12 x = i8L4SG12 x + (i8L4R120k1 x + i8L4R121 x + i8L4R122 x + i8L4R123 x +
      i8L4R124k0 x + i8L4R124k1 x + i8L4R125k0 x + i8L4R125k1 x + i8L4R125k2 x + i8L4R126 x) := by
  unfold i8L4PG12
  rw [i8L4_120k1_eq hx, i8L4_121_eq hx, i8L4_122_eq hx, i8L4_123_eq hx, i8L4_124k0_eq hx,
    i8L4_124k1_eq hx, i8L4_125k0_eq hx, i8L4_125k1_eq hx, i8L4_125k2_eq hx, i8L4_126_eq hx]
  have hS : i8L4S120k1 x + i8L4S121 x + i8L4S122 x + i8L4S123 x + i8L4S124k0 x +
    i8L4S124k1 x + i8L4S125k0 x + i8L4S125k1 x + i8L4S125k2 x + i8L4S126 x = i8L4SG12 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S120k1 i8L4S121 i8L4S122 i8L4S123 i8L4S124k0 i8L4S124k1 i8L4S125k0 i8L4S125k1
      i8L4S125k2 i8L4S126 i8L4SG12
    field_simp
    ring
  unfold i8L4R120k1 i8L4R121 i8L4R122 i8L4R123 i8L4R124k0 i8L4R124k1 i8L4R125k0 i8L4R125k1
    i8L4R125k2 i8L4R126
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 13. -/
noncomputable def i8L4SG13 (x : ℝ) : ℝ :=
  (32 + Real.log x ^ 4 / 2 + 4 * Real.log x ^ 3 + 16 * Real.log x ^ 2 + 32 * Real.log x + 48 * x -
    π ^ 2 / 3 - 8 * x * Real.log x ^ 2 - 2 * x * Real.log x ^ 3 - 2 / 3 * π ^ 2 * x -
    x * Real.log x ^ 4 / 2 - Real.log x * π ^ 2 / 3 - π ^ 2 * Real.log x ^ 2 / 6 -
    x * Real.log x ^ 5 / 10 + π ^ 2 * x * Real.log x ^ 2 / 3 +
    π ^ 2 * x * Real.log x ^ 3 / 18) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 13. -/
noncomputable def i8L4PG13 (x : ℝ) : ℝ :=
  i8Psi4s127 x + i8Psi4s128k0 x + i8Psi4s128k1 x + i8Psi4s128k2 x + i8Psi4s129 x +
    i8Psi4s130 x + i8Psi4s131k0 x + i8Psi4s131k1 x + i8Psi4s132 x + i8Psi4s133 x

theorem i8L4PG13_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG13 x = i8L4SG13 x + (i8L4R127 x + i8L4R128k0 x + i8L4R128k1 x + i8L4R128k2 x +
      i8L4R129 x + i8L4R130 x + i8L4R131k0 x + i8L4R131k1 x + i8L4R132 x + i8L4R133 x) := by
  unfold i8L4PG13
  rw [i8L4_127_eq hx, i8L4_128k0_eq hx, i8L4_128k1_eq hx, i8L4_128k2_eq hx, i8L4_129_eq hx,
    i8L4_130_eq hx, i8L4_131k0_eq hx, i8L4_131k1_eq hx, i8L4_132_eq hx, i8L4_133_eq hx]
  have hS : i8L4S127 x + i8L4S128k0 x + i8L4S128k1 x + i8L4S128k2 x + i8L4S129 x +
    i8L4S130 x + i8L4S131k0 x + i8L4S131k1 x + i8L4S132 x + i8L4S133 x = i8L4SG13 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S127 i8L4S128k0 i8L4S128k1 i8L4S128k2 i8L4S129 i8L4S130 i8L4S131k0 i8L4S131k1
      i8L4S132 i8L4S133 i8L4SG13
    field_simp
    ring
  unfold i8L4R127 i8L4R128k0 i8L4R128k1 i8L4R128k2 i8L4R129 i8L4R130 i8L4R131k0 i8L4R131k1 i8L4R132
    i8L4R133
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 14. -/
noncomputable def i8L4SG14 (x : ℝ) : ℝ :=
  (28 + Real.log x ^ 4 / 2 + 4 * Real.log x ^ 3 + 14 * Real.log x ^ 2 + 28 * Real.log x + 36 * x -
    x * Real.log x ^ 4 - 4 * x * Real.log x ^ 2 - 2 * x * Real.log x ^ 3 -
    3 / 10 * x * Real.log x ^ 5) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 14. -/
noncomputable def i8L4PG14 (x : ℝ) : ℝ :=
  i8Psi4s134 x + i8Psi4s135k0 x + i8Psi4s135k1 x + i8Psi4s136k0 x + i8Psi4s136k1 x +
    i8Psi4s137 x + i8Psi4s138 x + i8Psi4s139 x + i8Psi4s140k0 x + i8Psi4s140k1 x

theorem i8L4PG14_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG14 x = i8L4SG14 x + (i8L4R134 x + i8L4R135k0 x + i8L4R135k1 x + i8L4R136k0 x +
      i8L4R136k1 x + i8L4R137 x + i8L4R138 x + i8L4R139 x + i8L4R140k0 x + i8L4R140k1 x) := by
  unfold i8L4PG14
  rw [i8L4_134_eq hx, i8L4_135k0_eq hx, i8L4_135k1_eq hx, i8L4_136k0_eq hx, i8L4_136k1_eq hx,
    i8L4_137_eq hx, i8L4_138_eq hx, i8L4_139_eq hx, i8L4_140k0_eq hx, i8L4_140k1_eq hx]
  have hS : i8L4S134 x + i8L4S135k0 x + i8L4S135k1 x + i8L4S136k0 x + i8L4S136k1 x +
    i8L4S137 x + i8L4S138 x + i8L4S139 x + i8L4S140k0 x + i8L4S140k1 x = i8L4SG14 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S134 i8L4S135k0 i8L4S135k1 i8L4S136k0 i8L4S136k1 i8L4S137 i8L4S138 i8L4S139
      i8L4S140k0 i8L4S140k1 i8L4SG14
    field_simp
    ring
  unfold i8L4R134 i8L4R135k0 i8L4R135k1 i8L4R136k0 i8L4R136k1 i8L4R137 i8L4R138 i8L4R139 i8L4R140k0
    i8L4R140k1
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 15. -/
noncomputable def i8L4SG15 (x : ℝ) : ℝ :=
  (-55 / 32 + Real.log x ^ 4 / 48)

/-- The sub-pieces of `Ψ₄` in group 15. -/
noncomputable def i8L4PG15 (x : ℝ) : ℝ :=
  i8Psi4s140k2 x + i8Psi4s141 x + i8Psi4s142 x + i8Psi4s143 x + i8Psi4s144k0 x +
    i8Psi4s144k1 x + i8Psi4s144k2 x + i8Psi4s145 x + i8Psi4s146k0 x + i8Psi4s146k1 x

theorem i8L4PG15_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG15 x = i8L4SG15 x + (i8L4R140k2 x + i8L4R141 x + i8L4R142 x + i8L4R143 x +
      i8L4R144k0 x + i8L4R144k1 x + i8L4R144k2 x + i8L4R145 x + i8L4R146k0 x + i8L4R146k1 x) := by
  unfold i8L4PG15
  rw [i8L4_140k2_eq hx, i8L4_141_eq hx, i8L4_142_eq hx, i8L4_143_eq hx, i8L4_144k0_eq hx,
    i8L4_144k1_eq hx, i8L4_144k2_eq hx, i8L4_145_eq hx, i8L4_146k0_eq hx, i8L4_146k1_eq hx]
  have hS : i8L4S140k2 x + i8L4S141 x + i8L4S142 x + i8L4S143 x + i8L4S144k0 x +
    i8L4S144k1 x + i8L4S144k2 x + i8L4S145 x + i8L4S146k0 x + i8L4S146k1 x = i8L4SG15 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S140k2 i8L4S141 i8L4S142 i8L4S143 i8L4S144k0 i8L4S144k1 i8L4S144k2 i8L4S145
      i8L4S146k0 i8L4S146k1 i8L4SG15
    field_simp
    ring
  unfold i8L4R140k2 i8L4R141 i8L4R142 i8L4R143 i8L4R144k0 i8L4R144k1 i8L4R144k2 i8L4R145 i8L4R146k0
    i8L4R146k1
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 16. -/
noncomputable def i8L4SG16 (x : ℝ) : ℝ :=
  (13 + 13 * Real.log x + 22 * x + 3 / 8 * Real.log x ^ 4 + 13 / 2 * Real.log x ^ 2 +
    13 / 6 * Real.log x ^ 3 - 7 / 120 * x * Real.log x ^ 5 - 5 / 12 * x * Real.log x ^ 4 -
    4 / 3 * x * Real.log x ^ 3) / x ^ 1

/-- The sub-pieces of `Ψ₄` in group 16. -/
noncomputable def i8L4PG16 (x : ℝ) : ℝ :=
  i8Psi4s146k2 x + i8Psi4s147 x + i8Psi4s148k0 x + i8Psi4s149 x + i8Psi4s150 x +
    i8Psi4s151k0 x + i8Psi4s151k1 x + i8Psi4s151k2 x + i8Psi4s152 x + i8Psi4s153 x + i8Psi4s154 x

theorem i8L4PG16_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG16 x = i8L4SG16 x + (i8L4R146k2 x + i8L4R147 x + i8L4R148k0 x + i8L4R149 x +
      i8L4R150 x + i8L4R151k0 x + i8L4R151k1 x + i8L4R151k2 x + i8L4R152 x + i8L4R153 x +
      i8L4R154 x) := by
  unfold i8L4PG16
  rw [i8L4_146k2_eq hx, i8L4_147_eq hx, i8L4_148k0_eq hx, i8L4_149_eq hx, i8L4_150_eq hx,
    i8L4_151k0_eq hx, i8L4_151k1_eq hx, i8L4_151k2_eq hx, i8L4_152_eq hx, i8L4_153_eq hx,
    i8L4_154_eq hx]
  have hS : i8L4S146k2 x + i8L4S147 x + i8L4S148k0 x + i8L4S149 x + i8L4S150 x +
    i8L4S151k0 x + i8L4S151k1 x + i8L4S151k2 x + i8L4S152 x + i8L4S153 x +
    i8L4S154 x = i8L4SG16 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S146k2 i8L4S147 i8L4S148k0 i8L4S149 i8L4S150 i8L4S151k0 i8L4S151k1 i8L4S151k2
      i8L4S152 i8L4S153 i8L4S154 i8L4SG16
    field_simp
    ring
  unfold i8L4R146k2 i8L4R147 i8L4R148k0 i8L4R149 i8L4R150 i8L4R151k0 i8L4R151k1 i8L4R151k2 i8L4R152
    i8L4R153 i8L4R154
  linear_combination hS

/-- The singular parts of the sub-pieces of `Ψ₄` in group 17. -/
noncomputable def i8L4SG17 (_x : ℝ) : ℝ :=
  (0)

/-- The sub-pieces of `Ψ₄` in group 17. -/
noncomputable def i8L4PG17 (x : ℝ) : ℝ :=
  i8Psi4s155k0 x + i8Psi4s155k1 x + i8Psi4s156 x + i8Psi4s157 x

theorem i8L4PG17_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8L4PG17 x = i8L4SG17 x + (i8L4R155k0 x + i8L4R155k1 x + i8L4R156 x + i8L4R157 x) := by
  unfold i8L4PG17
  rw [i8L4_155k0_eq hx, i8L4_155k1_eq hx, i8L4_156_eq hx, i8L4_157_eq hx]
  have hS : i8L4S155k0 x + i8L4S155k1 x + i8L4S156 x + i8L4S157 x = i8L4SG17 x := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4S155k0 i8L4S155k1 i8L4S156 i8L4S157 i8L4SG17
    field_simp
    ring
  unfold i8L4R155k0 i8L4R155k1 i8L4R156 i8L4R157
  linear_combination hS

theorem i8Psi4_eq_groups (x : ℝ) : i8Psi4 x = i8L4PG0 x + i8L4PG1 x + i8L4PG2 x +
    i8L4PG3 x + i8L4PG4 x + i8L4PG5 x + i8L4PG6 x + i8L4PG7 x + i8L4PG8 x + i8L4PG9 x +
    i8L4PG10 x + i8L4PG11 x + i8L4PG12 x + i8L4PG13 x + i8L4PG14 x + i8L4PG15 x +
    i8L4PG16 x + i8L4PG17 x := by
  unfold i8Psi4 i8Psi4X040 i8Psi4X130 i8Psi4X220 i8Psi4X310 i8Psi4X310c0 i8Psi4X310c1 i8Psi4X400
    i8Psi4X400c0 i8Psi4X400c1 i8Psi4X400c2 i8Psi4X031 i8Psi4X031c0 i8Psi4X031c1 i8Psi4X121
    i8Psi4X211 i8Psi4X211c0 i8Psi4X211c1 i8Psi4X301 i8Psi4X301c0 i8Psi4X301c1 i8Psi4X301c2
    i8Psi4X022 i8Psi4X022c0 i8Psi4X022c1 i8Psi4X112 i8Psi4X202 i8Psi4X202c0 i8Psi4X202c1 i8Psi4X013
    i8Psi4X103 i8Psi4X004 i8Psi4s74 i8Psi4s75 i8Psi4s80 i8Psi4s81 i8Psi4s87 i8Psi4s108 i8Psi4s111
    i8Psi4s114 i8Psi4s115 i8Psi4s116 i8Psi4s119 i8Psi4s120 i8Psi4s124 i8Psi4s125 i8Psi4s128
    i8Psi4s131 i8Psi4s135 i8Psi4s136 i8Psi4s140 i8Psi4s144 i8Psi4s146 i8Psi4s148 i8Psi4s151
    i8Psi4s155 i8L4PG0 i8L4PG1 i8L4PG2 i8L4PG3 i8L4PG4 i8L4PG5 i8L4PG6 i8L4PG7 i8L4PG8 i8L4PG9
    i8L4PG10 i8L4PG11 i8L4PG12 i8L4PG13 i8L4PG14 i8L4PG15 i8L4PG16 i8L4PG17
  ring

theorem i8D4_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8D4 x = 8339 / 32 - 25 * zeta3 - 59 / 24 * π ^ 2 - 2 / 45 * π ^ 4 + (i8L4RG0 x +
      i8L4RG1 x + i8L4RG2 x + i8L4RG3 x + i8L4RG4 x + i8L4RG5 x + i8L4RG6 x + i8L4RG7 x +
      i8L4RG8 x + i8L4RG9 x + i8L4RG10 x + i8L4RG11 x + i8L4RG12 x + i8L4RG13 x +
      i8L4RG14 x + i8L4RG15 x + i8L4RG16 x + i8L4RG17 x) := by
  unfold i8D4
  rw [sub_eq_add_neg, i8Psi4_eq_groups, i8L4PG0_eq hx, i8L4PG1_eq hx, i8L4PG2_eq hx, i8L4PG3_eq hx,
    i8L4PG4_eq hx, i8L4PG5_eq hx, i8L4PG6_eq hx, i8L4PG7_eq hx, i8L4PG8_eq hx, i8L4PG9_eq hx,
    i8L4PG10_eq hx, i8L4PG11_eq hx, i8L4PG12_eq hx, i8L4PG13_eq hx, i8L4PG14_eq hx, i8L4PG15_eq hx,
    i8L4PG16_eq hx, i8L4PG17_eq hx, i8L4_P_eq hx]
  have hK : i8L4SG0 x + i8L4SG1 x + i8L4SG2 x + i8L4SG3 x + i8L4SG4 x + i8L4SG5 x +
    i8L4SG6 x + i8L4SG7 x + i8L4SG8 x + i8L4SG9 x + i8L4SG10 x + i8L4SG11 x + i8L4SG12 x +
    i8L4SG13 x + i8L4SG14 x + i8L4SG15 x + i8L4SG16 x + i8L4SG17 x + i8L4SP x = 8339 / 32 -
    25 * zeta3 - 59 / 24 * π ^ 2 - 2 / 45 * π ^ 4 := by
    have h0 : x ≠ 0 := hx.1.ne'
    unfold i8L4SG0 i8L4SG1 i8L4SG2 i8L4SG3 i8L4SG4 i8L4SG5 i8L4SG6 i8L4SG7 i8L4SG8 i8L4SG9 i8L4SG10
      i8L4SG11 i8L4SG12 i8L4SG13 i8L4SG14 i8L4SG15 i8L4SG16 i8L4SG17 i8L4SP
    field_simp
    ring
  unfold i8L4RG0 i8L4RG1 i8L4RG2 i8L4RG3 i8L4RG4 i8L4RG5 i8L4RG6 i8L4RG7 i8L4RG8 i8L4RG9 i8L4RG10
    i8L4RG11 i8L4RG12 i8L4RG13 i8L4RG14 i8L4RG15 i8L4RG16 i8L4RG17 i8L4RP
  linear_combination hK

/-! ### The limit -/

theorem tendsto_i8D4 : Tendsto i8D4 (𝓝[>] 0) (𝓝 (8339 / 32 - 25 * zeta3 - 59 / 24 * π ^ 2 -
    2 / 45 * π ^ 4)) := by
  have H := ((((((((((((((((((tendsto_i8L4RG0.add tendsto_i8L4RG1).add tendsto_i8L4RG2).add
    tendsto_i8L4RG3).add tendsto_i8L4RG4).add tendsto_i8L4RG5).add tendsto_i8L4RG6).add
    tendsto_i8L4RG7).add tendsto_i8L4RG8).add tendsto_i8L4RG9).add tendsto_i8L4RG10).add
    tendsto_i8L4RG11).add tendsto_i8L4RG12).add tendsto_i8L4RG13).add tendsto_i8L4RG14).add
    tendsto_i8L4RG15).add tendsto_i8L4RG16).add tendsto_i8L4RG17)).const_add (8339 / 32 -
    25 * zeta3 - 59 / 24 * π ^ 2 - 2 / 45 * π ^ 4)
  simp only [add_zero] at H
  refine H.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
  rw [i8D4_eq hx]

/-- **The limit** `F₄ - A₄ → 8339/32 - 2π⁴/45 - 59π²/24 - 25ζ(3)` as `t → ∞`. -/
theorem tendsto_i8F4_sub_prim4 :
    Tendsto (fun t => i8F4 t - i8Prim4 t) atTop (𝓝 (8339 / 32 - 25 * zeta3 - 59 / 24 * π ^ 2 -
      2 / 45 * π ^ 4)) :=
  (tendsto_i8D4.comp tendsto_i13Xi_atTop).congr'
    (eventually_atTop.2 ⟨1, fun t ht => (i8F4_sub_prim4 (by linarith)).symm⟩)

end QED.ThreeLoopD
