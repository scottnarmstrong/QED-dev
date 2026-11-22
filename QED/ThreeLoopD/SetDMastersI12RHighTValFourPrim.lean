/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighTValThree

/-!
# Set (d), master `I₁₂`: the primitive of the face integrand of order 4

The primitive `Φ = B + Ψ₀[P₀] + Ψ₋₁[P₋₁] + Ψ₋₁[P₁] ∘ φ - Ψ₀[P₁] ∘ φ` of `J_4`, as in
`QED.ThreeLoopD.SetDMastersI12RHighTValThree` (`φ(s) = (1 - s)/(1 + s)`). To keep each algebraic
check small, `J_4 = J_A + J_C + J_B` is split along its definition (`J_A` the part of `e_A`,
`J_C` the first term of the part of `e_B`, `J_B` the rest), and `Φ = Φ_A + Φ_C + Φ_B` with
`Φ_A' = J_A`, `Φ_C' = J_C`, `Φ_B' = J_B` (the coefficients of `Φ_A`, `Φ_C` from integrating by
parts, those of `Φ_B` the differences); each derivative is checked by `field_simp; ring`.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12TV4Phi`: `Φ' = J_4` on `(0, 1)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory
open QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### Coefficients -/

/-- The polynomial part of `B` (total). -/
noncomputable def i12TV4Q0 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((60 * log 2 ^ 3 - 864 * log 2 ^ 2 + 1944 * log 2 - 3096), 0, 1, 0),
    ((90 * log 2 ^ 2 - 864 * log 2 + 828), 0, 2, 0), ((60 * log 2 - 300), 0, 3, 0), (15, 0, 4, 0),
    ((96 * log 2 ^ 3 - 1152 * log 2 ^ 2 + 288 * log 2 - 6336), 1, 0, 0),
    ((-1296 * log 2 - 720), 2, 0, 0), ((-96 * log 2 - 624), 3, 0, 0), (-60, 4, 0, 0)]

/-- The `1/s` part of `B` (total). -/
noncomputable def i12TV4Q1 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((12 * log 2 ^ 3 + 108 * log 2 ^ 2 + 504 * log 2 + 1080), 0, 0, 1),
    ((-54 * log 2 ^ 2 - 324 * log 2 - 756), 0, 0, 2), ((108 * log 2 + 324), 0, 0, 3),
    (-81, 0, 0, 4), ((12 * log 2 ^ 3 + 108 * log 2 ^ 2 + 504 * log 2 + 1080), 0, 1, 0),
    ((-72 * log 2 ^ 2 - 360 * log 2 - 720), 0, 1, 1), ((216 * log 2 + 540), 0, 1, 2),
    (-216, 0, 1, 3), ((-18 * log 2 ^ 2 - 36 * log 2 + 36), 0, 2, 0),
    ((144 * log 2 + 324), 0, 2, 1), (-216, 0, 2, 2), ((36 * log 2 + 108), 0, 3, 0),
    (-96, 0, 3, 1), (-15, 0, 4, 0), ((72 * log 2 ^ 2 + 432 * log 2 + 1008), 1, 0, 1),
    ((-216 * log 2 - 648), 1, 0, 2), (216, 1, 0, 3),
    ((72 * log 2 ^ 2 + 432 * log 2 + 1008), 1, 1, 0), ((-216 * log 2 - 576), 1, 1, 1),
    (324, 1, 1, 2), (72, 1, 2, 0), (180, 1, 2, 1), (72, 1, 3, 0), ((144 * log 2 + 432), 2, 0, 1),
    (-216, 2, 0, 2), ((144 * log 2 + 432), 2, 1, 0), (-180, 2, 1, 1), (36, 2, 2, 0),
    (96, 3, 0, 1), (96, 3, 1, 0)]

/-- The `1/(1 - s)` part of `B` (total). -/
noncomputable def i12TV4Q2 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-60 * log 2 ^ 4 + 432 * log 2 ^ 3 - 1008 * log 2 ^ 2 + 4320 * log 2), 0, 0, 0),
    ((-48 * log 2 ^ 3 - 432 * log 2 ^ 2 - 2016 * log 2 - 4320), 0, 0, 1),
    ((216 * log 2 ^ 2 + 1296 * log 2 + 3024), 0, 0, 2), ((-432 * log 2 - 1296), 0, 0, 3),
    (324, 0, 0, 4), ((-288 * log 2 ^ 3 + 864 * log 2 ^ 2 - 4032 * log 2), 0, 1, 0),
    ((288 * log 2 ^ 2 + 1728 * log 2 + 4032), 0, 1, 1), ((-864 * log 2 - 2592), 0, 1, 2),
    (864, 0, 1, 3), ((-288 * log 2 ^ 2 + 1728 * log 2), 0, 2, 0),
    ((-576 * log 2 - 1728), 0, 2, 1), (864, 0, 2, 2), ((-384 * log 2), 0, 3, 0), (384, 0, 3, 1),
    ((-96 * log 2 ^ 3 + 1008 * log 2 ^ 2 - 1152 * log 2 + 4320), 1, 0, 0),
    ((-288 * log 2 ^ 2 - 1440 * log 2 - 2880), 1, 0, 1), ((864 * log 2 + 2160), 1, 0, 2),
    (-864, 1, 0, 3), ((-720 * log 2 ^ 2 + 1152 * log 2 - 4032), 1, 1, 0),
    ((864 * log 2 + 2304), 1, 1, 1), (-1296, 1, 1, 2), ((-432 * log 2 + 1728), 1, 2, 0),
    (-720, 1, 2, 1), (-384, 1, 3, 0), ((1008 * log 2 - 144), 2, 0, 0),
    ((-576 * log 2 - 1296), 2, 0, 1), (864, 2, 0, 2), ((-720 * log 2 + 288), 2, 1, 0),
    (720, 2, 1, 1), (-144, 2, 2, 0), ((96 * log 2 + 432), 3, 0, 0), (-384, 3, 0, 1),
    (-288, 3, 1, 0), (60, 4, 0, 0)]

/-- The residue polynomial at `0` (total). -/
noncomputable def i12TV4P0 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-48 * log 2 ^ 3 + 324 * log 2 ^ 2 + 2160 * log 2 + 4824), 0, 0, 1),
    ((216 * log 2 ^ 2 - 972 * log 2 - 3240), 0, 0, 2), ((-432 * log 2 + 972), 0, 0, 3),
    (324, 0, 0, 4), ((-192 * log 2 ^ 3 + 684 * log 2 ^ 2 - 720 * log 2 + 4536), 0, 1, 0),
    ((288 * log 2 ^ 2 - 1008 * log 2 - 3456), 0, 1, 1), ((-864 * log 2 + 1512), 0, 1, 2),
    (864, 0, 1, 3), ((-288 * log 2 ^ 2 + 324 * log 2 - 2016), 0, 2, 0),
    ((-576 * log 2 + 864), 0, 2, 1), (864, 0, 2, 2), ((-480 * log 2 + 420), 0, 3, 0),
    (384, 0, 3, 1), (-60, 0, 4, 0), ((-288 * log 2 ^ 2 + 1224 * log 2 + 3888), 1, 0, 1),
    ((864 * log 2 - 1836), 1, 0, 2), (-864, 1, 0, 3),
    ((-720 * log 2 ^ 2 + 1368 * log 2 - 144), 1, 1, 0), ((864 * log 2 - 1584), 1, 1, 1),
    (-1296, 1, 1, 2), ((-720 * log 2 + 180), 1, 2, 0), (-720, 1, 2, 1), (-624, 1, 3, 0),
    ((-576 * log 2 + 1188), 2, 0, 1), (864, 2, 0, 2), ((-1008 * log 2 + 828), 2, 1, 0),
    (720, 2, 1, 1), (-504, 2, 2, 0), (-384, 3, 0, 1), (-528, 3, 1, 0)]

/-- The residue polynomial at `-1` (total). -/
noncomputable def i12TV4Pm : List (ℝ × ℕ × ℕ × ℕ) :=
  [((36 * log 2 ^ 3 + 324 * log 2 ^ 2 + 1512 * log 2 + 3240), 0, 0, 0),
    ((-324 * log 2 ^ 2 - 1944 * log 2 - 4536), 0, 0, 1), ((972 * log 2 + 2916), 0, 0, 2),
    (-972, 0, 0, 3), ((-216 * log 2 ^ 2 - 1224 * log 2 - 2736), 0, 1, 0),
    ((1296 * log 2 + 3672), 0, 1, 1), (-1944, 0, 1, 2), ((432 * log 2 + 1188), 0, 2, 0),
    (-1296, 0, 2, 1), (-288, 0, 3, 0), ((216 * log 2 ^ 2 + 1152 * log 2 + 2448), 1, 0, 0),
    ((-1296 * log 2 - 3456), 1, 0, 1), (1944, 1, 0, 2), ((-648 * log 2 - 1728), 1, 1, 0),
    (1944, 1, 1, 1), (540, 1, 2, 0), ((432 * log 2 + 1080), 2, 0, 0), (-1296, 2, 0, 1),
    (-540, 2, 1, 0), (288, 3, 0, 0)]

/-- The residue polynomial at `1`, in the Möbius variable (total). -/
noncomputable def i12TV4P1 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((36 * log 2 ^ 2 - 360 * log 2 - 1152), 0, 0, 1), ((-36 * log 2 + 1044), 0, 0, 2),
    (-48, 0, 0, 3), ((180 * log 2 ^ 2 - 1008 * log 2 - 864), 0, 1, 0),
    ((-504 * log 2 + 864), 0, 1, 1), (252, 0, 1, 2), ((-324 * log 2 - 720), 0, 2, 0),
    (324, 0, 2, 1), (24, 0, 3, 0), (-60, 0, 4, 0),
    ((-144 * log 2 ^ 2 - 72 * log 2 - 1656), 1, 0, 1), ((144 * log 2 + 216), 1, 0, 2),
    (-48, 1, 0, 3), ((-144 * log 2 ^ 2 - 360 * log 2 - 1872), 1, 1, 0),
    ((-288 * log 2 + 504), 1, 1, 1), (144, 1, 1, 2), ((-432 * log 2 - 144), 1, 2, 0),
    (-144, 1, 2, 1), (-624, 1, 3, 0), ((-144 * log 2 - 144), 2, 0, 1), (72, 2, 0, 2),
    ((-144 * log 2 - 576), 2, 1, 0), (-144, 2, 1, 1), (-504, 2, 2, 0), (-144, 3, 0, 1),
    (-528, 3, 1, 0)]

/-- The polynomial part of `B` (part A). -/
noncomputable def i12TV4Q0A : List (ℝ × ℕ × ℕ × ℕ) :=
  []

/-- The `1/s` part of `B` (part A). -/
noncomputable def i12TV4Q1A : List (ℝ × ℕ × ℕ × ℕ) :=
  [((12 * log 2 ^ 3 + 108 * log 2 ^ 2 + 504 * log 2 + 1080), 0, 0, 1),
    ((-54 * log 2 ^ 2 - 324 * log 2 - 756), 0, 0, 2), ((108 * log 2 + 324), 0, 0, 3),
    (-81, 0, 0, 4), ((12 * log 2 ^ 3 + 108 * log 2 ^ 2 + 504 * log 2 + 1080), 0, 1, 0),
    ((-36 * log 2 ^ 2 - 216 * log 2 - 504), 0, 1, 1), ((108 * log 2 + 324), 0, 1, 2),
    (-108, 0, 1, 3), ((18 * log 2 ^ 2 + 108 * log 2 + 252), 0, 2, 0),
    ((36 * log 2 + 108), 0, 2, 1), (-54, 0, 2, 2), ((36 * log 2 + 108), 0, 3, 0), (-12, 0, 3, 1),
    (15, 0, 4, 0), ((72 * log 2 ^ 2 + 432 * log 2 + 1008), 1, 0, 1),
    ((-216 * log 2 - 648), 1, 0, 2), (216, 1, 0, 3),
    ((72 * log 2 ^ 2 + 432 * log 2 + 1008), 1, 1, 0), ((-144 * log 2 - 432), 1, 1, 1),
    (216, 1, 1, 2), ((72 * log 2 + 216), 1, 2, 0), (72, 1, 2, 1), (72, 1, 3, 0),
    ((144 * log 2 + 432), 2, 0, 1), (-216, 2, 0, 2), ((144 * log 2 + 432), 2, 1, 0),
    (-144, 2, 1, 1), (72, 2, 2, 0), (96, 3, 0, 1), (96, 3, 1, 0)]

/-- The `1/(1 - s)` part of `B` (part A). -/
noncomputable def i12TV4Q2A : List (ℝ × ℕ × ℕ × ℕ) :=
  [((144 * log 2 ^ 3 - 288 * log 2 ^ 2 + 864 * log 2), 1, 0, 0),
    ((-144 * log 2 ^ 2 - 576 * log 2 - 864), 1, 0, 1), ((432 * log 2 + 864), 1, 0, 2),
    (-432, 1, 0, 3), ((144 * log 2 ^ 2 - 576 * log 2), 1, 1, 0), ((288 * log 2 + 576), 1, 1, 1),
    (-432, 1, 1, 2), ((144 * log 2), 1, 2, 0), (-144, 1, 2, 1),
    ((360 * log 2 ^ 2 - 288 * log 2 + 864), 2, 0, 0), ((-432 * log 2 - 864), 2, 0, 1),
    (648, 2, 0, 2), ((144 * log 2 - 576), 2, 1, 0), (432, 2, 1, 1), (144, 2, 2, 0),
    ((336 * log 2), 3, 0, 0), (-336, 3, 0, 1), (120, 4, 0, 0)]

/-- The residue polynomial at `0` (part A). -/
noncomputable def i12TV4P0A : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-144 * log 2 ^ 3 + 144 * log 2 ^ 2 - 1728 * log 2 - 2016), 0, 0, 0),
    ((-36 * log 2 ^ 3 + 180 * log 2 ^ 2 + 1224 * log 2 + 2664), 0, 0, 1),
    ((162 * log 2 ^ 2 - 540 * log 2 - 1836), 0, 0, 2), ((-324 * log 2 + 540), 0, 0, 3),
    (243, 0, 0, 4), ((-36 * log 2 ^ 3 - 108 * log 2 ^ 2 + 648 * log 2 + 72), 0, 1, 0),
    ((108 * log 2 ^ 2 - 360 * log 2 - 1224), 0, 1, 1), ((-324 * log 2 + 540), 0, 1, 2),
    (324, 0, 1, 3), ((-54 * log 2 ^ 2 - 108 * log 2 - 252), 0, 2, 0),
    ((-108 * log 2 + 180), 0, 2, 1), (162, 0, 2, 2), ((-108 * log 2 + 36), 0, 3, 0),
    (36, 0, 3, 1), (-45, 0, 4, 0), ((-720 * log 2 ^ 2 - 3456), 1, 0, 0),
    ((-252 * log 2 ^ 2 + 936 * log 2 + 2952), 1, 0, 1), ((756 * log 2 - 1404), 1, 0, 2),
    (-756, 1, 0, 3), ((-252 * log 2 ^ 2 - 216 * log 2 + 1224), 1, 1, 0),
    ((504 * log 2 - 936), 1, 1, 1), (-756, 1, 1, 2), ((-252 * log 2 - 252), 1, 2, 0),
    (-252, 1, 2, 1), (-252, 1, 3, 0), ((-1008 * log 2 - 576), 2, 0, 0),
    ((-540 * log 2 + 1044), 2, 0, 1), (810, 2, 0, 2), ((-540 * log 2 + 36), 2, 1, 0),
    (540, 2, 1, 1), (-270, 2, 2, 0), (-480, 3, 0, 0), (-372, 3, 0, 1), (-372, 3, 1, 0)]

/-- The residue polynomial at `-1` (part A). -/
noncomputable def i12TV4PmA : List (ℝ × ℕ × ℕ × ℕ) :=
  [((12 * log 2 ^ 3 + 108 * log 2 ^ 2 + 504 * log 2 + 1080), 0, 0, 0),
    ((-108 * log 2 ^ 2 - 648 * log 2 - 1512), 0, 0, 1), ((324 * log 2 + 972), 0, 0, 2),
    (-324, 0, 0, 3), ((-36 * log 2 ^ 2 - 216 * log 2 - 504), 0, 1, 0),
    ((216 * log 2 + 648), 0, 1, 1), (-324, 0, 1, 2), ((36 * log 2 + 108), 0, 2, 0),
    (-108, 0, 2, 1), (-12, 0, 3, 0), ((144 * log 2 ^ 2 + 720 * log 2 + 1440), 1, 0, 0),
    ((-864 * log 2 - 2160), 1, 0, 1), (1296, 1, 0, 2), ((-288 * log 2 - 720), 1, 1, 0),
    (864, 1, 1, 1), (144, 1, 2, 0), ((360 * log 2 + 864), 2, 0, 0), (-1080, 2, 0, 1),
    (-360, 2, 1, 0), (264, 3, 0, 0)]

/-- The residue polynomial at `1`, in the Möbius variable (part A). -/
noncomputable def i12TV4P1A : List (ℝ × ℕ × ℕ × ℕ) :=
  [((12 * log 2 ^ 3 - 108 * log 2 ^ 2 + 504 * log 2 - 1080), 0, 0, 0),
    ((-144 * log 2 + 288), 0, 0, 1), (72, 0, 0, 2),
    ((48 * log 2 ^ 3 + 72 * log 2 ^ 2 - 864 * log 2 + 1872), 0, 1, 0),
    ((-144 * log 2 ^ 2 - 288 * log 2 + 720), 0, 1, 1), ((144 * log 2 + 144), 0, 1, 2),
    (-48, 0, 1, 3), ((-72 * log 2 ^ 2 - 144 * log 2 + 72), 0, 2, 0),
    ((144 * log 2 + 144), 0, 2, 1), (-72, 0, 2, 2), ((144 * log 2 + 96), 0, 3, 0),
    (-144, 0, 3, 1), (-60, 0, 4, 0), ((36 * log 2 ^ 2 - 216 * log 2 + 504), 1, 0, 0),
    ((-144 * log 2 ^ 2 - 144 * log 2 + 288), 1, 0, 1), ((144 * log 2 + 72), 1, 0, 2),
    (-48, 1, 0, 3), ((-288 * log 2 ^ 2 + 144), 1, 1, 0), (144, 1, 1, 1),
    ((-288 * log 2 + 216), 1, 2, 0), (-288, 1, 2, 1), (-480, 1, 3, 0),
    ((108 * log 2 - 324), 2, 0, 0), ((-144 * log 2 - 72), 2, 0, 1), (72, 2, 0, 2), (144, 2, 1, 0),
    (-288, 2, 1, 1), (-288, 2, 2, 0), (60, 3, 0, 0), (-144, 3, 0, 1), (-192, 3, 1, 0)]

/-- The polynomial part of `B` (part C). -/
noncomputable def i12TV4Q0C : List (ℝ × ℕ × ℕ × ℕ) :=
  []

/-- The `1/s` part of `B` (part C). -/
noncomputable def i12TV4Q1C : List (ℝ × ℕ × ℕ × ℕ) :=
  [((4 * log 2 ^ 3 + 24 * log 2 ^ 2 + 72 * log 2 + 96), 0, 1, 0),
    ((-36 * log 2 ^ 2 - 144 * log 2 - 216), 0, 1, 1), ((108 * log 2 + 216), 0, 1, 2),
    (-108, 0, 1, 3), ((-18 * log 2 ^ 2 - 72 * log 2 - 108), 0, 2, 0),
    ((108 * log 2 + 216), 0, 2, 1), (-162, 0, 2, 2), ((28 * log 2 + 56), 0, 3, 0), (-84, 0, 3, 1),
    (-15, 0, 4, 0), ((12 * log 2 ^ 2 + 48 * log 2 + 72), 1, 1, 0), ((-72 * log 2 - 144), 1, 1, 1),
    (108, 1, 1, 2), ((-36 * log 2 - 72), 1, 2, 0), (108, 1, 2, 1), (28, 1, 3, 0),
    ((12 * log 2 + 24), 2, 1, 0), (-36, 2, 1, 1), (-18, 2, 2, 0), (4, 3, 1, 0)]

/-- The `1/(1 - s)` part of `B` (part C). -/
noncomputable def i12TV4Q2C : List (ℝ × ℕ × ℕ × ℕ) :=
  [((4 * log 2 ^ 4 + 48 * log 2 ^ 3 + 336 * log 2 ^ 2 + 1440 * log 2 + 2976), 0, 0, 0),
    ((-48 * log 2 ^ 3 - 432 * log 2 ^ 2 - 2016 * log 2 - 4320), 0, 0, 1),
    ((216 * log 2 ^ 2 + 1296 * log 2 + 3024), 0, 0, 2), ((-432 * log 2 - 1296), 0, 0, 3),
    (324, 0, 0, 4), ((-32 * log 2 ^ 3 - 288 * log 2 ^ 2 - 1344 * log 2 - 2880), 0, 1, 0),
    ((288 * log 2 ^ 2 + 1728 * log 2 + 4032), 0, 1, 1), ((-864 * log 2 - 2592), 0, 1, 2),
    (864, 0, 1, 3), ((96 * log 2 ^ 2 + 576 * log 2 + 1344), 0, 2, 0),
    ((-576 * log 2 - 1728), 0, 2, 1), (864, 0, 2, 2), ((-128 * log 2 - 384), 0, 3, 0),
    (384, 0, 3, 1), (64, 0, 4, 0),
    ((16 * log 2 ^ 3 + 144 * log 2 ^ 2 + 672 * log 2 + 1440), 1, 0, 0),
    ((-144 * log 2 ^ 2 - 864 * log 2 - 2016), 1, 0, 1), ((432 * log 2 + 1296), 1, 0, 2),
    (-432, 1, 0, 3), ((-96 * log 2 ^ 2 - 576 * log 2 - 1344), 1, 1, 0),
    ((576 * log 2 + 1728), 1, 1, 1), (-864, 1, 1, 2), ((192 * log 2 + 576), 1, 2, 0),
    (-576, 1, 2, 1), (-128, 1, 3, 0), ((24 * log 2 ^ 2 + 144 * log 2 + 336), 2, 0, 0),
    ((-144 * log 2 - 432), 2, 0, 1), (216, 2, 0, 2), ((-96 * log 2 - 288), 2, 1, 0),
    (288, 2, 1, 1), (96, 2, 2, 0), ((16 * log 2 + 48), 3, 0, 0), (-48, 3, 0, 1), (-32, 3, 1, 0),
    (4, 4, 0, 0)]

/-- The residue polynomial at `0` (part C). -/
noncomputable def i12TV4P0C : List (ℝ × ℕ × ℕ × ℕ) :=
  [((log 2 ^ 4 - 16 * log 2 ^ 3 - 156 * log 2 ^ 2 - 720 * log 2 - 1512), 0, 0, 0),
    ((-12 * log 2 ^ 3 + 144 * log 2 ^ 2 + 936 * log 2 + 2160), 0, 0, 1),
    ((54 * log 2 ^ 2 - 432 * log 2 - 1404), 0, 0, 2), ((-108 * log 2 + 432), 0, 0, 3),
    (81, 0, 0, 4), ((-20 * log 2 ^ 3 + 108 * log 2 ^ 2 + 744 * log 2 + 1656), 0, 1, 0),
    ((180 * log 2 ^ 2 - 648 * log 2 - 2232), 0, 1, 1), ((-540 * log 2 + 972), 0, 1, 2),
    (540, 0, 1, 3), ((78 * log 2 ^ 2 - 228 * log 2 - 804), 0, 2, 0),
    ((-468 * log 2 + 684), 0, 2, 1), (702, 0, 2, 2), ((-116 * log 2 + 156), 0, 3, 0),
    (348, 0, 3, 1), (61, 0, 4, 0),
    ((4 * log 2 ^ 3 - 48 * log 2 ^ 2 - 312 * log 2 - 720), 1, 0, 0),
    ((-36 * log 2 ^ 2 + 288 * log 2 + 936), 1, 0, 1), ((108 * log 2 - 432), 1, 0, 2),
    (-108, 1, 0, 3), ((-60 * log 2 ^ 2 + 216 * log 2 + 744), 1, 1, 0),
    ((360 * log 2 - 648), 1, 1, 1), (-540, 1, 1, 2), ((156 * log 2 - 228), 1, 2, 0),
    (-468, 1, 2, 1), (-116, 1, 3, 0), ((6 * log 2 ^ 2 - 48 * log 2 - 156), 2, 0, 0),
    ((-36 * log 2 + 144), 2, 0, 1), (54, 2, 0, 2), ((-60 * log 2 + 108), 2, 1, 0), (180, 2, 1, 1),
    (78, 2, 2, 0), ((4 * log 2 - 16), 3, 0, 0), (-12, 3, 0, 1), (-20, 3, 1, 0), (1, 4, 0, 0)]

/-- The residue polynomial at `-1` (part C). -/
noncomputable def i12TV4PmC : List (ℝ × ℕ × ℕ × ℕ) :=
  [((24 * log 2 ^ 3 + 216 * log 2 ^ 2 + 1008 * log 2 + 2160), 0, 0, 0),
    ((-216 * log 2 ^ 2 - 1296 * log 2 - 3024), 0, 0, 1), ((648 * log 2 + 1944), 0, 0, 2),
    (-648, 0, 0, 3), ((-180 * log 2 ^ 2 - 1008 * log 2 - 2232), 0, 1, 0),
    ((1080 * log 2 + 3024), 0, 1, 1), (-1620, 0, 1, 2), ((396 * log 2 + 1080), 0, 2, 0),
    (-1188, 0, 2, 1), (-276, 0, 3, 0), ((72 * log 2 ^ 2 + 432 * log 2 + 1008), 1, 0, 0),
    ((-432 * log 2 - 1296), 1, 0, 1), (648, 1, 0, 2), ((-360 * log 2 - 1008), 1, 1, 0),
    (1080, 1, 1, 1), (396, 1, 2, 0), ((72 * log 2 + 216), 2, 0, 0), (-216, 2, 0, 1),
    (-180, 2, 1, 0), (24, 3, 0, 0)]

/-- The residue polynomial at `1`, in the Möbius variable (part C). -/
noncomputable def i12TV4P1C : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-4 * log 2 ^ 4 + 12 * log 2 ^ 3 - 24 * log 2 ^ 2 + 24 * log 2 + 624), 0, 0, 0),
    ((16 * log 2 ^ 3 - 36 * log 2 ^ 2 + 48 * log 2 - 24), 0, 0, 1),
    ((-24 * log 2 ^ 2 + 36 * log 2 - 24), 0, 0, 2), ((16 * log 2 - 12), 0, 0, 3), (-4, 0, 0, 4),
    ((-16 * log 2 ^ 3 + 36 * log 2 ^ 2 - 48 * log 2 - 264), 0, 1, 0),
    ((48 * log 2 ^ 2 - 72 * log 2 + 48), 0, 1, 1), ((-48 * log 2 + 36), 0, 1, 2), (16, 0, 1, 3),
    ((-24 * log 2 ^ 2 + 36 * log 2 + 48), 0, 2, 0), ((48 * log 2 - 36), 0, 2, 1), (-24, 0, 2, 2),
    ((-16 * log 2 - 4), 0, 3, 0), (16, 0, 3, 1),
    ((16 * log 2 ^ 3 - 36 * log 2 ^ 2 + 48 * log 2 + 552), 1, 0, 0),
    ((-48 * log 2 ^ 2 + 72 * log 2 - 48), 1, 0, 1), ((48 * log 2 - 36), 1, 0, 2), (-16, 1, 0, 3),
    ((48 * log 2 ^ 2 - 72 * log 2 - 240), 1, 1, 0), ((-96 * log 2 + 72), 1, 1, 1), (48, 1, 1, 2),
    ((48 * log 2 + 60), 1, 2, 0), (-48, 1, 2, 1), (-16, 1, 3, 0),
    ((-24 * log 2 ^ 2 + 36 * log 2 + 264), 2, 0, 0), ((48 * log 2 - 36), 2, 0, 1), (-24, 2, 0, 2),
    ((-48 * log 2 - 156), 2, 1, 0), (48, 2, 1, 1), (72, 2, 2, 0), ((16 * log 2 + 116), 3, 0, 0),
    (-16, 3, 0, 1), (-112, 3, 1, 0), (60, 4, 0, 0)]

/-- The polynomial part of `B` (part B). -/
noncomputable def i12TV4Q0B : List (ℝ × ℕ × ℕ × ℕ) :=
  [((60 * log 2 ^ 3 - 864 * log 2 ^ 2 + 1944 * log 2 - 3096), 0, 1, 0),
    ((90 * log 2 ^ 2 - 864 * log 2 + 828), 0, 2, 0), ((60 * log 2 - 300), 0, 3, 0), (15, 0, 4, 0),
    ((96 * log 2 ^ 3 - 1152 * log 2 ^ 2 + 288 * log 2 - 6336), 1, 0, 0),
    ((-1296 * log 2 - 720), 2, 0, 0), ((-96 * log 2 - 624), 3, 0, 0), (-60, 4, 0, 0)]

/-- The `1/s` part of `B` (part B). -/
noncomputable def i12TV4Q1B : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-4 * log 2 ^ 3 - 24 * log 2 ^ 2 - 72 * log 2 - 96), 0, 1, 0),
    ((-18 * log 2 ^ 2 - 72 * log 2 - 108), 0, 2, 0), ((-28 * log 2 - 56), 0, 3, 0),
    (-15, 0, 4, 0), ((-12 * log 2 ^ 2 - 48 * log 2 - 72), 1, 1, 0), ((-36 * log 2 - 72), 1, 2, 0),
    (-28, 1, 3, 0), ((-12 * log 2 - 24), 2, 1, 0), (-18, 2, 2, 0), (-4, 3, 1, 0)]

/-- The `1/(1 - s)` part of `B` (part B). -/
noncomputable def i12TV4Q2B : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-64 * log 2 ^ 4 + 384 * log 2 ^ 3 - 1344 * log 2 ^ 2 + 2880 * log 2 - 2976), 0, 0, 0),
    ((-256 * log 2 ^ 3 + 1152 * log 2 ^ 2 - 2688 * log 2 + 2880), 0, 1, 0),
    ((-384 * log 2 ^ 2 + 1152 * log 2 - 1344), 0, 2, 0), ((-256 * log 2 + 384), 0, 3, 0),
    (-64, 0, 4, 0), ((-256 * log 2 ^ 3 + 1152 * log 2 ^ 2 - 2688 * log 2 + 2880), 1, 0, 0),
    ((-768 * log 2 ^ 2 + 2304 * log 2 - 2688), 1, 1, 0), ((-768 * log 2 + 1152), 1, 2, 0),
    (-256, 1, 3, 0), ((-384 * log 2 ^ 2 + 1152 * log 2 - 1344), 2, 0, 0),
    ((-768 * log 2 + 1152), 2, 1, 0), (-384, 2, 2, 0), ((-256 * log 2 + 384), 3, 0, 0),
    (-256, 3, 1, 0), (-64, 4, 0, 0)]

/-- The residue polynomial at `0` (part B). -/
noncomputable def i12TV4P0B : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-log 2 ^ 4 + 160 * log 2 ^ 3 + 12 * log 2 ^ 2 + 2448 * log 2 + 3528), 0, 0, 0),
    ((-136 * log 2 ^ 3 + 684 * log 2 ^ 2 - 2112 * log 2 + 2808), 0, 1, 0),
    ((-312 * log 2 ^ 2 + 660 * log 2 - 960), 0, 2, 0), ((-256 * log 2 + 228), 0, 3, 0),
    (-76, 0, 4, 0), ((-4 * log 2 ^ 3 + 768 * log 2 ^ 2 + 312 * log 2 + 4176), 1, 0, 0),
    ((-408 * log 2 ^ 2 + 1368 * log 2 - 2112), 1, 1, 0), ((-624 * log 2 + 660), 1, 2, 0),
    (-256, 1, 3, 0), ((-6 * log 2 ^ 2 + 1056 * log 2 + 732), 2, 0, 0),
    ((-408 * log 2 + 684), 2, 1, 0), (-312, 2, 2, 0), ((-4 * log 2 + 496), 3, 0, 0),
    (-136, 3, 1, 0), (-1, 4, 0, 0)]

/-- The residue polynomial at `-1` (part B). -/
noncomputable def i12TV4PmB : List (ℝ × ℕ × ℕ × ℕ) :=
  []

/-- The residue polynomial at `1`, in the Möbius variable (part B). -/
noncomputable def i12TV4P1B : List (ℝ × ℕ × ℕ × ℕ) :=
  [((4 * log 2 ^ 4 - 24 * log 2 ^ 3 + 132 * log 2 ^ 2 - 528 * log 2 + 456), 0, 0, 0),
    ((-16 * log 2 ^ 3 + 72 * log 2 ^ 2 - 264 * log 2 - 1416), 0, 0, 1),
    ((24 * log 2 ^ 2 - 72 * log 2 + 996), 0, 0, 2), ((-16 * log 2 - 36), 0, 0, 3), (4, 0, 0, 4),
    ((-32 * log 2 ^ 3 + 72 * log 2 ^ 2 - 96 * log 2 - 2472), 0, 1, 0),
    ((96 * log 2 ^ 2 - 144 * log 2 + 96), 0, 1, 1), ((-96 * log 2 + 72), 0, 1, 2), (32, 0, 1, 3),
    ((96 * log 2 ^ 2 - 216 * log 2 - 840), 0, 2, 0), ((-192 * log 2 + 216), 0, 2, 1),
    (96, 0, 2, 2), ((-128 * log 2 - 68), 0, 3, 0), (128, 0, 3, 1),
    ((-16 * log 2 ^ 3 + 168 * log 2 - 1056), 1, 0, 0), ((48 * log 2 ^ 2 - 1896), 1, 0, 1),
    ((-48 * log 2 + 180), 1, 0, 2), (16, 1, 0, 3),
    ((96 * log 2 ^ 2 - 288 * log 2 - 1776), 1, 1, 0), ((-192 * log 2 + 288), 1, 1, 1),
    (96, 1, 1, 2), ((-192 * log 2 - 420), 1, 2, 0), (192, 1, 2, 1), (-128, 1, 3, 0),
    ((24 * log 2 ^ 2 - 144 * log 2 + 60), 2, 0, 0), ((-48 * log 2 - 36), 2, 0, 1), (24, 2, 0, 2),
    ((-96 * log 2 - 564), 2, 1, 0), (96, 2, 1, 1), (-288, 2, 2, 0),
    ((-16 * log 2 - 176), 3, 0, 0), (16, 3, 0, 1), (-224, 3, 1, 0), (-60, 4, 0, 0)]


/-! ### The primitive -/

/-- The part of `J_4` coming from `e_A`. -/
noncomputable def i12TV4JA (s : ℝ) : ℝ :=
  2 / (s * (1 - s)) * i12TE (i12TeA s) 4 (i12Rk s)

/-- The part of `J_4` coming from the first term of `E_N[e_B]`. -/
noncomputable def i12TV4JC (s : ℝ) : ℝ :=
  2 / (s * (1 - s)) * ((1 + 1 / i12Rk s) ^ 2 / (1 / i12Rk s) *
    i12TeB s 4 (2 * log (1 / i12Rk s) - 3 * log (1 + 1 / i12Rk s)))

/-- The part of `J_4` coming from the other terms of `E_N[e_B]`. -/
noncomputable def i12TV4JB (s : ℝ) : ℝ :=
  2 / (s * (1 - s)) * (-(1 / i12Rk s * i12TeB s 4 (-log (1 / i12Rk s))) -
    (1 / (1 / i12Rk s) + 2) * i12TeB s 4 (2 * log (1 / i12Rk s)) +
    3 * (4 : ℕ) * i12TeB s (4 - 1) (2 * log (1 / i12Rk s)))

/-- The elementary part of the primitive (part A). -/
noncomputable def i12TV4BA (s : ℝ) : ℝ :=
  i12TVPoly i12TV4Q0A s + i12TVPoly i12TV4Q1A s / s + i12TVPoly i12TV4Q2A s / (1 - s)

/-- The primitive (part A). -/
noncomputable def i12TV4PhiA (s : ℝ) : ℝ :=
  i12TV4BA s + i12TVPsi zero i12TV4P0A s + i12TVPsi negOne i12TV4PmA s +
    (i12TVPsi negOne i12TV4P1A (mobMap s) - i12TVPsi zero i12TV4P1A (mobMap s))

/-- The elementary part of the primitive (part C). -/
noncomputable def i12TV4BC (s : ℝ) : ℝ :=
  i12TVPoly i12TV4Q0C s + i12TVPoly i12TV4Q1C s / s + i12TVPoly i12TV4Q2C s / (1 - s)

/-- The primitive (part C). -/
noncomputable def i12TV4PhiC (s : ℝ) : ℝ :=
  i12TV4BC s + i12TVPsi zero i12TV4P0C s + i12TVPsi negOne i12TV4PmC s +
    (i12TVPsi negOne i12TV4P1C (mobMap s) - i12TVPsi zero i12TV4P1C (mobMap s))

/-- The elementary part of the primitive (part B). -/
noncomputable def i12TV4BB (s : ℝ) : ℝ :=
  i12TVPoly i12TV4Q0B s + i12TVPoly i12TV4Q1B s / s + i12TVPoly i12TV4Q2B s / (1 - s)

/-- The primitive (part B). -/
noncomputable def i12TV4PhiB (s : ℝ) : ℝ :=
  i12TV4BB s + i12TVPsi zero i12TV4P0B s + i12TVPsi negOne i12TV4PmB s +
    (i12TVPsi negOne i12TV4P1B (mobMap s) - i12TVPsi zero i12TV4P1B (mobMap s))

/-- The elementary part of the primitive (total). -/
noncomputable def i12TV4B (s : ℝ) : ℝ :=
  i12TVPoly i12TV4Q0 s + i12TVPoly i12TV4Q1 s / s + i12TVPoly i12TV4Q2 s / (1 - s)

/-- The primitive (total). -/
noncomputable def i12TV4Phi (s : ℝ) : ℝ :=
  i12TV4B s + i12TVPsi zero i12TV4P0 s + i12TVPsi negOne i12TV4Pm s +
    (i12TVPsi negOne i12TV4P1 (mobMap s) - i12TVPsi zero i12TV4P1 (mobMap s))

/-- **`ΦA' = JA` on `(0, 1)`.** -/
theorem hasDerivAt_i12TV4PhiA {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12TV4PhiA (i12TV4JA s) s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  have h1s' : 1 + s ≠ 0 := by linarith [hs.1]
  have hB := ((hasDerivAt_i12TVPoly i12TV4Q0A hs).add
    ((hasDerivAt_i12TVPoly i12TV4Q1A hs).div (hasDerivAt_id' s) hs0)).add
    ((hasDerivAt_i12TVPoly i12TV4Q2A hs).div ((hasDerivAt_id' s).const_sub 1) h1s)
  have h := ((hB.add (hasDerivAt_i12TVPsi zero i12TV4P0A hs)).add
    (hasDerivAt_i12TVPsi negOne i12TV4PmA hs)).add (hasDerivAt_i12TVMob i12TV4P1A hs)
  convert h using 1
  · rfl
  simp only [i12TV4JA, i12TE, i12TeA, i12TPn, i12_log_i12Rk hs, i12TV_log_one_add_i12Rk hs]
  simp only [i12TVPoly, i12TVPolyD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    i12TVMono_mobMap _ _ _ hs,
    i12TV4Q0A, i12TV4Q1A, i12TV4Q2A, i12TV4P0A, i12TV4PmA, i12TV4P1A]
  simp only [i12TVMono, kernel_zero, kernel_negOne, i12Rk, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_succ]
  field_simp
  ring

/-- **`ΦC' = JC` on `(0, 1)`.** -/
theorem hasDerivAt_i12TV4PhiC {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12TV4PhiC (i12TV4JC s) s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  have h1s' : 1 + s ≠ 0 := by linarith [hs.1]
  have hB := ((hasDerivAt_i12TVPoly i12TV4Q0C hs).add
    ((hasDerivAt_i12TVPoly i12TV4Q1C hs).div (hasDerivAt_id' s) hs0)).add
    ((hasDerivAt_i12TVPoly i12TV4Q2C hs).div ((hasDerivAt_id' s).const_sub 1) h1s)
  have h := ((hB.add (hasDerivAt_i12TVPsi zero i12TV4P0C hs)).add
    (hasDerivAt_i12TVPsi negOne i12TV4PmC hs)).add (hasDerivAt_i12TVMob i12TV4P1C hs)
  convert h using 1
  · rfl
  simp only [i12TV4JC, i12TeB, i12TPn, i12TV_log_one_div_i12Rk hs,
    i12TV_log_one_add_one_div_i12Rk hs]
  simp only [i12TVPoly, i12TVPolyD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    i12TVMono_mobMap _ _ _ hs,
    i12TV4Q0C, i12TV4Q1C, i12TV4Q2C, i12TV4P0C, i12TV4PmC, i12TV4P1C]
  simp only [i12TVMono, kernel_zero, kernel_negOne, i12Rk, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_succ]
  field_simp
  ring

/-- **`ΦB' = JB` on `(0, 1)`.** -/
theorem hasDerivAt_i12TV4PhiB {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12TV4PhiB (i12TV4JB s) s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  have h1s' : 1 + s ≠ 0 := by linarith [hs.1]
  have hB := ((hasDerivAt_i12TVPoly i12TV4Q0B hs).add
    ((hasDerivAt_i12TVPoly i12TV4Q1B hs).div (hasDerivAt_id' s) hs0)).add
    ((hasDerivAt_i12TVPoly i12TV4Q2B hs).div ((hasDerivAt_id' s).const_sub 1) h1s)
  have h := ((hB.add (hasDerivAt_i12TVPsi zero i12TV4P0B hs)).add
    (hasDerivAt_i12TVPsi negOne i12TV4PmB hs)).add (hasDerivAt_i12TVMob i12TV4P1B hs)
  convert h using 1
  · rfl
  simp only [i12TV4JB, i12TeB, i12TPn, i12TV_log_one_div_i12Rk hs]
  simp only [i12TVPoly, i12TVPolyD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    i12TVMono_mobMap _ _ _ hs,
    i12TV4Q0B, i12TV4Q1B, i12TV4Q2B, i12TV4P0B, i12TV4PmB, i12TV4P1B]
  simp only [i12TVMono, kernel_zero, kernel_negOne, i12Rk, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_succ]
  field_simp
  ring

theorem i12TV4Phi_eq :
    i12TV4Phi = fun s => i12TV4PhiA s + i12TV4PhiC s + i12TV4PhiB s := by
  funext s
  simp only [i12TV4Phi, i12TV4PhiA, i12TV4PhiC, i12TV4PhiB, i12TV4B, i12TV4BA, i12TV4BC, i12TV4BB,
    i12TVPoly, i12TVPsi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    i12TV4Q0, i12TV4Q1, i12TV4Q2, i12TV4P0, i12TV4Pm, i12TV4P1, i12TV4Q0A, i12TV4Q1A, i12TV4Q2A,
    i12TV4P0A, i12TV4PmA, i12TV4P1A, i12TV4Q0C, i12TV4Q1C, i12TV4Q2C, i12TV4P0C, i12TV4PmC,
    i12TV4P1C, i12TV4Q0B, i12TV4Q1B, i12TV4Q2B, i12TV4P0B, i12TV4PmB, i12TV4P1B]
  ring

/-- **`Φ' = J_4` on `(0, 1)`.** -/
theorem hasDerivAt_i12TV4Phi {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12TV4Phi (i12TJ 4 s) s := by
  rw [i12TV4Phi_eq, show i12TJ 4 s = i12TV4JA s + i12TV4JC s + i12TV4JB s by
    simp only [i12TJ, i12TE, i12TV4JA, i12TV4JC, i12TV4JB]; ring]
  exact ((hasDerivAt_i12TV4PhiA hs).add (hasDerivAt_i12TV4PhiC hs)).add (hasDerivAt_i12TV4PhiB hs)

end QED.ThreeLoopD
