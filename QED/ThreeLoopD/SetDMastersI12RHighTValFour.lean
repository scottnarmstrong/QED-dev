/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighTValFourPrim
import QED.Polylog.HPLAlt4Rel
import QED.Polylog.HPLAlt5Rel
import QED.Polylog.HPLLiHalf
import QED.Polylog.HPLValues
import QED.Polylog.HPLValues3
import QED.Polylog.HPLValues4
import QED.Polylog.HPLValues5
import QED.Polylog.HPLValuesAlt4
import QED.Polylog.HPLValuesAlt5A
import QED.Polylog.HPLValuesAlt5B
import QED.Polylog.HPLValuesAlt5C
import QED.Polylog.HPLValuesAlt5D
import QED.Polylog.HPLValuesTrailing
import QED.Polylog.LiHalf

/-!
# Set (d), master `I₁₂`: the face terms of order 4

`∫₀¹ J_4(s) ds = 24 T_4` (`QED.ThreeLoopD.integral_i12TJ_four`), hence the value of
`T_A⁽4⁾(0) + T_B⁽4⁾(0)` (`QED.ThreeLoopD.iteratedDeriv_i12TA_add_i12TB_four`).

## Proof

As for order three (`QED.ThreeLoopD.SetDMastersI12RHighTValThree`), with the primitive
`QED.ThreeLoopD.i12TV4Phi` of `QED.ThreeLoopD.SetDMastersI12RHighTValFourPrim`: at the endpoints
the elementary part `B` is a constant plus a combination of the atoms `QED.ThreeLoopD.i12TVZ`
(at `0`) and `QED.ThreeLoopD.i12TVO` (at `1`), which tend to `0`, and the harmonic
polylogarithm parts tend to `0` or to the library values at `1` (weight at most five; the
values of `Li₄(1/2)` and `Li₅(1/2)` cancel). The endpoint identities for `B` are checked after
multiplying by the denominators of the atoms (`QED.ThreeLoopD.i12TVZs_mul`,
`QED.ThreeLoopD.i12TVOs_mul`), so that `field_simp` only meets the folded polynomials.

## Main results

* `QED.ThreeLoopD.integral_i12TJ_four`: `∫₀¹ J_4 = 24 T_4`.
* `QED.ThreeLoopD.iteratedDeriv_i12TA_add_i12TB_four`: `T_A⁽4⁾(0) + T_B⁽4⁾(0) = 24 T_4`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory
open QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### Clearing the denominators of the endpoint atoms -/

/-- `QED.ThreeLoopD.i12TVZs L s` times `sᴺ (1 - s)ᴳ`, as a polynomial expression. -/
noncomputable def i12TVZsNum (N G : ℕ) (L : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (s : ℝ) : ℝ :=
  (L.map fun t => t.1 * (log s ^ t.2.1 * (log (1 - s) + s) ^ t.2.2.1 *
    (log (1 + s) - s) ^ t.2.2.2.1 * s ^ t.2.2.2.2.1 * s ^ (N - t.2.2.2.2.2.1) *
    (1 - s) ^ (G - t.2.2.2.2.2.2))).sum

/-- `QED.ThreeLoopD.i12TVOs L s` times `(1 - s)ᴺ sᴳ`, as a polynomial expression. -/
noncomputable def i12TVOsNum (N G : ℕ) (L : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (s : ℝ) : ℝ :=
  (L.map fun t => t.1 * (log (1 - s) ^ t.2.1 * (log s + (1 - s)) ^ t.2.2.1 *
    (log (1 + s) - log 2 + (1 - s) / 2) ^ t.2.2.2.1 * (1 - s) ^ t.2.2.2.2.1 *
    (1 - s) ^ (N - t.2.2.2.2.2.1) * s ^ (G - t.2.2.2.2.2.2))).sum

theorem i12TVZs_mul (N G : ℕ) (L : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) {s : ℝ} (hs0 : s ≠ 0)
    (h1s : 1 - s ≠ 0)
    (hL : (L.map Prod.snd).all (fun x => decide (x.2.2.2.2.1 ≤ N ∧ x.2.2.2.2.2 ≤ G)) = true) :
    i12TVZs L s * (s ^ N * (1 - s) ^ G) = i12TVZsNum N G L s := by
  induction L with
  | nil => simp [i12TVZs, i12TVZsNum]
  | cons t L ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hL
    simp only [i12TVZs, i12TVZsNum, List.map_cons, List.sum_cons] at ih ⊢
    rw [add_mul, ih hL.2, pow_sub₀ s hs0 hL.1.1, pow_sub₀ (1 - s) h1s hL.1.2, i12TVZ, inv_pow,
      inv_pow]
    ring

theorem i12TVOs_mul (N G : ℕ) (L : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) {s : ℝ} (hs0 : s ≠ 0)
    (h1s : 1 - s ≠ 0)
    (hL : (L.map Prod.snd).all (fun x => decide (x.2.2.2.2.1 ≤ N ∧ x.2.2.2.2.2 ≤ G)) = true) :
    i12TVOs L s * ((1 - s) ^ N * s ^ G) = i12TVOsNum N G L s := by
  induction L with
  | nil => simp [i12TVOs, i12TVOsNum]
  | cons t L ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hL
    simp only [i12TVOs, i12TVOsNum, List.map_cons, List.sum_cons] at ih ⊢
    rw [add_mul, ih hL.2, pow_sub₀ (1 - s) h1s hL.1.1, pow_sub₀ s hs0 hL.1.2, i12TVO, inv_pow,
      inv_pow]
    ring

/-! ### The endpoint limits -/

/-- The atoms of `B` at `0`. (part 1) -/
noncomputable def i12TV4Z_1 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((-276 * log 2 ^ 3 - 576 * log 2 ^ 2 - 4824 * log 2 - 8856), 0, 0, 0, 1, 0, 0),
    ((-60 * log 2 ^ 4 + 432 * log 2 ^ 3 - 1008 * log 2 ^ 2 + 4320 * log 2), 0, 0, 0, 1, 0, 1),
    ((306 * log 2 ^ 2 + 4392 * log 2 + 9180), 0, 0, 0, 2, 0, 0),
    ((-336 * log 2 ^ 3 + 432 * log 2 ^ 2 - 6048 * log 2 - 4320), 0, 0, 0, 2, 0, 1),
    ((-2196 * log 2 - 6540), 0, 0, 0, 3, 0, 0),
    ((216 * log 2 ^ 2 + 4752 * log 2 + 7056), 0, 0, 0, 3, 0, 1), (2451, 0, 0, 0, 4, 0, 0),
    ((-2256 * log 2 - 5616), 0, 0, 0, 4, 0, 1), (2436, 0, 0, 0, 5, 0, 1),
    ((-48 * log 2 ^ 3 - 612 * log 2 ^ 2 - 3024 * log 2 - 6552), 0, 0, 1, 0, 0, 0),
    ((12 * log 2 ^ 3 + 108 * log 2 ^ 2 + 504 * log 2 + 1080), 0, 0, 1, 0, 1, 0),
    ((720 * log 2 ^ 2 + 5220 * log 2 + 12456), 0, 0, 1, 1, 0, 0),
    ((-48 * log 2 ^ 3 - 432 * log 2 ^ 2 - 2016 * log 2 - 4320), 0, 0, 1, 1, 0, 1),
    ((-3600 * log 2 - 12300), 0, 0, 1, 2, 0, 0),
    ((720 * log 2 ^ 2 + 4320 * log 2 + 10080), 0, 0, 1, 2, 0, 1), (6000, 0, 0, 1, 3, 0, 0),
    ((-3600 * log 2 - 10800), 0, 0, 1, 3, 0, 1), (6000, 0, 0, 1, 4, 0, 1),
    ((216 * log 2 ^ 2 + 1836 * log 2 + 4536), 0, 0, 2, 0, 0, 0),
    ((-54 * log 2 ^ 2 - 324 * log 2 - 756), 0, 0, 2, 0, 1, 0),
    ((-2160 * log 2 - 7830), 0, 0, 2, 1, 0, 0),
    ((216 * log 2 ^ 2 + 1296 * log 2 + 3024), 0, 0, 2, 1, 0, 1), (5400, 0, 0, 2, 2, 0, 0),
    ((-2160 * log 2 - 6480), 0, 0, 2, 2, 0, 1), (5400, 0, 0, 2, 3, 0, 1),
    ((-432 * log 2 - 1836), 0, 0, 3, 0, 0, 0), ((108 * log 2 + 324), 0, 0, 3, 0, 1, 0),
    (2160, 0, 0, 3, 1, 0, 0), ((-432 * log 2 - 1296), 0, 0, 3, 1, 0, 1), (2160, 0, 0, 3, 2, 0, 1),
    (324, 0, 0, 4, 0, 0, 0), (-81, 0, 0, 4, 0, 1, 0), (324, 0, 0, 4, 1, 0, 1),
    ((228 * log 2 ^ 3 + 108 * log 2 ^ 2 + 2520 * log 2 + 3744), 0, 1, 0, 0, 0, 0),
    ((-12 * log 2 ^ 3 - 108 * log 2 ^ 2 - 504 * log 2 - 1080), 0, 1, 0, 0, 1, 0),
    ((108 * log 2 ^ 2 - 4068 * log 2 - 7200), 0, 1, 0, 1, 0, 0),
    ((288 * log 2 ^ 3 - 864 * log 2 ^ 2 + 4032 * log 2), 0, 1, 0, 1, 0, 1),
    ((2988 * log 2 + 7944), 0, 1, 0, 2, 0, 0),
    ((288 * log 2 ^ 2 - 5184 * log 2 - 4032), 0, 1, 0, 2, 0, 1), (-3804, 0, 1, 0, 3, 0, 0)]

/-- The atoms of `B` at `0`. (part 2) -/
noncomputable def i12TV4Z_2 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((3168 * log 2 + 6048), 0, 1, 0, 3, 0, 1), (-3744, 0, 1, 0, 4, 0, 1),
    ((-288 * log 2 ^ 2 - 2448 * log 2 - 5760), 0, 1, 1, 0, 0, 0),
    ((72 * log 2 ^ 2 + 360 * log 2 + 720), 0, 1, 1, 0, 1, 0),
    ((2880 * log 2 + 10440), 0, 1, 1, 1, 0, 0),
    ((-288 * log 2 ^ 2 - 1728 * log 2 - 4032), 0, 1, 1, 1, 0, 1), (-7200, 0, 1, 1, 2, 0, 0),
    ((2880 * log 2 + 8640), 0, 1, 1, 2, 0, 1), (-7200, 0, 1, 1, 3, 0, 1),
    ((864 * log 2 + 3672), 0, 1, 2, 0, 0, 0), ((-216 * log 2 - 540), 0, 1, 2, 0, 1, 0),
    (-4320, 0, 1, 2, 1, 0, 0), ((864 * log 2 + 2592), 0, 1, 2, 1, 0, 1),
    (-4320, 0, 1, 2, 2, 0, 1), (-864, 0, 1, 3, 0, 0, 0), (216, 0, 1, 3, 0, 1, 0),
    (-864, 0, 1, 3, 1, 0, 1), ((-198 * log 2 ^ 2 + 1116 * log 2 + 1476), 0, 2, 0, 0, 0, 0),
    ((-18 * log 2 ^ 2 - 36 * log 2 + 36), 0, 2, 0, 0, 1, 0),
    ((-1548 * log 2 - 3222), 0, 2, 0, 1, 0, 0),
    ((-288 * log 2 ^ 2 + 1728 * log 2), 0, 2, 0, 1, 0, 1), (2106, 0, 2, 0, 2, 0, 0),
    ((-1728 * log 2 - 1728), 0, 2, 0, 2, 0, 1), (2016, 0, 2, 0, 3, 0, 1),
    ((-576 * log 2 - 2448), 0, 2, 1, 0, 0, 0), ((144 * log 2 + 324), 0, 2, 1, 0, 1, 0),
    (2880, 0, 2, 1, 1, 0, 0), ((-576 * log 2 - 1728), 0, 2, 1, 1, 0, 1), (2880, 0, 2, 1, 2, 0, 1),
    (864, 0, 2, 2, 0, 0, 0), (-216, 0, 2, 2, 0, 1, 0), (864, 0, 2, 2, 1, 0, 1),
    ((324 * log 2 + 456), 0, 3, 0, 0, 0, 0), ((-36 * log 2 - 108), 0, 3, 0, 0, 1, 0),
    (-444, 0, 3, 0, 1, 0, 0), ((384 * log 2), 0, 3, 0, 1, 0, 1), (-384, 0, 3, 0, 2, 0, 1),
    (-384, 0, 3, 1, 0, 0, 0), (96, 0, 3, 1, 0, 1, 0), (-384, 0, 3, 1, 1, 0, 1)]

/-- The atoms of `B` at `0`. (part 3) -/
noncomputable def i12TV4Z_3 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(15, 0, 4, 0, 0, 0, 0), (-15, 0, 4, 0, 0, 1, 0),
    ((-1008 * log 2 ^ 2 - 720 * log 2 - 8064), 1, 0, 0, 1, 0, 0),
    ((-96 * log 2 ^ 3 + 1008 * log 2 ^ 2 - 1152 * log 2 + 4320), 1, 0, 0, 1, 0, 1),
    ((1296 * log 2 + 6984), 1, 0, 0, 2, 0, 0),
    ((-1008 * log 2 ^ 2 - 288 * log 2 - 6912), 1, 0, 0, 2, 0, 1), (-3264, 1, 0, 0, 3, 0, 0),
    ((1296 * log 2 + 6192), 1, 0, 0, 3, 0, 1), (-3264, 1, 0, 0, 4, 0, 1),
    ((-288 * log 2 ^ 2 - 2088 * log 2 - 4752), 1, 0, 1, 0, 0, 0),
    ((72 * log 2 ^ 2 + 432 * log 2 + 1008), 1, 0, 1, 0, 1, 0),
    ((2592 * log 2 + 8100), 1, 0, 1, 1, 0, 0),
    ((-288 * log 2 ^ 2 - 1440 * log 2 - 2880), 1, 0, 1, 1, 0, 1), (-5904, 1, 0, 1, 2, 0, 0),
    ((2592 * log 2 + 6624), 1, 0, 1, 2, 0, 1), (-5904, 1, 0, 1, 3, 0, 1),
    ((864 * log 2 + 3132), 1, 0, 2, 0, 0, 0), ((-216 * log 2 - 648), 1, 0, 2, 0, 1, 0),
    (-3888, 1, 0, 2, 1, 0, 0), ((864 * log 2 + 2160), 1, 0, 2, 1, 0, 1),
    (-3888, 1, 0, 2, 2, 0, 1), (-864, 1, 0, 3, 0, 0, 0), (216, 1, 0, 3, 0, 1, 0),
    (-864, 1, 0, 3, 1, 0, 1), ((720 * log 2 ^ 2 - 936 * log 2 + 4464), 1, 1, 0, 0, 0, 0),
    ((-72 * log 2 ^ 2 - 432 * log 2 - 1008), 1, 1, 0, 0, 1, 0), (-6660, 1, 1, 0, 1, 0, 0),
    ((720 * log 2 ^ 2 - 1152 * log 2 + 4032), 1, 1, 0, 1, 0, 1), (3888, 1, 1, 0, 2, 0, 0),
    (-5760, 1, 1, 0, 2, 0, 1), (3888, 1, 1, 0, 3, 0, 1),
    ((-864 * log 2 - 3312), 1, 1, 1, 0, 0, 0), ((216 * log 2 + 576), 1, 1, 1, 0, 1, 0),
    (4032, 1, 1, 1, 1, 0, 0), ((-864 * log 2 - 2304), 1, 1, 1, 1, 0, 1), (4032, 1, 1, 1, 2, 0, 1),
    (1296, 1, 1, 2, 0, 0, 0), (-324, 1, 1, 2, 0, 1, 0), (1296, 1, 1, 2, 1, 0, 1),
    ((-432 * log 2 + 2124), 1, 2, 0, 0, 0, 0)]

/-- The atoms of `B` at `0`. (part 4) -/
noncomputable def i12TV4Z_4 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(72, 1, 2, 0, 0, 1, 0), (-1872, 1, 2, 0, 1, 0, 0), ((-432 * log 2 + 1728), 1, 2, 0, 1, 0, 1),
    (-1872, 1, 2, 0, 2, 0, 1), (-720, 1, 2, 1, 0, 0, 0), (180, 1, 2, 1, 0, 1, 0),
    (-720, 1, 2, 1, 1, 0, 1), (384, 1, 3, 0, 0, 0, 0), (-72, 1, 3, 0, 0, 1, 0),
    (384, 1, 3, 0, 1, 0, 1), ((-1296 * log 2 - 1368), 2, 0, 0, 1, 0, 0),
    ((1008 * log 2 - 144), 2, 0, 0, 1, 0, 1), (1440, 2, 0, 0, 2, 0, 0),
    ((-1296 * log 2 - 1008), 2, 0, 0, 2, 0, 1), (1440, 2, 0, 0, 3, 0, 1),
    ((-576 * log 2 - 1908), 2, 0, 1, 0, 0, 0), ((144 * log 2 + 432), 2, 0, 1, 0, 1, 0),
    (2448, 2, 0, 1, 1, 0, 0), ((-576 * log 2 - 1296), 2, 0, 1, 1, 0, 1), (2448, 2, 0, 1, 2, 0, 1),
    (864, 2, 0, 2, 0, 0, 0), (-216, 2, 0, 2, 0, 1, 0), (864, 2, 0, 2, 1, 0, 1),
    ((720 * log 2 - 180), 2, 1, 0, 0, 0, 0), ((-144 * log 2 - 432), 2, 1, 0, 0, 1, 0),
    (-432, 2, 1, 0, 1, 0, 0), ((720 * log 2 - 288), 2, 1, 0, 1, 0, 1), (-432, 2, 1, 0, 2, 0, 1),
    (-720, 2, 1, 1, 0, 0, 0), (180, 2, 1, 1, 0, 1, 0), (-720, 2, 1, 1, 1, 0, 1),
    (-144, 2, 2, 0, 0, 0, 0), (36, 2, 2, 0, 0, 1, 0), (-144, 2, 2, 0, 1, 0, 1),
    (-672, 3, 0, 0, 1, 0, 0), ((96 * log 2 + 432), 3, 0, 0, 1, 0, 1), (-672, 3, 0, 0, 2, 0, 1),
    (-384, 3, 0, 1, 0, 0, 0), (96, 3, 0, 1, 0, 1, 0), (-384, 3, 0, 1, 1, 0, 1)]

/-- The atoms of `B` at `0`. (part 5) -/
noncomputable def i12TV4Z_5 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(288, 3, 1, 0, 0, 0, 0), (-96, 3, 1, 0, 0, 1, 0), (288, 3, 1, 0, 1, 0, 1),
    (60, 4, 0, 0, 1, 0, 1)]

/-- The atoms of `B` at `0`. -/
noncomputable def i12TV4Z : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  i12TV4Z_1 ++ i12TV4Z_2 ++ i12TV4Z_3 ++ i12TV4Z_4 ++ i12TV4Z_5

/-- The atoms of `B` at `1`. (part 1) -/
noncomputable def i12TV4O_1 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((-120 * log 2 ^ 3 + 1080 * log 2 ^ 2 - 288 * log 2 + 4968), 0, 0, 0, 1, 0, 0),
    ((-15 * log 2 ^ 4 + 108 * log 2 ^ 3 - 252 * log 2 ^ 2 + 1080 * log 2), 0, 0, 0, 1, 0, 1),
    ((18 * log 2 ^ 2 - 1098 * log 2 - 567), 0, 0, 0, 2, 0, 0),
    ((-24 * log 2 ^ 3 - 504 * log 2 - 540), 0, 0, 0, 2, 0, 1),
    ((63 * log 2 + 2103 / 4), 0, 0, 0, 3, 0, 0),
    ((18 * log 2 ^ 2 + 162 * log 2 + 315), 0, 0, 0, 3, 0, 1), ((-705 / 16), 0, 0, 0, 4, 0, 0),
    ((-33 * log 2 - 189 / 2), 0, 0, 0, 4, 0, 1), ((255 / 16), 0, 0, 0, 5, 0, 1),
    ((-96 * log 2 ^ 3 + 720 * log 2 ^ 2 - 1296 * log 2 + 936), 0, 0, 1, 0, 0, 0),
    ((384 * log 2 ^ 3 - 1728 * log 2 ^ 2 + 4032 * log 2 - 4320), 0, 0, 1, 0, 1, 0),
    ((-72 * log 2 ^ 2 + 288 * log 2 - 360), 0, 0, 1, 1, 0, 0),
    ((-96 * log 2 ^ 3 + 432 * log 2 ^ 2 - 1008 * log 2 + 1080), 0, 0, 1, 1, 0, 1),
    ((-18 * log 2 + 33), 0, 0, 1, 2, 0, 0),
    ((-72 * log 2 ^ 2 + 216 * log 2 - 252), 0, 0, 1, 2, 0, 1), ((-3 / 2), 0, 0, 1, 3, 0, 0),
    ((-18 * log 2 + 27), 0, 0, 1, 3, 0, 1), ((-3 / 2), 0, 0, 1, 4, 0, 1),
    ((-216 * log 2 ^ 2 + 1080 * log 2 - 972), 0, 0, 2, 0, 0, 0),
    ((864 * log 2 ^ 2 - 2592 * log 2 + 3024), 0, 0, 2, 0, 1, 0),
    ((-108 * log 2 + 216), 0, 0, 2, 1, 0, 0),
    ((-216 * log 2 ^ 2 + 648 * log 2 - 756), 0, 0, 2, 1, 0, 1), ((-27 / 2), 0, 0, 2, 2, 0, 0),
    ((-108 * log 2 + 162), 0, 0, 2, 2, 0, 1), ((-27 / 2), 0, 0, 2, 3, 0, 1),
    ((-216 * log 2 + 540), 0, 0, 3, 0, 0, 0), ((864 * log 2 - 1296), 0, 0, 3, 0, 1, 0),
    (-54, 0, 0, 3, 1, 0, 0), ((-216 * log 2 + 324), 0, 0, 3, 1, 0, 1), (-54, 0, 0, 3, 2, 0, 1),
    (-81, 0, 0, 4, 0, 0, 0), (324, 0, 0, 4, 0, 1, 0), (-81, 0, 0, 4, 1, 0, 1),
    ((168 * log 2 ^ 3 - 1368 * log 2 ^ 2 + 432 * log 2 - 4608), 0, 1, 0, 0, 0, 0),
    ((-384 * log 2 ^ 3 + 1728 * log 2 ^ 2 - 4032 * log 2 + 4320), 0, 1, 0, 0, 1, 0),
    ((2016 * log 2 + 1476), 0, 1, 0, 1, 0, 0),
    ((72 * log 2 ^ 3 - 216 * log 2 ^ 2 + 1008 * log 2), 0, 1, 0, 1, 0, 1),
    ((-180 * log 2 - 1590), 0, 1, 0, 2, 0, 0), ((-432 * log 2 - 504), 0, 1, 0, 2, 0, 1),
    (177, 0, 1, 0, 3, 0, 0)]

/-- The atoms of `B` at `1`. (part 2) -/
noncomputable def i12TV4O_2 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((108 * log 2 + 270), 0, 1, 0, 3, 0, 1), (-63, 0, 1, 0, 4, 0, 1),
    ((288 * log 2 ^ 2 - 1440 * log 2 + 1440), 0, 1, 1, 0, 0, 0),
    ((-1152 * log 2 ^ 2 + 2880 * log 2 - 2880), 0, 1, 1, 0, 1, 0),
    ((144 * log 2 - 288), 0, 1, 1, 1, 0, 0),
    ((288 * log 2 ^ 2 - 864 * log 2 + 1008), 0, 1, 1, 1, 0, 1), (18, 0, 1, 1, 2, 0, 0),
    ((144 * log 2 - 216), 0, 1, 1, 2, 0, 1), (18, 0, 1, 1, 3, 0, 1),
    ((432 * log 2 - 1080), 0, 1, 2, 0, 0, 0), ((-1728 * log 2 + 2160), 0, 1, 2, 0, 1, 0),
    (108, 0, 1, 2, 1, 0, 0), ((432 * log 2 - 648), 0, 1, 2, 1, 0, 1), (108, 0, 1, 2, 2, 0, 1),
    (216, 0, 1, 3, 0, 0, 0), (-864, 0, 1, 3, 0, 1, 0), (216, 0, 1, 3, 1, 0, 1),
    ((-72 * log 2 ^ 2 - 576 * log 2 - 1368), 0, 2, 0, 0, 0, 0),
    ((288 * log 2 ^ 2 - 288 * log 2 - 144), 0, 2, 0, 0, 1, 0),
    ((144 * log 2 + 1656), 0, 2, 0, 1, 0, 0), ((-72 * log 2 ^ 2 + 432 * log 2), 0, 2, 0, 1, 0, 1),
    (-270, 0, 2, 0, 2, 0, 0), ((-144 * log 2 - 216), 0, 2, 0, 2, 0, 1), (90, 0, 2, 0, 3, 0, 1),
    ((-288 * log 2 + 720), 0, 2, 1, 0, 0, 0), ((1152 * log 2 - 1296), 0, 2, 1, 0, 1, 0),
    (-72, 0, 2, 1, 1, 0, 0), ((-288 * log 2 + 432), 0, 2, 1, 1, 0, 1), (-72, 0, 2, 1, 2, 0, 1),
    (-216, 0, 2, 2, 0, 0, 0), (864, 0, 2, 2, 0, 1, 0), (-216, 0, 2, 2, 1, 0, 1),
    (-672, 0, 3, 0, 0, 0, 0), ((-288 * log 2 + 432), 0, 3, 0, 0, 1, 0), (192, 0, 3, 0, 1, 0, 0),
    ((96 * log 2), 0, 3, 0, 1, 0, 1), (-48, 0, 3, 0, 2, 0, 1), (96, 0, 3, 1, 0, 0, 0),
    (-384, 0, 3, 1, 0, 1, 0), (96, 0, 3, 1, 1, 0, 1)]

/-- The atoms of `B` at `1`. (part 3) -/
noncomputable def i12TV4O_3 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(-60, 0, 4, 0, 0, 0, 0), (60, 0, 4, 0, 0, 1, 0),
    ((36 * log 2 ^ 2 + 648 * log 2 - 144), 1, 0, 0, 1, 0, 0),
    ((60 * log 2 ^ 3 - 288 * log 2 ^ 2 + 216 * log 2 - 1080), 1, 0, 0, 1, 0, 1),
    ((-72 * log 2 - 423), 1, 0, 0, 2, 0, 0),
    ((36 * log 2 ^ 2 + 216 * log 2 + 648), 1, 0, 0, 2, 0, 1), (60, 1, 0, 0, 3, 0, 0),
    ((-72 * log 2 - 279), 1, 0, 0, 3, 0, 1), (60, 1, 0, 0, 4, 0, 1),
    ((288 * log 2 ^ 2 - 720 * log 2 + 432), 1, 0, 1, 0, 0, 0),
    ((-1152 * log 2 ^ 2 + 3456 * log 2 - 4032), 1, 0, 1, 0, 1, 0), (-108, 1, 0, 1, 1, 0, 0),
    ((288 * log 2 ^ 2 - 720 * log 2 + 720), 1, 0, 1, 1, 0, 1), (18, 1, 0, 1, 2, 0, 0),
    (-36, 1, 0, 1, 2, 0, 1), (18, 1, 0, 1, 3, 0, 1), ((432 * log 2 - 540), 1, 0, 2, 0, 0, 0),
    ((-1728 * log 2 + 2592), 1, 0, 2, 0, 1, 0), ((432 * log 2 - 540), 1, 0, 2, 1, 0, 1),
    (216, 1, 0, 3, 0, 0, 0), (-864, 1, 0, 3, 0, 1, 0), (216, 1, 0, 3, 1, 0, 1),
    ((-180 * log 2 ^ 2 - 720 * log 2 + 720), 1, 1, 0, 0, 0, 0),
    ((1152 * log 2 ^ 2 - 3456 * log 2 + 4032), 1, 1, 0, 0, 1, 0),
    ((144 * log 2 + 1044), 1, 1, 0, 1, 0, 0),
    ((-180 * log 2 ^ 2 + 144 * log 2 - 1008), 1, 1, 0, 1, 0, 1), (-189, 1, 1, 0, 2, 0, 0),
    ((144 * log 2 + 576), 1, 1, 0, 2, 0, 1), (-189, 1, 1, 0, 3, 0, 1),
    ((-432 * log 2 + 720), 1, 1, 1, 0, 0, 0), ((1728 * log 2 - 2304), 1, 1, 1, 0, 1, 0),
    (-36, 1, 1, 1, 1, 0, 0), ((-432 * log 2 + 576), 1, 1, 1, 1, 0, 1), (-36, 1, 1, 1, 2, 0, 1),
    (-324, 1, 1, 2, 0, 0, 0), (1296, 1, 1, 2, 0, 1, 0), (-324, 1, 1, 2, 1, 0, 1),
    ((36 * log 2 - 936), 1, 2, 0, 0, 0, 0), (-288, 1, 2, 0, 0, 1, 0), (198, 1, 2, 0, 1, 0, 0)]

/-- The atoms of `B` at `1`. (part 4) -/
noncomputable def i12TV4O_4 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((36 * log 2 - 432), 1, 2, 0, 1, 0, 1), (198, 1, 2, 0, 2, 0, 1), (180, 1, 2, 1, 0, 0, 0),
    (-720, 1, 2, 1, 0, 1, 0), (180, 1, 2, 1, 1, 0, 1), (-96, 1, 3, 0, 0, 0, 0),
    (288, 1, 3, 0, 0, 1, 0), (-96, 1, 3, 0, 1, 0, 1), ((-36 * log 2 - 522), 2, 0, 0, 1, 0, 0),
    ((-90 * log 2 ^ 2 + 288 * log 2 + 36), 2, 0, 0, 1, 0, 1), (72, 2, 0, 0, 2, 0, 0),
    ((-36 * log 2 - 234), 2, 0, 0, 2, 0, 1), (72, 2, 0, 0, 3, 0, 1),
    ((-288 * log 2 + 180), 2, 0, 1, 0, 0, 0), ((1152 * log 2 - 1728), 2, 0, 1, 0, 1, 0),
    (36, 2, 0, 1, 1, 0, 0), ((-288 * log 2 + 324), 2, 0, 1, 1, 0, 1), (36, 2, 0, 1, 2, 0, 1),
    (-216, 2, 0, 2, 0, 0, 0), (864, 2, 0, 2, 0, 1, 0), (-216, 2, 0, 2, 1, 0, 1),
    ((180 * log 2 + 720), 2, 1, 0, 0, 0, 0), ((-1152 * log 2 + 1728), 2, 1, 0, 0, 1, 0),
    (-162, 2, 1, 0, 1, 0, 0), ((180 * log 2 + 72), 2, 1, 0, 1, 0, 1), (-162, 2, 1, 0, 2, 0, 1),
    (180, 2, 1, 1, 0, 0, 0), (-720, 2, 1, 1, 0, 1, 0), (180, 2, 1, 1, 1, 0, 1),
    (36, 2, 2, 0, 0, 0, 0), (-144, 2, 2, 0, 0, 1, 0), (36, 2, 2, 0, 1, 0, 1),
    (24, 3, 0, 0, 1, 0, 0), ((60 * log 2 - 108), 3, 0, 0, 1, 0, 1), (24, 3, 0, 0, 2, 0, 1),
    (96, 3, 0, 1, 0, 0, 0), (-384, 3, 0, 1, 0, 1, 0), (96, 3, 0, 1, 1, 0, 1),
    (-72, 3, 1, 0, 0, 0, 0), (384, 3, 1, 0, 0, 1, 0)]

/-- The atoms of `B` at `1`. (part 5) -/
noncomputable def i12TV4O_5 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(-72, 3, 1, 0, 1, 0, 1), (-15, 4, 0, 0, 1, 0, 1)]

/-- The atoms of `B` at `1`. -/
noncomputable def i12TV4O : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  i12TV4O_1 ++ i12TV4O_2 ++ i12TV4O_3 ++ i12TV4O_4 ++ i12TV4O_5

theorem i12TV4B_eq_zero {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    i12TV4B s = -60 * log 2 ^ 4 + 456 * log 2 ^ 3 - 792 * log 2 ^ 2 + 5328 * log 2 + 2160 +
      i12TVZs i12TV4Z s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  rw [← mul_left_inj' (mul_ne_zero (pow_ne_zero 1 hs0) (pow_ne_zero 1 h1s)), add_mul,
    i12TVZs_mul 1 1 _ hs0 h1s (by decide +kernel), i12TV4B]
  field_simp
  simp only [i12TVZsNum, i12TVPoly, i12TVMono, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.map_append, List.sum_append,
    i12TV4Q0, i12TV4Q1, i12TV4Q2, i12TV4Z_1, i12TV4Z_2, i12TV4Z_3, i12TV4Z_4, i12TV4Z_5, i12TV4Z,
    Nat.reduceSub, pow_zero, pow_one, mul_one, one_mul]
  ring

/-- The atoms at `1` of the part 0 of `B`. -/
noncomputable def i12TV4O0 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((-96 * log 2 ^ 3 + 1152 * log 2 ^ 2 - 288 * log 2 + 6336), 0, 0, 0, 1, 0, 0),
    ((-1296 * log 2 - 720), 0, 0, 0, 2, 0, 0), ((96 * log 2 + 624), 0, 0, 0, 3, 0, 0),
    (-60, 0, 0, 0, 4, 0, 0),
    ((96 * log 2 ^ 3 - 1152 * log 2 ^ 2 + 288 * log 2 - 6336), 0, 1, 0, 0, 0, 0),
    ((2592 * log 2 + 1440), 0, 1, 0, 1, 0, 0), ((-288 * log 2 - 1872), 0, 1, 0, 2, 0, 0),
    (240, 0, 1, 0, 3, 0, 0), ((-1296 * log 2 - 720), 0, 2, 0, 0, 0, 0),
    ((288 * log 2 + 1872), 0, 2, 0, 1, 0, 0), (-360, 0, 2, 0, 2, 0, 0),
    ((-96 * log 2 - 624), 0, 3, 0, 0, 0, 0), (240, 0, 3, 0, 1, 0, 0), (-60, 0, 4, 0, 0, 0, 0),
    ((-60 * log 2 ^ 3 + 864 * log 2 ^ 2 - 1944 * log 2 + 3096), 1, 0, 0, 0, 0, 0),
    ((90 * log 2 ^ 2 - 864 * log 2 + 828), 2, 0, 0, 0, 0, 0),
    ((-60 * log 2 + 300), 3, 0, 0, 0, 0, 0), (15, 4, 0, 0, 0, 0, 0)]

theorem i12TV4B0_eq_one {{s : ℝ}} (hs : s ∈ Ioo (0 : ℝ) 1) :
    i12TVPoly i12TV4Q0 s = 0 +
      i12TVOs i12TV4O0 s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  simp only [i12TVOs, i12TVPoly, i12TVO, i12TVMono, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil,
    i12TV4Q0, i12TV4O0]
  field_simp
  ring

/-- The atoms at `1` of the part 1 of `B`. (part 1) -/
noncomputable def i12TV4O1_1 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((-24 * log 2 ^ 3 - 504 * log 2 - 540), 0, 0, 0, 1, 0, 0),
    ((-15 * log 2 ^ 4 + 108 * log 2 ^ 3 - 252 * log 2 ^ 2 + 1080 * log 2), 0, 0, 0, 1, 0, 1),
    ((18 * log 2 ^ 2 + 162 * log 2 + 315), 0, 0, 0, 2, 0, 0),
    ((-24 * log 2 ^ 3 - 504 * log 2 - 540), 0, 0, 0, 2, 0, 1),
    ((-33 * log 2 - 189 / 2), 0, 0, 0, 3, 0, 0),
    ((18 * log 2 ^ 2 + 162 * log 2 + 315), 0, 0, 0, 3, 0, 1), ((255 / 16), 0, 0, 0, 4, 0, 0),
    ((-33 * log 2 - 189 / 2), 0, 0, 0, 4, 0, 1), ((255 / 16), 0, 0, 0, 5, 0, 1),
    ((-96 * log 2 ^ 3 + 432 * log 2 ^ 2 - 1008 * log 2 + 1080), 0, 0, 1, 0, 0, 0),
    ((-72 * log 2 ^ 2 + 216 * log 2 - 252), 0, 0, 1, 1, 0, 0),
    ((-96 * log 2 ^ 3 + 432 * log 2 ^ 2 - 1008 * log 2 + 1080), 0, 0, 1, 1, 0, 1),
    ((-18 * log 2 + 27), 0, 0, 1, 2, 0, 0),
    ((-72 * log 2 ^ 2 + 216 * log 2 - 252), 0, 0, 1, 2, 0, 1), ((-3 / 2), 0, 0, 1, 3, 0, 0),
    ((-18 * log 2 + 27), 0, 0, 1, 3, 0, 1), ((-3 / 2), 0, 0, 1, 4, 0, 1),
    ((-216 * log 2 ^ 2 + 648 * log 2 - 756), 0, 0, 2, 0, 0, 0),
    ((-108 * log 2 + 162), 0, 0, 2, 1, 0, 0),
    ((-216 * log 2 ^ 2 + 648 * log 2 - 756), 0, 0, 2, 1, 0, 1), ((-27 / 2), 0, 0, 2, 2, 0, 0),
    ((-108 * log 2 + 162), 0, 0, 2, 2, 0, 1), ((-27 / 2), 0, 0, 2, 3, 0, 1),
    ((-216 * log 2 + 324), 0, 0, 3, 0, 0, 0), (-54, 0, 0, 3, 1, 0, 0),
    ((-216 * log 2 + 324), 0, 0, 3, 1, 0, 1), (-54, 0, 0, 3, 2, 0, 1), (-81, 0, 0, 4, 0, 0, 0),
    (-81, 0, 0, 4, 1, 0, 1),
    ((72 * log 2 ^ 3 - 216 * log 2 ^ 2 + 1008 * log 2), 0, 1, 0, 0, 0, 0),
    ((-432 * log 2 - 504), 0, 1, 0, 1, 0, 0),
    ((72 * log 2 ^ 3 - 216 * log 2 ^ 2 + 1008 * log 2), 0, 1, 0, 1, 0, 1),
    ((108 * log 2 + 270), 0, 1, 0, 2, 0, 0), ((-432 * log 2 - 504), 0, 1, 0, 2, 0, 1),
    (-63, 0, 1, 0, 3, 0, 0), ((108 * log 2 + 270), 0, 1, 0, 3, 0, 1), (-63, 0, 1, 0, 4, 0, 1),
    ((288 * log 2 ^ 2 - 864 * log 2 + 1008), 0, 1, 1, 0, 0, 0),
    ((144 * log 2 - 216), 0, 1, 1, 1, 0, 0),
    ((288 * log 2 ^ 2 - 864 * log 2 + 1008), 0, 1, 1, 1, 0, 1)]

/-- The atoms at `1` of the part 1 of `B`. (part 2) -/
noncomputable def i12TV4O1_2 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(18, 0, 1, 1, 2, 0, 0), ((144 * log 2 - 216), 0, 1, 1, 2, 0, 1), (18, 0, 1, 1, 3, 0, 1),
    ((432 * log 2 - 648), 0, 1, 2, 0, 0, 0), (108, 0, 1, 2, 1, 0, 0),
    ((432 * log 2 - 648), 0, 1, 2, 1, 0, 1), (108, 0, 1, 2, 2, 0, 1), (216, 0, 1, 3, 0, 0, 0),
    (216, 0, 1, 3, 1, 0, 1), ((-72 * log 2 ^ 2 + 432 * log 2), 0, 2, 0, 0, 0, 0),
    ((-144 * log 2 - 216), 0, 2, 0, 1, 0, 0), ((-72 * log 2 ^ 2 + 432 * log 2), 0, 2, 0, 1, 0, 1),
    (90, 0, 2, 0, 2, 0, 0), ((-144 * log 2 - 216), 0, 2, 0, 2, 0, 1), (90, 0, 2, 0, 3, 0, 1),
    ((-288 * log 2 + 432), 0, 2, 1, 0, 0, 0), (-72, 0, 2, 1, 1, 0, 0),
    ((-288 * log 2 + 432), 0, 2, 1, 1, 0, 1), (-72, 0, 2, 1, 2, 0, 1), (-216, 0, 2, 2, 0, 0, 0),
    (-216, 0, 2, 2, 1, 0, 1), ((96 * log 2), 0, 3, 0, 0, 0, 0), (-48, 0, 3, 0, 1, 0, 0),
    ((96 * log 2), 0, 3, 0, 1, 0, 1), (-48, 0, 3, 0, 2, 0, 1), (96, 0, 3, 1, 0, 0, 0),
    (96, 0, 3, 1, 1, 0, 1),
    ((60 * log 2 ^ 3 - 288 * log 2 ^ 2 + 216 * log 2 - 1080), 1, 0, 0, 0, 0, 0),
    ((36 * log 2 ^ 2 + 216 * log 2 + 648), 1, 0, 0, 1, 0, 0),
    ((60 * log 2 ^ 3 - 288 * log 2 ^ 2 + 216 * log 2 - 1080), 1, 0, 0, 1, 0, 1),
    ((-72 * log 2 - 279), 1, 0, 0, 2, 0, 0),
    ((36 * log 2 ^ 2 + 216 * log 2 + 648), 1, 0, 0, 2, 0, 1), (60, 1, 0, 0, 3, 0, 0),
    ((-72 * log 2 - 279), 1, 0, 0, 3, 0, 1), (60, 1, 0, 0, 4, 0, 1),
    ((288 * log 2 ^ 2 - 720 * log 2 + 720), 1, 0, 1, 0, 0, 0), (-36, 1, 0, 1, 1, 0, 0),
    ((288 * log 2 ^ 2 - 720 * log 2 + 720), 1, 0, 1, 1, 0, 1), (18, 1, 0, 1, 2, 0, 0),
    (-36, 1, 0, 1, 2, 0, 1)]

/-- The atoms at `1` of the part 1 of `B`. (part 3) -/
noncomputable def i12TV4O1_3 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(18, 1, 0, 1, 3, 0, 1), ((432 * log 2 - 540), 1, 0, 2, 0, 0, 0),
    ((432 * log 2 - 540), 1, 0, 2, 1, 0, 1), (216, 1, 0, 3, 0, 0, 0), (216, 1, 0, 3, 1, 0, 1),
    ((-180 * log 2 ^ 2 + 144 * log 2 - 1008), 1, 1, 0, 0, 0, 0),
    ((144 * log 2 + 576), 1, 1, 0, 1, 0, 0),
    ((-180 * log 2 ^ 2 + 144 * log 2 - 1008), 1, 1, 0, 1, 0, 1), (-189, 1, 1, 0, 2, 0, 0),
    ((144 * log 2 + 576), 1, 1, 0, 2, 0, 1), (-189, 1, 1, 0, 3, 0, 1),
    ((-432 * log 2 + 576), 1, 1, 1, 0, 0, 0), (-36, 1, 1, 1, 1, 0, 0),
    ((-432 * log 2 + 576), 1, 1, 1, 1, 0, 1), (-36, 1, 1, 1, 2, 0, 1), (-324, 1, 1, 2, 0, 0, 0),
    (-324, 1, 1, 2, 1, 0, 1), ((36 * log 2 - 432), 1, 2, 0, 0, 0, 0), (198, 1, 2, 0, 1, 0, 0),
    ((36 * log 2 - 432), 1, 2, 0, 1, 0, 1), (198, 1, 2, 0, 2, 0, 1), (180, 1, 2, 1, 0, 0, 0),
    (180, 1, 2, 1, 1, 0, 1), (-96, 1, 3, 0, 0, 0, 0), (-96, 1, 3, 0, 1, 0, 1),
    ((-90 * log 2 ^ 2 + 288 * log 2 + 36), 2, 0, 0, 0, 0, 0),
    ((-36 * log 2 - 234), 2, 0, 0, 1, 0, 0),
    ((-90 * log 2 ^ 2 + 288 * log 2 + 36), 2, 0, 0, 1, 0, 1), (72, 2, 0, 0, 2, 0, 0),
    ((-36 * log 2 - 234), 2, 0, 0, 2, 0, 1), (72, 2, 0, 0, 3, 0, 1),
    ((-288 * log 2 + 324), 2, 0, 1, 0, 0, 0), (36, 2, 0, 1, 1, 0, 0),
    ((-288 * log 2 + 324), 2, 0, 1, 1, 0, 1), (36, 2, 0, 1, 2, 0, 1), (-216, 2, 0, 2, 0, 0, 0),
    (-216, 2, 0, 2, 1, 0, 1), ((180 * log 2 + 72), 2, 1, 0, 0, 0, 0), (-162, 2, 1, 0, 1, 0, 0),
    ((180 * log 2 + 72), 2, 1, 0, 1, 0, 1)]

/-- The atoms at `1` of the part 1 of `B`. (part 4) -/
noncomputable def i12TV4O1_4 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(-162, 2, 1, 0, 2, 0, 1), (180, 2, 1, 1, 0, 0, 0), (180, 2, 1, 1, 1, 0, 1),
    (36, 2, 2, 0, 0, 0, 0), (36, 2, 2, 0, 1, 0, 1), ((60 * log 2 - 108), 3, 0, 0, 0, 0, 0),
    (24, 3, 0, 0, 1, 0, 0), ((60 * log 2 - 108), 3, 0, 0, 1, 0, 1), (24, 3, 0, 0, 2, 0, 1),
    (96, 3, 0, 1, 0, 0, 0), (96, 3, 0, 1, 1, 0, 1), (-72, 3, 1, 0, 0, 0, 0),
    (-72, 3, 1, 0, 1, 0, 1), (-15, 4, 0, 0, 0, 0, 0), (-15, 4, 0, 0, 1, 0, 1)]

/-- The atoms at `1` of the part 1 of `B`. -/
noncomputable def i12TV4O1 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  i12TV4O1_1 ++ i12TV4O1_2 ++ i12TV4O1_3 ++ i12TV4O1_4

theorem i12TV4B1_eq_one {{s : ℝ}} (hs : s ∈ Ioo (0 : ℝ) 1) :
    i12TVPoly i12TV4Q1 s / s = -15 * log 2 ^ 4 + 108 * log 2 ^ 3 - 252 * log 2 ^ 2 + 1080 * log 2 +
      i12TVOs i12TV4O1 s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  rw [← mul_left_inj' (mul_ne_zero (pow_ne_zero 1 h1s) (pow_ne_zero 1 hs0)), add_mul,
    i12TVOs_mul 1 1 _ hs0 h1s (by decide +kernel)]
  field_simp
  simp only [i12TVOsNum, i12TVPoly, i12TVMono, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.map_append, List.sum_append,
    i12TV4Q1, i12TV4O1_1, i12TV4O1_2, i12TV4O1_3, i12TV4O1_4, i12TV4O1,
    Nat.reduceSub, pow_zero, pow_one, mul_one, one_mul]
  ring

/-- The atoms at `1` of the part 2 of `B`. (part 1) -/
noncomputable def i12TV4O2_1 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((-72 * log 2 ^ 2 + 504 * log 2 - 828), 0, 0, 0, 1, 0, 0),
    ((36 * log 2 - 162), 0, 0, 0, 2, 0, 0), ((-15 / 4), 0, 0, 0, 3, 0, 0),
    ((288 * log 2 ^ 2 - 288 * log 2 - 144), 0, 0, 1, 0, 0, 0),
    ((384 * log 2 ^ 3 - 1728 * log 2 ^ 2 + 4032 * log 2 - 4320), 0, 0, 1, 0, 1, 0),
    ((72 * log 2 - 108), 0, 0, 1, 1, 0, 0), (6, 0, 0, 1, 2, 0, 0),
    ((432 * log 2 - 216), 0, 0, 2, 0, 0, 0),
    ((864 * log 2 ^ 2 - 2592 * log 2 + 3024), 0, 0, 2, 0, 1, 0), (54, 0, 0, 2, 1, 0, 0),
    (216, 0, 0, 3, 0, 0, 0), ((864 * log 2 - 1296), 0, 0, 3, 0, 1, 0), (324, 0, 0, 4, 0, 1, 0),
    ((-864 * log 2 + 1728), 0, 1, 0, 0, 0, 0),
    ((-384 * log 2 ^ 3 + 1728 * log 2 ^ 2 - 4032 * log 2 + 4320), 0, 1, 0, 0, 1, 0),
    ((-144 * log 2 + 540), 0, 1, 0, 1, 0, 0), (12, 0, 1, 0, 2, 0, 0),
    ((-576 * log 2 + 432), 0, 1, 1, 0, 0, 0),
    ((-1152 * log 2 ^ 2 + 2880 * log 2 - 2880), 0, 1, 1, 0, 1, 0), (-72, 0, 1, 1, 1, 0, 0),
    (-432, 0, 1, 2, 0, 0, 0), ((-1728 * log 2 + 2160), 0, 1, 2, 0, 1, 0),
    (-864, 0, 1, 3, 0, 1, 0), ((288 * log 2 - 648), 0, 2, 0, 0, 0, 0),
    ((288 * log 2 ^ 2 - 288 * log 2 - 144), 0, 2, 0, 0, 1, 0), (288, 0, 2, 1, 0, 0, 0),
    ((1152 * log 2 - 1296), 0, 2, 1, 0, 1, 0), (864, 0, 2, 2, 0, 1, 0), (-48, 0, 3, 0, 0, 0, 0),
    ((-288 * log 2 + 432), 0, 3, 0, 0, 1, 0), (-384, 0, 3, 1, 0, 1, 0), (60, 0, 4, 0, 0, 1, 0),
    ((-576 * log 2 ^ 2 + 1728 * log 2 - 2016), 1, 0, 0, 0, 0, 0),
    ((432 * log 2 - 792), 1, 0, 0, 1, 0, 0), (-144, 1, 0, 0, 2, 0, 0), (-288, 1, 0, 1, 0, 0, 0),
    ((-1152 * log 2 ^ 2 + 3456 * log 2 - 4032), 1, 0, 1, 0, 1, 0), (-72, 1, 0, 1, 1, 0, 0),
    ((-1728 * log 2 + 2592), 1, 0, 2, 0, 1, 0), (-864, 1, 0, 3, 0, 1, 0)]

/-- The atoms at `1` of the part 2 of `B`. (part 2) -/
noncomputable def i12TV4O2_2 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((-864 * log 2 + 1728), 1, 1, 0, 0, 0, 0),
    ((1152 * log 2 ^ 2 - 3456 * log 2 + 4032), 1, 1, 0, 0, 1, 0), (468, 1, 1, 0, 1, 0, 0),
    (144, 1, 1, 1, 0, 0, 0), ((1728 * log 2 - 2304), 1, 1, 1, 0, 1, 0), (1296, 1, 1, 2, 0, 1, 0),
    (-504, 1, 2, 0, 0, 0, 0), (-288, 1, 2, 0, 0, 1, 0), (-720, 1, 2, 1, 0, 1, 0),
    (288, 1, 3, 0, 0, 1, 0), ((576 * log 2 - 864), 2, 0, 0, 0, 0, 0), (-288, 2, 0, 0, 1, 0, 0),
    (-144, 2, 0, 1, 0, 0, 0), ((1152 * log 2 - 1728), 2, 0, 1, 0, 1, 0), (864, 2, 0, 2, 0, 1, 0),
    (648, 2, 1, 0, 0, 0, 0), ((-1152 * log 2 + 1728), 2, 1, 0, 0, 1, 0), (-720, 2, 1, 1, 0, 1, 0),
    (-144, 2, 2, 0, 0, 1, 0), (-192, 3, 0, 0, 0, 0, 0), (-384, 3, 0, 1, 0, 1, 0),
    (384, 3, 1, 0, 0, 1, 0)]

/-- The atoms at `1` of the part 2 of `B`. -/
noncomputable def i12TV4O2 : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  i12TV4O2_1 ++ i12TV4O2_2

theorem i12TV4B2_eq_one {{s : ℝ}} (hs : s ∈ Ioo (0 : ℝ) 1) :
    i12TVPoly i12TV4Q2 s / (1 - s) = 192 * log 2 ^ 3 - 864 * log 2 ^ 2 + 2016 * log 2 - 2160 +
      i12TVOs i12TV4O2 s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  rw [← mul_left_inj' (mul_ne_zero (pow_ne_zero 1 h1s) (pow_ne_zero 1 hs0)), add_mul,
    i12TVOs_mul 1 1 _ hs0 h1s (by decide +kernel)]
  field_simp
  simp only [i12TVOsNum, i12TVPoly, i12TVMono, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.map_append, List.sum_append,
    i12TV4Q2, i12TV4O2_1, i12TV4O2_2, i12TV4O2,
    Nat.reduceSub, pow_zero, pow_one, mul_one, one_mul]
  ring

theorem i12TV4B_eq_one {{s : ℝ}} (hs : s ∈ Ioo (0 : ℝ) 1) :
    i12TV4B s = -15 * log 2 ^ 4 + 300 * log 2 ^ 3 - 1116 * log 2 ^ 2 + 3096 * log 2 - 2160 +
      i12TVOs i12TV4O s := by
  rw [i12TV4B, i12TV4B0_eq_one hs, i12TV4B1_eq_one hs, i12TV4B2_eq_one hs]
  simp only [i12TVOs, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.map_append, List.sum_append,
    i12TV4O0, i12TV4O1_1, i12TV4O1_2, i12TV4O1_3, i12TV4O1_4, i12TV4O1, i12TV4O2_1, i12TV4O2_2,
    i12TV4O2, i12TV4O_1, i12TV4O_2, i12TV4O_3, i12TV4O_4, i12TV4O_5, i12TV4O]
  ring

theorem tendsto_i12TV4B_zero :
    Tendsto i12TV4B (𝓝[>] 0)
      (𝓝 (-60 * log 2 ^ 4 + 456 * log 2 ^ 3 - 792 * log 2 ^ 2 + 5328 * log 2 + 2160)) := by
  have h := (tendsto_const_nhds (x := (
    -60 * log 2 ^ 4 + 456 * log 2 ^ 3 - 792 * log 2 ^ 2 + 5328 * log 2 + 2160 : ℝ))).add
    (tendsto_i12TVZs i12TV4Z (by decide +kernel))
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs
  exact (i12TV4B_eq_zero hs).symm

theorem tendsto_i12TV4B_one :
    Tendsto i12TV4B (𝓝[<] 1)
      (𝓝 (-15 * log 2 ^ 4 + 300 * log 2 ^ 3 - 1116 * log 2 ^ 2 + 3096 * log 2 - 2160)) := by
  have h := (tendsto_const_nhds (x := (
    -15 * log 2 ^ 4 + 300 * log 2 ^ 3 - 1116 * log 2 ^ 2 + 3096 * log 2 - 2160 : ℝ))).add
    (tendsto_i12TVOs i12TV4O (by decide +kernel))
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with s hs
  exact (i12TV4B_eq_one hs).symm

/-! ### The values at `1` -/

/-- `Ψ₀[P₀](1)`. -/
theorem i12TV4_val_P0 :
    i12TVPsi zero i12TV4P0 1 =
      -189 / 5 * π ^ 4 * log 2 + 137 / 5 * π ^ 4 - 498 * π ^ 2 * zeta3 - 48 * π ^ 2 * log 2 ^ 3
      - 126 * π ^ 2 * log 2 ^ 2 + 60 * π ^ 2 * log 2 + 1158 * π ^ 2 - 36 * zeta3 * log 2 ^ 2
      + 3096 * zeta3 * log 2 - 9774 * zeta3 + 6948 * zeta5 + 228 / 5 * log 2 ^ 5 + 267 * log 2 ^ 4
      + 2304 * log 2 * Li 4 (1 / 2) + 6408 * Li 4 (1 / 2) + 6048 * Li 5 (1 / 2) := by
  simp only [i12TVPsi, i12TV4P0, i12TVH, i12TVws, i12TVsh, List.replicate, shuffle_cons_cons,
    shuffle_nil_left, shuffle_nil_right, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
  simp only [
    hpl_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_negOne_negOne_at_one,
    hpl_zero_negOne_negOne_negOne_negOne_at_one, hpl_zero_negOne_negOne_negOne_one_at_one,
    hpl_zero_negOne_negOne_negOne_zero_at_one, hpl_zero_negOne_negOne_one_at_one,
    hpl_zero_negOne_negOne_one_negOne_at_one, hpl_zero_negOne_negOne_one_one_at_one,
    hpl_zero_negOne_negOne_one_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_negOne_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_one_at_one,
    hpl_zero_negOne_negOne_zero_zero_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_negOne_one_negOne_at_one, hpl_zero_negOne_one_negOne_negOne_at_one,
    hpl_zero_negOne_one_negOne_one_at_one, hpl_zero_negOne_one_negOne_zero_at_one,
    hpl_zero_negOne_one_one_at_one, hpl_zero_negOne_one_one_negOne_at_one,
    hpl_zero_negOne_one_one_one_at_one, hpl_zero_negOne_one_one_zero_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_negOne_one_zero_negOne_at_one,
    hpl_zero_negOne_one_zero_one_at_one, hpl_zero_negOne_one_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_negOne_one_at_one,
    hpl_zero_negOne_zero_negOne_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_zero_one_negOne_at_one, hpl_zero_negOne_zero_one_one_at_one,
    hpl_zero_negOne_zero_one_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_negOne_at_one, hpl_zero_negOne_zero_zero_one_at_one,
    hpl_zero_negOne_zero_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_negOne_negOne_at_one, hpl_zero_one_negOne_negOne_negOne_at_one,
    hpl_zero_one_negOne_negOne_one_at_one, hpl_zero_one_negOne_negOne_zero_at_one,
    hpl_zero_one_negOne_one_at_one, hpl_zero_one_negOne_one_negOne_at_one,
    hpl_zero_one_negOne_one_one_at_one, hpl_zero_one_negOne_one_zero_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_negOne_zero_negOne_at_one,
    hpl_zero_one_negOne_zero_one_at_one, hpl_zero_one_negOne_zero_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_one_one_negOne_at_one,
    hpl_zero_one_one_negOne_negOne_at_one, hpl_zero_one_one_negOne_one_at_one,
    hpl_zero_one_one_negOne_zero_at_one, hpl_zero_one_one_one_at_one,
    hpl_zero_one_one_one_negOne_at_one, hpl_zero_one_one_one_one_at_one,
    hpl_zero_one_one_one_zero_at_one, hpl_zero_one_one_zero_at_one,
    hpl_zero_one_one_zero_negOne_at_one, hpl_zero_one_one_zero_one_at_one,
    hpl_zero_one_one_zero_zero_at_one, hpl_zero_one_zero_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_one_zero_negOne_negOne_at_one, hpl_zero_one_zero_negOne_one_at_one,
    hpl_zero_one_zero_negOne_zero_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_zero_one_negOne_at_one, hpl_zero_one_zero_one_one_at_one,
    hpl_zero_one_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_one_zero_zero_negOne_at_one, hpl_zero_one_zero_zero_one_at_one,
    hpl_zero_one_zero_zero_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_negOne_negOne_at_one,
    hpl_zero_zero_negOne_negOne_one_at_one, hpl_zero_zero_negOne_negOne_zero_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_negOne_one_negOne_at_one,
    hpl_zero_zero_negOne_one_one_at_one, hpl_zero_zero_negOne_one_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_negOne_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_one_at_one, hpl_zero_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_zero_one_negOne_negOne_at_one, hpl_zero_zero_one_negOne_one_at_one,
    hpl_zero_zero_one_negOne_zero_at_one, hpl_zero_zero_one_one_at_one,
    hpl_zero_zero_one_one_negOne_at_one, hpl_zero_zero_one_one_one_at_one,
    hpl_zero_zero_one_one_zero_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_negOne_at_one, hpl_zero_zero_one_zero_one_at_one,
    hpl_zero_zero_one_zero_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_negOne_negOne_at_one, hpl_zero_zero_zero_negOne_one_at_one,
    hpl_zero_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_zero_one_negOne_at_one, hpl_zero_zero_zero_one_one_at_one,
    hpl_zero_zero_zero_one_zero_at_one, hpl_zero_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_zero_one_at_one]
  ring

/-- `Ψ₋₁[P₋₁](1)`. -/
theorem i12TV4_val_Pm :
    i12TVPsi negOne i12TV4Pm 1 =
      201 / 10 * π ^ 4 + 351 * π ^ 2 * log 2 ^ 2 - 324 * π ^ 2 * log 2 - 432 * π ^ 2
      - 3240 * zeta3 * log 2 + 4401 * zeta3 - 486 * log 2 ^ 4 - 288 * log 2 ^ 3 + 612 * log 2 ^ 2
      + 864 * log 2 * Li 3 (1 / 2) + 3240 * log 2 - 8424 * Li 4 (1 / 2) + 2376 * Li 3 (1 / 2) := by
  simp only [i12TVPsi, i12TV4Pm, i12TVH, i12TVws, i12TVsh, List.replicate, shuffle_cons_cons,
    shuffle_nil_left, shuffle_nil_right, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
  simp only [
    hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_negOne_negOne_negOne_at_one,
    hpl_negOne_negOne_negOne_negOne_at_one, hpl_negOne_negOne_negOne_one_at_one,
    hpl_negOne_negOne_negOne_zero_at_one, hpl_negOne_negOne_one_at_one,
    hpl_negOne_negOne_one_negOne_at_one, hpl_negOne_negOne_one_one_at_one,
    hpl_negOne_negOne_one_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_zero_negOne_at_one, hpl_negOne_negOne_zero_one_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_one_at_one, hpl_negOne_one_negOne_at_one,
    hpl_negOne_one_negOne_negOne_at_one, hpl_negOne_one_negOne_one_at_one,
    hpl_negOne_one_negOne_zero_at_one, hpl_negOne_one_one_at_one,
    hpl_negOne_one_one_negOne_at_one, hpl_negOne_one_one_one_at_one,
    hpl_negOne_one_one_zero_at_one, hpl_negOne_one_zero_at_one,
    hpl_negOne_one_zero_negOne_at_one, hpl_negOne_one_zero_one_at_one,
    hpl_negOne_one_zero_zero_at_one, hpl_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_negOne_zero_negOne_negOne_at_one, hpl_negOne_zero_negOne_one_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_zero_one_negOne_at_one, hpl_negOne_zero_one_one_at_one,
    hpl_negOne_zero_one_zero_at_one, hpl_negOne_zero_zero_at_one,
    hpl_negOne_zero_zero_negOne_at_one, hpl_negOne_zero_zero_one_at_one,
    hpl_negOne_zero_zero_zero_at_one]
  ring

/-- `Ψ₀[P₁](1)`. -/
theorem i12TV4_val_P1z :
    i12TVPsi zero i12TV4P1 1 =
      -3 * π ^ 4 * log 2 + 17 / 20 * π ^ 4 - 282 * π ^ 2 * zeta3 + 72 * π ^ 2 * log 2 ^ 2
      - 198 * π ^ 2 * log 2 - 240 * π ^ 2 + 252 * zeta3 * log 2 ^ 2 - 1377 * zeta3 * log 2
      + 2475 * zeta3 + 5922 * zeta5 - 39 * log 2 ^ 4 - 936 * Li 4 (1 / 2) := by
  simp only [i12TVPsi, i12TV4P1, i12TVH, i12TVws, i12TVsh, List.replicate, shuffle_cons_cons,
    shuffle_nil_left, shuffle_nil_right, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
  simp only [
    hpl_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_negOne_negOne_at_one,
    hpl_zero_negOne_negOne_negOne_zero_at_one, hpl_zero_negOne_negOne_one_at_one,
    hpl_zero_negOne_negOne_one_zero_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_negOne_zero_negOne_at_one, hpl_zero_negOne_negOne_zero_one_at_one,
    hpl_zero_negOne_negOne_zero_zero_at_one, hpl_zero_negOne_one_at_one,
    hpl_zero_negOne_one_negOne_at_one, hpl_zero_negOne_one_negOne_zero_at_one,
    hpl_zero_negOne_one_one_at_one, hpl_zero_negOne_one_one_zero_at_one,
    hpl_zero_negOne_one_zero_at_one, hpl_zero_negOne_one_zero_negOne_at_one,
    hpl_zero_negOne_one_zero_one_at_one, hpl_zero_negOne_one_zero_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_negOne_negOne_at_one, hpl_zero_negOne_zero_negOne_one_at_one,
    hpl_zero_negOne_zero_negOne_zero_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_zero_one_negOne_at_one, hpl_zero_negOne_zero_one_one_at_one,
    hpl_zero_negOne_zero_one_zero_at_one, hpl_zero_negOne_zero_zero_at_one,
    hpl_zero_negOne_zero_zero_negOne_at_one, hpl_zero_negOne_zero_zero_one_at_one,
    hpl_zero_negOne_zero_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_negOne_negOne_at_one, hpl_zero_one_negOne_negOne_zero_at_one,
    hpl_zero_one_negOne_one_at_one, hpl_zero_one_negOne_one_zero_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_negOne_zero_negOne_at_one,
    hpl_zero_one_negOne_zero_one_at_one, hpl_zero_one_negOne_zero_zero_at_one,
    hpl_zero_one_one_at_one, hpl_zero_one_one_negOne_at_one, hpl_zero_one_one_negOne_zero_at_one,
    hpl_zero_one_one_one_at_one, hpl_zero_one_one_one_one_at_one,
    hpl_zero_one_one_one_zero_at_one, hpl_zero_one_one_zero_at_one,
    hpl_zero_one_one_zero_negOne_at_one, hpl_zero_one_one_zero_one_at_one,
    hpl_zero_one_one_zero_zero_at_one, hpl_zero_one_zero_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_one_zero_negOne_negOne_at_one, hpl_zero_one_zero_negOne_one_at_one,
    hpl_zero_one_zero_negOne_zero_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_zero_one_negOne_at_one, hpl_zero_one_zero_one_one_at_one,
    hpl_zero_one_zero_one_zero_at_one, hpl_zero_one_zero_zero_at_one,
    hpl_zero_one_zero_zero_negOne_at_one, hpl_zero_one_zero_zero_one_at_one,
    hpl_zero_one_zero_zero_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_negOne_negOne_at_one,
    hpl_zero_zero_negOne_negOne_one_at_one, hpl_zero_zero_negOne_negOne_zero_at_one,
    hpl_zero_zero_negOne_one_at_one, hpl_zero_zero_negOne_one_negOne_at_one,
    hpl_zero_zero_negOne_one_one_at_one, hpl_zero_zero_negOne_one_zero_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_negOne_zero_negOne_at_one,
    hpl_zero_zero_negOne_zero_one_at_one, hpl_zero_zero_negOne_zero_zero_at_one,
    hpl_zero_zero_one_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_zero_one_negOne_negOne_at_one, hpl_zero_zero_one_negOne_one_at_one,
    hpl_zero_zero_one_negOne_zero_at_one, hpl_zero_zero_one_one_at_one,
    hpl_zero_zero_one_one_negOne_at_one, hpl_zero_zero_one_one_one_at_one,
    hpl_zero_zero_one_one_zero_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_zero_one_zero_negOne_at_one, hpl_zero_zero_one_zero_one_at_one,
    hpl_zero_zero_one_zero_zero_at_one, hpl_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_negOne_negOne_at_one, hpl_zero_zero_zero_negOne_one_at_one,
    hpl_zero_zero_zero_negOne_zero_at_one, hpl_zero_zero_zero_one_at_one,
    hpl_zero_zero_zero_one_negOne_at_one, hpl_zero_zero_zero_one_one_at_one,
    hpl_zero_zero_zero_one_zero_at_one, hpl_zero_zero_zero_zero_negOne_at_one,
    hpl_zero_zero_zero_zero_one_at_one]
  ring

/-- `Ψ₋₁[P₁](1)`. -/
theorem i12TV4_val_P1m :
    i12TVPsi negOne i12TV4P1 1 =
      -339 / 5 * π ^ 4 * log 2 + 191 / 10 * π ^ 4 - 294 * π ^ 2 * zeta3 - 76 * π ^ 2 * log 2 ^ 3
      + 78 * π ^ 2 * log 2 ^ 2 - 480 * π ^ 2 * log 2 - 72 * π ^ 2 + 252 * zeta3 * log 2 ^ 2
      - 648 * zeta3 * log 2 + 3141 * zeta3 + 3780 * zeta5 + 168 / 5 * log 2 ^ 5 - 39 * log 2 ^ 4
      + 384 * log 2 ^ 3 - 144 * log 2 ^ 2 + 2304 * log 2 * Li 4 (1 / 2)
      - 648 * log 2 * Li 3 (1 / 2) - 2952 * Li 4 (1 / 2) + 6048 * Li 5 (1 / 2)
      - 1440 * Li 3 (1 / 2) := by
  simp only [i12TVPsi, i12TV4P1, i12TVH, i12TVws, i12TVsh, List.replicate, shuffle_cons_cons,
    shuffle_nil_left, shuffle_nil_right, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
  simp only [
    hpl_negOne_negOne_at_one, hpl_negOne_negOne_negOne_at_one,
    hpl_negOne_negOne_negOne_negOne_at_one, hpl_negOne_negOne_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_negOne_one_at_one, hpl_negOne_negOne_negOne_one_zero_at_one,
    hpl_negOne_negOne_negOne_zero_at_one, hpl_negOne_negOne_negOne_zero_negOne_at_one,
    hpl_negOne_negOne_negOne_zero_one_at_one, hpl_negOne_negOne_negOne_zero_zero_at_one,
    hpl_negOne_negOne_one_at_one, hpl_negOne_negOne_one_negOne_at_one,
    hpl_negOne_negOne_one_negOne_zero_at_one, hpl_negOne_negOne_one_one_at_one,
    hpl_negOne_negOne_one_one_zero_at_one, hpl_negOne_negOne_one_zero_at_one,
    hpl_negOne_negOne_one_zero_negOne_at_one, hpl_negOne_negOne_one_zero_one_at_one,
    hpl_negOne_negOne_one_zero_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_zero_negOne_at_one, hpl_negOne_negOne_zero_negOne_negOne_at_one,
    hpl_negOne_negOne_zero_negOne_one_at_one, hpl_negOne_negOne_zero_negOne_zero_at_one,
    hpl_negOne_negOne_zero_one_at_one, hpl_negOne_negOne_zero_one_negOne_at_one,
    hpl_negOne_negOne_zero_one_one_at_one, hpl_negOne_negOne_zero_one_zero_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_negOne_zero_zero_negOne_at_one,
    hpl_negOne_negOne_zero_zero_one_at_one, hpl_negOne_negOne_zero_zero_zero_at_one,
    hpl_negOne_one_at_one, hpl_negOne_one_negOne_at_one, hpl_negOne_one_negOne_negOne_at_one,
    hpl_negOne_one_negOne_negOne_zero_at_one, hpl_negOne_one_negOne_one_at_one,
    hpl_negOne_one_negOne_one_zero_at_one, hpl_negOne_one_negOne_zero_at_one,
    hpl_negOne_one_negOne_zero_negOne_at_one, hpl_negOne_one_negOne_zero_one_at_one,
    hpl_negOne_one_negOne_zero_zero_at_one, hpl_negOne_one_one_at_one,
    hpl_negOne_one_one_negOne_at_one, hpl_negOne_one_one_negOne_zero_at_one,
    hpl_negOne_one_one_one_at_one, hpl_negOne_one_one_one_one_at_one,
    hpl_negOne_one_one_one_zero_at_one, hpl_negOne_one_one_zero_at_one,
    hpl_negOne_one_one_zero_negOne_at_one, hpl_negOne_one_one_zero_one_at_one,
    hpl_negOne_one_one_zero_zero_at_one, hpl_negOne_one_zero_at_one,
    hpl_negOne_one_zero_negOne_at_one, hpl_negOne_one_zero_negOne_negOne_at_one,
    hpl_negOne_one_zero_negOne_one_at_one, hpl_negOne_one_zero_negOne_zero_at_one,
    hpl_negOne_one_zero_one_at_one, hpl_negOne_one_zero_one_negOne_at_one,
    hpl_negOne_one_zero_one_one_at_one, hpl_negOne_one_zero_one_zero_at_one,
    hpl_negOne_one_zero_zero_at_one, hpl_negOne_one_zero_zero_negOne_at_one,
    hpl_negOne_one_zero_zero_one_at_one, hpl_negOne_one_zero_zero_zero_at_one,
    hpl_negOne_zero_negOne_at_one, hpl_negOne_zero_negOne_negOne_at_one,
    hpl_negOne_zero_negOne_negOne_negOne_at_one, hpl_negOne_zero_negOne_negOne_one_at_one,
    hpl_negOne_zero_negOne_negOne_zero_at_one, hpl_negOne_zero_negOne_one_at_one,
    hpl_negOne_zero_negOne_one_negOne_at_one, hpl_negOne_zero_negOne_one_one_at_one,
    hpl_negOne_zero_negOne_one_zero_at_one, hpl_negOne_zero_negOne_zero_at_one,
    hpl_negOne_zero_negOne_zero_negOne_at_one, hpl_negOne_zero_negOne_zero_one_at_one,
    hpl_negOne_zero_negOne_zero_zero_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_zero_one_negOne_at_one, hpl_negOne_zero_one_negOne_negOne_at_one,
    hpl_negOne_zero_one_negOne_one_at_one, hpl_negOne_zero_one_negOne_zero_at_one,
    hpl_negOne_zero_one_one_at_one, hpl_negOne_zero_one_one_negOne_at_one,
    hpl_negOne_zero_one_one_one_at_one, hpl_negOne_zero_one_one_zero_at_one,
    hpl_negOne_zero_one_zero_at_one, hpl_negOne_zero_one_zero_negOne_at_one,
    hpl_negOne_zero_one_zero_one_at_one, hpl_negOne_zero_one_zero_zero_at_one,
    hpl_negOne_zero_zero_negOne_at_one, hpl_negOne_zero_zero_negOne_negOne_at_one,
    hpl_negOne_zero_zero_negOne_one_at_one, hpl_negOne_zero_zero_negOne_zero_at_one,
    hpl_negOne_zero_zero_one_at_one, hpl_negOne_zero_zero_one_negOne_at_one,
    hpl_negOne_zero_zero_one_one_at_one, hpl_negOne_zero_zero_one_zero_at_one,
    hpl_negOne_zero_zero_zero_negOne_at_one, hpl_negOne_zero_zero_zero_one_at_one]
  ring

/-! ### The value -/

/-- **`∫₀¹ J_4 = 24 T_4`.** -/
theorem integral_i12TJ_four :
    ∫ s in Ioo (0 : ℝ) 1, i12TJ 4 s =
      24 * (9 / 8 * π ^ 4 * log 2 + 39 / 32 * π ^ 4 - 81 / 4 * π ^ 2 * zeta3
      + 7 / 6 * π ^ 2 * log 2 ^ 3 + 31 / 8 * π ^ 2 * log 2 ^ 2 - 25 / 2 * π ^ 2 * log 2
      + 93 / 4 * π ^ 2 - 3 / 2 * zeta3 * log 2 ^ 2 + 75 / 4 * zeta3 * log 2 - 225 / 2 * zeta3
      + 1515 / 4 * zeta5 + 1 / 2 * log 2 ^ 5 + 13 / 4 * log 2 ^ 4 - 8 * log 2 ^ 3 + 18 * log 2 ^ 2
      + 42 * log 2 - 180) := by
  have h0 := ((tendsto_i12TV4B_zero.add (tendsto_i12TVPsi_zero (c := zero) (P := i12TV4P0)
    (by decide +kernel))).add (tendsto_i12TVPsi_zero (c := negOne) (P := i12TV4Pm)
    (by decide +kernel))).add (tendsto_i12TVMob_zero i12TV4P1)
  have h1 := ((tendsto_i12TV4B_one.add (tendsto_i12TVPsi_one (c := zero) (by decide) i12TV4P0)).add
    (tendsto_i12TVPsi_one (c := negOne) (by decide) i12TV4Pm)).add
    (tendsto_i12TVMob_one (P := i12TV4P1) (by decide +kernel))
  rw [i12TV_integral_eq (fun s hs => hasDerivAt_i12TV4Phi hs)
    (integral_i12TAd_add_integral_i12TBd 4).1 h0 h1, i12TV4_val_P0,
    i12TV4_val_Pm, i12TV4_val_P1z, i12TV4_val_P1m, Li_three_one_half]
  ring

/-- **`T_A⁽4⁾(0) + T_B⁽4⁾(0) = 24 T_4`.** -/
theorem iteratedDeriv_i12TA_add_i12TB_four :
    iteratedDeriv 4 i12TA 0 + iteratedDeriv 4 i12TB 0 =
      ((24 * (9 / 8 * π ^ 4 * log 2 + 39 / 32 * π ^ 4 - 81 / 4 * π ^ 2 * zeta3
        + 7 / 6 * π ^ 2 * log 2 ^ 3 + 31 / 8 * π ^ 2 * log 2 ^ 2 - 25 / 2 * π ^ 2 * log 2
        + 93 / 4 * π ^ 2 - 3 / 2 * zeta3 * log 2 ^ 2 + 75 / 4 * zeta3 * log 2 - 225 / 2 * zeta3
        + 1515 / 4 * zeta5 + 1 / 2 * log 2 ^ 5 + 13 / 4 * log 2 ^ 4 - 8 * log 2 ^ 3
        + 18 * log 2 ^ 2 + 42 * log 2 - 180) : ℝ) : ℂ) := by
  rw [iteratedDeriv_i12TA_add_i12TB_eq_integral_i12TJ, integral_i12TJ_four]

end QED.ThreeLoopD
