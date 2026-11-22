/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighTValGen
public import QED.ThreeLoopD.SetDMastersI12RHighTRed
import QED.Polylog.HPLValues
import QED.Polylog.HPLValues3
import QED.Polylog.HPLValues4
import QED.Polylog.HPLValuesAlt4
import QED.Polylog.HPLValuesTrailing
import QED.Polylog.LiHalf

/-!
# Set (d), master `I₁₂`: the face terms of order 3

`∫₀¹ J_3(s) ds = 6 T_3` (`QED.ThreeLoopD.integral_i12TJ_three`), hence the value of
`T_A⁽3⁾(0) + T_B⁽3⁾(0)` (`QED.ThreeLoopD.iteratedDeriv_i12TA_add_i12TB_three`).

## Proof

`J_3` has the explicit primitive

  `Φ(s) = B(s) + Ψ₀[P₀](s) + Ψ₋₁[P₋₁](s) + Ψ₋₁[P₁](φ(s)) - Ψ₀[P₁](φ(s))`,

`φ(s) = (1 - s)/(1 + s)`, where `B = Q₀ + Q₁/s + Q₂/(1 - s)` with `Q₀`, `Q₁`, `Q₂` polynomials in
`log s`, `log (1 - s)`, `log (1 + s)`, `log 2`, and `Ψ_c[P]` is the primitive of `f_c P` through
harmonic polylogarithms (`QED.ThreeLoopD.i12TVPsi`). The polynomials were found by integrating by
parts; `Φ' = J_3` is checked by `field_simp; ring` after the logarithms of `2s/(1 - s)`,
`(1 + s)/(1 - s)` and of `φ(s)`, `1 ∓ φ(s)` are expanded. At the endpoints, `B` is a constant
plus a combination of the atoms `QED.ThreeLoopD.i12TVZ` (at `0`) and `QED.ThreeLoopD.i12TVO`
(at `1`), which tend to `0`: the poles of `Q₁/s` and `Q₂/(1 - s)` cancel against the vanishing
combinations `log (1 - s) + s`, `log (1 + s) - s`, resp. `log s + (1 - s)`,
`log ((1 + s)/2) + (1 - s)/2`. The harmonic polylogarithm parts tend to `0` or to their values at
`1` (`H(c · w; 1)`, first letter `0` or `-1`), which are the library values
`QED.Polylog.HPL.hpl_zero_one_negOne_at_one` and its companions.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i12TV3Phi`: `Φ' = J_3` on `(0, 1)`.
* `QED.ThreeLoopD.integral_i12TJ_three`: `∫₀¹ J_3 = 6 T_3`.
* `QED.ThreeLoopD.iteratedDeriv_i12TA_add_i12TB_three`: `T_A⁽3⁾(0) + T_B⁽3⁾(0) = 6 T_3`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory
open QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### Logarithms of `k = 2s/(1 - s)` -/

theorem i12TV_log_one_add_i12Rk {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    log (1 + i12Rk s) = log (1 + s) - log (1 - s) := by
  have h1 : 0 < 1 - s := by linarith [hs.2]
  rw [show 1 + i12Rk s = (1 + s) / (1 - s) by unfold i12Rk; field_simp; ring,
    log_div (by linarith [hs.1]) h1.ne']

theorem i12TV_log_one_div_i12Rk {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    log (1 / i12Rk s) = -(log 2 + log s - log (1 - s)) := by
  rw [one_div, log_inv, i12_log_i12Rk hs]

theorem i12TV_log_one_add_one_div_i12Rk {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    log (1 + 1 / i12Rk s) = log (1 + s) - log 2 - log s := by
  have h1 : 0 < 1 - s := by linarith [hs.2]
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1' : 1 - s ≠ 0 := h1.ne'
  rw [show 1 + 1 / i12Rk s = (1 + s) / (2 * s) by unfold i12Rk; field_simp; ring,
    log_div (by linarith [hs.1]) (by linarith [hs.1]), log_mul (by norm_num) hs.1.ne']
  ring

/-! ### The primitive -/

/-- The polynomial part of `B`. -/
noncomputable def i12TV3Q0 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-27 * log 2 ^ 2 + 180 * log 2 - 342), 0, 1, 0), ((-27 * log 2 + 81), 0, 2, 0), (-9, 0, 3, 0),
    ((-72 * log 2 ^ 2 - 720), 1, 0, 0), ((-72 * log 2 - 108), 2, 0, 0), (-36, 3, 0, 0)]
/-- The `1/s` part of `B`. -/
noncomputable def i12TV3Q1 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((9 * log 2 ^ 2 + 54 * log 2 + 126), 0, 0, 1), ((-27 * log 2 - 81), 0, 0, 2), (27, 0, 0, 3),
    ((9 * log 2 ^ 2 + 54 * log 2 + 126), 0, 1, 0), ((-36 * log 2 - 90), 0, 1, 1), (54, 0, 1, 2),
    ((-9 * log 2 - 9), 0, 2, 0), (36, 0, 2, 1), (9, 0, 3, 0), ((36 * log 2 + 108), 1, 0, 1),
    (-54, 1, 0, 2), ((36 * log 2 + 108), 1, 1, 0), (-54, 1, 1, 1), (36, 2, 0, 1), (36, 2, 1, 0)]
/-- The `1/(1 - s)` part of `B`. -/
noncomputable def i12TV3Q2 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((36 * log 2 ^ 3 - 108 * log 2 ^ 2 + 504 * log 2), 0, 0, 0),
    ((-36 * log 2 ^ 2 - 216 * log 2 - 504), 0, 0, 1), ((108 * log 2 + 324), 0, 0, 2),
    (-108, 0, 0, 3), ((72 * log 2 ^ 2 - 432 * log 2), 0, 1, 0), ((144 * log 2 + 432), 0, 1, 1),
    (-216, 0, 1, 2), ((144 * log 2), 0, 2, 0), (-144, 0, 2, 1),
    ((72 * log 2 ^ 2 - 72 * log 2 + 504), 1, 0, 0), ((-144 * log 2 - 360), 1, 0, 1),
    (216, 1, 0, 2), ((72 * log 2 - 432), 1, 1, 0), (216, 1, 1, 1), (144, 1, 2, 0),
    ((72 * log 2 + 36), 2, 0, 0), (-144, 2, 0, 1), (36, 3, 0, 0)]
/-- The residue polynomial at `0`. -/
noncomputable def i12TV3P0 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-36 * log 2 ^ 2 + 162 * log 2 + 540), 0, 0, 1), ((108 * log 2 - 243), 0, 0, 2),
    (-108, 0, 0, 3), ((-18 * log 2 + 504), 0, 1, 0), ((144 * log 2 - 252), 0, 1, 1),
    (-216, 0, 1, 2), ((72 * log 2 - 117), 0, 2, 0), (-144, 0, 2, 1), (-36, 0, 3, 0),
    ((-144 * log 2 + 306), 1, 0, 1), (216, 1, 0, 2), ((-72 * log 2 + 54), 1, 1, 0),
    (216, 1, 1, 1), (36, 1, 2, 0), (-144, 2, 0, 1), (-108, 2, 1, 0)]
/-- The residue polynomial at `-1`. -/
noncomputable def i12TV3Pm : List (ℝ × ℕ × ℕ × ℕ) :=
  [((27 * log 2 ^ 2 + 162 * log 2 + 378), 0, 0, 0), ((-162 * log 2 - 486), 0, 0, 1),
    (243, 0, 0, 2), ((-108 * log 2 - 306), 0, 1, 0), (324, 0, 1, 1), (108, 0, 2, 0),
    ((108 * log 2 + 288), 1, 0, 0), (-324, 1, 0, 1), (-162, 1, 1, 0), (108, 2, 0, 0)]
/-- The residue polynomial at `1`, in the Möbius variable. -/
noncomputable def i12TV3P1 : List (ℝ × ℕ × ℕ × ℕ) :=
  [((-18 * log 2 - 90), 0, 0, 1), (36, 0, 0, 2), ((-90 * log 2 - 36), 0, 1, 0), (126, 0, 1, 1),
    (18, 0, 2, 0), (-36, 0, 3, 0), ((72 * log 2 - 36), 1, 0, 1), (-36, 1, 0, 2),
    ((72 * log 2 - 108), 1, 1, 0), (72, 1, 1, 1), (36, 1, 2, 0), (36, 2, 0, 1), (-108, 2, 1, 0)]

/-- The elementary part `B = Q₀ + Q₁/s + Q₂/(1 - s)` of the primitive. -/
noncomputable def i12TV3B (s : ℝ) : ℝ :=
  i12TVPoly i12TV3Q0 s + i12TVPoly i12TV3Q1 s / s + i12TVPoly i12TV3Q2 s / (1 - s)

/-- **The primitive `Φ` of `J_3`.** -/
noncomputable def i12TV3Phi (s : ℝ) : ℝ :=
  i12TV3B s + i12TVPsi zero i12TV3P0 s + i12TVPsi negOne i12TV3Pm s +
    (i12TVPsi negOne i12TV3P1 (mobMap s) - i12TVPsi zero i12TV3P1 (mobMap s))

/-- **`Φ' = J_3` on `(0, 1)`.** -/
theorem hasDerivAt_i12TV3Phi {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i12TV3Phi (i12TJ 3 s) s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  have h1s' : 1 + s ≠ 0 := by linarith [hs.1]
  have hB := ((hasDerivAt_i12TVPoly i12TV3Q0 hs).add
    ((hasDerivAt_i12TVPoly i12TV3Q1 hs).div (hasDerivAt_id' s) hs0)).add
    ((hasDerivAt_i12TVPoly i12TV3Q2 hs).div ((hasDerivAt_id' s).const_sub 1) h1s)
  have h := ((hB.add (hasDerivAt_i12TVPsi zero i12TV3P0 hs)).add
    (hasDerivAt_i12TVPsi negOne i12TV3Pm hs)).add (hasDerivAt_i12TVMob i12TV3P1 hs)
  convert h using 1
  · rfl
  simp only [i12TJ, i12TE, i12TeA, i12TeB, i12TPn, i12_log_i12Rk hs, i12TV_log_one_add_i12Rk hs,
    i12TV_log_one_div_i12Rk hs, i12TV_log_one_add_one_div_i12Rk hs]
  simp only [i12TVPoly, i12TVPolyD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    i12TVMono_mobMap _ _ _ hs, i12TV3Q0, i12TV3Q1, i12TV3Q2, i12TV3P0, i12TV3Pm, i12TV3P1]
  simp only [i12TVMono, kernel_zero, kernel_negOne, i12Rk, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_succ]
  field_simp
  ring

/-! ### The endpoint limits -/

/-- The atoms of `B` at `0`. -/
noncomputable def i12TV3Z : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((9 * log 2 ^ 2 - 540 * log 2 - 1026), 0, 0, 0, 1, 0, 0),
    ((36 * log 2 ^ 3 - 108 * log 2 ^ 2 + 504 * log 2), 0, 0, 0, 1, 0, 1),
    ((369 * log 2 + 963), 0, 0, 0, 2, 0, 0),
    ((36 * log 2 ^ 2 - 648 * log 2 - 504), 0, 0, 0, 2, 0, 1), (-477, 0, 0, 0, 3, 0, 0),
    ((396 * log 2 + 756), 0, 0, 0, 3, 0, 1), (-468, 0, 0, 0, 4, 0, 1),
    ((-36 * log 2 ^ 2 - 306 * log 2 - 756), 0, 0, 1, 0, 0, 0),
    ((9 * log 2 ^ 2 + 54 * log 2 + 126), 0, 0, 1, 0, 1, 0),
    ((360 * log 2 + 1305), 0, 0, 1, 1, 0, 0),
    ((-36 * log 2 ^ 2 - 216 * log 2 - 504), 0, 0, 1, 1, 0, 1), (-900, 0, 0, 1, 2, 0, 0),
    ((360 * log 2 + 1080), 0, 0, 1, 2, 0, 1), (-900, 0, 0, 1, 3, 0, 1),
    ((108 * log 2 + 459), 0, 0, 2, 0, 0, 0), ((-27 * log 2 - 81), 0, 0, 2, 0, 1, 0),
    (-540, 0, 0, 2, 1, 0, 0), ((108 * log 2 + 324), 0, 0, 2, 1, 0, 1), (-540, 0, 0, 2, 2, 0, 1),
    (-108, 0, 0, 3, 0, 0, 0), (27, 0, 0, 3, 0, 1, 0), (-108, 0, 0, 3, 1, 0, 1),
    ((-45 * log 2 ^ 2 + 306 * log 2 + 450), 0, 1, 0, 0, 0, 0),
    ((-9 * log 2 ^ 2 - 54 * log 2 - 126), 0, 1, 0, 0, 1, 0),
    ((-378 * log 2 - 747), 0, 1, 0, 1, 0, 0), ((-72 * log 2 ^ 2 + 432 * log 2), 0, 1, 0, 1, 0, 1),
    (531, 0, 1, 0, 2, 0, 0), ((-432 * log 2 - 432), 0, 1, 0, 2, 0, 1), (504, 0, 1, 0, 3, 0, 1),
    ((-144 * log 2 - 612), 0, 1, 1, 0, 0, 0), ((36 * log 2 + 90), 0, 1, 1, 0, 1, 0),
    (720, 0, 1, 1, 1, 0, 0), ((-144 * log 2 - 432), 0, 1, 1, 1, 0, 1), (720, 0, 1, 1, 2, 0, 1),
    (216, 0, 1, 2, 0, 0, 0), (-54, 0, 1, 2, 0, 1, 0), (216, 0, 1, 2, 1, 0, 1),
    ((117 * log 2 + 144), 0, 2, 0, 0, 0, 0), ((-9 * log 2 - 9), 0, 2, 0, 0, 1, 0),
    (-171, 0, 2, 0, 1, 0, 0), ((144 * log 2), 0, 2, 0, 1, 0, 1), (-144, 0, 2, 0, 2, 0, 1),
    (-144, 0, 2, 1, 0, 0, 0), (36, 0, 2, 1, 0, 1, 0), (-144, 0, 2, 1, 1, 0, 1),
    (9, 0, 3, 0, 0, 0, 0), (-9, 0, 3, 0, 0, 1, 0), ((-72 * log 2 - 900), 1, 0, 0, 1, 0, 0),
    ((72 * log 2 ^ 2 - 72 * log 2 + 504), 1, 0, 0, 1, 0, 1), (576, 1, 0, 0, 2, 0, 0),
    ((-72 * log 2 - 792), 1, 0, 0, 2, 0, 1), (576, 1, 0, 0, 3, 0, 1),
    ((-144 * log 2 - 522), 1, 0, 1, 0, 0, 0), ((36 * log 2 + 108), 1, 0, 1, 0, 1, 0),
    (648, 1, 0, 1, 1, 0, 0), ((-144 * log 2 - 360), 1, 0, 1, 1, 0, 1), (648, 1, 0, 1, 2, 0, 1),
    (216, 1, 0, 2, 0, 0, 0), (-54, 1, 0, 2, 0, 1, 0), (216, 1, 0, 2, 1, 0, 1),
    ((-72 * log 2 + 486), 1, 1, 0, 0, 0, 0), ((-36 * log 2 - 108), 1, 1, 0, 0, 1, 0),
    (-504, 1, 1, 0, 1, 0, 0), ((-72 * log 2 + 432), 1, 1, 0, 1, 0, 1), (-504, 1, 1, 0, 2, 0, 1),
    (-216, 1, 1, 1, 0, 0, 0), (54, 1, 1, 1, 0, 1, 0), (-216, 1, 1, 1, 1, 0, 1),
    (144, 1, 2, 0, 0, 0, 0), (144, 1, 2, 0, 1, 0, 1), (-144, 2, 0, 0, 1, 0, 0),
    ((72 * log 2 + 36), 2, 0, 0, 1, 0, 1), (-144, 2, 0, 0, 2, 0, 1), (-144, 2, 0, 1, 0, 0, 0),
    (36, 2, 0, 1, 0, 1, 0), (-144, 2, 0, 1, 1, 0, 1), (-36, 2, 1, 0, 0, 1, 0),
    (36, 3, 0, 0, 1, 0, 1)]

/-- The atoms of `B` at `1`. -/
noncomputable def i12TV3O : List (ℝ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [((72 * log 2 ^ 2 - 36 * log 2 + 594), 0, 0, 0, 1, 0, 0),
    ((9 * log 2 ^ 3 - 27 * log 2 ^ 2 + 126 * log 2), 0, 0, 0, 1, 0, 1),
    ((-117 / 2 * log 2 - 315 / 4), 0, 0, 0, 2, 0, 0), ((-54 * log 2 - 63), 0, 0, 0, 2, 0, 1),
    ((225 / 8), 0, 0, 0, 3, 0, 0), ((27 / 2 * log 2 + 135 / 4), 0, 0, 0, 3, 0, 1),
    ((-63 / 8), 0, 0, 0, 4, 0, 1), ((36 * log 2 ^ 2 - 180 * log 2 + 162), 0, 0, 1, 0, 0, 0),
    ((-144 * log 2 ^ 2 + 432 * log 2 - 504), 0, 0, 1, 0, 1, 0),
    ((18 * log 2 - 36), 0, 0, 1, 1, 0, 0),
    ((36 * log 2 ^ 2 - 108 * log 2 + 126), 0, 0, 1, 1, 0, 1), ((9 / 4), 0, 0, 1, 2, 0, 0),
    ((18 * log 2 - 27), 0, 0, 1, 2, 0, 1), ((9 / 4), 0, 0, 1, 3, 0, 1),
    ((54 * log 2 - 135), 0, 0, 2, 0, 0, 0), ((-216 * log 2 + 324), 0, 0, 2, 0, 1, 0),
    ((27 / 2), 0, 0, 2, 1, 0, 0), ((54 * log 2 - 81), 0, 0, 2, 1, 0, 1),
    ((27 / 2), 0, 0, 2, 2, 0, 1), (27, 0, 0, 3, 0, 0, 0), (-108, 0, 0, 3, 0, 1, 0),
    (27, 0, 0, 3, 1, 0, 1), ((-90 * log 2 ^ 2 + 108 * log 2 - 612), 0, 1, 0, 0, 0, 0),
    ((144 * log 2 ^ 2 - 432 * log 2 + 504), 0, 1, 0, 0, 1, 0),
    ((108 * log 2 + 180), 0, 1, 0, 1, 0, 0), ((-18 * log 2 ^ 2 + 108 * log 2), 0, 1, 0, 1, 0, 1),
    ((-171 / 2), 0, 1, 0, 2, 0, 0), ((-36 * log 2 - 54), 0, 1, 0, 2, 0, 1),
    ((45 / 2), 0, 1, 0, 3, 0, 1), ((-72 * log 2 + 180), 0, 1, 1, 0, 0, 0),
    ((288 * log 2 - 360), 0, 1, 1, 0, 1, 0), (-18, 0, 1, 1, 1, 0, 0),
    ((-72 * log 2 + 108), 0, 1, 1, 1, 0, 1), (-18, 0, 1, 1, 2, 0, 1), (-54, 0, 1, 2, 0, 0, 0),
    (216, 0, 1, 2, 0, 1, 0), (-54, 0, 1, 2, 1, 0, 1), ((-36 * log 2 - 144), 0, 2, 0, 0, 0, 0),
    ((-72 * log 2 + 36), 0, 2, 0, 0, 1, 0), (90, 0, 2, 0, 1, 0, 0),
    ((36 * log 2), 0, 2, 0, 1, 0, 1), (-18, 0, 2, 0, 2, 0, 1), (36, 0, 2, 1, 0, 0, 0),
    (-144, 0, 2, 1, 0, 1, 0), (36, 0, 2, 1, 1, 0, 1), (-36, 0, 3, 0, 0, 0, 0),
    (36, 0, 3, 0, 0, 1, 0), ((18 * log 2 + 9), 1, 0, 0, 1, 0, 0),
    ((-27 * log 2 ^ 2 + 36 * log 2 - 126), 1, 0, 0, 1, 0, 1), ((-45 / 2), 1, 0, 0, 2, 0, 0),
    ((18 * log 2 + 63), 1, 0, 0, 2, 0, 1), ((-45 / 2), 1, 0, 0, 3, 0, 1),
    ((-72 * log 2 + 90), 1, 0, 1, 0, 0, 0), ((288 * log 2 - 432), 1, 0, 1, 0, 1, 0),
    ((-72 * log 2 + 90), 1, 0, 1, 1, 0, 1), (-54, 1, 0, 2, 0, 0, 0), (216, 1, 0, 2, 0, 1, 0),
    (-54, 1, 0, 2, 1, 0, 1), ((18 * log 2), 1, 1, 0, 0, 0, 0),
    ((-288 * log 2 + 432), 1, 1, 0, 0, 1, 0), (45, 1, 1, 0, 1, 0, 0),
    ((18 * log 2 - 108), 1, 1, 0, 1, 0, 1), (45, 1, 1, 0, 2, 0, 1), (54, 1, 1, 1, 0, 0, 0),
    (-216, 1, 1, 1, 0, 1, 0), (54, 1, 1, 1, 1, 0, 1), (-36, 1, 2, 0, 0, 0, 0),
    (-36, 1, 2, 0, 1, 0, 1), (-18, 2, 0, 0, 1, 0, 0), ((27 * log 2 - 9), 2, 0, 0, 1, 0, 1),
    (-18, 2, 0, 0, 2, 0, 1), (36, 2, 0, 1, 0, 0, 0), (-144, 2, 0, 1, 0, 1, 0),
    (36, 2, 0, 1, 1, 0, 1), (144, 2, 1, 0, 0, 1, 0), (-9, 3, 0, 0, 1, 0, 1)]

theorem i12TV3B_eq_zero {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    i12TV3B s = 36 * log 2 ^ 3 - 90 * log 2 ^ 2 + 612 * log 2 + 252 + i12TVZs i12TV3Z s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  simp only [i12TV3B, i12TVZs, i12TV3Z, i12TVPoly, i12TV3Q0, i12TV3Q1, i12TV3Q2, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, i12TVZ, i12TVMono]
  field_simp
  ring

theorem i12TV3B_eq_one {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    i12TV3B s = 9 * log 2 ^ 3 - 99 * log 2 ^ 2 + 342 * log 2 - 252 + i12TVOs i12TV3O s := by
  have hs0 : s ≠ 0 := hs.1.ne'
  have h1s : 1 - s ≠ 0 := by linarith [hs.2]
  simp only [i12TV3B, i12TVOs, i12TV3O, i12TVPoly, i12TV3Q0, i12TV3Q1, i12TV3Q2, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, i12TVO, i12TVMono]
  field_simp
  ring

theorem tendsto_i12TV3B_zero :
    Tendsto i12TV3B (𝓝[>] 0) (𝓝 (36 * log 2 ^ 3 - 90 * log 2 ^ 2 + 612 * log 2 + 252)) := by
  have h := (tendsto_const_nhds (x := (
    36 * log 2 ^ 3 - 90 * log 2 ^ 2 + 612 * log 2 + 252 : ℝ))).add
    (tendsto_i12TVZs i12TV3Z (by decide +kernel))
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs
  exact (i12TV3B_eq_zero hs).symm

theorem tendsto_i12TV3B_one :
    Tendsto i12TV3B (𝓝[<] 1) (𝓝 (9 * log 2 ^ 3 - 99 * log 2 ^ 2 + 342 * log 2 - 252)) := by
  have h := (tendsto_const_nhds (x := (
    9 * log 2 ^ 3 - 99 * log 2 ^ 2 + 342 * log 2 - 252 : ℝ))).add
    (tendsto_i12TVOs i12TV3O (by decide +kernel))
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with s hs
  exact (i12TV3B_eq_one hs).symm

/-! ### The values at `1` -/

/-- `Ψ₀[P₀](1)`. -/
theorem i12TV3_val_P0 :
    i12TVPsi zero i12TV3P0 1 =
      -37 / 20 * π ^ 4 + 36 * π ^ 2 * log 2 ^ 2 + 21 / 2 * π ^ 2 * log 2 + 129 * π ^ 2
      - 378 * zeta3 * log 2 - 2943 / 4 * zeta3 - 39 * log 2 ^ 4 - 936 * Li 4 (1 / 2) := by
  simp only [i12TVPsi, i12TV3P0, i12TVH, i12TVws, i12TVsh, List.replicate, shuffle_cons_cons,
    shuffle_nil_left, shuffle_nil_right, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
  simp only [
    hpl_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_negOne_negOne_at_one,
    hpl_zero_negOne_negOne_one_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_negOne_one_negOne_at_one,
    hpl_zero_negOne_one_one_at_one, hpl_zero_negOne_one_zero_at_one,
    hpl_zero_negOne_zero_at_one, hpl_zero_negOne_zero_negOne_at_one,
    hpl_zero_negOne_zero_one_at_one, hpl_zero_negOne_zero_zero_at_one, hpl_zero_one_at_one,
    hpl_zero_one_negOne_at_one, hpl_zero_one_negOne_negOne_at_one,
    hpl_zero_one_negOne_one_at_one, hpl_zero_one_negOne_zero_at_one, hpl_zero_one_one_at_one,
    hpl_zero_one_one_negOne_at_one, hpl_zero_one_one_one_at_one, hpl_zero_one_one_zero_at_one,
    hpl_zero_one_zero_at_one, hpl_zero_one_zero_negOne_at_one, hpl_zero_one_zero_one_at_one,
    hpl_zero_one_zero_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_zero_one_one_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one, hpl_zero_zero_zero_one_at_one]
  ring

/-- `Ψ₋₁[P₋₁](1)`. -/
theorem i12TV3_val_Pm :
    i12TVPsi negOne i12TV3Pm 1 =
      -63 / 2 * π ^ 2 * log 2 - 99 / 2 * π ^ 2 + 1701 / 4 * zeta3 - 27 * log 2 ^ 3 + 72 * log 2 ^ 2
      + 378 * log 2 + 216 * Li 3 (1 / 2) := by
  simp only [i12TVPsi, i12TV3Pm, i12TVH, i12TVws, i12TVsh, List.replicate, shuffle_cons_cons,
    shuffle_nil_left, shuffle_nil_right, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
  simp only [
    hpl_negOne_at_one, hpl_negOne_negOne_at_one, hpl_negOne_negOne_negOne_at_one,
    hpl_negOne_negOne_one_at_one, hpl_negOne_negOne_zero_at_one, hpl_negOne_one_at_one,
    hpl_negOne_one_negOne_at_one, hpl_negOne_one_one_at_one, hpl_negOne_one_zero_at_one,
    hpl_negOne_zero_at_one, hpl_negOne_zero_negOne_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_zero_zero_at_one]
  ring

/-- `Ψ₀[P₁](1)`. -/
theorem i12TV3_val_P1z :
    i12TVPsi zero i12TV3P1 1 =
      -89 / 20 * π ^ 4 - 33 / 2 * π ^ 2 * log 2 - 27 / 2 * π ^ 2 - 126 * zeta3 * log 2
      + 1035 / 4 * zeta3 := by
  simp only [i12TVPsi, i12TV3P1, i12TVH, i12TVws, i12TVsh, List.replicate, shuffle_cons_cons,
    shuffle_nil_left, shuffle_nil_right, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
  simp only [
    hpl_zero_negOne_at_one, hpl_zero_negOne_negOne_at_one, hpl_zero_negOne_negOne_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_negOne_one_zero_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_negOne_zero_negOne_at_one, hpl_zero_negOne_zero_one_at_one,
    hpl_zero_negOne_zero_zero_at_one, hpl_zero_one_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_negOne_zero_at_one, hpl_zero_one_one_at_one, hpl_zero_one_one_one_at_one,
    hpl_zero_one_one_zero_at_one, hpl_zero_one_zero_at_one, hpl_zero_one_zero_negOne_at_one,
    hpl_zero_one_zero_one_at_one, hpl_zero_one_zero_zero_at_one, hpl_zero_zero_negOne_at_one,
    hpl_zero_zero_negOne_negOne_at_one, hpl_zero_zero_negOne_one_at_one,
    hpl_zero_zero_negOne_zero_at_one, hpl_zero_zero_one_at_one, hpl_zero_zero_one_negOne_at_one,
    hpl_zero_zero_one_one_at_one, hpl_zero_zero_one_zero_at_one,
    hpl_zero_zero_zero_negOne_at_one, hpl_zero_zero_zero_one_at_one]
  ring

/-- `Ψ₋₁[P₁](1)`. -/
theorem i12TV3_val_P1m :
    i12TVPsi negOne i12TV3P1 1 =
      16 / 5 * π ^ 4 + 48 * π ^ 2 * log 2 ^ 2 - 24 * π ^ 2 * log 2 - 3 * π ^ 2
      - 252 * zeta3 * log 2 + 657 / 4 * zeta3 - 30 * log 2 ^ 4 + 6 * log 2 ^ 3 - 27 * log 2 ^ 2
      - 936 * Li 4 (1 / 2) + 36 * Li 3 (1 / 2) := by
  simp only [i12TVPsi, i12TV3P1, i12TVH, i12TVws, i12TVsh, List.replicate, shuffle_cons_cons,
    shuffle_nil_left, shuffle_nil_right, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
  simp only [
    hpl_negOne_negOne_at_one, hpl_negOne_negOne_negOne_at_one,
    hpl_negOne_negOne_negOne_zero_at_one, hpl_negOne_negOne_one_at_one,
    hpl_negOne_negOne_one_zero_at_one, hpl_negOne_negOne_zero_at_one,
    hpl_negOne_negOne_zero_negOne_at_one, hpl_negOne_negOne_zero_one_at_one,
    hpl_negOne_negOne_zero_zero_at_one, hpl_negOne_one_at_one, hpl_negOne_one_negOne_at_one,
    hpl_negOne_one_negOne_zero_at_one, hpl_negOne_one_one_at_one, hpl_negOne_one_one_one_at_one,
    hpl_negOne_one_one_zero_at_one, hpl_negOne_one_zero_at_one,
    hpl_negOne_one_zero_negOne_at_one, hpl_negOne_one_zero_one_at_one,
    hpl_negOne_one_zero_zero_at_one, hpl_negOne_zero_negOne_at_one,
    hpl_negOne_zero_negOne_negOne_at_one, hpl_negOne_zero_negOne_one_at_one,
    hpl_negOne_zero_negOne_zero_at_one, hpl_negOne_zero_one_at_one,
    hpl_negOne_zero_one_negOne_at_one, hpl_negOne_zero_one_one_at_one,
    hpl_negOne_zero_one_zero_at_one, hpl_negOne_zero_zero_negOne_at_one,
    hpl_negOne_zero_zero_one_at_one]
  ring

/-! ### The value -/

/-- **`∫₀¹ J_3 = 6 T_3`.** -/
theorem integral_i12TJ_three :
    ∫ s in Ioo (0 : ℝ) 1, i12TJ 3 s =
      6 * (-19 / 12 * π ^ 4 - 2 * π ^ 2 * log 2 ^ 2 - 19 / 4 * π ^ 2 * log 2 + 23 / 2 * π ^ 2
      - 42 * zeta3 * log 2 - 39 / 4 * zeta3 - 3 / 2 * log 2 ^ 4 - 5 * log 2 ^ 3 + 15 * log 2 ^ 2
      + 18 * log 2 - 84) := by
  have h0 := ((tendsto_i12TV3B_zero.add (tendsto_i12TVPsi_zero (c := zero) (P := i12TV3P0)
    (by decide +kernel))).add (tendsto_i12TVPsi_zero (c := negOne) (P := i12TV3Pm)
    (by decide +kernel))).add (tendsto_i12TVMob_zero i12TV3P1)
  have h1 := ((tendsto_i12TV3B_one.add (tendsto_i12TVPsi_one (c := zero) (by decide) i12TV3P0)).add
    (tendsto_i12TVPsi_one (c := negOne) (by decide) i12TV3Pm)).add
    (tendsto_i12TVMob_one (P := i12TV3P1) (by decide +kernel))
  rw [i12TV_integral_eq (fun s hs => hasDerivAt_i12TV3Phi hs)
    (integral_i12TAd_add_integral_i12TBd 3).1 h0 h1, i12TV3_val_P0,
    i12TV3_val_Pm, i12TV3_val_P1z, i12TV3_val_P1m, Li_three_one_half]
  ring

/-- **`T_A⁽3⁾(0) + T_B⁽3⁾(0) = 6 T_3`.** -/
theorem iteratedDeriv_i12TA_add_i12TB_three :
    iteratedDeriv 3 i12TA 0 + iteratedDeriv 3 i12TB 0 =
      ((6 * (-19 / 12 * π ^ 4 - 2 * π ^ 2 * log 2 ^ 2 - 19 / 4 * π ^ 2 * log 2 + 23 / 2 * π ^ 2
        - 42 * zeta3 * log 2 - 39 / 4 * zeta3 - 3 / 2 * log 2 ^ 4 - 5 * log 2 ^ 3 + 15 * log 2 ^ 2
        + 18 * log 2 - 84) : ℝ) : ℂ) := by
  rw [iteratedDeriv_i12TA_add_i12TB_eq_integral_i12TJ, integral_i12TJ_three]

end QED.ThreeLoopD
