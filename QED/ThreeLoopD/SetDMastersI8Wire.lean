/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8Def
public import QED.ThreeLoopD.SetDMastersI13Wire
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₈`: the input from the expansion of the subtracted integral

`I₈` has the same prefactor as `I₁₃`, so
`I₈ C⁻¹ = (i8Tail + i8Rem) / (ε² (1 - ε) Γ(1 + ε) Γ(1 - ε))`
(`QED.ThreeLoopD.setDMasterI8_eq`), and the tail is a rational function of `ε` and
`G = Γ(1 - ε)² / Γ(1 - 2ε)` with no `G`-free term (`QED.ThreeLoopD.i8Tail_eq`). With the
truncations of `G` and of `(Γ(1 + ε) Γ(1 - ε))⁻¹` through `ε⁵` from
`QED.ThreeLoopD.SetDMastersI13Wire`, the expansion

  `Rem = 3/2 + (39/4 - π²/6) ε + (2ζ₃ - 13π²/3 + 491/8) ε²
    + (16π² ln 2 - 80ζ₃ - 379π²/12 - 25π⁴/72 + 5539/16) ε³
    + (-512 a₄ - 64/3 ln⁴2 - 80/3 π² ln²2 + 152π² ln 2 - 763ζ₃ + 62/3 π²ζ₃ - 126ζ₅
      - 4259π²/24 + 323π⁴/120 + 56307/32) ε⁴ + O(ε⁵)` (`QED.ThreeLoopD.i8RemLaurent`)

gives `HasTruncLaurent setDMasterI8 setDLaurentI8 3`
(`QED.ThreeLoopD.hasTruncLaurent_setDMasterI8_of_Rem`). The orders `ε⁰` to `ε⁵` of
`ε³ I₈ C⁻¹` match by the polynomial identity `QED.ThreeLoopD.i8Wire_key`, checked by `ring`.
The expansion of `Rem` is the one implied by the LR96 table; numerically (contour integrals of
`setDI258/i8num.py`) the integral reproduces the six LR96 coefficients of `I₈ C⁻¹` to 37 digits.
Its proof is the hypothesis that remains.

## Main results

* `QED.ThreeLoopD.setDMasterI8_eq`, `QED.ThreeLoopD.i8Tail_eq`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI8_of_Rem`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- **The target expansion of `i8Rem`** through `ε⁴`. -/
noncomputable def i8RemLaurent (ε : ℂ) : ℂ :=
    3 / 2 + (-1 / 6 * (π : ℂ) ^ 2 + 39 / 4) * ε + (-13 / 3 * (π : ℂ) ^ 2 + 2 * (zeta3 : ℂ)
    + 491 / 8) * ε ^ 2 + (-25 / 72 * (π : ℂ) ^ 4 + 16 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
    - 379 / 12 * (π : ℂ) ^ 2 - 80 * (zeta3 : ℂ) + 5539 / 16) * ε ^ 3 + (323 / 120 * (π : ℂ) ^ 4
    + 62 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 80 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2
    + 152 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 4259 / 24 * (π : ℂ) ^ 2 - 763 * (zeta3 : ℂ)
    - 126 * (zeta5 : ℂ) - 64 / 3 * (Real.log 2 : ℂ) ^ 4 - 512 * (Li 4 (1 / 2) : ℂ)
    + 56307 / 32) * ε ^ 4

/-! ### The master and the tail -/

/-- The numerator coefficient of `G²` in `ε · i8Tail`. -/
noncomputable def i8B2 (ε : ℂ) : ℂ := -(ε - 1) * (24 * ε ^ 3 - 71 * ε ^ 2 + 44 * ε - 6)

/-- The numerator coefficient of `G` in `ε · i8Tail`. -/
noncomputable def i8B1 (ε : ℂ) : ℂ := -6 * (ε - 2) * (2 * ε - 1) * (3 * ε - 1)

/-- The denominator of `ε · i8Tail`. -/
noncomputable def i8D (ε : ℂ) : ℂ := 3 * (ε - 2) * (ε - 1) * (2 * ε - 1) ^ 2 * (3 * ε - 1)

theorem i8D_ne_zero {ε : ℂ} (hε : ‖ε‖ < 1 / 8) : i8D ε ≠ 0 := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl (-2) 1 (by norm_num) (by norm_num) (x := ε - 2) (by ring)
  have h2 := hl (-1) 1 (by norm_num) (by norm_num) (x := ε - 1) (by ring)
  have h3 := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
  have h4 := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
  simp only [i8D]
  simp [h1, h2, h3, h4]

/-- **The tail as a rational function of `ε` and `G`.** -/
theorem i8Tail_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    i8Tail ε = (i13G ε ^ 2 * i8B2 ε + i13G ε * i8B1 ε) / (ε * i8D ε) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl (-2) 1 (by norm_num) (by norm_num) (x := ε - 2) (by ring)
  have h2 := hl (-1) 1 (by norm_num) (by norm_num) (x := ε - 1) (by ring)
  have h3 := hl 1 (-2) (by norm_num) (by norm_num) (x := 1 - 2 * ε) (by ring)
  have h4 := hl (-1) 3 (by norm_num) (by norm_num) (x := 3 * ε - 1) (by ring)
  have h5 := hl 2 (-1) (by norm_num) (by norm_num) (x := 2 - ε) (by ring)
  have h3' : 1 - ε * 2 ≠ 0 := by rwa [mul_comm]
  have h4' : ε * 3 - 1 ≠ 0 := by rwa [mul_comm]
  have h6 := hl (-1) 2 (by norm_num) (by norm_num) (x := 2 * ε - 1) (by ring)
  have h6' : ε * 2 - 1 ≠ 0 := by rwa [mul_comm]
  simp only [i8Tail, i8Kap, i13Al0, i13Al1, i13Be0, i8B2, i8B1, i8D]
  generalize i13G ε = G
  field_simp
  ring

/-- `I₈ C⁻¹ = T / (ε² (1 - ε) Γ(1 + ε) Γ(1 - ε))`. -/
theorem setDMasterI8_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setDMasterI8 ε =
      i8T ε / (ε ^ 2 * (1 - ε) * (Gamma (1 + 1 * ε) * Gamma (1 + (-1) * ε))) := by
  have hl := fun c a hc ha {x : ℂ} (hx : x = c + a * ε) => setDGamma_lin_ne_zero hε c a hc ha hx
  have h1 := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 + (-1) * ε) (by ring)
  have h1' := hl 1 (-1) (by norm_num) (by norm_num) (x := 1 - ε) (by ring)
  have hG1 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hGm := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε (-1) (by norm_num))
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  simp only [setDMasterI8, lr96I8, lr96C, QED.DimReg.lr96LoopFactor_four_sub]
  rw [show (1 : ℂ) + ε = 1 + 1 * ε by ring,
    Gamma_eq_div_one (s := ε) (t := 1 + 1 * ε) (p := ε) h0 (by ring) rfl,
    show (2 : ℂ) - ε = 1 + (-1) * ε + 1 by ring, Gamma_add_one _ h1]
  rw [show (1 : ℂ) * ε = ε by ring] at hG1 ⊢
  rw [show (1 : ℂ) + (-1) * ε = 1 - ε by ring] at hGm ⊢
  generalize Gamma (1 + ε) = A at *
  generalize Gamma (1 - ε) = B at *
  generalize (π : ℂ) ^ ε = P at *
  field_simp

/-! ### The polynomial identity -/

/-- `ε³` times the Laurent polynomial of `I₈ C⁻¹`. -/
noncomputable def i8L8e (ε : ℂ) : ℂ :=
    -1 - 16 / 3 * ε - 16 * ε ^ 2 + (-8 / 3 * (π : ℂ) ^ 2 + 2 * (zeta3 : ℂ) - 20) * ε ^ 3
    + (-3 / 10 * (π : ℂ) ^ 4 + 16 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 28 * (π : ℂ) ^ 2
    - 200 / 3 * (zeta3 : ℂ) + 364 / 3) * ε ^ 4 + (46 / 15 * (π : ℂ) ^ 4
    + 21 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 80 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2
    + 168 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 188 * (π : ℂ) ^ 2 - 776 * (zeta3 : ℂ)
    - 126 * (zeta5 : ℂ) - 64 / 3 * (Real.log 2 : ℂ) ^ 4 - 512 * (Li 4 (1 / 2) : ℂ) + 1244) * ε ^ 5

/-- The coefficient of `ε ^ 0` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP0 : ℂ :=
  ((-13 / 36 * (π : ℂ) ^ 6 + 16 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) - 719 / 15 * (π : ℂ) ^ 4
  - 184 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 160 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2
  - 1008 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) + 7373 / 8 * (π : ℂ) ^ 2 - 24 * (zeta3 : ℂ) ^ 2
  + 3447 * (zeta3 : ℂ) + 552 * (zeta5 : ℂ) + 128 * (Real.log 2 : ℂ) ^ 4 + 3072 * (Li 4 (1 / 2) : ℂ)
  + 139257 / 32))

/-- The coefficient of `ε ^ 1` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP1 : ℂ :=
  ((3277 / 540 * (π : ℂ) ^ 6 + 213 / 10 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
  - 80 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2 + 16 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ)
  + 951 / 4 * (π : ℂ) ^ 4 + 934 * (π : ℂ) ^ 2 * (zeta3 : ℂ) - 138 * (π : ℂ) ^ 2 * (zeta5 : ℂ)
  - 64 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4 - 1360 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2
  + 8568 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 512 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ)
  - 7859 * (π : ℂ) ^ 2 + 200 * (zeta3 : ℂ) ^ 2 - 33472 * (zeta3 : ℂ) - 5658 * (zeta5 : ℂ)
  - 1088 * (Real.log 2 : ℂ) ^ 4 - 26112 * (Li 4 (1 / 2) : ℂ) - 2605 / 4))

/-- The coefficient of `ε ^ 2` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP2 : ℂ :=
  ((37 / 1800 * (π : ℂ) ^ 8 - 4 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) - 35719 / 1080 * (π : ℂ) ^ 6
  - 10763 / 60 * (π : ℂ) ^ 4 * (zeta3 : ℂ) + 680 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2
  - 860 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) + 8191 / 48 * (π : ℂ) ^ 4
  + 12 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 + 1863 / 2 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
  + 1205 * (π : ℂ) ^ 2 * (zeta5 : ℂ) + 544 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4
  + 4320 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 27216 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
  + 4352 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ) + 1244421 / 64 * (π : ℂ) ^ 2 - 460 * (zeta3 : ℂ) ^ 2
  - 144 * (zeta3 : ℂ) * (zeta5 : ℂ) + 114761 * (zeta3 : ℂ) + 19488 * (zeta5 : ℂ)
  + 3456 * (Real.log 2 : ℂ) ^ 4 + 82944 * (Li 4 (1 / 2) : ℂ) - 2565761 / 32))

/-- The coefficient of `ε ^ 3` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP3 : ℂ :=
  ((-2729 / 8640 * (π : ℂ) ^ 8 - 44 / 45 * (π : ℂ) ^ 6 * (zeta3 : ℂ)
  + 4 / 3 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 - 4 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ)
  + 11899 / 135 * (π : ℂ) ^ 6 + 2331 / 4 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
  + 13 / 2 * (π : ℂ) ^ 4 * (zeta5 : ℂ) + 16 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4
  - 720 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2 + 3472 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ)
  + 128 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ) - 5663 / 2 * (π : ℂ) ^ 4
  - 100 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 - 12408 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
  - 3760 * (π : ℂ) ^ 2 * (zeta5 : ℂ) - 576 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4
  - 6320 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 39816 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
  - 13824 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ) - 53485 / 8 * (π : ℂ) ^ 2 + 380 * (zeta3 : ℂ) ^ 2
  + 1200 * (zeta3 : ℂ) * (zeta5 : ℂ) - 175948 * (zeta3 : ℂ) - 29574 * (zeta5 : ℂ)
  - 5056 * (Real.log 2 : ℂ) ^ 4 - 121344 * (Li 4 (1 / 2) : ℂ) + 1622737 / 8))

/-- The coefficient of `ε ^ 4` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP4 : ℂ :=
  ((1 / 4800 * (π : ℂ) ^ 10 + 36733 / 21600 * (π : ℂ) ^ 8 + 1136 / 135 * (π : ℂ) ^ 6 * (zeta3 : ℂ)
  - 34 / 3 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 + 43 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ)
  - 150427 / 960 * (π : ℂ) ^ 6 - 11 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
  - 126167 / 120 * (π : ℂ) ^ 4 * (zeta3 : ℂ) - 683 / 12 * (π : ℂ) ^ 4 * (zeta5 : ℂ)
  - 136 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4 + 3160 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2
  - 5588 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) - 1088 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ)
  + 7809539 / 1280 * (π : ℂ) ^ 4 + 230 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2
  + 48 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) + 49517 / 2 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
  + 5321 * (π : ℂ) ^ 2 * (zeta5 : ℂ) + 2528 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4
  + 4160 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 - 26208 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
  + 20224 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ) - 2058997 / 64 * (π : ℂ) ^ 2 - 96 * (zeta3 : ℂ) ^ 2
  - 2760 * (zeta3 : ℂ) * (zeta5 : ℂ) + 119124 * (zeta3 : ℂ) - 216 * (zeta5 : ℂ) ^ 2
  + 19656 * (zeta5 : ℂ) + 3328 * (Real.log 2 : ℂ) ^ 4 + 79872 * (Li 4 (1 / 2) : ℂ) - 1369077 / 8))

/-- The coefficient of `ε ^ 5` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP5 : ℂ :=
  ((-1 / 576 * (π : ℂ) ^ 10 - 29 / 1800 * (π : ℂ) ^ 8 * (zeta3 : ℂ) - 95087 / 21600 * (π : ℂ) ^ 8
  - 14683 / 540 * (π : ℂ) ^ 6 * (zeta3 : ℂ) + 1 / 5 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
  + 36 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 - 868 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ)
  + 30581 / 120 * (π : ℂ) ^ 6 + 55 / 3 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
  + 84791 / 60 * (π : ℂ) ^ 4 * (zeta3 : ℂ) + 541 / 3 * (π : ℂ) ^ 4 * (zeta5 : ℂ)
  + 144 / 5 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4 - 2080 / 3 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2
  + 3856 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) + 3456 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ)
  - 2919653 / 480 * (π : ℂ) ^ 4 - 190 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2
  - 400 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) - 18602 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
  - 3372 * (π : ℂ) ^ 2 * (zeta5 : ℂ) - 1664 / 3 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4
  - 960 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 2 + 6048 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)
  - 13312 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ) + 590469 / 16 * (π : ℂ) ^ 2
  + 2280 * (zeta3 : ℂ) * (zeta5 : ℂ) - 27936 * (zeta3 : ℂ) + 1800 * (zeta5 : ℂ) ^ 2
  - 4536 * (zeta5 : ℂ) - 768 * (Real.log 2 : ℂ) ^ 4 - 18432 * (Li 4 (1 / 2) : ℂ) + 44784))

/-- The coefficient of `ε ^ 6` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP6 : ℂ :=
  ((-1 / 32000 * (π : ℂ) ^ 12 + 23 / 5760 * (π : ℂ) ^ 10 + 29 / 216 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
  + 27793 / 4800 * (π : ℂ) ^ 8 + 8 / 45 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2
  + 21797 / 540 * (π : ℂ) ^ 6 * (zeta3 : ℂ) - 5 / 3 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
  - 158 / 3 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 + 1397 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ)
  - 104599 / 320 * (π : ℂ) ^ 6 - 253 / 6 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
  - 26 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) - 61053 / 40 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
  - 15583 / 60 * (π : ℂ) ^ 4 * (zeta5 : ℂ) - 632 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4
  + 160 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 2 - 912 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ)
  - 5056 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ) + 1051729 / 256 * (π : ℂ) ^ 4
  + 48 * (π : ℂ) ^ 2 * (zeta3 : ℂ) ^ 2 + 920 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ)
  + 4578 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 36 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2
  + 756 * (π : ℂ) ^ 2 * (zeta5 : ℂ) + 128 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) ^ 4
  + 3072 * (π : ℂ) ^ 2 * (Li 4 (1 / 2) : ℂ) - 168921 / 16 * (π : ℂ) ^ 2
  - 576 * (zeta3 : ℂ) * (zeta5 : ℂ) - 4140 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 7` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP7 : ℂ :=
  ((1 / 3840 * (π : ℂ) ^ 12 + 1 / 1200 * (π : ℂ) ^ 10 * (zeta3 : ℂ) - 19 / 5760 * (π : ℂ) ^ 10
  - 667 / 2160 * (π : ℂ) ^ 8 * (zeta3 : ℂ) - 3 / 200 * (π : ℂ) ^ 8 * (zeta5 : ℂ)
  - 1081 / 300 * (π : ℂ) ^ 8 - 40 / 27 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2
  - 241 / 9 * (π : ℂ) ^ 6 * (zeta3 : ℂ) + 23 / 6 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
  + 104 / 3 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 - 964 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ)
  + 53093 / 240 * (π : ℂ) ^ 6 + 209 / 6 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
  + 130 / 3 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) + 9679 / 10 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
  + 167 * (π : ℂ) ^ 4 * (zeta5 : ℂ) + 416 / 15 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4
  + 3328 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ) - 698757 / 320 * (π : ℂ) ^ 4
  - 760 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ) - 300 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2
  + 3420 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 8` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP8 : ℂ :=
  ((-23 / 38400 * (π : ℂ) ^ 12 - 1 / 144 * (π : ℂ) ^ 10 * (zeta3 : ℂ) + 1 / 1200 * (π : ℂ) ^ 10
  - 1 / 180 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 + 551 / 2160 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
  + 1 / 8 * (π : ℂ) ^ 8 * (zeta5 : ℂ) + 323 / 400 * (π : ℂ) ^ 8
  + 92 / 27 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2 + 1 / 5 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
  + 31 / 5 * (π : ℂ) ^ 6 * (zeta3 : ℂ) - 19 / 6 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
  - 8 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) ^ 2 + 228 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ)
  - 4259 / 80 * (π : ℂ) ^ 6 - 44 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) ^ 2
  - 299 / 3 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) - 2289 / 10 * (π : ℂ) ^ 4 * (zeta3 : ℂ)
  - 9 / 5 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2 - 189 / 5 * (π : ℂ) ^ 4 * (zeta5 : ℂ)
  - 32 / 5 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ) ^ 4 - 768 / 5 * (π : ℂ) ^ 4 * (Li 4 (1 / 2) : ℂ)
  + 168921 / 320 * (π : ℂ) ^ 4 + 192 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (zeta5 : ℂ)
  + 690 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2 - 864 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 9` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP9 : ℂ :=
  ((19 / 38400 * (π : ℂ) ^ 12 + 23 / 1440 * (π : ℂ) ^ 10 * (zeta3 : ℂ)
  + 5 / 108 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 - 29 / 450 * (π : ℂ) ^ 8 * (zeta3 : ℂ)
  - 23 / 80 * (π : ℂ) ^ 8 * (zeta5 : ℂ) - 76 / 27 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2
  - 5 / 3 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ) + 4 / 5 * (π : ℂ) ^ 6 * (zeta5 : ℂ)
  + 247 / 3 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) + 15 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2
  - 570 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 10` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP10 : ℂ :=
  ((-1 / 8000 * (π : ℂ) ^ 12 - 19 / 1440 * (π : ℂ) ^ 10 * (zeta3 : ℂ)
  - 23 / 216 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 + 19 / 80 * (π : ℂ) ^ 8 * (zeta5 : ℂ)
  + 32 / 45 * (π : ℂ) ^ 6 * (zeta3 : ℂ) ^ 2 + 23 / 6 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
  - 104 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) * (zeta5 : ℂ) - 69 / 2 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2
  + 144 * (π : ℂ) ^ 2 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 11` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP11 : ℂ :=
  ((1 / 300 * (π : ℂ) ^ 10 * (zeta3 : ℂ) + 19 / 216 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2
  - 3 / 50 * (π : ℂ) ^ 8 * (zeta5 : ℂ) - 19 / 6 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
  + 57 / 2 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2))

/-- The coefficient of `ε ^ 12` in `QED.ThreeLoopD.i8WireP`. -/
noncomputable def i8WP12 : ℂ :=
  ((-1 / 45 * (π : ℂ) ^ 8 * (zeta3 : ℂ) ^ 2 + 4 / 5 * (π : ℂ) ^ 6 * (zeta3 : ℂ) * (zeta5 : ℂ)
  - 36 / 5 * (π : ℂ) ^ 4 * (zeta5 : ℂ) ^ 2))

/-- The polynomial `(K S_p - ε³ L₈ D (1 - ε)) / ε⁶`. -/
noncomputable def i8WireP (ε : ℂ) : ℂ :=
  i8WP0 + i8WP1 * ε + i8WP2 * ε ^ 2 + i8WP3 * ε ^ 3 + i8WP4 * ε ^ 4 + i8WP5 * ε ^ 5 + i8WP6 * ε ^ 6
    + i8WP7 * ε ^ 7 + i8WP8 * ε ^ 8 + i8WP9 * ε ^ 9 + i8WP10 * ε ^ 10 + i8WP11 * ε ^ 11
    + i8WP12 * ε ^ 12

/-- The truncated numerator `G_p² B₂ + G_p B₁ + ε D Rem_L`. -/
noncomputable def i8K (ε : ℂ) : ℂ :=
  i13Gp ε ^ 2 * i8B2 ε + i13Gp ε * i8B1 ε + ε * i8D ε * i8RemLaurent ε

/-- **The polynomial identity behind the expansion of `I₈`**: the orders `ε⁰` to `ε⁵` of
`K S_p` are those of `ε³ L₈ D (1 - ε)`. -/
theorem i8Wire_key (ε : ℂ) :
    i8K ε * i13Sp ε - i8L8e ε * i8D ε * (1 - ε) = ε ^ 6 * i8WireP ε := by
  simp only [i8K, i13Gp, i8B2, i8B1, i8D, i8RemLaurent, i13Sp, i8L8e, i8WireP,
    i8WP0, i8WP1, i8WP2, i8WP3, i8WP4, i8WP5, i8WP6, i8WP7, i8WP8, i8WP9, i8WP10, i8WP11,
    i8WP12]
  ring

/-! ### The expansion -/

/-- `H = (2 G_p ΔG + ε⁶ ΔG²) B₂ + ΔG B₁ + D R`. -/
noncomputable def i8H (ε R : ℂ) : ℂ :=
  (2 * i13Gp ε * i13dG ε + ε ^ 6 * i13dG ε ^ 2) * i8B2 ε + i13dG ε * i8B1 ε + i8D ε * R

/-- The remainder `R₈` with `I₈ C⁻¹ = L₈ + ε³ R₈`, given `Rem = Rem_L + ε⁵ R`. -/
noncomputable def i8R (ε R : ℂ) : ℂ :=
  (i8WireP ε + i8K ε * i13dS ε + i8H ε R * i13S ε) / (i8D ε * (1 - ε))

theorem analyticAt_i8R {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0) :
    AnalyticAt ℂ (fun ε => i8R ε (R ε)) 0 := by
  have hV : AnalyticAt ℂ i13V 0 := by
    have h1 := analyticAt_logGammaRem_mul (-1)
    have h2 := analyticAt_logGammaRem_mul (-2)
    unfold i13V
    fun_prop
  have hW : AnalyticAt ℂ i13W 0 := by
    have h1 := analyticAt_logGammaRem_mul 1
    have h2 := analyticAt_logGammaRem_mul (-1)
    unfold i13W
    fun_prop
  have hX : AnalyticAt ℂ i13X 0 := by unfold i13X; fun_prop
  have hY : AnalyticAt ℂ i13Y 0 := by unfold i13Y; fun_prop
  have hEG : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (ε ^ 2 * i13X ε)) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hES : AnalyticAt ℂ (fun ε => QED.DimReg.expRem3 (-(ε ^ 2 * i13Y ε))) 0 :=
    QED.DimReg.analyticAt_expRem3.comp_of_eq (by fun_prop) (by simp)
  have hdG : AnalyticAt ℂ i13dG 0 := by unfold i13dG i13dGp; fun_prop
  have hdS : AnalyticAt ℂ i13dS 0 := by unfold i13dS i13dSp; fun_prop
  have hS : AnalyticAt ℂ i13S 0 := by unfold i13S; fun_prop
  have hP : AnalyticAt ℂ i8WireP 0 := by unfold i8WireP; fun_prop
  have hGp : AnalyticAt ℂ i13Gp 0 := by unfold i13Gp; fun_prop
  have hB2 : AnalyticAt ℂ i8B2 0 := by unfold i8B2; fun_prop
  have hB1 : AnalyticAt ℂ i8B1 0 := by unfold i8B1; fun_prop
  have hD : AnalyticAt ℂ i8D 0 := by unfold i8D; fun_prop
  have hRL : AnalyticAt ℂ i8RemLaurent 0 := by unfold i8RemLaurent; fun_prop
  have hK : AnalyticAt ℂ i8K 0 := by unfold i8K; fun_prop
  unfold i8R i8H
  refine AnalyticAt.div (by fun_prop) (by fun_prop) ?_
  norm_num [i8D]

/-- **The set (d) input for `I₈` from the expansion of `Rem`**: if
`Rem = Rem_L + ε⁵ R` with `R` analytic at `0`, then `I₈ C⁻¹ = L₈ + ε³ R₈` with `R₈` analytic
at `0`. -/
theorem hasTruncLaurent_setDMasterI8_of_Rem (hRem : HasTruncLaurent i8Rem i8RemLaurent 5) :
    HasTruncLaurent setDMasterI8 setDLaurentI8 3 := by
  obtain ⟨RR, hRR, hRe⟩ := hRem
  refine ⟨fun ε => i8R ε (RR ε), analyticAt_i8R hRR, ?_⟩
  filter_upwards [setDGamma_eventually_small, hRe, self_mem_nhdsWithin] with ε hε hRε h0
  have h0 : ε ≠ 0 := h0
  have hD := i8D_ne_zero hε
  have h1 : (1 : ℂ) - ε ≠ 0 :=
    setDGamma_lin_ne_zero hε 1 (-1) (by norm_num) (by norm_num) (by ring)
  have hL : setDLaurentI8 ε = i8L8e ε / ε ^ 3 := by
    simp only [setDLaurentI8, i8L8e]
    field_simp
    ring
  have hS0 : i13Sp ε + ε ^ 6 * i13dS ε ≠ 0 := by
    rw [← i13S_trunc]; exact Complex.exp_ne_zero _
  have hSG : Gamma (1 + 1 * ε) * Gamma (1 + (-1) * ε) = (i13Sp ε + ε ^ 6 * i13dS ε)⁻¹ := by
    rw [i13GammaProd_eq hε, ← i13S_trunc, i13S, Complex.exp_neg, inv_inv]
  have key := i8Wire_key ε
  rw [setDMasterI8_eq h0 hε, i8T, i8Tail_eq h0 hε, hRε, i13G_eq hε, i13G_trunc, hSG, hL,
    i8R, i8H, i13S_trunc]
  simp only [i8K] at key ⊢
  generalize i13Gp ε = Gp at *
  generalize i13dG ε = dG at *
  generalize i8B2 ε = B2 at *
  generalize i8B1 ε = B1 at *
  generalize i8D ε = D at *
  generalize i8RemLaurent ε = RL at *
  generalize RR ε = R at *
  generalize i13Sp ε = Sp at *
  generalize i13dS ε = dS at *
  generalize i8L8e ε = L at *
  generalize i8WireP ε = P at *
  field_simp
  linear_combination key

end QED.ThreeLoopD
