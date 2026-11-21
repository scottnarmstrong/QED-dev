/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLAlt5Rel

/-!
# Harmonic polylogarithms at `1`: alternating words of weight five (C)

The values `H(w; 1)` of the 35 words `w` of weight five over `{0, 1, -1}`
starting with `-1, 0` or `-1, 1` and with no trailing zero (excluding those known in closed form in
`QED.Polylog.HPLValues5`, `QED.Polylog.HPLLiHalf` and `QED.Polylog.HPLAlt5Rel`), in the basis
`ζ(5), π² ζ(3), π⁴ log 2, π² log³ 2, log⁵ 2, Li₅(1/2), Li₄(1/2) log 2, ζ(3) log² 2`
(`ζ(3) = zeta3`, `ζ(5) = zeta5`).

Each value is a rational linear combination of the relations of `QED.Polylog.HPLAlt5Rel` and
the ten known values (coefficients found by exact linear algebra over `ℚ` by a script,
checked here by `linear_combination`).
-/

@[expose] public section

open Real

namespace QED.Polylog.HPL

open Letter

theorem hpl_negOne_zero_zero_zero_one_at_one :
    hpl [negOne, zero, zero, zero, one] 1 =
      1 / 90 * log 2 * π ^ 4 + 1 / 8 * zeta3 * π ^ 2 - 59 / 32 * zeta5 := by
  linear_combination (389 / 288) * hpl_zero_zero_zero_zero_one_at_one +
    (11 / 12) * hpl_zero_zero_zero_one_one_at_one +
    (305 / 288) * hpl_zero_zero_one_zero_one_at_one +
    (121 / 288) * hpl_zero_one_zero_zero_one_at_one + (1) * hpl_zero_zero_one_one_one_at_one +
    (1 / 2) * hpl_zero_one_zero_one_one_at_one + (1 / 6) * hpl_zero_one_one_zero_one_at_one +
    (-7 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (37 / 32) * rel5_sh_m_mmmm +
    (3 / 64) * rel5_sh_m_0mmm + (-1 / 64) * rel5_sh_m_m0mm + (5 / 16) * rel5_sh_m_mm0m +
    (91 / 64) * rel5_sh_m_mm1m + (79 / 64) * rel5_sh_m_mmm1 + (233 / 256) * rel5_st_m_0001 +
    (-713 / 576) * rel5_st_m_000m + (-11 / 18) * rel5_sh_m_00mm + (-19 / 32) * rel5_sh_m_01mm +
    (5 / 9) * rel5_sh_m_0m0m + (-11 / 32) * rel5_sh_m_0m1m + (-1 / 3) * rel5_sh_m_0mm1 +
    (-19 / 64) * rel5_sh_m_m01m + (1 / 48) * rel5_sh_m_m0m1 + (-27 / 64) * rel5_sh_m_m10m +
    (-5 / 12) * rel5_sh_m_m1m1 + (19 / 32) * rel5_sh_m_mm01 + (-335 / 768) * rel5_st_01_00m +
    (133 / 192) * rel5_st_0m_001 + (-2 / 9) * rel5_sh_0m_00m + (-65 / 576) * rel5_st_0m_00m +
    (-11 / 18) * rel5_sh_0m_0mm + (11 / 12) * rel5_sh_m1_mm1 + (3 / 16) * rel5_mob_0mmm1 +
    (13 / 288) * rel5_sh_m_000m + (17 / 36) * rel5_sh_m_001m + (-73 / 288) * rel5_st_m_001m +
    (79 / 144) * rel5_sh_m_00m1 + (-19 / 72) * rel5_st_m_00m1 + (1 / 8) * rel5_sh_m_010m +
    (5 / 16) * rel5_sh_m_01m1 + (19 / 36) * rel5_sh_m_0m01 + (41 / 48) * rel5_sh_m_0m11 +
    (-5 / 144) * rel5_sh_m_m001 + (65 / 1152) * rel5_st_m_m001 + (1 / 288) * rel5_st_m_m00m +
    (65 / 48) * rel5_sh_m_m011 + (21 / 32) * rel5_sh_m_m101 + (407 / 2304) * rel5_st_01_01m +
    (115 / 256) * rel5_st_01_m0m + (-9 / 64) * rel5_st_0m_0m1 + (1 / 18) * rel5_st_0m_0mm +
    (23 / 64) * rel5_st_0m_m01 + (-139 / 576) * rel5_sh_m_0001 + (-17 / 18) * rel5_sh_m_0011 +
    (-67 / 288) * rel5_st_m_0011 + (31 / 36) * rel5_st_m_00mm + (-143 / 144) * rel5_sh_m_0101 +
    (-5 / 12) * rel5_st_m_010m + (-11 / 144) * rel5_st_m_01m1 + (29 / 36) * rel5_st_m_0m0m +
    (13 / 48) * rel5_st_m_0m1m + (37 / 144) * rel5_st_m_m01m + (265 / 1152) * rel5_st_m_m0m1 +
    (-65 / 576) * rel5_st_m_m101 + (-1 / 144) * rel5_st_m_m10m + (1 / 12) * rel5_st_m_m1m1 +
    (91 / 288) * rel5_sh_01_00m + (1 / 6) * rel5_sh_01_01m + (-1 / 12) * rel5_sh_01_0m1 +
    (97 / 96) * rel5_st_01_0mm + (1 / 6) * rel5_sh_01_m11 + (-211 / 288) * rel5_sh_0m_001 +
    (-5 / 24) * rel5_sh_0m_01m + (-1 / 2) * rel5_sh_m1_011 + (-17 / 96) * rel5_sh_m1_0m1 +
    (-65 / 96) * rel5_sh_m1_m01 + (11 / 2) * rel5_mob_00mmm + (57 / 32) * rel5_mob_01mmm +
    (2) * rel5_mob_0m0mm + (19 / 32) * rel5_mob_0m1mm + (-27 / 32) * rel5_mob_m10mm +
    (-17 / 72) * rel5_st_m_011m + (5 / 12) * rel5_st_m_01mm + (-11 / 32) * rel5_st_m_0m11 +
    (49 / 96) * rel5_st_m_0mm1 + (-27 / 32) * rel5_st_m_m011 + (-1 / 12) * rel5_st_m_m0mm +
    (-1 / 36) * rel5_st_m_m11m + (5 / 72) * rel5_st_m_mm0m + (-1 / 36) * rel5_st_m_mm1m +
    (-1) * rel5_st_m_0mmm

theorem hpl_negOne_zero_zero_zero_negOne_at_one :
    hpl [negOne, zero, zero, zero, negOne] 1 =
      7 / 720 * log 2 * π ^ 4 + 1 / 16 * zeta3 * π ^ 2 - 17 / 16 * zeta5 := by
  linear_combination (-2) * hpl_zero_zero_zero_zero_one_at_one +
    (1) * hpl_zero_zero_zero_zero_negOne_at_one + (-1) * rel5_st_m_0001 + (1) * rel5_st_m_000m +
    (1) * rel5_st_0m_00m + (1) * rel5_sh_m_0001

theorem hpl_negOne_zero_zero_one_one_at_one :
    hpl [negOne, zero, zero, one, one] 1 =
      2 * Li 4 (1 / 2) * log 2 + 2 * Li 5 (1 / 2) + 1 / 15 * log 2 ^ 5
      - 1 / 18 * log 2 ^ 3 * π ^ 2 + 7 / 8 * log 2 ^ 2 * zeta3 + 1 / 360 * log 2 * π ^ 4
      - 7 / 48 * zeta3 * π ^ 2 - 15 / 32 * zeta5 := by
  linear_combination (95 / 288) * hpl_zero_zero_zero_zero_one_at_one +
    (-10 / 3) * hpl_zero_zero_zero_one_one_at_one +
    (-763 / 288) * hpl_zero_zero_one_zero_one_at_one +
    (-323 / 288) * hpl_zero_one_zero_zero_one_at_one + (1 / 2) * hpl_zero_zero_one_one_one_at_one +
    (1 / 2) * hpl_zero_one_zero_one_one_at_one + (1 / 6) * hpl_zero_one_one_zero_one_at_one +
    (-17 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (2) * hpl_negOne_one_one_one_one_at_one +
    (-89 / 60) * rel5_sh_m_mmmm + (5 / 48) * rel5_sh_m_0mmm + (-5 / 144) * rel5_sh_m_m0mm +
    (2 / 3) * rel5_sh_m_m1mm + (-17 / 72) * rel5_sh_m_mm0m + (-11 / 8) * rel5_sh_m_mm1m +
    (-13 / 8) * rel5_sh_m_mmm1 + (9 / 128) * rel5_st_m_0001 + (73 / 64) * rel5_st_m_000m +
    (25 / 18) * rel5_sh_m_00mm + (13 / 24) * rel5_sh_m_01mm + (-91 / 144) * rel5_sh_m_0m0m +
    (1 / 6) * rel5_sh_m_0m1m + (-1 / 6) * rel5_sh_m_0mm1 + (13 / 48) * rel5_sh_m_m01m +
    (-7 / 48) * rel5_sh_m_m0m1 + (11 / 24) * rel5_sh_m_m10m + (1) * rel5_sh_m_m11m +
    (73 / 48) * rel5_sh_m_m1m1 + (-13 / 24) * rel5_sh_m_mm01 + (85 / 192) * rel5_st_01_00m +
    (41 / 128) * rel5_st_0m_001 + (-125 / 576) * rel5_sh_0m_00m + (-847 / 576) * rel5_st_0m_00m +
    (43 / 72) * rel5_sh_0m_0mm + (-1 / 3) * rel5_sh_m1_m11 + (-23 / 24) * rel5_sh_m1_mm1 +
    (5 / 12) * rel5_mob_0mmm1 + (455 / 576) * rel5_sh_m_000m + (-281 / 288) * rel5_sh_m_001m +
    (199 / 288) * rel5_st_m_001m + (-167 / 144) * rel5_sh_m_00m1 + (205 / 288) * rel5_st_m_00m1 +
    (-79 / 192) * rel5_sh_m_010m + (-13 / 48) * rel5_sh_m_01m1 + (-31 / 72) * rel5_sh_m_0m01 +
    (-1 / 4) * rel5_sh_m_0m11 + (37 / 144) * rel5_sh_m_m001 + (-17 / 288) * rel5_st_m_m001 +
    (-19 / 288) * rel5_st_m_m00m + (-1) * rel5_sh_m_m011 + (-17 / 48) * rel5_sh_m_m101 +
    (2) * rel5_sh_m_m111 + (-61 / 192) * rel5_st_01_01m + (-235 / 576) * rel5_st_01_m0m +
    (191 / 384) * rel5_st_0m_0m1 + (-49 / 36) * rel5_st_0m_0mm + (-97 / 384) * rel5_st_0m_m01 +
    (695 / 576) * rel5_sh_m_0001 + (20 / 9) * rel5_sh_m_0011 + (-17 / 36) * rel5_st_m_0011 +
    (-71 / 36) * rel5_st_m_00mm + (229 / 144) * rel5_sh_m_0101 + (19 / 18) * rel5_st_m_010m +
    (1 / 18) * rel5_st_m_01m1 + (-47 / 24) * rel5_st_m_0m0m + (-1 / 144) * rel5_st_m_0m1m +
    (-7 / 48) * rel5_st_m_m01m + (-19 / 288) * rel5_st_m_m0m1 + (17 / 144) * rel5_st_m_m101 +
    (19 / 144) * rel5_st_m_m10m + (-5 / 48) * rel5_st_m_m1m1 + (-53 / 288) * rel5_sh_01_00m +
    (-5 / 12) * rel5_sh_01_01m + (3 / 8) * rel5_st_01_0m1 + (-3 / 4) * rel5_st_01_0mm +
    (-13 / 12) * rel5_sh_01_m11 + (77 / 288) * rel5_sh_0m_001 + (21 / 64) * rel5_sh_0m_01m +
    (11 / 12) * rel5_sh_m1_011 + (1 / 4) * rel5_sh_m1_0m1 + (1 / 2) * rel5_sh_m1_m01 +
    (-31 / 4) * rel5_mob_00mmm + (-13 / 8) * rel5_mob_01mmm + (-5 / 2) * rel5_mob_0m0mm +
    (-13 / 24) * rel5_mob_0m1mm + (11 / 12) * rel5_mob_m10mm + (25 / 72) * rel5_st_m_011m +
    (-1 / 4) * rel5_st_m_01mm + (1 / 6) * rel5_st_m_0m11 + (-1 / 12) * rel5_st_m_0mm1 +
    (11 / 12) * rel5_st_m_m011 + (-3 / 4) * rel5_st_m_m0mm + (1 / 18) * rel5_st_m_m11m +
    (1 / 4) * rel5_st_m_m1mm + (-37 / 72) * rel5_st_m_mm0m + (2 / 9) * rel5_st_m_mm1m +
    (-1 / 2) * rel5_st_m_0mmm + (2) * rel5_mob_0000m

theorem hpl_negOne_zero_zero_one_negOne_at_one :
    hpl [negOne, zero, zero, one, negOne] 1 =
      -2 * Li 4 (1 / 2) * log 2 - 1 / 12 * log 2 ^ 5 + 1 / 12 * log 2 ^ 3 * π ^ 2
      + 15 / 32 * zeta5 := by
  linear_combination (1 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (-1 / 4) * rel5_st_m_0001 +
    (-1 / 4) * rel5_st_0m_001 + (1) * rel5_sh_m_001m + (1 / 2) * rel5_sh_m_010m +
    (-1 / 4) * rel5_st_0m_0m1 + (-1 / 4) * rel5_st_0m_m01 + (-1 / 2) * rel5_sh_0m_01m

theorem hpl_negOne_zero_zero_negOne_one_at_one :
    hpl [negOne, zero, zero, negOne, one] 1 =
      -4 * Li 5 (1 / 2) + 1 / 30 * log 2 ^ 5 - 1 / 18 * log 2 ^ 3 * π ^ 2
      - 3 / 160 * log 2 * π ^ 4 + 27 / 8 * zeta5 := by
  linear_combination (-193 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (33 / 4) * hpl_zero_zero_zero_one_one_at_one + (479 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (199 / 96) * hpl_zero_one_zero_zero_one_at_one + (-2) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 2) * hpl_zero_one_zero_one_one_at_one + (-1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (16 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (869 / 480) * rel5_sh_m_mmmm + (-49 / 192) * rel5_sh_m_0mmm + (49 / 576) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (23 / 144) * rel5_sh_m_mm0m + (85 / 64) * rel5_sh_m_mm1m +
    (129 / 64) * rel5_sh_m_mmm1 + (51 / 256) * rel5_st_m_0001 + (-889 / 576) * rel5_st_m_000m +
    (-1 / 6) * rel5_sh_m_00mm + (-47 / 96) * rel5_sh_m_01mm + (47 / 24) * rel5_sh_m_0m0m +
    (1 / 96) * rel5_sh_m_0m1m + (2 / 3) * rel5_sh_m_0mm1 + (-47 / 192) * rel5_sh_m_m01m +
    (13 / 48) * rel5_sh_m_m0m1 + (-95 / 192) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-21 / 8) * rel5_sh_m_m1m1 + (47 / 96) * rel5_sh_m_mm01 + (-403 / 256) * rel5_st_01_00m +
    (1 / 24) * rel5_st_0m_001 + (-3 / 32) * rel5_sh_0m_00m + (2047 / 576) * rel5_st_0m_00m +
    (-19 / 12) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (1) * rel5_sh_m1_mm1 +
    (-49 / 48) * rel5_mob_0mmm1 + (-9 / 8) * rel5_sh_m_000m + (71 / 48) * rel5_sh_m_001m +
    (-325 / 288) * rel5_st_m_001m + (133 / 48) * rel5_sh_m_00m1 + (-167 / 144) * rel5_st_m_00m1 +
    (43 / 96) * rel5_sh_m_010m + (11 / 48) * rel5_sh_m_01m1 + (7 / 12) * rel5_sh_m_0m01 +
    (-17 / 48) * rel5_sh_m_0m11 + (-23 / 48) * rel5_sh_m_m001 + (71 / 1152) * rel5_st_m_m001 +
    (37 / 288) * rel5_st_m_m00m + (31 / 48) * rel5_sh_m_m011 + (5 / 96) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (769 / 2304) * rel5_st_01_01m + (2285 / 2304) * rel5_st_01_m0m +
    (-35 / 48) * rel5_st_0m_0m1 + (19 / 6) * rel5_st_0m_0mm + (13 / 48) * rel5_st_0m_m01 +
    (-107 / 64) * rel5_sh_m_0001 + (-7 / 2) * rel5_sh_m_0011 + (-79 / 96) * rel5_st_m_0011 +
    (61 / 12) * rel5_st_m_00mm + (-47 / 16) * rel5_sh_m_0101 + (-35 / 18) * rel5_st_m_010m +
    (-5 / 144) * rel5_st_m_01m1 + (139 / 36) * rel5_st_m_0m0m + (-37 / 144) * rel5_st_m_0m1m +
    (5 / 144) * rel5_st_m_m01m + (-113 / 1152) * rel5_st_m_m0m1 + (-71 / 576) * rel5_st_m_m101 +
    (-37 / 144) * rel5_st_m_m10m + (1 / 8) * rel5_st_m_m1m1 + (125 / 96) * rel5_sh_01_00m +
    (7 / 6) * rel5_sh_01_01m + (-5 / 12) * rel5_sh_01_0m1 + (-1 / 4) * rel5_st_01_0m1 +
    (191 / 96) * rel5_st_01_0mm + (2) * rel5_sh_01_m11 + (-149 / 96) * rel5_sh_0m_001 +
    (-91 / 96) * rel5_sh_0m_01m + (-4 / 3) * rel5_sh_m1_011 + (-31 / 96) * rel5_sh_m1_0m1 +
    (-31 / 96) * rel5_sh_m1_m01 + (10) * rel5_mob_00mmm + (47 / 32) * rel5_mob_01mmm +
    (3) * rel5_mob_0m0mm + (47 / 96) * rel5_mob_0m1mm + (-95 / 96) * rel5_mob_m10mm +
    (-11 / 24) * rel5_st_m_011m + (1 / 12) * rel5_st_m_01mm + (1 / 96) * rel5_st_m_0m11 +
    (-11 / 32) * rel5_st_m_0mm1 + (-95 / 96) * rel5_st_m_m011 + (19 / 12) * rel5_st_m_m0mm +
    (-1 / 12) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm + (23 / 24) * rel5_st_m_mm0m +
    (-5 / 12) * rel5_st_m_mm1m + (2) * rel5_st_m_0mmm + (-4) * rel5_mob_0000m

theorem hpl_negOne_zero_zero_negOne_negOne_at_one :
    hpl [negOne, zero, zero, negOne, negOne] 1 =
      -2 * Li 5 (1 / 2) + 1 / 60 * log 2 ^ 5 - 1 / 36 * log 2 ^ 3 * π ^ 2
      + 7 / 8 * log 2 ^ 2 * zeta3 - 1 / 48 * log 2 * π ^ 4 + 125 / 64 * zeta5 := by
  linear_combination (-97 / 192) * hpl_zero_zero_zero_zero_one_at_one +
    (21 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (335 / 192) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 192) * hpl_zero_one_zero_zero_one_at_one + (-1) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 4) * hpl_zero_one_zero_one_one_at_one + (-1 / 4) * hpl_zero_one_one_zero_one_at_one +
    (29 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-2) * hpl_negOne_one_one_one_one_at_one +
    (869 / 960) * rel5_sh_m_mmmm + (-49 / 384) * rel5_sh_m_0mmm + (49 / 1152) * rel5_sh_m_m0mm +
    (-2 / 3) * rel5_sh_m_m1mm + (23 / 288) * rel5_sh_m_mm0m + (85 / 128) * rel5_sh_m_mm1m +
    (129 / 128) * rel5_sh_m_mmm1 + (-13 / 512) * rel5_st_m_0001 + (-889 / 1152) * rel5_st_m_000m +
    (-1 / 12) * rel5_sh_m_00mm + (-47 / 192) * rel5_sh_m_01mm + (35 / 48) * rel5_sh_m_0m0m +
    (1 / 192) * rel5_sh_m_0m1m + (1 / 3) * rel5_sh_m_0mm1 + (-47 / 384) * rel5_sh_m_m01m +
    (13 / 96) * rel5_sh_m_m0m1 + (-95 / 384) * rel5_sh_m_m10m + (-1) * rel5_sh_m_m11m +
    (-21 / 16) * rel5_sh_m_m1m1 + (47 / 192) * rel5_sh_m_mm01 + (-83 / 512) * rel5_st_01_00m +
    (-11 / 48) * rel5_st_0m_001 + (13 / 64) * rel5_sh_0m_00m + (1471 / 1152) * rel5_st_0m_00m +
    (-19 / 24) * rel5_sh_0m_0mm + (1 / 3) * rel5_sh_m1_m11 + (1 / 2) * rel5_sh_m1_mm1 +
    (-49 / 96) * rel5_mob_0mmm1 + (-9 / 16) * rel5_sh_m_000m + (71 / 96) * rel5_sh_m_001m +
    (-325 / 576) * rel5_st_m_001m + (85 / 96) * rel5_sh_m_00m1 + (-167 / 288) * rel5_st_m_00m1 +
    (43 / 192) * rel5_sh_m_010m + (11 / 96) * rel5_sh_m_01m1 + (1 / 24) * rel5_sh_m_0m01 +
    (-17 / 96) * rel5_sh_m_0m11 + (-23 / 96) * rel5_sh_m_m001 + (71 / 2304) * rel5_st_m_m001 +
    (37 / 576) * rel5_st_m_m00m + (31 / 96) * rel5_sh_m_m011 + (5 / 192) * rel5_sh_m_m101 +
    (-2) * rel5_sh_m_m111 + (1345 / 4608) * rel5_st_01_01m + (1709 / 4608) * rel5_st_01_m0m +
    (-35 / 96) * rel5_st_0m_0m1 + (13 / 12) * rel5_st_0m_0mm + (13 / 96) * rel5_st_0m_m01 +
    (-107 / 128) * rel5_sh_m_0001 + (-3 / 4) * rel5_sh_m_0011 + (113 / 192) * rel5_st_m_0011 +
    (37 / 24) * rel5_st_m_00mm + (-23 / 32) * rel5_sh_m_0101 + (-13 / 18) * rel5_st_m_010m +
    (-5 / 288) * rel5_st_m_01m1 + (85 / 72) * rel5_st_m_0m0m + (-37 / 288) * rel5_st_m_0m1m +
    (5 / 288) * rel5_st_m_m01m + (-113 / 2304) * rel5_st_m_m0m1 + (-71 / 1152) * rel5_st_m_m101 +
    (-37 / 288) * rel5_st_m_m10m + (1 / 16) * rel5_st_m_m1m1 + (-19 / 192) * rel5_sh_01_00m +
    (1 / 12) * rel5_sh_01_01m + (-5 / 24) * rel5_sh_01_0m1 + (-1 / 8) * rel5_st_01_0m1 +
    (95 / 192) * rel5_st_01_0mm + (1) * rel5_sh_01_m11 + (-5 / 192) * rel5_sh_0m_001 +
    (-43 / 192) * rel5_sh_0m_01m + (-2 / 3) * rel5_sh_m1_011 + (-31 / 192) * rel5_sh_m1_0m1 +
    (-31 / 192) * rel5_sh_m1_m01 + (5) * rel5_mob_00mmm + (47 / 64) * rel5_mob_01mmm +
    (3 / 2) * rel5_mob_0m0mm + (47 / 192) * rel5_mob_0m1mm + (-95 / 192) * rel5_mob_m10mm +
    (-11 / 48) * rel5_st_m_011m + (1 / 24) * rel5_st_m_01mm + (1 / 192) * rel5_st_m_0m11 +
    (-11 / 64) * rel5_st_m_0mm1 + (-95 / 192) * rel5_st_m_m011 + (19 / 24) * rel5_st_m_m0mm +
    (-1 / 24) * rel5_st_m_m11m + (-1 / 4) * rel5_st_m_m1mm + (23 / 48) * rel5_st_m_mm0m +
    (-5 / 24) * rel5_st_m_mm1m + (1) * rel5_st_m_0mmm + (-2) * rel5_mob_0000m

theorem hpl_negOne_zero_one_zero_one_at_one :
    hpl [negOne, zero, one, zero, one] 1 =
      -4 * Li 4 (1 / 2) * log 2 - 4 * Li 5 (1 / 2) - 2 / 15 * log 2 ^ 5
      + 1 / 9 * log 2 ^ 3 * π ^ 2 - 7 / 4 * log 2 ^ 2 * zeta3 + 1 / 120 * log 2 * π ^ 4
      + 3 / 16 * zeta3 * π ^ 2 + 89 / 64 * zeta5 := by
  linear_combination (-2987 / 576) * hpl_zero_zero_zero_zero_one_at_one +
    (151 / 24) * hpl_zero_zero_zero_one_one_at_one +
    (2425 / 576) * hpl_zero_zero_one_zero_one_at_one +
    (929 / 576) * hpl_zero_one_zero_zero_one_at_one + (-5 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-7 / 4) * hpl_zero_one_zero_one_one_at_one + (-7 / 12) * hpl_zero_one_one_zero_one_at_one +
    (101 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (4783 / 960) * rel5_sh_m_mmmm + (-251 / 384) * rel5_sh_m_0mmm + (251 / 1152) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (145 / 288) * rel5_sh_m_mm0m + (543 / 128) * rel5_sh_m_mm1m +
    (707 / 128) * rel5_sh_m_mmm1 + (-1395 / 512) * rel5_st_m_0001 + (413 / 384) * rel5_st_m_000m +
    (-103 / 36) * rel5_sh_m_00mm + (-277 / 192) * rel5_sh_m_01mm + (355 / 72) * rel5_sh_m_0m0m +
    (-13 / 192) * rel5_sh_m_0m1m + (5 / 6) * rel5_sh_m_0mm1 + (-277 / 384) * rel5_sh_m_m01m +
    (25 / 96) * rel5_sh_m_m0m1 + (-541 / 384) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-11 / 3) * rel5_sh_m_m1m1 + (277 / 192) * rel5_sh_m_mm01 + (-2995 / 1536) * rel5_st_01_00m +
    (33 / 128) * rel5_st_0m_001 + (401 / 288) * rel5_sh_0m_00m + (4735 / 1152) * rel5_st_0m_00m +
    (-41 / 18) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (73 / 24) * rel5_sh_m1_mm1 +
    (-251 / 96) * rel5_mob_0mmm1 + (-4477 / 576) * rel5_sh_m_000m + (215 / 144) * rel5_sh_m_001m +
    (-577 / 576) * rel5_st_m_001m + (575 / 288) * rel5_sh_m_00m1 + (-77 / 72) * rel5_st_m_00m1 +
    (-143 / 96) * rel5_sh_m_010m + (7 / 96) * rel5_sh_m_01m1 + (5 / 72) * rel5_sh_m_0m01 +
    (-9 / 32) * rel5_sh_m_0m11 + (-133 / 288) * rel5_sh_m_m001 + (413 / 2304) * rel5_st_m_m001 +
    (73 / 576) * rel5_st_m_m00m + (79 / 32) * rel5_sh_m_m011 + (187 / 192) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (361 / 1536) * rel5_st_01_01m + (12511 / 4608) * rel5_st_01_m0m +
    (-229 / 384) * rel5_st_0m_0m1 + (95 / 36) * rel5_st_0m_0mm + (827 / 384) * rel5_st_0m_m01 +
    (1093 / 1152) * rel5_sh_m_0001 + (-73 / 36) * rel5_sh_m_0011 + (25 / 576) * rel5_st_m_0011 +
    (263 / 72) * rel5_st_m_00mm + (-487 / 288) * rel5_sh_m_0101 + (-107 / 72) * rel5_st_m_010m +
    (25 / 288) * rel5_st_m_01m1 + (77 / 24) * rel5_st_m_0m0m + (-113 / 288) * rel5_st_m_0m1m +
    (13 / 32) * rel5_st_m_m01m + (325 / 2304) * rel5_st_m_m0m1 + (-413 / 1152) * rel5_st_m_m101 +
    (-73 / 288) * rel5_st_m_m10m + (1 / 3) * rel5_st_m_m1m1 + (1091 / 576) * rel5_sh_01_00m +
    (7 / 12) * rel5_sh_01_01m + (-3 / 8) * rel5_sh_01_0m1 + (-3 / 4) * rel5_st_01_0m1 +
    (463 / 64) * rel5_st_01_0mm + (23 / 12) * rel5_sh_01_m11 + (-1115 / 576) * rel5_sh_0m_001 +
    (-23 / 32) * rel5_sh_0m_01m + (-13 / 12) * rel5_sh_m1_011 + (-31 / 64) * rel5_sh_m1_0m1 +
    (-79 / 64) * rel5_sh_m1_m01 + (89 / 4) * rel5_mob_00mmm + (277 / 64) * rel5_mob_01mmm +
    (7) * rel5_mob_0m0mm + (277 / 192) * rel5_mob_0m1mm + (-541 / 192) * rel5_mob_m10mm +
    (-49 / 144) * rel5_st_m_011m + (-1 / 8) * rel5_st_m_01mm + (-13 / 192) * rel5_st_m_0m11 +
    (-67 / 192) * rel5_st_m_0mm1 + (-541 / 192) * rel5_st_m_m011 + (13 / 8) * rel5_st_m_m0mm +
    (-5 / 72) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm + (133 / 144) * rel5_st_m_mm0m +
    (-29 / 72) * rel5_st_m_mm1m + (5 / 2) * rel5_st_m_0mmm + (-4) * rel5_mob_0000m

theorem hpl_negOne_zero_one_zero_negOne_at_one :
    hpl [negOne, zero, one, zero, negOne] 1 =
      4 * Li 4 (1 / 2) * log 2 + 8 * Li 5 (1 / 2) + 1 / 10 * log 2 ^ 5
      - 1 / 18 * log 2 ^ 3 * π ^ 2 + 71 / 1440 * log 2 * π ^ 4 - 5 / 96 * zeta3 * π ^ 2
      - 123 / 16 * zeta5 := by
  linear_combination (193 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 2) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 48) * hpl_zero_one_zero_zero_one_at_one + (4) * hpl_zero_zero_one_one_one_at_one +
    (3) * hpl_zero_one_zero_one_one_at_one + (1) * hpl_zero_one_one_zero_one_at_one +
    (-35 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (8) * hpl_negOne_one_one_one_one_at_one +
    (-869 / 240) * rel5_sh_m_mmmm + (49 / 96) * rel5_sh_m_0mmm + (-49 / 288) * rel5_sh_m_m0mm +
    (8 / 3) * rel5_sh_m_m1mm + (-23 / 72) * rel5_sh_m_mm0m + (-85 / 32) * rel5_sh_m_mm1m +
    (-129 / 32) * rel5_sh_m_mmm1 + (141 / 128) * rel5_st_m_0001 + (601 / 288) * rel5_st_m_000m +
    (13 / 3) * rel5_sh_m_00mm + (47 / 48) * rel5_sh_m_01mm + (-11 / 12) * rel5_sh_m_0m0m +
    (-1 / 48) * rel5_sh_m_0m1m + (-4 / 3) * rel5_sh_m_0mm1 + (47 / 96) * rel5_sh_m_m01m +
    (-13 / 24) * rel5_sh_m_m0m1 + (95 / 96) * rel5_sh_m_m10m + (4) * rel5_sh_m_m11m +
    (21 / 4) * rel5_sh_m_m1m1 + (-47 / 48) * rel5_sh_m_mm01 + (83 / 128) * rel5_st_01_00m +
    (23 / 12) * rel5_st_0m_001 + (-13 / 16) * rel5_sh_0m_00m + (-1759 / 288) * rel5_st_0m_00m +
    (7 / 6) * rel5_sh_0m_0mm + (-4 / 3) * rel5_sh_m1_m11 + (-2) * rel5_sh_m1_mm1 +
    (49 / 24) * rel5_mob_0mmm1 + (5 / 4) * rel5_sh_m_000m + (-71 / 24) * rel5_sh_m_001m +
    (325 / 144) * rel5_st_m_001m + (-85 / 24) * rel5_sh_m_00m1 + (167 / 72) * rel5_st_m_00m1 +
    (-91 / 48) * rel5_sh_m_010m + (-11 / 24) * rel5_sh_m_01m1 + (-1 / 6) * rel5_sh_m_0m01 +
    (17 / 24) * rel5_sh_m_0m11 + (23 / 24) * rel5_sh_m_m001 + (-71 / 576) * rel5_st_m_m001 +
    (-37 / 144) * rel5_st_m_m00m + (-31 / 24) * rel5_sh_m_m011 + (-5 / 48) * rel5_sh_m_m101 +
    (8) * rel5_sh_m_m111 + (-1345 / 1152) * rel5_st_01_01m + (-557 / 1152) * rel5_st_01_m0m +
    (35 / 24) * rel5_st_0m_0m1 + (-13 / 3) * rel5_st_0m_0mm + (11 / 24) * rel5_st_0m_m01 +
    (75 / 32) * rel5_sh_m_0001 + (3) * rel5_sh_m_0011 + (-113 / 48) * rel5_st_m_0011 +
    (-37 / 6) * rel5_st_m_00mm + (23 / 8) * rel5_sh_m_0101 + (26 / 9) * rel5_st_m_010m +
    (5 / 72) * rel5_st_m_01m1 + (-85 / 18) * rel5_st_m_0m0m + (37 / 72) * rel5_st_m_0m1m +
    (-5 / 72) * rel5_st_m_m01m + (113 / 576) * rel5_st_m_m0m1 + (71 / 288) * rel5_st_m_m101 +
    (37 / 72) * rel5_st_m_m10m + (-1 / 4) * rel5_st_m_m1m1 + (19 / 48) * rel5_sh_01_00m +
    (-1 / 3) * rel5_sh_01_01m + (5 / 6) * rel5_sh_01_0m1 + (1 / 2) * rel5_st_01_0m1 +
    (1 / 48) * rel5_st_01_0mm + (-4) * rel5_sh_01_m11 + (5 / 48) * rel5_sh_0m_001 +
    (43 / 48) * rel5_sh_0m_01m + (8 / 3) * rel5_sh_m1_011 + (31 / 48) * rel5_sh_m1_0m1 +
    (31 / 48) * rel5_sh_m1_m01 + (-20) * rel5_mob_00mmm + (-47 / 16) * rel5_mob_01mmm +
    (-6) * rel5_mob_0m0mm + (-47 / 48) * rel5_mob_0m1mm + (95 / 48) * rel5_mob_m10mm +
    (11 / 12) * rel5_st_m_011m + (-1 / 6) * rel5_st_m_01mm + (-1 / 48) * rel5_st_m_0m11 +
    (11 / 16) * rel5_st_m_0mm1 + (95 / 48) * rel5_st_m_m011 + (-19 / 6) * rel5_st_m_m0mm +
    (1 / 6) * rel5_st_m_m11m + (1) * rel5_st_m_m1mm + (-23 / 12) * rel5_st_m_mm0m +
    (5 / 6) * rel5_st_m_mm1m + (-4) * rel5_st_m_0mmm + (8) * rel5_mob_0000m

theorem hpl_negOne_zero_one_one_one_at_one :
    hpl [negOne, zero, one, one, one] 1 =
      Li 4 (1 / 2) * log 2 + Li 5 (1 / 2) + 1 / 30 * log 2 ^ 5 - 1 / 36 * log 2 ^ 3 * π ^ 2
      + 7 / 16 * log 2 ^ 2 * zeta3 + 1 / 90 * log 2 * π ^ 4 - 7 / 96 * zeta3 * π ^ 2
      - 27 / 32 * zeta5 := by
  linear_combination (385 / 192) * hpl_zero_zero_zero_zero_one_at_one +
    (1) * hpl_zero_one_one_one_one_at_one + (-21 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 192) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 192) * hpl_zero_one_zero_zero_one_at_one + (1) * hpl_zero_zero_one_one_one_at_one +
    (3 / 4) * hpl_zero_one_zero_one_one_at_one + (1 / 4) * hpl_zero_one_one_zero_one_at_one +
    (-39 / 10) * hpl_zero_zero_zero_zero_negOne_at_one + (1) * hpl_negOne_one_one_one_one_at_one +
    (187 / 960) * rel5_sh_m_mmmm + (-47 / 384) * rel5_sh_m_0mmm + (47 / 1152) * rel5_sh_m_m0mm +
    (1) * rel5_sh_m_m1mm + (-215 / 288) * rel5_sh_m_mm0m + (-223 / 384) * rel5_sh_m_mm1m +
    (95 / 128) * rel5_sh_m_mmm1 + (1217 / 2560) * rel5_st_m_0001 + (-119 / 1152) * rel5_st_m_000m +
    (17 / 12) * rel5_sh_m_00mm + (69 / 64) * rel5_sh_m_01mm + (-9 / 16) * rel5_sh_m_0m0m +
    (31 / 192) * rel5_sh_m_0m1m + (-1 / 3) * rel5_sh_m_0mm1 + (79 / 384) * rel5_sh_m_m01m +
    (-13 / 96) * rel5_sh_m_m0m1 + (191 / 384) * rel5_sh_m_m10m + (3 / 2) * rel5_sh_m_m11m +
    (83 / 48) * rel5_sh_m_m1m1 + (-271 / 192) * rel5_sh_m_mm01 + (767 / 2560) * rel5_st_01_00m +
    (1 / 8) * rel5_st_0m_001 + (-21 / 64) * rel5_sh_0m_00m + (-2191 / 1152) * rel5_st_0m_00m +
    (1 / 8) * rel5_sh_0m_0mm + (-1 / 3) * rel5_sh_m1_m11 + (-1 / 3) * rel5_sh_m1_mm1 +
    (-47 / 96) * rel5_mob_0mmm1 + (61 / 48) * rel5_sh_m_000m + (-21 / 32) * rel5_sh_m_001m +
    (325 / 576) * rel5_st_m_001m + (-85 / 96) * rel5_sh_m_00m1 + (197 / 480) * rel5_st_m_00m1 +
    (-67 / 192) * rel5_sh_m_010m + (-11 / 96) * rel5_sh_m_01m1 + (-1 / 24) * rel5_sh_m_0m01 +
    (-47 / 96) * rel5_sh_m_0m11 + (23 / 96) * rel5_sh_m_m001 + (-289 / 3840) * rel5_st_m_m001 +
    (-37 / 576) * rel5_st_m_m00m + (-95 / 96) * rel5_sh_m_m011 + (-23 / 64) * rel5_sh_m_m101 +
    (3) * rel5_sh_m_m111 + (-573 / 2560) * rel5_st_01_01m + (-1017 / 2560) * rel5_st_01_m0m +
    (17 / 96) * rel5_st_0m_0m1 + (-13 / 12) * rel5_st_0m_0mm + (-31 / 96) * rel5_st_0m_m01 +
    (-5 / 128) * rel5_sh_m_0001 + (3 / 4) * rel5_sh_m_0011 + (-27 / 64) * rel5_st_m_0011 +
    (-37 / 24) * rel5_st_m_00mm + (23 / 32) * rel5_sh_m_0101 + (13 / 18) * rel5_st_m_010m +
    (11 / 480) * rel5_st_m_01m1 + (-85 / 72) * rel5_st_m_0m0m + (37 / 288) * rel5_st_m_0m1m +
    (-5 / 288) * rel5_st_m_m01m + (-313 / 3840) * rel5_st_m_m0m1 + (289 / 1920) * rel5_st_m_m101 +
    (37 / 288) * rel5_st_m_m10m + (-11 / 240) * rel5_st_m_m1m1 + (-29 / 192) * rel5_sh_01_00m +
    (-1 / 12) * rel5_sh_01_01m + (5 / 24) * rel5_sh_01_0m1 + (1 / 8) * rel5_st_01_0m1 +
    (-191 / 192) * rel5_st_01_0mm + (-1) * rel5_sh_01_m11 + (53 / 192) * rel5_sh_0m_001 +
    (67 / 192) * rel5_sh_0m_01m + (2 / 3) * rel5_sh_m1_011 + (95 / 192) * rel5_sh_m1_0m1 +
    (95 / 192) * rel5_sh_m1_m01 + (-5) * rel5_mob_00mmm + (-207 / 64) * rel5_mob_01mmm +
    (-7 / 6) * rel5_mob_0m0mm + (-79 / 192) * rel5_mob_0m1mm + (191 / 192) * rel5_mob_m10mm +
    (11 / 48) * rel5_st_m_011m + (-1 / 24) * rel5_st_m_01mm + (95 / 192) * rel5_st_m_0m11 +
    (1 / 192) * rel5_st_m_0mm1 + (191 / 192) * rel5_st_m_m011 + (-19 / 24) * rel5_st_m_m0mm +
    (1 / 24) * rel5_st_m_m11m + (1 / 4) * rel5_st_m_m1mm + (-23 / 48) * rel5_st_m_mm0m +
    (5 / 24) * rel5_st_m_mm1m + (-1) * rel5_st_m_0mmm + (1) * rel5_st_m_mmmm +
    (-1) * rel5_mob_001mm + (3) * rel5_mob_0000m

theorem hpl_negOne_zero_one_one_negOne_at_one :
    hpl [negOne, zero, one, one, negOne] 1 =
      -3 * Li 4 (1 / 2) * log 2 - 7 * Li 5 (1 / 2) - 1 / 15 * log 2 ^ 5
      + 11 / 72 * log 2 ^ 3 * π ^ 2 - 23 / 480 * log 2 * π ^ 4 + 457 / 64 * zeta5 := by
  linear_combination (-967 / 384) * hpl_zero_zero_zero_zero_one_at_one +
    (147 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (2345 / 384) * hpl_zero_zero_one_zero_one_at_one +
    (1057 / 384) * hpl_zero_one_zero_zero_one_at_one +
    (-7 / 2) * hpl_zero_zero_one_one_one_at_one + (-21 / 8) * hpl_zero_one_zero_one_one_at_one +
    (-7 / 8) * hpl_zero_one_one_zero_one_at_one +
    (115 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-7) * hpl_negOne_one_one_one_one_at_one +
    (1043 / 1920) * rel5_sh_m_mmmm + (89 / 768) * rel5_sh_m_0mmm + (-89 / 2304) * rel5_sh_m_m0mm +
    (-7 / 3) * rel5_sh_m_m1mm + (305 / 576) * rel5_sh_m_mm0m + (227 / 256) * rel5_sh_m_mm1m +
    (87 / 256) * rel5_sh_m_mmm1 + (-267 / 1024) * rel5_st_m_0001 +
    (-4783 / 2304) * rel5_st_m_000m + (-67 / 24) * rel5_sh_m_00mm + (-377 / 384) * rel5_sh_m_01mm +
    (-19 / 96) * rel5_sh_m_0m0m + (-233 / 384) * rel5_sh_m_0m1m + (7 / 6) * rel5_sh_m_0mm1 +
    (-377 / 768) * rel5_sh_m_m01m + (91 / 192) * rel5_sh_m_m0m1 + (-521 / 768) * rel5_sh_m_m10m +
    (-7 / 2) * rel5_sh_m_m11m + (-127 / 32) * rel5_sh_m_m1m1 + (377 / 384) * rel5_sh_m_mm01 +
    (-885 / 1024) * rel5_st_01_00m + (-35 / 24) * rel5_st_0m_001 + (51 / 128) * rel5_sh_0m_00m +
    (10585 / 2304) * rel5_st_0m_00m + (-13 / 48) * rel5_sh_0m_0mm + (7 / 6) * rel5_sh_m1_m11 +
    (1 / 2) * rel5_sh_m1_mm1 + (89 / 192) * rel5_mob_0mmm1 + (-5 / 32) * rel5_sh_m_000m +
    (569 / 192) * rel5_sh_m_001m + (-2275 / 1152) * rel5_st_m_001m + (595 / 192) * rel5_sh_m_00m1 +
    (-1157 / 576) * rel5_st_m_00m1 + (757 / 384) * rel5_sh_m_010m + (77 / 192) * rel5_sh_m_01m1 +
    (7 / 48) * rel5_sh_m_0m01 + (121 / 192) * rel5_sh_m_0m11 + (-161 / 192) * rel5_sh_m_m001 +
    (449 / 4608) * rel5_st_m_m001 + (259 / 1152) * rel5_st_m_m00m + (457 / 192) * rel5_sh_m_m011 +
    (275 / 384) * rel5_sh_m_m101 + (-7) * rel5_sh_m_m111 + (7447 / 9216) * rel5_st_01_01m +
    (971 / 9216) * rel5_st_01_m0m + (-203 / 192) * rel5_st_0m_0m1 + (91 / 24) * rel5_st_0m_0mm +
    (-59 / 192) * rel5_st_0m_m01 + (-589 / 256) * rel5_sh_m_0001 + (-21 / 8) * rel5_sh_m_0011 +
    (551 / 384) * rel5_st_m_0011 + (259 / 48) * rel5_st_m_00mm + (-161 / 64) * rel5_sh_m_0101 +
    (-91 / 36) * rel5_st_m_010m + (-59 / 576) * rel5_st_m_01m1 + (595 / 144) * rel5_st_m_0m0m +
    (-259 / 576) * rel5_st_m_0m1m + (35 / 576) * rel5_st_m_m01m + (985 / 4608) * rel5_st_m_m0m1 +
    (-449 / 2304) * rel5_st_m_m101 + (-259 / 576) * rel5_st_m_m10m + (3 / 32) * rel5_st_m_m1m1 +
    (59 / 384) * rel5_sh_01_00m + (7 / 24) * rel5_sh_01_01m + (-35 / 48) * rel5_sh_01_0m1 +
    (-7 / 16) * rel5_st_01_0m1 + (-247 / 384) * rel5_st_01_0mm + (7 / 2) * rel5_sh_01_m11 +
    (-227 / 384) * rel5_sh_0m_001 + (-373 / 384) * rel5_sh_0m_01m + (-7 / 3) * rel5_sh_m1_011 +
    (-457 / 384) * rel5_sh_m1_0m1 + (-457 / 384) * rel5_sh_m1_m01 + (10) * rel5_mob_00mmm +
    (377 / 128) * rel5_mob_01mmm + (11 / 4) * rel5_mob_0m0mm + (377 / 384) * rel5_mob_0m1mm +
    (-521 / 384) * rel5_mob_m10mm + (-77 / 96) * rel5_st_m_011m + (7 / 48) * rel5_st_m_01mm +
    (-233 / 384) * rel5_st_m_0m11 + (3 / 128) * rel5_st_m_0mm1 + (-521 / 384) * rel5_st_m_m011 +
    (133 / 48) * rel5_st_m_m0mm + (-7 / 48) * rel5_st_m_m11m + (-7 / 8) * rel5_st_m_m1mm +
    (161 / 96) * rel5_st_m_mm0m + (-35 / 48) * rel5_st_m_mm1m + (7 / 2) * rel5_st_m_0mmm +
    (-7) * rel5_mob_0000m

theorem hpl_negOne_zero_one_negOne_one_at_one :
    hpl [negOne, zero, one, negOne, one] 1 =
      11 * Li 5 (1 / 2) - 11 / 120 * log 2 ^ 5 - 7 / 72 * log 2 ^ 3 * π ^ 2
      - 21 / 16 * log 2 ^ 2 * zeta3 + 47 / 480 * log 2 * π ^ 4 + 7 / 32 * zeta3 * π ^ 2
      - 845 / 64 * zeta5 := by
  linear_combination (3803 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (-505 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (-7621 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (-3725 / 1152) * hpl_zero_one_zero_zero_one_at_one + (5) * hpl_zero_zero_one_one_one_at_one +
    (31 / 8) * hpl_zero_one_zero_one_one_at_one + (31 / 24) * hpl_zero_one_one_zero_one_at_one +
    (-151 / 12) * hpl_zero_zero_zero_zero_negOne_at_one +
    (11) * hpl_negOne_one_one_one_one_at_one + (-10369 / 1920) * rel5_sh_m_mmmm +
    (1325 / 768) * rel5_sh_m_0mmm + (-1325 / 2304) * rel5_sh_m_m0mm + (11 / 3) * rel5_sh_m_m1mm +
    (29 / 576) * rel5_sh_m_mm0m + (-561 / 256) * rel5_sh_m_mm1m + (-1709 / 256) * rel5_sh_m_mmm1 +
    (1 / 1024) * rel5_st_m_0001 + (681 / 256) * rel5_st_m_000m + (187 / 72) * rel5_sh_m_00mm +
    (19 / 384) * rel5_sh_m_01mm + (-329 / 288) * rel5_sh_m_0m0m + (115 / 384) * rel5_sh_m_0m1m +
    (-5 / 3) * rel5_sh_m_0mm1 + (19 / 768) * rel5_sh_m_m01m + (-157 / 192) * rel5_sh_m_m0m1 +
    (115 / 768) * rel5_sh_m_m10m + (11 / 2) * rel5_sh_m_m11m + (653 / 96) * rel5_sh_m_m1m1 +
    (-19 / 384) * rel5_sh_m_mm01 + (565 / 3072) * rel5_st_01_00m + (179 / 128) * rel5_st_0m_001 +
    (-535 / 1152) * rel5_sh_0m_00m + (-13735 / 2304) * rel5_st_0m_00m +
    (395 / 144) * rel5_sh_0m_0mm + (-11 / 6) * rel5_sh_m1_m11 + (-53 / 24) * rel5_sh_m1_mm1 +
    (1325 / 192) * rel5_mob_0mmm1 + (-145 / 576) * rel5_sh_m_000m +
    (-1639 / 576) * rel5_sh_m_001m + (2629 / 1152) * rel5_st_m_001m +
    (-1895 / 576) * rel5_sh_m_00m1 + (1277 / 576) * rel5_st_m_00m1 +
    (-593 / 384) * rel5_sh_m_010m + (5 / 192) * rel5_sh_m_01m1 + (17 / 72) * rel5_sh_m_0m01 +
    (47 / 64) * rel5_sh_m_0m11 + (541 / 576) * rel5_sh_m_m001 + (85 / 4608) * rel5_st_m_m001 +
    (-325 / 1152) * rel5_st_m_m00m + (15 / 64) * rel5_sh_m_m011 + (167 / 384) * rel5_sh_m_m101 +
    (11) * rel5_sh_m_m111 + (-3583 / 3072) * rel5_st_01_01m + (-3577 / 9216) * rel5_st_01_m0m +
    (431 / 384) * rel5_st_0m_0m1 + (-163 / 36) * rel5_st_0m_0mm + (239 / 384) * rel5_st_0m_m01 +
    (6779 / 2304) * rel5_sh_m_0001 + (175 / 72) * rel5_sh_m_0011 +
    (-2647 / 1152) * rel5_st_m_0011 + (-863 / 144) * rel5_st_m_00mm +
    (1291 / 576) * rel5_sh_m_0101 + (425 / 144) * rel5_st_m_010m + (-55 / 576) * rel5_st_m_01m1 +
    (-13 / 3) * rel5_st_m_0m0m + (485 / 576) * rel5_st_m_0m1m + (41 / 192) * rel5_st_m_m01m +
    (1517 / 4608) * rel5_st_m_m0m1 + (-85 / 2304) * rel5_st_m_m101 + (325 / 576) * rel5_st_m_m10m +
    (-25 / 96) * rel5_st_m_m1m1 + (1153 / 1152) * rel5_sh_01_00m + (-1 / 6) * rel5_sh_01_01m +
    (13 / 16) * rel5_sh_01_0m1 + (7 / 16) * rel5_st_01_0m1 + (127 / 128) * rel5_st_01_0mm +
    (-49 / 12) * rel5_sh_01_m11 + (-553 / 1152) * rel5_sh_0m_001 + (115 / 128) * rel5_sh_0m_01m +
    (29 / 12) * rel5_sh_m1_011 + (113 / 128) * rel5_sh_m1_0m1 + (-15 / 128) * rel5_sh_m1_m01 +
    (-97 / 4) * rel5_mob_00mmm + (-19 / 128) * rel5_mob_01mmm + (-31 / 4) * rel5_mob_0m0mm +
    (-403 / 384) * rel5_mob_0m1mm + (115 / 384) * rel5_mob_m10mm + (169 / 288) * rel5_st_m_011m +
    (5 / 16) * rel5_st_m_01mm + (-77 / 384) * rel5_st_m_0m11 + (205 / 384) * rel5_st_m_0mm1 +
    (115 / 384) * rel5_st_m_m011 + (-57 / 16) * rel5_st_m_m0mm + (47 / 144) * rel5_st_m_m11m +
    (11 / 8) * rel5_st_m_m1mm + (-541 / 288) * rel5_st_m_mm0m + (179 / 144) * rel5_st_m_mm1m +
    (-5) * rel5_st_m_0mmm + (11) * rel5_mob_0000m

theorem hpl_negOne_zero_one_negOne_negOne_at_one :
    hpl [negOne, zero, one, negOne, negOne] 1 =
      -2 * Li 4 (1 / 2) * log 2 - 7 * Li 5 (1 / 2) - 1 / 40 * log 2 ^ 5
      + 1 / 9 * log 2 ^ 3 * π ^ 2 - 23 / 480 * log 2 * π ^ 4 + 221 / 32 * zeta5 := by
  linear_combination (-967 / 384) * hpl_zero_zero_zero_zero_one_at_one +
    (147 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (2345 / 384) * hpl_zero_zero_one_zero_one_at_one +
    (1057 / 384) * hpl_zero_one_zero_zero_one_at_one +
    (-7 / 2) * hpl_zero_zero_one_one_one_at_one + (-21 / 8) * hpl_zero_one_zero_one_one_at_one +
    (-7 / 8) * hpl_zero_one_one_zero_one_at_one +
    (28 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (-7) * hpl_negOne_one_one_one_one_at_one +
    (11123 / 1920) * rel5_sh_m_mmmm + (-775 / 768) * rel5_sh_m_0mmm +
    (775 / 2304) * rel5_sh_m_m0mm + (-7 / 3) * rel5_sh_m_m1mm + (17 / 576) * rel5_sh_m_mm0m +
    (963 / 256) * rel5_sh_m_mm1m + (1719 / 256) * rel5_sh_m_mmm1 + (-555 / 1024) * rel5_st_m_0001 +
    (-4783 / 2304) * rel5_st_m_000m + (-91 / 24) * rel5_sh_m_00mm + (-281 / 384) * rel5_sh_m_01mm +
    (221 / 96) * rel5_sh_m_0m0m + (-137 / 384) * rel5_sh_m_0m1m + (7 / 6) * rel5_sh_m_0mm1 +
    (-281 / 768) * rel5_sh_m_m01m + (91 / 192) * rel5_sh_m_m0m1 + (-809 / 768) * rel5_sh_m_m10m +
    (-7 / 2) * rel5_sh_m_m11m + (-167 / 32) * rel5_sh_m_m1m1 + (281 / 384) * rel5_sh_m_mm01 +
    (-1045 / 1024) * rel5_st_01_00m + (-37 / 48) * rel5_st_0m_001 + (99 / 128) * rel5_sh_0m_00m +
    (10585 / 2304) * rel5_st_0m_00m + (-109 / 48) * rel5_sh_0m_0mm + (7 / 6) * rel5_sh_m1_m11 +
    (3) * rel5_sh_m1_mm1 + (-775 / 192) * rel5_mob_0mmm1 + (-81 / 32) * rel5_sh_m_000m +
    (521 / 192) * rel5_sh_m_001m + (-2275 / 1152) * rel5_st_m_001m + (595 / 192) * rel5_sh_m_00m1 +
    (-1181 / 576) * rel5_st_m_00m1 + (325 / 384) * rel5_sh_m_010m + (77 / 192) * rel5_sh_m_01m1 +
    (7 / 48) * rel5_sh_m_0m01 + (25 / 192) * rel5_sh_m_0m11 + (-161 / 192) * rel5_sh_m_m001 +
    (545 / 4608) * rel5_st_m_m001 + (259 / 1152) * rel5_st_m_m00m + (361 / 192) * rel5_sh_m_m011 +
    (179 / 384) * rel5_sh_m_m101 + (-7) * rel5_sh_m_m111 + (9079 / 9216) * rel5_st_01_01m +
    (11435 / 9216) * rel5_st_01_m0m + (-215 / 192) * rel5_st_0m_0m1 + (91 / 24) * rel5_st_0m_0mm +
    (121 / 192) * rel5_st_0m_m01 + (-589 / 256) * rel5_sh_m_0001 + (-21 / 8) * rel5_sh_m_0011 +
    (647 / 384) * rel5_st_m_0011 + (259 / 48) * rel5_st_m_00mm + (-161 / 64) * rel5_sh_m_0101 +
    (-91 / 36) * rel5_st_m_010m + (-11 / 576) * rel5_st_m_01m1 + (595 / 144) * rel5_st_m_0m0m +
    (-259 / 576) * rel5_st_m_0m1m + (35 / 576) * rel5_st_m_m01m + (-263 / 4608) * rel5_st_m_m0m1 +
    (-545 / 2304) * rel5_st_m_m101 + (-259 / 576) * rel5_st_m_m10m + (11 / 32) * rel5_st_m_m1m1 +
    (59 / 384) * rel5_sh_01_00m + (7 / 24) * rel5_sh_01_01m + (-35 / 48) * rel5_sh_01_0m1 +
    (-7 / 16) * rel5_st_01_0m1 + (809 / 384) * rel5_st_01_0mm + (7 / 2) * rel5_sh_01_m11 +
    (-227 / 384) * rel5_sh_0m_001 + (-325 / 384) * rel5_sh_0m_01m + (-7 / 3) * rel5_sh_m1_011 +
    (-361 / 384) * rel5_sh_m1_0m1 + (-361 / 384) * rel5_sh_m1_m01 + (25) * rel5_mob_00mmm +
    (281 / 128) * rel5_mob_01mmm + (31 / 4) * rel5_mob_0m0mm + (281 / 384) * rel5_mob_0m1mm +
    (-809 / 384) * rel5_mob_m10mm + (-77 / 96) * rel5_st_m_011m + (7 / 48) * rel5_st_m_01mm +
    (-137 / 384) * rel5_st_m_0m11 + (-29 / 128) * rel5_st_m_0mm1 + (-809 / 384) * rel5_st_m_m011 +
    (133 / 48) * rel5_st_m_m0mm + (-7 / 48) * rel5_st_m_m11m + (-7 / 8) * rel5_st_m_m1mm +
    (161 / 96) * rel5_st_m_mm0m + (-35 / 48) * rel5_st_m_mm1m + (7 / 2) * rel5_st_m_0mmm +
    (-7) * rel5_mob_0000m

theorem hpl_negOne_zero_negOne_zero_one_at_one :
    hpl [negOne, zero, negOne, zero, one] 1 =
      -4 * Li 4 (1 / 2) * log 2 - 4 * Li 5 (1 / 2) - 2 / 15 * log 2 ^ 5
      + 1 / 9 * log 2 ^ 3 * π ^ 2 - 7 / 4 * log 2 ^ 2 * zeta3 + 1 / 480 * log 2 * π ^ 4
      + 1 / 4 * zeta3 * π ^ 2 + 33 / 32 * zeta5 := by
  linear_combination (-377 / 288) * hpl_zero_zero_zero_zero_one_at_one +
    (49 / 12) * hpl_zero_zero_zero_one_one_at_one +
    (895 / 288) * hpl_zero_zero_one_zero_one_at_one +
    (263 / 288) * hpl_zero_one_zero_zero_one_at_one + (-1 / 2) * hpl_zero_one_zero_one_one_at_one +
    (-1 / 6) * hpl_zero_one_one_zero_one_at_one +
    (11 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (1979 / 480) * rel5_sh_m_mmmm + (-31 / 192) * rel5_sh_m_0mmm + (31 / 576) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (113 / 144) * rel5_sh_m_mm0m + (267 / 64) * rel5_sh_m_mm1m +
    (287 / 64) * rel5_sh_m_mmm1 + (-187 / 256) * rel5_st_m_0001 + (-11 / 576) * rel5_st_m_000m +
    (-25 / 18) * rel5_sh_m_00mm + (-161 / 96) * rel5_sh_m_01mm + (293 / 72) * rel5_sh_m_0m0m +
    (-65 / 96) * rel5_sh_m_0m1m + (-161 / 192) * rel5_sh_m_m01m + (5 / 16) * rel5_sh_m_m0m1 +
    (-257 / 192) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m + (-83 / 24) * rel5_sh_m_m1m1 +
    (161 / 96) * rel5_sh_m_mm01 + (-1495 / 768) * rel5_st_01_00m + (113 / 96) * rel5_st_0m_001 +
    (133 / 288) * rel5_sh_0m_00m + (85 / 64) * rel5_st_0m_00m + (-101 / 36) * rel5_sh_0m_0mm +
    (2 / 3) * rel5_sh_m1_m11 + (17 / 6) * rel5_sh_m1_mm1 + (-31 / 48) * rel5_mob_0mmm1 +
    (-725 / 144) * rel5_sh_m_000m + (205 / 144) * rel5_sh_m_001m + (-61 / 96) * rel5_st_m_001m +
    (269 / 144) * rel5_sh_m_00m1 + (-11 / 16) * rel5_st_m_00m1 + (-77 / 96) * rel5_sh_m_010m +
    (41 / 48) * rel5_sh_m_01m1 + (23 / 36) * rel5_sh_m_0m01 + (65 / 48) * rel5_sh_m_0m11 +
    (-79 / 144) * rel5_sh_m_m001 + (67 / 384) * rel5_st_m_m001 + (13 / 96) * rel5_st_m_m00m +
    (161 / 48) * rel5_sh_m_m011 + (131 / 96) * rel5_sh_m_m101 + (-4) * rel5_sh_m_m111 +
    (431 / 2304) * rel5_st_01_01m + (5507 / 2304) * rel5_st_01_m0m + (-25 / 96) * rel5_st_0m_0m1 +
    (23 / 18) * rel5_st_0m_0mm + (167 / 96) * rel5_st_0m_m01 + (-89 / 576) * rel5_sh_m_0001 +
    (-25 / 18) * rel5_sh_m_0011 + (-371 / 288) * rel5_st_m_0011 + (101 / 36) * rel5_st_m_00mm +
    (-277 / 144) * rel5_sh_m_0101 + (-7 / 9) * rel5_st_m_010m + (-3 / 16) * rel5_st_m_01m1 +
    (89 / 36) * rel5_st_m_0m0m + (41 / 144) * rel5_st_m_0m1m + (79 / 144) * rel5_st_m_m01m +
    (139 / 384) * rel5_st_m_m0m1 + (-67 / 192) * rel5_st_m_m101 + (-13 / 48) * rel5_st_m_m10m +
    (7 / 24) * rel5_st_m_m1m1 + (557 / 288) * rel5_sh_01_00m + (1 / 2) * rel5_sh_01_01m +
    (-7 / 12) * rel5_sh_01_0m1 + (-1 / 4) * rel5_st_01_0m1 + (577 / 96) * rel5_st_01_0mm +
    (7 / 3) * rel5_sh_01_m11 + (-581 / 288) * rel5_sh_0m_001 + (-83 / 96) * rel5_sh_0m_01m +
    (-7 / 3) * rel5_sh_m1_011 + (-65 / 96) * rel5_sh_m1_0m1 + (-161 / 96) * rel5_sh_m1_m01 +
    (21) * rel5_mob_00mmm + (161 / 32) * rel5_mob_01mmm + (7) * rel5_mob_0m0mm +
    (161 / 96) * rel5_mob_0m1mm + (-257 / 96) * rel5_mob_m10mm + (-67 / 72) * rel5_st_m_011m +
    (11 / 12) * rel5_st_m_01mm + (-65 / 96) * rel5_st_m_0m11 + (65 / 96) * rel5_st_m_0mm1 +
    (-257 / 96) * rel5_st_m_m011 + (17 / 12) * rel5_st_m_m0mm + (-5 / 36) * rel5_st_m_m11m +
    (-1 / 2) * rel5_st_m_m1mm + (79 / 72) * rel5_st_m_mm0m + (-17 / 36) * rel5_st_m_mm1m +
    (-4) * rel5_mob_0000m

theorem hpl_negOne_zero_negOne_zero_negOne_at_one :
    hpl [negOne, zero, negOne, zero, negOne] 1 =
      4 * Li 4 (1 / 2) * log 2 + 8 * Li 5 (1 / 2) + 1 / 10 * log 2 ^ 5
      - 1 / 18 * log 2 ^ 3 * π ^ 2 + 13 / 288 * log 2 * π ^ 4 - 1 / 48 * zeta3 * π ^ 2
      - 125 / 16 * zeta5 := by
  linear_combination (97 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 2) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 48) * hpl_zero_one_zero_zero_one_at_one + (4) * hpl_zero_zero_one_one_one_at_one +
    (3) * hpl_zero_one_zero_one_one_at_one + (1) * hpl_zero_one_one_zero_one_at_one +
    (-29 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (8) * hpl_negOne_one_one_one_one_at_one +
    (-869 / 240) * rel5_sh_m_mmmm + (49 / 96) * rel5_sh_m_0mmm + (-49 / 288) * rel5_sh_m_m0mm +
    (8 / 3) * rel5_sh_m_m1mm + (-23 / 72) * rel5_sh_m_mm0m + (-85 / 32) * rel5_sh_m_mm1m +
    (-129 / 32) * rel5_sh_m_mmm1 + (13 / 128) * rel5_st_m_0001 + (889 / 288) * rel5_st_m_000m +
    (13 / 3) * rel5_sh_m_00mm + (47 / 48) * rel5_sh_m_01mm + (-23 / 12) * rel5_sh_m_0m0m +
    (-1 / 48) * rel5_sh_m_0m1m + (-4 / 3) * rel5_sh_m_0mm1 + (47 / 96) * rel5_sh_m_m01m +
    (-13 / 24) * rel5_sh_m_m0m1 + (95 / 96) * rel5_sh_m_m10m + (4) * rel5_sh_m_m11m +
    (21 / 4) * rel5_sh_m_m1m1 + (-47 / 48) * rel5_sh_m_mm01 + (83 / 128) * rel5_st_01_00m +
    (11 / 12) * rel5_st_0m_001 + (-13 / 16) * rel5_sh_0m_00m + (-1471 / 288) * rel5_st_0m_00m +
    (7 / 6) * rel5_sh_0m_0mm + (-4 / 3) * rel5_sh_m1_m11 + (-2) * rel5_sh_m1_mm1 +
    (49 / 24) * rel5_mob_0mmm1 + (9 / 4) * rel5_sh_m_000m + (-71 / 24) * rel5_sh_m_001m +
    (325 / 144) * rel5_st_m_001m + (-85 / 24) * rel5_sh_m_00m1 + (167 / 72) * rel5_st_m_00m1 +
    (-43 / 48) * rel5_sh_m_010m + (-11 / 24) * rel5_sh_m_01m1 + (-1 / 6) * rel5_sh_m_0m01 +
    (17 / 24) * rel5_sh_m_0m11 + (23 / 24) * rel5_sh_m_m001 + (-71 / 576) * rel5_st_m_m001 +
    (-37 / 144) * rel5_st_m_m00m + (-31 / 24) * rel5_sh_m_m011 + (-5 / 48) * rel5_sh_m_m101 +
    (8) * rel5_sh_m_m111 + (-1345 / 1152) * rel5_st_01_01m + (-1709 / 1152) * rel5_st_01_m0m +
    (35 / 24) * rel5_st_0m_0m1 + (-13 / 3) * rel5_st_0m_0mm + (-13 / 24) * rel5_st_0m_m01 +
    (107 / 32) * rel5_sh_m_0001 + (3) * rel5_sh_m_0011 + (-113 / 48) * rel5_st_m_0011 +
    (-37 / 6) * rel5_st_m_00mm + (23 / 8) * rel5_sh_m_0101 + (26 / 9) * rel5_st_m_010m +
    (5 / 72) * rel5_st_m_01m1 + (-85 / 18) * rel5_st_m_0m0m + (37 / 72) * rel5_st_m_0m1m +
    (-5 / 72) * rel5_st_m_m01m + (113 / 576) * rel5_st_m_m0m1 + (71 / 288) * rel5_st_m_m101 +
    (37 / 72) * rel5_st_m_m10m + (-1 / 4) * rel5_st_m_m1m1 + (19 / 48) * rel5_sh_01_00m +
    (-1 / 3) * rel5_sh_01_01m + (5 / 6) * rel5_sh_01_0m1 + (1 / 2) * rel5_st_01_0m1 +
    (-95 / 48) * rel5_st_01_0mm + (-4) * rel5_sh_01_m11 + (5 / 48) * rel5_sh_0m_001 +
    (43 / 48) * rel5_sh_0m_01m + (8 / 3) * rel5_sh_m1_011 + (31 / 48) * rel5_sh_m1_0m1 +
    (31 / 48) * rel5_sh_m1_m01 + (-20) * rel5_mob_00mmm + (-47 / 16) * rel5_mob_01mmm +
    (-6) * rel5_mob_0m0mm + (-47 / 48) * rel5_mob_0m1mm + (95 / 48) * rel5_mob_m10mm +
    (11 / 12) * rel5_st_m_011m + (-1 / 6) * rel5_st_m_01mm + (-1 / 48) * rel5_st_m_0m11 +
    (11 / 16) * rel5_st_m_0mm1 + (95 / 48) * rel5_st_m_m011 + (-19 / 6) * rel5_st_m_m0mm +
    (1 / 6) * rel5_st_m_m11m + (1) * rel5_st_m_m1mm + (-23 / 12) * rel5_st_m_mm0m +
    (5 / 6) * rel5_st_m_mm1m + (-4) * rel5_st_m_0mmm + (8) * rel5_mob_0000m

theorem hpl_negOne_zero_negOne_one_one_at_one :
    hpl [negOne, zero, negOne, one, one] 1 =
      2 * Li 4 (1 / 2) * log 2 - 6 * Li 5 (1 / 2) + 2 / 15 * log 2 ^ 5
      - 1 / 24 * log 2 ^ 3 * π ^ 2 + 21 / 16 * log 2 ^ 2 * zeta3
      - 77 / 1440 * log 2 * π ^ 4 - 7 / 32 * zeta3 * π ^ 2 + 61 / 8 * zeta5 := by
  linear_combination (-415 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (23 / 8) * hpl_zero_zero_zero_one_one_at_one + (137 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (31 / 32) * hpl_zero_one_zero_zero_one_at_one + (-5 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-2) * hpl_zero_one_zero_one_one_at_one + (-2 / 3) * hpl_zero_one_one_zero_one_at_one +
    (107 / 15) * hpl_zero_zero_zero_zero_negOne_at_one + (-6) * hpl_negOne_one_one_one_one_at_one +
    (-21 / 10) * rel5_sh_m_mmmm + (5 / 16) * rel5_sh_m_0mmm + (-5 / 48) * rel5_sh_m_m0mm +
    (-2) * rel5_sh_m_m1mm + (11 / 8) * rel5_sh_m_mm0m + (-2 / 3) * rel5_sh_m_mm1m +
    (-11 / 4) * rel5_sh_m_mmm1 + (-1793 / 1920) * rel5_st_m_0001 + (199 / 192) * rel5_st_m_000m +
    (-4 / 3) * rel5_sh_m_00mm + (-37 / 24) * rel5_sh_m_01mm + (1 / 6) * rel5_sh_m_0m0m +
    (-1 / 12) * rel5_sh_m_0m1m + (5 / 6) * rel5_sh_m_0mm1 + (11 / 48) * rel5_sh_m_m01m +
    (7 / 16) * rel5_sh_m_m0m1 + (-1 / 4) * rel5_sh_m_m10m + (-3) * rel5_sh_m_m11m +
    (-131 / 48) * rel5_sh_m_m1m1 + (37 / 24) * rel5_sh_m_mm01 + (47 / 320) * rel5_st_01_00m +
    (-133 / 384) * rel5_st_0m_001 + (89 / 192) * rel5_sh_0m_00m + (631 / 192) * rel5_st_0m_00m +
    (1 / 8) * rel5_sh_0m_0mm + (1) * rel5_sh_m1_m11 + (-19 / 24) * rel5_sh_m1_mm1 +
    (5 / 4) * rel5_mob_0mmm1 + (-199 / 192) * rel5_sh_m_000m + (25 / 96) * rel5_sh_m_001m +
    (-59 / 96) * rel5_st_m_001m + (31 / 48) * rel5_sh_m_00m1 + (-347 / 1440) * rel5_st_m_00m1 +
    (89 / 192) * rel5_sh_m_010m + (-7 / 16) * rel5_sh_m_01m1 + (-25 / 48) * rel5_sh_m_0m01 +
    (1 / 4) * rel5_sh_m_0m11 + (-13 / 48) * rel5_sh_m_m001 + (73 / 1440) * rel5_st_m_m001 +
    (11 / 96) * rel5_st_m_m00m + (1 / 6) * rel5_sh_m_m011 + (-17 / 48) * rel5_sh_m_m101 +
    (-6) * rel5_sh_m_m111 + (713 / 2880) * rel5_st_01_01m + (97 / 2880) * rel5_st_01_m0m +
    (13 / 128) * rel5_st_0m_0m1 + (35 / 24) * rel5_st_0m_0mm + (7 / 384) * rel5_st_0m_m01 +
    (59 / 64) * rel5_sh_m_0001 + (5 / 6) * rel5_st_m_0011 + (17 / 12) * rel5_st_m_00mm +
    (1 / 12) * rel5_sh_m_0101 + (-41 / 48) * rel5_st_m_010m + (23 / 180) * rel5_st_m_01m1 +
    (13 / 16) * rel5_st_m_0m0m + (-9 / 16) * rel5_st_m_0m1m + (-17 / 48) * rel5_st_m_m01m +
    (-289 / 1440) * rel5_st_m_m0m1 + (-73 / 720) * rel5_st_m_m101 + (-11 / 48) * rel5_st_m_m10m +
    (-13 / 240) * rel5_st_m_m1m1 + (-11 / 32) * rel5_sh_01_00m + (-1 / 8) * rel5_sh_01_01m +
    (-5 / 24) * rel5_sh_01_0m1 + (-1 / 8) * rel5_st_01_0m1 + (1 / 8) * rel5_st_01_0mm +
    (5 / 4) * rel5_sh_01_m11 + (7 / 32) * rel5_sh_0m_001 + (-53 / 192) * rel5_sh_0m_01m +
    (-5 / 12) * rel5_sh_m1_011 + (-3 / 4) * rel5_sh_m1_0m1 + (5 / 12) * rel5_sh_m1_m01 +
    (13 / 4) * rel5_mob_00mmm + (37 / 8) * rel5_mob_01mmm + (1 / 6) * rel5_mob_0m0mm +
    (13 / 24) * rel5_mob_0m1mm + (-1 / 2) * rel5_mob_m10mm + (1 / 8) * rel5_st_m_011m +
    (-7 / 12) * rel5_st_m_01mm + (-7 / 12) * rel5_st_m_0m11 + (-1 / 3) * rel5_st_m_0mm1 +
    (-1 / 2) * rel5_st_m_m011 + (17 / 12) * rel5_st_m_m0mm + (-1 / 6) * rel5_st_m_m11m +
    (-3 / 4) * rel5_st_m_m1mm + (13 / 24) * rel5_st_m_mm0m + (-2 / 3) * rel5_st_m_mm1m +
    (5 / 2) * rel5_st_m_0mmm + (2) * rel5_mob_001mm + (-6) * rel5_mob_0000m

theorem hpl_negOne_zero_negOne_one_negOne_at_one :
    hpl [negOne, zero, negOne, one, negOne] 1 =
      8 * Li 5 (1 / 2) - 1 / 15 * log 2 ^ 5 - 5 / 36 * log 2 ^ 3 * π ^ 2
      + 23 / 360 * log 2 * π ^ 4 - 61 / 8 * zeta5 := by
  linear_combination (241 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 2) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 48) * hpl_zero_one_zero_zero_one_at_one + (4) * hpl_zero_zero_one_one_one_at_one +
    (3) * hpl_zero_one_zero_one_one_at_one + (1) * hpl_zero_one_one_zero_one_at_one +
    (-38 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (8) * hpl_negOne_one_one_one_one_at_one +
    (-509 / 240) * rel5_sh_m_mmmm + (-23 / 96) * rel5_sh_m_0mmm + (23 / 288) * rel5_sh_m_m0mm +
    (8 / 3) * rel5_sh_m_m1mm + (-95 / 72) * rel5_sh_m_mm0m + (-109 / 32) * rel5_sh_m_mm1m +
    (-57 / 32) * rel5_sh_m_mmm1 + (213 / 128) * rel5_st_m_0001 + (169 / 288) * rel5_st_m_000m +
    (13 / 3) * rel5_sh_m_00mm + (119 / 48) * rel5_sh_m_01mm + (-23 / 12) * rel5_sh_m_0m0m +
    (71 / 48) * rel5_sh_m_0m1m + (-4 / 3) * rel5_sh_m_0mm1 + (119 / 96) * rel5_sh_m_m01m +
    (-13 / 24) * rel5_sh_m_m0m1 + (167 / 96) * rel5_sh_m_m10m + (4) * rel5_sh_m_m11m +
    (21 / 4) * rel5_sh_m_m1m1 + (-119 / 48) * rel5_sh_m_mm01 + (283 / 128) * rel5_st_01_00m +
    (19 / 24) * rel5_st_0m_001 + (-17 / 16) * rel5_sh_0m_00m + (-1615 / 288) * rel5_st_0m_00m +
    (7 / 6) * rel5_sh_0m_0mm + (-4 / 3) * rel5_sh_m1_m11 + (-2) * rel5_sh_m1_mm1 +
    (-23 / 24) * rel5_mob_0mmm1 + (9 / 2) * rel5_sh_m_000m + (-83 / 24) * rel5_sh_m_001m +
    (325 / 144) * rel5_st_m_001m + (-85 / 24) * rel5_sh_m_00m1 + (167 / 72) * rel5_st_m_00m1 +
    (-55 / 48) * rel5_sh_m_010m + (-11 / 24) * rel5_sh_m_01m1 + (-1 / 6) * rel5_sh_m_0m01 +
    (-55 / 24) * rel5_sh_m_0m11 + (23 / 24) * rel5_sh_m_m001 + (-143 / 576) * rel5_st_m_m001 +
    (-37 / 144) * rel5_st_m_m00m + (-103 / 24) * rel5_sh_m_m011 + (-77 / 48) * rel5_sh_m_m101 +
    (8) * rel5_sh_m_m111 + (-985 / 1152) * rel5_st_01_01m + (-1637 / 1152) * rel5_st_01_m0m +
    (5 / 6) * rel5_st_0m_0m1 + (-13 / 3) * rel5_st_0m_0mm + (-7 / 6) * rel5_st_0m_m01 +
    (27 / 32) * rel5_sh_m_0001 + (3) * rel5_sh_m_0011 + (-41 / 48) * rel5_st_m_0011 +
    (-37 / 6) * rel5_st_m_00mm + (23 / 8) * rel5_sh_m_0101 + (26 / 9) * rel5_st_m_010m +
    (5 / 72) * rel5_st_m_01m1 + (-85 / 18) * rel5_st_m_0m0m + (37 / 72) * rel5_st_m_0m1m +
    (-5 / 72) * rel5_st_m_m01m + (-247 / 576) * rel5_st_m_m0m1 + (143 / 288) * rel5_st_m_m101 +
    (37 / 72) * rel5_st_m_m10m + (-1 / 4) * rel5_st_m_m1m1 + (-77 / 48) * rel5_sh_01_00m +
    (-1 / 3) * rel5_sh_01_01m + (5 / 6) * rel5_sh_01_0m1 + (1 / 2) * rel5_st_01_0m1 +
    (-167 / 48) * rel5_st_01_0mm + (-4) * rel5_sh_01_m11 + (101 / 48) * rel5_sh_0m_001 +
    (55 / 48) * rel5_sh_0m_01m + (8 / 3) * rel5_sh_m1_011 + (103 / 48) * rel5_sh_m1_0m1 +
    (103 / 48) * rel5_sh_m1_m01 + (-20) * rel5_mob_00mmm + (-119 / 16) * rel5_mob_01mmm +
    (-6) * rel5_mob_0m0mm + (-119 / 48) * rel5_mob_0m1mm + (167 / 48) * rel5_mob_m10mm +
    (11 / 12) * rel5_st_m_011m + (-1 / 6) * rel5_st_m_01mm + (71 / 48) * rel5_st_m_0m11 +
    (-13 / 16) * rel5_st_m_0mm1 + (167 / 48) * rel5_st_m_m011 + (-19 / 6) * rel5_st_m_m0mm +
    (1 / 6) * rel5_st_m_m11m + (1) * rel5_st_m_m1mm + (-23 / 12) * rel5_st_m_mm0m +
    (5 / 6) * rel5_st_m_mm1m + (-4) * rel5_st_m_0mmm + (8) * rel5_mob_0000m

theorem hpl_negOne_zero_negOne_negOne_one_at_one :
    hpl [negOne, zero, negOne, negOne, one] 1 =
      -Li 4 (1 / 2) * log 2 - 4 * Li 5 (1 / 2) - 1 / 120 * log 2 ^ 5
      + 1 / 9 * log 2 ^ 3 * π ^ 2 - 21 / 16 * log 2 ^ 2 * zeta3 - 1 / 72 * log 2 * π ^ 4
      + 7 / 32 * zeta3 * π ^ 2 + 35 / 32 * zeta5 := by
  linear_combination (-77 / 24) * hpl_zero_zero_zero_zero_one_at_one +
    (55 / 8) * hpl_zero_zero_zero_one_one_at_one + (227 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (97 / 48) * hpl_zero_one_zero_zero_one_at_one + (-2) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 2) * hpl_zero_one_zero_one_one_at_one + (-1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (35 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (1627 / 240) * rel5_sh_m_mmmm + (-155 / 96) * rel5_sh_m_0mmm + (155 / 288) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (43 / 72) * rel5_sh_m_mm0m + (155 / 32) * rel5_sh_m_mm1m +
    (255 / 32) * rel5_sh_m_mmm1 + (-97 / 128) * rel5_st_m_0001 + (-91 / 144) * rel5_st_m_000m +
    (-5 / 2) * rel5_sh_m_00mm + (-61 / 48) * rel5_sh_m_01mm + (49 / 16) * rel5_sh_m_0m0m +
    (-49 / 48) * rel5_sh_m_0m1m + (2 / 3) * rel5_sh_m_0mm1 + (-61 / 96) * rel5_sh_m_m01m +
    (5 / 6) * rel5_sh_m_m0m1 + (-97 / 96) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-31 / 8) * rel5_sh_m_m1m1 + (61 / 48) * rel5_sh_m_mm01 + (-165 / 128) * rel5_st_01_00m +
    (41 / 192) * rel5_st_0m_001 + (65 / 96) * rel5_sh_0m_00m + (553 / 144) * rel5_st_0m_00m +
    (-19 / 6) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (15 / 4) * rel5_sh_m1_mm1 +
    (-155 / 24) * rel5_mob_0mmm1 + (-347 / 96) * rel5_sh_m_000m + (103 / 48) * rel5_sh_m_001m +
    (-109 / 72) * rel5_st_m_001m + (29 / 12) * rel5_sh_m_00m1 + (-209 / 144) * rel5_st_m_00m1 +
    (1 / 96) * rel5_sh_m_010m + (5 / 12) * rel5_sh_m_01m1 + (17 / 48) * rel5_sh_m_0m01 +
    (29 / 24) * rel5_sh_m_0m11 + (-7 / 12) * rel5_sh_m_m001 + (61 / 576) * rel5_st_m_m001 +
    (5 / 36) * rel5_st_m_m00m + (65 / 24) * rel5_sh_m_m011 + (49 / 48) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (815 / 1152) * rel5_st_01_01m + (2011 / 1152) * rel5_st_01_m0m +
    (-95 / 192) * rel5_st_0m_0m1 + (65 / 24) * rel5_st_0m_0mm + (193 / 192) * rel5_st_0m_m01 +
    (-37 / 48) * rel5_sh_m_0001 + (-7 / 3) * rel5_sh_m_0011 + (23 / 48) * rel5_st_m_0011 +
    (25 / 6) * rel5_st_m_00mm + (-107 / 48) * rel5_sh_m_0101 + (-271 / 144) * rel5_st_m_010m +
    (-1 / 72) * rel5_st_m_01m1 + (463 / 144) * rel5_st_m_0m0m + (-7 / 36) * rel5_st_m_0m1m +
    (13 / 72) * rel5_st_m_m01m + (125 / 576) * rel5_st_m_m0m1 + (-61 / 288) * rel5_st_m_m101 +
    (-5 / 18) * rel5_st_m_m10m + (3 / 8) * rel5_st_m_m1m1 + (11 / 16) * rel5_sh_01_00m +
    (7 / 24) * rel5_sh_01_01m + (-13 / 24) * rel5_sh_01_0m1 + (-1 / 4) * rel5_st_01_0m1 +
    (175 / 48) * rel5_st_01_0mm + (5 / 2) * rel5_sh_01_m11 + (-17 / 16) * rel5_sh_0m_001 +
    (-79 / 96) * rel5_sh_0m_01m + (-11 / 6) * rel5_sh_m1_011 + (-53 / 48) * rel5_sh_m1_0m1 +
    (-65 / 48) * rel5_sh_m1_m01 + (53 / 2) * rel5_mob_00mmm + (61 / 16) * rel5_mob_01mmm +
    (9) * rel5_mob_0m0mm + (109 / 48) * rel5_mob_0m1mm + (-97 / 48) * rel5_mob_m10mm +
    (-2 / 3) * rel5_st_m_011m + (1 / 3) * rel5_st_m_01mm + (-25 / 48) * rel5_st_m_0m11 +
    (11 / 16) * rel5_st_m_0mm1 + (-97 / 48) * rel5_st_m_m011 + (11 / 6) * rel5_st_m_m0mm +
    (-1 / 6) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm + (7 / 6) * rel5_st_m_mm0m +
    (-1 / 2) * rel5_st_m_mm1m + (2) * rel5_st_m_0mmm + (-4) * rel5_mob_0000m

theorem hpl_negOne_zero_negOne_negOne_negOne_at_one :
    hpl [negOne, zero, negOne, negOne, negOne] 1 =
      3 * Li 4 (1 / 2) * log 2 + 4 * Li 5 (1 / 2) + 11 / 120 * log 2 ^ 5
      - 5 / 72 * log 2 ^ 3 * π ^ 2 + 7 / 8 * log 2 ^ 2 * zeta3 + 1 / 90 * log 2 * π ^ 4
      - 4 * zeta5 := by
  linear_combination (97 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 4) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 96) * hpl_zero_one_zero_zero_one_at_one + (2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 2) * hpl_zero_one_zero_one_one_at_one + (1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (-74 / 15) * hpl_zero_zero_zero_zero_negOne_at_one + (4) * hpl_negOne_one_one_one_one_at_one +
    (-2021 / 480) * rel5_sh_m_mmmm + (241 / 192) * rel5_sh_m_0mmm + (-49 / 576) * rel5_sh_m_m0mm +
    (4 / 3) * rel5_sh_m_m1mm + (-23 / 144) * rel5_sh_m_mm0m + (-149 / 64) * rel5_sh_m_mm1m +
    (-321 / 64) * rel5_sh_m_mmm1 + (129 / 1280) * rel5_st_m_0001 + (889 / 576) * rel5_st_m_000m +
    (13 / 6) * rel5_sh_m_00mm + (47 / 96) * rel5_sh_m_01mm + (-35 / 24) * rel5_sh_m_0m0m +
    (-1 / 96) * rel5_sh_m_0m1m + (-2 / 3) * rel5_sh_m_0mm1 + (47 / 192) * rel5_sh_m_m01m +
    (-13 / 48) * rel5_sh_m_m0m1 + (95 / 192) * rel5_sh_m_m10m + (2) * rel5_sh_m_m11m +
    (25 / 8) * rel5_sh_m_m1m1 + (-47 / 96) * rel5_sh_m_mm01 + (479 / 1280) * rel5_st_01_00m +
    (11 / 24) * rel5_st_0m_001 + (-13 / 32) * rel5_sh_0m_00m + (-1471 / 576) * rel5_st_0m_00m +
    (19 / 12) * rel5_sh_0m_0mm + (-2 / 3) * rel5_sh_m1_m11 + (-2) * rel5_sh_m1_mm1 +
    (241 / 48) * rel5_mob_0mmm1 + (9 / 8) * rel5_sh_m_000m + (-71 / 48) * rel5_sh_m_001m +
    (325 / 288) * rel5_st_m_001m + (-85 / 48) * rel5_sh_m_00m1 + (847 / 720) * rel5_st_m_00m1 +
    (-43 / 96) * rel5_sh_m_010m + (-11 / 48) * rel5_sh_m_01m1 + (-1 / 12) * rel5_sh_m_0m01 +
    (17 / 48) * rel5_sh_m_0m11 + (23 / 48) * rel5_sh_m_m001 + (-259 / 5760) * rel5_st_m_m001 +
    (-37 / 288) * rel5_st_m_m00m + (-31 / 48) * rel5_sh_m_m011 + (-5 / 96) * rel5_sh_m_m101 +
    (4) * rel5_sh_m_m111 + (-7109 / 11520) * rel5_st_01_01m + (-8161 / 11520) * rel5_st_01_m0m +
    (35 / 48) * rel5_st_0m_0m1 + (-13 / 6) * rel5_st_0m_0mm + (-13 / 48) * rel5_st_0m_m01 +
    (107 / 64) * rel5_sh_m_0001 + (3 / 2) * rel5_sh_m_0011 + (-113 / 96) * rel5_st_m_0011 +
    (-37 / 12) * rel5_st_m_00mm + (23 / 16) * rel5_sh_m_0101 + (13 / 9) * rel5_st_m_010m +
    (1 / 720) * rel5_st_m_01m1 + (-85 / 36) * rel5_st_m_0m0m + (37 / 144) * rel5_st_m_0m1m +
    (-5 / 144) * rel5_st_m_m01m + (757 / 5760) * rel5_st_m_m0m1 + (259 / 2880) * rel5_st_m_m101 +
    (37 / 144) * rel5_st_m_m10m + (-9 / 40) * rel5_st_m_m1m1 + (19 / 96) * rel5_sh_01_00m +
    (-1 / 6) * rel5_sh_01_01m + (5 / 12) * rel5_sh_01_0m1 + (1 / 4) * rel5_st_01_0m1 +
    (-95 / 96) * rel5_st_01_0mm + (-2) * rel5_sh_01_m11 + (5 / 96) * rel5_sh_0m_001 +
    (43 / 96) * rel5_sh_0m_01m + (4 / 3) * rel5_sh_m1_011 + (31 / 96) * rel5_sh_m1_0m1 +
    (31 / 96) * rel5_sh_m1_m01 + (-16) * rel5_mob_00mmm + (-47 / 32) * rel5_mob_01mmm +
    (-5) * rel5_mob_0m0mm + (-47 / 96) * rel5_mob_0m1mm + (95 / 96) * rel5_mob_m10mm +
    (11 / 24) * rel5_st_m_011m + (-1 / 12) * rel5_st_m_01mm + (-1 / 96) * rel5_st_m_0m11 +
    (11 / 32) * rel5_st_m_0mm1 + (95 / 96) * rel5_st_m_m011 + (-19 / 12) * rel5_st_m_m0mm +
    (1 / 12) * rel5_st_m_m11m + (1 / 2) * rel5_st_m_m1mm + (-23 / 24) * rel5_st_m_mm0m +
    (5 / 12) * rel5_st_m_mm1m + (-2) * rel5_st_m_0mmm + (4) * rel5_mob_0000m

theorem hpl_negOne_one_zero_zero_one_at_one :
    hpl [negOne, one, zero, zero, one] 1 =
      -2 * Li 5 (1 / 2) + 1 / 60 * log 2 ^ 5 - 1 / 36 * log 2 ^ 3 * π ^ 2
      + 3 / 8 * log 2 ^ 2 * zeta3 - 1 / 60 * log 2 * π ^ 4 - 11 / 48 * zeta3 * π ^ 2
      + 311 / 64 * zeta5 := by
  linear_combination (-121 / 72) * hpl_zero_zero_zero_zero_one_at_one +
    (11 / 3) * hpl_zero_zero_zero_one_one_at_one +
    (283 / 144) * hpl_zero_zero_one_zero_one_at_one +
    (191 / 144) * hpl_zero_one_zero_zero_one_at_one + (-3 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-1) * hpl_zero_one_zero_one_one_at_one + (-1 / 3) * hpl_zero_one_one_zero_one_at_one +
    (13 / 4) * hpl_zero_zero_zero_zero_negOne_at_one + (-2) * hpl_negOne_one_one_one_one_at_one +
    (157 / 480) * rel5_sh_m_mmmm + (-29 / 192) * rel5_sh_m_0mmm + (29 / 576) * rel5_sh_m_m0mm +
    (-2 / 3) * rel5_sh_m_m1mm + (-11 / 144) * rel5_sh_m_mm0m + (-3 / 64) * rel5_sh_m_mm1m +
    (25 / 64) * rel5_sh_m_mmm1 + (-91 / 256) * rel5_st_m_0001 + (-11 / 72) * rel5_st_m_000m +
    (2 / 9) * rel5_sh_m_00mm + (5 / 96) * rel5_sh_m_01mm + (101 / 144) * rel5_sh_m_0m0m +
    (17 / 96) * rel5_sh_m_0m1m + (1 / 2) * rel5_sh_m_0mm1 + (5 / 192) * rel5_sh_m_m01m +
    (1 / 8) * rel5_sh_m_m0m1 + (-7 / 192) * rel5_sh_m_m10m + (-1) * rel5_sh_m_m11m +
    (-53 / 48) * rel5_sh_m_m1m1 + (-5 / 96) * rel5_sh_m_mm01 + (-437 / 768) * rel5_st_01_00m +
    (-125 / 384) * rel5_st_0m_001 + (37 / 576) * rel5_sh_0m_00m + (11 / 6) * rel5_st_0m_00m +
    (-35 / 72) * rel5_sh_0m_0mm + (1 / 3) * rel5_sh_m1_m11 + (1 / 24) * rel5_sh_m1_mm1 +
    (-29 / 48) * rel5_mob_0mmm1 + (-337 / 576) * rel5_sh_m_000m + (145 / 288) * rel5_sh_m_001m +
    (-7 / 16) * rel5_st_m_001m + (10 / 9) * rel5_sh_m_00m1 + (-43 / 96) * rel5_st_m_00m1 +
    (31 / 192) * rel5_sh_m_010m + (-1 / 24) * rel5_sh_m_01m1 + (1 / 36) * rel5_sh_m_0m01 +
    (-29 / 48) * rel5_sh_m_0m11 + (-2 / 9) * rel5_sh_m_m001 + (1 / 384) * rel5_st_m_m001 +
    (9 / 16) * rel5_st_m_m00m + (-17 / 48) * rel5_sh_m_m011 + (-29 / 96) * rel5_sh_m_m101 +
    (-2) * rel5_sh_m_m111 + (181 / 2304) * rel5_st_01_01m + (625 / 2304) * rel5_st_01_m0m +
    (-113 / 384) * rel5_st_0m_0m1 + (14 / 9) * rel5_st_0m_0mm + (-17 / 384) * rel5_st_0m_m01 +
    (-103 / 144) * rel5_sh_m_0001 + (-23 / 18) * rel5_sh_m_0011 + (-85 / 288) * rel5_st_m_0011 +
    (19 / 9) * rel5_st_m_00mm + (-35 / 36) * rel5_sh_m_0101 + (-55 / 72) * rel5_st_m_010m +
    (1 / 48) * rel5_st_m_01m1 + (55 / 36) * rel5_st_m_0m0m + (-19 / 72) * rel5_st_m_0m1m +
    (-1 / 9) * rel5_st_m_m01m + (-21 / 128) * rel5_st_m_m0m1 + (-1 / 192) * rel5_st_m_m101 +
    (-1 / 8) * rel5_st_m_m10m + (1 / 48) * rel5_st_m_m1m1 + (71 / 144) * rel5_sh_01_00m +
    (1 / 2) * rel5_sh_01_01m + (-1 / 6) * rel5_sh_01_0m1 + (-1 / 8) * rel5_st_01_0m1 +
    (47 / 96) * rel5_st_01_0mm + (11 / 12) * rel5_sh_01_m11 + (-59 / 144) * rel5_sh_0m_001 +
    (-71 / 192) * rel5_sh_0m_01m + (-5 / 12) * rel5_sh_m1_011 + (-7 / 96) * rel5_sh_m1_0m1 +
    (17 / 96) * rel5_sh_m1_m01 + (9 / 4) * rel5_mob_00mmm + (-5 / 32) * rel5_mob_01mmm +
    (1 / 2) * rel5_mob_0m0mm + (-5 / 96) * rel5_mob_0m1mm + (-7 / 96) * rel5_mob_m10mm +
    (-1 / 9) * rel5_st_m_011m + (-1 / 6) * rel5_st_m_01mm + (17 / 96) * rel5_st_m_0m11 +
    (-41 / 96) * rel5_st_m_0mm1 + (-7 / 96) * rel5_st_m_m011 + (5 / 6) * rel5_st_m_m0mm +
    (-1 / 36) * rel5_st_m_m11m + (-1 / 4) * rel5_st_m_m1mm + (4 / 9) * rel5_st_m_mm0m +
    (-7 / 36) * rel5_st_m_mm1m + (3 / 2) * rel5_st_m_0mmm + (-2) * rel5_mob_0000m

theorem hpl_negOne_one_zero_zero_negOne_at_one :
    hpl [negOne, one, zero, zero, negOne] 1 =
      -3 / 8 * log 2 ^ 2 * zeta3 + 1 / 288 * log 2 * π ^ 4 - 1 / 48 * zeta3 * π ^ 2
      + 15 / 32 * zeta5 := by
  linear_combination (1 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (-1 / 8) * rel5_st_m_0001 +
    (1 / 4) * rel5_st_m_000m + (-3 / 8) * rel5_st_0m_001 + (1 / 4) * rel5_sh_0m_00m +
    (-1 / 4) * rel5_st_0m_00m + (-3 / 4) * rel5_sh_m_000m + (-1 / 2) * rel5_sh_m_001m +
    (-1 / 4) * rel5_sh_m_010m + (1 / 2) * rel5_st_m_m001 + (1 / 8) * rel5_st_0m_0m1 +
    (1 / 8) * rel5_st_0m_m01 + (1 / 4) * rel5_sh_m_0001 + (1 / 2) * rel5_sh_01_00m +
    (-1 / 2) * rel5_sh_0m_001 + (1 / 4) * rel5_sh_0m_01m

theorem hpl_negOne_one_zero_one_one_at_one :
    hpl [negOne, one, zero, one, one] 1 =
      -3 * Li 4 (1 / 2) * log 2 - 4 * Li 5 (1 / 2) - 11 / 120 * log 2 ^ 5
      + 5 / 72 * log 2 ^ 3 * π ^ 2 - 11 / 8 * log 2 ^ 2 * zeta3 - 1 / 288 * log 2 * π ^ 4
      + 11 / 48 * zeta3 * π ^ 2 + 81 / 64 * zeta5 := by
  linear_combination (-793 / 576) * hpl_zero_zero_zero_zero_one_at_one +
    (41 / 24) * hpl_zero_zero_zero_one_one_at_one +
    (707 / 576) * hpl_zero_zero_one_zero_one_at_one +
    (283 / 576) * hpl_zero_one_zero_zero_one_at_one + (-1 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-1 / 4) * hpl_zero_one_zero_one_one_at_one + (-1 / 4) * hpl_zero_one_one_zero_one_at_one +
    (289 / 60) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (-1571 / 960) * rel5_sh_m_mmmm + (319 / 384) * rel5_sh_m_0mmm +
    (-319 / 1152) * rel5_sh_m_m0mm + (-4 / 3) * rel5_sh_m_m1mm + (259 / 288) * rel5_sh_m_mm0m +
    (7 / 384) * rel5_sh_m_mm1m + (-295 / 128) * rel5_sh_m_mmm1 + (-3751 / 7680) * rel5_st_m_0001 +
    (293 / 1152) * rel5_st_m_000m + (-29 / 36) * rel5_sh_m_00mm + (-239 / 192) * rel5_sh_m_01mm +
    (65 / 72) * rel5_sh_m_0m0m + (3 / 64) * rel5_sh_m_0m1m + (1 / 6) * rel5_sh_m_0mm1 +
    (-47 / 384) * rel5_sh_m_m01m + (1 / 32) * rel5_sh_m_m0m1 + (-199 / 384) * rel5_sh_m_m10m +
    (-2) * rel5_sh_m_m11m + (-23 / 12) * rel5_sh_m_m1m1 + (239 / 192) * rel5_sh_m_mm01 +
    (-3661 / 7680) * rel5_st_01_00m + (19 / 128) * rel5_st_0m_001 + (67 / 288) * rel5_sh_0m_00m +
    (431 / 384) * rel5_st_0m_00m + (-1 / 18) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 +
    (-3 / 8) * rel5_sh_m1_mm1 + (319 / 96) * rel5_mob_0mmm1 + (-935 / 576) * rel5_sh_m_000m +
    (37 / 144) * rel5_sh_m_001m + (-41 / 192) * rel5_st_m_001m + (181 / 288) * rel5_sh_m_00m1 +
    (-17 / 180) * rel5_st_m_00m1 + (1 / 32) * rel5_sh_m_010m + (13 / 96) * rel5_sh_m_01m1 +
    (7 / 72) * rel5_sh_m_0m01 + (31 / 96) * rel5_sh_m_0m11 + (-71 / 288) * rel5_sh_m_m001 +
    (1027 / 11520) * rel5_st_m_m001 + (17 / 192) * rel5_st_m_m00m + (29 / 32) * rel5_sh_m_m011 +
    (11 / 64) * rel5_sh_m_m101 + (-4) * rel5_sh_m_m111 + (517 / 23040) * rel5_st_01_01m +
    (4171 / 7680) * rel5_st_01_m0m + (-31 / 384) * rel5_st_0m_0m1 + (25 / 36) * rel5_st_0m_0mm +
    (193 / 384) * rel5_st_0m_m01 + (191 / 1152) * rel5_sh_m_0001 + (-23 / 36) * rel5_sh_m_0011 +
    (-133 / 576) * rel5_st_m_0011 + (73 / 72) * rel5_st_m_00mm + (-173 / 288) * rel5_sh_m_0101 +
    (-29 / 72) * rel5_st_m_010m + (-73 / 1440) * rel5_st_m_01m1 + (73 / 72) * rel5_st_m_0m0m +
    (-11 / 288) * rel5_st_m_0m1m + (23 / 288) * rel5_st_m_m01m + (59 / 11520) * rel5_st_m_m0m1 +
    (-1027 / 5760) * rel5_st_m_m101 + (-17 / 96) * rel5_st_m_m10m + (-1 / 60) * rel5_st_m_m1m1 +
    (313 / 576) * rel5_sh_01_00m + (1 / 4) * rel5_sh_01_01m + (-1 / 8) * rel5_sh_01_0m1 +
    (-1 / 4) * rel5_st_01_0m1 + (311 / 192) * rel5_st_01_0mm + (13 / 12) * rel5_sh_01_m11 +
    (-289 / 576) * rel5_sh_0m_001 + (-31 / 96) * rel5_sh_0m_01m + (-11 / 12) * rel5_sh_m1_011 +
    (-55 / 192) * rel5_sh_m1_0m1 + (-13 / 64) * rel5_sh_m1_m01 + (11 / 4) * rel5_mob_00mmm +
    (239 / 64) * rel5_mob_01mmm + (1 / 3) * rel5_mob_0m0mm + (47 / 192) * rel5_mob_0m1mm +
    (-199 / 192) * rel5_mob_m10mm + (-35 / 144) * rel5_st_m_011m + (1 / 8) * rel5_st_m_01mm +
    (-29 / 64) * rel5_st_m_0m11 + (-25 / 192) * rel5_st_m_0mm1 + (-199 / 192) * rel5_st_m_m011 +
    (3 / 8) * rel5_st_m_m0mm + (-7 / 72) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm +
    (71 / 144) * rel5_st_m_mm0m + (-31 / 72) * rel5_st_m_mm1m + (1 / 2) * rel5_st_m_0mmm +
    (1) * rel5_mob_001mm + (-4) * rel5_mob_0000m

theorem hpl_negOne_one_zero_one_negOne_at_one :
    hpl [negOne, one, zero, one, negOne] 1 =
      7 * Li 4 (1 / 2) * log 2 + 16 * Li 5 (1 / 2) + 19 / 120 * log 2 ^ 5
      - 7 / 36 * log 2 ^ 3 * π ^ 2 + 1 / 2 * log 2 ^ 2 * zeta3 + 47 / 480 * log 2 * π ^ 4
      - 1 / 12 * zeta3 * π ^ 2 - 245 / 16 * zeta5 := by
  linear_combination (217 / 24) * hpl_zero_zero_zero_zero_one_at_one +
    (-21) * hpl_zero_zero_zero_one_one_at_one + (-335 / 24) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 24) * hpl_zero_one_zero_zero_one_at_one + (8) * hpl_zero_zero_one_one_one_at_one +
    (6) * hpl_zero_one_zero_one_one_at_one + (2) * hpl_zero_one_one_zero_one_at_one +
    (-73 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (16) * hpl_negOne_one_one_one_one_at_one +
    (-689 / 120) * rel5_sh_m_mmmm + (13 / 48) * rel5_sh_m_0mmm + (-13 / 144) * rel5_sh_m_m0mm +
    (16 / 3) * rel5_sh_m_m1mm + (-59 / 36) * rel5_sh_m_mm0m + (-97 / 16) * rel5_sh_m_mm1m +
    (-93 / 16) * rel5_sh_m_mmm1 + (185 / 64) * rel5_st_m_0001 + (349 / 144) * rel5_st_m_000m +
    (26 / 3) * rel5_sh_m_00mm + (83 / 24) * rel5_sh_m_01mm + (-23 / 6) * rel5_sh_m_0m0m +
    (35 / 24) * rel5_sh_m_0m1m + (-8 / 3) * rel5_sh_m_0mm1 + (83 / 48) * rel5_sh_m_m01m +
    (-13 / 12) * rel5_sh_m_m0m1 + (131 / 48) * rel5_sh_m_m10m + (8) * rel5_sh_m_m11m +
    (21 / 2) * rel5_sh_m_m1m1 + (-83 / 24) * rel5_sh_m_mm01 + (199 / 64) * rel5_st_01_00m +
    (7 / 3) * rel5_st_0m_001 + (-17 / 8) * rel5_sh_0m_00m + (-1651 / 144) * rel5_st_0m_00m +
    (7 / 3) * rel5_sh_0m_0mm + (-8 / 3) * rel5_sh_m1_m11 + (-4) * rel5_sh_m1_mm1 +
    (13 / 12) * rel5_mob_0mmm1 + (15 / 2) * rel5_sh_m_000m + (-83 / 12) * rel5_sh_m_001m +
    (325 / 72) * rel5_st_m_001m + (-85 / 12) * rel5_sh_m_00m1 + (167 / 36) * rel5_st_m_00m1 +
    (-55 / 24) * rel5_sh_m_010m + (-11 / 12) * rel5_sh_m_01m1 + (-1 / 3) * rel5_sh_m_0m01 +
    (-19 / 12) * rel5_sh_m_0m11 + (23 / 12) * rel5_sh_m_m001 + (-107 / 288) * rel5_st_m_m001 +
    (-37 / 72) * rel5_st_m_m00m + (-67 / 12) * rel5_sh_m_m011 + (-41 / 24) * rel5_sh_m_m101 +
    (16) * rel5_sh_m_m111 + (-1021 / 576) * rel5_st_01_01m + (-1529 / 576) * rel5_st_01_m0m +
    (29 / 12) * rel5_st_0m_0m1 + (-26 / 3) * rel5_st_0m_0mm + (-19 / 12) * rel5_st_0m_m01 +
    (47 / 16) * rel5_sh_m_0001 + (6) * rel5_sh_m_0011 + (-77 / 24) * rel5_st_m_0011 +
    (-37 / 3) * rel5_st_m_00mm + (23 / 4) * rel5_sh_m_0101 + (52 / 9) * rel5_st_m_010m +
    (5 / 36) * rel5_st_m_01m1 + (-85 / 9) * rel5_st_m_0m0m + (37 / 36) * rel5_st_m_0m1m +
    (-5 / 36) * rel5_st_m_m01m + (-211 / 288) * rel5_st_m_m0m1 + (107 / 144) * rel5_st_m_m101 +
    (37 / 36) * rel5_st_m_m10m + (-1 / 2) * rel5_st_m_m1m1 + (-41 / 24) * rel5_sh_01_00m +
    (-2 / 3) * rel5_sh_01_01m + (5 / 3) * rel5_sh_01_0m1 + (1) * rel5_st_01_0m1 +
    (-131 / 24) * rel5_st_01_0mm + (-8) * rel5_sh_01_m11 + (65 / 24) * rel5_sh_0m_001 +
    (55 / 24) * rel5_sh_0m_01m + (16 / 3) * rel5_sh_m1_011 + (67 / 24) * rel5_sh_m1_0m1 +
    (67 / 24) * rel5_sh_m1_m01 + (-40) * rel5_mob_00mmm + (-83 / 8) * rel5_mob_01mmm +
    (-12) * rel5_mob_0m0mm + (-83 / 24) * rel5_mob_0m1mm + (131 / 24) * rel5_mob_m10mm +
    (11 / 6) * rel5_st_m_011m + (-1 / 3) * rel5_st_m_01mm + (35 / 24) * rel5_st_m_0m11 +
    (-1 / 8) * rel5_st_m_0mm1 + (131 / 24) * rel5_st_m_m011 + (-19 / 3) * rel5_st_m_m0mm +
    (1 / 3) * rel5_st_m_m11m + (2) * rel5_st_m_m1mm + (-23 / 6) * rel5_st_m_mm0m +
    (5 / 3) * rel5_st_m_mm1m + (-8) * rel5_st_m_0mmm + (16) * rel5_mob_0000m

theorem hpl_negOne_one_zero_negOne_one_at_one :
    hpl [negOne, one, zero, negOne, one] 1 =
      -4 * Li 4 (1 / 2) * log 2 - 13 * Li 5 (1 / 2) - 7 / 120 * log 2 ^ 5
      + 1 / 9 * log 2 ^ 3 * π ^ 2 + 1 / 2 * log 2 ^ 2 * zeta3 - 3 / 32 * log 2 * π ^ 4
      - 1 / 12 * zeta3 * π ^ 2 + 911 / 64 * zeta5 := by
  linear_combination (-8417 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (631 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (9631 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (4631 / 1152) * hpl_zero_one_zero_zero_one_at_one + (-6) * hpl_zero_zero_one_one_one_at_one +
    (-37 / 8) * hpl_zero_one_zero_one_one_at_one + (-37 / 24) * hpl_zero_one_one_zero_one_at_one +
    (71 / 4) * hpl_zero_zero_zero_zero_negOne_at_one + (-13) * hpl_negOne_one_one_one_one_at_one +
    (19307 / 1920) * rel5_sh_m_mmmm + (-1711 / 768) * rel5_sh_m_0mmm +
    (1711 / 2304) * rel5_sh_m_m0mm + (-13 / 3) * rel5_sh_m_m1mm + (305 / 576) * rel5_sh_m_mm0m +
    (1659 / 256) * rel5_sh_m_mm1m + (3023 / 256) * rel5_sh_m_mmm1 +
    (-2427 / 1024) * rel5_st_m_0001 + (-2147 / 2304) * rel5_st_m_000m +
    (-409 / 72) * rel5_sh_m_00mm + (-593 / 384) * rel5_sh_m_01mm + (1547 / 288) * rel5_sh_m_0m0m +
    (-209 / 384) * rel5_sh_m_0m1m + (2) * rel5_sh_m_0mm1 + (-593 / 768) * rel5_sh_m_m01m +
    (61 / 64) * rel5_sh_m_m0m1 + (-1169 / 768) * rel5_sh_m_m10m + (-13 / 2) * rel5_sh_m_m11m +
    (-899 / 96) * rel5_sh_m_m1m1 + (593 / 384) * rel5_sh_m_mm01 + (-4807 / 3072) * rel5_st_01_00m +
    (-313 / 384) * rel5_st_0m_001 + (2065 / 1152) * rel5_sh_0m_00m +
    (2109 / 256) * rel5_st_0m_00m + (-653 / 144) * rel5_sh_0m_0mm + (13 / 6) * rel5_sh_m1_m11 +
    (125 / 24) * rel5_sh_m1_mm1 + (-1711 / 192) * rel5_mob_0mmm1 + (-3995 / 576) * rel5_sh_m_000m +
    (2209 / 576) * rel5_sh_m_001m + (-1093 / 384) * rel5_st_m_001m +
    (2405 / 576) * rel5_sh_m_00m1 + (-545 / 192) * rel5_st_m_00m1 + (-41 / 384) * rel5_sh_m_010m +
    (17 / 192) * rel5_sh_m_01m1 + (-7 / 36) * rel5_sh_m_0m01 + (-79 / 192) * rel5_sh_m_0m11 +
    (-679 / 576) * rel5_sh_m_m001 + (81 / 512) * rel5_st_m_m001 + (133 / 384) * rel5_st_m_m00m +
    (497 / 192) * rel5_sh_m_m011 + (323 / 384) * rel5_sh_m_m101 + (-13) * rel5_sh_m_m111 +
    (12191 / 9216) * rel5_st_01_01m + (26099 / 9216) * rel5_st_01_m0m +
    (-547 / 384) * rel5_st_0m_0m1 + (101 / 18) * rel5_st_0m_0mm + (605 / 384) * rel5_st_0m_m01 +
    (-2945 / 2304) * rel5_sh_m_0001 + (-229 / 72) * rel5_sh_m_0011 +
    (3037 / 1152) * rel5_st_m_0011 + (1085 / 144) * rel5_st_m_00mm +
    (-1705 / 576) * rel5_sh_m_0101 + (-529 / 144) * rel5_st_m_010m + (31 / 192) * rel5_st_m_01m1 +
    (397 / 72) * rel5_st_m_0m0m + (-559 / 576) * rel5_st_m_0m1m + (-113 / 576) * rel5_st_m_m01m +
    (-37 / 1536) * rel5_st_m_m0m1 + (-81 / 256) * rel5_st_m_m101 + (-133 / 192) * rel5_st_m_m10m +
    (55 / 96) * rel5_st_m_m1m1 + (461 / 1152) * rel5_sh_01_00m + (1 / 4) * rel5_sh_01_01m +
    (-49 / 48) * rel5_sh_01_0m1 + (-9 / 16) * rel5_st_01_0m1 + (2209 / 384) * rel5_st_01_0mm +
    (61 / 12) * rel5_sh_01_m11 + (-1205 / 1152) * rel5_sh_0m_001 + (-479 / 384) * rel5_sh_0m_01m +
    (-37 / 12) * rel5_sh_m1_011 + (-497 / 384) * rel5_sh_m1_0m1 + (-497 / 384) * rel5_sh_m1_m01 +
    (177 / 4) * rel5_mob_00mmm + (593 / 128) * rel5_mob_01mmm + (57 / 4) * rel5_mob_0m0mm +
    (977 / 384) * rel5_mob_0m1mm + (-1169 / 384) * rel5_mob_m10mm + (-235 / 288) * rel5_st_m_011m +
    (-13 / 48) * rel5_st_m_01mm + (-17 / 384) * rel5_st_m_0m11 + (-175 / 384) * rel5_st_m_0mm1 +
    (-1169 / 384) * rel5_st_m_m011 + (209 / 48) * rel5_st_m_m0mm + (-53 / 144) * rel5_st_m_m11m +
    (-13 / 8) * rel5_st_m_m1mm + (679 / 288) * rel5_st_m_mm0m + (-209 / 144) * rel5_st_m_mm1m +
    (6) * rel5_st_m_0mmm + (-13) * rel5_mob_0000m

theorem hpl_negOne_one_zero_negOne_negOne_at_one :
    hpl [negOne, one, zero, negOne, negOne] 1 =
      3 * Li 5 (1 / 2) - 1 / 40 * log 2 ^ 5 + 1 / 24 * log 2 ^ 3 * π ^ 2
      - 11 / 8 * log 2 ^ 2 * zeta3 + 1 / 30 * log 2 * π ^ 4 + 1 / 96 * zeta3 * π ^ 2
      - 99 / 32 * zeta5 := by
  linear_combination (1 / 128) * hpl_zero_zero_zero_zero_one_at_one +
    (-63 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 128) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 128) * hpl_zero_one_zero_zero_one_at_one + (3 / 2) * hpl_zero_zero_one_one_one_at_one +
    (9 / 8) * hpl_zero_one_zero_one_one_at_one + (3 / 8) * hpl_zero_one_one_zero_one_at_one +
    (-3) * hpl_zero_zero_zero_zero_negOne_at_one + (3) * hpl_negOne_one_one_one_one_at_one +
    (-2549 / 640) * rel5_sh_m_mmmm + (193 / 256) * rel5_sh_m_0mmm + (-193 / 768) * rel5_sh_m_m0mm +
    (1) * rel5_sh_m_m1mm + (25 / 192) * rel5_sh_m_mm0m + (-623 / 256) * rel5_sh_m_mm1m +
    (-1203 / 256) * rel5_sh_m_mmm1 + (-329 / 1024) * rel5_st_m_0001 +
    (1273 / 768) * rel5_st_m_000m + (13 / 8) * rel5_sh_m_00mm + (31 / 128) * rel5_sh_m_01mm +
    (-43 / 32) * rel5_sh_m_0m0m + (-17 / 128) * rel5_sh_m_0m1m + (-1 / 2) * rel5_sh_m_0mm1 +
    (31 / 256) * rel5_sh_m_m01m + (-13 / 64) * rel5_sh_m_m0m1 + (143 / 256) * rel5_sh_m_m10m +
    (3 / 2) * rel5_sh_m_m11m + (83 / 32) * rel5_sh_m_m1m1 + (-31 / 128) * rel5_sh_m_mm01 +
    (73 / 1024) * rel5_st_01_00m + (1 / 4) * rel5_st_0m_001 + (-31 / 128) * rel5_sh_0m_00m +
    (-1279 / 768) * rel5_st_0m_00m + (27 / 16) * rel5_sh_0m_0mm + (-1 / 2) * rel5_sh_m1_m11 +
    (-2) * rel5_sh_m1_mm1 + (193 / 64) * rel5_mob_0mmm1 + (17 / 32) * rel5_sh_m_000m +
    (-63 / 64) * rel5_sh_m_001m + (325 / 384) * rel5_st_m_001m + (-85 / 64) * rel5_sh_m_00m1 +
    (57 / 64) * rel5_st_m_00m1 + (-35 / 128) * rel5_sh_m_010m + (-11 / 64) * rel5_sh_m_01m1 +
    (-1 / 16) * rel5_sh_m_0m01 + (33 / 64) * rel5_sh_m_0m11 + (23 / 64) * rel5_sh_m_m001 +
    (-29 / 512) * rel5_st_m_m001 + (-37 / 384) * rel5_st_m_m00m + (-15 / 64) * rel5_sh_m_m011 +
    (11 / 128) * rel5_sh_m_m101 + (3) * rel5_sh_m_m111 + (-539 / 1024) * rel5_st_01_01m +
    (-639 / 1024) * rel5_st_01_m0m + (37 / 64) * rel5_st_0m_0m1 + (-13 / 8) * rel5_st_0m_0mm +
    (-11 / 64) * rel5_st_0m_m01 + (449 / 256) * rel5_sh_m_0001 + (9 / 8) * rel5_sh_m_0011 +
    (-129 / 128) * rel5_st_m_0011 + (-37 / 16) * rel5_st_m_00mm + (69 / 64) * rel5_sh_m_0101 +
    (13 / 12) * rel5_st_m_010m + (-1 / 64) * rel5_st_m_01m1 + (-85 / 48) * rel5_st_m_0m0m +
    (37 / 192) * rel5_st_m_0m1m + (-5 / 192) * rel5_st_m_m01m + (107 / 512) * rel5_st_m_m0m1 +
    (29 / 256) * rel5_st_m_m101 + (37 / 192) * rel5_st_m_m10m + (-7 / 32) * rel5_st_m_m1m1 +
    (51 / 128) * rel5_sh_01_00m + (-1 / 8) * rel5_sh_01_01m + (5 / 16) * rel5_sh_01_0m1 +
    (3 / 16) * rel5_st_01_0m1 + (-79 / 128) * rel5_st_01_0mm + (-3 / 2) * rel5_sh_01_m11 +
    (-27 / 128) * rel5_sh_0m_001 + (35 / 128) * rel5_sh_0m_01m + (1) * rel5_sh_m1_011 +
    (15 / 128) * rel5_sh_m1_0m1 + (15 / 128) * rel5_sh_m1_m01 + (-15) * rel5_mob_00mmm +
    (-93 / 128) * rel5_mob_01mmm + (-19 / 4) * rel5_mob_0m0mm + (-31 / 128) * rel5_mob_0m1mm +
    (143 / 128) * rel5_mob_m10mm + (11 / 32) * rel5_st_m_011m + (-1 / 16) * rel5_st_m_01mm +
    (-17 / 128) * rel5_st_m_0m11 + (49 / 128) * rel5_st_m_0mm1 + (79 / 128) * rel5_st_m_m011 +
    (-19 / 16) * rel5_st_m_m0mm + (1 / 16) * rel5_st_m_m11m + (3 / 8) * rel5_st_m_m1mm +
    (-23 / 32) * rel5_st_m_mm0m + (5 / 16) * rel5_st_m_mm1m + (-3 / 2) * rel5_st_m_0mmm +
    (3) * rel5_mob_0000m

theorem hpl_negOne_one_one_zero_one_at_one :
    hpl [negOne, one, one, zero, one] 1 =
      3 * Li 4 (1 / 2) * log 2 + 2 * Li 5 (1 / 2) + 13 / 120 * log 2 ^ 5
      - 5 / 72 * log 2 ^ 3 * π ^ 2 + 23 / 16 * log 2 ^ 2 * zeta3
      - 19 / 1440 * log 2 * π ^ 4 - 3 / 32 * zeta3 * π ^ 2 - 23 / 64 * zeta5 := by
  linear_combination (1165 / 576) * hpl_zero_zero_zero_zero_one_at_one +
    (-11 / 6) * hpl_zero_zero_zero_one_one_at_one +
    (-551 / 576) * hpl_zero_zero_one_zero_one_at_one +
    (-199 / 576) * hpl_zero_one_zero_zero_one_at_one + (1) * hpl_zero_zero_one_one_one_at_one +
    (3 / 4) * hpl_zero_one_zero_one_one_at_one + (3 / 4) * hpl_zero_one_one_zero_one_at_one +
    (-47 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (2) * hpl_negOne_one_one_one_one_at_one +
    (-559 / 960) * rel5_sh_m_mmmm + (-61 / 384) * rel5_sh_m_0mmm + (61 / 1152) * rel5_sh_m_m0mm +
    (2 / 3) * rel5_sh_m_m1mm + (-13 / 288) * rel5_sh_m_mm0m + (-253 / 384) * rel5_sh_m_mm1m +
    (-67 / 128) * rel5_sh_m_mmm1 + (639 / 512) * rel5_st_m_0001 + (-1001 / 1152) * rel5_st_m_000m +
    (-1 / 36) * rel5_sh_m_00mm + (61 / 192) * rel5_sh_m_01mm + (-167 / 72) * rel5_sh_m_0m0m +
    (-67 / 192) * rel5_sh_m_0m1m + (-1 / 3) * rel5_sh_m_0mm1 + (61 / 384) * rel5_sh_m_m01m +
    (-11 / 96) * rel5_sh_m_m0m1 + (157 / 384) * rel5_sh_m_m10m + (1) * rel5_sh_m_m11m +
    (21 / 16) * rel5_sh_m_m1m1 + (-61 / 192) * rel5_sh_m_mm01 + (505 / 512) * rel5_st_01_00m +
    (-61 / 192) * rel5_st_0m_001 + (-233 / 576) * rel5_sh_0m_00m + (-443 / 384) * rel5_st_0m_00m +
    (55 / 72) * rel5_sh_0m_0mm + (-1 / 3) * rel5_sh_m1_m11 + (-5 / 12) * rel5_sh_m1_mm1 +
    (-61 / 96) * rel5_mob_0mmm1 + (955 / 288) * rel5_sh_m_000m + (-53 / 288) * rel5_sh_m_001m +
    (-7 / 192) * rel5_st_m_001m + (-145 / 288) * rel5_sh_m_00m1 + (7 / 288) * rel5_st_m_00m1 +
    (59 / 64) * rel5_sh_m_010m + (11 / 96) * rel5_sh_m_01m1 + (13 / 144) * rel5_sh_m_0m01 +
    (67 / 96) * rel5_sh_m_0m11 + (107 / 288) * rel5_sh_m_m001 + (-133 / 2304) * rel5_st_m_m001 +
    (-17 / 192) * rel5_st_m_m00m + (-29 / 96) * rel5_sh_m_m011 + (25 / 192) * rel5_sh_m_m101 +
    (2) * rel5_sh_m_m111 + (287 / 1536) * rel5_st_01_01m + (-5255 / 4608) * rel5_st_01_m0m +
    (25 / 192) * rel5_st_0m_0m1 + (-59 / 72) * rel5_st_0m_0mm + (-167 / 192) * rel5_st_0m_m01 +
    (-899 / 1152) * rel5_sh_m_0001 + (17 / 36) * rel5_sh_m_0011 + (487 / 576) * rel5_st_m_0011 +
    (-73 / 72) * rel5_st_m_00mm + (95 / 288) * rel5_sh_m_0101 + (37 / 144) * rel5_st_m_010m +
    (-17 / 288) * rel5_st_m_01m1 + (-143 / 144) * rel5_st_m_0m0m + (59 / 288) * rel5_st_m_0m1m +
    (-23 / 288) * rel5_st_m_m01m + (355 / 2304) * rel5_st_m_m0m1 + (133 / 1152) * rel5_st_m_m101 +
    (17 / 96) * rel5_st_m_m10m + (-1 / 16) * rel5_st_m_m1m1 + (-709 / 576) * rel5_sh_01_00m +
    (-11 / 24) * rel5_sh_01_01m + (1 / 12) * rel5_sh_01_0m1 + (3 / 8) * rel5_st_01_0m1 +
    (-215 / 64) * rel5_st_01_0mm + (-1 / 2) * rel5_sh_01_m11 + (613 / 576) * rel5_sh_0m_001 +
    (67 / 192) * rel5_sh_0m_01m + (1 / 6) * rel5_sh_m1_011 + (-19 / 192) * rel5_sh_m1_0m1 +
    (29 / 192) * rel5_sh_m1_m01 + (-9 / 2) * rel5_mob_00mmm + (-61 / 64) * rel5_mob_01mmm +
    (-7 / 6) * rel5_mob_0m0mm + (1 / 64) * rel5_mob_0m1mm + (157 / 192) * rel5_mob_m10mm +
    (-1 / 144) * rel5_st_m_011m + (5 / 24) * rel5_st_m_01mm + (-35 / 192) * rel5_st_m_0m11 +
    (33 / 64) * rel5_st_m_0mm1 + (157 / 192) * rel5_st_m_m011 + (-13 / 24) * rel5_st_m_m0mm +
    (1 / 72) * rel5_st_m_m11m + (1 / 4) * rel5_st_m_m1mm + (-107 / 144) * rel5_st_m_mm0m +
    (13 / 72) * rel5_st_m_mm1m + (-1) * rel5_st_m_0mmm + (2) * rel5_mob_0000m

theorem hpl_negOne_one_one_zero_negOne_at_one :
    hpl [negOne, one, one, zero, negOne] 1 =
      -3 * Li 4 (1 / 2) * log 2 - 7 * Li 5 (1 / 2) - 1 / 15 * log 2 ^ 5
      + 1 / 24 * log 2 ^ 3 * π ^ 2 + 5 / 16 * log 2 ^ 2 * zeta3 - 11 / 240 * log 2 * π ^ 4
      + 1 / 48 * zeta3 * π ^ 2 + 457 / 64 * zeta5 := by
  linear_combination (-521 / 128) * hpl_zero_zero_zero_zero_one_at_one +
    (121 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (623 / 128) * hpl_zero_zero_one_zero_one_at_one +
    (295 / 128) * hpl_zero_one_zero_zero_one_at_one + (-7 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-21 / 8) * hpl_zero_one_zero_one_one_at_one + (-7 / 8) * hpl_zero_one_one_zero_one_at_one +
    (115 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-7) * hpl_negOne_one_one_one_one_at_one +
    (623 / 1920) * rel5_sh_m_mmmm + (-115 / 768) * rel5_sh_m_0mmm + (115 / 2304) * rel5_sh_m_m0mm +
    (-7 / 3) * rel5_sh_m_m1mm + (245 / 576) * rel5_sh_m_mm0m + (127 / 256) * rel5_sh_m_mm1m +
    (3 / 256) * rel5_sh_m_mmm1 + (-1143 / 1024) * rel5_st_m_0001 +
    (-2419 / 2304) * rel5_st_m_000m + (-83 / 24) * rel5_sh_m_00mm + (-365 / 384) * rel5_sh_m_01mm +
    (43 / 96) * rel5_sh_m_0m0m + (-29 / 384) * rel5_sh_m_0m1m + (7 / 6) * rel5_sh_m_0mm1 +
    (1 / 4) * rel5_sh_m_m00m + (-173 / 768) * rel5_sh_m_m01m + (79 / 192) * rel5_sh_m_m0m1 +
    (-413 / 768) * rel5_sh_m_m10m + (-7 / 2) * rel5_sh_m_m11m + (-127 / 32) * rel5_sh_m_m1m1 +
    (365 / 384) * rel5_sh_m_mm01 + (-569 / 1024) * rel5_st_01_00m + (-175 / 192) * rel5_st_0m_001 +
    (265 / 384) * rel5_sh_0m_00m + (11797 / 2304) * rel5_st_0m_00m + (5 / 16) * rel5_sh_0m_0mm +
    (7 / 6) * rel5_sh_m1_m11 + (1 / 4) * rel5_sh_m1_mm1 + (-115 / 192) * rel5_mob_0mmm1 +
    (-65 / 48) * rel5_sh_m_000m + (139 / 64) * rel5_sh_m_001m + (-1831 / 1152) * rel5_st_m_001m +
    (157 / 64) * rel5_sh_m_00m1 + (-941 / 576) * rel5_st_m_00m1 + (469 / 384) * rel5_sh_m_010m +
    (41 / 192) * rel5_sh_m_01m1 + (-1 / 8) * rel5_sh_m_0m01 + (-83 / 192) * rel5_sh_m_0m11 +
    (-47 / 64) * rel5_sh_m_m001 + (341 / 4608) * rel5_st_m_m001 + (247 / 1152) * rel5_st_m_m00m +
    (157 / 192) * rel5_sh_m_m011 + (-1 / 384) * rel5_sh_m_m101 + (-7) * rel5_sh_m_m111 +
    (6787 / 9216) * rel5_st_01_01m + (3335 / 9216) * rel5_st_01_m0m + (-91 / 96) * rel5_st_0m_0m1 +
    (13 / 4) * rel5_st_0m_0mm + (-19 / 96) * rel5_st_0m_m01 + (-971 / 768) * rel5_sh_m_0001 +
    (-43 / 24) * rel5_sh_m_0011 + (209 / 128) * rel5_st_m_0011 + (69 / 16) * rel5_st_m_00mm +
    (-331 / 192) * rel5_sh_m_0101 + (-301 / 144) * rel5_st_m_010m + (-23 / 576) * rel5_st_m_01m1 +
    (59 / 18) * rel5_st_m_0m0m + (-295 / 576) * rel5_st_m_0m1m + (-49 / 576) * rel5_st_m_m01m +
    (-563 / 4608) * rel5_st_m_m0m1 + (-341 / 2304) * rel5_st_m_m101 +
    (-247 / 576) * rel5_st_m_m10m + (3 / 32) * rel5_st_m_m1m1 + (-233 / 384) * rel5_sh_01_00m +
    (1 / 6) * rel5_sh_01_01m + (-29 / 48) * rel5_sh_01_0m1 + (-7 / 16) * rel5_st_01_0m1 +
    (269 / 384) * rel5_st_01_0mm + (3) * rel5_sh_01_m11 + (113 / 384) * rel5_sh_0m_001 +
    (1 / 2) * rel5_st_0m_011 + (-253 / 384) * rel5_sh_0m_01m + (-11 / 6) * rel5_sh_m1_011 +
    (-253 / 384) * rel5_sh_m1_0m1 + (-157 / 384) * rel5_sh_m1_m01 + (17 / 2) * rel5_mob_00mmm +
    (365 / 128) * rel5_mob_01mmm + (7 / 4) * rel5_mob_0m0mm + (365 / 384) * rel5_mob_0m1mm +
    (-605 / 384) * rel5_mob_m10mm + (-19 / 32) * rel5_st_m_011m + (-5 / 48) * rel5_st_m_01mm +
    (-29 / 384) * rel5_st_m_0m11 + (-65 / 128) * rel5_st_m_0mm1 + (-509 / 384) * rel5_st_m_m011 +
    (121 / 48) * rel5_st_m_m0mm + (-1 / 16) * rel5_st_m_m11m + (-7 / 8) * rel5_st_m_m1mm +
    (-1 / 2) * rel5_st_m_mm01 + (47 / 32) * rel5_st_m_mm0m + (-31 / 48) * rel5_st_m_mm1m +
    (7 / 2) * rel5_st_m_0mmm + (-7) * rel5_mob_0000m

theorem hpl_negOne_one_one_one_negOne_at_one :
    hpl [negOne, one, one, one, negOne] 1 =
      -Li 4 (1 / 2) * log 2 - 2 * Li 5 (1 / 2) - 1 / 30 * log 2 ^ 5
      + 1 / 36 * log 2 ^ 3 * π ^ 2 - 7 / 16 * log 2 ^ 2 * zeta3 + 7 / 96 * zeta3 * π ^ 2
      + 27 / 32 * zeta5 := by
  linear_combination (-397 / 192) * hpl_zero_zero_zero_zero_one_at_one +
    (25 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (371 / 192) * hpl_zero_zero_one_zero_one_at_one +
    (155 / 192) * hpl_zero_one_zero_zero_one_at_one + (-1) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 4) * hpl_zero_one_zero_one_one_at_one + (-5 / 12) * hpl_zero_one_one_zero_one_at_one +
    (109 / 30) * hpl_zero_zero_zero_zero_negOne_at_one + (-2) * hpl_negOne_one_one_one_one_at_one +
    (683 / 320) * rel5_sh_m_mmmm + (-31 / 128) * rel5_sh_m_0mmm + (31 / 384) * rel5_sh_m_m0mm +
    (-2 / 3) * rel5_sh_m_m1mm + (25 / 96) * rel5_sh_m_mm0m + (241 / 128) * rel5_sh_m_mm1m +
    (301 / 128) * rel5_sh_m_mmm1 + (-6887 / 7680) * rel5_st_m_0001 + (89 / 384) * rel5_st_m_000m +
    (-17 / 12) * rel5_sh_m_00mm + (-131 / 192) * rel5_sh_m_01mm + (91 / 48) * rel5_sh_m_0m0m +
    (-19 / 192) * rel5_sh_m_0m1m + (1 / 3) * rel5_sh_m_0mm1 + (-131 / 384) * rel5_sh_m_m01m +
    (3 / 32) * rel5_sh_m_m0m1 + (-81 / 128) * rel5_sh_m_m10m + (-1) * rel5_sh_m_m11m +
    (-95 / 48) * rel5_sh_m_m1m1 + (131 / 192) * rel5_sh_m_mm01 + (-2099 / 2560) * rel5_st_01_00m +
    (1 / 12) * rel5_st_0m_001 + (33 / 64) * rel5_sh_0m_00m + (235 / 128) * rel5_st_0m_00m +
    (-23 / 24) * rel5_sh_0m_0mm + (4 / 3) * rel5_sh_m1_mm1 + (-31 / 32) * rel5_mob_0mmm1 +
    (-137 / 48) * rel5_sh_m_000m + (83 / 96) * rel5_sh_m_001m + (-107 / 192) * rel5_st_m_001m +
    (97 / 96) * rel5_sh_m_00m1 + (-827 / 1440) * rel5_st_m_00m1 + (-73 / 192) * rel5_sh_m_010m +
    (5 / 32) * rel5_sh_m_01m1 + (1 / 8) * rel5_sh_m_0m01 + (1 / 32) * rel5_sh_m_0m11 +
    (-9 / 32) * rel5_sh_m_m001 + (839 / 11520) * rel5_st_m_m001 + (11 / 192) * rel5_st_m_m00m +
    (115 / 96) * rel5_sh_m_m011 + (97 / 192) * rel5_sh_m_m101 + (-1) * rel5_sh_m_m111 +
    (4129 / 23040) * rel5_st_01_01m + (24461 / 23040) * rel5_st_01_m0m +
    (-11 / 32) * rel5_st_0m_0m1 + (5 / 4) * rel5_st_0m_0mm + (79 / 96) * rel5_st_0m_m01 +
    (67 / 384) * rel5_sh_m_0001 + (-13 / 12) * rel5_sh_m_0011 + (29 / 192) * rel5_st_m_0011 +
    (15 / 8) * rel5_st_m_00mm + (-89 / 96) * rel5_sh_m_0101 + (-3 / 4) * rel5_st_m_010m +
    (19 / 1440) * rel5_st_m_01m1 + (11 / 8) * rel5_st_m_0m0m + (-11 / 96) * rel5_st_m_0m1m +
    (11 / 96) * rel5_st_m_m01m + (943 / 11520) * rel5_st_m_m0m1 + (-839 / 5760) * rel5_st_m_m101 +
    (-11 / 96) * rel5_st_m_m10m + (47 / 240) * rel5_st_m_m1m1 + (137 / 192) * rel5_sh_01_00m +
    (1 / 4) * rel5_sh_01_01m + (-5 / 24) * rel5_sh_01_0m1 + (-1 / 8) * rel5_st_01_0m1 +
    (177 / 64) * rel5_st_01_0mm + (1) * rel5_sh_01_m11 + (-161 / 192) * rel5_sh_0m_001 +
    (-71 / 192) * rel5_sh_0m_01m + (-2 / 3) * rel5_sh_m1_011 + (-17 / 64) * rel5_sh_m1_0m1 +
    (-115 / 192) * rel5_sh_m1_m01 + (10) * rel5_mob_00mmm + (131 / 64) * rel5_mob_01mmm +
    (19 / 6) * rel5_mob_0m0mm + (131 / 192) * rel5_mob_0m1mm + (-81 / 64) * rel5_mob_m10mm +
    (-7 / 48) * rel5_st_m_011m + (1 / 24) * rel5_st_m_01mm + (-19 / 192) * rel5_st_m_0m11 +
    (-13 / 192) * rel5_st_m_0mm1 + (-81 / 64) * rel5_st_m_m011 + (19 / 24) * rel5_st_m_m0mm +
    (1 / 8) * rel5_st_m_m11m + (-1 / 4) * rel5_st_m_m1mm + (9 / 16) * rel5_st_m_mm0m +
    (-3 / 8) * rel5_st_m_mm1m + (1) * rel5_st_m_0mmm + (-2) * rel5_mob_0000m

theorem hpl_negOne_one_one_negOne_one_at_one :
    hpl [negOne, one, one, negOne, one] 1 =
      3 * Li 4 (1 / 2) * log 2 + 3 * Li 5 (1 / 2) + 11 / 120 * log 2 ^ 5
      - 5 / 72 * log 2 ^ 3 * π ^ 2 + 7 / 8 * log 2 ^ 2 * zeta3 + 1 / 288 * log 2 * π ^ 4
      - 7 / 48 * zeta3 * π ^ 2 - 81 / 64 * zeta5 := by
  linear_combination (397 / 128) * hpl_zero_zero_zero_zero_one_at_one +
    (-75 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (-371 / 128) * hpl_zero_zero_one_zero_one_at_one +
    (-155 / 128) * hpl_zero_one_zero_zero_one_at_one + (3 / 2) * hpl_zero_zero_one_one_one_at_one +
    (9 / 8) * hpl_zero_one_zero_one_one_at_one + (5 / 8) * hpl_zero_one_one_zero_one_at_one +
    (-109 / 20) * hpl_zero_zero_zero_zero_negOne_at_one + (3) * hpl_negOne_one_one_one_one_at_one +
    (-2049 / 640) * rel5_sh_m_mmmm + (93 / 256) * rel5_sh_m_0mmm + (-31 / 256) * rel5_sh_m_m0mm +
    (1) * rel5_sh_m_m1mm + (-25 / 64) * rel5_sh_m_mm0m + (-723 / 256) * rel5_sh_m_mm1m +
    (-903 / 256) * rel5_sh_m_mmm1 + (6887 / 5120) * rel5_st_m_0001 + (-89 / 256) * rel5_st_m_000m +
    (17 / 8) * rel5_sh_m_00mm + (131 / 128) * rel5_sh_m_01mm + (-91 / 32) * rel5_sh_m_0m0m +
    (19 / 128) * rel5_sh_m_0m1m + (-1 / 2) * rel5_sh_m_0mm1 + (131 / 256) * rel5_sh_m_m01m +
    (-9 / 64) * rel5_sh_m_m0m1 + (243 / 256) * rel5_sh_m_m10m + (3 / 2) * rel5_sh_m_m11m +
    (95 / 32) * rel5_sh_m_m1m1 + (-131 / 128) * rel5_sh_m_mm01 + (6297 / 5120) * rel5_st_01_00m +
    (-1 / 8) * rel5_st_0m_001 + (-99 / 128) * rel5_sh_0m_00m + (-705 / 256) * rel5_st_0m_00m +
    (23 / 16) * rel5_sh_0m_0mm + (-1 / 2) * rel5_sh_m1_m11 + (-2) * rel5_sh_m1_mm1 +
    (93 / 64) * rel5_mob_0mmm1 + (137 / 32) * rel5_sh_m_000m + (-83 / 64) * rel5_sh_m_001m +
    (107 / 128) * rel5_st_m_001m + (-97 / 64) * rel5_sh_m_00m1 + (827 / 960) * rel5_st_m_00m1 +
    (73 / 128) * rel5_sh_m_010m + (-15 / 64) * rel5_sh_m_01m1 + (-3 / 16) * rel5_sh_m_0m01 +
    (-3 / 64) * rel5_sh_m_0m11 + (27 / 64) * rel5_sh_m_m001 + (-839 / 7680) * rel5_st_m_m001 +
    (-11 / 128) * rel5_st_m_m00m + (-115 / 64) * rel5_sh_m_m011 + (-97 / 128) * rel5_sh_m_m101 +
    (3) * rel5_sh_m_m111 + (-4129 / 15360) * rel5_st_01_01m + (-24461 / 15360) * rel5_st_01_m0m +
    (33 / 64) * rel5_st_0m_0m1 + (-15 / 8) * rel5_st_0m_0mm + (-79 / 64) * rel5_st_0m_m01 +
    (-67 / 256) * rel5_sh_m_0001 + (13 / 8) * rel5_sh_m_0011 + (-29 / 128) * rel5_st_m_0011 +
    (-45 / 16) * rel5_st_m_00mm + (89 / 64) * rel5_sh_m_0101 + (9 / 8) * rel5_st_m_010m +
    (-19 / 960) * rel5_st_m_01m1 + (-33 / 16) * rel5_st_m_0m0m + (11 / 64) * rel5_st_m_0m1m +
    (-11 / 64) * rel5_st_m_m01m + (-943 / 7680) * rel5_st_m_m0m1 + (839 / 3840) * rel5_st_m_m101 +
    (11 / 64) * rel5_st_m_m10m + (-47 / 160) * rel5_st_m_m1m1 + (-137 / 128) * rel5_sh_01_00m +
    (-3 / 8) * rel5_sh_01_01m + (5 / 16) * rel5_sh_01_0m1 + (3 / 16) * rel5_st_01_0m1 +
    (-531 / 128) * rel5_st_01_0mm + (-3 / 2) * rel5_sh_01_m11 + (161 / 128) * rel5_sh_0m_001 +
    (71 / 128) * rel5_sh_0m_01m + (1) * rel5_sh_m1_011 + (51 / 128) * rel5_sh_m1_0m1 +
    (115 / 128) * rel5_sh_m1_m01 + (-15) * rel5_mob_00mmm + (-393 / 128) * rel5_mob_01mmm +
    (-19 / 4) * rel5_mob_0m0mm + (-131 / 128) * rel5_mob_0m1mm + (243 / 128) * rel5_mob_m10mm +
    (7 / 32) * rel5_st_m_011m + (-1 / 16) * rel5_st_m_01mm + (19 / 128) * rel5_st_m_0m11 +
    (13 / 128) * rel5_st_m_0mm1 + (243 / 128) * rel5_st_m_m011 + (-19 / 16) * rel5_st_m_m0mm +
    (-3 / 16) * rel5_st_m_m11m + (3 / 8) * rel5_st_m_m1mm + (-27 / 32) * rel5_st_m_mm0m +
    (9 / 16) * rel5_st_m_mm1m + (-3 / 2) * rel5_st_m_0mmm + (3) * rel5_mob_0000m

theorem hpl_negOne_one_one_negOne_negOne_at_one :
    hpl [negOne, one, one, negOne, negOne] 1 =
      1 / 120 * log 2 ^ 5 - 1 / 72 * log 2 ^ 3 * π ^ 2 + 7 / 16 * log 2 ^ 2 * zeta3
      - 1 / 288 * log 2 * π ^ 4 + 1 / 96 * zeta3 * π ^ 2 - 3 / 64 * zeta5 := by
  linear_combination (-1 / 20) * hpl_zero_zero_zero_zero_negOne_at_one +
    (1 / 40) * rel5_st_m_0001 + (1 / 2) * rel5_sh_m_m11m + (-1 / 4) * rel5_sh_m_m1m1 +
    (-1) * rel5_sh_m_mm11 + (1 / 40) * rel5_st_01_00m + (1 / 2) * rel5_sh_m1_mm1 +
    (1 / 120) * rel5_st_m_00m1 + (1 / 120) * rel5_st_m_m001 + (-1 / 60) * rel5_st_01_01m +
    (1 / 60) * rel5_st_01_m0m + (-1 / 60) * rel5_st_m_01m1 + (1 / 60) * rel5_st_m_m0m1 +
    (-1 / 60) * rel5_st_m_m101 + (-1 / 20) * rel5_st_m_m1m1

theorem hpl_negOne_one_negOne_zero_one_at_one :
    hpl [negOne, one, negOne, zero, one] 1 =
      4 * Li 4 (1 / 2) * log 2 + 5 * Li 5 (1 / 2) + 1 / 8 * log 2 ^ 5
      - 1 / 8 * log 2 ^ 3 * π ^ 2 + 13 / 8 * log 2 ^ 2 * zeta3 + 19 / 1440 * log 2 * π ^ 4
      - 5 / 16 * zeta3 * π ^ 2 - 101 / 64 * zeta5 := by
  linear_combination (2845 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (-311 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (-5315 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (-1915 / 1152) * hpl_zero_one_zero_zero_one_at_one + (1) * hpl_zero_zero_one_one_one_at_one +
    (9 / 8) * hpl_zero_one_zero_one_one_at_one + (3 / 8) * hpl_zero_one_one_zero_one_at_one +
    (-83 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (5) * hpl_negOne_one_one_one_one_at_one +
    (-825 / 128) * rel5_sh_m_mmmm + (217 / 256) * rel5_sh_m_0mmm + (-217 / 768) * rel5_sh_m_m0mm +
    (5 / 3) * rel5_sh_m_m1mm + (-151 / 192) * rel5_sh_m_mm0m + (-4213 / 768) * rel5_sh_m_mm1m +
    (-1867 / 256) * rel5_sh_m_mmm1 + (887 / 1024) * rel5_st_m_0001 +
    (1655 / 2304) * rel5_st_m_000m + (269 / 72) * rel5_sh_m_00mm + (231 / 128) * rel5_sh_m_01mm +
    (-1135 / 288) * rel5_sh_m_0m0m + (277 / 384) * rel5_sh_m_0m1m + (-1 / 3) * rel5_sh_m_0mm1 +
    (231 / 256) * rel5_sh_m_m01m + (-25 / 64) * rel5_sh_m_m0m1 + (391 / 256) * rel5_sh_m_m10m +
    (5 / 2) * rel5_sh_m_m11m + (145 / 32) * rel5_sh_m_m1m1 + (-231 / 128) * rel5_sh_m_mm01 +
    (1601 / 1024) * rel5_st_01_00m + (-197 / 384) * rel5_st_0m_001 +
    (-1049 / 1152) * rel5_sh_0m_00m + (-7345 / 2304) * rel5_st_0m_00m +
    (421 / 144) * rel5_sh_0m_0mm + (-5 / 6) * rel5_sh_m1_m11 + (-95 / 24) * rel5_sh_m1_mm1 +
    (217 / 64) * rel5_mob_0mmm1 + (2965 / 576) * rel5_sh_m_000m + (-1289 / 576) * rel5_sh_m_001m +
    (1699 / 1152) * rel5_st_m_001m + (-1393 / 576) * rel5_sh_m_00m1 +
    (289 / 192) * rel5_st_m_00m1 + (161 / 384) * rel5_sh_m_010m + (-31 / 64) * rel5_sh_m_01m1 +
    (-47 / 72) * rel5_sh_m_0m01 + (-71 / 64) * rel5_sh_m_0m11 + (299 / 576) * rel5_sh_m_m001 +
    (-287 / 1536) * rel5_st_m_m001 + (29 / 1152) * rel5_st_m_m00m + (-231 / 64) * rel5_sh_m_m011 +
    (-607 / 384) * rel5_sh_m_m101 + (5) * rel5_sh_m_m111 + (-6715 / 9216) * rel5_st_01_01m +
    (-21727 / 9216) * rel5_st_01_m0m + (293 / 384) * rel5_st_0m_0m1 + (-83 / 36) * rel5_st_0m_0mm +
    (-667 / 384) * rel5_st_0m_m01 + (1597 / 2304) * rel5_sh_m_0001 + (185 / 72) * rel5_sh_m_0011 +
    (-785 / 1152) * rel5_st_m_0011 + (-601 / 144) * rel5_st_m_00mm +
    (1469 / 576) * rel5_sh_m_0101 + (27 / 16) * rel5_st_m_010m + (5 / 192) * rel5_st_m_01m1 +
    (-113 / 36) * rel5_st_m_0m0m + (1 / 192) * rel5_st_m_0m1m + (-259 / 576) * rel5_st_m_m01m +
    (-205 / 512) * rel5_st_m_m0m1 + (287 / 768) * rel5_st_m_m101 + (-29 / 576) * rel5_st_m_m10m +
    (-13 / 32) * rel5_st_m_m1m1 + (-1177 / 1152) * rel5_sh_01_00m + (-1 / 3) * rel5_sh_01_01m +
    (25 / 48) * rel5_sh_01_0m1 + (1 / 16) * rel5_st_01_0m1 + (-2117 / 384) * rel5_st_01_0mm +
    (-9 / 4) * rel5_sh_01_m11 + (1729 / 1152) * rel5_sh_0m_001 + (311 / 384) * rel5_sh_0m_01m +
    (23 / 12) * rel5_sh_m1_011 + (103 / 128) * rel5_sh_m1_0m1 + (231 / 128) * rel5_sh_m1_m01 +
    (-115 / 4) * rel5_mob_00mmm + (-693 / 128) * rel5_mob_01mmm + (-115 / 12) * rel5_mob_0m0mm +
    (-821 / 384) * rel5_mob_0m1mm + (391 / 128) * rel5_mob_m10mm + (191 / 288) * rel5_st_m_011m +
    (-23 / 48) * rel5_st_m_01mm + (71 / 128) * rel5_st_m_0m11 + (-71 / 128) * rel5_st_m_0mm1 +
    (391 / 128) * rel5_st_m_m011 + (-77 / 48) * rel5_st_m_m0mm + (25 / 144) * rel5_st_m_m11m +
    (5 / 8) * rel5_st_m_m1mm + (-299 / 288) * rel5_st_m_mm0m + (85 / 144) * rel5_st_m_mm1m +
    (-1) * rel5_st_m_0mmm + (5) * rel5_mob_0000m

theorem hpl_negOne_one_negOne_zero_negOne_at_one :
    hpl [negOne, one, negOne, zero, negOne] 1 =
      4 * Li 4 (1 / 2) * log 2 + 8 * Li 5 (1 / 2) + 1 / 10 * log 2 ^ 5
      - 5 / 72 * log 2 ^ 3 * π ^ 2 + 1 / 8 * log 2 ^ 2 * zeta3 + 11 / 240 * log 2 * π ^ 4
      - 1 / 24 * zeta3 * π ^ 2 - 61 / 8 * zeta5 := by
  linear_combination (241 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 2) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 48) * hpl_zero_one_zero_zero_one_at_one + (4) * hpl_zero_zero_one_one_one_at_one +
    (3) * hpl_zero_one_zero_one_one_at_one + (1) * hpl_zero_one_one_zero_one_at_one +
    (-38 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (8) * hpl_negOne_one_one_one_one_at_one +
    (-749 / 240) * rel5_sh_m_mmmm + (25 / 96) * rel5_sh_m_0mmm + (-25 / 288) * rel5_sh_m_m0mm +
    (8 / 3) * rel5_sh_m_m1mm + (-47 / 72) * rel5_sh_m_mm0m + (-93 / 32) * rel5_sh_m_mm1m +
    (-105 / 32) * rel5_sh_m_mmm1 + (229 / 128) * rel5_st_m_0001 + (313 / 288) * rel5_st_m_000m +
    (13 / 3) * rel5_sh_m_00mm + (71 / 48) * rel5_sh_m_01mm + (-23 / 12) * rel5_sh_m_0m0m +
    (23 / 48) * rel5_sh_m_0m1m + (-4 / 3) * rel5_sh_m_0mm1 + (71 / 96) * rel5_sh_m_m01m +
    (-13 / 24) * rel5_sh_m_m0m1 + (119 / 96) * rel5_sh_m_m10m + (4) * rel5_sh_m_m11m +
    (21 / 4) * rel5_sh_m_m1m1 + (-71 / 48) * rel5_sh_m_mm01 + (203 / 128) * rel5_st_01_00m +
    (31 / 24) * rel5_st_0m_001 + (-17 / 16) * rel5_sh_0m_00m + (-1759 / 288) * rel5_st_0m_00m +
    (7 / 6) * rel5_sh_0m_0mm + (-4 / 3) * rel5_sh_m1_m11 + (-2) * rel5_sh_m1_mm1 +
    (25 / 24) * rel5_mob_0mmm1 + (7 / 2) * rel5_sh_m_000m + (-83 / 24) * rel5_sh_m_001m +
    (325 / 144) * rel5_st_m_001m + (-85 / 24) * rel5_sh_m_00m1 + (167 / 72) * rel5_st_m_00m1 +
    (-55 / 48) * rel5_sh_m_010m + (-11 / 24) * rel5_sh_m_01m1 + (-1 / 6) * rel5_sh_m_0m01 +
    (-7 / 24) * rel5_sh_m_0m11 + (23 / 24) * rel5_sh_m_m001 + (1 / 576) * rel5_st_m_m001 +
    (-37 / 144) * rel5_st_m_m00m + (-55 / 24) * rel5_sh_m_m011 + (-29 / 48) * rel5_sh_m_m101 +
    (8) * rel5_sh_m_m111 + (-1129 / 1152) * rel5_st_01_01m + (-1205 / 1152) * rel5_st_01_m0m +
    (4 / 3) * rel5_st_0m_0m1 + (-13 / 3) * rel5_st_0m_0mm + (-2 / 3) * rel5_st_0m_m01 +
    (43 / 32) * rel5_sh_m_0001 + (3) * rel5_sh_m_0011 + (-89 / 48) * rel5_st_m_0011 +
    (-37 / 6) * rel5_st_m_00mm + (23 / 8) * rel5_sh_m_0101 + (26 / 9) * rel5_st_m_010m +
    (5 / 72) * rel5_st_m_01m1 + (-85 / 18) * rel5_st_m_0m0m + (37 / 72) * rel5_st_m_0m1m +
    (-5 / 72) * rel5_st_m_m01m + (-103 / 576) * rel5_st_m_m0m1 + (-1 / 288) * rel5_st_m_m101 +
    (37 / 72) * rel5_st_m_m10m + (-1 / 4) * rel5_st_m_m1m1 + (-29 / 48) * rel5_sh_01_00m +
    (-1 / 3) * rel5_sh_01_01m + (5 / 6) * rel5_sh_01_0m1 + (1 / 2) * rel5_st_01_0m1 +
    (-119 / 48) * rel5_st_01_0mm + (-4) * rel5_sh_01_m11 + (53 / 48) * rel5_sh_0m_001 +
    (55 / 48) * rel5_sh_0m_01m + (8 / 3) * rel5_sh_m1_011 + (55 / 48) * rel5_sh_m1_0m1 +
    (55 / 48) * rel5_sh_m1_m01 + (-20) * rel5_mob_00mmm + (-71 / 16) * rel5_mob_01mmm +
    (-6) * rel5_mob_0m0mm + (-71 / 48) * rel5_mob_0m1mm + (119 / 48) * rel5_mob_m10mm +
    (11 / 12) * rel5_st_m_011m + (-1 / 6) * rel5_st_m_01mm + (23 / 48) * rel5_st_m_0m11 +
    (3 / 16) * rel5_st_m_0mm1 + (119 / 48) * rel5_st_m_m011 + (-19 / 6) * rel5_st_m_m0mm +
    (1 / 6) * rel5_st_m_m11m + (1) * rel5_st_m_m1mm + (-23 / 12) * rel5_st_m_mm0m +
    (5 / 6) * rel5_st_m_mm1m + (-4) * rel5_st_m_0mmm + (8) * rel5_mob_0000m

theorem hpl_negOne_one_negOne_one_one_at_one :
    hpl [negOne, one, negOne, one, one] 1 =
      -3 * Li 4 (1 / 2) * log 2 - 3 * Li 5 (1 / 2) - 13 / 120 * log 2 ^ 5
      + 7 / 72 * log 2 ^ 3 * π ^ 2 - 23 / 16 * log 2 ^ 2 * zeta3 - 1 / 1440 * log 2 * π ^ 4
      + 23 / 96 * zeta3 * π ^ 2 + 23 / 64 * zeta5 := by
  linear_combination (-1111 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (179 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (3017 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (1153 / 1152) * hpl_zero_one_zero_zero_one_at_one +
    (-1 / 2) * hpl_zero_zero_one_one_one_at_one + (-3 / 8) * hpl_zero_one_zero_one_one_at_one +
    (-5 / 24) * hpl_zero_one_one_zero_one_at_one +
    (233 / 60) * hpl_zero_zero_zero_zero_negOne_at_one + (-3) * hpl_negOne_one_one_one_one_at_one +
    (1659 / 640) * rel5_sh_m_mmmm + (-47 / 256) * rel5_sh_m_0mmm + (47 / 768) * rel5_sh_m_m0mm +
    (-1) * rel5_sh_m_m1mm + (73 / 192) * rel5_sh_m_mm0m + (609 / 256) * rel5_sh_m_mm1m +
    (733 / 256) * rel5_sh_m_mmm1 + (-1213 / 5120) * rel5_st_m_0001 +
    (-1541 / 2304) * rel5_st_m_000m + (-131 / 72) * rel5_sh_m_00mm +
    (-113 / 128) * rel5_sh_m_01mm + (505 / 288) * rel5_sh_m_0m0m + (-33 / 128) * rel5_sh_m_0m1m +
    (1 / 6) * rel5_sh_m_0mm1 + (-113 / 256) * rel5_sh_m_m01m + (25 / 192) * rel5_sh_m_m0m1 +
    (-193 / 256) * rel5_sh_m_m10m + (-3 / 2) * rel5_sh_m_m11m + (-223 / 96) * rel5_sh_m_m1m1 +
    (113 / 128) * rel5_sh_m_mm01 + (-12169 / 15360) * rel5_st_01_00m + (7 / 48) * rel5_st_0m_001 +
    (425 / 1152) * rel5_sh_0m_00m + (3763 / 2304) * rel5_st_0m_00m +
    (-181 / 144) * rel5_sh_0m_0mm + (1 / 2) * rel5_sh_m1_m11 + (5 / 3) * rel5_sh_m1_mm1 +
    (-47 / 64) * rel5_mob_0mmm1 + (-623 / 288) * rel5_sh_m_000m + (665 / 576) * rel5_sh_m_001m +
    (-913 / 1152) * rel5_st_m_001m + (787 / 576) * rel5_sh_m_00m1 +
    (-2299 / 2880) * rel5_st_m_00m1 + (-3 / 128) * rel5_sh_m_010m + (21 / 64) * rel5_sh_m_01m1 +
    (61 / 144) * rel5_sh_m_0m01 + (83 / 192) * rel5_sh_m_0m11 + (-161 / 576) * rel5_sh_m_m001 +
    (2263 / 23040) * rel5_st_m_m001 + (49 / 1152) * rel5_st_m_m00m + (323 / 192) * rel5_sh_m_m011 +
    (91 / 128) * rel5_sh_m_m101 + (-3) * rel5_sh_m_m111 + (16273 / 46080) * rel5_st_01_01m +
    (16319 / 15360) * rel5_st_01_m0m + (-31 / 64) * rel5_st_0m_0m1 + (97 / 72) * rel5_st_0m_0mm +
    (49 / 64) * rel5_st_0m_m01 + (-1639 / 2304) * rel5_sh_m_0001 + (-119 / 72) * rel5_sh_m_0011 +
    (359 / 1152) * rel5_st_m_0011 + (343 / 144) * rel5_st_m_00mm + (-875 / 576) * rel5_sh_m_0101 +
    (-23 / 24) * rel5_st_m_010m + (-157 / 2880) * rel5_st_m_01m1 + (263 / 144) * rel5_st_m_0m0m +
    (5 / 192) * rel5_st_m_0m1m + (145 / 576) * rel5_st_m_m01m + (4031 / 23040) * rel5_st_m_m0m1 +
    (-2263 / 11520) * rel5_st_m_m101 + (-49 / 576) * rel5_st_m_m10m + (79 / 480) * rel5_st_m_m1m1 +
    (619 / 1152) * rel5_sh_01_00m + (7 / 24) * rel5_sh_01_01m + (-13 / 48) * rel5_sh_01_0m1 +
    (-1 / 16) * rel5_st_01_0m1 + (931 / 384) * rel5_st_01_0mm + (7 / 6) * rel5_sh_01_m11 +
    (-883 / 1152) * rel5_sh_0m_001 + (-167 / 384) * rel5_sh_0m_01m + (-1) * rel5_sh_m1_011 +
    (-131 / 384) * rel5_sh_m1_0m1 + (-323 / 384) * rel5_sh_m1_m01 + (13) * rel5_mob_00mmm +
    (339 / 128) * rel5_mob_01mmm + (17 / 4) * rel5_mob_0m0mm + (113 / 128) * rel5_mob_0m1mm +
    (-193 / 128) * rel5_mob_m10mm + (-101 / 288) * rel5_st_m_011m + (17 / 48) * rel5_st_m_01mm +
    (-33 / 128) * rel5_st_m_0m11 + (67 / 384) * rel5_st_m_0mm1 + (-193 / 128) * rel5_st_m_m011 +
    (35 / 48) * rel5_st_m_m0mm + (-7 / 144) * rel5_st_m_m11m + (-1 / 8) * rel5_st_m_m1mm +
    (161 / 288) * rel5_st_m_mm0m + (-43 / 144) * rel5_st_m_mm1m + (1 / 2) * rel5_st_m_0mmm +
    (-3) * rel5_mob_0000m

theorem hpl_negOne_one_negOne_one_negOne_at_one :
    hpl [negOne, one, negOne, one, negOne] 1 =
      1 / 120 * log 2 ^ 5 - 1 / 72 * log 2 ^ 3 * π ^ 2 + 1 / 8 * log 2 ^ 2 * zeta3
      + 1 / 1440 * log 2 * π ^ 4 - 1 / 48 * zeta3 * π ^ 2 + 3 / 16 * zeta5 := by
  linear_combination (1 / 5) * hpl_zero_zero_zero_zero_negOne_at_one + (-1 / 10) * rel5_st_m_0001 +
    (-1 / 10) * rel5_st_01_00m + (-1 / 30) * rel5_st_m_00m1 + (-1 / 30) * rel5_st_m_m001 +
    (1 / 15) * rel5_st_01_01m + (-1 / 15) * rel5_st_01_m0m + (1 / 15) * rel5_st_m_01m1 +
    (-1 / 15) * rel5_st_m_m0m1 + (1 / 15) * rel5_st_m_m101 + (1 / 5) * rel5_st_m_m1m1

theorem hpl_negOne_one_negOne_negOne_one_at_one :
    hpl [negOne, one, negOne, negOne, one] 1 =
      -3 * Li 5 (1 / 2) + 1 / 30 * log 2 ^ 5 - 1 / 18 * log 2 ^ 3 * π ^ 2
      + 23 / 16 * log 2 ^ 2 * zeta3 - 1 / 30 * log 2 * π ^ 4 - 23 / 96 * zeta3 * π ^ 2
      + 369 / 64 * zeta5 := by
  linear_combination (-331 / 384) * hpl_zero_zero_zero_zero_one_at_one +
    (11 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (53 / 384) * hpl_zero_zero_one_zero_one_at_one +
    (109 / 384) * hpl_zero_one_zero_zero_one_at_one + (-3 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-9 / 8) * hpl_zero_one_zero_one_one_at_one + (-3 / 8) * hpl_zero_one_one_zero_one_at_one +
    (69 / 20) * hpl_zero_zero_zero_zero_negOne_at_one + (-3) * hpl_negOne_one_one_one_one_at_one +
    (-211 / 640) * rel5_sh_m_mmmm + (-25 / 256) * rel5_sh_m_0mmm + (25 / 768) * rel5_sh_m_m0mm +
    (-1) * rel5_sh_m_m1mm + (-49 / 192) * rel5_sh_m_mm0m + (-233 / 256) * rel5_sh_m_mm1m +
    (-69 / 256) * rel5_sh_m_mmm1 + (-1627 / 5120) * rel5_st_m_0001 + (5 / 256) * rel5_st_m_000m +
    (1 / 24) * rel5_sh_m_00mm + (57 / 128) * rel5_sh_m_01mm + (-11 / 96) * rel5_sh_m_0m0m +
    (41 / 128) * rel5_sh_m_0m1m + (1 / 2) * rel5_sh_m_0mm1 + (57 / 256) * rel5_sh_m_m01m +
    (5 / 64) * rel5_sh_m_m0m1 + (73 / 256) * rel5_sh_m_m10m + (-3 / 2) * rel5_sh_m_m11m +
    (-35 / 32) * rel5_sh_m_m1m1 + (-57 / 128) * rel5_sh_m_mm01 + (1883 / 5120) * rel5_st_01_00m +
    (-1 / 2) * rel5_st_0m_001 + (53 / 384) * rel5_sh_0m_00m + (647 / 768) * rel5_st_0m_00m +
    (-1 / 48) * rel5_sh_0m_0mm + (1 / 2) * rel5_sh_m1_m11 + (-1 / 2) * rel5_sh_m1_mm1 +
    (-25 / 64) * rel5_mob_0mmm1 + (25 / 96) * rel5_sh_m_000m + (5 / 192) * rel5_sh_m_001m +
    (-29 / 384) * rel5_st_m_001m + (7 / 192) * rel5_sh_m_00m1 + (-29 / 320) * rel5_st_m_00m1 +
    (11 / 128) * rel5_sh_m_010m + (-13 / 64) * rel5_sh_m_01m1 + (-23 / 48) * rel5_sh_m_0m01 +
    (-57 / 64) * rel5_sh_m_0m11 + (-29 / 192) * rel5_sh_m_m001 + (-87 / 2560) * rel5_st_m_m001 +
    (29 / 384) * rel5_st_m_m00m + (-73 / 64) * rel5_sh_m_m011 + (-83 / 128) * rel5_sh_m_m101 +
    (-3) * rel5_sh_m_m111 + (269 / 15360) * rel5_st_01_01m + (-3319 / 15360) * rel5_st_01_m0m +
    (-5 / 64) * rel5_st_0m_0m1 + (13 / 24) * rel5_st_0m_0mm + (-21 / 64) * rel5_st_0m_m01 +
    (-43 / 768) * rel5_sh_m_0001 + (13 / 24) * rel5_sh_m_0011 + (203 / 384) * rel5_st_m_0011 +
    (7 / 48) * rel5_st_m_00mm + (97 / 192) * rel5_sh_m_0101 + (-5 / 24) * rel5_st_m_010m +
    (13 / 320) * rel5_st_m_01m1 + (1 / 16) * rel5_st_m_0m0m + (-61 / 192) * rel5_st_m_0m1m +
    (-17 / 64) * rel5_st_m_m01m + (-639 / 2560) * rel5_st_m_m0m1 + (87 / 1280) * rel5_st_m_m101 +
    (-29 / 192) * rel5_st_m_m10m + (-13 / 160) * rel5_st_m_m1m1 + (-161 / 384) * rel5_sh_01_00m +
    (-1 / 8) * rel5_sh_01_01m + (-1 / 16) * rel5_sh_01_0m1 + (-3 / 16) * rel5_st_01_0m1 +
    (-105 / 128) * rel5_st_01_0mm + (1 / 2) * rel5_sh_01_m11 + (185 / 384) * rel5_sh_0m_001 +
    (5 / 128) * rel5_sh_0m_01m + (9 / 128) * rel5_sh_m1_0m1 + (73 / 128) * rel5_sh_m1_m01 +
    (-171 / 128) * rel5_mob_01mmm + (-1 / 4) * rel5_mob_0m0mm + (-57 / 128) * rel5_mob_0m1mm +
    (73 / 128) * rel5_mob_m10mm + (7 / 96) * rel5_st_m_011m + (-7 / 16) * rel5_st_m_01mm +
    (41 / 128) * rel5_st_m_0m11 + (-73 / 128) * rel5_st_m_0mm1 + (73 / 128) * rel5_st_m_m011 +
    (11 / 16) * rel5_st_m_m0mm + (5 / 48) * rel5_st_m_m11m + (-3 / 8) * rel5_st_m_m1mm +
    (29 / 96) * rel5_st_m_mm0m + (-7 / 48) * rel5_st_m_mm1m + (3 / 2) * rel5_st_m_0mmm +
    (-3) * rel5_mob_0000m

theorem hpl_negOne_one_negOne_negOne_negOne_at_one :
    hpl [negOne, one, negOne, negOne, negOne] 1 =
      Li 4 (1 / 2) * log 2 + 4 * Li 5 (1 / 2) + 1 / 36 * log 2 ^ 3 * π ^ 2
      - log 2 ^ 2 * zeta3 + 1 / 30 * log 2 * π ^ 4 - 4 * zeta5 := by
  linear_combination (97 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 4) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 96) * hpl_zero_one_zero_zero_one_at_one + (2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 2) * hpl_zero_one_zero_one_one_at_one + (1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (-74 / 15) * hpl_zero_zero_zero_zero_negOne_at_one + (4) * hpl_negOne_one_one_one_one_at_one +
    (-1637 / 480) * rel5_sh_m_mmmm + (49 / 192) * rel5_sh_m_0mmm + (-49 / 576) * rel5_sh_m_m0mm +
    (5 / 3) * rel5_sh_m_m1mm + (-23 / 144) * rel5_sh_m_mm0m + (-511 / 192) * rel5_sh_m_mm1m +
    (-257 / 64) * rel5_sh_m_mmm1 + (129 / 1280) * rel5_st_m_0001 + (889 / 576) * rel5_st_m_000m +
    (13 / 6) * rel5_sh_m_00mm + (47 / 96) * rel5_sh_m_01mm + (-35 / 24) * rel5_sh_m_0m0m +
    (-1 / 96) * rel5_sh_m_0m1m + (-2 / 3) * rel5_sh_m_0mm1 + (47 / 192) * rel5_sh_m_m01m +
    (-13 / 48) * rel5_sh_m_m0m1 + (95 / 192) * rel5_sh_m_m10m + (2) * rel5_sh_m_m11m +
    (25 / 8) * rel5_sh_m_m1m1 + (-47 / 96) * rel5_sh_m_mm01 + (479 / 1280) * rel5_st_01_00m +
    (11 / 24) * rel5_st_0m_001 + (-13 / 32) * rel5_sh_0m_00m + (-1471 / 576) * rel5_st_0m_00m +
    (19 / 12) * rel5_sh_0m_0mm + (-2 / 3) * rel5_sh_m1_m11 + (-2) * rel5_sh_m1_mm1 +
    (49 / 48) * rel5_mob_0mmm1 + (9 / 8) * rel5_sh_m_000m + (-71 / 48) * rel5_sh_m_001m +
    (325 / 288) * rel5_st_m_001m + (-85 / 48) * rel5_sh_m_00m1 + (847 / 720) * rel5_st_m_00m1 +
    (-43 / 96) * rel5_sh_m_010m + (-11 / 48) * rel5_sh_m_01m1 + (-1 / 12) * rel5_sh_m_0m01 +
    (17 / 48) * rel5_sh_m_0m11 + (23 / 48) * rel5_sh_m_m001 + (-259 / 5760) * rel5_st_m_m001 +
    (-37 / 288) * rel5_st_m_m00m + (-31 / 48) * rel5_sh_m_m011 + (-5 / 96) * rel5_sh_m_m101 +
    (4) * rel5_sh_m_m111 + (-7109 / 11520) * rel5_st_01_01m + (-8161 / 11520) * rel5_st_01_m0m +
    (35 / 48) * rel5_st_0m_0m1 + (-13 / 6) * rel5_st_0m_0mm + (-13 / 48) * rel5_st_0m_m01 +
    (107 / 64) * rel5_sh_m_0001 + (3 / 2) * rel5_sh_m_0011 + (-113 / 96) * rel5_st_m_0011 +
    (-37 / 12) * rel5_st_m_00mm + (23 / 16) * rel5_sh_m_0101 + (13 / 9) * rel5_st_m_010m +
    (1 / 720) * rel5_st_m_01m1 + (-85 / 36) * rel5_st_m_0m0m + (37 / 144) * rel5_st_m_0m1m +
    (-5 / 144) * rel5_st_m_m01m + (757 / 5760) * rel5_st_m_m0m1 + (259 / 2880) * rel5_st_m_m101 +
    (37 / 144) * rel5_st_m_m10m + (-9 / 40) * rel5_st_m_m1m1 + (19 / 96) * rel5_sh_01_00m +
    (-1 / 6) * rel5_sh_01_01m + (5 / 12) * rel5_sh_01_0m1 + (1 / 4) * rel5_st_01_0m1 +
    (-95 / 96) * rel5_st_01_0mm + (-2) * rel5_sh_01_m11 + (5 / 96) * rel5_sh_0m_001 +
    (43 / 96) * rel5_sh_0m_01m + (4 / 3) * rel5_sh_m1_011 + (31 / 96) * rel5_sh_m1_0m1 +
    (31 / 96) * rel5_sh_m1_m01 + (-16) * rel5_mob_00mmm + (-47 / 32) * rel5_mob_01mmm +
    (-5) * rel5_mob_0m0mm + (-47 / 96) * rel5_mob_0m1mm + (95 / 96) * rel5_mob_m10mm +
    (11 / 24) * rel5_st_m_011m + (-1 / 12) * rel5_st_m_01mm + (-1 / 96) * rel5_st_m_0m11 +
    (11 / 32) * rel5_st_m_0mm1 + (95 / 96) * rel5_st_m_m011 + (-19 / 12) * rel5_st_m_m0mm +
    (1 / 12) * rel5_st_m_m11m + (1 / 2) * rel5_st_m_m1mm + (-23 / 24) * rel5_st_m_mm0m +
    (5 / 12) * rel5_st_m_mm1m + (-2) * rel5_st_m_0mmm + (4) * rel5_mob_0000m

end QED.Polylog.HPL
