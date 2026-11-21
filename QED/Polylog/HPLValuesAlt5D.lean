/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLAlt5Rel

/-!
# Harmonic polylogarithms at `1`: alternating words of weight five (D)

The values `H(w; 1)` of the 18 words `w` of weight five over `{0, 1, -1}`
starting with `-1, -1` and with no trailing zero (excluding those known in closed form in
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

theorem hpl_negOne_negOne_zero_zero_one_at_one :
    hpl [negOne, negOne, zero, zero, one] 1 =
      2 * Li 4 (1 / 2) * log 2 + 4 * Li 5 (1 / 2) + 1 / 20 * log 2 ^ 5
      - 1 / 36 * log 2 ^ 3 * π ^ 2 + 1 / 2 * log 2 ^ 2 * zeta3 + 1 / 60 * log 2 * π ^ 4
      - 1 / 8 * zeta3 * π ^ 2 - 39 / 16 * zeta5 := by
  linear_combination (239 / 144) * hpl_zero_zero_zero_zero_one_at_one +
    (-37 / 6) * hpl_zero_zero_zero_one_one_at_one +
    (-583 / 144) * hpl_zero_zero_one_zero_one_at_one +
    (-215 / 144) * hpl_zero_one_zero_zero_one_at_one + (1) * hpl_zero_zero_one_one_one_at_one +
    (1) * hpl_zero_one_zero_one_one_at_one + (1 / 3) * hpl_zero_one_one_zero_one_at_one +
    (-17 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (4) * hpl_negOne_one_one_one_one_at_one +
    (-89 / 30) * rel5_sh_m_mmmm + (5 / 24) * rel5_sh_m_0mmm + (-5 / 72) * rel5_sh_m_m0mm +
    (4 / 3) * rel5_sh_m_m1mm + (-17 / 36) * rel5_sh_m_mm0m + (-11 / 4) * rel5_sh_m_mm1m +
    (-13 / 4) * rel5_sh_m_mmm1 + (25 / 64) * rel5_st_m_0001 + (25 / 32) * rel5_st_m_000m +
    (7 / 9) * rel5_sh_m_00mm + (13 / 12) * rel5_sh_m_01mm + (-217 / 72) * rel5_sh_m_0m0m +
    (1 / 3) * rel5_sh_m_0m1m + (-1 / 3) * rel5_sh_m_0mm1 + (13 / 24) * rel5_sh_m_m01m +
    (-7 / 24) * rel5_sh_m_m0m1 + (11 / 12) * rel5_sh_m_m10m + (2) * rel5_sh_m_m11m +
    (73 / 24) * rel5_sh_m_m1m1 + (-13 / 12) * rel5_sh_m_mm01 + (169 / 96) * rel5_st_01_00m +
    (-31 / 64) * rel5_st_0m_001 + (-53 / 288) * rel5_sh_0m_00m + (-703 / 288) * rel5_st_0m_00m +
    (79 / 36) * rel5_sh_0m_0mm + (-2 / 3) * rel5_sh_m1_m11 + (-23 / 12) * rel5_sh_m1_mm1 +
    (5 / 6) * rel5_mob_0mmm1 + (887 / 288) * rel5_sh_m_000m + (-281 / 144) * rel5_sh_m_001m +
    (127 / 144) * rel5_st_m_001m + (-167 / 72) * rel5_sh_m_00m1 + (133 / 144) * rel5_st_m_00m1 +
    (-7 / 96) * rel5_sh_m_010m + (-13 / 24) * rel5_sh_m_01m1 + (-11 / 18) * rel5_sh_m_0m01 +
    (-1 / 2) * rel5_sh_m_0m11 + (73 / 72) * rel5_sh_m_m001 + (-17 / 144) * rel5_st_m_m001 +
    (-19 / 144) * rel5_st_m_m00m + (-2) * rel5_sh_m_m011 + (-17 / 24) * rel5_sh_m_m101 +
    (4) * rel5_sh_m_m111 + (-25 / 96) * rel5_st_01_01m + (-487 / 288) * rel5_st_01_m0m +
    (119 / 192) * rel5_st_0m_0m1 + (-20 / 9) * rel5_st_0m_0mm + (-169 / 192) * rel5_st_0m_m01 +
    (263 / 288) * rel5_sh_m_0001 + (22 / 9) * rel5_sh_m_0011 + (19 / 18) * rel5_st_m_0011 +
    (-71 / 18) * rel5_st_m_00mm + (175 / 72) * rel5_sh_m_0101 + (49 / 36) * rel5_st_m_010m +
    (1 / 9) * rel5_st_m_01m1 + (-19 / 6) * rel5_st_m_0m0m + (-1 / 72) * rel5_st_m_0m1m +
    (-7 / 24) * rel5_st_m_m01m + (-19 / 144) * rel5_st_m_m0m1 + (17 / 72) * rel5_st_m_m101 +
    (19 / 72) * rel5_st_m_m10m + (-5 / 24) * rel5_st_m_m1m1 + (-233 / 144) * rel5_sh_01_00m +
    (-5 / 6) * rel5_sh_01_01m + (1 / 2) * rel5_sh_01_0m1 + (1 / 4) * rel5_st_01_0m1 +
    (-4) * rel5_st_01_0mm + (-13 / 6) * rel5_sh_01_m11 + (257 / 144) * rel5_sh_0m_001 +
    (37 / 32) * rel5_sh_0m_01m + (11 / 6) * rel5_sh_m1_011 + (1 / 2) * rel5_sh_m1_0m1 +
    (1) * rel5_sh_m1_m01 + (-31 / 2) * rel5_mob_00mmm + (-13 / 4) * rel5_mob_01mmm +
    (-5) * rel5_mob_0m0mm + (-13 / 12) * rel5_mob_0m1mm + (11 / 6) * rel5_mob_m10mm +
    (25 / 36) * rel5_st_m_011m + (-1 / 2) * rel5_st_m_01mm + (1 / 3) * rel5_st_m_0m11 +
    (-1 / 6) * rel5_st_m_0mm1 + (11 / 6) * rel5_st_m_m011 + (-3 / 2) * rel5_st_m_m0mm +
    (1 / 9) * rel5_st_m_m11m + (1 / 2) * rel5_st_m_m1mm + (-37 / 36) * rel5_st_m_mm0m +
    (4 / 9) * rel5_st_m_mm1m + (-1) * rel5_st_m_0mmm + (4) * rel5_mob_0000m

theorem hpl_negOne_negOne_zero_zero_negOne_at_one :
    hpl [negOne, negOne, zero, zero, negOne] 1 =
      -2 * Li 4 (1 / 2) * log 2 - 2 * Li 5 (1 / 2) - 1 / 15 * log 2 ^ 5
      + 1 / 18 * log 2 ^ 3 * π ^ 2 - 1 / 2 * log 2 ^ 2 * zeta3 - 1 / 288 * log 2 * π ^ 4
      + 1 / 96 * zeta3 * π ^ 2 + 125 / 64 * zeta5 := by
  linear_combination (-97 / 192) * hpl_zero_zero_zero_zero_one_at_one +
    (21 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (335 / 192) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 192) * hpl_zero_one_zero_zero_one_at_one + (-1) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 4) * hpl_zero_one_zero_one_one_at_one + (-1 / 4) * hpl_zero_one_one_zero_one_at_one +
    (29 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-2) * hpl_negOne_one_one_one_one_at_one +
    (869 / 960) * rel5_sh_m_mmmm + (-49 / 384) * rel5_sh_m_0mmm + (49 / 1152) * rel5_sh_m_m0mm +
    (-2 / 3) * rel5_sh_m_m1mm + (23 / 288) * rel5_sh_m_mm0m + (85 / 128) * rel5_sh_m_mm1m +
    (129 / 128) * rel5_sh_m_mmm1 + (-13 / 512) * rel5_st_m_0001 + (-889 / 1152) * rel5_st_m_000m +
    (-25 / 12) * rel5_sh_m_00mm + (-47 / 192) * rel5_sh_m_01mm + (11 / 48) * rel5_sh_m_0m0m +
    (1 / 192) * rel5_sh_m_0m1m + (1 / 3) * rel5_sh_m_0mm1 + (1 / 2) * rel5_sh_m_m00m +
    (-47 / 384) * rel5_sh_m_m01m + (13 / 96) * rel5_sh_m_m0m1 + (-95 / 384) * rel5_sh_m_m10m +
    (-1) * rel5_sh_m_m11m + (-21 / 16) * rel5_sh_m_m1m1 + (47 / 192) * rel5_sh_m_mm01 +
    (-83 / 512) * rel5_st_01_00m + (-11 / 48) * rel5_st_0m_001 + (13 / 64) * rel5_sh_0m_00m +
    (1471 / 1152) * rel5_st_0m_00m + (5 / 24) * rel5_sh_0m_0mm + (1 / 3) * rel5_sh_m1_m11 +
    (1 / 2) * rel5_sh_m1_mm1 + (-49 / 96) * rel5_mob_0mmm1 + (-9 / 16) * rel5_sh_m_000m +
    (71 / 96) * rel5_sh_m_001m + (-325 / 576) * rel5_st_m_001m + (85 / 96) * rel5_sh_m_00m1 +
    (-167 / 288) * rel5_st_m_00m1 + (43 / 192) * rel5_sh_m_010m + (11 / 96) * rel5_sh_m_01m1 +
    (1 / 24) * rel5_sh_m_0m01 + (-17 / 96) * rel5_sh_m_0m11 + (-23 / 96) * rel5_sh_m_m001 +
    (71 / 2304) * rel5_st_m_m001 + (37 / 576) * rel5_st_m_m00m + (31 / 96) * rel5_sh_m_m011 +
    (5 / 192) * rel5_sh_m_m101 + (-2) * rel5_sh_m_m111 + (1345 / 4608) * rel5_st_01_01m +
    (1709 / 4608) * rel5_st_01_m0m + (-35 / 96) * rel5_st_0m_0m1 + (13 / 12) * rel5_st_0m_0mm +
    (13 / 96) * rel5_st_0m_m01 + (-107 / 128) * rel5_sh_m_0001 + (-3 / 4) * rel5_sh_m_0011 +
    (113 / 192) * rel5_st_m_0011 + (37 / 24) * rel5_st_m_00mm + (-23 / 32) * rel5_sh_m_0101 +
    (-13 / 18) * rel5_st_m_010m + (-5 / 288) * rel5_st_m_01m1 + (85 / 72) * rel5_st_m_0m0m +
    (-37 / 288) * rel5_st_m_0m1m + (5 / 288) * rel5_st_m_m01m + (-113 / 2304) * rel5_st_m_m0m1 +
    (-71 / 1152) * rel5_st_m_m101 + (-37 / 288) * rel5_st_m_m10m + (1 / 16) * rel5_st_m_m1m1 +
    (-19 / 192) * rel5_sh_01_00m + (1 / 12) * rel5_sh_01_01m + (-5 / 24) * rel5_sh_01_0m1 +
    (-1 / 8) * rel5_st_01_0m1 + (95 / 192) * rel5_st_01_0mm + (1) * rel5_sh_01_m11 +
    (-5 / 192) * rel5_sh_0m_001 + (-43 / 192) * rel5_sh_0m_01m + (-2 / 3) * rel5_sh_m1_011 +
    (-31 / 192) * rel5_sh_m1_0m1 + (-31 / 192) * rel5_sh_m1_m01 + (5) * rel5_mob_00mmm +
    (47 / 64) * rel5_mob_01mmm + (3 / 2) * rel5_mob_0m0mm + (47 / 192) * rel5_mob_0m1mm +
    (-95 / 192) * rel5_mob_m10mm + (-11 / 48) * rel5_st_m_011m + (1 / 24) * rel5_st_m_01mm +
    (1 / 192) * rel5_st_m_0m11 + (-11 / 64) * rel5_st_m_0mm1 + (-95 / 192) * rel5_st_m_m011 +
    (19 / 24) * rel5_st_m_m0mm + (-1 / 24) * rel5_st_m_m11m + (-1 / 4) * rel5_st_m_m1mm +
    (23 / 48) * rel5_st_m_mm0m + (-5 / 24) * rel5_st_m_mm1m + (1) * rel5_st_m_0mmm +
    (-2) * rel5_mob_0000m

theorem hpl_negOne_negOne_zero_one_one_at_one :
    hpl [negOne, negOne, zero, one, one] 1 =
      Li 5 (1 / 2) - 1 / 120 * log 2 ^ 5 + 1 / 72 * log 2 ^ 3 * π ^ 2
      + 1 / 16 * log 2 ^ 2 * zeta3 + 1 / 288 * log 2 * π ^ 4 - 25 / 32 * zeta5 := by
  linear_combination (2039 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (-37 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (-529 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (-281 / 1152) * hpl_zero_one_zero_zero_one_at_one +
    (1 / 2) * hpl_zero_zero_one_one_one_at_one + (3 / 8) * hpl_zero_one_zero_one_one_at_one +
    (1 / 8) * hpl_zero_one_one_zero_one_at_one +
    (-31 / 15) * hpl_zero_zero_zero_zero_negOne_at_one + (1) * hpl_negOne_one_one_one_one_at_one +
    (6679 / 1920) * rel5_sh_m_mmmm + (-827 / 768) * rel5_sh_m_0mmm +
    (827 / 2304) * rel5_sh_m_m0mm + (1 / 3) * rel5_sh_m_m1mm + (-563 / 576) * rel5_sh_m_mm0m +
    (757 / 768) * rel5_sh_m_mm1m + (1163 / 256) * rel5_sh_m_mmm1 +
    (9167 / 15360) * rel5_st_m_0001 + (-1867 / 2304) * rel5_st_m_000m +
    (55 / 72) * rel5_sh_m_00mm + (475 / 384) * rel5_sh_m_01mm + (169 / 288) * rel5_sh_m_0m0m +
    (25 / 128) * rel5_sh_m_0m1m + (-1 / 6) * rel5_sh_m_0mm1 + (91 / 768) * rel5_sh_m_m01m +
    (-3 / 64) * rel5_sh_m_m0m1 + (299 / 768) * rel5_sh_m_m10m + (1 / 2) * rel5_sh_m_m11m +
    (-5 / 96) * rel5_sh_m_m1m1 + (-475 / 384) * rel5_sh_m_mm01 + (4097 / 15360) * rel5_st_01_00m +
    (13 / 64) * rel5_st_0m_001 + (-229 / 1152) * rel5_sh_0m_00m + (-737 / 768) * rel5_st_0m_00m +
    (-187 / 144) * rel5_sh_0m_0mm + (-1 / 6) * rel5_sh_m1_m11 + (5 / 4) * rel5_sh_m1_mm1 +
    (-827 / 192) * rel5_mob_0mmm1 + (13 / 18) * rel5_sh_m_000m + (-109 / 576) * rel5_sh_m_001m +
    (59 / 384) * rel5_st_m_001m + (-131 / 576) * rel5_sh_m_00m1 + (47 / 2880) * rel5_st_m_00m1 +
    (-57 / 128) * rel5_sh_m_010m + (1 / 192) * rel5_sh_m_01m1 + (5 / 72) * rel5_sh_m_0m01 +
    (-155 / 192) * rel5_sh_m_0m11 + (49 / 576) * rel5_sh_m_m001 +
    (-1919 / 23040) * rel5_st_m_m001 + (-11 / 384) * rel5_st_m_m00m + (-57 / 64) * rel5_sh_m_m011 +
    (-51 / 128) * rel5_sh_m_m101 + (1) * rel5_sh_m_m111 + (2551 / 46080) * rel5_st_01_01m +
    (1913 / 15360) * rel5_st_01_m0m + (-1 / 12) * rel5_st_0m_0m1 + (-13 / 36) * rel5_st_0m_0mm +
    (-1 / 6) * rel5_st_0m_m01 + (-1801 / 2304) * rel5_sh_m_0001 + (7 / 72) * rel5_sh_m_0011 +
    (17 / 1152) * rel5_st_m_0011 + (-59 / 144) * rel5_st_m_00mm + (55 / 576) * rel5_sh_m_0101 +
    (31 / 144) * rel5_st_m_010m + (101 / 2880) * rel5_st_m_01m1 + (-11 / 36) * rel5_st_m_0m0m +
    (49 / 576) * rel5_st_m_0m1m + (23 / 576) * rel5_st_m_m01m + (-3943 / 23040) * rel5_st_m_m0m1 +
    (1919 / 11520) * rel5_st_m_m101 + (11 / 192) * rel5_st_m_m10m + (53 / 480) * rel5_st_m_m1m1 +
    (-467 / 1152) * rel5_sh_01_00m + (1 / 16) * rel5_sh_01_0m1 + (1 / 16) * rel5_st_01_0m1 +
    (-91 / 384) * rel5_st_01_0mm + (-1 / 3) * rel5_sh_01_m11 + (491 / 1152) * rel5_sh_0m_001 +
    (67 / 384) * rel5_sh_0m_01m + (1 / 6) * rel5_sh_m1_011 + (203 / 384) * rel5_sh_m1_0m1 +
    (57 / 128) * rel5_sh_m1_m01 + (11 / 2) * rel5_mob_00mmm + (-475 / 128) * rel5_mob_01mmm +
    (29 / 12) * rel5_mob_0m0mm + (-91 / 384) * rel5_mob_0m1mm + (299 / 384) * rel5_mob_m10mm +
    (13 / 288) * rel5_st_m_011m + (1 / 16) * rel5_st_m_01mm + (89 / 128) * rel5_st_m_0m11 +
    (-43 / 384) * rel5_st_m_0mm1 + (299 / 384) * rel5_st_m_m011 + (-5 / 16) * rel5_st_m_m0mm +
    (-1 / 144) * rel5_st_m_m11m + (1 / 8) * rel5_st_m_m1mm + (-49 / 288) * rel5_st_m_mm0m +
    (11 / 144) * rel5_st_m_mm1m + (-1 / 2) * rel5_st_m_0mmm + (-1) * rel5_mob_001mm +
    (1) * rel5_mob_0000m

theorem hpl_negOne_negOne_zero_one_negOne_at_one :
    hpl [negOne, negOne, zero, one, negOne] 1 =
      4 * Li 4 (1 / 2) * log 2 + 3 * Li 5 (1 / 2) + 17 / 120 * log 2 ^ 5
      + 13 / 16 * log 2 ^ 2 * zeta3 - 1 / 288 * log 2 * π ^ 4 - 99 / 32 * zeta5 := by
  linear_combination (1 / 128) * hpl_zero_zero_zero_zero_one_at_one +
    (-63 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 128) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 128) * hpl_zero_one_zero_zero_one_at_one + (3 / 2) * hpl_zero_zero_one_one_one_at_one +
    (9 / 8) * hpl_zero_one_zero_one_one_at_one + (3 / 8) * hpl_zero_one_one_zero_one_at_one +
    (-3) * hpl_zero_zero_zero_zero_negOne_at_one + (3) * hpl_negOne_one_one_one_one_at_one +
    (-3029 / 640) * rel5_sh_m_mmmm + (289 / 256) * rel5_sh_m_0mmm + (-289 / 768) * rel5_sh_m_m0mm +
    (1) * rel5_sh_m_m1mm + (121 / 192) * rel5_sh_m_mm0m + (-527 / 256) * rel5_sh_m_mm1m +
    (-1491 / 256) * rel5_sh_m_mmm1 + (-297 / 1024) * rel5_st_m_0001 +
    (1369 / 768) * rel5_st_m_000m + (13 / 8) * rel5_sh_m_00mm + (-65 / 128) * rel5_sh_m_01mm +
    (-43 / 32) * rel5_sh_m_0m0m + (-49 / 128) * rel5_sh_m_0m1m + (-1 / 2) * rel5_sh_m_0mm1 +
    (63 / 256) * rel5_sh_m_m01m + (-13 / 64) * rel5_sh_m_m0m1 + (47 / 256) * rel5_sh_m_m10m +
    (3 / 2) * rel5_sh_m_m11m + (83 / 32) * rel5_sh_m_m1m1 + (65 / 128) * rel5_sh_m_mm01 +
    (-87 / 1024) * rel5_st_01_00m + (3 / 8) * rel5_st_0m_001 + (-31 / 128) * rel5_sh_0m_00m +
    (-1375 / 768) * rel5_st_0m_00m + (27 / 16) * rel5_sh_0m_0mm + (-1 / 2) * rel5_sh_m1_m11 +
    (-2) * rel5_sh_m1_mm1 + (289 / 64) * rel5_mob_0mmm1 + (9 / 32) * rel5_sh_m_000m +
    (-63 / 64) * rel5_sh_m_001m + (325 / 384) * rel5_st_m_001m + (-85 / 64) * rel5_sh_m_00m1 +
    (57 / 64) * rel5_st_m_00m1 + (-35 / 128) * rel5_sh_m_010m + (-11 / 64) * rel5_sh_m_01m1 +
    (-1 / 16) * rel5_sh_m_0m01 + (65 / 64) * rel5_sh_m_0m11 + (23 / 64) * rel5_sh_m_m001 +
    (3 / 512) * rel5_st_m_m001 + (-37 / 384) * rel5_st_m_m00m + (17 / 64) * rel5_sh_m_m011 +
    (43 / 128) * rel5_sh_m_m101 + (3) * rel5_sh_m_m111 + (-571 / 1024) * rel5_st_01_01m +
    (-543 / 1024) * rel5_st_01_m0m + (45 / 64) * rel5_st_0m_0m1 + (-13 / 8) * rel5_st_0m_0mm +
    (-3 / 64) * rel5_st_0m_m01 + (481 / 256) * rel5_sh_m_0001 + (9 / 8) * rel5_sh_m_0011 +
    (-161 / 128) * rel5_st_m_0011 + (-37 / 16) * rel5_st_m_00mm + (69 / 64) * rel5_sh_m_0101 +
    (13 / 12) * rel5_st_m_010m + (-1 / 64) * rel5_st_m_01m1 + (-85 / 48) * rel5_st_m_0m0m +
    (37 / 192) * rel5_st_m_0m1m + (-5 / 192) * rel5_st_m_m01m + (139 / 512) * rel5_st_m_m0m1 +
    (-3 / 256) * rel5_st_m_m101 + (37 / 192) * rel5_st_m_m10m + (-7 / 32) * rel5_st_m_m1m1 +
    (83 / 128) * rel5_sh_01_00m + (-1 / 8) * rel5_sh_01_01m + (5 / 16) * rel5_sh_01_0m1 +
    (3 / 16) * rel5_st_01_0m1 + (-47 / 128) * rel5_st_01_0mm + (-3 / 2) * rel5_sh_01_m11 +
    (-59 / 128) * rel5_sh_0m_001 + (35 / 128) * rel5_sh_0m_01m + (1) * rel5_sh_m1_011 +
    (-17 / 128) * rel5_sh_m1_0m1 + (-17 / 128) * rel5_sh_m1_m01 + (-15) * rel5_mob_00mmm +
    (195 / 128) * rel5_mob_01mmm + (-19 / 4) * rel5_mob_0m0mm + (65 / 128) * rel5_mob_0m1mm +
    (47 / 128) * rel5_mob_m10mm + (11 / 32) * rel5_st_m_011m + (-1 / 16) * rel5_st_m_01mm +
    (-49 / 128) * rel5_st_m_0m11 + (81 / 128) * rel5_st_m_0mm1 + (47 / 128) * rel5_st_m_m011 +
    (-19 / 16) * rel5_st_m_m0mm + (1 / 16) * rel5_st_m_m11m + (3 / 8) * rel5_st_m_m1mm +
    (-23 / 32) * rel5_st_m_mm0m + (5 / 16) * rel5_st_m_mm1m + (-3 / 2) * rel5_st_m_0mmm +
    (3) * rel5_mob_0000m

theorem hpl_negOne_negOne_zero_negOne_one_at_one :
    hpl [negOne, negOne, zero, negOne, one] 1 =
      -Li 4 (1 / 2) * log 2 - 1 / 24 * log 2 ^ 5 - 1 / 12 * log 2 ^ 3 * π ^ 2
      + 13 / 16 * log 2 ^ 2 * zeta3 - 1 / 1440 * log 2 * π ^ 4 - 7 / 32 * zeta3 * π ^ 2
      + 87 / 32 * zeta5 := by
  linear_combination (67 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (-13 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (-119 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (-43 / 96) * hpl_zero_one_zero_zero_one_at_one +
    (1 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (-183 / 32) * rel5_sh_m_mmmm +
    (111 / 64) * rel5_sh_m_0mmm + (-37 / 64) * rel5_sh_m_m0mm + (1 / 16) * rel5_sh_m_mm0m +
    (-201 / 64) * rel5_sh_m_mm1m + (-453 / 64) * rel5_sh_m_mmm1 + (-19 / 256) * rel5_st_m_0001 +
    (65 / 192) * rel5_st_m_000m + (1 / 3) * rel5_sh_m_00mm + (1 / 32) * rel5_sh_m_01mm +
    (-101 / 48) * rel5_sh_m_0m0m + (9 / 32) * rel5_sh_m_0m1m + (1 / 64) * rel5_sh_m_m01m +
    (-1 / 16) * rel5_sh_m_m0m1 + (9 / 64) * rel5_sh_m_m10m + (5 / 4) * rel5_sh_m_m1m1 +
    (-1 / 32) * rel5_sh_m_mm01 + (47 / 256) * rel5_st_01_00m + (-39 / 64) * rel5_st_0m_001 +
    (-7 / 48) * rel5_sh_0m_00m + (-199 / 192) * rel5_st_0m_00m + (31 / 12) * rel5_sh_0m_0mm +
    (-11 / 4) * rel5_sh_m1_mm1 + (111 / 16) * rel5_mob_0mmm1 + (131 / 96) * rel5_sh_m_000m +
    (-5 / 12) * rel5_sh_m_001m + (37 / 96) * rel5_st_m_001m + (-31 / 48) * rel5_sh_m_00m1 +
    (7 / 24) * rel5_st_m_00m1 + (9 / 16) * rel5_sh_m_010m + (-3 / 16) * rel5_sh_m_01m1 +
    (-13 / 48) * rel5_sh_m_0m01 + (-1 / 16) * rel5_sh_m_0m11 + (5 / 48) * rel5_sh_m_m001 +
    (7 / 384) * rel5_st_m_m001 + (-1 / 96) * rel5_st_m_m00m + (-9 / 16) * rel5_sh_m_m011 +
    (-7 / 32) * rel5_sh_m_m101 + (-215 / 768) * rel5_st_01_01m + (-265 / 256) * rel5_st_01_m0m +
    (5 / 64) * rel5_st_0m_0m1 + (-13 / 24) * rel5_st_0m_0mm + (-27 / 64) * rel5_st_0m_m01 +
    (67 / 192) * rel5_sh_m_0001 + (5 / 6) * rel5_sh_m_0011 + (-5 / 96) * rel5_st_m_0011 +
    (-13 / 12) * rel5_st_m_00mm + (19 / 24) * rel5_sh_m_0101 + (7 / 16) * rel5_st_m_010m +
    (-1 / 48) * rel5_st_m_01m1 + (-41 / 48) * rel5_st_m_0m0m + (-1 / 16) * rel5_st_m_0m1m +
    (-7 / 48) * rel5_st_m_m01m + (-1 / 384) * rel5_st_m_m0m1 + (-7 / 192) * rel5_st_m_m101 +
    (1 / 48) * rel5_st_m_m10m + (-1 / 4) * rel5_st_m_m1m1 + (11 / 96) * rel5_sh_01_00m +
    (-1 / 8) * rel5_sh_01_01m + (1 / 8) * rel5_sh_01_0m1 + (-61 / 32) * rel5_st_01_0mm +
    (-1 / 2) * rel5_sh_01_m11 + (1 / 96) * rel5_sh_0m_001 + (1 / 4) * rel5_sh_0m_01m +
    (1 / 2) * rel5_sh_m1_011 + (1 / 32) * rel5_sh_m1_0m1 + (9 / 32) * rel5_sh_m1_m01 +
    (-33 / 2) * rel5_mob_00mmm + (-3 / 32) * rel5_mob_01mmm + (-6) * rel5_mob_0m0mm +
    (-33 / 32) * rel5_mob_0m1mm + (9 / 32) * rel5_mob_m10mm + (5 / 24) * rel5_st_m_011m +
    (-1 / 4) * rel5_st_m_01mm + (-7 / 32) * rel5_st_m_0m11 + (-9 / 32) * rel5_st_m_0mm1 +
    (9 / 32) * rel5_st_m_m011 + (-1 / 4) * rel5_st_m_m0mm + (1 / 12) * rel5_st_m_m11m +
    (-5 / 24) * rel5_st_m_mm0m + (1 / 12) * rel5_st_m_mm1m

theorem hpl_negOne_negOne_zero_negOne_negOne_at_one :
    hpl [negOne, negOne, zero, negOne, negOne] 1 =
      -3 * Li 4 (1 / 2) * log 2 - 6 * Li 5 (1 / 2) - 3 / 40 * log 2 ^ 5
      + 1 / 24 * log 2 ^ 3 * π ^ 2 + 1 / 16 * log 2 ^ 2 * zeta3 - 1 / 30 * log 2 * π ^ 4
      + 6 * zeta5 := by
  linear_combination (-97 / 64) * hpl_zero_zero_zero_zero_one_at_one +
    (63 / 8) * hpl_zero_zero_zero_one_one_at_one + (335 / 64) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 64) * hpl_zero_one_zero_zero_one_at_one + (-3) * hpl_zero_zero_one_one_one_at_one +
    (-9 / 4) * hpl_zero_one_zero_one_one_at_one + (-3 / 4) * hpl_zero_one_one_zero_one_at_one +
    (37 / 5) * hpl_zero_zero_zero_zero_negOne_at_one + (-6) * hpl_negOne_one_one_one_one_at_one +
    (2021 / 320) * rel5_sh_m_mmmm + (-241 / 128) * rel5_sh_m_0mmm + (241 / 384) * rel5_sh_m_m0mm +
    (-2) * rel5_sh_m_m1mm + (23 / 96) * rel5_sh_m_mm0m + (447 / 128) * rel5_sh_m_mm1m +
    (963 / 128) * rel5_sh_m_mmm1 + (-387 / 2560) * rel5_st_m_0001 + (-889 / 384) * rel5_st_m_000m +
    (-13 / 4) * rel5_sh_m_00mm + (-47 / 64) * rel5_sh_m_01mm + (35 / 16) * rel5_sh_m_0m0m +
    (1 / 64) * rel5_sh_m_0m1m + (1) * rel5_sh_m_0mm1 + (-47 / 128) * rel5_sh_m_m01m +
    (13 / 32) * rel5_sh_m_m0m1 + (-95 / 128) * rel5_sh_m_m10m + (-3) * rel5_sh_m_m11m +
    (-75 / 16) * rel5_sh_m_m1m1 + (47 / 64) * rel5_sh_m_mm01 + (-1437 / 2560) * rel5_st_01_00m +
    (-11 / 16) * rel5_st_0m_001 + (39 / 64) * rel5_sh_0m_00m + (1471 / 384) * rel5_st_0m_00m +
    (-19 / 8) * rel5_sh_0m_0mm + (1) * rel5_sh_m1_m11 + (3) * rel5_sh_m1_mm1 +
    (-241 / 32) * rel5_mob_0mmm1 + (-27 / 16) * rel5_sh_m_000m + (71 / 32) * rel5_sh_m_001m +
    (-325 / 192) * rel5_st_m_001m + (85 / 32) * rel5_sh_m_00m1 + (-847 / 480) * rel5_st_m_00m1 +
    (43 / 64) * rel5_sh_m_010m + (11 / 32) * rel5_sh_m_01m1 + (1 / 8) * rel5_sh_m_0m01 +
    (-17 / 32) * rel5_sh_m_0m11 + (-23 / 32) * rel5_sh_m_m001 + (259 / 3840) * rel5_st_m_m001 +
    (37 / 192) * rel5_st_m_m00m + (31 / 32) * rel5_sh_m_m011 + (5 / 64) * rel5_sh_m_m101 +
    (-6) * rel5_sh_m_m111 + (7109 / 7680) * rel5_st_01_01m + (8161 / 7680) * rel5_st_01_m0m +
    (-35 / 32) * rel5_st_0m_0m1 + (13 / 4) * rel5_st_0m_0mm + (13 / 32) * rel5_st_0m_m01 +
    (-321 / 128) * rel5_sh_m_0001 + (-9 / 4) * rel5_sh_m_0011 + (113 / 64) * rel5_st_m_0011 +
    (37 / 8) * rel5_st_m_00mm + (-69 / 32) * rel5_sh_m_0101 + (-13 / 6) * rel5_st_m_010m +
    (-1 / 480) * rel5_st_m_01m1 + (85 / 24) * rel5_st_m_0m0m + (-37 / 96) * rel5_st_m_0m1m +
    (5 / 96) * rel5_st_m_m01m + (-757 / 3840) * rel5_st_m_m0m1 + (-259 / 1920) * rel5_st_m_m101 +
    (-37 / 96) * rel5_st_m_m10m + (27 / 80) * rel5_st_m_m1m1 + (-19 / 64) * rel5_sh_01_00m +
    (1 / 4) * rel5_sh_01_01m + (-5 / 8) * rel5_sh_01_0m1 + (-3 / 8) * rel5_st_01_0m1 +
    (95 / 64) * rel5_st_01_0mm + (3) * rel5_sh_01_m11 + (-5 / 64) * rel5_sh_0m_001 +
    (-43 / 64) * rel5_sh_0m_01m + (-2) * rel5_sh_m1_011 + (-31 / 64) * rel5_sh_m1_0m1 +
    (-31 / 64) * rel5_sh_m1_m01 + (24) * rel5_mob_00mmm + (141 / 64) * rel5_mob_01mmm +
    (15 / 2) * rel5_mob_0m0mm + (47 / 64) * rel5_mob_0m1mm + (-95 / 64) * rel5_mob_m10mm +
    (-11 / 16) * rel5_st_m_011m + (1 / 8) * rel5_st_m_01mm + (1 / 64) * rel5_st_m_0m11 +
    (-33 / 64) * rel5_st_m_0mm1 + (-95 / 64) * rel5_st_m_m011 + (19 / 8) * rel5_st_m_m0mm +
    (-1 / 8) * rel5_st_m_m11m + (-3 / 4) * rel5_st_m_m1mm + (23 / 16) * rel5_st_m_mm0m +
    (-5 / 8) * rel5_st_m_mm1m + (3) * rel5_st_m_0mmm + (-6) * rel5_mob_0000m

theorem hpl_negOne_negOne_one_zero_one_at_one :
    hpl [negOne, negOne, one, zero, one] 1 =
      -4 * Li 4 (1 / 2) * log 2 - 4 * Li 5 (1 / 2) - 2 / 15 * log 2 ^ 5
      + 1 / 12 * log 2 ^ 3 * π ^ 2 - 23 / 16 * log 2 ^ 2 * zeta3 - 1 / 480 * log 2 * π ^ 4
      + 23 / 96 * zeta3 * π ^ 2 + 85 / 64 * zeta5 := by
  linear_combination (-1211 / 576) * hpl_zero_zero_zero_zero_one_at_one +
    (43 / 6) * hpl_zero_zero_zero_one_one_at_one +
    (2941 / 576) * hpl_zero_zero_one_zero_one_at_one +
    (1133 / 576) * hpl_zero_one_zero_zero_one_at_one +
    (-3 / 2) * hpl_zero_zero_one_one_one_at_one + (-5 / 4) * hpl_zero_one_zero_one_one_at_one +
    (-5 / 12) * hpl_zero_one_one_zero_one_at_one +
    (27 / 4) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (341 / 320) * rel5_sh_m_mmmm + (71 / 128) * rel5_sh_m_0mmm + (-71 / 384) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (91 / 96) * rel5_sh_m_mm0m + (973 / 384) * rel5_sh_m_mm1m +
    (83 / 128) * rel5_sh_m_mmm1 + (-355 / 512) * rel5_st_m_0001 + (-1273 / 1152) * rel5_st_m_000m +
    (-121 / 36) * rel5_sh_m_00mm + (-119 / 64) * rel5_sh_m_01mm + (173 / 144) * rel5_sh_m_0m0m +
    (-157 / 192) * rel5_sh_m_0m1m + (1 / 2) * rel5_sh_m_0mm1 + (-119 / 128) * rel5_sh_m_m01m +
    (25 / 96) * rel5_sh_m_m0m1 + (-175 / 128) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-17 / 6) * rel5_sh_m_m1m1 + (119 / 64) * rel5_sh_m_mm01 + (-2387 / 1536) * rel5_st_01_00m +
    (-193 / 384) * rel5_st_0m_001 + (179 / 288) * rel5_sh_0m_00m + (3695 / 1152) * rel5_st_0m_00m +
    (-13 / 36) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (11 / 8) * rel5_sh_m1_mm1 +
    (71 / 32) * rel5_mob_0mmm1 + (-1645 / 576) * rel5_sh_m_000m + (383 / 144) * rel5_sh_m_001m +
    (-905 / 576) * rel5_st_m_001m + (767 / 288) * rel5_sh_m_00m1 + (-119 / 72) * rel5_st_m_00m1 +
    (95 / 96) * rel5_sh_m_010m + (21 / 32) * rel5_sh_m_01m1 + (85 / 144) * rel5_sh_m_0m01 +
    (149 / 96) * rel5_sh_m_0m11 + (-181 / 288) * rel5_sh_m_m001 + (461 / 2304) * rel5_st_m_m001 +
    (41 / 576) * rel5_st_m_m00m + (317 / 96) * rel5_sh_m_m011 + (331 / 192) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (905 / 1536) * rel5_st_01_01m + (5023 / 4608) * rel5_st_01_m0m +
    (-337 / 384) * rel5_st_0m_0m1 + (193 / 72) * rel5_st_0m_0mm + (335 / 384) * rel5_st_0m_m01 +
    (-1355 / 1152) * rel5_sh_m_0001 + (-97 / 36) * rel5_sh_m_0011 + (361 / 576) * rel5_st_m_0011 +
    (323 / 72) * rel5_st_m_00mm + (-769 / 288) * rel5_sh_m_0101 + (-91 / 48) * rel5_st_m_010m +
    (-47 / 288) * rel5_st_m_01m1 + (509 / 144) * rel5_st_m_0m0m + (-1 / 32) * rel5_st_m_0m1m +
    (113 / 288) * rel5_st_m_m01m + (1333 / 2304) * rel5_st_m_m0m1 +
    (-461 / 1152) * rel5_st_m_m101 + (-41 / 288) * rel5_st_m_m10m + (1 / 6) * rel5_st_m_m1m1 +
    (671 / 576) * rel5_sh_01_00m + (3 / 8) * rel5_sh_01_01m + (-7 / 12) * rel5_sh_01_0m1 +
    (-1 / 4) * rel5_st_01_0m1 + (167 / 64) * rel5_st_01_0mm + (31 / 12) * rel5_sh_01_m11 +
    (-911 / 576) * rel5_sh_0m_001 + (-89 / 96) * rel5_sh_0m_01m + (-25 / 12) * rel5_sh_m1_011 +
    (-221 / 192) * rel5_sh_m1_0m1 + (-317 / 192) * rel5_sh_m1_m01 + (49 / 4) * rel5_mob_00mmm +
    (357 / 64) * rel5_mob_01mmm + (11 / 3) * rel5_mob_0m0mm + (293 / 192) * rel5_mob_0m1mm +
    (-175 / 64) * rel5_mob_m10mm + (-121 / 144) * rel5_st_m_011m + (13 / 24) * rel5_st_m_01mm +
    (-63 / 64) * rel5_st_m_0m11 + (109 / 192) * rel5_st_m_0mm1 + (-175 / 64) * rel5_st_m_m011 +
    (43 / 24) * rel5_st_m_m0mm + (-5 / 72) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm +
    (181 / 144) * rel5_st_m_mm0m + (-29 / 72) * rel5_st_m_mm1m + (3 / 2) * rel5_st_m_0mmm +
    (-4) * rel5_mob_0000m

theorem hpl_negOne_negOne_one_zero_negOne_at_one :
    hpl [negOne, negOne, one, zero, negOne] 1 =
      -4 * Li 4 (1 / 2) * log 2 - 7 * Li 5 (1 / 2) - 13 / 120 * log 2 ^ 5
      + 1 / 18 * log 2 ^ 3 * π ^ 2 - 5 / 16 * log 2 ^ 2 * zeta3 - 1 / 30 * log 2 * π ^ 4
      + 1 / 96 * zeta3 * π ^ 2 + 221 / 32 * zeta5 := by
  linear_combination (-967 / 384) * hpl_zero_zero_zero_zero_one_at_one +
    (147 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (2345 / 384) * hpl_zero_zero_one_zero_one_at_one +
    (1057 / 384) * hpl_zero_one_zero_zero_one_at_one +
    (-7 / 2) * hpl_zero_zero_one_one_one_at_one + (-21 / 8) * hpl_zero_one_zero_one_one_at_one +
    (-7 / 8) * hpl_zero_one_one_zero_one_at_one +
    (28 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (-7) * hpl_negOne_one_one_one_one_at_one +
    (10643 / 1920) * rel5_sh_m_mmmm + (-679 / 768) * rel5_sh_m_0mmm +
    (679 / 2304) * rel5_sh_m_m0mm + (-7 / 3) * rel5_sh_m_m1mm + (113 / 576) * rel5_sh_m_mm0m +
    (995 / 256) * rel5_sh_m_mm1m + (1623 / 256) * rel5_sh_m_mmm1 + (-587 / 1024) * rel5_st_m_0001 +
    (-5071 / 2304) * rel5_st_m_000m + (-91 / 24) * rel5_sh_m_00mm + (-377 / 384) * rel5_sh_m_01mm +
    (221 / 96) * rel5_sh_m_0m0m + (-41 / 384) * rel5_sh_m_0m1m + (7 / 6) * rel5_sh_m_0mm1 +
    (-377 / 768) * rel5_sh_m_m01m + (91 / 192) * rel5_sh_m_m0m1 + (-521 / 768) * rel5_sh_m_m10m +
    (-7 / 2) * rel5_sh_m_m11m + (-167 / 32) * rel5_sh_m_m1m1 + (377 / 384) * rel5_sh_m_mm01 +
    (-885 / 1024) * rel5_st_01_00m + (-43 / 48) * rel5_st_0m_001 + (99 / 128) * rel5_sh_0m_00m +
    (10873 / 2304) * rel5_st_0m_00m + (-109 / 48) * rel5_sh_0m_0mm + (7 / 6) * rel5_sh_m1_m11 +
    (3) * rel5_sh_m1_mm1 + (-679 / 192) * rel5_mob_0mmm1 + (-73 / 32) * rel5_sh_m_000m +
    (521 / 192) * rel5_sh_m_001m + (-2275 / 1152) * rel5_st_m_001m + (595 / 192) * rel5_sh_m_00m1 +
    (-1181 / 576) * rel5_st_m_00m1 + (325 / 384) * rel5_sh_m_010m + (77 / 192) * rel5_sh_m_01m1 +
    (7 / 48) * rel5_sh_m_0m01 + (-71 / 192) * rel5_sh_m_0m11 + (-161 / 192) * rel5_sh_m_m001 +
    (257 / 4608) * rel5_st_m_m001 + (259 / 1152) * rel5_st_m_m00m + (265 / 192) * rel5_sh_m_m011 +
    (83 / 384) * rel5_sh_m_m101 + (-7) * rel5_sh_m_m111 + (9367 / 9216) * rel5_st_01_01m +
    (10571 / 9216) * rel5_st_01_m0m + (-239 / 192) * rel5_st_0m_0m1 + (91 / 24) * rel5_st_0m_0mm +
    (97 / 192) * rel5_st_0m_m01 + (-621 / 256) * rel5_sh_m_0001 + (-21 / 8) * rel5_sh_m_0011 +
    (743 / 384) * rel5_st_m_0011 + (259 / 48) * rel5_st_m_00mm + (-161 / 64) * rel5_sh_m_0101 +
    (-91 / 36) * rel5_st_m_010m + (-11 / 576) * rel5_st_m_01m1 + (595 / 144) * rel5_st_m_0m0m +
    (-259 / 576) * rel5_st_m_0m1m + (35 / 576) * rel5_st_m_m01m + (-551 / 4608) * rel5_st_m_m0m1 +
    (-257 / 2304) * rel5_st_m_m101 + (-259 / 576) * rel5_st_m_m10m + (11 / 32) * rel5_st_m_m1m1 +
    (-37 / 384) * rel5_sh_01_00m + (7 / 24) * rel5_sh_01_01m + (-35 / 48) * rel5_sh_01_0m1 +
    (-7 / 16) * rel5_st_01_0m1 + (713 / 384) * rel5_st_01_0mm + (7 / 2) * rel5_sh_01_m11 +
    (-131 / 384) * rel5_sh_0m_001 + (-325 / 384) * rel5_sh_0m_01m + (-7 / 3) * rel5_sh_m1_011 +
    (-265 / 384) * rel5_sh_m1_0m1 + (-265 / 384) * rel5_sh_m1_m01 + (25) * rel5_mob_00mmm +
    (377 / 128) * rel5_mob_01mmm + (31 / 4) * rel5_mob_0m0mm + (377 / 384) * rel5_mob_0m1mm +
    (-905 / 384) * rel5_mob_m10mm + (-77 / 96) * rel5_st_m_011m + (7 / 48) * rel5_st_m_01mm +
    (-41 / 384) * rel5_st_m_0m11 + (-61 / 128) * rel5_st_m_0mm1 + (-713 / 384) * rel5_st_m_m011 +
    (133 / 48) * rel5_st_m_m0mm + (-7 / 48) * rel5_st_m_m11m + (-7 / 8) * rel5_st_m_m1mm +
    (161 / 96) * rel5_st_m_mm0m + (-35 / 48) * rel5_st_m_mm1m + (7 / 2) * rel5_st_m_0mmm +
    (-7) * rel5_mob_0000m

theorem hpl_negOne_negOne_one_one_one_at_one :
    hpl [negOne, negOne, one, one, one] 1 =
      Li 4 (1 / 2) * log 2 + Li 5 (1 / 2) + 1 / 40 * log 2 ^ 5 - 1 / 36 * log 2 ^ 3 * π ^ 2
      + 1 / 2 * log 2 ^ 2 * zeta3 - 1 / 720 * log 2 * π ^ 4 - 1 / 12 * zeta3 * π ^ 2
      + 1 / 32 * zeta5 := by
  linear_combination (-5 / 144) * hpl_zero_zero_zero_zero_one_at_one +
    (-13 / 12) * hpl_zero_zero_zero_one_one_at_one +
    (-119 / 144) * hpl_zero_zero_one_zero_one_at_one +
    (-43 / 144) * hpl_zero_one_zero_zero_one_at_one +
    (-31 / 30) * hpl_zero_zero_zero_zero_negOne_at_one + (1) * hpl_negOne_one_one_one_one_at_one +
    (-61 / 80) * rel5_sh_m_mmmm + (1 / 32) * rel5_sh_m_0mmm + (-1 / 96) * rel5_sh_m_m0mm +
    (1 / 3) * rel5_sh_m_m1mm + (-1 / 8) * rel5_sh_m_mm0m + (-23 / 32) * rel5_sh_m_mm1m +
    (-27 / 32) * rel5_sh_m_mmm1 + (-203 / 1920) * rel5_st_m_0001 + (113 / 288) * rel5_st_m_000m +
    (5 / 9) * rel5_sh_m_00mm + (13 / 48) * rel5_sh_m_01mm + (-29 / 72) * rel5_sh_m_0m0m +
    (5 / 48) * rel5_sh_m_0m1m + (13 / 96) * rel5_sh_m_m01m + (-1 / 24) * rel5_sh_m_m0m1 +
    (7 / 32) * rel5_sh_m_m10m + (1 / 2) * rel5_sh_m_m11m + (2 / 3) * rel5_sh_m_m1m1 +
    (-13 / 48) * rel5_sh_m_mm01 + (367 / 1920) * rel5_st_01_00m + (-5 / 96) * rel5_st_0m_001 +
    (-1 / 18) * rel5_sh_0m_00m + (-103 / 288) * rel5_st_0m_00m + (7 / 18) * rel5_sh_0m_0mm +
    (-1 / 2) * rel5_sh_m1_mm1 + (1 / 8) * rel5_mob_0mmm1 + (53 / 144) * rel5_sh_m_000m +
    (-13 / 36) * rel5_sh_m_001m + (37 / 144) * rel5_st_m_001m + (-31 / 72) * rel5_sh_m_00m1 +
    (23 / 90) * rel5_st_m_00m1 + (-1 / 12) * rel5_sh_m_010m + (-1 / 8) * rel5_sh_m_01m1 +
    (-13 / 72) * rel5_sh_m_0m01 + (-5 / 24) * rel5_sh_m_0m11 + (5 / 72) * rel5_sh_m_m001 +
    (-89 / 2880) * rel5_st_m_m001 + (-1 / 144) * rel5_st_m_m00m + (-13 / 24) * rel5_sh_m_m011 +
    (-11 / 48) * rel5_sh_m_m101 + (1) * rel5_sh_m_m111 + (-253 / 1920) * rel5_st_01_01m +
    (-1531 / 5760) * rel5_st_01_m0m + (5 / 32) * rel5_st_0m_0m1 + (-13 / 36) * rel5_st_0m_0mm +
    (-17 / 96) * rel5_st_0m_m01 + (115 / 288) * rel5_sh_m_0001 + (5 / 9) * rel5_sh_m_0011 +
    (-17 / 144) * rel5_st_m_0011 + (-13 / 18) * rel5_st_m_00mm + (19 / 36) * rel5_sh_m_0101 +
    (7 / 24) * rel5_st_m_010m + (11 / 360) * rel5_st_m_01m1 + (-41 / 72) * rel5_st_m_0m0m +
    (-1 / 24) * rel5_st_m_0m1m + (-7 / 72) * rel5_st_m_m01m + (-193 / 2880) * rel5_st_m_m0m1 +
    (89 / 1440) * rel5_st_m_m101 + (1 / 72) * rel5_st_m_m10m + (-1 / 30) * rel5_st_m_m1m1 +
    (-13 / 144) * rel5_sh_01_00m + (-1 / 12) * rel5_sh_01_01m + (1 / 12) * rel5_sh_01_0m1 +
    (-25 / 48) * rel5_st_01_0mm + (-1 / 3) * rel5_sh_01_m11 + (25 / 144) * rel5_sh_0m_001 +
    (1 / 8) * rel5_sh_0m_01m + (1 / 3) * rel5_sh_m1_011 + (5 / 48) * rel5_sh_m1_0m1 +
    (13 / 48) * rel5_sh_m1_m01 + (-4) * rel5_mob_00mmm + (-13 / 16) * rel5_mob_01mmm +
    (-4 / 3) * rel5_mob_0m0mm + (-13 / 48) * rel5_mob_0m1mm + (7 / 16) * rel5_mob_m10mm +
    (5 / 36) * rel5_st_m_011m + (-1 / 6) * rel5_st_m_01mm + (5 / 48) * rel5_st_m_0m11 +
    (-5 / 48) * rel5_st_m_0mm1 + (7 / 16) * rel5_st_m_m011 + (-1 / 6) * rel5_st_m_m0mm +
    (1 / 18) * rel5_st_m_m11m + (-5 / 36) * rel5_st_m_mm0m + (1 / 18) * rel5_st_m_mm1m +
    (1) * rel5_mob_0000m

theorem hpl_negOne_negOne_one_one_negOne_at_one :
    hpl [negOne, negOne, one, one, negOne] 1 =
      1 / 120 * log 2 ^ 5 - 1 / 16 * log 2 ^ 2 * zeta3 + 1 / 720 * log 2 * π ^ 4
      - 3 / 64 * zeta5 := by
  linear_combination (-1 / 20) * hpl_zero_zero_zero_zero_negOne_at_one +
    (1 / 40) * rel5_st_m_0001 + (1 / 4) * rel5_sh_m_m1m1 + (1) * rel5_sh_m_mm11 +
    (1 / 40) * rel5_st_01_00m + (-1 / 2) * rel5_sh_m1_mm1 + (1 / 120) * rel5_st_m_00m1 +
    (1 / 120) * rel5_st_m_m001 + (-1 / 60) * rel5_st_01_01m + (1 / 60) * rel5_st_01_m0m +
    (-1 / 60) * rel5_st_m_01m1 + (1 / 60) * rel5_st_m_m0m1 + (-1 / 60) * rel5_st_m_m101 +
    (-1 / 20) * rel5_st_m_m1m1

theorem hpl_negOne_negOne_one_negOne_one_at_one :
    hpl [negOne, negOne, one, negOne, one] 1 =
      3 * Li 5 (1 / 2) - 1 / 60 * log 2 ^ 5 + 1 / 24 * log 2 ^ 3 * π ^ 2
      - 11 / 8 * log 2 ^ 2 * zeta3 + 1 / 30 * log 2 * π ^ 4 + 1 / 4 * zeta3 * π ^ 2
      - 375 / 64 * zeta5 := by
  linear_combination (331 / 384) * hpl_zero_zero_zero_zero_one_at_one +
    (-11 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (-53 / 384) * hpl_zero_zero_one_zero_one_at_one +
    (-109 / 384) * hpl_zero_one_zero_zero_one_at_one + (3 / 2) * hpl_zero_zero_one_one_one_at_one +
    (9 / 8) * hpl_zero_one_zero_one_one_at_one + (3 / 8) * hpl_zero_one_one_zero_one_at_one +
    (-71 / 20) * hpl_zero_zero_zero_zero_negOne_at_one + (3) * hpl_negOne_one_one_one_one_at_one +
    (211 / 640) * rel5_sh_m_mmmm + (25 / 256) * rel5_sh_m_0mmm + (-25 / 768) * rel5_sh_m_m0mm +
    (1) * rel5_sh_m_m1mm + (49 / 192) * rel5_sh_m_mm0m + (233 / 256) * rel5_sh_m_mm1m +
    (69 / 256) * rel5_sh_m_mmm1 + (1883 / 5120) * rel5_st_m_0001 + (-5 / 256) * rel5_st_m_000m +
    (-1 / 24) * rel5_sh_m_00mm + (-57 / 128) * rel5_sh_m_01mm + (11 / 96) * rel5_sh_m_0m0m +
    (-41 / 128) * rel5_sh_m_0m1m + (-1 / 2) * rel5_sh_m_0mm1 + (-57 / 256) * rel5_sh_m_m01m +
    (-5 / 64) * rel5_sh_m_m0m1 + (-73 / 256) * rel5_sh_m_m10m + (3 / 2) * rel5_sh_m_m11m +
    (51 / 32) * rel5_sh_m_m1m1 + (57 / 128) * rel5_sh_m_mm01 + (-1627 / 5120) * rel5_st_01_00m +
    (1 / 2) * rel5_st_0m_001 + (-53 / 384) * rel5_sh_0m_00m + (-647 / 768) * rel5_st_0m_00m +
    (1 / 48) * rel5_sh_0m_0mm + (-1 / 2) * rel5_sh_m1_m11 + (1 / 2) * rel5_sh_m1_mm1 +
    (25 / 64) * rel5_mob_0mmm1 + (-25 / 96) * rel5_sh_m_000m + (-5 / 192) * rel5_sh_m_001m +
    (29 / 384) * rel5_st_m_001m + (-7 / 192) * rel5_sh_m_00m1 + (103 / 960) * rel5_st_m_00m1 +
    (-11 / 128) * rel5_sh_m_010m + (13 / 64) * rel5_sh_m_01m1 + (23 / 48) * rel5_sh_m_0m01 +
    (57 / 64) * rel5_sh_m_0m11 + (29 / 192) * rel5_sh_m_m001 + (389 / 7680) * rel5_st_m_m001 +
    (-29 / 384) * rel5_st_m_m00m + (73 / 64) * rel5_sh_m_m011 + (83 / 128) * rel5_sh_m_m101 +
    (3) * rel5_sh_m_m111 + (-781 / 15360) * rel5_st_01_01m + (1277 / 5120) * rel5_st_01_m0m +
    (5 / 64) * rel5_st_0m_0m1 + (-13 / 24) * rel5_st_0m_0mm + (21 / 64) * rel5_st_0m_m01 +
    (43 / 768) * rel5_sh_m_0001 + (-13 / 24) * rel5_sh_m_0011 + (-203 / 384) * rel5_st_m_0011 +
    (-7 / 48) * rel5_st_m_00mm + (-97 / 192) * rel5_sh_m_0101 + (5 / 24) * rel5_st_m_010m +
    (-71 / 960) * rel5_st_m_01m1 + (-1 / 16) * rel5_st_m_0m0m + (61 / 192) * rel5_st_m_0m1m +
    (17 / 64) * rel5_st_m_m01m + (2173 / 7680) * rel5_st_m_m0m1 + (-389 / 3840) * rel5_st_m_m101 +
    (29 / 192) * rel5_st_m_m10m + (-3 / 160) * rel5_st_m_m1m1 + (161 / 384) * rel5_sh_01_00m +
    (1 / 8) * rel5_sh_01_01m + (1 / 16) * rel5_sh_01_0m1 + (3 / 16) * rel5_st_01_0m1 +
    (105 / 128) * rel5_st_01_0mm + (-1 / 2) * rel5_sh_01_m11 + (-185 / 384) * rel5_sh_0m_001 +
    (-5 / 128) * rel5_sh_0m_01m + (-9 / 128) * rel5_sh_m1_0m1 + (-73 / 128) * rel5_sh_m1_m01 +
    (171 / 128) * rel5_mob_01mmm + (1 / 4) * rel5_mob_0m0mm + (57 / 128) * rel5_mob_0m1mm +
    (-73 / 128) * rel5_mob_m10mm + (-7 / 96) * rel5_st_m_011m + (7 / 16) * rel5_st_m_01mm +
    (-41 / 128) * rel5_st_m_0m11 + (73 / 128) * rel5_st_m_0mm1 + (-73 / 128) * rel5_st_m_m011 +
    (-11 / 16) * rel5_st_m_m0mm + (-5 / 48) * rel5_st_m_m11m + (3 / 8) * rel5_st_m_m1mm +
    (-29 / 96) * rel5_st_m_mm0m + (7 / 48) * rel5_st_m_mm1m + (-3 / 2) * rel5_st_m_0mmm +
    (3) * rel5_mob_0000m

theorem hpl_negOne_negOne_one_negOne_negOne_at_one :
    hpl [negOne, negOne, one, negOne, negOne] 1 =
      -3 * Li 4 (1 / 2) * log 2 - 6 * Li 5 (1 / 2) - 1 / 12 * log 2 ^ 5
      + 1 / 24 * log 2 ^ 3 * π ^ 2 + 1 / 16 * log 2 ^ 2 * zeta3 - 1 / 30 * log 2 * π ^ 4
      + 6 * zeta5 := by
  linear_combination (-97 / 64) * hpl_zero_zero_zero_zero_one_at_one +
    (63 / 8) * hpl_zero_zero_zero_one_one_at_one + (335 / 64) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 64) * hpl_zero_one_zero_zero_one_at_one + (-3) * hpl_zero_zero_one_one_one_at_one +
    (-9 / 4) * hpl_zero_one_zero_one_one_at_one + (-3 / 4) * hpl_zero_one_one_zero_one_at_one +
    (37 / 5) * hpl_zero_zero_zero_zero_negOne_at_one + (-6) * hpl_negOne_one_one_one_one_at_one +
    (1637 / 320) * rel5_sh_m_mmmm + (-49 / 128) * rel5_sh_m_0mmm + (49 / 384) * rel5_sh_m_m0mm +
    (-2) * rel5_sh_m_m1mm + (23 / 96) * rel5_sh_m_mm0m + (511 / 128) * rel5_sh_m_mm1m +
    (771 / 128) * rel5_sh_m_mmm1 + (-387 / 2560) * rel5_st_m_0001 + (-889 / 384) * rel5_st_m_000m +
    (-13 / 4) * rel5_sh_m_00mm + (-47 / 64) * rel5_sh_m_01mm + (35 / 16) * rel5_sh_m_0m0m +
    (1 / 64) * rel5_sh_m_0m1m + (1) * rel5_sh_m_0mm1 + (-47 / 128) * rel5_sh_m_m01m +
    (13 / 32) * rel5_sh_m_m0m1 + (-95 / 128) * rel5_sh_m_m10m + (-3) * rel5_sh_m_m11m +
    (-75 / 16) * rel5_sh_m_m1m1 + (47 / 64) * rel5_sh_m_mm01 + (-1437 / 2560) * rel5_st_01_00m +
    (-11 / 16) * rel5_st_0m_001 + (39 / 64) * rel5_sh_0m_00m + (1471 / 384) * rel5_st_0m_00m +
    (-19 / 8) * rel5_sh_0m_0mm + (1) * rel5_sh_m1_m11 + (3) * rel5_sh_m1_mm1 +
    (-49 / 32) * rel5_mob_0mmm1 + (-27 / 16) * rel5_sh_m_000m + (71 / 32) * rel5_sh_m_001m +
    (-325 / 192) * rel5_st_m_001m + (85 / 32) * rel5_sh_m_00m1 + (-847 / 480) * rel5_st_m_00m1 +
    (43 / 64) * rel5_sh_m_010m + (11 / 32) * rel5_sh_m_01m1 + (1 / 8) * rel5_sh_m_0m01 +
    (-17 / 32) * rel5_sh_m_0m11 + (-23 / 32) * rel5_sh_m_m001 + (259 / 3840) * rel5_st_m_m001 +
    (37 / 192) * rel5_st_m_m00m + (31 / 32) * rel5_sh_m_m011 + (5 / 64) * rel5_sh_m_m101 +
    (-6) * rel5_sh_m_m111 + (7109 / 7680) * rel5_st_01_01m + (8161 / 7680) * rel5_st_01_m0m +
    (-35 / 32) * rel5_st_0m_0m1 + (13 / 4) * rel5_st_0m_0mm + (13 / 32) * rel5_st_0m_m01 +
    (-321 / 128) * rel5_sh_m_0001 + (-9 / 4) * rel5_sh_m_0011 + (113 / 64) * rel5_st_m_0011 +
    (37 / 8) * rel5_st_m_00mm + (-69 / 32) * rel5_sh_m_0101 + (-13 / 6) * rel5_st_m_010m +
    (-1 / 480) * rel5_st_m_01m1 + (85 / 24) * rel5_st_m_0m0m + (-37 / 96) * rel5_st_m_0m1m +
    (5 / 96) * rel5_st_m_m01m + (-757 / 3840) * rel5_st_m_m0m1 + (-259 / 1920) * rel5_st_m_m101 +
    (-37 / 96) * rel5_st_m_m10m + (27 / 80) * rel5_st_m_m1m1 + (-19 / 64) * rel5_sh_01_00m +
    (1 / 4) * rel5_sh_01_01m + (-5 / 8) * rel5_sh_01_0m1 + (-3 / 8) * rel5_st_01_0m1 +
    (95 / 64) * rel5_st_01_0mm + (3) * rel5_sh_01_m11 + (-5 / 64) * rel5_sh_0m_001 +
    (-43 / 64) * rel5_sh_0m_01m + (-2) * rel5_sh_m1_011 + (-31 / 64) * rel5_sh_m1_0m1 +
    (-31 / 64) * rel5_sh_m1_m01 + (24) * rel5_mob_00mmm + (141 / 64) * rel5_mob_01mmm +
    (15 / 2) * rel5_mob_0m0mm + (47 / 64) * rel5_mob_0m1mm + (-95 / 64) * rel5_mob_m10mm +
    (-11 / 16) * rel5_st_m_011m + (1 / 8) * rel5_st_m_01mm + (1 / 64) * rel5_st_m_0m11 +
    (-33 / 64) * rel5_st_m_0mm1 + (-95 / 64) * rel5_st_m_m011 + (19 / 8) * rel5_st_m_m0mm +
    (-1 / 8) * rel5_st_m_m11m + (-3 / 4) * rel5_st_m_m1mm + (23 / 16) * rel5_st_m_mm0m +
    (-5 / 8) * rel5_st_m_mm1m + (3) * rel5_st_m_0mmm + (-6) * rel5_mob_0000m

theorem hpl_negOne_negOne_negOne_zero_one_at_one :
    hpl [negOne, negOne, negOne, zero, one] 1 =
      -Li 4 (1 / 2) * log 2 - Li 5 (1 / 2) - 1 / 30 * log 2 ^ 5
      + 1 / 18 * log 2 ^ 3 * π ^ 2 - 3 / 4 * log 2 ^ 2 * zeta3 + 1 / 480 * log 2 * π ^ 4
      + 7 / 96 * zeta3 * π ^ 2 + 1 / 8 * zeta5 := by
  linear_combination (-271 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (89 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (1481 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (625 / 1152) * hpl_zero_one_zero_zero_one_at_one +
    (-1 / 2) * hpl_zero_zero_one_one_one_at_one + (-3 / 8) * hpl_zero_one_zero_one_one_at_one +
    (-1 / 8) * hpl_zero_one_one_zero_one_at_one + (5 / 6) * hpl_zero_zero_zero_zero_negOne_at_one +
    (-1) * hpl_negOne_one_one_one_one_at_one + (6689 / 1920) * rel5_sh_m_mmmm +
    (-733 / 768) * rel5_sh_m_0mmm + (733 / 2304) * rel5_sh_m_m0mm + (-1 / 3) * rel5_sh_m_m1mm +
    (-133 / 576) * rel5_sh_m_mm0m + (1331 / 768) * rel5_sh_m_mm1m + (1101 / 256) * rel5_sh_m_mmm1 +
    (373 / 3072) * rel5_st_m_0001 + (-181 / 256) * rel5_st_m_000m + (-47 / 72) * rel5_sh_m_00mm +
    (61 / 384) * rel5_sh_m_01mm + (331 / 288) * rel5_sh_m_0m0m + (13 / 384) * rel5_sh_m_0m1m +
    (1 / 6) * rel5_sh_m_0mm1 + (-67 / 768) * rel5_sh_m_m01m + (17 / 192) * rel5_sh_m_m0m1 +
    (-83 / 768) * rel5_sh_m_m10m + (-1 / 2) * rel5_sh_m_m11m + (-41 / 32) * rel5_sh_m_m1m1 +
    (67 / 384) * rel5_sh_m_mm01 + (-101 / 3072) * rel5_st_01_00m + (5 / 64) * rel5_st_0m_001 +
    (149 / 1152) * rel5_sh_0m_00m + (2171 / 2304) * rel5_st_0m_00m +
    (-205 / 144) * rel5_sh_0m_0mm + (1 / 6) * rel5_sh_m1_m11 + (19 / 12) * rel5_sh_m1_mm1 +
    (-733 / 192) * rel5_mob_0mmm1 + (-79 / 144) * rel5_sh_m_000m + (269 / 576) * rel5_sh_m_001m +
    (-473 / 1152) * rel5_st_m_001m + (379 / 576) * rel5_sh_m_00m1 + (-227 / 576) * rel5_st_m_00m1 +
    (-37 / 384) * rel5_sh_m_010m + (23 / 192) * rel5_sh_m_01m1 + (1 / 9) * rel5_sh_m_0m01 +
    (-61 / 192) * rel5_sh_m_0m11 + (-89 / 576) * rel5_sh_m_m001 + (-37 / 4608) * rel5_st_m_m001 +
    (41 / 1152) * rel5_st_m_m00m + (19 / 192) * rel5_sh_m_m011 + (-5 / 128) * rel5_sh_m_m101 +
    (-1) * rel5_sh_m_m111 + (2573 / 9216) * rel5_st_01_01m + (1603 / 3072) * rel5_st_01_m0m +
    (-25 / 96) * rel5_st_0m_0m1 + (13 / 18) * rel5_st_0m_0mm + (5 / 32) * rel5_st_0m_m01 +
    (-1711 / 2304) * rel5_sh_m_0001 + (-47 / 72) * rel5_sh_m_0011 + (503 / 1152) * rel5_st_m_0011 +
    (163 / 144) * rel5_st_m_00mm + (-359 / 576) * rel5_sh_m_0101 + (-73 / 144) * rel5_st_m_010m +
    (7 / 576) * rel5_st_m_01m1 + (7 / 8) * rel5_st_m_0m0m + (-25 / 576) * rel5_st_m_0m1m +
    (11 / 192) * rel5_st_m_m01m + (-413 / 4608) * rel5_st_m_m0m1 + (37 / 2304) * rel5_st_m_m101 +
    (-41 / 576) * rel5_st_m_m10m + (5 / 32) * rel5_st_m_m1m1 + (-293 / 1152) * rel5_sh_01_00m +
    (1 / 12) * rel5_sh_01_01m + (-7 / 48) * rel5_sh_01_0m1 + (-1 / 16) * rel5_st_01_0m1 +
    (97 / 128) * rel5_st_01_0mm + (2 / 3) * rel5_sh_01_m11 + (173 / 1152) * rel5_sh_0m_001 +
    (-67 / 384) * rel5_sh_0m_01m + (-1 / 2) * rel5_sh_m1_011 + (13 / 384) * rel5_sh_m1_0m1 +
    (-19 / 384) * rel5_sh_m1_m01 + (21 / 2) * rel5_mob_00mmm + (-61 / 128) * rel5_mob_01mmm +
    (43 / 12) * rel5_mob_0m0mm + (67 / 384) * rel5_mob_0m1mm + (-83 / 384) * rel5_mob_m10mm +
    (-53 / 288) * rel5_st_m_011m + (5 / 48) * rel5_st_m_01mm + (77 / 384) * rel5_st_m_0m11 +
    (-15 / 128) * rel5_st_m_0mm1 + (-83 / 384) * rel5_st_m_m011 + (23 / 48) * rel5_st_m_m0mm +
    (-7 / 144) * rel5_st_m_m11m + (-1 / 8) * rel5_st_m_m1mm + (89 / 288) * rel5_st_m_mm0m +
    (-19 / 144) * rel5_st_m_mm1m + (1 / 2) * rel5_st_m_0mmm + (-1) * rel5_mob_0000m

theorem hpl_negOne_negOne_negOne_zero_negOne_at_one :
    hpl [negOne, negOne, negOne, zero, negOne] 1 =
      Li 4 (1 / 2) * log 2 + 4 * Li 5 (1 / 2) + 1 / 120 * log 2 ^ 5
      + 1 / 36 * log 2 ^ 3 * π ^ 2 - log 2 ^ 2 * zeta3 + 1 / 30 * log 2 * π ^ 4 - 4 * zeta5 := by
  linear_combination (97 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 4) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 96) * hpl_zero_one_zero_zero_one_at_one + (2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 2) * hpl_zero_one_zero_one_one_at_one + (1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (-74 / 15) * hpl_zero_zero_zero_zero_negOne_at_one + (4) * hpl_negOne_one_one_one_one_at_one +
    (-2021 / 480) * rel5_sh_m_mmmm + (241 / 192) * rel5_sh_m_0mmm + (-241 / 576) * rel5_sh_m_m0mm +
    (4 / 3) * rel5_sh_m_m1mm + (25 / 144) * rel5_sh_m_mm0m + (-149 / 64) * rel5_sh_m_mm1m +
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

theorem hpl_negOne_negOne_negOne_one_one_at_one :
    hpl [negOne, negOne, negOne, one, one] 1 =
      -Li 5 (1 / 2) + 1 / 60 * log 2 ^ 5 - 1 / 72 * log 2 ^ 3 * π ^ 2
      + 7 / 16 * log 2 ^ 2 * zeta3 - 1 / 90 * log 2 * π ^ 4 - 1 / 12 * zeta3 * π ^ 2
      + 63 / 32 * zeta5 := by
  linear_combination (-331 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (11 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (53 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (109 / 1152) * hpl_zero_one_zero_zero_one_at_one +
    (-1 / 2) * hpl_zero_zero_one_one_one_at_one + (-3 / 8) * hpl_zero_one_zero_one_one_at_one +
    (-1 / 8) * hpl_zero_one_one_zero_one_at_one + (6 / 5) * hpl_zero_zero_zero_zero_negOne_at_one +
    (-1) * hpl_negOne_one_one_one_one_at_one + (-211 / 1920) * rel5_sh_m_mmmm +
    (-25 / 768) * rel5_sh_m_0mmm + (25 / 2304) * rel5_sh_m_m0mm + (-1 / 3) * rel5_sh_m_m1mm +
    (-49 / 576) * rel5_sh_m_mm0m + (-233 / 768) * rel5_sh_m_mm1m + (-23 / 256) * rel5_sh_m_mmm1 +
    (-2011 / 15360) * rel5_st_m_0001 + (5 / 768) * rel5_st_m_000m + (1 / 72) * rel5_sh_m_00mm +
    (19 / 128) * rel5_sh_m_01mm + (-11 / 288) * rel5_sh_m_0m0m + (41 / 384) * rel5_sh_m_0m1m +
    (1 / 6) * rel5_sh_m_0mm1 + (19 / 256) * rel5_sh_m_m01m + (5 / 192) * rel5_sh_m_m0m1 +
    (73 / 768) * rel5_sh_m_m10m + (-1 / 2) * rel5_sh_m_m11m + (-59 / 96) * rel5_sh_m_m1m1 +
    (-19 / 128) * rel5_sh_m_mm01 + (1499 / 15360) * rel5_st_01_00m + (-1 / 6) * rel5_st_0m_001 +
    (53 / 1152) * rel5_sh_0m_00m + (647 / 2304) * rel5_st_0m_00m + (-1 / 144) * rel5_sh_0m_0mm +
    (1 / 6) * rel5_sh_m1_m11 + (-25 / 192) * rel5_mob_0mmm1 + (25 / 288) * rel5_sh_m_000m +
    (5 / 576) * rel5_sh_m_001m + (-29 / 1152) * rel5_st_m_001m + (7 / 576) * rel5_sh_m_00m1 +
    (-37 / 960) * rel5_st_m_00m1 + (11 / 384) * rel5_sh_m_010m + (-13 / 192) * rel5_sh_m_01m1 +
    (-23 / 144) * rel5_sh_m_0m01 + (-19 / 64) * rel5_sh_m_0m11 + (-29 / 576) * rel5_sh_m_m001 +
    (-151 / 7680) * rel5_st_m_m001 + (29 / 1152) * rel5_st_m_m00m + (-73 / 192) * rel5_sh_m_m011 +
    (-83 / 384) * rel5_sh_m_m101 + (-1) * rel5_sh_m_m111 + (1037 / 46080) * rel5_st_01_01m +
    (-4087 / 46080) * rel5_st_01_m0m + (-5 / 192) * rel5_st_0m_0m1 + (13 / 72) * rel5_st_0m_0mm +
    (-7 / 64) * rel5_st_0m_m01 + (-43 / 2304) * rel5_sh_m_0001 + (13 / 72) * rel5_sh_m_0011 +
    (203 / 1152) * rel5_st_m_0011 + (7 / 144) * rel5_st_m_00mm + (97 / 576) * rel5_sh_m_0101 +
    (-5 / 72) * rel5_st_m_010m + (29 / 960) * rel5_st_m_01m1 + (1 / 48) * rel5_st_m_0m0m +
    (-61 / 576) * rel5_st_m_0m1m + (-17 / 192) * rel5_st_m_m01m + (-767 / 7680) * rel5_st_m_m0m1 +
    (151 / 3840) * rel5_st_m_m101 + (-29 / 576) * rel5_st_m_m10m + (11 / 480) * rel5_st_m_m1m1 +
    (-161 / 1152) * rel5_sh_01_00m + (-1 / 24) * rel5_sh_01_01m + (-1 / 48) * rel5_sh_01_0m1 +
    (-1 / 16) * rel5_st_01_0m1 + (-35 / 128) * rel5_st_01_0mm + (1 / 6) * rel5_sh_01_m11 +
    (185 / 1152) * rel5_sh_0m_001 + (5 / 384) * rel5_sh_0m_01m + (3 / 128) * rel5_sh_m1_0m1 +
    (73 / 384) * rel5_sh_m1_m01 + (-57 / 128) * rel5_mob_01mmm + (-1 / 12) * rel5_mob_0m0mm +
    (-19 / 128) * rel5_mob_0m1mm + (73 / 384) * rel5_mob_m10mm + (7 / 288) * rel5_st_m_011m +
    (-7 / 48) * rel5_st_m_01mm + (41 / 384) * rel5_st_m_0m11 + (-73 / 384) * rel5_st_m_0mm1 +
    (73 / 384) * rel5_st_m_m011 + (11 / 48) * rel5_st_m_m0mm + (5 / 144) * rel5_st_m_m11m +
    (-1 / 8) * rel5_st_m_m1mm + (29 / 288) * rel5_st_m_mm0m + (-7 / 144) * rel5_st_m_mm1m +
    (1 / 2) * rel5_st_m_0mmm + (-1) * rel5_mob_0000m

theorem hpl_negOne_negOne_negOne_one_negOne_at_one :
    hpl [negOne, negOne, negOne, one, negOne] 1 =
      3 * Li 4 (1 / 2) * log 2 + 4 * Li 5 (1 / 2) + 1 / 12 * log 2 ^ 5
      - 5 / 72 * log 2 ^ 3 * π ^ 2 + 7 / 8 * log 2 ^ 2 * zeta3 + 1 / 90 * log 2 * π ^ 4
      - 4 * zeta5 := by
  linear_combination (97 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 4) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 96) * hpl_zero_one_zero_zero_one_at_one + (2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 2) * hpl_zero_one_zero_one_one_at_one + (1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (-74 / 15) * hpl_zero_zero_zero_zero_negOne_at_one + (4) * hpl_negOne_one_one_one_one_at_one +
    (-1637 / 480) * rel5_sh_m_mmmm + (49 / 192) * rel5_sh_m_0mmm + (-49 / 576) * rel5_sh_m_m0mm +
    (4 / 3) * rel5_sh_m_m1mm + (-23 / 144) * rel5_sh_m_mm0m + (-149 / 64) * rel5_sh_m_mm1m +
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

theorem hpl_negOne_negOne_negOne_negOne_one_at_one :
    hpl [negOne, negOne, negOne, negOne, one] 1 =
      -Li 4 (1 / 2) * log 2 - Li 5 (1 / 2) - 1 / 24 * log 2 ^ 5
      + 1 / 36 * log 2 ^ 3 * π ^ 2 - 7 / 16 * log 2 ^ 2 * zeta3 + zeta5 := by
  linear_combination (-97 / 384) * hpl_zero_zero_zero_zero_one_at_one +
    (21 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (335 / 384) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 384) * hpl_zero_one_zero_zero_one_at_one + (-1 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 8) * hpl_zero_one_zero_one_one_at_one + (-1 / 8) * hpl_zero_one_one_zero_one_at_one +
    (37 / 30) * hpl_zero_zero_zero_zero_negOne_at_one + (-1) * hpl_negOne_one_one_one_one_at_one +
    (1637 / 1920) * rel5_sh_m_mmmm + (-49 / 768) * rel5_sh_m_0mmm + (49 / 2304) * rel5_sh_m_m0mm +
    (-1 / 3) * rel5_sh_m_m1mm + (23 / 576) * rel5_sh_m_mm0m + (149 / 256) * rel5_sh_m_mm1m +
    (321 / 256) * rel5_sh_m_mmm1 + (-129 / 5120) * rel5_st_m_0001 +
    (-889 / 2304) * rel5_st_m_000m + (-13 / 24) * rel5_sh_m_00mm + (-47 / 384) * rel5_sh_m_01mm +
    (35 / 96) * rel5_sh_m_0m0m + (1 / 384) * rel5_sh_m_0m1m + (1 / 6) * rel5_sh_m_0mm1 +
    (-47 / 768) * rel5_sh_m_m01m + (13 / 192) * rel5_sh_m_m0m1 + (-95 / 768) * rel5_sh_m_m10m +
    (-1 / 2) * rel5_sh_m_m11m + (-25 / 32) * rel5_sh_m_m1m1 + (47 / 384) * rel5_sh_m_mm01 +
    (-479 / 5120) * rel5_st_01_00m + (-11 / 96) * rel5_st_0m_001 + (13 / 128) * rel5_sh_0m_00m +
    (1471 / 2304) * rel5_st_0m_00m + (-19 / 48) * rel5_sh_0m_0mm + (1 / 6) * rel5_sh_m1_m11 +
    (1 / 2) * rel5_sh_m1_mm1 + (-49 / 192) * rel5_mob_0mmm1 + (-9 / 32) * rel5_sh_m_000m +
    (71 / 192) * rel5_sh_m_001m + (-325 / 1152) * rel5_st_m_001m + (85 / 192) * rel5_sh_m_00m1 +
    (-847 / 2880) * rel5_st_m_00m1 + (43 / 384) * rel5_sh_m_010m + (11 / 192) * rel5_sh_m_01m1 +
    (1 / 48) * rel5_sh_m_0m01 + (-17 / 192) * rel5_sh_m_0m11 + (-23 / 192) * rel5_sh_m_m001 +
    (259 / 23040) * rel5_st_m_m001 + (37 / 1152) * rel5_st_m_m00m + (31 / 192) * rel5_sh_m_m011 +
    (5 / 384) * rel5_sh_m_m101 + (-1) * rel5_sh_m_m111 + (7109 / 46080) * rel5_st_01_01m +
    (8161 / 46080) * rel5_st_01_m0m + (-35 / 192) * rel5_st_0m_0m1 + (13 / 24) * rel5_st_0m_0mm +
    (13 / 192) * rel5_st_0m_m01 + (-107 / 256) * rel5_sh_m_0001 + (-3 / 8) * rel5_sh_m_0011 +
    (113 / 384) * rel5_st_m_0011 + (37 / 48) * rel5_st_m_00mm + (-23 / 64) * rel5_sh_m_0101 +
    (-13 / 36) * rel5_st_m_010m + (-1 / 2880) * rel5_st_m_01m1 + (85 / 144) * rel5_st_m_0m0m +
    (-37 / 576) * rel5_st_m_0m1m + (5 / 576) * rel5_st_m_m01m + (-757 / 23040) * rel5_st_m_m0m1 +
    (-259 / 11520) * rel5_st_m_m101 + (-37 / 576) * rel5_st_m_m10m + (9 / 160) * rel5_st_m_m1m1 +
    (-19 / 384) * rel5_sh_01_00m + (1 / 24) * rel5_sh_01_01m + (-5 / 48) * rel5_sh_01_0m1 +
    (-1 / 16) * rel5_st_01_0m1 + (95 / 384) * rel5_st_01_0mm + (1 / 2) * rel5_sh_01_m11 +
    (-5 / 384) * rel5_sh_0m_001 + (-43 / 384) * rel5_sh_0m_01m + (-1 / 3) * rel5_sh_m1_011 +
    (-31 / 384) * rel5_sh_m1_0m1 + (-31 / 384) * rel5_sh_m1_m01 + (4) * rel5_mob_00mmm +
    (47 / 128) * rel5_mob_01mmm + (5 / 4) * rel5_mob_0m0mm + (47 / 384) * rel5_mob_0m1mm +
    (-95 / 384) * rel5_mob_m10mm + (-11 / 96) * rel5_st_m_011m + (1 / 48) * rel5_st_m_01mm +
    (1 / 384) * rel5_st_m_0m11 + (-11 / 128) * rel5_st_m_0mm1 + (-95 / 384) * rel5_st_m_m011 +
    (19 / 48) * rel5_st_m_m0mm + (-1 / 48) * rel5_st_m_m11m + (-1 / 8) * rel5_st_m_m1mm +
    (23 / 96) * rel5_st_m_mm0m + (-5 / 48) * rel5_st_m_mm1m + (1 / 2) * rel5_st_m_0mmm +
    (-1) * rel5_mob_0000m

theorem hpl_negOne_negOne_negOne_negOne_negOne_at_one :
    hpl [negOne, negOne, negOne, negOne, negOne] 1 =
      1 / 120 * log 2 ^ 5 := by
  linear_combination (1 / 5) * rel5_sh_m_mmmm

end QED.Polylog.HPL
