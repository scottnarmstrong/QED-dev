/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLAlt5Rel

/-!
# Harmonic polylogarithms at `1`: alternating words of weight five (A)

The values `H(w; 1)` of the 27 words `w` of weight five over `{0, 1, -1}`
starting with `0, 0` or `0, 1` and with no trailing zero (excluding those known in closed form in
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

theorem hpl_zero_zero_zero_one_negOne_at_one :
    hpl [zero, zero, zero, one, negOne] 1 =
      1 / 48 * log 2 * π ^ 4 + 1 / 16 * zeta3 * π ^ 2 - 2 * zeta5 := by
  linear_combination (-2) * hpl_zero_zero_zero_zero_one_at_one + (1) * rel5_st_m_000m +
    (1) * rel5_st_0m_00m + (1) * rel5_sh_m_0001

theorem hpl_zero_zero_zero_negOne_one_at_one :
    hpl [zero, zero, zero, negOne, one] 1 =
      -1 / 48 * log 2 * π ^ 4 - 1 / 8 * zeta3 * π ^ 2 + 91 / 32 * zeta5 := by
  linear_combination (-101 / 288) * hpl_zero_zero_zero_zero_one_at_one +
    (-11 / 12) * hpl_zero_zero_zero_one_one_at_one +
    (-305 / 288) * hpl_zero_zero_one_zero_one_at_one +
    (-121 / 288) * hpl_zero_one_zero_zero_one_at_one + (-1) * hpl_zero_zero_one_one_one_at_one +
    (-1 / 2) * hpl_zero_one_zero_one_one_at_one + (-1 / 6) * hpl_zero_one_one_zero_one_at_one +
    (7 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (-37 / 32) * rel5_sh_m_mmmm +
    (-3 / 64) * rel5_sh_m_0mmm + (1 / 64) * rel5_sh_m_m0mm + (-5 / 16) * rel5_sh_m_mm0m +
    (-91 / 64) * rel5_sh_m_mm1m + (-79 / 64) * rel5_sh_m_mmm1 + (-233 / 256) * rel5_st_m_0001 +
    (137 / 576) * rel5_st_m_000m + (11 / 18) * rel5_sh_m_00mm + (19 / 32) * rel5_sh_m_01mm +
    (-5 / 9) * rel5_sh_m_0m0m + (11 / 32) * rel5_sh_m_0m1m + (1 / 3) * rel5_sh_m_0mm1 +
    (19 / 64) * rel5_sh_m_m01m + (-1 / 48) * rel5_sh_m_m0m1 + (27 / 64) * rel5_sh_m_m10m +
    (5 / 12) * rel5_sh_m_m1m1 + (-19 / 32) * rel5_sh_m_mm01 + (335 / 768) * rel5_st_01_00m +
    (-133 / 192) * rel5_st_0m_001 + (2 / 9) * rel5_sh_0m_00m + (65 / 576) * rel5_st_0m_00m +
    (11 / 18) * rel5_sh_0m_0mm + (-11 / 12) * rel5_sh_m1_mm1 + (-3 / 16) * rel5_mob_0mmm1 +
    (-13 / 288) * rel5_sh_m_000m + (-17 / 36) * rel5_sh_m_001m + (73 / 288) * rel5_st_m_001m +
    (-79 / 144) * rel5_sh_m_00m1 + (19 / 72) * rel5_st_m_00m1 + (-1 / 8) * rel5_sh_m_010m +
    (-5 / 16) * rel5_sh_m_01m1 + (-19 / 36) * rel5_sh_m_0m01 + (-41 / 48) * rel5_sh_m_0m11 +
    (5 / 144) * rel5_sh_m_m001 + (-65 / 1152) * rel5_st_m_m001 + (-1 / 288) * rel5_st_m_m00m +
    (-65 / 48) * rel5_sh_m_m011 + (-21 / 32) * rel5_sh_m_m101 + (-407 / 2304) * rel5_st_01_01m +
    (-115 / 256) * rel5_st_01_m0m + (9 / 64) * rel5_st_0m_0m1 + (-1 / 18) * rel5_st_0m_0mm +
    (-23 / 64) * rel5_st_0m_m01 + (139 / 576) * rel5_sh_m_0001 + (17 / 18) * rel5_sh_m_0011 +
    (67 / 288) * rel5_st_m_0011 + (-31 / 36) * rel5_st_m_00mm + (143 / 144) * rel5_sh_m_0101 +
    (5 / 12) * rel5_st_m_010m + (11 / 144) * rel5_st_m_01m1 + (-29 / 36) * rel5_st_m_0m0m +
    (-13 / 48) * rel5_st_m_0m1m + (-37 / 144) * rel5_st_m_m01m + (-265 / 1152) * rel5_st_m_m0m1 +
    (65 / 576) * rel5_st_m_m101 + (1 / 144) * rel5_st_m_m10m + (-1 / 12) * rel5_st_m_m1m1 +
    (-91 / 288) * rel5_sh_01_00m + (-1 / 6) * rel5_sh_01_01m + (1 / 12) * rel5_sh_01_0m1 +
    (-97 / 96) * rel5_st_01_0mm + (-1 / 6) * rel5_sh_01_m11 + (211 / 288) * rel5_sh_0m_001 +
    (5 / 24) * rel5_sh_0m_01m + (1 / 2) * rel5_sh_m1_011 + (17 / 96) * rel5_sh_m1_0m1 +
    (65 / 96) * rel5_sh_m1_m01 + (-11 / 2) * rel5_mob_00mmm + (-57 / 32) * rel5_mob_01mmm +
    (-2) * rel5_mob_0m0mm + (-19 / 32) * rel5_mob_0m1mm + (27 / 32) * rel5_mob_m10mm +
    (17 / 72) * rel5_st_m_011m + (-5 / 12) * rel5_st_m_01mm + (11 / 32) * rel5_st_m_0m11 +
    (-49 / 96) * rel5_st_m_0mm1 + (27 / 32) * rel5_st_m_m011 + (1 / 12) * rel5_st_m_m0mm +
    (1 / 36) * rel5_st_m_m11m + (-5 / 72) * rel5_st_m_mm0m + (1 / 36) * rel5_st_m_mm1m +
    (1) * rel5_st_m_0mmm

theorem hpl_zero_zero_zero_negOne_negOne_at_one :
    hpl [zero, zero, zero, negOne, negOne] 1 =
      1 / 12 * zeta3 * π ^ 2 - 29 / 32 * zeta5 := by
  linear_combination (1 / 2) * hpl_zero_zero_zero_zero_one_at_one +
    (-3 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (1 / 2) * rel5_st_m_0001 +
    (-1 / 2) * rel5_st_m_000m + (1 / 2) * rel5_st_01_00m + (1 / 2) * rel5_st_0m_001 +
    (1 / 2) * rel5_sh_m_000m + (-1 / 2) * rel5_sh_m_0001 + (-1 / 2) * rel5_sh_01_00m +
    (1 / 2) * rel5_sh_0m_001

theorem hpl_zero_zero_one_zero_negOne_at_one :
    hpl [zero, zero, one, zero, negOne] 1 =
      -1 / 24 * zeta3 * π ^ 2 + 21 / 32 * zeta5 := by
  linear_combination (3) * hpl_zero_zero_zero_zero_one_at_one +
    (-5 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (3 / 2) * rel5_st_m_0001 +
    (-3 / 2) * rel5_st_m_000m + (1) * rel5_st_0m_001 + (-1 / 2) * rel5_sh_0m_00m +
    (-3 / 2) * rel5_st_0m_00m + (3 / 2) * rel5_sh_m_000m + (-3 / 2) * rel5_sh_m_0001

theorem hpl_zero_zero_one_one_negOne_at_one :
    hpl [zero, zero, one, one, negOne] 1 =
      -2 * Li 4 (1 / 2) * log 2 - 2 * Li 5 (1 / 2) - 1 / 15 * log 2 ^ 5
      + 1 / 18 * log 2 ^ 3 * π ^ 2 - 1 / 96 * log 2 * π ^ 4 - 1 / 96 * zeta3 * π ^ 2
      + 151 / 64 * zeta5 := by
  linear_combination (-289 / 192) * hpl_zero_zero_zero_zero_one_at_one +
    (21 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (335 / 192) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 192) * hpl_zero_one_zero_zero_one_at_one + (-1) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 4) * hpl_zero_one_zero_one_one_at_one + (-1 / 4) * hpl_zero_one_one_zero_one_at_one +
    (47 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-2) * hpl_negOne_one_one_one_one_at_one +
    (869 / 960) * rel5_sh_m_mmmm + (-49 / 384) * rel5_sh_m_0mmm + (49 / 1152) * rel5_sh_m_m0mm +
    (-2 / 3) * rel5_sh_m_m1mm + (23 / 288) * rel5_sh_m_mm0m + (85 / 128) * rel5_sh_m_mm1m +
    (129 / 128) * rel5_sh_m_mmm1 + (-429 / 512) * rel5_st_m_0001 + (-457 / 1152) * rel5_st_m_000m +
    (-25 / 12) * rel5_sh_m_00mm + (-47 / 192) * rel5_sh_m_01mm + (-13 / 48) * rel5_sh_m_0m0m +
    (1 / 192) * rel5_sh_m_0m1m + (1 / 3) * rel5_sh_m_0mm1 + (-47 / 384) * rel5_sh_m_m01m +
    (13 / 96) * rel5_sh_m_m0m1 + (-95 / 384) * rel5_sh_m_m10m + (-1) * rel5_sh_m_m11m +
    (-21 / 16) * rel5_sh_m_m1m1 + (47 / 192) * rel5_sh_m_mm01 + (45 / 512) * rel5_st_01_00m +
    (-7 / 6) * rel5_st_0m_001 + (37 / 64) * rel5_sh_0m_00m + (2191 / 1152) * rel5_st_0m_00m +
    (5 / 24) * rel5_sh_0m_0mm + (1 / 3) * rel5_sh_m1_m11 + (1 / 2) * rel5_sh_m1_mm1 +
    (-49 / 96) * rel5_mob_0mmm1 + (-11 / 16) * rel5_sh_m_000m + (95 / 96) * rel5_sh_m_001m +
    (-325 / 576) * rel5_st_m_001m + (85 / 96) * rel5_sh_m_00m1 + (-239 / 288) * rel5_st_m_00m1 +
    (115 / 192) * rel5_sh_m_010m + (11 / 96) * rel5_sh_m_01m1 + (1 / 24) * rel5_sh_m_0m01 +
    (-17 / 96) * rel5_sh_m_0m11 + (-23 / 96) * rel5_sh_m_m001 + (71 / 2304) * rel5_st_m_m001 +
    (37 / 576) * rel5_st_m_m00m + (31 / 96) * rel5_sh_m_m011 + (5 / 192) * rel5_sh_m_m101 +
    (-2) * rel5_sh_m_m111 + (1345 / 4608) * rel5_st_01_01m + (-595 / 4608) * rel5_st_01_m0m +
    (-53 / 96) * rel5_st_0m_0m1 + (13 / 12) * rel5_st_0m_0mm + (-5 / 96) * rel5_st_0m_m01 +
    (-59 / 128) * rel5_sh_m_0001 + (-3 / 4) * rel5_sh_m_0011 + (305 / 192) * rel5_st_m_0011 +
    (37 / 24) * rel5_st_m_00mm + (-23 / 32) * rel5_sh_m_0101 + (-13 / 18) * rel5_st_m_010m +
    (-5 / 288) * rel5_st_m_01m1 + (85 / 72) * rel5_st_m_0m0m + (-37 / 288) * rel5_st_m_0m1m +
    (5 / 288) * rel5_st_m_m01m + (-113 / 2304) * rel5_st_m_m0m1 + (-71 / 1152) * rel5_st_m_m101 +
    (-37 / 288) * rel5_st_m_m10m + (1 / 16) * rel5_st_m_m1m1 + (-67 / 192) * rel5_sh_01_00m +
    (1 / 12) * rel5_sh_01_01m + (-5 / 24) * rel5_sh_01_0m1 + (-1 / 8) * rel5_st_01_0m1 +
    (-97 / 192) * rel5_st_01_0mm + (1) * rel5_sh_01_m11 + (43 / 192) * rel5_sh_0m_001 +
    (-19 / 192) * rel5_sh_0m_01m + (-2 / 3) * rel5_sh_m1_011 + (-31 / 192) * rel5_sh_m1_0m1 +
    (-31 / 192) * rel5_sh_m1_m01 + (5) * rel5_mob_00mmm + (47 / 64) * rel5_mob_01mmm +
    (3 / 2) * rel5_mob_0m0mm + (47 / 192) * rel5_mob_0m1mm + (-95 / 192) * rel5_mob_m10mm +
    (-11 / 48) * rel5_st_m_011m + (1 / 24) * rel5_st_m_01mm + (1 / 192) * rel5_st_m_0m11 +
    (-11 / 64) * rel5_st_m_0mm1 + (-95 / 192) * rel5_st_m_m011 + (19 / 24) * rel5_st_m_m0mm +
    (-1 / 24) * rel5_st_m_m11m + (-1 / 4) * rel5_st_m_m1mm + (23 / 48) * rel5_st_m_mm0m +
    (-5 / 24) * rel5_st_m_mm1m + (1) * rel5_st_m_0mmm + (-2) * rel5_mob_0000m

theorem hpl_zero_zero_one_negOne_one_at_one :
    hpl [zero, zero, one, negOne, one] 1 =
      -2 * Li 5 (1 / 2) + 1 / 60 * log 2 ^ 5 - 1 / 36 * log 2 ^ 3 * π ^ 2
      - 7 / 8 * log 2 ^ 2 * zeta3 + 11 / 1440 * log 2 * π ^ 4 + 5 / 16 * zeta3 * π ^ 2
      - 159 / 64 * zeta5 := by
  linear_combination (-239 / 288) * hpl_zero_zero_zero_zero_one_at_one +
    (55 / 12) * hpl_zero_zero_zero_one_one_at_one +
    (1015 / 288) * hpl_zero_zero_one_zero_one_at_one +
    (359 / 288) * hpl_zero_one_zero_zero_one_at_one + (-1 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-1 / 2) * hpl_zero_one_zero_one_one_at_one + (-1 / 6) * hpl_zero_one_one_zero_one_at_one +
    (25 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-2) * hpl_negOne_one_one_one_one_at_one +
    (89 / 60) * rel5_sh_m_mmmm + (-5 / 48) * rel5_sh_m_0mmm + (5 / 144) * rel5_sh_m_m0mm +
    (-2 / 3) * rel5_sh_m_m1mm + (17 / 72) * rel5_sh_m_mm0m + (11 / 8) * rel5_sh_m_mm1m +
    (13 / 8) * rel5_sh_m_mmm1 + (71 / 128) * rel5_st_m_0001 + (-57 / 64) * rel5_st_m_000m +
    (-7 / 18) * rel5_sh_m_00mm + (-13 / 24) * rel5_sh_m_01mm + (181 / 144) * rel5_sh_m_0m0m +
    (-1 / 6) * rel5_sh_m_0m1m + (1 / 6) * rel5_sh_m_0mm1 + (-13 / 48) * rel5_sh_m_m01m +
    (7 / 48) * rel5_sh_m_m0m1 + (-11 / 24) * rel5_sh_m_m10m + (-1) * rel5_sh_m_m11m +
    (-73 / 48) * rel5_sh_m_m1m1 + (13 / 24) * rel5_sh_m_mm01 + (-193 / 192) * rel5_st_01_00m +
    (47 / 128) * rel5_st_0m_001 + (-91 / 576) * rel5_sh_0m_00m + (991 / 576) * rel5_st_0m_00m +
    (-79 / 72) * rel5_sh_0m_0mm + (1 / 3) * rel5_sh_m1_m11 + (23 / 24) * rel5_sh_m1_mm1 +
    (-5 / 12) * rel5_mob_0mmm1 + (-311 / 576) * rel5_sh_m_000m + (281 / 288) * rel5_sh_m_001m +
    (-343 / 288) * rel5_st_m_001m + (239 / 144) * rel5_sh_m_00m1 + (-205 / 288) * rel5_st_m_00m1 +
    (55 / 192) * rel5_sh_m_010m + (13 / 48) * rel5_sh_m_01m1 + (5 / 9) * rel5_sh_m_0m01 +
    (1 / 4) * rel5_sh_m_0m11 + (-37 / 144) * rel5_sh_m_m001 + (17 / 288) * rel5_st_m_m001 +
    (19 / 288) * rel5_st_m_m00m + (1) * rel5_sh_m_m011 + (17 / 48) * rel5_sh_m_m101 +
    (-2) * rel5_sh_m_m111 + (49 / 192) * rel5_st_01_01m + (415 / 576) * rel5_st_01_m0m +
    (-167 / 384) * rel5_st_0m_0m1 + (29 / 18) * rel5_st_0m_0mm + (121 / 384) * rel5_st_0m_m01 +
    (-551 / 576) * rel5_sh_m_0001 + (-20 / 9) * rel5_sh_m_0011 + (-19 / 36) * rel5_st_m_0011 +
    (107 / 36) * rel5_st_m_00mm + (-283 / 144) * rel5_sh_m_0101 + (-85 / 72) * rel5_st_m_010m +
    (-1 / 18) * rel5_st_m_01m1 + (7 / 3) * rel5_st_m_0m0m + (1 / 144) * rel5_st_m_0m1m +
    (7 / 48) * rel5_st_m_m01m + (19 / 288) * rel5_st_m_m0m1 + (-17 / 144) * rel5_st_m_m101 +
    (-19 / 144) * rel5_st_m_m10m + (5 / 48) * rel5_st_m_m1m1 + (233 / 288) * rel5_sh_01_00m +
    (2 / 3) * rel5_sh_01_01m + (-1 / 4) * rel5_sh_01_0m1 + (-1 / 8) * rel5_st_01_0m1 +
    (3 / 2) * rel5_st_01_0mm + (13 / 12) * rel5_sh_01_m11 + (-329 / 288) * rel5_sh_0m_001 +
    (-37 / 64) * rel5_sh_0m_01m + (-11 / 12) * rel5_sh_m1_011 + (-1 / 4) * rel5_sh_m1_0m1 +
    (-1 / 2) * rel5_sh_m1_m01 + (31 / 4) * rel5_mob_00mmm + (13 / 8) * rel5_mob_01mmm +
    (5 / 2) * rel5_mob_0m0mm + (13 / 24) * rel5_mob_0m1mm + (-11 / 12) * rel5_mob_m10mm +
    (-25 / 72) * rel5_st_m_011m + (1 / 4) * rel5_st_m_01mm + (-1 / 6) * rel5_st_m_0m11 +
    (1 / 12) * rel5_st_m_0mm1 + (-11 / 12) * rel5_st_m_m011 + (3 / 4) * rel5_st_m_m0mm +
    (-1 / 18) * rel5_st_m_m11m + (-1 / 4) * rel5_st_m_m1mm + (37 / 72) * rel5_st_m_mm0m +
    (-2 / 9) * rel5_st_m_mm1m + (1 / 2) * rel5_st_m_0mmm + (-2) * rel5_mob_0000m

theorem hpl_zero_zero_one_negOne_negOne_at_one :
    hpl [zero, zero, one, negOne, negOne] 1 =
      -2 * Li 4 (1 / 2) * log 2 - 4 * Li 5 (1 / 2) - 1 / 20 * log 2 ^ 5
      + 1 / 36 * log 2 ^ 3 * π ^ 2 + 7 / 8 * log 2 ^ 2 * zeta3 - 49 / 1440 * log 2 * π ^ 4
      - 13 / 96 * zeta3 * π ^ 2 + 47 / 8 * zeta5 := by
  linear_combination (47 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (21 / 4) * hpl_zero_zero_zero_one_one_at_one + (335 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 96) * hpl_zero_one_zero_zero_one_at_one + (-2) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 2) * hpl_zero_one_zero_one_one_at_one + (-1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (16 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (869 / 480) * rel5_sh_m_mmmm + (-49 / 192) * rel5_sh_m_0mmm + (49 / 576) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (23 / 144) * rel5_sh_m_mm0m + (85 / 64) * rel5_sh_m_mm1m +
    (129 / 64) * rel5_sh_m_mmm1 + (35 / 256) * rel5_st_m_0001 + (-1249 / 576) * rel5_st_m_000m +
    (-13 / 6) * rel5_sh_m_00mm + (-47 / 96) * rel5_sh_m_01mm + (11 / 24) * rel5_sh_m_0m0m +
    (1 / 96) * rel5_sh_m_0m1m + (2 / 3) * rel5_sh_m_0mm1 + (-47 / 192) * rel5_sh_m_m01m +
    (13 / 48) * rel5_sh_m_m0m1 + (-95 / 192) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-21 / 8) * rel5_sh_m_m1m1 + (47 / 96) * rel5_sh_m_mm01 + (-147 / 256) * rel5_st_01_00m +
    (-43 / 48) * rel5_st_0m_001 + (9 / 32) * rel5_sh_0m_00m + (967 / 576) * rel5_st_0m_00m +
    (-7 / 12) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (1) * rel5_sh_m1_mm1 +
    (-49 / 48) * rel5_mob_0mmm1 + (-1 / 4) * rel5_sh_m_000m + (83 / 48) * rel5_sh_m_001m +
    (-325 / 288) * rel5_st_m_001m + (85 / 48) * rel5_sh_m_00m1 + (-203 / 144) * rel5_st_m_00m1 +
    (79 / 96) * rel5_sh_m_010m + (11 / 48) * rel5_sh_m_01m1 + (1 / 12) * rel5_sh_m_0m01 +
    (-17 / 48) * rel5_sh_m_0m11 + (-23 / 48) * rel5_sh_m_m001 + (71 / 1152) * rel5_st_m_m001 +
    (37 / 288) * rel5_st_m_m00m + (31 / 48) * rel5_sh_m_m011 + (5 / 96) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (1345 / 2304) * rel5_st_01_01m + (557 / 2304) * rel5_st_01_m0m +
    (-11 / 12) * rel5_st_0m_0m1 + (13 / 6) * rel5_st_0m_0mm + (1 / 12) * rel5_st_0m_m01 +
    (-147 / 64) * rel5_sh_m_0001 + (-3 / 2) * rel5_sh_m_0011 + (113 / 96) * rel5_st_m_0011 +
    (37 / 12) * rel5_st_m_00mm + (-23 / 16) * rel5_sh_m_0101 + (-13 / 9) * rel5_st_m_010m +
    (-5 / 144) * rel5_st_m_01m1 + (85 / 36) * rel5_st_m_0m0m + (-37 / 144) * rel5_st_m_0m1m +
    (5 / 144) * rel5_st_m_m01m + (-113 / 1152) * rel5_st_m_m0m1 + (-71 / 576) * rel5_st_m_m101 +
    (-37 / 144) * rel5_st_m_m10m + (1 / 8) * rel5_st_m_m1m1 + (5 / 96) * rel5_sh_01_00m +
    (1 / 6) * rel5_sh_01_01m + (-5 / 12) * rel5_sh_01_0m1 + (-1 / 4) * rel5_st_01_0m1 +
    (-1 / 96) * rel5_st_01_0mm + (2) * rel5_sh_01_m11 + (-29 / 96) * rel5_sh_0m_001 +
    (-31 / 96) * rel5_sh_0m_01m + (-4 / 3) * rel5_sh_m1_011 + (-31 / 96) * rel5_sh_m1_0m1 +
    (-31 / 96) * rel5_sh_m1_m01 + (10) * rel5_mob_00mmm + (47 / 32) * rel5_mob_01mmm +
    (3) * rel5_mob_0m0mm + (47 / 96) * rel5_mob_0m1mm + (-95 / 96) * rel5_mob_m10mm +
    (-11 / 24) * rel5_st_m_011m + (1 / 12) * rel5_st_m_01mm + (1 / 96) * rel5_st_m_0m11 +
    (-11 / 32) * rel5_st_m_0mm1 + (-95 / 96) * rel5_st_m_m011 + (19 / 12) * rel5_st_m_m0mm +
    (-1 / 12) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm + (23 / 24) * rel5_st_m_mm0m +
    (-5 / 12) * rel5_st_m_mm1m + (2) * rel5_st_m_0mmm + (-4) * rel5_mob_0000m

theorem hpl_zero_zero_negOne_zero_one_at_one :
    hpl [zero, zero, negOne, zero, one] 1 =
      3 / 8 * zeta3 * π ^ 2 - 67 / 16 * zeta5 := by
  linear_combination (293 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (11 / 4) * hpl_zero_zero_zero_one_one_at_one + (305 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (121 / 96) * hpl_zero_one_zero_zero_one_at_one + (3) * hpl_zero_zero_one_one_one_at_one +
    (3 / 2) * hpl_zero_one_zero_one_one_at_one + (1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (-1) * hpl_zero_zero_zero_zero_negOne_at_one + (111 / 32) * rel5_sh_m_mmmm +
    (9 / 64) * rel5_sh_m_0mmm + (-3 / 64) * rel5_sh_m_m0mm + (15 / 16) * rel5_sh_m_mm0m +
    (273 / 64) * rel5_sh_m_mm1m + (237 / 64) * rel5_sh_m_mmm1 + (315 / 256) * rel5_st_m_0001 +
    (-425 / 192) * rel5_st_m_000m + (-11 / 6) * rel5_sh_m_00mm + (-57 / 32) * rel5_sh_m_01mm +
    (5 / 3) * rel5_sh_m_0m0m + (-33 / 32) * rel5_sh_m_0m1m + (-1) * rel5_sh_m_0mm1 +
    (-57 / 64) * rel5_sh_m_m01m + (1 / 16) * rel5_sh_m_m0m1 + (-81 / 64) * rel5_sh_m_m10m +
    (-5 / 4) * rel5_sh_m_m1m1 + (57 / 32) * rel5_sh_m_mm01 + (-335 / 256) * rel5_st_01_00m +
    (69 / 64) * rel5_st_0m_001 + (-1 / 6) * rel5_sh_0m_00m + (-161 / 192) * rel5_st_0m_00m +
    (-11 / 6) * rel5_sh_0m_0mm + (11 / 4) * rel5_sh_m1_mm1 + (9 / 16) * rel5_mob_0mmm1 +
    (-131 / 96) * rel5_sh_m_000m + (17 / 12) * rel5_sh_m_001m + (-73 / 96) * rel5_st_m_001m +
    (79 / 48) * rel5_sh_m_00m1 + (-19 / 24) * rel5_st_m_00m1 + (3 / 8) * rel5_sh_m_010m +
    (15 / 16) * rel5_sh_m_01m1 + (19 / 12) * rel5_sh_m_0m01 + (41 / 16) * rel5_sh_m_0m11 +
    (-5 / 48) * rel5_sh_m_m001 + (65 / 384) * rel5_st_m_m001 + (1 / 96) * rel5_st_m_m00m +
    (65 / 16) * rel5_sh_m_m011 + (63 / 32) * rel5_sh_m_m101 + (407 / 768) * rel5_st_01_01m +
    (345 / 256) * rel5_st_01_m0m + (-27 / 64) * rel5_st_0m_0m1 + (1 / 6) * rel5_st_0m_0mm +
    (69 / 64) * rel5_st_0m_m01 + (-427 / 192) * rel5_sh_m_0001 + (-17 / 6) * rel5_sh_m_0011 +
    (-67 / 96) * rel5_st_m_0011 + (31 / 12) * rel5_st_m_00mm + (-143 / 48) * rel5_sh_m_0101 +
    (-5 / 4) * rel5_st_m_010m + (-11 / 48) * rel5_st_m_01m1 + (29 / 12) * rel5_st_m_0m0m +
    (13 / 16) * rel5_st_m_0m1m + (37 / 48) * rel5_st_m_m01m + (265 / 384) * rel5_st_m_m0m1 +
    (-65 / 192) * rel5_st_m_m101 + (-1 / 48) * rel5_st_m_m10m + (1 / 4) * rel5_st_m_m1m1 +
    (91 / 96) * rel5_sh_01_00m + (1 / 2) * rel5_sh_01_01m + (-1 / 4) * rel5_sh_01_0m1 +
    (97 / 32) * rel5_st_01_0mm + (1 / 2) * rel5_sh_01_m11 + (-115 / 96) * rel5_sh_0m_001 +
    (-5 / 8) * rel5_sh_0m_01m + (-3 / 2) * rel5_sh_m1_011 + (-17 / 32) * rel5_sh_m1_0m1 +
    (-65 / 32) * rel5_sh_m1_m01 + (33 / 2) * rel5_mob_00mmm + (171 / 32) * rel5_mob_01mmm +
    (6) * rel5_mob_0m0mm + (57 / 32) * rel5_mob_0m1mm + (-81 / 32) * rel5_mob_m10mm +
    (-17 / 24) * rel5_st_m_011m + (5 / 4) * rel5_st_m_01mm + (-33 / 32) * rel5_st_m_0m11 +
    (49 / 32) * rel5_st_m_0mm1 + (-81 / 32) * rel5_st_m_m011 + (-1 / 4) * rel5_st_m_m0mm +
    (-1 / 12) * rel5_st_m_m11m + (5 / 24) * rel5_st_m_mm0m + (-1 / 12) * rel5_st_m_mm1m +
    (-3) * rel5_st_m_0mmm

theorem hpl_zero_zero_negOne_zero_negOne_at_one :
    hpl [zero, zero, negOne, zero, negOne] 1 =
      -5 / 48 * zeta3 * π ^ 2 + 41 / 32 * zeta5 := by
  linear_combination (-2) * hpl_zero_zero_zero_zero_one_at_one +
    (7 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (-3 / 2) * rel5_st_m_0001 +
    (3 / 2) * rel5_st_m_000m + (-1) * rel5_st_01_00m + (-1) * rel5_st_0m_001 +
    (1 / 2) * rel5_sh_0m_00m + (1 / 2) * rel5_st_0m_00m + (-3 / 2) * rel5_sh_m_000m +
    (3 / 2) * rel5_sh_m_0001 + (1) * rel5_sh_01_00m + (-1) * rel5_sh_0m_001

theorem hpl_zero_zero_negOne_one_one_at_one :
    hpl [zero, zero, negOne, one, one] 1 =
      2 * Li 5 (1 / 2) - 1 / 60 * log 2 ^ 5 + 1 / 36 * log 2 ^ 3 * π ^ 2
      + 1 / 360 * log 2 * π ^ 4 - 13 / 48 * zeta3 * π ^ 2 + 15 / 8 * zeta5 := by
  linear_combination (-25 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-23 / 4) * hpl_zero_zero_zero_one_one_at_one +
    (-107 / 24) * hpl_zero_zero_one_zero_one_at_one +
    (-43 / 24) * hpl_zero_one_zero_zero_one_at_one + (-1 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-5 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (2) * hpl_negOne_one_one_one_one_at_one +
    (-1267 / 480) * rel5_sh_m_mmmm + (11 / 192) * rel5_sh_m_0mmm + (-11 / 576) * rel5_sh_m_m0mm +
    (2 / 3) * rel5_sh_m_m1mm + (-79 / 144) * rel5_sh_m_mm0m + (-179 / 64) * rel5_sh_m_mm1m +
    (-183 / 64) * rel5_sh_m_mmm1 + (-295 / 256) * rel5_st_m_0001 + (649 / 288) * rel5_st_m_000m +
    (2) * rel5_sh_m_00mm + (109 / 96) * rel5_sh_m_01mm + (-15 / 16) * rel5_sh_m_0m0m +
    (49 / 96) * rel5_sh_m_0m1m + (1 / 6) * rel5_sh_m_0mm1 + (109 / 192) * rel5_sh_m_m01m +
    (-1 / 6) * rel5_sh_m_m0m1 + (169 / 192) * rel5_sh_m_m10m + (1) * rel5_sh_m_m11m +
    (31 / 16) * rel5_sh_m_m1m1 + (-109 / 96) * rel5_sh_m_mm01 + (257 / 256) * rel5_st_01_00m +
    (-71 / 384) * rel5_st_0m_001 + (25 / 192) * rel5_sh_0m_00m + (-499 / 288) * rel5_st_0m_00m +
    (29 / 24) * rel5_sh_0m_0mm + (-1 / 3) * rel5_sh_m1_m11 + (-15 / 8) * rel5_sh_m1_mm1 +
    (11 / 48) * rel5_mob_0mmm1 + (23 / 192) * rel5_sh_m_000m + (-163 / 96) * rel5_sh_m_001m +
    (13 / 9) * rel5_st_m_001m + (-53 / 24) * rel5_sh_m_00m1 + (353 / 288) * rel5_st_m_00m1 +
    (-175 / 192) * rel5_sh_m_010m + (-7 / 12) * rel5_sh_m_01m1 + (-29 / 24) * rel5_sh_m_0m01 +
    (-53 / 48) * rel5_sh_m_0m11 + (7 / 24) * rel5_sh_m_m001 + (-133 / 1152) * rel5_st_m_m001 +
    (-5 / 72) * rel5_st_m_m00m + (-113 / 48) * rel5_sh_m_m011 + (-97 / 96) * rel5_sh_m_m101 +
    (2) * rel5_sh_m_m111 + (-1427 / 2304) * rel5_st_01_01m + (-1687 / 2304) * rel5_st_01_m0m +
    (317 / 384) * rel5_st_0m_0m1 + (-23 / 12) * rel5_st_0m_0mm + (-163 / 384) * rel5_st_0m_m01 +
    (223 / 96) * rel5_sh_m_0001 + (19 / 6) * rel5_sh_m_0011 + (-23 / 96) * rel5_st_m_0011 +
    (-23 / 6) * rel5_st_m_00mm + (17 / 6) * rel5_sh_m_0101 + (31 / 18) * rel5_st_m_010m +
    (19 / 144) * rel5_st_m_01m1 + (-217 / 72) * rel5_st_m_0m0m + (-5 / 18) * rel5_st_m_0m1m +
    (-29 / 72) * rel5_st_m_m01m + (-341 / 1152) * rel5_st_m_m0m1 + (133 / 576) * rel5_st_m_m101 +
    (5 / 36) * rel5_st_m_m10m + (-3 / 16) * rel5_st_m_m1m1 + (-1 / 2) * rel5_sh_01_00m +
    (-7 / 12) * rel5_sh_01_01m + (7 / 12) * rel5_sh_01_0m1 + (-1 / 8) * rel5_st_01_0m1 +
    (-121 / 96) * rel5_st_01_0mm + (-5 / 4) * rel5_sh_01_m11 + (1) * rel5_sh_0m_001 +
    (127 / 192) * rel5_sh_0m_01m + (17 / 12) * rel5_sh_m1_011 + (41 / 96) * rel5_sh_m1_0m1 +
    (113 / 96) * rel5_sh_m1_m01 + (-53 / 4) * rel5_mob_00mmm + (-109 / 32) * rel5_mob_01mmm +
    (-9 / 2) * rel5_mob_0m0mm + (-109 / 96) * rel5_mob_0m1mm + (169 / 96) * rel5_mob_m10mm +
    (7 / 12) * rel5_st_m_011m + (-2 / 3) * rel5_st_m_01mm + (49 / 96) * rel5_st_m_0m11 +
    (-19 / 32) * rel5_st_m_0mm1 + (169 / 96) * rel5_st_m_m011 + (-2 / 3) * rel5_st_m_m0mm +
    (1 / 12) * rel5_st_m_m11m + (1 / 4) * rel5_st_m_m1mm + (-7 / 12) * rel5_st_m_mm0m +
    (1 / 4) * rel5_st_m_mm1m + (1 / 2) * rel5_st_m_0mmm + (2) * rel5_mob_0000m

theorem hpl_zero_zero_negOne_one_negOne_at_one :
    hpl [zero, zero, negOne, one, negOne] 1 =
      2 * Li 4 (1 / 2) * log 2 + 1 / 12 * log 2 ^ 5 - 1 / 12 * log 2 ^ 3 * π ^ 2
      + 11 / 1440 * log 2 * π ^ 4 + 1 / 12 * zeta3 * π ^ 2 - 15 / 8 * zeta5 := by
  linear_combination (-2) * hpl_zero_zero_zero_zero_negOne_at_one + (7 / 8) * rel5_st_m_0001 +
    (-1 / 4) * rel5_st_m_000m + (1 / 2) * rel5_st_01_00m + (5 / 8) * rel5_st_0m_001 +
    (-1 / 4) * rel5_sh_0m_00m + (1 / 4) * rel5_st_0m_00m + (3 / 4) * rel5_sh_m_000m +
    (-1 / 2) * rel5_sh_m_001m + (1 / 2) * rel5_st_m_00m1 + (-1 / 4) * rel5_sh_m_010m +
    (1 / 8) * rel5_st_0m_0m1 + (1 / 8) * rel5_st_0m_m01 + (-1 / 4) * rel5_sh_m_0001 +
    (-1 / 2) * rel5_sh_01_00m + (1 / 2) * rel5_sh_0m_001 + (1 / 4) * rel5_sh_0m_01m

theorem hpl_zero_zero_negOne_negOne_one_at_one :
    hpl [zero, zero, negOne, negOne, one] 1 =
      4 * Li 5 (1 / 2) - 1 / 30 * log 2 ^ 5 + 1 / 18 * log 2 ^ 3 * π ^ 2
      - 7 / 8 * log 2 ^ 2 * zeta3 + 19 / 720 * log 2 * π ^ 4 + 1 / 8 * zeta3 * π ^ 2
      - 153 / 32 * zeta5 := by
  linear_combination (103 / 36) * hpl_zero_zero_zero_zero_one_at_one +
    (-22 / 3) * hpl_zero_zero_zero_one_one_at_one +
    (-283 / 72) * hpl_zero_zero_one_zero_one_at_one +
    (-119 / 72) * hpl_zero_one_zero_zero_one_at_one + (3) * hpl_zero_zero_one_one_one_at_one +
    (2) * hpl_zero_one_zero_one_one_at_one + (2 / 3) * hpl_zero_one_one_zero_one_at_one +
    (-11 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (4) * hpl_negOne_one_one_one_one_at_one +
    (-157 / 240) * rel5_sh_m_mmmm + (29 / 96) * rel5_sh_m_0mmm + (-29 / 288) * rel5_sh_m_m0mm +
    (4 / 3) * rel5_sh_m_m1mm + (11 / 72) * rel5_sh_m_mm0m + (3 / 32) * rel5_sh_m_mm1m +
    (-25 / 32) * rel5_sh_m_mmm1 + (19 / 128) * rel5_st_m_0001 + (85 / 72) * rel5_st_m_000m +
    (14 / 9) * rel5_sh_m_00mm + (-5 / 48) * rel5_sh_m_01mm + (7 / 72) * rel5_sh_m_0m0m +
    (-17 / 48) * rel5_sh_m_0m1m + (-1) * rel5_sh_m_0mm1 + (-5 / 96) * rel5_sh_m_m01m +
    (-1 / 4) * rel5_sh_m_m0m1 + (7 / 96) * rel5_sh_m_m10m + (2) * rel5_sh_m_m11m +
    (53 / 24) * rel5_sh_m_m1m1 + (5 / 48) * rel5_sh_m_mm01 + (53 / 384) * rel5_st_01_00m +
    (233 / 192) * rel5_st_0m_001 + (-73 / 288) * rel5_sh_0m_00m + (-97 / 24) * rel5_st_0m_00m +
    (-1 / 36) * rel5_sh_0m_0mm + (-2 / 3) * rel5_sh_m1_m11 + (-1 / 12) * rel5_sh_m1_mm1 +
    (29 / 24) * rel5_mob_0mmm1 + (-131 / 288) * rel5_sh_m_000m + (-181 / 144) * rel5_sh_m_001m +
    (11 / 8) * rel5_st_m_001m + (-31 / 18) * rel5_sh_m_00m1 + (55 / 48) * rel5_st_m_00m1 +
    (-91 / 96) * rel5_sh_m_010m + (1 / 12) * rel5_sh_m_01m1 + (-1 / 18) * rel5_sh_m_0m01 +
    (29 / 24) * rel5_sh_m_0m11 + (4 / 9) * rel5_sh_m_m001 + (-1 / 192) * rel5_st_m_m001 +
    (-1 / 8) * rel5_st_m_m00m + (17 / 24) * rel5_sh_m_m011 + (29 / 48) * rel5_sh_m_m101 +
    (4) * rel5_sh_m_m111 + (-469 / 1152) * rel5_st_01_01m + (239 / 1152) * rel5_st_01_m0m +
    (173 / 192) * rel5_st_0m_0m1 + (-28 / 9) * rel5_st_0m_0mm + (77 / 192) * rel5_st_0m_m01 +
    (47 / 36) * rel5_sh_m_0001 + (23 / 9) * rel5_sh_m_0011 + (-203 / 144) * rel5_st_m_0011 +
    (-38 / 9) * rel5_st_m_00mm + (13 / 9) * rel5_sh_m_0101 + (55 / 36) * rel5_st_m_010m +
    (-1 / 24) * rel5_st_m_01m1 + (-23 / 9) * rel5_st_m_0m0m + (19 / 36) * rel5_st_m_0m1m +
    (2 / 9) * rel5_st_m_m01m + (21 / 64) * rel5_st_m_m0m1 + (1 / 96) * rel5_st_m_m101 +
    (1 / 4) * rel5_st_m_m10m + (-1 / 24) * rel5_st_m_m1m1 + (19 / 72) * rel5_sh_01_00m +
    (-1 / 2) * rel5_sh_01_01m + (1 / 3) * rel5_sh_01_0m1 + (1 / 4) * rel5_st_01_0m1 +
    (49 / 48) * rel5_st_01_0mm + (-11 / 6) * rel5_sh_01_m11 + (5 / 72) * rel5_sh_0m_001 +
    (35 / 96) * rel5_sh_0m_01m + (5 / 6) * rel5_sh_m1_011 + (7 / 48) * rel5_sh_m1_0m1 +
    (-17 / 48) * rel5_sh_m1_m01 + (-9 / 2) * rel5_mob_00mmm + (5 / 16) * rel5_mob_01mmm +
    (-1) * rel5_mob_0m0mm + (5 / 48) * rel5_mob_0m1mm + (7 / 48) * rel5_mob_m10mm +
    (2 / 9) * rel5_st_m_011m + (1 / 3) * rel5_st_m_01mm + (-17 / 48) * rel5_st_m_0m11 +
    (41 / 48) * rel5_st_m_0mm1 + (7 / 48) * rel5_st_m_m011 + (-5 / 3) * rel5_st_m_m0mm +
    (1 / 18) * rel5_st_m_m11m + (1 / 2) * rel5_st_m_m1mm + (-8 / 9) * rel5_st_m_mm0m +
    (7 / 18) * rel5_st_m_mm1m + (-3) * rel5_st_m_0mmm + (4) * rel5_mob_0000m

theorem hpl_zero_zero_negOne_negOne_negOne_at_one :
    hpl [zero, zero, negOne, negOne, negOne] 1 =
      2 * Li 4 (1 / 2) * log 2 + 2 * Li 5 (1 / 2) + 1 / 15 * log 2 ^ 5
      - 1 / 18 * log 2 ^ 3 * π ^ 2 + 7 / 8 * log 2 ^ 2 * zeta3 - 1 / 12 * zeta3 * π ^ 2
      - 33 / 32 * zeta5 := by
  linear_combination (271 / 576) * hpl_zero_zero_zero_zero_one_at_one +
    (-89 / 24) * hpl_zero_zero_zero_one_one_at_one +
    (-1481 / 576) * hpl_zero_zero_one_zero_one_at_one +
    (-625 / 576) * hpl_zero_one_zero_zero_one_at_one + (1) * hpl_zero_zero_one_one_one_at_one +
    (3 / 4) * hpl_zero_one_zero_one_one_at_one + (1 / 4) * hpl_zero_one_one_zero_one_at_one +
    (-5 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (2) * hpl_negOne_one_one_one_one_at_one +
    (-2369 / 960) * rel5_sh_m_mmmm + (61 / 384) * rel5_sh_m_0mmm + (-61 / 1152) * rel5_sh_m_m0mm +
    (2 / 3) * rel5_sh_m_m1mm + (-59 / 288) * rel5_sh_m_mm0m + (-787 / 384) * rel5_sh_m_mm1m +
    (-365 / 128) * rel5_sh_m_mmm1 + (-85 / 1536) * rel5_st_m_0001 + (149 / 128) * rel5_st_m_000m +
    (59 / 36) * rel5_sh_m_00mm + (33 / 64) * rel5_sh_m_01mm + (-163 / 144) * rel5_sh_m_0m0m +
    (19 / 192) * rel5_sh_m_0m1m + (-1 / 3) * rel5_sh_m_0mm1 + (33 / 128) * rel5_sh_m_m01m +
    (-17 / 96) * rel5_sh_m_m0m1 + (179 / 384) * rel5_sh_m_m10m + (1) * rel5_sh_m_m11m +
    (83 / 48) * rel5_sh_m_m1m1 + (-33 / 64) * rel5_sh_m_mm01 + (581 / 1536) * rel5_st_01_00m +
    (17 / 96) * rel5_st_0m_001 + (-149 / 576) * rel5_sh_0m_00m + (-1883 / 1152) * rel5_st_0m_00m +
    (85 / 72) * rel5_sh_0m_0mm + (-1 / 3) * rel5_sh_m1_m11 + (-3 / 2) * rel5_sh_m1_mm1 +
    (61 / 96) * rel5_mob_0mmm1 + (67 / 72) * rel5_sh_m_000m + (-317 / 288) * rel5_sh_m_001m +
    (473 / 576) * rel5_st_m_001m + (-379 / 288) * rel5_sh_m_00m1 + (27 / 32) * rel5_st_m_00m1 +
    (-59 / 192) * rel5_sh_m_010m + (-23 / 96) * rel5_sh_m_01m1 + (-2 / 9) * rel5_sh_m_0m01 +
    (-1 / 32) * rel5_sh_m_0m11 + (89 / 288) * rel5_sh_m_m001 + (-41 / 768) * rel5_st_m_m001 +
    (-41 / 576) * rel5_st_m_m00m + (-83 / 96) * rel5_sh_m_m011 + (-49 / 192) * rel5_sh_m_m101 +
    (2) * rel5_sh_m_m111 + (-2029 / 4608) * rel5_st_01_01m + (-2857 / 4608) * rel5_st_01_m0m +
    (25 / 48) * rel5_st_0m_0m1 + (-13 / 9) * rel5_st_0m_0mm + (-5 / 16) * rel5_st_0m_m01 +
    (1423 / 1152) * rel5_sh_m_0001 + (47 / 36) * rel5_sh_m_0011 + (-407 / 576) * rel5_st_m_0011 +
    (-163 / 72) * rel5_st_m_00mm + (359 / 288) * rel5_sh_m_0101 + (73 / 72) * rel5_st_m_010m +
    (1 / 32) * rel5_st_m_01m1 + (-7 / 4) * rel5_st_m_0m0m + (25 / 288) * rel5_st_m_0m1m +
    (-11 / 96) * rel5_st_m_m01m + (-1 / 768) * rel5_st_m_m0m1 + (41 / 384) * rel5_st_m_m101 +
    (41 / 288) * rel5_st_m_m10m + (-7 / 48) * rel5_st_m_m1m1 + (5 / 576) * rel5_sh_01_00m +
    (-1 / 6) * rel5_sh_01_01m + (7 / 24) * rel5_sh_01_0m1 + (1 / 8) * rel5_st_01_0m1 +
    (-65 / 64) * rel5_st_01_0mm + (-4 / 3) * rel5_sh_01_m11 + (115 / 576) * rel5_sh_0m_001 +
    (67 / 192) * rel5_sh_0m_01m + (1) * rel5_sh_m1_011 + (17 / 64) * rel5_sh_m1_0m1 +
    (83 / 192) * rel5_sh_m1_m01 + (-11) * rel5_mob_00mmm + (-99 / 64) * rel5_mob_01mmm +
    (-23 / 6) * rel5_mob_0m0mm + (-33 / 64) * rel5_mob_0m1mm + (179 / 192) * rel5_mob_m10mm +
    (53 / 144) * rel5_st_m_011m + (-5 / 24) * rel5_st_m_01mm + (19 / 192) * rel5_st_m_0m11 +
    (13 / 192) * rel5_st_m_0mm1 + (179 / 192) * rel5_st_m_m011 + (-23 / 24) * rel5_st_m_m0mm +
    (7 / 72) * rel5_st_m_m11m + (1 / 4) * rel5_st_m_m1mm + (-89 / 144) * rel5_st_m_mm0m +
    (19 / 72) * rel5_st_m_mm1m + (-1) * rel5_st_m_0mmm + (2) * rel5_mob_0000m

theorem hpl_zero_one_zero_zero_negOne_at_one :
    hpl [zero, one, zero, zero, negOne] 1 =
      1 / 48 * zeta3 * π ^ 2 + 11 / 32 * zeta5 := by
  linear_combination (-2) * hpl_zero_zero_zero_zero_one_at_one +
    (5 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (-3 / 2) * rel5_st_m_0001 +
    (3 / 2) * rel5_st_m_000m + (-1) * rel5_st_0m_001 + (1 / 2) * rel5_sh_0m_00m +
    (1 / 2) * rel5_st_0m_00m + (-3 / 2) * rel5_sh_m_000m + (3 / 2) * rel5_sh_m_0001 +
    (1) * rel5_sh_01_00m + (-1) * rel5_sh_0m_001

theorem hpl_zero_one_zero_one_negOne_at_one :
    hpl [zero, one, zero, one, negOne] 1 =
      4 * Li 4 (1 / 2) * log 2 + 8 * Li 5 (1 / 2) + 1 / 10 * log 2 ^ 5
      - 1 / 18 * log 2 ^ 3 * π ^ 2 + 83 / 1440 * log 2 * π ^ 4 - 7 / 48 * zeta3 * π ^ 2
      - 227 / 32 * zeta5 := by
  linear_combination (289 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 2) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 48) * hpl_zero_one_zero_zero_one_at_one + (4) * hpl_zero_zero_one_one_one_at_one +
    (3) * hpl_zero_one_zero_one_one_at_one + (1) * hpl_zero_one_one_zero_one_at_one +
    (-79 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (8) * hpl_negOne_one_one_one_one_at_one +
    (-869 / 240) * rel5_sh_m_mmmm + (49 / 96) * rel5_sh_m_0mmm + (-49 / 288) * rel5_sh_m_m0mm +
    (8 / 3) * rel5_sh_m_m1mm + (-23 / 72) * rel5_sh_m_mm0m + (-85 / 32) * rel5_sh_m_mm1m +
    (-129 / 32) * rel5_sh_m_mmm1 + (269 / 128) * rel5_st_m_0001 + (169 / 288) * rel5_st_m_000m +
    (13 / 3) * rel5_sh_m_00mm + (47 / 48) * rel5_sh_m_01mm + (-23 / 12) * rel5_sh_m_0m0m +
    (-1 / 48) * rel5_sh_m_0m1m + (-4 / 3) * rel5_sh_m_0mm1 + (47 / 96) * rel5_sh_m_m01m +
    (-13 / 24) * rel5_sh_m_m0m1 + (95 / 96) * rel5_sh_m_m10m + (4) * rel5_sh_m_m11m +
    (21 / 4) * rel5_sh_m_m1m1 + (-47 / 48) * rel5_sh_m_mm01 + (147 / 128) * rel5_st_01_00m +
    (23 / 12) * rel5_st_0m_001 + (-21 / 16) * rel5_sh_0m_00m + (-1903 / 288) * rel5_st_0m_00m +
    (7 / 6) * rel5_sh_0m_0mm + (-4 / 3) * rel5_sh_m1_m11 + (-2) * rel5_sh_m1_mm1 +
    (49 / 24) * rel5_mob_0mmm1 + (15 / 4) * rel5_sh_m_000m + (-71 / 24) * rel5_sh_m_001m +
    (325 / 144) * rel5_st_m_001m + (-85 / 24) * rel5_sh_m_00m1 + (167 / 72) * rel5_st_m_00m1 +
    (-43 / 48) * rel5_sh_m_010m + (-11 / 24) * rel5_sh_m_01m1 + (-1 / 6) * rel5_sh_m_0m01 +
    (17 / 24) * rel5_sh_m_0m11 + (23 / 24) * rel5_sh_m_m001 + (-71 / 576) * rel5_st_m_m001 +
    (-37 / 144) * rel5_st_m_m00m + (-31 / 24) * rel5_sh_m_m011 + (-5 / 48) * rel5_sh_m_m101 +
    (8) * rel5_sh_m_m111 + (-769 / 1152) * rel5_st_01_01m + (-1133 / 1152) * rel5_st_01_m0m +
    (35 / 24) * rel5_st_0m_0m1 + (-13 / 3) * rel5_st_0m_0mm + (-13 / 24) * rel5_st_0m_m01 +
    (27 / 32) * rel5_sh_m_0001 + (3) * rel5_sh_m_0011 + (-113 / 48) * rel5_st_m_0011 +
    (-37 / 6) * rel5_st_m_00mm + (23 / 8) * rel5_sh_m_0101 + (26 / 9) * rel5_st_m_010m +
    (5 / 72) * rel5_st_m_01m1 + (-85 / 18) * rel5_st_m_0m0m + (37 / 72) * rel5_st_m_0m1m +
    (-5 / 72) * rel5_st_m_m01m + (113 / 576) * rel5_st_m_m0m1 + (71 / 288) * rel5_st_m_m101 +
    (37 / 72) * rel5_st_m_m10m + (-1 / 4) * rel5_st_m_m1m1 + (-29 / 48) * rel5_sh_01_00m +
    (-1 / 3) * rel5_sh_01_01m + (5 / 6) * rel5_sh_01_0m1 + (1 / 2) * rel5_st_01_0m1 +
    (-95 / 48) * rel5_st_01_0mm + (-4) * rel5_sh_01_m11 + (53 / 48) * rel5_sh_0m_001 +
    (43 / 48) * rel5_sh_0m_01m + (8 / 3) * rel5_sh_m1_011 + (31 / 48) * rel5_sh_m1_0m1 +
    (31 / 48) * rel5_sh_m1_m01 + (-20) * rel5_mob_00mmm + (-47 / 16) * rel5_mob_01mmm +
    (-6) * rel5_mob_0m0mm + (-47 / 48) * rel5_mob_0m1mm + (95 / 48) * rel5_mob_m10mm +
    (11 / 12) * rel5_st_m_011m + (-1 / 6) * rel5_st_m_01mm + (-1 / 48) * rel5_st_m_0m11 +
    (11 / 16) * rel5_st_m_0mm1 + (95 / 48) * rel5_st_m_m011 + (-19 / 6) * rel5_st_m_m0mm +
    (1 / 6) * rel5_st_m_m11m + (1) * rel5_st_m_m1mm + (-23 / 12) * rel5_st_m_mm0m +
    (5 / 6) * rel5_st_m_mm1m + (-4) * rel5_st_m_0mmm + (8) * rel5_mob_0000m

theorem hpl_zero_one_zero_negOne_one_at_one :
    hpl [zero, one, zero, negOne, one] 1 =
      -4 * Li 5 (1 / 2) + 1 / 30 * log 2 ^ 5 - 1 / 18 * log 2 ^ 3 * π ^ 2
      + 7 / 4 * log 2 ^ 2 * zeta3 - 83 / 1440 * log 2 * π ^ 4 + 1 / 12 * zeta3 * π ^ 2
      + 259 / 64 * zeta5 := by
  linear_combination (-2785 / 576) * hpl_zero_zero_zero_zero_one_at_one +
    (173 / 24) * hpl_zero_zero_zero_one_one_at_one +
    (2459 / 576) * hpl_zero_zero_one_zero_one_at_one +
    (1171 / 576) * hpl_zero_one_zero_zero_one_at_one +
    (-3 / 2) * hpl_zero_zero_one_one_one_at_one + (-5 / 4) * hpl_zero_one_zero_one_one_at_one +
    (-5 / 12) * hpl_zero_one_one_zero_one_at_one +
    (29 / 4) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (5893 / 960) * rel5_sh_m_mmmm + (-233 / 384) * rel5_sh_m_0mmm + (233 / 1152) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (235 / 288) * rel5_sh_m_mm0m + (725 / 128) * rel5_sh_m_mm1m +
    (865 / 128) * rel5_sh_m_mmm1 + (-929 / 512) * rel5_st_m_0001 + (965 / 1152) * rel5_st_m_000m +
    (-125 / 36) * rel5_sh_m_00mm + (-391 / 192) * rel5_sh_m_01mm + (395 / 72) * rel5_sh_m_0m0m +
    (-79 / 192) * rel5_sh_m_0m1m + (1 / 2) * rel5_sh_m_0mm1 + (-391 / 384) * rel5_sh_m_m01m +
    (9 / 32) * rel5_sh_m_m0m1 + (-703 / 384) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-49 / 12) * rel5_sh_m_m1m1 + (391 / 192) * rel5_sh_m_mm01 + (-3665 / 1536) * rel5_st_01_00m +
    (365 / 384) * rel5_st_0m_001 + (337 / 288) * rel5_sh_0m_00m + (1535 / 384) * rel5_st_0m_00m +
    (-26 / 9) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (95 / 24) * rel5_sh_m1_mm1 +
    (-233 / 96) * rel5_mob_0mmm1 + (-4451 / 576) * rel5_sh_m_000m + (283 / 144) * rel5_sh_m_001m +
    (-241 / 192) * rel5_st_m_001m + (733 / 288) * rel5_sh_m_00m1 + (-4 / 3) * rel5_st_m_00m1 +
    (-131 / 96) * rel5_sh_m_010m + (37 / 96) * rel5_sh_m_01m1 + (43 / 72) * rel5_sh_m_0m01 +
    (55 / 96) * rel5_sh_m_0m11 + (-143 / 288) * rel5_sh_m_m001 + (181 / 768) * rel5_st_m_m001 +
    (25 / 192) * rel5_st_m_m00m + (367 / 96) * rel5_sh_m_m011 + (313 / 192) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (1897 / 4608) * rel5_st_01_01m + (14581 / 4608) * rel5_st_01_m0m +
    (-283 / 384) * rel5_st_0m_0m1 + (97 / 36) * rel5_st_0m_0mm + (965 / 384) * rel5_st_0m_m01 +
    (815 / 1152) * rel5_sh_m_0001 + (-107 / 36) * rel5_sh_m_0011 + (-109 / 576) * rel5_st_m_0011 +
    (325 / 72) * rel5_st_m_00mm + (-773 / 288) * rel5_sh_m_0101 + (-137 / 72) * rel5_st_m_010m +
    (1 / 96) * rel5_st_m_01m1 + (217 / 72) * rel5_st_m_0m0m + (-35 / 288) * rel5_st_m_0m1m +
    (191 / 288) * rel5_st_m_m01m + (95 / 256) * rel5_st_m_m0m1 + (-181 / 384) * rel5_st_m_m101 +
    (-25 / 96) * rel5_st_m_m10m + (5 / 12) * rel5_st_m_m1m1 + (1273 / 576) * rel5_sh_01_00m +
    (3 / 4) * rel5_sh_01_01m + (-11 / 24) * rel5_sh_01_0m1 + (1 / 4) * rel5_st_01_0m1 +
    (1583 / 192) * rel5_st_01_0mm + (25 / 12) * rel5_sh_01_m11 + (-1537 / 576) * rel5_sh_0m_001 +
    (-89 / 96) * rel5_sh_0m_01m + (-19 / 12) * rel5_sh_m1_011 + (-127 / 192) * rel5_sh_m1_0m1 +
    (-367 / 192) * rel5_sh_m1_m01 + (111 / 4) * rel5_mob_00mmm + (391 / 64) * rel5_mob_01mmm +
    (9) * rel5_mob_0m0mm + (391 / 192) * rel5_mob_0m1mm + (-703 / 192) * rel5_mob_m10mm +
    (-83 / 144) * rel5_st_m_011m + (7 / 24) * rel5_st_m_01mm + (-79 / 192) * rel5_st_m_0m11 +
    (31 / 192) * rel5_st_m_0mm1 + (-703 / 192) * rel5_st_m_m011 + (37 / 24) * rel5_st_m_m0mm +
    (-7 / 72) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm + (143 / 144) * rel5_st_m_mm0m +
    (-31 / 72) * rel5_st_m_mm1m + (3 / 2) * rel5_st_m_0mmm + (-4) * rel5_mob_0000m

theorem hpl_zero_one_zero_negOne_negOne_at_one :
    hpl [zero, one, zero, negOne, negOne] 1 =
      -4 * Li 4 (1 / 2) * log 2 - 4 * Li 5 (1 / 2) - 2 / 15 * log 2 ^ 5
      + 1 / 9 * log 2 ^ 3 * π ^ 2 - 7 / 4 * log 2 ^ 2 * zeta3 + 7 / 96 * zeta3 * π ^ 2
      + 103 / 32 * zeta5 := by
  linear_combination (-433 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (21 / 4) * hpl_zero_zero_zero_one_one_at_one + (335 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 96) * hpl_zero_one_zero_zero_one_at_one + (-2) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 2) * hpl_zero_one_zero_one_one_at_one + (-1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (47 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (869 / 480) * rel5_sh_m_mmmm + (-49 / 192) * rel5_sh_m_0mmm + (49 / 576) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (23 / 144) * rel5_sh_m_mm0m + (85 / 64) * rel5_sh_m_mm1m +
    (129 / 64) * rel5_sh_m_mmm1 + (-525 / 256) * rel5_st_m_0001 + (263 / 576) * rel5_st_m_000m +
    (-13 / 6) * rel5_sh_m_00mm + (-47 / 96) * rel5_sh_m_01mm + (35 / 24) * rel5_sh_m_0m0m +
    (1 / 96) * rel5_sh_m_0m1m + (2 / 3) * rel5_sh_m_0mm1 + (-47 / 192) * rel5_sh_m_m01m +
    (13 / 48) * rel5_sh_m_m0m1 + (-95 / 192) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-21 / 8) * rel5_sh_m_m1m1 + (47 / 96) * rel5_sh_m_mm01 + (-211 / 256) * rel5_st_01_00m +
    (-23 / 24) * rel5_st_0m_001 + (29 / 32) * rel5_sh_0m_00m + (2335 / 576) * rel5_st_0m_00m +
    (-7 / 12) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (1) * rel5_sh_m1_mm1 +
    (-49 / 48) * rel5_mob_0mmm1 + (-25 / 8) * rel5_sh_m_000m + (71 / 48) * rel5_sh_m_001m +
    (-325 / 288) * rel5_st_m_001m + (85 / 48) * rel5_sh_m_00m1 + (-167 / 144) * rel5_st_m_00m1 +
    (43 / 96) * rel5_sh_m_010m + (11 / 48) * rel5_sh_m_01m1 + (1 / 12) * rel5_sh_m_0m01 +
    (-17 / 48) * rel5_sh_m_0m11 + (-23 / 48) * rel5_sh_m_m001 + (71 / 1152) * rel5_st_m_m001 +
    (37 / 288) * rel5_st_m_m00m + (31 / 48) * rel5_sh_m_m011 + (5 / 96) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (1345 / 2304) * rel5_st_01_01m + (1709 / 2304) * rel5_st_01_m0m +
    (-35 / 48) * rel5_st_0m_0m1 + (13 / 6) * rel5_st_0m_0mm + (13 / 48) * rel5_st_0m_m01 +
    (21 / 64) * rel5_sh_m_0001 + (-3 / 2) * rel5_sh_m_0011 + (113 / 96) * rel5_st_m_0011 +
    (37 / 12) * rel5_st_m_00mm + (-23 / 16) * rel5_sh_m_0101 + (-13 / 9) * rel5_st_m_010m +
    (-5 / 144) * rel5_st_m_01m1 + (85 / 36) * rel5_st_m_0m0m + (-37 / 144) * rel5_st_m_0m1m +
    (5 / 144) * rel5_st_m_m01m + (-113 / 1152) * rel5_st_m_m0m1 + (-71 / 576) * rel5_st_m_m101 +
    (-37 / 144) * rel5_st_m_m10m + (1 / 8) * rel5_st_m_m1m1 + (29 / 96) * rel5_sh_01_00m +
    (1 / 6) * rel5_sh_01_01m + (-5 / 12) * rel5_sh_01_0m1 + (-1 / 4) * rel5_st_01_0m1 +
    (191 / 96) * rel5_st_01_0mm + (2) * rel5_sh_01_m11 + (-53 / 96) * rel5_sh_0m_001 +
    (-43 / 96) * rel5_sh_0m_01m + (-4 / 3) * rel5_sh_m1_011 + (-31 / 96) * rel5_sh_m1_0m1 +
    (-31 / 96) * rel5_sh_m1_m01 + (10) * rel5_mob_00mmm + (47 / 32) * rel5_mob_01mmm +
    (3) * rel5_mob_0m0mm + (47 / 96) * rel5_mob_0m1mm + (-95 / 96) * rel5_mob_m10mm +
    (-11 / 24) * rel5_st_m_011m + (1 / 12) * rel5_st_m_01mm + (1 / 96) * rel5_st_m_0m11 +
    (-11 / 32) * rel5_st_m_0mm1 + (-95 / 96) * rel5_st_m_m011 + (19 / 12) * rel5_st_m_m0mm +
    (-1 / 12) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm + (23 / 24) * rel5_st_m_mm0m +
    (-5 / 12) * rel5_st_m_mm1m + (2) * rel5_st_m_0mmm + (-4) * rel5_mob_0000m

theorem hpl_zero_one_one_zero_negOne_at_one :
    hpl [zero, one, one, zero, negOne] 1 =
      -1 / 32 * zeta3 * π ^ 2 + 53 / 64 * zeta5 := by
  linear_combination (-53 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-13 / 4) * hpl_zero_zero_zero_one_one_at_one +
    (-119 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (-43 / 48) * hpl_zero_one_zero_zero_one_at_one +
    (-5 / 4) * hpl_zero_zero_zero_zero_negOne_at_one + (-75 / 16) * rel5_sh_m_mmmm +
    (3 / 32) * rel5_sh_m_0mmm + (-1 / 32) * rel5_sh_m_m0mm + (-3 / 8) * rel5_sh_m_mm0m +
    (-133 / 32) * rel5_sh_m_mm1m + (-177 / 32) * rel5_sh_m_mmm1 + (-31 / 128) * rel5_st_m_0001 +
    (113 / 96) * rel5_st_m_000m + (5 / 3) * rel5_sh_m_00mm + (13 / 16) * rel5_sh_m_01mm +
    (-29 / 24) * rel5_sh_m_0m0m + (5 / 16) * rel5_sh_m_0m1m + (13 / 32) * rel5_sh_m_m01m +
    (-1 / 8) * rel5_sh_m_m0m1 + (21 / 32) * rel5_sh_m_m10m + (5 / 4) * rel5_sh_m_m1m1 +
    (-13 / 16) * rel5_sh_m_mm01 + (83 / 128) * rel5_st_01_00m + (27 / 32) * rel5_st_0m_001 +
    (-1 / 6) * rel5_sh_0m_00m + (-7 / 96) * rel5_st_0m_00m + (13 / 6) * rel5_sh_0m_0mm +
    (-3) * rel5_sh_m1_mm1 + (3 / 8) * rel5_mob_0mmm1 + (53 / 48) * rel5_sh_m_000m +
    (-13 / 12) * rel5_sh_m_001m + (37 / 48) * rel5_st_m_001m + (-31 / 24) * rel5_sh_m_00m1 +
    (19 / 24) * rel5_st_m_00m1 + (-1 / 4) * rel5_sh_m_010m + (-3 / 8) * rel5_sh_m_01m1 +
    (-13 / 24) * rel5_sh_m_0m01 + (-5 / 8) * rel5_sh_m_0m11 + (5 / 24) * rel5_sh_m_m001 +
    (-13 / 192) * rel5_st_m_m001 + (-1 / 48) * rel5_st_m_m00m + (-13 / 8) * rel5_sh_m_m011 +
    (-11 / 16) * rel5_sh_m_m101 + (-57 / 128) * rel5_st_01_01m + (-287 / 384) * rel5_st_01_m0m +
    (15 / 32) * rel5_st_0m_0m1 + (-13 / 12) * rel5_st_0m_0mm + (-17 / 32) * rel5_st_0m_m01 +
    (115 / 96) * rel5_sh_m_0001 + (5 / 3) * rel5_sh_m_0011 + (-17 / 48) * rel5_st_m_0011 +
    (-13 / 6) * rel5_st_m_00mm + (19 / 12) * rel5_sh_m_0101 + (7 / 8) * rel5_st_m_010m +
    (1 / 24) * rel5_st_m_01m1 + (-41 / 24) * rel5_st_m_0m0m + (-1 / 8) * rel5_st_m_0m1m +
    (-7 / 24) * rel5_st_m_m01m + (-29 / 192) * rel5_st_m_m0m1 + (13 / 96) * rel5_st_m_m101 +
    (1 / 24) * rel5_st_m_m10m + (-1 / 4) * rel5_st_m_m1m1 + (-61 / 48) * rel5_sh_01_00m +
    (-1 / 4) * rel5_sh_01_01m + (1 / 4) * rel5_sh_01_0m1 + (-9 / 16) * rel5_st_01_0mm +
    (-1) * rel5_sh_01_m11 + (73 / 48) * rel5_sh_0m_001 + (1) * rel5_st_0m_011 +
    (3 / 8) * rel5_sh_0m_01m + (1) * rel5_sh_m1_011 + (5 / 16) * rel5_sh_m1_0m1 +
    (13 / 16) * rel5_sh_m1_m01 + (-18) * rel5_mob_00mmm + (-39 / 16) * rel5_mob_01mmm +
    (-7) * rel5_mob_0m0mm + (-13 / 16) * rel5_mob_0m1mm + (21 / 16) * rel5_mob_m10mm +
    (5 / 12) * rel5_st_m_011m + (-1 / 2) * rel5_st_m_01mm + (5 / 16) * rel5_st_m_0m11 +
    (-5 / 16) * rel5_st_m_0mm1 + (21 / 16) * rel5_st_m_m011 + (-1 / 2) * rel5_st_m_m0mm +
    (1 / 6) * rel5_st_m_m11m + (-5 / 12) * rel5_st_m_mm0m + (1 / 6) * rel5_st_m_mm1m

theorem hpl_zero_one_one_one_negOne_at_one :
    hpl [zero, one, one, one, negOne] 1 =
      -Li 4 (1 / 2) * log 2 - 2 * Li 5 (1 / 2) - 1 / 40 * log 2 ^ 5
      + 1 / 18 * log 2 ^ 3 * π ^ 2 - 1 / 720 * log 2 * π ^ 4 + 7 / 48 * zeta3 * π ^ 2
      - 1 / 32 * zeta5 := by
  linear_combination (-131 / 64) * hpl_zero_zero_zero_zero_one_at_one +
    (29 / 8) * hpl_zero_zero_zero_one_one_at_one + (141 / 64) * hpl_zero_zero_one_zero_one_at_one +
    (175 / 192) * hpl_zero_one_zero_zero_one_at_one + (-1) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 4) * hpl_zero_one_zero_one_one_at_one + (-7 / 12) * hpl_zero_one_one_zero_one_at_one +
    (7 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (-2) * hpl_negOne_one_one_one_one_at_one +
    (703 / 320) * rel5_sh_m_mmmm + (-35 / 128) * rel5_sh_m_0mmm + (35 / 384) * rel5_sh_m_m0mm +
    (-2 / 3) * rel5_sh_m_m1mm + (7 / 32) * rel5_sh_m_mm0m + (237 / 128) * rel5_sh_m_mm1m +
    (313 / 128) * rel5_sh_m_mmm1 + (-1135 / 1536) * rel5_st_m_0001 + (37 / 384) * rel5_st_m_000m +
    (-13 / 12) * rel5_sh_m_00mm + (-119 / 192) * rel5_sh_m_01mm + (33 / 16) * rel5_sh_m_0m0m +
    (-7 / 192) * rel5_sh_m_0m1m + (1 / 3) * rel5_sh_m_0mm1 + (-119 / 384) * rel5_sh_m_m01m +
    (7 / 32) * rel5_sh_m_m0m1 + (-77 / 128) * rel5_sh_m_m10m + (-1) * rel5_sh_m_m11m +
    (-83 / 48) * rel5_sh_m_m1m1 + (119 / 192) * rel5_sh_m_mm01 + (-1457 / 1536) * rel5_st_01_00m +
    (3 / 16) * rel5_st_0m_001 + (79 / 192) * rel5_sh_0m_00m + (749 / 384) * rel5_st_0m_00m +
    (-9 / 8) * rel5_sh_0m_0mm + (1 / 3) * rel5_sh_m1_m11 + (4 / 3) * rel5_sh_m1_mm1 +
    (-35 / 32) * rel5_mob_0mmm1 + (-131 / 48) * rel5_sh_m_000m + (79 / 96) * rel5_sh_m_001m +
    (-37 / 64) * rel5_st_m_001m + (109 / 96) * rel5_sh_m_00m1 + (-163 / 288) * rel5_st_m_00m1 +
    (-77 / 192) * rel5_sh_m_010m + (1 / 32) * rel5_sh_m_01m1 + (5 / 24) * rel5_sh_m_0m01 +
    (-3 / 32) * rel5_sh_m_0m11 + (-31 / 96) * rel5_sh_m_m001 + (175 / 2304) * rel5_st_m_m001 +
    (5 / 64) * rel5_st_m_m00m + (103 / 96) * rel5_sh_m_m011 + (61 / 192) * rel5_sh_m_m101 +
    (-2) * rel5_sh_m_m111 + (761 / 4608) * rel5_st_01_01m + (5125 / 4608) * rel5_st_01_m0m +
    (-35 / 96) * rel5_st_0m_0m1 + (17 / 12) * rel5_st_0m_0mm + (77 / 96) * rel5_st_0m_m01 +
    (7 / 384) * rel5_sh_m_0001 + (-17 / 12) * rel5_sh_m_0011 + (-23 / 192) * rel5_st_m_0011 +
    (53 / 24) * rel5_st_m_00mm + (-109 / 96) * rel5_sh_m_0101 + (-5 / 6) * rel5_st_m_010m +
    (1) * rel5_sh_m_0111 + (11 / 288) * rel5_st_m_01m1 + (13 / 8) * rel5_st_m_0m0m +
    (-5 / 32) * rel5_st_m_0m1m + (5 / 32) * rel5_st_m_m01m + (23 / 2304) * rel5_st_m_m0m1 +
    (-175 / 1152) * rel5_st_m_m101 + (-5 / 32) * rel5_st_m_m10m + (7 / 48) * rel5_st_m_m1m1 +
    (55 / 64) * rel5_sh_01_00m + (5 / 12) * rel5_sh_01_01m + (-5 / 24) * rel5_sh_01_0m1 +
    (-1 / 8) * rel5_st_01_0m1 + (551 / 192) * rel5_st_01_0mm + (4 / 3) * rel5_sh_01_m11 +
    (-63 / 64) * rel5_sh_0m_001 + (-83 / 192) * rel5_sh_0m_01m + (-4 / 3) * rel5_sh_m1_011 +
    (-13 / 64) * rel5_sh_m1_0m1 + (-103 / 192) * rel5_sh_m1_m01 + (10) * rel5_mob_00mmm +
    (119 / 64) * rel5_mob_01mmm + (19 / 6) * rel5_mob_0m0mm + (119 / 192) * rel5_mob_0m1mm +
    (-77 / 64) * rel5_mob_m10mm + (-1 / 16) * rel5_st_m_011m + (1 / 24) * rel5_st_m_01mm +
    (-7 / 192) * rel5_st_m_0m11 + (-25 / 192) * rel5_st_m_0mm1 + (-77 / 64) * rel5_st_m_m011 +
    (19 / 24) * rel5_st_m_m0mm + (-1 / 24) * rel5_st_m_m11m + (-1 / 4) * rel5_st_m_m1mm +
    (31 / 48) * rel5_st_m_mm0m + (-5 / 24) * rel5_st_m_mm1m + (1) * rel5_st_m_0mmm +
    (-2) * rel5_mob_0000m

theorem hpl_zero_one_one_negOne_one_at_one :
    hpl [zero, one, one, negOne, one] 1 =
      4 * Li 5 (1 / 2) - 1 / 30 * log 2 ^ 5 - 5 / 72 * log 2 ^ 3 * π ^ 2
      - 7 / 16 * log 2 ^ 2 * zeta3 + 53 / 1440 * log 2 * π ^ 4 - 35 / 96 * zeta3 * π ^ 2
      + 29 / 64 * zeta5 := by
  linear_combination (593 / 144) * hpl_zero_zero_zero_zero_one_at_one +
    (-217 / 24) * hpl_zero_zero_zero_one_one_at_one +
    (-407 / 72) * hpl_zero_zero_one_zero_one_at_one +
    (-43 / 18) * hpl_zero_one_zero_zero_one_at_one + (2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 2) * hpl_zero_one_zero_one_one_at_one + (1) * hpl_zero_one_one_zero_one_at_one +
    (-79 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (4) * hpl_negOne_one_one_one_one_at_one +
    (-721 / 120) * rel5_sh_m_mmmm + (47 / 48) * rel5_sh_m_0mmm + (-47 / 144) * rel5_sh_m_m0mm +
    (4 / 3) * rel5_sh_m_m1mm + (-11 / 18) * rel5_sh_m_mm0m + (-235 / 48) * rel5_sh_m_mm1m +
    (-109 / 16) * rel5_sh_m_mmm1 + (31 / 32) * rel5_st_m_0001 + (167 / 288) * rel5_st_m_000m +
    (59 / 18) * rel5_sh_m_00mm + (37 / 24) * rel5_sh_m_01mm + (-557 / 144) * rel5_sh_m_0m0m +
    (11 / 24) * rel5_sh_m_0m1m + (-2 / 3) * rel5_sh_m_0mm1 + (37 / 48) * rel5_sh_m_m01m +
    (-13 / 24) * rel5_sh_m_m0m1 + (67 / 48) * rel5_sh_m_m10m + (2) * rel5_sh_m_m11m +
    (31 / 8) * rel5_sh_m_m1m1 + (-37 / 24) * rel5_sh_m_mm01 + (119 / 64) * rel5_st_01_00m +
    (-47 / 192) * rel5_st_0m_001 + (-239 / 288) * rel5_sh_0m_00m + (-451 / 96) * rel5_st_0m_00m +
    (47 / 18) * rel5_sh_0m_0mm + (-2 / 3) * rel5_sh_m1_m11 + (-43 / 12) * rel5_sh_m1_mm1 +
    (47 / 12) * rel5_mob_0mmm1 + (1403 / 288) * rel5_sh_m_000m + (-329 / 144) * rel5_sh_m_001m +
    (85 / 48) * rel5_st_m_001m + (-209 / 72) * rel5_sh_m_00m1 + (241 / 144) * rel5_st_m_00m1 +
    (9 / 32) * rel5_sh_m_010m + (-5 / 24) * rel5_sh_m_01m1 + (-103 / 144) * rel5_sh_m_0m01 +
    (-5 / 12) * rel5_sh_m_0m11 + (43 / 72) * rel5_sh_m_m001 + (-49 / 288) * rel5_st_m_m001 +
    (-7 / 48) * rel5_st_m_m00m + (-35 / 12) * rel5_sh_m_m011 + (-13 / 12) * rel5_sh_m_m101 +
    (4) * rel5_sh_m_m111 + (-131 / 192) * rel5_st_01_01m + (-1265 / 576) * rel5_st_01_m0m +
    (185 / 192) * rel5_st_0m_0m1 + (-247 / 72) * rel5_st_0m_0mm + (-295 / 192) * rel5_st_0m_m01 +
    (209 / 288) * rel5_sh_m_0001 + (34 / 9) * rel5_sh_m_0011 + (-35 / 72) * rel5_st_m_0011 +
    (-101 / 18) * rel5_st_m_00mm + (443 / 144) * rel5_sh_m_0101 + (323 / 144) * rel5_st_m_010m +
    (-1 / 18) * rel5_st_m_01m1 + (-559 / 144) * rel5_st_m_0m0m + (19 / 72) * rel5_st_m_0m1m +
    (-7 / 18) * rel5_st_m_m01m + (-53 / 288) * rel5_st_m_m0m1 + (49 / 144) * rel5_st_m_m101 +
    (7 / 24) * rel5_st_m_m10m + (-3 / 8) * rel5_st_m_m1m1 + (-97 / 72) * rel5_sh_01_00m +
    (-19 / 24) * rel5_sh_01_01m + (13 / 24) * rel5_sh_01_0m1 + (-21 / 4) * rel5_st_01_0mm +
    (-5 / 2) * rel5_sh_01_m11 + (17 / 9) * rel5_sh_0m_001 + (91 / 96) * rel5_sh_0m_01m +
    (11 / 6) * rel5_sh_m1_011 + (17 / 24) * rel5_sh_m1_0m1 + (35 / 24) * rel5_sh_m1_m01 +
    (-51 / 2) * rel5_mob_00mmm + (-37 / 8) * rel5_mob_01mmm + (-25 / 3) * rel5_mob_0m0mm +
    (-15 / 8) * rel5_mob_0m1mm + (67 / 24) * rel5_mob_m10mm + (7 / 36) * rel5_st_m_011m +
    (-1 / 3) * rel5_st_m_01mm + (7 / 24) * rel5_st_m_0m11 + (-1 / 8) * rel5_st_m_0mm1 +
    (67 / 24) * rel5_st_m_m011 + (-11 / 6) * rel5_st_m_m0mm + (1 / 9) * rel5_st_m_m11m +
    (1 / 2) * rel5_st_m_m1mm + (-43 / 36) * rel5_st_m_mm0m + (4 / 9) * rel5_st_m_mm1m +
    (-2) * rel5_st_m_0mmm + (4) * rel5_mob_0000m

theorem hpl_zero_one_one_negOne_negOne_at_one :
    hpl [zero, one, one, negOne, negOne] 1 =
      3 * Li 4 (1 / 2) * log 2 + 4 * Li 5 (1 / 2) + 11 / 120 * log 2 ^ 5
      + 1 / 72 * log 2 ^ 3 * π ^ 2 + 7 / 16 * log 2 ^ 2 * zeta3 + 17 / 1440 * log 2 * π ^ 4
      + 1 / 32 * zeta3 * π ^ 2 - 277 / 64 * zeta5 := by
  linear_combination (169 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 4) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 96) * hpl_zero_one_zero_zero_one_at_one + (2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 2) * hpl_zero_one_zero_one_one_at_one + (1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (-73 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (4) * hpl_negOne_one_one_one_one_at_one +
    (-809 / 480) * rel5_sh_m_mmmm + (37 / 192) * rel5_sh_m_0mmm + (-37 / 576) * rel5_sh_m_m0mm +
    (4 / 3) * rel5_sh_m_m1mm + (-35 / 144) * rel5_sh_m_mm0m + (-89 / 64) * rel5_sh_m_mm1m +
    (-117 / 64) * rel5_sh_m_mmm1 + (177 / 256) * rel5_st_m_0001 + (565 / 576) * rel5_st_m_000m +
    (13 / 6) * rel5_sh_m_00mm + (59 / 96) * rel5_sh_m_01mm + (-23 / 24) * rel5_sh_m_0m0m +
    (11 / 96) * rel5_sh_m_0m1m + (-2 / 3) * rel5_sh_m_0mm1 + (59 / 192) * rel5_sh_m_m01m +
    (-13 / 48) * rel5_sh_m_m0m1 + (107 / 192) * rel5_sh_m_m10m + (2) * rel5_sh_m_m11m +
    (21 / 8) * rel5_sh_m_m1m1 + (-59 / 96) * rel5_sh_m_mm01 + (175 / 256) * rel5_st_01_00m +
    (17 / 24) * rel5_st_0m_001 + (-17 / 32) * rel5_sh_0m_00m + (-1579 / 576) * rel5_st_0m_00m +
    (7 / 12) * rel5_sh_0m_0mm + (-2 / 3) * rel5_sh_m1_m11 + (-1) * rel5_sh_m1_mm1 +
    (37 / 48) * rel5_mob_0mmm1 + (13 / 8) * rel5_sh_m_000m + (-83 / 48) * rel5_sh_m_001m +
    (325 / 288) * rel5_st_m_001m + (-85 / 48) * rel5_sh_m_00m1 + (179 / 144) * rel5_st_m_00m1 +
    (-55 / 96) * rel5_sh_m_010m + (1 / 2) * rel5_sh_m_011m + (-11 / 48) * rel5_sh_m_01m1 +
    (-1 / 12) * rel5_sh_m_0m01 + (-19 / 48) * rel5_sh_m_0m11 + (23 / 48) * rel5_sh_m_m001 +
    (-83 / 1152) * rel5_st_m_m001 + (-37 / 288) * rel5_st_m_m00m + (-67 / 48) * rel5_sh_m_m011 +
    (-41 / 96) * rel5_sh_m_m101 + (4) * rel5_sh_m_m111 + (-1333 / 2304) * rel5_st_01_01m +
    (-1361 / 2304) * rel5_st_01_m0m + (35 / 48) * rel5_st_0m_0m1 + (-13 / 6) * rel5_st_0m_0mm +
    (-13 / 48) * rel5_st_0m_m01 + (71 / 64) * rel5_sh_m_0001 + (3 / 2) * rel5_sh_m_0011 +
    (-101 / 96) * rel5_st_m_0011 + (-37 / 12) * rel5_st_m_00mm + (23 / 16) * rel5_sh_m_0101 +
    (13 / 9) * rel5_st_m_010m + (-19 / 144) * rel5_st_m_01m1 + (-85 / 36) * rel5_st_m_0m0m +
    (37 / 144) * rel5_st_m_0m1m + (-5 / 144) * rel5_st_m_m01m + (-91 / 1152) * rel5_st_m_m0m1 +
    (83 / 576) * rel5_st_m_m101 + (37 / 144) * rel5_st_m_m10m + (-1 / 8) * rel5_st_m_m1m1 +
    (-17 / 96) * rel5_sh_01_00m + (-1 / 6) * rel5_sh_01_01m + (5 / 12) * rel5_sh_01_0m1 +
    (1 / 4) * rel5_st_01_0m1 + (-107 / 96) * rel5_st_01_0mm + (-2) * rel5_sh_01_m11 +
    (41 / 96) * rel5_sh_0m_001 + (55 / 96) * rel5_sh_0m_01m + (4 / 3) * rel5_sh_m1_011 +
    (67 / 96) * rel5_sh_m1_0m1 + (67 / 96) * rel5_sh_m1_m01 + (-10) * rel5_mob_00mmm +
    (-59 / 32) * rel5_mob_01mmm + (-3) * rel5_mob_0m0mm + (-59 / 96) * rel5_mob_0m1mm +
    (107 / 96) * rel5_mob_m10mm + (11 / 24) * rel5_st_m_011m + (-1 / 12) * rel5_st_m_01mm +
    (11 / 96) * rel5_st_m_0m11 + (7 / 32) * rel5_st_m_0mm1 + (107 / 96) * rel5_st_m_m011 +
    (-19 / 12) * rel5_st_m_m0mm + (1 / 12) * rel5_st_m_m11m + (1 / 2) * rel5_st_m_m1mm +
    (-23 / 24) * rel5_st_m_mm0m + (5 / 12) * rel5_st_m_mm1m + (-2) * rel5_st_m_0mmm +
    (4) * rel5_mob_0000m

theorem hpl_zero_one_negOne_zero_one_at_one :
    hpl [zero, one, negOne, zero, one] 1 =
      1 / 96 * log 2 * π ^ 4 - 13 / 24 * zeta3 * π ^ 2 + 363 / 64 * zeta5 := by
  linear_combination (91 / 192) * hpl_zero_zero_zero_zero_one_at_one +
    (-47 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (-833 / 192) * hpl_zero_zero_one_zero_one_at_one +
    (-265 / 192) * hpl_zero_one_zero_zero_one_at_one +
    (-3 / 2) * hpl_zero_zero_one_one_one_at_one + (-3 / 4) * hpl_zero_one_zero_one_one_at_one +
    (-1 / 4) * hpl_zero_one_one_zero_one_at_one +
    (-3 / 4) * hpl_zero_zero_zero_zero_negOne_at_one + (-351 / 64) * rel5_sh_m_mmmm +
    (39 / 128) * rel5_sh_m_0mmm + (-13 / 128) * rel5_sh_m_m0mm + (-31 / 32) * rel5_sh_m_mm0m +
    (-737 / 128) * rel5_sh_m_mm1m + (-765 / 128) * rel5_sh_m_mmm1 + (-75 / 512) * rel5_st_m_0001 +
    (521 / 384) * rel5_st_m_000m + (47 / 12) * rel5_sh_m_00mm + (137 / 64) * rel5_sh_m_01mm +
    (-37 / 12) * rel5_sh_m_0m0m + (49 / 64) * rel5_sh_m_0m1m + (1 / 2) * rel5_sh_m_0mm1 +
    (137 / 128) * rel5_sh_m_m01m + (-1 / 32) * rel5_sh_m_m0m1 + (225 / 128) * rel5_sh_m_m10m +
    (15 / 8) * rel5_sh_m_m1m1 + (-137 / 64) * rel5_sh_m_mm01 + (895 / 512) * rel5_st_01_00m +
    (-109 / 128) * rel5_st_0m_001 + (-13 / 24) * rel5_sh_0m_00m + (-703 / 384) * rel5_st_0m_00m +
    (23 / 12) * rel5_sh_0m_0mm + (-31 / 8) * rel5_sh_m1_mm1 + (39 / 32) * rel5_mob_0mmm1 +
    (779 / 192) * rel5_sh_m_000m + (-47 / 24) * rel5_sh_m_001m + (265 / 192) * rel5_st_m_001m +
    (-223 / 96) * rel5_sh_m_00m1 + (23 / 16) * rel5_st_m_00m1 + (3 / 16) * rel5_sh_m_010m +
    (-15 / 32) * rel5_sh_m_01m1 + (-37 / 24) * rel5_sh_m_0m01 + (-57 / 32) * rel5_sh_m_0m11 +
    (5 / 96) * rel5_sh_m_m001 + (-59 / 256) * rel5_st_m_m001 + (-1 / 192) * rel5_st_m_m00m +
    (-145 / 32) * rel5_sh_m_m011 + (-143 / 64) * rel5_sh_m_m101 + (-1159 / 1536) * rel5_st_01_01m +
    (-3259 / 1536) * rel5_st_01_m0m + (115 / 128) * rel5_st_0m_0m1 + (-19 / 12) * rel5_st_0m_0mm +
    (-237 / 128) * rel5_st_0m_m01 + (523 / 384) * rel5_sh_m_0001 + (53 / 12) * rel5_sh_m_0011 +
    (-77 / 192) * rel5_st_m_0011 + (-103 / 24) * rel5_st_m_00mm + (359 / 96) * rel5_sh_m_0101 +
    (11 / 8) * rel5_st_m_010m + (1 / 32) * rel5_st_m_01m1 + (-71 / 24) * rel5_st_m_0m0m +
    (-13 / 32) * rel5_st_m_0m1m + (-85 / 96) * rel5_st_m_m01m + (-179 / 256) * rel5_st_m_m0m1 +
    (59 / 128) * rel5_st_m_m101 + (1 / 96) * rel5_st_m_m10m + (-3 / 8) * rel5_st_m_m1m1 +
    (-235 / 192) * rel5_sh_01_00m + (-3 / 4) * rel5_sh_01_01m + (1 / 8) * rel5_sh_01_0m1 +
    (-1 / 2) * rel5_st_01_0m1 + (-337 / 64) * rel5_st_01_0mm + (-1 / 4) * rel5_sh_01_m11 +
    (355 / 192) * rel5_sh_0m_001 + (11 / 16) * rel5_sh_0m_01m + (3 / 4) * rel5_sh_m1_011 +
    (33 / 64) * rel5_sh_m1_0m1 + (145 / 64) * rel5_sh_m1_m01 + (-93 / 4) * rel5_mob_00mmm +
    (-411 / 64) * rel5_mob_01mmm + (-8) * rel5_mob_0m0mm + (-137 / 64) * rel5_mob_0m1mm +
    (225 / 64) * rel5_mob_m10mm + (17 / 48) * rel5_st_m_011m + (-5 / 8) * rel5_st_m_01mm +
    (49 / 64) * rel5_st_m_0m11 + (-65 / 64) * rel5_st_m_0mm1 + (225 / 64) * rel5_st_m_m011 +
    (1 / 8) * rel5_st_m_m0mm + (1 / 24) * rel5_st_m_m11m + (-5 / 48) * rel5_st_m_mm0m +
    (1 / 24) * rel5_st_m_mm1m + (3 / 2) * rel5_st_m_0mmm

theorem hpl_zero_one_negOne_zero_negOne_at_one :
    hpl [zero, one, negOne, zero, negOne] 1 =
      8 * Li 4 (1 / 2) * log 2 + 16 * Li 5 (1 / 2) + 1 / 5 * log 2 ^ 5
      - 1 / 9 * log 2 ^ 3 * π ^ 2 + 17 / 180 * log 2 * π ^ 4 - 1 / 24 * zeta3 * π ^ 2
      - 507 / 32 * zeta5 := by
  linear_combination (193 / 24) * hpl_zero_zero_zero_zero_one_at_one +
    (-21) * hpl_zero_zero_zero_one_one_at_one + (-335 / 24) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 24) * hpl_zero_one_zero_zero_one_at_one + (8) * hpl_zero_zero_one_one_one_at_one +
    (6) * hpl_zero_one_zero_one_one_at_one + (2) * hpl_zero_one_one_zero_one_at_one +
    (-143 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (16) * hpl_negOne_one_one_one_one_at_one +
    (-869 / 120) * rel5_sh_m_mmmm + (49 / 48) * rel5_sh_m_0mmm + (-49 / 144) * rel5_sh_m_m0mm +
    (16 / 3) * rel5_sh_m_m1mm + (-23 / 36) * rel5_sh_m_mm0m + (-85 / 16) * rel5_sh_m_mm1m +
    (-129 / 16) * rel5_sh_m_mmm1 + (173 / 64) * rel5_st_m_0001 + (529 / 144) * rel5_st_m_000m +
    (26 / 3) * rel5_sh_m_00mm + (47 / 24) * rel5_sh_m_01mm + (-23 / 6) * rel5_sh_m_0m0m +
    (-1 / 24) * rel5_sh_m_0m1m + (-8 / 3) * rel5_sh_m_0mm1 + (47 / 48) * rel5_sh_m_m01m +
    (-13 / 12) * rel5_sh_m_m0m1 + (95 / 48) * rel5_sh_m_m10m + (8) * rel5_sh_m_m11m +
    (21 / 2) * rel5_sh_m_m1m1 + (-47 / 24) * rel5_sh_m_mm01 + (147 / 64) * rel5_st_01_00m +
    (17 / 6) * rel5_st_0m_001 + (-17 / 8) * rel5_sh_0m_00m + (-1687 / 144) * rel5_st_0m_00m +
    (7 / 3) * rel5_sh_0m_0mm + (-8 / 3) * rel5_sh_m1_m11 + (-4) * rel5_sh_m1_mm1 +
    (49 / 12) * rel5_mob_0mmm1 + (6) * rel5_sh_m_000m + (-71 / 12) * rel5_sh_m_001m +
    (325 / 72) * rel5_st_m_001m + (-85 / 12) * rel5_sh_m_00m1 + (167 / 36) * rel5_st_m_00m1 +
    (-43 / 24) * rel5_sh_m_010m + (-11 / 12) * rel5_sh_m_01m1 + (-1 / 3) * rel5_sh_m_0m01 +
    (17 / 12) * rel5_sh_m_0m11 + (23 / 12) * rel5_sh_m_m001 + (-71 / 288) * rel5_st_m_m001 +
    (-37 / 72) * rel5_st_m_m00m + (-31 / 12) * rel5_sh_m_m011 + (-5 / 24) * rel5_sh_m_m101 +
    (16) * rel5_sh_m_m111 + (-1345 / 576) * rel5_st_01_01m + (-1133 / 576) * rel5_st_01_m0m +
    (35 / 12) * rel5_st_0m_0m1 + (-26 / 3) * rel5_st_0m_0mm + (-13 / 12) * rel5_st_0m_m01 +
    (67 / 16) * rel5_sh_m_0001 + (6) * rel5_sh_m_0011 + (-113 / 24) * rel5_st_m_0011 +
    (-37 / 3) * rel5_st_m_00mm + (23 / 4) * rel5_sh_m_0101 + (52 / 9) * rel5_st_m_010m +
    (5 / 36) * rel5_st_m_01m1 + (-85 / 9) * rel5_st_m_0m0m + (37 / 36) * rel5_st_m_0m1m +
    (-5 / 36) * rel5_st_m_m01m + (113 / 288) * rel5_st_m_m0m1 + (71 / 144) * rel5_st_m_m101 +
    (37 / 36) * rel5_st_m_m10m + (-1 / 2) * rel5_st_m_m1m1 + (-5 / 24) * rel5_sh_01_00m +
    (-2 / 3) * rel5_sh_01_01m + (5 / 3) * rel5_sh_01_0m1 + (1) * rel5_st_01_0m1 +
    (-95 / 24) * rel5_st_01_0mm + (-8) * rel5_sh_01_m11 + (29 / 24) * rel5_sh_0m_001 +
    (43 / 24) * rel5_sh_0m_01m + (16 / 3) * rel5_sh_m1_011 + (31 / 24) * rel5_sh_m1_0m1 +
    (31 / 24) * rel5_sh_m1_m01 + (-40) * rel5_mob_00mmm + (-47 / 8) * rel5_mob_01mmm +
    (-12) * rel5_mob_0m0mm + (-47 / 24) * rel5_mob_0m1mm + (95 / 24) * rel5_mob_m10mm +
    (11 / 6) * rel5_st_m_011m + (-1 / 3) * rel5_st_m_01mm + (-1 / 24) * rel5_st_m_0m11 +
    (11 / 8) * rel5_st_m_0mm1 + (95 / 24) * rel5_st_m_m011 + (-19 / 3) * rel5_st_m_m0mm +
    (1 / 3) * rel5_st_m_m11m + (2) * rel5_st_m_m1mm + (-23 / 6) * rel5_st_m_mm0m +
    (5 / 3) * rel5_st_m_mm1m + (-8) * rel5_st_m_0mmm + (16) * rel5_mob_0000m

theorem hpl_zero_one_negOne_one_one_at_one :
    hpl [zero, one, negOne, one, one] 1 =
      -6 * Li 5 (1 / 2) + 1 / 20 * log 2 ^ 5 + 1 / 24 * log 2 ^ 3 * π ^ 2
      - 19 / 480 * log 2 * π ^ 4 + 7 / 16 * zeta3 * π ^ 2 + 29 / 64 * zeta5 := by
  linear_combination (-125 / 36) * hpl_zero_zero_zero_zero_one_at_one +
    (107 / 12) * hpl_zero_zero_zero_one_one_at_one +
    (853 / 144) * hpl_zero_zero_one_zero_one_at_one +
    (365 / 144) * hpl_zero_one_zero_zero_one_at_one + (-3 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-1) * hpl_zero_one_zero_one_one_at_one + (-1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (449 / 60) * hpl_zero_zero_zero_zero_negOne_at_one + (-6) * hpl_negOne_one_one_one_one_at_one +
    (1819 / 480) * rel5_sh_m_mmmm + (-59 / 192) * rel5_sh_m_0mmm + (59 / 576) * rel5_sh_m_m0mm +
    (-2) * rel5_sh_m_m1mm + (211 / 144) * rel5_sh_m_mm0m + (817 / 192) * rel5_sh_m_mm1m +
    (255 / 64) * rel5_sh_m_mmm1 + (-803 / 3840) * rel5_st_m_0001 + (-43 / 36) * rel5_st_m_000m +
    (-37 / 9) * rel5_sh_m_00mm + (-79 / 32) * rel5_sh_m_01mm + (353 / 144) * rel5_sh_m_0m0m +
    (-73 / 96) * rel5_sh_m_0m1m + (1 / 2) * rel5_sh_m_0mm1 + (-47 / 64) * rel5_sh_m_m01m +
    (11 / 24) * rel5_sh_m_m0m1 + (-289 / 192) * rel5_sh_m_m10m + (-3) * rel5_sh_m_m11m +
    (-215 / 48) * rel5_sh_m_m1m1 + (79 / 32) * rel5_sh_m_mm01 + (-5183 / 3840) * rel5_st_01_00m +
    (29 / 384) * rel5_st_0m_001 + (379 / 576) * rel5_sh_0m_00m + (14 / 3) * rel5_st_0m_00m +
    (-137 / 72) * rel5_sh_0m_0mm + (1) * rel5_sh_m1_m11 + (67 / 24) * rel5_sh_m1_mm1 +
    (-59 / 48) * rel5_mob_0mmm1 + (-1831 / 576) * rel5_sh_m_000m + (679 / 288) * rel5_sh_m_001m +
    (-97 / 48) * rel5_st_m_001m + (109 / 36) * rel5_sh_m_00m1 + (-279 / 160) * rel5_st_m_00m1 +
    (43 / 64) * rel5_sh_m_010m + (11 / 24) * rel5_sh_m_01m1 + (65 / 72) * rel5_sh_m_0m01 +
    (23 / 16) * rel5_sh_m_0m11 + (-17 / 36) * rel5_sh_m_m001 + (129 / 640) * rel5_st_m_m001 +
    (7 / 48) * rel5_st_m_m00m + (169 / 48) * rel5_sh_m_m011 + (133 / 96) * rel5_sh_m_m101 +
    (-6) * rel5_sh_m_m111 + (10271 / 11520) * rel5_st_01_01m + (18419 / 11520) * rel5_st_01_m0m +
    (-117 / 128) * rel5_st_0m_0m1 + (119 / 36) * rel5_st_0m_0mm + (449 / 384) * rel5_st_0m_m01 +
    (-193 / 144) * rel5_sh_m_0001 + (-71 / 18) * rel5_sh_m_0011 + (317 / 288) * rel5_st_m_0011 +
    (101 / 18) * rel5_st_m_00mm + (-241 / 72) * rel5_sh_m_0101 + (-43 / 18) * rel5_st_m_010m +
    (-13 / 240) * rel5_st_m_01m1 + (281 / 72) * rel5_st_m_0m0m + (-7 / 72) * rel5_st_m_0m1m +
    (7 / 18) * rel5_st_m_m01m + (659 / 1920) * rel5_st_m_m0m1 + (-129 / 320) * rel5_st_m_m101 +
    (-7 / 24) * rel5_st_m_m10m + (71 / 240) * rel5_st_m_m1m1 + (95 / 144) * rel5_sh_01_00m +
    (7 / 12) * rel5_sh_01_01m + (-7 / 12) * rel5_sh_01_0m1 + (1 / 8) * rel5_st_01_0m1 +
    (337 / 96) * rel5_st_01_0mm + (25 / 12) * rel5_sh_01_m11 + (-191 / 144) * rel5_sh_0m_001 +
    (-59 / 64) * rel5_sh_0m_01m + (-19 / 12) * rel5_sh_m1_011 + (-35 / 32) * rel5_sh_m1_0m1 +
    (-145 / 96) * rel5_sh_m1_m01 + (95 / 4) * rel5_mob_00mmm + (237 / 32) * rel5_mob_01mmm +
    (15 / 2) * rel5_mob_0m0mm + (205 / 96) * rel5_mob_0m1mm + (-289 / 96) * rel5_mob_m10mm +
    (-4 / 9) * rel5_st_m_011m + (2 / 3) * rel5_st_m_01mm + (-89 / 96) * rel5_st_m_0m11 +
    (49 / 96) * rel5_st_m_0mm1 + (-289 / 96) * rel5_st_m_m011 + (5 / 3) * rel5_st_m_m0mm +
    (-7 / 36) * rel5_st_m_m11m + (-3 / 4) * rel5_st_m_m1mm + (17 / 18) * rel5_st_m_mm0m +
    (-25 / 36) * rel5_st_m_mm1m + (3 / 2) * rel5_st_m_0mmm + (1) * rel5_mob_001mm +
    (-6) * rel5_mob_0000m

theorem hpl_zero_one_negOne_one_negOne_at_one :
    hpl [zero, one, negOne, one, negOne] 1 =
      -3 * Li 4 (1 / 2) * log 2 - 1 / 8 * log 2 ^ 5 - 1 / 24 * log 2 ^ 3 * π ^ 2
      + 7 / 480 * log 2 * π ^ 4 - 1 / 16 * zeta3 * π ^ 2 + zeta5 := by
  linear_combination (1) * hpl_zero_zero_zero_zero_one_at_one + (1 / 2) * rel5_sh_m_mmmm +
    (-1 / 4) * rel5_sh_m_0mmm + (1 / 12) * rel5_sh_m_m0mm + (-1 / 3) * rel5_sh_m_mm0m +
    (-1 / 4) * rel5_sh_m_mm1m + (3 / 4) * rel5_sh_m_mmm1 + (1 / 16) * rel5_st_m_0001 +
    (-3 / 4) * rel5_st_m_000m + (1 / 2) * rel5_sh_m_01mm + (1 / 2) * rel5_sh_m_0m1m +
    (1 / 4) * rel5_sh_m_m01m + (1 / 4) * rel5_sh_m_m10m + (-1 / 2) * rel5_sh_m_mm01 +
    (3 / 16) * rel5_st_01_00m + (-1 / 4) * rel5_st_0m_001 + (-1 / 4) * rel5_st_0m_00m +
    (-1) * rel5_mob_0mmm1 + (1 / 2) * rel5_sh_m_000m + (-1 / 6) * rel5_st_m_00m1 +
    (-1) * rel5_sh_m_0m11 + (-1 / 24) * rel5_st_m_m001 + (-1) * rel5_sh_m_m011 +
    (-1 / 2) * rel5_sh_m_m101 + (13 / 48) * rel5_st_01_01m + (-7 / 48) * rel5_st_01_m0m +
    (-1 / 4) * rel5_st_0m_0m1 + (-1 / 4) * rel5_st_0m_m01 + (-3 / 4) * rel5_sh_m_0001 +
    (1 / 2) * rel5_st_m_0011 + (1 / 3) * rel5_st_m_01m1 + (-5 / 24) * rel5_st_m_m0m1 +
    (1 / 12) * rel5_st_m_m101 + (-1 / 2) * rel5_sh_01_00m + (-1 / 2) * rel5_st_01_0mm +
    (1 / 2) * rel5_sh_0m_001 + (1 / 2) * rel5_sh_m1_0m1 + (1 / 2) * rel5_sh_m1_m01 +
    (-3 / 2) * rel5_mob_01mmm + (-1 / 2) * rel5_mob_0m1mm + (1 / 2) * rel5_mob_m10mm +
    (1 / 2) * rel5_st_m_0m11 + (-1 / 2) * rel5_st_m_0mm1 + (1 / 2) * rel5_st_m_m011

theorem hpl_zero_one_negOne_negOne_one_at_one :
    hpl [zero, one, negOne, negOne, one] 1 =
      -4 * Li 5 (1 / 2) + 1 / 30 * log 2 ^ 5 - 1 / 18 * log 2 ^ 3 * π ^ 2
      + 21 / 16 * log 2 ^ 2 * zeta3 - 53 / 1440 * log 2 * π ^ 4 - 7 / 32 * zeta3 * π ^ 2
      + 405 / 64 * zeta5 := by
  linear_combination (-1537 / 576) * hpl_zero_zero_zero_zero_one_at_one +
    (10 / 3) * hpl_zero_zero_zero_one_one_at_one +
    (935 / 576) * hpl_zero_zero_one_zero_one_at_one +
    (535 / 576) * hpl_zero_one_zero_zero_one_at_one + (-5 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-7 / 4) * hpl_zero_one_zero_one_one_at_one + (-7 / 12) * hpl_zero_one_one_zero_one_at_one +
    (65 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (1493 / 960) * rel5_sh_m_mmmm + (-217 / 384) * rel5_sh_m_0mmm + (217 / 1152) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (11 / 288) * rel5_sh_m_mm0m + (239 / 384) * rel5_sh_m_mm1m +
    (241 / 128) * rel5_sh_m_mmm1 + (-401 / 512) * rel5_st_m_0001 + (71 / 384) * rel5_st_m_000m +
    (-35 / 36) * rel5_sh_m_00mm + (-23 / 192) * rel5_sh_m_01mm + (103 / 144) * rel5_sh_m_0m0m +
    (-31 / 192) * rel5_sh_m_0m1m + (5 / 6) * rel5_sh_m_0mm1 + (-23 / 384) * rel5_sh_m_m01m +
    (9 / 32) * rel5_sh_m_m0m1 + (-47 / 384) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-29 / 12) * rel5_sh_m_m1m1 + (23 / 192) * rel5_sh_m_mm01 + (-145 / 1536) * rel5_st_01_00m +
    (-69 / 128) * rel5_st_0m_001 + (127 / 288) * rel5_sh_0m_00m + (2861 / 1152) * rel5_st_0m_00m +
    (-29 / 36) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (5 / 8) * rel5_sh_m1_mm1 +
    (-217 / 96) * rel5_mob_0mmm1 + (-659 / 576) * rel5_sh_m_000m + (115 / 144) * rel5_sh_m_001m +
    (-347 / 576) * rel5_st_m_001m + (253 / 288) * rel5_sh_m_00m1 + (-7 / 12) * rel5_st_m_00m1 +
    (5 / 32) * rel5_sh_m_010m + (29 / 96) * rel5_sh_m_01m1 + (-61 / 144) * rel5_sh_m_0m01 +
    (-25 / 96) * rel5_sh_m_0m11 + (-95 / 288) * rel5_sh_m_m001 + (5 / 768) * rel5_st_m_m001 +
    (59 / 576) * rel5_st_m_m00m + (-1 / 96) * rel5_sh_m_m011 + (-23 / 192) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (745 / 4608) * rel5_st_01_01m + (1429 / 4608) * rel5_st_01_m0m +
    (-79 / 384) * rel5_st_0m_0m1 + (119 / 72) * rel5_st_0m_0mm + (17 / 384) * rel5_st_0m_m01 +
    (95 / 1152) * rel5_sh_m_0001 + (-11 / 36) * rel5_sh_m_0011 + (419 / 576) * rel5_st_m_0011 +
    (121 / 72) * rel5_st_m_00mm + (-59 / 288) * rel5_sh_m_0101 + (-119 / 144) * rel5_st_m_010m +
    (-7 / 96) * rel5_st_m_01m1 + (49 / 48) * rel5_st_m_0m0m + (-91 / 288) * rel5_st_m_0m1m +
    (-5 / 32) * rel5_st_m_m01m + (-83 / 768) * rel5_st_m_m0m1 + (-5 / 384) * rel5_st_m_m101 +
    (-59 / 288) * rel5_st_m_m10m + (1 / 12) * rel5_st_m_m1m1 + (-35 / 576) * rel5_sh_01_00m +
    (-1 / 24) * rel5_sh_01_01m + (-1 / 4) * rel5_sh_01_0m1 + (-1 / 4) * rel5_st_01_0m1 +
    (71 / 192) * rel5_st_01_0mm + (17 / 12) * rel5_sh_01_m11 + (-13 / 576) * rel5_sh_0m_001 +
    (-7 / 32) * rel5_sh_0m_01m + (-7 / 12) * rel5_sh_m1_011 + (-95 / 192) * rel5_sh_m1_0m1 +
    (1 / 192) * rel5_sh_m1_m01 + (31 / 4) * rel5_mob_00mmm + (23 / 64) * rel5_mob_01mmm +
    (7 / 3) * rel5_mob_0m0mm + (29 / 64) * rel5_mob_0m1mm + (-47 / 192) * rel5_mob_m10mm +
    (-11 / 144) * rel5_st_m_011m + (-3 / 8) * rel5_st_m_01mm + (1 / 192) * rel5_st_m_0m11 +
    (-49 / 192) * rel5_st_m_0mm1 + (-47 / 192) * rel5_st_m_m011 + (11 / 8) * rel5_st_m_m0mm +
    (-7 / 72) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm + (95 / 144) * rel5_st_m_mm0m +
    (-31 / 72) * rel5_st_m_mm1m + (5 / 2) * rel5_st_m_0mmm + (-4) * rel5_mob_0000m

theorem hpl_zero_one_negOne_negOne_negOne_at_one :
    hpl [zero, one, negOne, negOne, negOne] 1 =
      Li 4 (1 / 2) * log 2 + 4 * Li 5 (1 / 2) + 1 / 120 * log 2 ^ 5
      + 1 / 18 * log 2 ^ 3 * π ^ 2 - 21 / 16 * log 2 ^ 2 * zeta3 + 17 / 480 * log 2 * π ^ 4
      + 7 / 96 * zeta3 * π ^ 2 - 39 / 8 * zeta5 := by
  linear_combination (37 / 36) * hpl_zero_zero_zero_zero_one_at_one +
    (-113 / 24) * hpl_zero_zero_zero_one_one_at_one +
    (-443 / 144) * hpl_zero_zero_one_zero_one_at_one +
    (-205 / 144) * hpl_zero_one_zero_zero_one_at_one + (2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 2) * hpl_zero_one_zero_one_one_at_one + (1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (-16 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (4) * hpl_negOne_one_one_one_one_at_one +
    (-427 / 240) * rel5_sh_m_mmmm + (35 / 96) * rel5_sh_m_0mmm + (-35 / 288) * rel5_sh_m_m0mm +
    (4 / 3) * rel5_sh_m_m1mm + (-7 / 72) * rel5_sh_m_mm0m + (-113 / 96) * rel5_sh_m_mm1m +
    (-63 / 32) * rel5_sh_m_mmm1 + (95 / 384) * rel5_st_m_0001 + (11 / 9) * rel5_st_m_000m +
    (37 / 18) * rel5_sh_m_00mm + (37 / 48) * rel5_sh_m_01mm + (-97 / 144) * rel5_sh_m_0m0m +
    (1 / 48) * rel5_sh_m_0m1m + (-2 / 3) * rel5_sh_m_0mm1 + (7 / 32) * rel5_sh_m_m01m +
    (-1 / 4) * rel5_sh_m_m0m1 + (49 / 96) * rel5_sh_m_m10m + (2) * rel5_sh_m_m11m +
    (21 / 8) * rel5_sh_m_m1m1 + (-7 / 16) * rel5_sh_m_mm01 + (167 / 384) * rel5_st_01_00m +
    (125 / 192) * rel5_st_0m_001 + (-109 / 288) * rel5_sh_0m_00m + (-9 / 4) * rel5_st_0m_00m +
    (5 / 9) * rel5_sh_0m_0mm + (-2 / 3) * rel5_sh_m1_m11 + (-11 / 12) * rel5_sh_m1_mm1 +
    (35 / 24) * rel5_mob_0mmm1 + (247 / 288) * rel5_sh_m_000m + (-199 / 144) * rel5_sh_m_001m +
    (1) * rel5_st_m_001m + (-14 / 9) * rel5_sh_m_00m1 + (155 / 144) * rel5_st_m_00m1 +
    (-21 / 32) * rel5_sh_m_010m + (-1 / 6) * rel5_sh_m_01m1 + (1 / 144) * rel5_sh_m_0m01 +
    (1 / 8) * rel5_sh_m_0m11 + (4 / 9) * rel5_sh_m_m001 + (-37 / 576) * rel5_st_m_m001 +
    (-1 / 8) * rel5_st_m_m00m + (-17 / 24) * rel5_sh_m_m011 + (-5 / 48) * rel5_sh_m_m101 +
    (4) * rel5_sh_m_m111 + (-63 / 128) * rel5_st_01_01m + (-419 / 1152) * rel5_st_01_m0m +
    (125 / 192) * rel5_st_0m_0m1 + (-143 / 72) * rel5_st_0m_0mm + (-35 / 192) * rel5_st_0m_m01 +
    (97 / 72) * rel5_sh_m_0001 + (11 / 9) * rel5_sh_m_0011 + (-149 / 144) * rel5_st_m_0011 +
    (-49 / 18) * rel5_st_m_00mm + (169 / 144) * rel5_sh_m_0101 + (187 / 144) * rel5_st_m_010m +
    (1 / 72) * rel5_st_m_01m1 + (-299 / 144) * rel5_st_m_0m0m + (5 / 18) * rel5_st_m_0m1m +
    (1 / 72) * rel5_st_m_m01m + (43 / 576) * rel5_st_m_m0m1 + (37 / 288) * rel5_st_m_m101 +
    (1 / 4) * rel5_st_m_m10m + (-1 / 8) * rel5_st_m_m1m1 + (-1 / 144) * rel5_sh_01_00m +
    (-1 / 8) * rel5_sh_01_01m + (3 / 8) * rel5_sh_01_0m1 + (1 / 4) * rel5_st_01_0m1 +
    (-23 / 48) * rel5_st_01_0mm + (-11 / 6) * rel5_sh_01_m11 + (31 / 144) * rel5_sh_0m_001 +
    (37 / 96) * rel5_sh_0m_01m + (7 / 6) * rel5_sh_m1_011 + (7 / 16) * rel5_sh_m1_0m1 +
    (17 / 48) * rel5_sh_m1_m01 + (-19 / 2) * rel5_mob_00mmm + (-21 / 16) * rel5_mob_01mmm +
    (-8 / 3) * rel5_mob_0m0mm + (-7 / 16) * rel5_mob_0m1mm + (49 / 48) * rel5_mob_m10mm +
    (7 / 18) * rel5_st_m_011m + (3 / 16) * rel5_st_m_0m11 + (5 / 16) * rel5_st_m_0mm1 +
    (49 / 48) * rel5_st_m_m011 + (-3 / 2) * rel5_st_m_m0mm + (1 / 18) * rel5_st_m_m11m +
    (1 / 2) * rel5_st_m_m1mm + (-8 / 9) * rel5_st_m_mm0m + (7 / 18) * rel5_st_m_mm1m +
    (-2) * rel5_st_m_0mmm + (4) * rel5_mob_0000m

end QED.Polylog.HPL
