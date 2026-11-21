/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLAlt5Rel

/-!
# Harmonic polylogarithms at `1`: alternating words of weight five (B)

The values `H(w; 1)` of the 18 words `w` of weight five over `{0, 1, -1}`
starting with `0, -1` and with no trailing zero (excluding those known in closed form in
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

theorem hpl_zero_negOne_zero_zero_one_at_one :
    hpl [zero, negOne, zero, zero, one] 1 =
      -7 / 16 * zeta3 * π ^ 2 + 83 / 16 * zeta5 := by
  linear_combination (-197 / 96) * hpl_zero_zero_zero_zero_one_at_one +
    (-11 / 4) * hpl_zero_zero_zero_one_one_at_one +
    (-305 / 96) * hpl_zero_zero_one_zero_one_at_one +
    (-121 / 96) * hpl_zero_one_zero_zero_one_at_one + (-3) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 2) * hpl_zero_one_zero_one_one_at_one + (-1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (1) * hpl_zero_zero_zero_zero_negOne_at_one + (-111 / 32) * rel5_sh_m_mmmm +
    (-9 / 64) * rel5_sh_m_0mmm + (3 / 64) * rel5_sh_m_m0mm + (-15 / 16) * rel5_sh_m_mm0m +
    (-273 / 64) * rel5_sh_m_mm1m + (-237 / 64) * rel5_sh_m_mmm1 + (-315 / 256) * rel5_st_m_0001 +
    (425 / 192) * rel5_st_m_000m + (11 / 6) * rel5_sh_m_00mm + (57 / 32) * rel5_sh_m_01mm +
    (-5 / 3) * rel5_sh_m_0m0m + (33 / 32) * rel5_sh_m_0m1m + (1) * rel5_sh_m_0mm1 +
    (57 / 64) * rel5_sh_m_m01m + (-1 / 16) * rel5_sh_m_m0m1 + (81 / 64) * rel5_sh_m_m10m +
    (5 / 4) * rel5_sh_m_m1m1 + (-57 / 32) * rel5_sh_m_mm01 + (335 / 256) * rel5_st_01_00m +
    (-69 / 64) * rel5_st_0m_001 + (1 / 6) * rel5_sh_0m_00m + (-31 / 192) * rel5_st_0m_00m +
    (11 / 6) * rel5_sh_0m_0mm + (-11 / 4) * rel5_sh_m1_mm1 + (-9 / 16) * rel5_mob_0mmm1 +
    (131 / 96) * rel5_sh_m_000m + (-17 / 12) * rel5_sh_m_001m + (73 / 96) * rel5_st_m_001m +
    (-79 / 48) * rel5_sh_m_00m1 + (19 / 24) * rel5_st_m_00m1 + (-3 / 8) * rel5_sh_m_010m +
    (-15 / 16) * rel5_sh_m_01m1 + (-19 / 12) * rel5_sh_m_0m01 + (-41 / 16) * rel5_sh_m_0m11 +
    (5 / 48) * rel5_sh_m_m001 + (-65 / 384) * rel5_st_m_m001 + (-1 / 96) * rel5_st_m_m00m +
    (-65 / 16) * rel5_sh_m_m011 + (-63 / 32) * rel5_sh_m_m101 + (-407 / 768) * rel5_st_01_01m +
    (-345 / 256) * rel5_st_01_m0m + (27 / 64) * rel5_st_0m_0m1 + (-1 / 6) * rel5_st_0m_0mm +
    (-69 / 64) * rel5_st_0m_m01 + (427 / 192) * rel5_sh_m_0001 + (17 / 6) * rel5_sh_m_0011 +
    (67 / 96) * rel5_st_m_0011 + (-31 / 12) * rel5_st_m_00mm + (143 / 48) * rel5_sh_m_0101 +
    (5 / 4) * rel5_st_m_010m + (11 / 48) * rel5_st_m_01m1 + (-29 / 12) * rel5_st_m_0m0m +
    (-13 / 16) * rel5_st_m_0m1m + (-37 / 48) * rel5_st_m_m01m + (-265 / 384) * rel5_st_m_m0m1 +
    (65 / 192) * rel5_st_m_m101 + (1 / 48) * rel5_st_m_m10m + (-1 / 4) * rel5_st_m_m1m1 +
    (-91 / 96) * rel5_sh_01_00m + (-1 / 2) * rel5_sh_01_01m + (1 / 4) * rel5_sh_01_0m1 +
    (-97 / 32) * rel5_st_01_0mm + (-1 / 2) * rel5_sh_01_m11 + (115 / 96) * rel5_sh_0m_001 +
    (5 / 8) * rel5_sh_0m_01m + (3 / 2) * rel5_sh_m1_011 + (17 / 32) * rel5_sh_m1_0m1 +
    (65 / 32) * rel5_sh_m1_m01 + (-33 / 2) * rel5_mob_00mmm + (-171 / 32) * rel5_mob_01mmm +
    (-6) * rel5_mob_0m0mm + (-57 / 32) * rel5_mob_0m1mm + (81 / 32) * rel5_mob_m10mm +
    (17 / 24) * rel5_st_m_011m + (-5 / 4) * rel5_st_m_01mm + (33 / 32) * rel5_st_m_0m11 +
    (-49 / 32) * rel5_st_m_0mm1 + (81 / 32) * rel5_st_m_m011 + (1 / 4) * rel5_st_m_m0mm +
    (1 / 12) * rel5_st_m_m11m + (-5 / 24) * rel5_st_m_mm0m + (1 / 12) * rel5_st_m_mm1m +
    (3) * rel5_st_m_0mmm

theorem hpl_zero_negOne_zero_zero_negOne_at_one :
    hpl [zero, negOne, zero, zero, negOne] 1 =
      -1 / 8 * zeta3 * π ^ 2 + 51 / 32 * zeta5 := by
  linear_combination (3) * hpl_zero_zero_zero_zero_one_at_one +
    (-3 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (3 / 2) * rel5_st_m_0001 +
    (-3 / 2) * rel5_st_m_000m + (-1 / 2) * rel5_sh_0m_00m + (-3 / 2) * rel5_st_0m_00m +
    (3 / 2) * rel5_sh_m_000m + (-3 / 2) * rel5_sh_m_0001

theorem hpl_zero_negOne_zero_one_one_at_one :
    hpl [zero, negOne, zero, one, one] 1 =
      11 / 96 * zeta3 * π ^ 2 - 41 / 32 * zeta5 := by
  linear_combination (485 / 192) * hpl_zero_zero_zero_zero_one_at_one +
    (15 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (353 / 192) * hpl_zero_zero_one_zero_one_at_one +
    (169 / 192) * hpl_zero_one_zero_zero_one_at_one + (3 / 2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 4) * hpl_zero_one_zero_one_one_at_one + (1 / 4) * hpl_zero_one_one_zero_one_at_one +
    (-3 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (111 / 64) * rel5_sh_m_mmmm +
    (9 / 128) * rel5_sh_m_0mmm + (-3 / 128) * rel5_sh_m_m0mm + (15 / 32) * rel5_sh_m_mm0m +
    (273 / 128) * rel5_sh_m_mm1m + (237 / 128) * rel5_sh_m_mmm1 + (699 / 512) * rel5_st_m_0001 +
    (-809 / 384) * rel5_st_m_000m + (-11 / 12) * rel5_sh_m_00mm + (-57 / 64) * rel5_sh_m_01mm +
    (7 / 12) * rel5_sh_m_0m0m + (-33 / 64) * rel5_sh_m_0m1m + (-1 / 2) * rel5_sh_m_0mm1 +
    (-57 / 128) * rel5_sh_m_m01m + (1 / 32) * rel5_sh_m_m0m1 + (-81 / 128) * rel5_sh_m_m10m +
    (-5 / 8) * rel5_sh_m_m1m1 + (57 / 64) * rel5_sh_m_mm01 + (-271 / 512) * rel5_st_01_00m +
    (85 / 128) * rel5_st_0m_001 + (-1 / 3) * rel5_sh_0m_00m + (-161 / 384) * rel5_st_0m_00m +
    (-11 / 12) * rel5_sh_0m_0mm + (11 / 8) * rel5_sh_m1_mm1 + (9 / 32) * rel5_mob_0mmm1 +
    (61 / 192) * rel5_sh_m_000m + (17 / 24) * rel5_sh_m_001m + (-73 / 192) * rel5_st_m_001m +
    (79 / 96) * rel5_sh_m_00m1 + (-19 / 48) * rel5_st_m_00m1 + (7 / 16) * rel5_sh_m_010m +
    (15 / 32) * rel5_sh_m_01m1 + (25 / 24) * rel5_sh_m_0m01 + (41 / 32) * rel5_sh_m_0m11 +
    (-5 / 96) * rel5_sh_m_m001 + (65 / 768) * rel5_st_m_m001 + (1 / 192) * rel5_st_m_m00m +
    (65 / 32) * rel5_sh_m_m011 + (63 / 64) * rel5_sh_m_m101 + (599 / 1536) * rel5_st_01_01m +
    (281 / 512) * rel5_st_01_m0m + (-43 / 128) * rel5_st_0m_0m1 + (7 / 12) * rel5_st_0m_0mm +
    (53 / 128) * rel5_st_0m_m01 + (-811 / 384) * rel5_sh_m_0001 + (-17 / 12) * rel5_sh_m_0011 +
    (-67 / 192) * rel5_st_m_0011 + (31 / 24) * rel5_st_m_00mm + (-167 / 96) * rel5_sh_m_0101 +
    (-7 / 8) * rel5_st_m_010m + (-11 / 96) * rel5_st_m_01m1 + (35 / 24) * rel5_st_m_0m0m +
    (13 / 32) * rel5_st_m_0m1m + (37 / 96) * rel5_st_m_m01m + (265 / 768) * rel5_st_m_m0m1 +
    (-65 / 384) * rel5_st_m_m101 + (-1 / 96) * rel5_st_m_m10m + (1 / 8) * rel5_st_m_m1m1 +
    (43 / 192) * rel5_sh_01_00m + (1 / 4) * rel5_sh_01_01m + (-1 / 8) * rel5_sh_01_0m1 +
    (65 / 64) * rel5_st_01_0mm + (1 / 4) * rel5_sh_01_m11 + (-67 / 192) * rel5_sh_0m_001 +
    (-5 / 16) * rel5_sh_0m_01m + (-3 / 4) * rel5_sh_m1_011 + (-17 / 64) * rel5_sh_m1_0m1 +
    (-65 / 64) * rel5_sh_m1_m01 + (33 / 4) * rel5_mob_00mmm + (171 / 64) * rel5_mob_01mmm +
    (3) * rel5_mob_0m0mm + (57 / 64) * rel5_mob_0m1mm + (-81 / 64) * rel5_mob_m10mm +
    (-17 / 48) * rel5_st_m_011m + (5 / 8) * rel5_st_m_01mm + (-33 / 64) * rel5_st_m_0m11 +
    (49 / 64) * rel5_st_m_0mm1 + (-81 / 64) * rel5_st_m_m011 + (-1 / 8) * rel5_st_m_m0mm +
    (-1 / 24) * rel5_st_m_m11m + (5 / 48) * rel5_st_m_mm0m + (-1 / 24) * rel5_st_m_mm1m +
    (-3 / 2) * rel5_st_m_0mmm

theorem hpl_zero_negOne_zero_one_negOne_at_one :
    hpl [zero, negOne, zero, one, negOne] 1 =
      4 * Li 4 (1 / 2) * log 2 + 8 * Li 5 (1 / 2) + 1 / 10 * log 2 ^ 5
      - 1 / 18 * log 2 ^ 3 * π ^ 2 + 17 / 360 * log 2 * π ^ 4 + 3 / 16 * zeta3 * π ^ 2
      - 331 / 32 * zeta5 := by
  linear_combination (-47 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-21 / 2) * hpl_zero_zero_zero_one_one_at_one +
    (-335 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (-151 / 48) * hpl_zero_one_zero_zero_one_at_one + (4) * hpl_zero_zero_one_one_one_at_one +
    (3) * hpl_zero_one_zero_one_one_at_one + (1) * hpl_zero_one_one_zero_one_at_one +
    (-55 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (8) * hpl_negOne_one_one_one_one_at_one +
    (-869 / 240) * rel5_sh_m_mmmm + (49 / 96) * rel5_sh_m_0mmm + (-49 / 288) * rel5_sh_m_m0mm +
    (8 / 3) * rel5_sh_m_m1mm + (-23 / 72) * rel5_sh_m_mm0m + (-85 / 32) * rel5_sh_m_mm1m +
    (-129 / 32) * rel5_sh_m_mmm1 + (-115 / 128) * rel5_st_m_0001 + (1321 / 288) * rel5_st_m_000m +
    (13 / 3) * rel5_sh_m_00mm + (47 / 48) * rel5_sh_m_01mm + (-11 / 12) * rel5_sh_m_0m0m +
    (-1 / 48) * rel5_sh_m_0m1m + (-4 / 3) * rel5_sh_m_0mm1 + (47 / 96) * rel5_sh_m_m01m +
    (-13 / 24) * rel5_sh_m_m0m1 + (95 / 96) * rel5_sh_m_m10m + (4) * rel5_sh_m_m11m +
    (21 / 4) * rel5_sh_m_m1m1 + (-47 / 48) * rel5_sh_m_mm01 + (83 / 128) * rel5_st_01_00m +
    (17 / 12) * rel5_st_0m_001 + (-5 / 16) * rel5_sh_0m_00m + (-1039 / 288) * rel5_st_0m_00m +
    (7 / 6) * rel5_sh_0m_0mm + (-4 / 3) * rel5_sh_m1_m11 + (-2) * rel5_sh_m1_mm1 +
    (49 / 24) * rel5_mob_0mmm1 + (-1 / 4) * rel5_sh_m_000m + (-71 / 24) * rel5_sh_m_001m +
    (325 / 144) * rel5_st_m_001m + (-85 / 24) * rel5_sh_m_00m1 + (167 / 72) * rel5_st_m_00m1 +
    (-91 / 48) * rel5_sh_m_010m + (-11 / 24) * rel5_sh_m_01m1 + (-1 / 6) * rel5_sh_m_0m01 +
    (17 / 24) * rel5_sh_m_0m11 + (23 / 24) * rel5_sh_m_m001 + (-71 / 576) * rel5_st_m_m001 +
    (-37 / 144) * rel5_st_m_m00m + (-31 / 24) * rel5_sh_m_m011 + (-5 / 48) * rel5_sh_m_m101 +
    (8) * rel5_sh_m_m111 + (-1345 / 1152) * rel5_st_01_01m + (-557 / 1152) * rel5_st_01_m0m +
    (47 / 24) * rel5_st_0m_0m1 + (-13 / 3) * rel5_st_0m_0mm + (-1 / 24) * rel5_st_0m_m01 +
    (155 / 32) * rel5_sh_m_0001 + (3) * rel5_sh_m_0011 + (-113 / 48) * rel5_st_m_0011 +
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

theorem hpl_zero_negOne_zero_negOne_one_at_one :
    hpl [zero, negOne, zero, negOne, one] 1 =
      -4 * Li 5 (1 / 2) + 1 / 30 * log 2 ^ 5 - 1 / 18 * log 2 ^ 3 * π ^ 2
      + 7 / 4 * log 2 ^ 2 * zeta3 - 17 / 360 * log 2 * π ^ 4 - 1 / 3 * zeta3 * π ^ 2
      + 129 / 16 * zeta5 := by
  linear_combination (-1069 / 288) * hpl_zero_zero_zero_zero_one_at_one +
    (77 / 12) * hpl_zero_zero_zero_one_one_at_one +
    (827 / 288) * hpl_zero_zero_one_zero_one_at_one +
    (355 / 288) * hpl_zero_one_zero_zero_one_at_one + (-4) * hpl_zero_zero_one_one_one_at_one +
    (-5 / 2) * hpl_zero_one_zero_one_one_at_one + (-5 / 6) * hpl_zero_one_one_zero_one_at_one +
    (23 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (-241 / 480) * rel5_sh_m_mmmm + (-67 / 192) * rel5_sh_m_0mmm + (67 / 576) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (-67 / 144) * rel5_sh_m_mm0m + (-97 / 64) * rel5_sh_m_mm1m +
    (-29 / 64) * rel5_sh_m_mmm1 + (-351 / 256) * rel5_st_m_0001 + (-109 / 192) * rel5_st_m_000m +
    (-53 / 18) * rel5_sh_m_00mm + (67 / 96) * rel5_sh_m_01mm + (-155 / 72) * rel5_sh_m_0m0m +
    (67 / 96) * rel5_sh_m_0m1m + (4 / 3) * rel5_sh_m_0mm1 + (67 / 192) * rel5_sh_m_m01m +
    (11 / 48) * rel5_sh_m_m0m1 + (67 / 192) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-43 / 24) * rel5_sh_m_m1m1 + (-67 / 96) * rel5_sh_m_mm01 + (613 / 768) * rel5_st_01_00m +
    (-99 / 32) * rel5_st_0m_001 + (245 / 288) * rel5_sh_0m_00m + (2465 / 576) * rel5_st_0m_00m +
    (59 / 36) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (-5 / 6) * rel5_sh_m1_mm1 +
    (-67 / 48) * rel5_mob_0mmm1 + (185 / 144) * rel5_sh_m_000m + (221 / 144) * rel5_sh_m_001m +
    (-467 / 288) * rel5_st_m_001m + (241 / 144) * rel5_sh_m_00m1 + (-235 / 144) * rel5_st_m_00m1 +
    (163 / 96) * rel5_sh_m_010m + (-19 / 48) * rel5_sh_m_01m1 + (-17 / 36) * rel5_sh_m_0m01 +
    (-33 / 16) * rel5_sh_m_0m11 + (-59 / 144) * rel5_sh_m_m001 + (-59 / 1152) * rel5_st_m_m001 +
    (35 / 288) * rel5_st_m_m00m + (-33 / 16) * rel5_sh_m_m011 + (-121 / 96) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (123 / 256) * rel5_st_01_01m + (-3241 / 2304) * rel5_st_01_m0m +
    (-115 / 96) * rel5_st_0m_0m1 + (55 / 18) * rel5_st_0m_0mm + (-115 / 96) * rel5_st_0m_m01 +
    (-397 / 576) * rel5_sh_m_0001 + (-29 / 18) * rel5_sh_m_0011 + (1049 / 288) * rel5_st_m_0011 +
    (121 / 36) * rel5_st_m_00mm + (7 / 144) * rel5_sh_m_0101 + (-10 / 9) * rel5_st_m_010m +
    (17 / 144) * rel5_st_m_01m1 + (5 / 4) * rel5_st_m_0m0m + (-115 / 144) * rel5_st_m_0m1m +
    (-23 / 48) * rel5_st_m_m01m + (-643 / 1152) * rel5_st_m_m0m1 + (59 / 576) * rel5_st_m_m101 +
    (-35 / 144) * rel5_st_m_m10m + (-1 / 24) * rel5_st_m_m1m1 + (-383 / 288) * rel5_sh_01_00m +
    (-1 / 6) * rel5_sh_01_01m + (-1 / 4) * rel5_sh_01_0m1 + (-1 / 4) * rel5_st_01_0m1 +
    (-129 / 32) * rel5_st_01_0mm + (5 / 3) * rel5_sh_01_m11 + (263 / 288) * rel5_sh_0m_001 +
    (-1 / 32) * rel5_sh_0m_01m + (-1 / 3) * rel5_sh_m1_011 + (1 / 32) * rel5_sh_m1_0m1 +
    (33 / 32) * rel5_sh_m1_m01 + (-1) * rel5_mob_00mmm + (-67 / 32) * rel5_mob_01mmm +
    (-1) * rel5_mob_0m0mm + (-67 / 96) * rel5_mob_0m1mm + (67 / 96) * rel5_mob_m10mm +
    (1 / 72) * rel5_st_m_011m + (-3 / 4) * rel5_st_m_01mm + (67 / 96) * rel5_st_m_0m11 +
    (-131 / 96) * rel5_st_m_0mm1 + (67 / 96) * rel5_st_m_m011 + (7 / 4) * rel5_st_m_m0mm +
    (-1 / 36) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm + (59 / 72) * rel5_st_m_mm0m +
    (-13 / 36) * rel5_st_m_mm1m + (4) * rel5_st_m_0mmm + (-4) * rel5_mob_0000m

theorem hpl_zero_negOne_zero_negOne_negOne_at_one :
    hpl [zero, negOne, zero, negOne, negOne] 1 =
      -4 * Li 4 (1 / 2) * log 2 - 4 * Li 5 (1 / 2) - 2 / 15 * log 2 ^ 5
      + 1 / 9 * log 2 ^ 3 * π ^ 2 - 7 / 4 * log 2 ^ 2 * zeta3 + 1 / 4 * zeta3 * π ^ 2
      + 73 / 64 * zeta5 := by
  linear_combination (-29 / 32) * hpl_zero_zero_zero_zero_one_at_one +
    (17 / 2) * hpl_zero_zero_zero_one_one_at_one + (191 / 32) * hpl_zero_zero_one_zero_one_at_one +
    (79 / 32) * hpl_zero_one_zero_zero_one_at_one + (-2) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 2) * hpl_zero_one_zero_one_one_at_one + (-1 / 2) * hpl_zero_one_one_zero_one_at_one +
    (61 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-4) * hpl_negOne_one_one_one_one_at_one +
    (3119 / 480) * rel5_sh_m_mmmm + (-67 / 192) * rel5_sh_m_0mmm + (67 / 576) * rel5_sh_m_m0mm +
    (-4 / 3) * rel5_sh_m_m1mm + (77 / 144) * rel5_sh_m_mm0m + (351 / 64) * rel5_sh_m_mm1m +
    (483 / 64) * rel5_sh_m_mmm1 + (49 / 256) * rel5_st_m_0001 + (-1567 / 576) * rel5_st_m_000m +
    (-23 / 6) * rel5_sh_m_00mm + (-125 / 96) * rel5_sh_m_01mm + (8 / 3) * rel5_sh_m_0m0m +
    (-29 / 96) * rel5_sh_m_0m1m + (2 / 3) * rel5_sh_m_0mm1 + (-125 / 192) * rel5_sh_m_m01m +
    (19 / 48) * rel5_sh_m_m0m1 + (-221 / 192) * rel5_sh_m_m10m + (-2) * rel5_sh_m_m11m +
    (-31 / 8) * rel5_sh_m_m1m1 + (125 / 96) * rel5_sh_m_mm01 + (-249 / 256) * rel5_st_01_00m +
    (-29 / 96) * rel5_st_0m_001 + (55 / 96) * rel5_sh_0m_00m + (2089 / 576) * rel5_st_0m_00m +
    (-11 / 4) * rel5_sh_0m_0mm + (2 / 3) * rel5_sh_m1_m11 + (4) * rel5_sh_m1_mm1 +
    (-67 / 48) * rel5_mob_0mmm1 + (-107 / 48) * rel5_sh_m_000m + (41 / 16) * rel5_sh_m_001m +
    (-547 / 288) * rel5_st_m_001m + (49 / 16) * rel5_sh_m_00m1 + (-281 / 144) * rel5_st_m_00m1 +
    (67 / 96) * rel5_sh_m_010m + (29 / 48) * rel5_sh_m_01m1 + (5 / 8) * rel5_sh_m_0m01 +
    (13 / 48) * rel5_sh_m_0m11 + (-11 / 16) * rel5_sh_m_m001 + (149 / 1152) * rel5_st_m_m001 +
    (43 / 288) * rel5_st_m_m00m + (109 / 48) * rel5_sh_m_m011 + (71 / 96) * rel5_sh_m_m101 +
    (-4) * rel5_sh_m_m111 + (2371 / 2304) * rel5_st_01_01m + (3431 / 2304) * rel5_st_01_m0m +
    (-115 / 96) * rel5_st_0m_0m1 + (13 / 4) * rel5_st_0m_0mm + (77 / 96) * rel5_st_0m_m01 +
    (-551 / 192) * rel5_sh_m_0001 + (-19 / 6) * rel5_sh_m_0011 + (49 / 32) * rel5_st_m_0011 +
    (21 / 4) * rel5_st_m_00mm + (-145 / 48) * rel5_sh_m_0101 + (-167 / 72) * rel5_st_m_010m +
    (-11 / 144) * rel5_st_m_01m1 + (293 / 72) * rel5_st_m_0m0m + (-19 / 144) * rel5_st_m_0m1m +
    (47 / 144) * rel5_st_m_m01m + (61 / 1152) * rel5_st_m_m0m1 + (-149 / 576) * rel5_st_m_m101 +
    (-43 / 144) * rel5_st_m_m10m + (3 / 8) * rel5_st_m_m1m1 + (7 / 96) * rel5_sh_01_00m +
    (5 / 12) * rel5_sh_01_01m + (-2 / 3) * rel5_sh_01_0m1 + (-1 / 4) * rel5_st_01_0m1 +
    (245 / 96) * rel5_st_01_0mm + (3) * rel5_sh_01_m11 + (-55 / 96) * rel5_sh_0m_001 +
    (-79 / 96) * rel5_sh_0m_01m + (-7 / 3) * rel5_sh_m1_011 + (-61 / 96) * rel5_sh_m1_0m1 +
    (-109 / 96) * rel5_sh_m1_m01 + (28) * rel5_mob_00mmm + (125 / 32) * rel5_mob_01mmm +
    (10) * rel5_mob_0m0mm + (125 / 96) * rel5_mob_0m1mm + (-221 / 96) * rel5_mob_m10mm +
    (-7 / 8) * rel5_st_m_011m + (7 / 12) * rel5_st_m_01mm + (-29 / 96) * rel5_st_m_0m11 +
    (-1 / 32) * rel5_st_m_0mm1 + (-221 / 96) * rel5_st_m_m011 + (25 / 12) * rel5_st_m_m0mm +
    (-1 / 4) * rel5_st_m_m11m + (-1 / 2) * rel5_st_m_m1mm + (11 / 8) * rel5_st_m_mm0m +
    (-7 / 12) * rel5_st_m_mm1m + (2) * rel5_st_m_0mmm + (-4) * rel5_mob_0000m

theorem hpl_zero_negOne_one_zero_one_at_one :
    hpl [zero, negOne, one, zero, one] 1 =
      -1 / 96 * log 2 * π ^ 4 + 5 / 12 * zeta3 * π ^ 2 - 257 / 64 * zeta5 := by
  linear_combination (677 / 192) * hpl_zero_zero_zero_zero_one_at_one +
    (23 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (545 / 192) * hpl_zero_zero_one_zero_one_at_one +
    (169 / 192) * hpl_zero_one_zero_zero_one_at_one + (3 / 2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 4) * hpl_zero_one_zero_one_one_at_one + (1 / 4) * hpl_zero_one_one_zero_one_at_one +
    (-7 / 4) * hpl_zero_zero_zero_zero_negOne_at_one + (-129 / 64) * rel5_sh_m_mmmm +
    (57 / 128) * rel5_sh_m_0mmm + (-19 / 128) * rel5_sh_m_m0mm + (-1 / 32) * rel5_sh_m_mm0m +
    (-191 / 128) * rel5_sh_m_mm1m + (-291 / 128) * rel5_sh_m_mmm1 + (1323 / 512) * rel5_st_m_0001 +
    (-1481 / 384) * rel5_st_m_000m + (-23 / 12) * rel5_sh_m_00mm + (23 / 64) * rel5_sh_m_01mm +
    (-65 / 12) * rel5_sh_m_0m0m + (-17 / 64) * rel5_sh_m_0m1m + (-1 / 2) * rel5_sh_m_0mm1 +
    (23 / 128) * rel5_sh_m_m01m + (1 / 32) * rel5_sh_m_m0m1 + (63 / 128) * rel5_sh_m_m10m +
    (5 / 8) * rel5_sh_m_m1m1 + (-23 / 64) * rel5_sh_m_mm01 + (737 / 512) * rel5_st_01_00m +
    (-291 / 128) * rel5_st_0m_001 + (-17 / 24) * rel5_sh_0m_00m + (127 / 384) * rel5_st_0m_00m +
    (25 / 12) * rel5_sh_0m_0mm + (-9 / 8) * rel5_sh_m1_mm1 + (57 / 32) * rel5_mob_0mmm1 +
    (1477 / 192) * rel5_sh_m_000m + (35 / 24) * rel5_sh_m_001m + (-265 / 192) * rel5_st_m_001m +
    (127 / 96) * rel5_sh_m_00m1 + (-65 / 48) * rel5_st_m_00m1 + (57 / 16) * rel5_sh_m_010m +
    (15 / 32) * rel5_sh_m_01m1 + (25 / 24) * rel5_sh_m_0m01 + (25 / 32) * rel5_sh_m_0m11 +
    (-5 / 96) * rel5_sh_m_m001 + (-47 / 768) * rel5_st_m_m001 + (1 / 192) * rel5_st_m_m00m +
    (-15 / 32) * rel5_sh_m_m011 + (-17 / 64) * rel5_sh_m_m101 + (397 / 512) * rel5_st_01_01m +
    (-4261 / 1536) * rel5_st_01_m0m + (-131 / 128) * rel5_st_0m_0m1 + (7 / 12) * rel5_st_0m_0mm +
    (-291 / 128) * rel5_st_0m_m01 + (-1483 / 384) * rel5_sh_m_0001 + (-29 / 12) * rel5_sh_m_0011 +
    (557 / 192) * rel5_st_m_0011 + (55 / 24) * rel5_st_m_00mm + (-119 / 96) * rel5_sh_m_0101 +
    (-7 / 8) * rel5_st_m_010m + (-19 / 96) * rel5_st_m_01m1 + (35 / 24) * rel5_st_m_0m0m +
    (13 / 32) * rel5_st_m_0m1m + (-11 / 96) * rel5_st_m_m01m + (-7 / 768) * rel5_st_m_m0m1 +
    (47 / 384) * rel5_st_m_m101 + (-1 / 96) * rel5_st_m_m10m + (-1 / 8) * rel5_st_m_m1m1 +
    (-437 / 192) * rel5_sh_01_00m + (-1 / 4) * rel5_sh_01_01m + (-1 / 8) * rel5_sh_01_0m1 +
    (1 / 2) * rel5_st_01_0m1 + (-527 / 64) * rel5_st_01_0mm + (1 / 4) * rel5_sh_01_m11 +
    (317 / 192) * rel5_sh_0m_001 + (1 / 16) * rel5_sh_0m_01m + (-3 / 4) * rel5_sh_m1_011 +
    (-1 / 64) * rel5_sh_m1_0m1 + (15 / 64) * rel5_sh_m1_m01 + (-27 / 4) * rel5_mob_00mmm +
    (-69 / 64) * rel5_mob_01mmm + (-2) * rel5_mob_0m0mm + (-23 / 64) * rel5_mob_0m1mm +
    (63 / 64) * rel5_mob_m10mm + (-17 / 48) * rel5_st_m_011m + (5 / 8) * rel5_st_m_01mm +
    (-17 / 64) * rel5_st_m_0m11 + (33 / 64) * rel5_st_m_0mm1 + (63 / 64) * rel5_st_m_m011 +
    (-1 / 8) * rel5_st_m_m0mm + (-1 / 24) * rel5_st_m_m11m + (5 / 48) * rel5_st_m_mm0m +
    (-1 / 24) * rel5_st_m_mm1m + (-3 / 2) * rel5_st_m_0mmm

theorem hpl_zero_negOne_one_zero_negOne_at_one :
    hpl [zero, negOne, one, zero, negOne] 1 =
      -8 * Li 4 (1 / 2) * log 2 - 16 * Li 5 (1 / 2) - 1 / 5 * log 2 ^ 5
      + 1 / 9 * log 2 ^ 3 * π ^ 2 - 17 / 180 * log 2 * π ^ 4 - 5 / 96 * zeta3 * π ^ 2
      + 547 / 32 * zeta5 := by
  linear_combination (-73 / 24) * hpl_zero_zero_zero_zero_one_at_one +
    (21) * hpl_zero_zero_zero_one_one_at_one + (335 / 24) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 24) * hpl_zero_one_zero_zero_one_at_one + (-8) * hpl_zero_zero_one_one_one_at_one +
    (-6) * hpl_zero_one_zero_one_one_at_one + (-2) * hpl_zero_one_one_zero_one_at_one +
    (119 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (-16) * hpl_negOne_one_one_one_one_at_one +
    (869 / 120) * rel5_sh_m_mmmm + (-49 / 48) * rel5_sh_m_0mmm + (49 / 144) * rel5_sh_m_m0mm +
    (-16 / 3) * rel5_sh_m_m1mm + (23 / 36) * rel5_sh_m_mm0m + (85 / 16) * rel5_sh_m_mm1m +
    (129 / 16) * rel5_sh_m_mmm1 + (19 / 64) * rel5_st_m_0001 + (-961 / 144) * rel5_st_m_000m +
    (-26 / 3) * rel5_sh_m_00mm + (-47 / 24) * rel5_sh_m_01mm + (11 / 6) * rel5_sh_m_0m0m +
    (1 / 24) * rel5_sh_m_0m1m + (8 / 3) * rel5_sh_m_0mm1 + (-47 / 48) * rel5_sh_m_m01m +
    (13 / 12) * rel5_sh_m_m0m1 + (-95 / 48) * rel5_sh_m_m10m + (-8) * rel5_sh_m_m11m +
    (-21 / 2) * rel5_sh_m_m1m1 + (47 / 24) * rel5_sh_m_mm01 + (-83 / 64) * rel5_st_01_00m +
    (-17 / 6) * rel5_st_0m_001 + (9 / 8) * rel5_sh_0m_00m + (1399 / 144) * rel5_st_0m_00m +
    (-7 / 3) * rel5_sh_0m_0mm + (8 / 3) * rel5_sh_m1_m11 + (4) * rel5_sh_m1_mm1 +
    (-49 / 12) * rel5_mob_0mmm1 + (-1) * rel5_sh_m_000m + (71 / 12) * rel5_sh_m_001m +
    (-325 / 72) * rel5_st_m_001m + (85 / 12) * rel5_sh_m_00m1 + (-167 / 36) * rel5_st_m_00m1 +
    (91 / 24) * rel5_sh_m_010m + (11 / 12) * rel5_sh_m_01m1 + (1 / 3) * rel5_sh_m_0m01 +
    (-17 / 12) * rel5_sh_m_0m11 + (-23 / 12) * rel5_sh_m_m001 + (71 / 288) * rel5_st_m_m001 +
    (37 / 72) * rel5_st_m_m00m + (31 / 12) * rel5_sh_m_m011 + (5 / 24) * rel5_sh_m_m101 +
    (-16) * rel5_sh_m_m111 + (1345 / 576) * rel5_st_01_01m + (557 / 576) * rel5_st_01_m0m +
    (-35 / 12) * rel5_st_0m_0m1 + (26 / 3) * rel5_st_0m_0mm + (1 / 12) * rel5_st_0m_m01 +
    (-115 / 16) * rel5_sh_m_0001 + (-6) * rel5_sh_m_0011 + (113 / 24) * rel5_st_m_0011 +
    (37 / 3) * rel5_st_m_00mm + (-23 / 4) * rel5_sh_m_0101 + (-52 / 9) * rel5_st_m_010m +
    (-5 / 36) * rel5_st_m_01m1 + (85 / 9) * rel5_st_m_0m0m + (-37 / 36) * rel5_st_m_0m1m +
    (5 / 36) * rel5_st_m_m01m + (-113 / 288) * rel5_st_m_m0m1 + (-71 / 144) * rel5_st_m_m101 +
    (-37 / 36) * rel5_st_m_m10m + (1 / 2) * rel5_st_m_m1m1 + (-19 / 24) * rel5_sh_01_00m +
    (2 / 3) * rel5_sh_01_01m + (-5 / 3) * rel5_sh_01_0m1 + (-1) * rel5_st_01_0m1 +
    (-1 / 24) * rel5_st_01_0mm + (8) * rel5_sh_01_m11 + (-5 / 24) * rel5_sh_0m_001 +
    (-43 / 24) * rel5_sh_0m_01m + (-16 / 3) * rel5_sh_m1_011 + (-31 / 24) * rel5_sh_m1_0m1 +
    (-31 / 24) * rel5_sh_m1_m01 + (40) * rel5_mob_00mmm + (47 / 8) * rel5_mob_01mmm +
    (12) * rel5_mob_0m0mm + (47 / 24) * rel5_mob_0m1mm + (-95 / 24) * rel5_mob_m10mm +
    (-11 / 6) * rel5_st_m_011m + (1 / 3) * rel5_st_m_01mm + (1 / 24) * rel5_st_m_0m11 +
    (-11 / 8) * rel5_st_m_0mm1 + (-95 / 24) * rel5_st_m_m011 + (19 / 3) * rel5_st_m_m0mm +
    (-1 / 3) * rel5_st_m_m11m + (-2) * rel5_st_m_m1mm + (23 / 6) * rel5_st_m_mm0m +
    (-5 / 3) * rel5_st_m_mm1m + (8) * rel5_st_m_0mmm + (-16) * rel5_mob_0000m

theorem hpl_zero_negOne_one_one_one_at_one :
    hpl [zero, negOne, one, one, one] 1 =
      3 * Li 5 (1 / 2) - 1 / 40 * log 2 ^ 5 + 1 / 240 * log 2 * π ^ 4
      - 7 / 48 * zeta3 * π ^ 2 - 1 / 32 * zeta5 := by
  linear_combination (-29 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-1) * hpl_zero_one_one_one_one_at_one + (-7 / 8) * hpl_zero_zero_zero_one_one_at_one +
    (-35 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (-13 / 48) * hpl_zero_one_zero_zero_one_at_one + (-1 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-1 / 2) * hpl_zero_one_zero_one_one_at_one + (-1 / 6) * hpl_zero_one_one_zero_one_at_one +
    (-1 / 2) * hpl_zero_zero_zero_zero_negOne_at_one + (3) * hpl_negOne_one_one_one_one_at_one +
    (-83 / 480) * rel5_sh_m_mmmm + (-53 / 192) * rel5_sh_m_0mmm + (53 / 576) * rel5_sh_m_m0mm +
    (1 / 3) * rel5_sh_m_m1mm + (-47 / 144) * rel5_sh_m_mm0m + (-121 / 192) * rel5_sh_m_mm1m +
    (-23 / 64) * rel5_sh_m_mmm1 + (-127 / 256) * rel5_st_m_0001 + (179 / 288) * rel5_st_m_000m +
    (1 / 2) * rel5_sh_m_00mm + (15 / 32) * rel5_sh_m_01mm + (-1 / 12) * rel5_sh_m_0m0m +
    (17 / 96) * rel5_sh_m_0m1m + (1 / 6) * rel5_sh_m_0mm1 + (13 / 192) * rel5_sh_m_m01m +
    (41 / 192) * rel5_sh_m_m10m + (1 / 2) * rel5_sh_m_m11m + (29 / 48) * rel5_sh_m_m1m1 +
    (-13 / 96) * rel5_sh_m_mm01 + (107 / 768) * rel5_st_01_00m + (-55 / 384) * rel5_st_0m_001 +
    (17 / 192) * rel5_sh_0m_00m + (-5 / 288) * rel5_st_0m_00m + (7 / 24) * rel5_sh_0m_0mm +
    (-1 / 3) * rel5_sh_m1_m11 + (-5 / 24) * rel5_sh_m1_mm1 + (-53 / 48) * rel5_mob_0mmm1 +
    (-15 / 64) * rel5_sh_m_000m + (-23 / 96) * rel5_sh_m_001m + (19 / 72) * rel5_st_m_001m +
    (-3 / 8) * rel5_sh_m_00m1 + (65 / 288) * rel5_st_m_00m1 + (-13 / 64) * rel5_sh_m_010m +
    (-1 / 6) * rel5_sh_m_01m1 + (-17 / 48) * rel5_sh_m_0m01 + (-7 / 16) * rel5_sh_m_0m11 +
    (-1 / 24) * rel5_sh_m_m001 + (-37 / 1152) * rel5_st_m_m001 + (-1 / 72) * rel5_st_m_m00m +
    (-11 / 16) * rel5_sh_m_m011 + (-25 / 96) * rel5_sh_m_m101 + (1) * rel5_sh_m_m111 +
    (-347 / 2304) * rel5_st_01_01m + (-271 / 2304) * rel5_st_01_m0m + (53 / 384) * rel5_st_0m_0m1 +
    (-5 / 24) * rel5_st_0m_0mm + (-43 / 384) * rel5_st_0m_m01 + (61 / 96) * rel5_sh_m_0001 +
    (5 / 6) * rel5_sh_m_0011 + (-7 / 96) * rel5_st_m_0011 + (-2 / 3) * rel5_st_m_00mm +
    (11 / 16) * rel5_sh_m_0101 + (37 / 144) * rel5_st_m_010m + (7 / 144) * rel5_st_m_01m1 +
    (-67 / 144) * rel5_st_m_0m0m + (-5 / 36) * rel5_st_m_0m1m + (-5 / 36) * rel5_st_m_m01m +
    (-101 / 1152) * rel5_st_m_m0m1 + (37 / 576) * rel5_st_m_m101 + (1 / 36) * rel5_st_m_m10m +
    (-1 / 48) * rel5_st_m_m1m1 + (-1 / 48) * rel5_sh_01_00m + (-1 / 8) * rel5_sh_01_01m +
    (1 / 24) * rel5_sh_01_0m1 + (-1 / 8) * rel5_st_01_0m1 + (-13 / 96) * rel5_st_01_0mm +
    (1 / 12) * rel5_sh_01_m11 + (7 / 48) * rel5_sh_0m_001 + (11 / 192) * rel5_sh_0m_01m +
    (5 / 12) * rel5_sh_m1_011 + (3 / 32) * rel5_sh_m1_0m1 + (3 / 32) * rel5_sh_m1_m01 +
    (-13 / 4) * rel5_mob_00mmm + (-45 / 32) * rel5_mob_01mmm + (-7 / 6) * rel5_mob_0m0mm +
    (-15 / 32) * rel5_mob_0m1mm + (41 / 96) * rel5_mob_m10mm + (1 / 12) * rel5_st_m_011m +
    (-1 / 3) * rel5_st_m_01mm + (17 / 96) * rel5_st_m_0m11 + (-25 / 96) * rel5_st_m_0mm1 +
    (41 / 96) * rel5_st_m_m011 + (1 / 6) * rel5_st_m_m0mm + (1 / 12) * rel5_st_m_m11m +
    (1 / 4) * rel5_st_m_m1mm + (1 / 12) * rel5_st_m_mm0m + (1 / 4) * rel5_st_m_mm1m +
    (1 / 2) * rel5_st_m_0mmm + (-1) * rel5_st_m_mmmm + (1) * rel5_mob_0000m

theorem hpl_zero_negOne_one_one_negOne_at_one :
    hpl [zero, negOne, one, one, negOne] 1 =
      Li 4 (1 / 2) * log 2 - Li 5 (1 / 2) + 1 / 20 * log 2 ^ 5 - 1 / 18 * log 2 ^ 3 * π ^ 2
      - 1 / 360 * log 2 * π ^ 4 + 33 / 64 * zeta5 := by
  linear_combination (-769 / 384) * hpl_zero_zero_zero_zero_one_at_one +
    (21 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (335 / 384) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 384) * hpl_zero_one_zero_zero_one_at_one + (-1 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 8) * hpl_zero_one_zero_one_one_at_one + (-1 / 8) * hpl_zero_one_one_zero_one_at_one +
    (31 / 12) * hpl_zero_zero_zero_zero_negOne_at_one + (-1) * hpl_negOne_one_one_one_one_at_one +
    (4469 / 1920) * rel5_sh_m_mmmm + (-193 / 768) * rel5_sh_m_0mmm +
    (193 / 2304) * rel5_sh_m_m0mm + (-1 / 3) * rel5_sh_m_m1mm + (167 / 576) * rel5_sh_m_mm0m +
    (549 / 256) * rel5_sh_m_mm1m + (657 / 256) * rel5_sh_m_mmm1 + (-1213 / 1024) * rel5_st_m_0001 +
    (1991 / 2304) * rel5_st_m_000m + (-37 / 24) * rel5_sh_m_00mm + (-287 / 384) * rel5_sh_m_01mm +
    (203 / 96) * rel5_sh_m_0m0m + (-47 / 384) * rel5_sh_m_0m1m + (1 / 6) * rel5_sh_m_0mm1 +
    (-287 / 768) * rel5_sh_m_m01m + (13 / 192) * rel5_sh_m_m0m1 + (-527 / 768) * rel5_sh_m_m10m +
    (-1 / 2) * rel5_sh_m_m11m + (-41 / 32) * rel5_sh_m_m1m1 + (287 / 384) * rel5_sh_m_mm01 +
    (-707 / 1024) * rel5_st_01_00m + (7 / 24) * rel5_st_0m_001 + (85 / 128) * rel5_sh_0m_00m +
    (2623 / 2304) * rel5_st_0m_00m + (-43 / 48) * rel5_sh_0m_0mm + (1 / 6) * rel5_sh_m1_m11 +
    (3 / 2) * rel5_sh_m1_mm1 + (-193 / 192) * rel5_mob_0mmm1 + (-115 / 32) * rel5_sh_m_000m +
    (95 / 192) * rel5_sh_m_001m + (-325 / 1152) * rel5_st_m_001m + (85 / 192) * rel5_sh_m_00m1 +
    (-179 / 576) * rel5_st_m_00m1 + (-317 / 384) * rel5_sh_m_010m + (11 / 192) * rel5_sh_m_01m1 +
    (1 / 48) * rel5_sh_m_0m01 + (223 / 192) * rel5_sh_m_0m11 + (-23 / 192) * rel5_sh_m_m001 +
    (407 / 4608) * rel5_st_m_m001 + (37 / 1152) * rel5_st_m_m00m + (271 / 192) * rel5_sh_m_m011 +
    (245 / 384) * rel5_sh_m_m101 + (-1) * rel5_sh_m_m111 + (721 / 9216) * rel5_st_01_01m +
    (11261 / 9216) * rel5_st_01_m0m + (-29 / 192) * rel5_st_0m_0m1 + (13 / 24) * rel5_st_0m_0mm +
    (211 / 192) * rel5_st_0m_m01 + (213 / 256) * rel5_sh_m_0001 + (-3 / 8) * rel5_sh_m_0011 +
    (65 / 384) * rel5_st_m_0011 + (37 / 48) * rel5_st_m_00mm + (-23 / 64) * rel5_sh_m_0101 +
    (-13 / 36) * rel5_st_m_010m + (19 / 576) * rel5_st_m_01m1 + (85 / 144) * rel5_st_m_0m0m +
    (-37 / 576) * rel5_st_m_0m1m + (5 / 576) * rel5_st_m_m01m + (703 / 4608) * rel5_st_m_m0m1 +
    (-407 / 2304) * rel5_st_m_m101 + (-37 / 576) * rel5_st_m_m10m + (5 / 32) * rel5_st_m_m1m1 +
    (269 / 384) * rel5_sh_01_00m + (1 / 24) * rel5_sh_01_01m + (-5 / 48) * rel5_sh_01_0m1 +
    (-1 / 16) * rel5_st_01_0m1 + (1295 / 384) * rel5_st_01_0mm + (1 / 2) * rel5_sh_01_m11 +
    (-293 / 384) * rel5_sh_0m_001 + (-67 / 384) * rel5_sh_0m_01m + (-1 / 3) * rel5_sh_m1_011 +
    (-271 / 384) * rel5_sh_m1_0m1 + (-271 / 384) * rel5_sh_m1_m01 + (10) * rel5_mob_00mmm +
    (287 / 128) * rel5_mob_01mmm + (13 / 4) * rel5_mob_0m0mm + (287 / 384) * rel5_mob_0m1mm +
    (-527 / 384) * rel5_mob_m10mm + (-11 / 96) * rel5_st_m_011m + (1 / 48) * rel5_st_m_01mm +
    (-47 / 384) * rel5_st_m_0m11 + (5 / 128) * rel5_st_m_0mm1 + (-527 / 384) * rel5_st_m_m011 +
    (19 / 48) * rel5_st_m_m0mm + (-1 / 48) * rel5_st_m_m11m + (-1 / 8) * rel5_st_m_m1mm +
    (23 / 96) * rel5_st_m_mm0m + (-5 / 48) * rel5_st_m_mm1m + (1 / 2) * rel5_st_m_0mmm +
    (-1) * rel5_mob_0000m

theorem hpl_zero_negOne_one_negOne_one_at_one :
    hpl [zero, negOne, one, negOne, one] 1 =
      -3 * Li 5 (1 / 2) + 1 / 40 * log 2 ^ 5 + 1 / 8 * log 2 ^ 3 * π ^ 2
      - 21 / 16 * log 2 ^ 2 * zeta3 - 7 / 480 * log 2 * π ^ 4 + 9 / 32 * zeta3 * π ^ 2
      - 29 / 64 * zeta5 := by
  linear_combination (1193 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (185 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (3881 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (1585 / 1152) * hpl_zero_one_zero_zero_one_at_one +
    (-3 / 8) * hpl_zero_one_zero_one_one_at_one + (-1 / 8) * hpl_zero_one_one_zero_one_at_one +
    (7 / 4) * hpl_zero_zero_zero_zero_negOne_at_one + (-3) * hpl_negOne_one_one_one_one_at_one +
    (3437 / 1920) * rel5_sh_m_mmmm + (-265 / 768) * rel5_sh_m_0mmm +
    (265 / 2304) * rel5_sh_m_m0mm + (-1) * rel5_sh_m_m1mm + (119 / 576) * rel5_sh_m_mm0m +
    (919 / 768) * rel5_sh_m_mm1m + (553 / 256) * rel5_sh_m_mmm1 + (1539 / 1024) * rel5_st_m_0001 +
    (-1751 / 768) * rel5_st_m_000m + (-47 / 72) * rel5_sh_m_00mm + (-119 / 384) * rel5_sh_m_01mm +
    (-83 / 288) * rel5_sh_m_0m0m + (-61 / 128) * rel5_sh_m_0m1m + (-119 / 768) * rel5_sh_m_m01m +
    (49 / 192) * rel5_sh_m_m0m1 + (-119 / 768) * rel5_sh_m_m10m + (-3 / 2) * rel5_sh_m_m11m +
    (-63 / 32) * rel5_sh_m_m1m1 + (119 / 384) * rel5_sh_m_mm01 + (-187 / 1024) * rel5_st_01_00m +
    (-9 / 128) * rel5_st_0m_001 + (-481 / 1152) * rel5_sh_0m_00m + (2867 / 2304) * rel5_st_0m_00m +
    (-163 / 144) * rel5_sh_0m_0mm + (1 / 2) * rel5_sh_m1_m11 + (23 / 24) * rel5_sh_m1_mm1 +
    (-265 / 192) * rel5_mob_0mmm1 + (1175 / 576) * rel5_sh_m_000m + (719 / 576) * rel5_sh_m_001m +
    (-1241 / 1152) * rel5_st_m_001m + (883 / 576) * rel5_sh_m_00m1 +
    (-509 / 576) * rel5_st_m_00m1 + (473 / 384) * rel5_sh_m_010m + (71 / 192) * rel5_sh_m_01m1 +
    (11 / 18) * rel5_sh_m_0m01 + (151 / 192) * rel5_sh_m_0m11 + (-161 / 576) * rel5_sh_m_m001 +
    (47 / 4608) * rel5_st_m_m001 + (89 / 1152) * rel5_st_m_m00m + (151 / 192) * rel5_sh_m_m011 +
    (39 / 128) * rel5_sh_m_m101 + (-3) * rel5_sh_m_m111 + (5273 / 9216) * rel5_st_01_01m +
    (-265 / 3072) * rel5_st_01_m0m + (-59 / 128) * rel5_st_0m_0m1 + (11 / 9) * rel5_st_0m_0mm +
    (-59 / 128) * rel5_st_0m_m01 + (-5431 / 2304) * rel5_sh_m_0001 + (-131 / 72) * rel5_sh_m_0011 +
    (395 / 1152) * rel5_st_m_0011 + (379 / 144) * rel5_st_m_00mm + (-1055 / 576) * rel5_sh_m_0101 +
    (-187 / 144) * rel5_st_m_010m + (-53 / 576) * rel5_st_m_01m1 + (55 / 24) * rel5_st_m_0m0m +
    (-121 / 576) * rel5_st_m_0m1m + (19 / 192) * rel5_st_m_m01m + (439 / 4608) * rel5_st_m_m0m1 +
    (-47 / 2304) * rel5_st_m_m101 + (-89 / 576) * rel5_st_m_m10m + (3 / 32) * rel5_st_m_m1m1 +
    (-437 / 1152) * rel5_sh_01_00m + (1 / 4) * rel5_sh_01_01m + (-5 / 16) * rel5_sh_01_0m1 +
    (1 / 16) * rel5_st_01_0m1 + (-473 / 384) * rel5_st_01_0mm + (5 / 4) * rel5_sh_01_m11 +
    (29 / 1152) * rel5_sh_0m_001 + (-59 / 128) * rel5_sh_0m_01m + (-5 / 4) * rel5_sh_m1_011 +
    (-151 / 384) * rel5_sh_m1_0m1 + (-151 / 384) * rel5_sh_m1_m01 + (35 / 4) * rel5_mob_00mmm +
    (119 / 128) * rel5_mob_01mmm + (37 / 12) * rel5_mob_0m0mm + (247 / 384) * rel5_mob_0m1mm +
    (-119 / 384) * rel5_mob_m10mm + (-125 / 288) * rel5_st_m_011m + (7 / 16) * rel5_st_m_01mm +
    (-119 / 384) * rel5_st_m_0m11 + (61 / 128) * rel5_st_m_0mm1 + (-119 / 384) * rel5_st_m_m011 +
    (13 / 16) * rel5_st_m_m0mm + (-19 / 144) * rel5_st_m_m11m + (-3 / 8) * rel5_st_m_m1mm +
    (161 / 288) * rel5_st_m_mm0m + (-55 / 144) * rel5_st_m_mm1m + (-3) * rel5_mob_0000m

theorem hpl_zero_negOne_one_negOne_negOne_at_one :
    hpl [zero, negOne, one, negOne, negOne] 1 =
      -3 * Li 4 (1 / 2) * log 2 - 5 * Li 5 (1 / 2) - 1 / 12 * log 2 ^ 5
      - 5 / 72 * log 2 ^ 3 * π ^ 2 + 21 / 16 * log 2 ^ 2 * zeta3
      - 49 / 1440 * log 2 * π ^ 4 - 7 / 32 * zeta3 * π ^ 2 + 247 / 32 * zeta5 := by
  linear_combination (-217 / 384) * hpl_zero_zero_zero_zero_one_at_one +
    (79 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (1199 / 384) * hpl_zero_zero_one_zero_one_at_one +
    (583 / 384) * hpl_zero_one_zero_zero_one_at_one + (-5 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-15 / 8) * hpl_zero_one_zero_one_one_at_one + (-5 / 8) * hpl_zero_one_one_zero_one_at_one +
    (20 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (-5) * hpl_negOne_one_one_one_one_at_one +
    (-175 / 384) * rel5_sh_m_mmmm + (-65 / 768) * rel5_sh_m_0mmm + (65 / 2304) * rel5_sh_m_m0mm +
    (-5 / 3) * rel5_sh_m_m1mm + (151 / 576) * rel5_sh_m_mm0m + (-59 / 256) * rel5_sh_m_mm1m +
    (-207 / 256) * rel5_sh_m_mmm1 + (-205 / 1024) * rel5_st_m_0001 +
    (-3665 / 2304) * rel5_st_m_000m + (-19 / 8) * rel5_sh_m_00mm + (-223 / 384) * rel5_sh_m_01mm +
    (-9 / 32) * rel5_sh_m_0m0m + (113 / 384) * rel5_sh_m_0m1m + (5 / 6) * rel5_sh_m_0mm1 +
    (-223 / 768) * rel5_sh_m_m01m + (53 / 192) * rel5_sh_m_m0m1 + (-367 / 768) * rel5_sh_m_m10m +
    (-5 / 2) * rel5_sh_m_m11m + (-85 / 32) * rel5_sh_m_m1m1 + (223 / 384) * rel5_sh_m_mm01 +
    (-291 / 1024) * rel5_st_01_00m + (-227 / 192) * rel5_st_0m_001 + (139 / 384) * rel5_sh_0m_00m +
    (4967 / 2304) * rel5_st_0m_00m + (29 / 48) * rel5_sh_0m_0mm + (5 / 6) * rel5_sh_m1_m11 +
    (-1 / 4) * rel5_sh_m1_mm1 + (-65 / 192) * rel5_mob_0mmm1 + (-1 / 24) * rel5_sh_m_000m +
    (275 / 192) * rel5_sh_m_001m + (-1181 / 1152) * rel5_st_m_001m + (301 / 192) * rel5_sh_m_00m1 +
    (-679 / 576) * rel5_st_m_00m1 + (431 / 384) * rel5_sh_m_010m + (19 / 192) * rel5_sh_m_01m1 +
    (-1 / 6) * rel5_sh_m_0m01 + (-97 / 192) * rel5_sh_m_0m11 + (-95 / 192) * rel5_sh_m_m001 +
    (343 / 4608) * rel5_st_m_m001 + (173 / 1152) * rel5_st_m_m00m + (47 / 192) * rel5_sh_m_m011 +
    (-59 / 384) * rel5_sh_m_m101 + (-5) * rel5_sh_m_m111 + (4529 / 9216) * rel5_st_01_01m +
    (-1379 / 9216) * rel5_st_01_m0m + (-5 / 6) * rel5_st_0m_0m1 + (13 / 6) * rel5_st_0m_0mm +
    (-1 / 12) * rel5_st_0m_m01 + (-1337 / 768) * rel5_sh_m_0001 + (-25 / 24) * rel5_sh_m_0011 +
    (545 / 384) * rel5_st_m_0011 + (133 / 48) * rel5_st_m_00mm + (-193 / 192) * rel5_sh_m_0101 +
    (-197 / 144) * rel5_st_m_010m + (-13 / 576) * rel5_st_m_01m1 + (151 / 72) * rel5_st_m_0m0m +
    (-221 / 576) * rel5_st_m_0m1m + (-59 / 576) * rel5_st_m_m01m + (-769 / 4608) * rel5_st_m_m0m1 +
    (-343 / 2304) * rel5_st_m_m101 + (-173 / 576) * rel5_st_m_m10m + (1 / 32) * rel5_st_m_m1m1 +
    (-17 / 128) * rel5_sh_01_00m + (1 / 12) * rel5_sh_01_01m + (-19 / 48) * rel5_sh_01_0m1 +
    (-5 / 16) * rel5_st_01_0m1 + (-257 / 384) * rel5_st_01_0mm + (2) * rel5_sh_01_m11 +
    (-7 / 128) * rel5_sh_0m_001 + (-119 / 384) * rel5_sh_0m_01m + (-7 / 6) * rel5_sh_m1_011 +
    (-143 / 384) * rel5_sh_m1_0m1 + (-47 / 384) * rel5_sh_m1_m01 + (7 / 2) * rel5_mob_00mmm +
    (223 / 128) * rel5_mob_01mmm + (1 / 4) * rel5_mob_0m0mm + (223 / 384) * rel5_mob_0m1mm +
    (-367 / 384) * rel5_mob_m10mm + (-35 / 96) * rel5_st_m_011m + (-7 / 48) * rel5_st_m_01mm +
    (-79 / 384) * rel5_st_m_0m11 + (-91 / 128) * rel5_st_m_0mm1 + (-367 / 384) * rel5_st_m_m011 +
    (83 / 48) * rel5_st_m_m0mm + (-1 / 48) * rel5_st_m_m11m + (-5 / 8) * rel5_st_m_m1mm +
    (95 / 96) * rel5_st_m_mm0m + (-7 / 16) * rel5_st_m_mm1m + (5 / 2) * rel5_st_m_0mmm +
    (-5) * rel5_mob_0000m

theorem hpl_zero_negOne_negOne_zero_one_at_one :
    hpl [zero, negOne, negOne, zero, one] 1 =
      -5 / 96 * zeta3 * π ^ 2 + 5 / 8 * zeta5 := by
  linear_combination (3) * hpl_zero_zero_zero_zero_one_at_one +
    (1 / 2) * hpl_zero_zero_one_zero_one_at_one + (1 / 2) * hpl_zero_one_zero_zero_one_at_one +
    (-2) * hpl_zero_zero_zero_zero_negOne_at_one + (3 / 2) * rel5_st_m_0001 +
    (-2) * rel5_st_m_000m + (-1 / 2) * rel5_sh_m_0m0m + (1 / 4) * rel5_st_01_00m +
    (1 / 4) * rel5_st_0m_001 + (-1 / 2) * rel5_sh_0m_00m + (-1) * rel5_st_0m_00m +
    (2) * rel5_sh_m_000m + (1 / 2) * rel5_sh_m_010m + (1 / 2) * rel5_sh_m_0m01 +
    (1 / 4) * rel5_st_01_01m + (-1 / 4) * rel5_st_01_m0m + (-1 / 4) * rel5_st_0m_0m1 +
    (-1 / 4) * rel5_st_0m_m01 + (-2) * rel5_sh_m_0001 + (-1 / 2) * rel5_sh_m_0101 +
    (-1 / 2) * rel5_st_m_010m + (1 / 2) * rel5_st_m_0m0m + (-1 / 2) * rel5_sh_01_00m +
    (-1) * rel5_st_01_0mm + (1 / 2) * rel5_sh_0m_001

theorem hpl_zero_negOne_negOne_zero_negOne_at_one :
    hpl [zero, negOne, negOne, zero, negOne] 1 =
      -23 / 96 * zeta3 * π ^ 2 + 177 / 64 * zeta5 := by
  linear_combination (-5 / 48) * hpl_zero_zero_zero_zero_one_at_one +
    (-13 / 4) * hpl_zero_zero_zero_one_one_at_one +
    (-119 / 48) * hpl_zero_zero_one_zero_one_at_one +
    (-43 / 48) * hpl_zero_one_zero_zero_one_at_one +
    (-1 / 4) * hpl_zero_zero_zero_zero_negOne_at_one + (-75 / 16) * rel5_sh_m_mmmm +
    (3 / 32) * rel5_sh_m_0mmm + (-1 / 32) * rel5_sh_m_m0mm + (-3 / 8) * rel5_sh_m_mm0m +
    (-133 / 32) * rel5_sh_m_mm1m + (-177 / 32) * rel5_sh_m_mmm1 + (-31 / 128) * rel5_st_m_0001 +
    (113 / 96) * rel5_st_m_000m + (5 / 3) * rel5_sh_m_00mm + (13 / 16) * rel5_sh_m_01mm +
    (-29 / 24) * rel5_sh_m_0m0m + (5 / 16) * rel5_sh_m_0m1m + (13 / 32) * rel5_sh_m_m01m +
    (-1 / 8) * rel5_sh_m_m0m1 + (21 / 32) * rel5_sh_m_m10m + (5 / 4) * rel5_sh_m_m1m1 +
    (-13 / 16) * rel5_sh_m_mm01 + (83 / 128) * rel5_st_01_00m + (-5 / 32) * rel5_st_0m_001 +
    (-1 / 6) * rel5_sh_0m_00m + (-103 / 96) * rel5_st_0m_00m + (13 / 6) * rel5_sh_0m_0mm +
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
    (1 / 24) * rel5_st_m_m10m + (-1 / 4) * rel5_st_m_m1m1 + (-13 / 48) * rel5_sh_01_00m +
    (-1 / 4) * rel5_sh_01_01m + (1 / 4) * rel5_sh_01_0m1 + (-25 / 16) * rel5_st_01_0mm +
    (-1) * rel5_sh_01_m11 + (25 / 48) * rel5_sh_0m_001 + (3 / 8) * rel5_sh_0m_01m +
    (1) * rel5_sh_m1_011 + (5 / 16) * rel5_sh_m1_0m1 + (13 / 16) * rel5_sh_m1_m01 +
    (-18) * rel5_mob_00mmm + (-39 / 16) * rel5_mob_01mmm + (-7) * rel5_mob_0m0mm +
    (-13 / 16) * rel5_mob_0m1mm + (21 / 16) * rel5_mob_m10mm + (5 / 12) * rel5_st_m_011m +
    (-1 / 2) * rel5_st_m_01mm + (5 / 16) * rel5_st_m_0m11 + (-5 / 16) * rel5_st_m_0mm1 +
    (21 / 16) * rel5_st_m_m011 + (-1 / 2) * rel5_st_m_m0mm + (1 / 6) * rel5_st_m_m11m +
    (-5 / 12) * rel5_st_m_mm0m + (1 / 6) * rel5_st_m_mm1m

theorem hpl_zero_negOne_negOne_one_one_at_one :
    hpl [zero, negOne, negOne, one, one] 1 =
      5 * Li 5 (1 / 2) - 1 / 24 * log 2 ^ 5 - 1 / 72 * log 2 ^ 3 * π ^ 2
      + 1 / 36 * log 2 * π ^ 4 - 1 / 32 * zeta3 * π ^ 2 - 123 / 32 * zeta5 := by
  linear_combination (3047 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (-193 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (-3265 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (-1577 / 1152) * hpl_zero_one_zero_zero_one_at_one +
    (3 / 2) * hpl_zero_zero_one_one_one_at_one + (11 / 8) * hpl_zero_one_zero_one_one_at_one +
    (11 / 24) * hpl_zero_one_one_zero_one_at_one +
    (-86 / 15) * hpl_zero_zero_zero_zero_negOne_at_one + (5) * hpl_negOne_one_one_one_one_at_one +
    (-1937 / 1920) * rel5_sh_m_mmmm + (109 / 768) * rel5_sh_m_0mmm +
    (-109 / 2304) * rel5_sh_m_m0mm + (5 / 3) * rel5_sh_m_m1mm + (-539 / 576) * rel5_sh_m_mm0m +
    (-1027 / 768) * rel5_sh_m_mm1m + (-253 / 256) * rel5_sh_m_mmm1 +
    (4727 / 15360) * rel5_st_m_0001 + (437 / 2304) * rel5_st_m_000m + (127 / 72) * rel5_sh_m_00mm +
    (499 / 384) * rel5_sh_m_01mm + (-287 / 288) * rel5_sh_m_0m0m + (131 / 384) * rel5_sh_m_0m1m +
    (-1 / 2) * rel5_sh_m_0mm1 + (115 / 768) * rel5_sh_m_m01m + (-73 / 192) * rel5_sh_m_m0m1 +
    (419 / 768) * rel5_sh_m_m10m + (5 / 2) * rel5_sh_m_m11m + (287 / 96) * rel5_sh_m_m1m1 +
    (-499 / 384) * rel5_sh_m_mm01 + (1859 / 5120) * rel5_st_01_00m + (1 / 16) * rel5_st_0m_001 +
    (-409 / 1152) * rel5_sh_0m_00m + (-2177 / 768) * rel5_st_0m_00m +
    (137 / 144) * rel5_sh_0m_0mm + (-5 / 6) * rel5_sh_m1_m11 + (-5 / 6) * rel5_sh_m1_mm1 +
    (109 / 192) * rel5_mob_0mmm1 + (373 / 288) * rel5_sh_m_000m + (-577 / 576) * rel5_sh_m_001m +
    (379 / 384) * rel5_st_m_001m + (-755 / 576) * rel5_sh_m_00m1 + (689 / 960) * rel5_st_m_00m1 +
    (-167 / 384) * rel5_sh_m_010m + (1 / 192) * rel5_sh_m_01m1 + (-1 / 18) * rel5_sh_m_0m01 +
    (-115 / 192) * rel5_sh_m_0m11 + (193 / 576) * rel5_sh_m_m001 + (-191 / 2560) * rel5_st_m_m001 +
    (-43 / 384) * rel5_st_m_m00m + (-227 / 192) * rel5_sh_m_m011 + (-113 / 384) * rel5_sh_m_m101 +
    (5) * rel5_sh_m_m111 + (-20689 / 46080) * rel5_st_01_01m + (-26941 / 46080) * rel5_st_01_m0m +
    (49 / 192) * rel5_st_0m_0m1 + (-29 / 18) * rel5_st_0m_0mm + (-21 / 64) * rel5_st_0m_m01 +
    (695 / 2304) * rel5_sh_m_0001 + (79 / 72) * rel5_sh_m_0011 + (-775 / 1152) * rel5_st_m_0011 +
    (-347 / 144) * rel5_st_m_00mm + (607 / 576) * rel5_sh_m_0101 + (181 / 144) * rel5_st_m_010m +
    (-11 / 320) * rel5_st_m_01m1 + (-133 / 72) * rel5_st_m_0m0m + (241 / 576) * rel5_st_m_0m1m +
    (71 / 576) * rel5_st_m_m01m + (-181 / 7680) * rel5_st_m_m0m1 + (191 / 1280) * rel5_st_m_m101 +
    (43 / 192) * rel5_st_m_m10m + (-47 / 480) * rel5_st_m_m1m1 + (13 / 1152) * rel5_sh_01_00m +
    (-1 / 12) * rel5_sh_01_01m + (5 / 16) * rel5_sh_01_0m1 + (1 / 16) * rel5_st_01_0m1 +
    (-145 / 128) * rel5_st_01_0mm + (-3 / 2) * rel5_sh_01_m11 + (299 / 1152) * rel5_sh_0m_001 +
    (175 / 384) * rel5_sh_0m_01m + (1) * rel5_sh_m1_011 + (355 / 384) * rel5_sh_m1_0m1 +
    (131 / 384) * rel5_sh_m1_m01 + (-11) * rel5_mob_00mmm + (-499 / 128) * rel5_mob_01mmm +
    (-13 / 4) * rel5_mob_0m0mm + (-371 / 384) * rel5_mob_0m1mm + (419 / 384) * rel5_mob_m10mm +
    (61 / 288) * rel5_st_m_011m + (1 / 16) * rel5_st_m_01mm + (65 / 128) * rel5_st_m_0m11 +
    (-35 / 384) * rel5_st_m_0mm1 + (419 / 384) * rel5_st_m_m011 + (-21 / 16) * rel5_st_m_m0mm +
    (23 / 144) * rel5_st_m_m11m + (5 / 8) * rel5_st_m_m1mm + (-193 / 288) * rel5_st_m_mm0m +
    (83 / 144) * rel5_st_m_mm1m + (-3 / 2) * rel5_st_m_0mmm + (-1) * rel5_mob_001mm +
    (5) * rel5_mob_0000m

theorem hpl_zero_negOne_negOne_one_negOne_at_one :
    hpl [zero, negOne, negOne, one, negOne] 1 =
      3 * Li 4 (1 / 2) * log 2 + Li 5 (1 / 2) + 7 / 60 * log 2 ^ 5
      + 1 / 72 * log 2 ^ 3 * π ^ 2 - 1 / 360 * log 2 * π ^ 4 + 7 / 32 * zeta3 * π ^ 2
      - 125 / 32 * zeta5 := by
  linear_combination (-249 / 128) * hpl_zero_zero_zero_zero_one_at_one +
    (5 / 16) * hpl_zero_zero_zero_one_one_at_one + (47 / 128) * hpl_zero_zero_one_zero_one_at_one +
    (7 / 128) * hpl_zero_one_zero_zero_one_at_one + (1 / 2) * hpl_zero_zero_one_one_one_at_one +
    (3 / 8) * hpl_zero_one_zero_one_one_at_one + (1 / 8) * hpl_zero_one_one_zero_one_at_one +
    (-1 / 3) * hpl_zero_zero_zero_zero_negOne_at_one + (1) * hpl_negOne_one_one_one_one_at_one +
    (2911 / 1920) * rel5_sh_m_mmmm + (157 / 768) * rel5_sh_m_0mmm +
    (-157 / 2304) * rel5_sh_m_m0mm + (1 / 3) * rel5_sh_m_m1mm + (229 / 576) * rel5_sh_m_mm0m +
    (495 / 256) * rel5_sh_m_mm1m + (435 / 256) * rel5_sh_m_mmm1 + (-647 / 1024) * rel5_st_m_0001 +
    (2989 / 2304) * rel5_st_m_000m + (5 / 24) * rel5_sh_m_00mm + (-253 / 384) * rel5_sh_m_01mm +
    (119 / 96) * rel5_sh_m_0m0m + (-205 / 384) * rel5_sh_m_0m1m + (-1 / 6) * rel5_sh_m_0mm1 +
    (-253 / 768) * rel5_sh_m_m01m + (-1 / 192) * rel5_sh_m_m0m1 + (-301 / 768) * rel5_sh_m_m10m +
    (1 / 2) * rel5_sh_m_m11m + (1 / 32) * rel5_sh_m_m1m1 + (253 / 384) * rel5_sh_m_mm01 +
    (-841 / 1024) * rel5_st_01_00m + (151 / 192) * rel5_st_0m_001 + (65 / 384) * rel5_sh_0m_00m +
    (1493 / 2304) * rel5_st_0m_00m + (-19 / 16) * rel5_sh_0m_0mm + (-1 / 6) * rel5_sh_m1_m11 +
    (5 / 4) * rel5_sh_m1_mm1 + (157 / 192) * rel5_mob_0mmm1 + (-53 / 24) * rel5_sh_m_000m +
    (19 / 64) * rel5_sh_m_001m + (-119 / 1152) * rel5_st_m_001m + (13 / 64) * rel5_sh_m_00m1 +
    (11 / 576) * rel5_st_m_00m1 + (-211 / 384) * rel5_sh_m_010m + (25 / 192) * rel5_sh_m_01m1 +
    (1 / 4) * rel5_sh_m_0m01 + (317 / 192) * rel5_sh_m_0m11 + (1 / 64) * rel5_sh_m_m001 +
    (229 / 4608) * rel5_st_m_m001 + (-25 / 1152) * rel5_st_m_m00m + (365 / 192) * rel5_sh_m_m011 +
    (367 / 384) * rel5_sh_m_m101 + (1) * rel5_sh_m_m111 + (-589 / 9216) * rel5_st_01_01m +
    (7927 / 9216) * rel5_st_01_m0m + (5 / 12) * rel5_st_0m_0m1 + (2 / 3) * rel5_st_0m_m01 +
    (1013 / 768) * rel5_sh_m_0001 + (-11 / 24) * rel5_sh_m_0011 + (-127 / 128) * rel5_st_m_0011 +
    (5 / 16) * rel5_st_m_00mm + (-83 / 192) * rel5_sh_m_0101 + (-11 / 144) * rel5_st_m_010m +
    (-7 / 576) * rel5_st_m_01m1 + (19 / 72) * rel5_st_m_0m0m + (73 / 576) * rel5_st_m_0m1m +
    (79 / 576) * rel5_st_m_m01m + (1757 / 4608) * rel5_st_m_m0m1 + (-229 / 2304) * rel5_st_m_m101 +
    (25 / 576) * rel5_st_m_m10m + (3 / 32) * rel5_st_m_m1m1 + (359 / 384) * rel5_sh_01_00m +
    (1 / 12) * rel5_sh_01_01m + (-1 / 48) * rel5_sh_01_0m1 + (1 / 16) * rel5_st_01_0m1 +
    (925 / 384) * rel5_st_01_0mm + (-383 / 384) * rel5_sh_0m_001 + (-101 / 384) * rel5_sh_0m_01m +
    (-1 / 6) * rel5_sh_m1_011 + (-269 / 384) * rel5_sh_m1_0m1 + (-365 / 384) * rel5_sh_m1_m01 +
    (13 / 2) * rel5_mob_00mmm + (253 / 128) * rel5_mob_01mmm + (11 / 4) * rel5_mob_0m0mm +
    (253 / 384) * rel5_mob_0m1mm + (-301 / 384) * rel5_mob_m10mm + (-3 / 32) * rel5_st_m_011m +
    (11 / 48) * rel5_st_m_01mm + (-205 / 384) * rel5_st_m_0m11 + (143 / 128) * rel5_st_m_0mm1 +
    (-301 / 384) * rel5_st_m_m011 + (-7 / 48) * rel5_st_m_m0mm + (-1 / 16) * rel5_st_m_m11m +
    (1 / 8) * rel5_st_m_m1mm + (-1 / 32) * rel5_st_m_mm0m + (1 / 48) * rel5_st_m_mm1m +
    (-1 / 2) * rel5_st_m_0mmm + (1) * rel5_mob_0000m

theorem hpl_zero_negOne_negOne_negOne_one_at_one :
    hpl [zero, negOne, negOne, negOne, one] 1 =
      Li 5 (1 / 2) - 1 / 120 * log 2 ^ 5 - 1 / 36 * log 2 ^ 3 * π ^ 2
      + 7 / 16 * log 2 ^ 2 * zeta3 + 1 / 720 * log 2 * π ^ 4 - 7 / 48 * zeta3 * π ^ 2
      + 15 / 16 * zeta5 := by
  linear_combination (1979 / 1152) * hpl_zero_zero_zero_zero_one_at_one +
    (-115 / 48) * hpl_zero_zero_zero_one_one_at_one +
    (-1957 / 1152) * hpl_zero_zero_one_zero_one_at_one +
    (-797 / 1152) * hpl_zero_one_zero_zero_one_at_one +
    (1 / 2) * hpl_zero_zero_one_one_one_at_one + (3 / 8) * hpl_zero_one_zero_one_one_at_one +
    (1 / 8) * hpl_zero_one_one_zero_one_at_one +
    (-11 / 6) * hpl_zero_zero_zero_zero_negOne_at_one + (1) * hpl_negOne_one_one_one_one_at_one +
    (-5309 / 1920) * rel5_sh_m_mmmm + (361 / 768) * rel5_sh_m_0mmm +
    (-361 / 2304) * rel5_sh_m_m0mm + (1 / 3) * rel5_sh_m_m1mm + (-191 / 576) * rel5_sh_m_mm0m +
    (-1735 / 768) * rel5_sh_m_mm1m + (-825 / 256) * rel5_sh_m_mmm1 +
    (1423 / 3072) * rel5_st_m_0001 + (-511 / 2304) * rel5_st_m_000m + (55 / 72) * rel5_sh_m_00mm +
    (247 / 384) * rel5_sh_m_01mm + (-413 / 288) * rel5_sh_m_0m0m + (199 / 384) * rel5_sh_m_0m1m +
    (1 / 6) * rel5_sh_m_0mm1 + (247 / 768) * rel5_sh_m_m01m + (-53 / 192) * rel5_sh_m_m0m1 +
    (359 / 768) * rel5_sh_m_m10m + (1 / 2) * rel5_sh_m_m11m + (41 / 32) * rel5_sh_m_m1m1 +
    (-247 / 384) * rel5_sh_m_mm01 + (2161 / 3072) * rel5_st_01_00m + (-1 / 3) * rel5_st_0m_001 +
    (-325 / 1152) * rel5_sh_0m_00m + (-383 / 256) * rel5_st_0m_00m + (209 / 144) * rel5_sh_0m_0mm +
    (-1 / 6) * rel5_sh_m1_m11 + (-5 / 3) * rel5_sh_m1_mm1 + (361 / 192) * rel5_mob_0mmm1 +
    (559 / 288) * rel5_sh_m_000m + (-469 / 576) * rel5_sh_m_001m + (69 / 128) * rel5_st_m_001m +
    (-503 / 576) * rel5_sh_m_00m1 + (275 / 576) * rel5_st_m_00m1 + (23 / 128) * rel5_sh_m_010m +
    (-35 / 192) * rel5_sh_m_01m1 + (-29 / 144) * rel5_sh_m_0m01 + (-61 / 64) * rel5_sh_m_0m11 +
    (109 / 576) * rel5_sh_m_m001 + (-239 / 4608) * rel5_st_m_m001 + (-5 / 128) * rel5_st_m_m00m +
    (-295 / 192) * rel5_sh_m_m011 + (-253 / 384) * rel5_sh_m_m101 + (1) * rel5_sh_m_m111 +
    (-659 / 3072) * rel5_st_01_01m + (-8005 / 9216) * rel5_st_01_m0m + (5 / 192) * rel5_st_0m_0m1 +
    (-65 / 72) * rel5_st_0m_0mm + (-107 / 192) * rel5_st_0m_m01 + (-421 / 2304) * rel5_sh_m_0001 +
    (67 / 72) * rel5_sh_m_0011 + (197 / 1152) * rel5_st_m_0011 + (-215 / 144) * rel5_st_m_00mm +
    (511 / 576) * rel5_sh_m_0101 + (47 / 72) * rel5_st_m_010m + (5 / 576) * rel5_st_m_01m1 +
    (-167 / 144) * rel5_st_m_0m0m + (13 / 576) * rel5_st_m_0m1m + (-61 / 576) * rel5_st_m_m01m +
    (-919 / 4608) * rel5_st_m_m0m1 + (239 / 2304) * rel5_st_m_m101 + (5 / 64) * rel5_st_m_m10m +
    (-5 / 32) * rel5_st_m_m1m1 + (-623 / 1152) * rel5_sh_01_00m + (-1 / 8) * rel5_sh_01_01m +
    (3 / 16) * rel5_sh_01_0m1 + (1 / 16) * rel5_st_01_0m1 + (-775 / 384) * rel5_st_01_0mm +
    (-5 / 6) * rel5_sh_01_m11 + (791 / 1152) * rel5_sh_0m_001 + (139 / 384) * rel5_sh_0m_01m +
    (2 / 3) * rel5_sh_m1_011 + (77 / 128) * rel5_sh_m1_0m1 + (295 / 384) * rel5_sh_m1_m01 +
    (-11) * rel5_mob_00mmm + (-247 / 128) * rel5_mob_01mmm + (-47 / 12) * rel5_mob_0m0mm +
    (-125 / 128) * rel5_mob_0m1mm + (359 / 384) * rel5_mob_m10mm + (73 / 288) * rel5_st_m_011m +
    (-3 / 16) * rel5_st_m_01mm + (45 / 128) * rel5_st_m_0m11 + (-77 / 128) * rel5_st_m_0mm1 +
    (359 / 384) * rel5_st_m_m011 + (-9 / 16) * rel5_st_m_m0mm + (11 / 144) * rel5_st_m_m11m +
    (1 / 8) * rel5_st_m_m1mm + (-109 / 288) * rel5_st_m_mm0m + (23 / 144) * rel5_st_m_mm1m +
    (-1 / 2) * rel5_st_m_0mmm + (1) * rel5_mob_0000m

theorem hpl_zero_negOne_negOne_negOne_negOne_at_one :
    hpl [zero, negOne, negOne, negOne, negOne] 1 =
      -Li 4 (1 / 2) * log 2 - Li 5 (1 / 2) - 1 / 30 * log 2 ^ 5
      + 1 / 36 * log 2 ^ 3 * π ^ 2 - 7 / 16 * log 2 ^ 2 * zeta3 + zeta5 := by
  linear_combination (-97 / 384) * hpl_zero_zero_zero_zero_one_at_one +
    (21 / 16) * hpl_zero_zero_zero_one_one_at_one +
    (335 / 384) * hpl_zero_zero_one_zero_one_at_one +
    (151 / 384) * hpl_zero_one_zero_zero_one_at_one + (-1 / 2) * hpl_zero_zero_one_one_one_at_one +
    (-3 / 8) * hpl_zero_one_zero_one_one_at_one + (-1 / 8) * hpl_zero_one_one_zero_one_at_one +
    (37 / 30) * hpl_zero_zero_zero_zero_negOne_at_one + (-1) * hpl_negOne_one_one_one_one_at_one +
    (2021 / 1920) * rel5_sh_m_mmmm + (-49 / 768) * rel5_sh_m_0mmm + (49 / 2304) * rel5_sh_m_m0mm +
    (-1 / 3) * rel5_sh_m_m1mm + (23 / 576) * rel5_sh_m_mm0m + (149 / 256) * rel5_sh_m_mm1m +
    (321 / 256) * rel5_sh_m_mmm1 + (-129 / 5120) * rel5_st_m_0001 +
    (-889 / 2304) * rel5_st_m_000m + (-13 / 24) * rel5_sh_m_00mm + (-47 / 384) * rel5_sh_m_01mm +
    (35 / 96) * rel5_sh_m_0m0m + (1 / 384) * rel5_sh_m_0m1m + (1 / 6) * rel5_sh_m_0mm1 +
    (-47 / 768) * rel5_sh_m_m01m + (13 / 192) * rel5_sh_m_m0m1 + (-95 / 768) * rel5_sh_m_m10m +
    (-1 / 2) * rel5_sh_m_m11m + (-25 / 32) * rel5_sh_m_m1m1 + (47 / 384) * rel5_sh_m_mm01 +
    (-479 / 5120) * rel5_st_01_00m + (-11 / 96) * rel5_st_0m_001 + (13 / 128) * rel5_sh_0m_00m +
    (1471 / 2304) * rel5_st_0m_00m + (-19 / 48) * rel5_sh_0m_0mm + (1 / 6) * rel5_sh_m1_m11 +
    (1 / 2) * rel5_sh_m1_mm1 + (-241 / 192) * rel5_mob_0mmm1 + (-9 / 32) * rel5_sh_m_000m +
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

end QED.Polylog.HPL
