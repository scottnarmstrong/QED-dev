/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersCoeffs
public import QED.Polylog.Zeta5
public import Mathlib.Analysis.Analytic.Basic

/-!
# Set (d) of `A₁⁽⁶⁾`: the master expansions as inputs, and the assembled combination

This file states the interface of set (d) "from master inputs".

**Masters.** `QED.ThreeLoopD.SetDMasters` bundles eleven functions of `ε` (with `d = 4 - 2ε`):
the Laporta–Remiddi masters `I₂, …, I₁₈` (Phys. Lett. B 379 (1996) 283, arXiv:hep-ph/9602417,
triple-cross family, normalization `((-i)/π^(n-2))³ ∫ dⁿk₁ dⁿk₂ dⁿk₃`), each divided by
`C(ε) = (π ^ ε Γ(1 + ε))³`. These are the functions whose expansions Laporta (2001,
arXiv:hep-ph/0111123, eqs. (2)–(17)) tabulates.

**Inputs.** `QED.ThreeLoopD.SetDMasters.Expansions` states, for each master, its truncated
Laurent expansion `Iⱼ C⁻¹ = Lⱼ(ε) + ε ^ (kⱼ + 1) Rⱼ(ε)` near `ε = 0`, with `Rⱼ` analytic at `0`
(`QED.ThreeLoopD.HasTruncLaurent`), where `kⱼ` is the order the assembly needs. The Laurent
polynomials `Lⱼ = setDLaurentIj` are the closed forms of the LR96 table, with the constants
`C₁, C₂` corrected by Laporta (2001), eqs. (18)–(23) (`QED.ThreeLoopD.laportaC1`,
`QED.ThreeLoopD.laportaC2`). They use `ζ(3) = zeta3`, `ζ(5) = zeta5`, `a₄ = Li 4 (1/2)`, `ln 2`
and `π`. These expansions are open inputs: nothing in this file proves them. The input for
`I₁₈` is proved in `QED.ThreeLoopD.SetDMastersGamma`.

**Combination.** `QED.ThreeLoopD.setDCombination M ε = ∑ⱼ (-1) ^ (lines j) cⱼ(4 - 2ε) Mⱼ(ε)`,
the sign being that between the survey's master basis and LR96's (`M_ours = (-1)^(lines)
Γ(1 + ε)³ Iⱼ C⁻¹`). The coefficients `cⱼ` (`QED.ThreeLoopD.setDCoeffIj`) already include the
`g - 2` projector and the overall factor, so the value at `ε → 0` is the coefficient of
`(α/π)³`; the common factor `Γ(1 + ε)³` (or any factor tending to `1`) does not change it
(`QED.ThreeLoopD.SetDMasters.Expansions.tendsto_mul`).

**Value.** `QED.ThreeLoopD.a1SixSetDJN` is the closed form quoted by Jegerlehner–Nyffeler
(Phys. Rept. 477 (2009) 1; analytic result of Laporta–Remiddi, Phys. Lett. B 265 (1991) 182),
`5/6 ζ₅ - 5/18 π²ζ₃ - 41/540 π⁴ - 2/3 π² ln²2 + 2/3 ln⁴2 + 16 a₄ - 4/3 ζ₃ - 24 π² ln 2
  + 931/54 π² + 5/9 = 0.371 005 292 107 220 840 821 …`.
-/

@[expose] public section

open Real QED.Polylog Filter Topology

namespace QED.ThreeLoopD

/-- Laporta (2001), eqs. (18)–(23): the constant `C₁` (corrected from LR96). -/
noncomputable def laportaC1 : ℂ :=
  2 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) + 25 / 12 * (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ)
    - 49 / 180 * (π : ℂ) ^ (4 : ℕ) - 49 / 4 * (zeta5 : ℂ) + (zeta3 : ℂ) - 1 / 3 * (π : ℂ) ^ (2 : ℕ)

/-- Laporta (2001), eqs. (18)–(23): the constant `C₂` (corrected from LR96). -/
noncomputable def laportaC2 : ℂ :=
  2 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) + 53 / 12 * (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ)
    - 2 / 15 * (π : ℂ) ^ (4 : ℕ) - 173 / 4 * (zeta5 : ℂ) + 18 * (zeta3 : ℂ) - 3 * (π : ℂ) ^ (2 : ℕ)

/-- The truncated Laurent expansion of `I₂ C⁻¹` through `ε ^ 1` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI2 (ε : ℂ) : ℂ :=
  (2 * (zeta3 : ℂ)) * ε⁻¹ +
  (-13 / 90 * (π : ℂ) ^ (4 : ℕ) + 10 * (zeta3 : ℂ) - 1 / 3 * (π : ℂ) ^ (2 : ℕ)) +
  (-4 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) - 85 / 6 * (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ)
    - 7 / 15 * (π : ℂ) ^ (4 : ℕ) + 6 * laportaC2 - 2 * laportaC1 + 385 / 2 * (zeta5 : ℂ)
    - 82 * (zeta3 : ℂ) + 16 * (π : ℂ) ^ (2 : ℕ)) * ε

/-- The truncated Laurent expansion of `I₃ C⁻¹` through `ε ^ 0` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI3 (ε : ℂ) : ℂ :=
  (1 / 3) * ε⁻¹ ^ (3 : ℕ) +
  (7 / 3) * ε⁻¹ ^ (2 : ℕ) +
  (31 / 3) * ε⁻¹ +
  (-2 / 15 * (π : ℂ) ^ (4 : ℕ) - 4 / 3 * (zeta3 : ℂ) + 103 / 3)

/-- The truncated Laurent expansion of `I₅ C⁻¹` through `ε ^ 1` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI5 (ε : ℂ) : ℂ :=
  (1 / 6) * ε⁻¹ ^ (3 : ℕ) +
  (3 / 2) * ε⁻¹ ^ (2 : ℕ) +
  (-1 / 3 * (π : ℂ) ^ (2 : ℕ) + 55 / 6) * ε⁻¹ +
  (-4 / 45 * (π : ℂ) ^ (4 : ℕ) - 14 / 3 * (zeta3 : ℂ) - 7 / 3 * (π : ℂ) ^ (2 : ℕ) + 95 / 2) +
  (-2 / 9 * (π : ℂ) ^ (4 : ℕ) + 2 * laportaC1 - 44 * (zeta3 : ℂ) - 29 / 3 * (π : ℂ) ^ (2 : ℕ)
    + 1351 / 6) * ε

/-- The truncated Laurent expansion of `I₈ C⁻¹` through `ε ^ 2` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI8 (ε : ℂ) : ℂ :=
  (-1) * ε⁻¹ ^ (3 : ℕ) +
  (-16 / 3) * ε⁻¹ ^ (2 : ℕ) +
  (-16) * ε⁻¹ +
  (2 * (zeta3 : ℂ) - 8 / 3 * (π : ℂ) ^ (2 : ℕ) - 20) +
  (16 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) - 3 / 10 * (π : ℂ) ^ (4 : ℕ) - 200 / 3 * (zeta3 : ℂ)
    - 28 * (π : ℂ) ^ (2 : ℕ) + 364 / 3) * ε +
  (-64 / 3 * (Real.log 2 : ℂ) ^ (4 : ℕ) - 80 / 3 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) ^ (2 : ℕ)
    + 168 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) + 21 * (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ)
    + 46 / 15 * (π : ℂ) ^ (4 : ℕ) - 512 * (Li 4 (1 / 2) : ℂ) - 126 * (zeta5 : ℂ) - 776 * (zeta3 : ℂ)
    - 188 * (π : ℂ) ^ (2 : ℕ) + 1244) * ε ^ (2 : ℕ)

/-- The truncated Laurent expansion of `I₉ C⁻¹` through `ε ^ 1` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI9 (ε : ℂ) : ℂ :=
  (-2 / 3) * ε⁻¹ ^ (3 : ℕ) +
  (-10 / 3) * ε⁻¹ ^ (2 : ℕ) +
  (-1 / 3 * (π : ℂ) ^ (2 : ℕ) - 26 / 3) * ε⁻¹ +
  (-16 / 3 * (zeta3 : ℂ) - 11 / 3 * (π : ℂ) ^ (2 : ℕ) - 2) +
  (16 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) - 13 / 45 * (π : ℂ) ^ (4 : ℕ) - 248 / 3 * (zeta3 : ℂ)
    - 73 / 3 * (π : ℂ) ^ (2 : ℕ) + 398 / 3) * ε

/-- The truncated Laurent expansion of `I₁₂ C⁻¹` through `ε ^ 2` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI12 (ε : ℂ) : ℂ :=
  ε⁻¹ ^ (3 : ℕ) +
  (7 / 2) * ε⁻¹ ^ (2 : ℕ) +
  (253 / 36) * ε⁻¹ +
  (2501 / 216) +
  (-64 / 9 * (π : ℂ) ^ (2 : ℕ) + 59437 / 1296) * ε +
  (256 / 3 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) - 1792 / 9 * (zeta3 : ℂ)
    - 2272 / 27 * (π : ℂ) ^ (2 : ℕ) + 2831381 / 7776) * ε ^ (2 : ℕ)

/-- The truncated Laurent expansion of `I₁₃ C⁻¹` through `ε ^ 2` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI13 (ε : ℂ) : ℂ :=
  (2) * ε⁻¹ ^ (3 : ℕ) +
  (23 / 3) * ε⁻¹ ^ (2 : ℕ) +
  (35 / 2) * ε⁻¹ +
  (275 / 12) +
  (112 / 3 * (zeta3 : ℂ) - 189 / 8) * ε +
  (32 / 3 * (Real.log 2 : ℂ) ^ (4 : ℕ) - 32 / 3 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) ^ (2 : ℕ)
    - 136 / 45 * (π : ℂ) ^ (4 : ℕ) + 256 * (Li 4 (1 / 2) : ℂ) + 280 * (zeta3 : ℂ)
    - 14917 / 48) * ε ^ (2 : ℕ)

/-- The truncated Laurent expansion of `I₁₄ C⁻¹` through `ε ^ 2` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI14 (ε : ℂ) : ℂ :=
  (1 / 3) * ε⁻¹ ^ (3 : ℕ) +
  (7 / 6) * ε⁻¹ ^ (2 : ℕ) +
  (25 / 12) * ε⁻¹ +
  (8 / 3 * (zeta3 : ℂ) - 5 / 24) +
  (-2 / 15 * (π : ℂ) ^ (4 : ℕ) + 28 / 3 * (zeta3 : ℂ) - 959 / 48) * ε +
  (-7 / 15 * (π : ℂ) ^ (4 : ℕ) + 48 * (zeta5 : ℂ) + 50 / 3 * (zeta3 : ℂ) - 10493 / 96) * ε ^ (2 : ℕ)

/-- The truncated Laurent expansion of `I₁₅ C⁻¹` through `ε ^ 2` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI15 (ε : ℂ) : ℂ :=
  (3 / 2) * ε⁻¹ ^ (3 : ℕ) +
  (23 / 4) * ε⁻¹ ^ (2 : ℕ) +
  (105 / 8) * ε⁻¹ +
  (4 / 3 * (π : ℂ) ^ (2 : ℕ) + 275 / 16) +
  (-8 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) + 28 * (zeta3 : ℂ) + 10 * (π : ℂ) ^ (2 : ℕ)
    - 567 / 32) * ε +
  (8 * (Real.log 2 : ℂ) ^ (4 : ℕ) + 16 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) ^ (2 : ℕ)
    - 60 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) - 62 / 45 * (π : ℂ) ^ (4 : ℕ)
    + 192 * (Li 4 (1 / 2) : ℂ) + 210 * (zeta3 : ℂ) + 145 / 3 * (π : ℂ) ^ (2 : ℕ)
    - 14917 / 64) * ε ^ (2 : ℕ)

/-- The truncated Laurent expansion of `I₁₆ C⁻¹` through `ε ^ 1` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI16 (ε : ℂ) : ℂ :=
  (1 / 2) * ε⁻¹ ^ (3 : ℕ) +
  (7 / 4) * ε⁻¹ ^ (2 : ℕ) +
  (1 / 3 * (π : ℂ) ^ (2 : ℕ) + 25 / 8) * ε⁻¹ +
  (4 * (zeta3 : ℂ) + 7 / 6 * (π : ℂ) ^ (2 : ℕ) - 5 / 16) +
  (16 / 45 * (π : ℂ) ^ (4 : ℕ) + 14 * (zeta3 : ℂ) + 25 / 12 * (π : ℂ) ^ (2 : ℕ) - 959 / 32) * ε

/-- The truncated Laurent expansion of `I₁₈ C⁻¹` through `ε ^ 2` (LR96 table, Laporta 2001). -/
noncomputable def setDLaurentI18 (ε : ℂ) : ℂ :=
  (-1) * ε⁻¹ ^ (3 : ℕ) +
  (-3) * ε⁻¹ ^ (2 : ℕ) +
  (-6) * ε⁻¹ +
  (-10) +
  (-15) * ε +
  (-21) * ε ^ (2 : ℕ)

/-- `f` has the truncated Laurent expansion `L` up to `O(ε ^ n)` at `0`: on a punctured
neighbourhood of `0`, `f ε = L ε + ε ^ n R ε` with `R` analytic at `0`. -/
def HasTruncLaurent (f L : ℂ → ℂ) (n : ℕ) : Prop :=
  ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ ε in 𝓝[≠] (0 : ℂ), f ε = L ε + ε ^ n * R ε

/-- The eleven masters of set (d), each in the normalization `Iⱼ C(ε)⁻¹` of Laporta–Remiddi
(1996) (`d = 4 - 2ε`, `C(ε) = (π ^ ε Γ(1 + ε))³`). -/
structure SetDMasters where
  /-- `I₂ C⁻¹` (Kira master `lbl[0,1,1,1,0,1,1,1,0]`, 6 lines). -/
  I2 : ℂ → ℂ
  /-- `I₃ C⁻¹` (Kira master `lbl[1,0,1,1,1,0,1,1,0]`, 6 lines). -/
  I3 : ℂ → ℂ
  /-- `I₅ C⁻¹` (Kira master `lbl[0,1,1,1,1,1,1,0,0]`, 6 lines). -/
  I5 : ℂ → ℂ
  /-- `I₈ C⁻¹` (Kira master `lbl[0,0,0,1,1,1,1,1,0]`, 5 lines). -/
  I8 : ℂ → ℂ
  /-- `I₉ C⁻¹` (Kira master `lbl[0,1,1,1,0,1,1,0,0]`, 5 lines). -/
  I9 : ℂ → ℂ
  /-- `I₁₂ C⁻¹` (Kira master `lbl[0,1,0,0,1,1,1,0,0]`, 4 lines). -/
  I12 : ℂ → ℂ
  /-- `I₁₃ C⁻¹` (Kira master `lbl[0,0,0,1,1,0,1,1,0]`, 4 lines). -/
  I13 : ℂ → ℂ
  /-- `I₁₄ C⁻¹` (Kira master `lbl[0,1,1,0,0,1,1,0,0]`, 4 lines). -/
  I14 : ℂ → ℂ
  /-- `I₁₅ C⁻¹` (Kira master `lbl[0,0,0,1,1,1,1,0,0]`, 4 lines). -/
  I15 : ℂ → ℂ
  /-- `I₁₆ C⁻¹` (Kira master `lbl[0,1,1,1,0,1,0,0,0]`, 4 lines). -/
  I16 : ℂ → ℂ
  /-- `I₁₈ C⁻¹` (Kira master `lbl[0,0,0,1,1,1,0,0,0]`, 3 lines). -/
  I18 : ℂ → ℂ

/-- **The master inputs of set (d)**: each master has its published truncated expansion, to the
order the assembly needs. -/
structure SetDMasters.Expansions (M : SetDMasters) : Prop where
  I2 : HasTruncLaurent M.I2 setDLaurentI2 2
  I3 : HasTruncLaurent M.I3 setDLaurentI3 1
  I5 : HasTruncLaurent M.I5 setDLaurentI5 2
  I8 : HasTruncLaurent M.I8 setDLaurentI8 3
  I9 : HasTruncLaurent M.I9 setDLaurentI9 2
  I12 : HasTruncLaurent M.I12 setDLaurentI12 3
  I13 : HasTruncLaurent M.I13 setDLaurentI13 3
  I14 : HasTruncLaurent M.I14 setDLaurentI14 3
  I15 : HasTruncLaurent M.I15 setDLaurentI15 3
  I16 : HasTruncLaurent M.I16 setDLaurentI16 2
  I18 : HasTruncLaurent M.I18 setDLaurentI18 3

/-- **The Jegerlehner–Nyffeler closed form of set (d)** (light-by-light, electron loop),
`≈ 0.371005292107220840821`. -/
noncomputable def a1SixSetDJN : ℝ :=
  5 / 6 * zeta5 - 5 / 18 * π ^ 2 * zeta3 - 41 / 540 * π ^ 4 - 2 / 3 * π ^ 2 * Real.log 2 ^ 2 +
    2 / 3 * Real.log 2 ^ 4 + 16 * Li 4 (1 / 2) - 4 / 3 * zeta3 - 24 * π ^ 2 * Real.log 2 +
    931 / 54 * π ^ 2 + 5 / 9

/-- **The set (d) combination** `∑ⱼ (-1) ^ (lines j) cⱼ(4 - 2ε) Mⱼ(ε)`. -/
noncomputable def setDCombination (M : SetDMasters) (ε : ℂ) : ℂ :=
  setDCoeffI2 ε * M.I2 ε + setDCoeffI3 ε * M.I3 ε + setDCoeffI5 ε * M.I5 ε - setDCoeffI8 ε * M.I8 ε
    - setDCoeffI9 ε * M.I9 ε + setDCoeffI12 ε * M.I12 ε + setDCoeffI13 ε * M.I13 ε
    + setDCoeffI14 ε * M.I14 ε + setDCoeffI15 ε * M.I15 ε + setDCoeffI16 ε * M.I16 ε
    - setDCoeffI18 ε * M.I18 ε

end QED.ThreeLoopD
