/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersCoeffsA
public import QED.ThreeLoopE.SetEMastersCoeffsB
public import QED.ThreeLoopD.SetDMastersLaurent
import Mathlib.Analysis.Analytic.Constructions

/-!
# Set (e) of `A₁⁽⁶⁾`: the master expansions as inputs, and the combination

This file states the interface of set (e) "from master inputs", in the conventions of set (d)
(`QED.ThreeLoopD.SetDMastersLaurent`), whose masters, truncated expansions and constants it
reuses.

**Masters.** `QED.ThreeLoopE.SetEMasters` extends the eleven set (d) masters
`QED.ThreeLoopD.SetDMasters` by the six masters `I₁, I₄, I₆, I₇, I₁₀, I₁₇` of Laporta–Remiddi
(Phys. Lett. B 379 (1996) 283), each in the normalization `Iⱼ C(ε)⁻¹`, `C(ε) = (π ^ ε Γ(1 + ε))³`.
The masters `I₁₁` and Kira's `J₀` do not appear: the reduction has eliminated them
(`QED.ThreeLoopE.SetEMastersCoeffsA`).

**Inputs.** `QED.ThreeLoopE.SetEMasters.Expansions` states, for each master, a truncated Laurent
expansion `Iⱼ C⁻¹ = Lⱼ(ε) + ε ^ (pⱼ + 1) Rⱼ(ε)` with `Rⱼ` analytic at `0`
(`QED.ThreeLoopD.HasTruncLaurent`), where `pⱼ` is the pole order of the coefficient of the master.
For the ten masters shared with set (d) other than `I₃`, `Lⱼ` is the set (d) target
`QED.ThreeLoopD.setDLaurentIj`; since set (e) never needs a deeper order than set (d) for them,
the hypotheses are implied by the set (d) ones (`QED.ThreeLoopE.SetEMasters.Expansions.ofSetD`).
`I₃` is needed one order deeper, through `ε ^ 1` (`QED.ThreeLoopE.setELaurentI3`). The new
targets are the closed forms of the LR96 table with the constants `C₁, C₂` corrected by Laporta
(2001, arXiv:hep-ph/0111123, eqs. (18)–(23)), `QED.ThreeLoopD.laportaC1`,
`QED.ThreeLoopD.laportaC2`. In the combination `C₁` cancels and `C₂` survives, with coefficient
`-23/6`. These expansions are open inputs: nothing in this file proves them.

**Combination.** `QED.ThreeLoopE.setECombination M ε = ∑ⱼ sⱼ cⱼ(4 - 2ε) Mⱼ(ε)`, with the sign
`sⱼ = (-1) ^ (lines j)` between the survey's master basis and LR96's, and an extra `-1` for the
numerator master `I₁` (so `s = -1` for `I₁, I₈, I₉, I₁₀, I₁₈` and `s = 1` otherwise). The
coefficients include the `g - 2` projector and the overall factor, so the value at `ε → 0` is the
coefficient of `(α/π)³`.

**Value.** `QED.ThreeLoopE.a1SixSetE`, the closed form of the exact assembly of the survey,
`20a₄/3 + 5ln⁴2/18 - 5π²ln²2/18 - 22π²ln2/3 - 139π⁴/2160 + 103π²ζ₃/72 + 23π²/6 + 241ζ₃/24`
`- 235ζ₅/24 - 101/64 = 0.904 979 269 167 493 194 536 633 31…`; numerically it agrees to 26 digits
with `LR96 (5) - (a) - (b) - (c) - (d)`.
-/

@[expose] public section

open Real QED.Polylog Filter Topology QED.ThreeLoopD

namespace QED.ThreeLoopE

/-- The truncated Laurent expansion of `I₁ C⁻¹`: the finite value `5ζ₅ - π²ζ₃/2` (LR96). -/
noncomputable def setELaurentI1 (_ε : ℂ) : ℂ :=
  (-1 / 2 * (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ) + 5 * (zeta5 : ℂ))

/-- The `ε ^ 1` coefficient of `I₃ C⁻¹` (LR96 table, Laporta 2001). -/
noncomputable def setEI3EpsOne : ℂ :=
  -8 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) - 25 / 3 * (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ)
    - 1 / 15 * (π : ℂ) ^ (4 : ℕ) + 4 * laportaC2 + 95 * (zeta5 : ℂ) - 184 / 3 * (zeta3 : ℂ)
    + 44 / 3 * (π : ℂ) ^ (2 : ℕ) + 235 / 3

/-- The truncated Laurent expansion of `I₃ C⁻¹` through `ε ^ 1`: the set (d) target
`QED.ThreeLoopD.setDLaurentI3` (through `ε ^ 0`) plus the `ε ^ 1` term. -/
noncomputable def setELaurentI3 (ε : ℂ) : ℂ :=
  setDLaurentI3 ε + setEI3EpsOne * ε

/-- The truncated Laurent expansion of `I₄ C⁻¹`: through `ε ^ 1` (LR96 table, Laporta 2001). -/
noncomputable def setELaurentI4 (ε : ℂ) : ℂ :=
  2 * (zeta3 : ℂ) * ε⁻¹ +
  (-7 / 90 * (π : ℂ) ^ (4 : ℕ) + 2 * (zeta3 : ℂ) + 1 / 3 * (π : ℂ) ^ (2 : ℕ)) +
  (-4 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) - 85 / 6 * (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ)
    - 7 / 15 * (π : ℂ) ^ (4 : ℕ) + 4 * laportaC2 - 2 * laportaC1 + 385 / 2 * (zeta5 : ℂ)
    - 82 * (zeta3 : ℂ) + 16 * (π : ℂ) ^ (2 : ℕ)) * ε

/-- The truncated Laurent expansion of `I₆ C⁻¹`: through `ε ^ 1` (LR96 table, Laporta 2001). -/
noncomputable def setELaurentI6 (ε : ℂ) : ℂ :=
  1 / 3 * ε⁻¹ ^ (3 : ℕ) +
  7 / 3 * ε⁻¹ ^ (2 : ℕ) +
  31 / 3 * ε⁻¹ +
  (-4 / 45 * (π : ℂ) ^ (4 : ℕ) + 2 / 3 * (zeta3 : ℂ) + 1 / 3 * (π : ℂ) ^ (2 : ℕ) + 103 / 3) +
  (-4 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) - 7 / 2 * (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ)
    + 11 / 45 * (π : ℂ) ^ (4 : ℕ) + 2 * laportaC1 + 45 / 2 * (zeta5 : ℂ) + 14 / 3 * (zeta3 : ℂ)
    + 14 / 3 * (π : ℂ) ^ (2 : ℕ) + 235 / 3) * ε

/-- The truncated Laurent expansion of `I₇ C⁻¹`: through `ε ^ 1` (LR96 table, Laporta 2001). -/
noncomputable def setELaurentI7 (ε : ℂ) : ℂ :=
  1 / 6 * ε⁻¹ ^ (3 : ℕ) +
  3 / 2 * ε⁻¹ ^ (2 : ℕ) +
  (-1 / 3 * (π : ℂ) ^ (2 : ℕ) + 55 / 6) * ε⁻¹ +
  (-1 / 15 * (π : ℂ) ^ (4 : ℕ) - 8 / 3 * (zeta3 : ℂ) - 2 * (π : ℂ) ^ (2 : ℕ) + 95 / 2) +
  (-4 * (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) - 17 / 6 * (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ)
    - 7 / 9 * (π : ℂ) ^ (4 : ℕ) + 2 * laportaC2 + 45 / 2 * (zeta5 : ℂ) - 50 * (zeta3 : ℂ)
    + 1 / 3 * (π : ℂ) ^ (2 : ℕ) + 1351 / 6) * ε

/-- The truncated Laurent expansion of `I₁₀ C⁻¹`: through `ε ^ 1` (LR96 table, Laporta 2001). -/
noncomputable def setELaurentI10 (ε : ℂ) : ℂ :=
  (-1 / 3) * ε⁻¹ ^ (3 : ℕ) +
  (-5 / 3) * ε⁻¹ ^ (2 : ℕ) +
  (-2 / 3 * (π : ℂ) ^ (2 : ℕ) - 4) * ε⁻¹ +
  (-26 / 3 * (zeta3 : ℂ) - 7 / 3 * (π : ℂ) ^ (2 : ℕ) + 10 / 3) +
  (-35 / 18 * (π : ℂ) ^ (4 : ℕ) - 94 / 3 * (zeta3 : ℂ) - (π : ℂ) ^ (2 : ℕ) + 302 / 3) * ε

/-- The truncated Laurent expansion of `I₁₇ C⁻¹`: through `ε ^ 1` (LR96 table, Laporta 2001). -/
noncomputable def setELaurentI17 (ε : ℂ) : ℂ :=
  (-1 / 6) * ε⁻¹ ^ (2 : ℕ) +
  (-35 / 36) * ε⁻¹ +
  (-1 / 3 * (π : ℂ) ^ (2 : ℕ) - 559 / 216) +
  (-16 / 3 * (zeta3 : ℂ) - 35 / 18 * (π : ℂ) ^ (2 : ℕ) + 2737 / 1296) * ε

/-- The seventeen masters of set (e): the eleven of set (d) and six more, each in the
normalization `Iⱼ C(ε)⁻¹` of Laporta–Remiddi (1996). -/
structure SetEMasters extends SetDMasters where
  /-- `I₁ C⁻¹` (triple cross with numerator, 8 lines). -/
  I1 : ℂ → ℂ
  /-- `I₄ C⁻¹` (6 lines). -/
  I4 : ℂ → ℂ
  /-- `I₆ C⁻¹` (6 lines). -/
  I6 : ℂ → ℂ
  /-- `I₇ C⁻¹` (6 lines). -/
  I7 : ℂ → ℂ
  /-- `I₁₀ C⁻¹` (5 lines). -/
  I10 : ℂ → ℂ
  /-- `I₁₇ C⁻¹` (4 lines). -/
  I17 : ℂ → ℂ

/-- **The master inputs of set (e)**: each master has its published truncated expansion, to the
order `pⱼ` the assembly needs (remainder `O(ε ^ (pⱼ + 1))`). -/
structure SetEMasters.Expansions (M : SetEMasters) : Prop where
  I1 : HasTruncLaurent M.I1 setELaurentI1 1
  I2 : HasTruncLaurent M.I2 setDLaurentI2 2
  I3 : HasTruncLaurent M.I3 setELaurentI3 2
  I4 : HasTruncLaurent M.I4 setELaurentI4 2
  I5 : HasTruncLaurent M.I5 setDLaurentI5 2
  I6 : HasTruncLaurent M.I6 setELaurentI6 2
  I7 : HasTruncLaurent M.I7 setELaurentI7 2
  I8 : HasTruncLaurent M.I8 setDLaurentI8 3
  I9 : HasTruncLaurent M.I9 setDLaurentI9 2
  I10 : HasTruncLaurent M.I10 setELaurentI10 2
  I12 : HasTruncLaurent M.I12 setDLaurentI12 2
  I13 : HasTruncLaurent M.I13 setDLaurentI13 3
  I14 : HasTruncLaurent M.I14 setDLaurentI14 3
  I15 : HasTruncLaurent M.I15 setDLaurentI15 3
  I16 : HasTruncLaurent M.I16 setDLaurentI16 2
  I17 : HasTruncLaurent M.I17 setELaurentI17 2
  I18 : HasTruncLaurent M.I18 setDLaurentI18 3

/-- **The closed form of set (e)** (no closed electron loop),
`≈ 0.904979269167493194536633315`. -/
noncomputable def a1SixSetE : ℝ :=
  20 / 3 * Li 4 (1 / 2) + 5 / 18 * Real.log 2 ^ 4 - 5 / 18 * π ^ 2 * Real.log 2 ^ 2
    - 22 / 3 * π ^ 2 * Real.log 2 - 139 / 2160 * π ^ 4 + 103 / 72 * π ^ 2 * zeta3 + 23 / 6 * π ^ 2
    + 241 / 24 * zeta3 - 235 / 24 * zeta5 - 101 / 64

/-- **The set (e) combination** `∑ⱼ sⱼ cⱼ(4 - 2ε) Mⱼ(ε)`. -/
noncomputable def setECombination (M : SetEMasters) (ε : ℂ) : ℂ :=
  -(setECoeffI1 ε * M.I1 ε) + setECoeffI2 ε * M.I2 ε + setECoeffI3 ε * M.I3 ε
    + setECoeffI4 ε * M.I4 ε + setECoeffI5 ε * M.I5 ε + setECoeffI6 ε * M.I6 ε
    + setECoeffI7 ε * M.I7 ε - setECoeffI8 ε * M.I8 ε - setECoeffI9 ε * M.I9 ε
    - setECoeffI10 ε * M.I10 ε + setECoeffI12 ε * M.I12 ε + setECoeffI13 ε * M.I13 ε
    + setECoeffI14 ε * M.I14 ε + setECoeffI15 ε * M.I15 ε + setECoeffI16 ε * M.I16 ε
    + setECoeffI17 ε * M.I17 ε - setECoeffI18 ε * M.I18 ε

/-- A coefficient times a master with a truncated expansion: if, pointwise,
`c (L + ε ^ n r) = S + ε (A + B r)` with `A`, `B` analytic at `0`, then `c f = S + ε g` near `0`
with `g` analytic at `0`. -/
theorem _root_.QED.ThreeLoopD.HasTruncLaurent.coeff_mul {f L c S A B U : ℂ → ℂ} {n : ℕ}
    (hf : HasTruncLaurent f L n) (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (hU : ContinuousAt U 0) (hU0 : U 0 ≠ 0)
    (h : ∀ ε, ε ≠ 0 → U ε ≠ 0 → ∀ r, c ε * (L ε + ε ^ n * r) = S ε + ε * (A ε + B ε * r)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ᶠ ε in 𝓝[≠] (0 : ℂ), c ε * f ε = S ε + ε * g ε := by
  obtain ⟨R, hR, hfR⟩ := hf
  refine ⟨fun ε => A ε + B ε * R ε, hA.add (hB.mul hR), ?_⟩
  have hq : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), U ε ≠ 0 := nhdsWithin_le_nhds (hU.eventually_ne hU0)
  filter_upwards [hfR, hq, self_mem_nhdsWithin] with ε h1 h2 h3
  rw [h1]
  exact h ε h3 h2 (R ε)

/-- A truncated expansion to a higher order gives one to any lower order. -/
theorem _root_.QED.ThreeLoopD.HasTruncLaurent.of_le {f L : ℂ → ℂ} {m n : ℕ}
    (h : HasTruncLaurent f L n) (hmn : m ≤ n) : HasTruncLaurent f L m := by
  obtain ⟨R, hR, hfR⟩ := h
  refine ⟨fun ε => ε ^ (n - m) * R ε, by fun_prop, ?_⟩
  filter_upwards [hfR] with ε h1
  rw [h1, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]

/-- The set (e) input for `I₃` (through `ε ^ 1`) implies the set (d) one (through `ε ^ 0`). -/
theorem hasTruncLaurent_setDLaurentI3_of {f : ℂ → ℂ} (h : HasTruncLaurent f setELaurentI3 2) :
    HasTruncLaurent f setDLaurentI3 1 := by
  obtain ⟨R, hR, hfR⟩ := h
  refine ⟨fun ε => setEI3EpsOne + ε * R ε, by fun_prop, ?_⟩
  filter_upwards [hfR] with ε h1
  rw [h1, setELaurentI3]
  ring

/-- The set (d) inputs, with the six new masters and `I₃` through `ε ^ 1`, give the set (e)
inputs. -/
theorem SetEMasters.Expansions.ofSetD {M : SetEMasters} (hd : M.toSetDMasters.Expansions)
    (h1 : HasTruncLaurent M.I1 setELaurentI1 1)
    (h3 : HasTruncLaurent M.I3 setELaurentI3 2)
    (h4 : HasTruncLaurent M.I4 setELaurentI4 2)
    (h6 : HasTruncLaurent M.I6 setELaurentI6 2)
    (h7 : HasTruncLaurent M.I7 setELaurentI7 2)
    (h10 : HasTruncLaurent M.I10 setELaurentI10 2)
    (h17 : HasTruncLaurent M.I17 setELaurentI17 2) :
    M.Expansions where
  I1 := h1
  I2 := hd.I2
  I3 := h3
  I4 := h4
  I5 := hd.I5
  I6 := h6
  I7 := h7
  I8 := hd.I8
  I9 := hd.I9
  I10 := h10
  I12 := hd.I12.of_le (by norm_num)
  I13 := hd.I13
  I14 := hd.I14
  I15 := hd.I15
  I16 := hd.I16
  I17 := h17
  I18 := hd.I18

end QED.ThreeLoopE
