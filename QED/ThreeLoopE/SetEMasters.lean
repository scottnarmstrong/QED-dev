/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersProductsA
public import QED.ThreeLoopE.SetEMastersProductsB
public import QED.ThreeLoopD.SetDMasters
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (e) of `A₁⁽⁶⁾` from the master inputs

Under the seventeen master expansions `QED.ThreeLoopE.SetEMasters.Expansions`, the set (e)
combination `QED.ThreeLoopE.setECombination M ε = ∑ⱼ sⱼ cⱼ(4 - 2ε) Mⱼ(ε)` has no pole at
`ε = 0`, and its value there is the closed form `QED.ThreeLoopE.a1SixSetE`.

## Main results

* `QED.ThreeLoopE.setELaurentSum_eq`: the pole cancellation. The orders `≤ 0` of the seventeen
  products, `∑ⱼ sⱼ Sⱼ(ε)`, sum to the constant `a1SixSetE`: the coefficients of `ε⁻⁵, …, ε⁻¹`
  cancel exactly, `C₁` cancels and `C₂` enters the constant term with coefficient `-23/6`.
* `QED.ThreeLoopE.SetEMasters.Expansions.exists_analyticAt`: the combination agrees, on a
  punctured neighbourhood of `0`, with a function analytic at `0` whose value at `0` is
  `a1SixSetE` (no poles, and the value).
* `QED.ThreeLoopE.SetEMasters.Expansions.tendsto`, `…tendsto_mul`: the limit `ε → 0`, also after
  a normalization factor continuous at `0` with value `1` (such as `Γ(1 + ε)³`).
* `QED.ThreeLoopE.SetEMasters.ofLaurent_expansions`: the inputs are consistent.

## Proof

Each product `cⱼ Mⱼ` is `Sⱼ + ε gⱼ` near `0` with `gⱼ` analytic
(`QED.ThreeLoopE.setECoeffIj_mul`), and `∑ⱼ sⱼ Sⱼ = a1SixSetE` is an identity of Laurent
polynomials in `ε` over `ℚ[π², ζ₃, ζ₅, ln 2, a₄]`, checked by `ring`.
-/

@[expose] public section

open Filter Topology Real QED.Polylog QED.ThreeLoopD

namespace QED.ThreeLoopE

/-- **Pole cancellation and value**: the parts of order `≤ 0` of the seventeen products
sum to `a1SixSetE`. -/
theorem setELaurentSum_eq (ε : ℂ) :
    -setESI1 ε + setESI2 ε + setESI3 ε + setESI4 ε + setESI5 ε + setESI6 ε + setESI7 ε - setESI8 ε
      - setESI9 ε - setESI10 ε + setESI12 ε + setESI13 ε + setESI14 ε + setESI15 ε + setESI16 ε
      + setESI17 ε - setESI18 ε = (a1SixSetE : ℂ) := by
  simp only [setESI1, setESI2, setESI3, setESI4, setESI5, setESI6, setESI7, setESI8, setESI9,
    setESI10, setESI12, setESI13, setESI14, setESI15, setESI16, setESI17, setESI18, laportaC1,
    laportaC2, a1SixSetE]
  push_cast
  ring

/-- **Set (e) from master inputs: no poles, and the value.** Under the seventeen master
expansions, the set (e) combination agrees on a punctured neighbourhood of `ε = 0` with a
function analytic at `0`, whose value at `0` is `a1SixSetE`. -/
theorem SetEMasters.Expansions.exists_analyticAt {M : SetEMasters} (h : M.Expansions) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = (a1SixSetE : ℂ) ∧
      ∀ᶠ ε in 𝓝[≠] (0 : ℂ), setECombination M ε = g ε := by
  obtain ⟨g1, hg1, e1⟩ := setECoeffI1_mul h.I1
  obtain ⟨g2, hg2, e2⟩ := setECoeffI2_mul h.I2
  obtain ⟨g3, hg3, e3⟩ := setECoeffI3_mul h.I3
  obtain ⟨g4, hg4, e4⟩ := setECoeffI4_mul h.I4
  obtain ⟨g5, hg5, e5⟩ := setECoeffI5_mul h.I5
  obtain ⟨g6, hg6, e6⟩ := setECoeffI6_mul h.I6
  obtain ⟨g7, hg7, e7⟩ := setECoeffI7_mul h.I7
  obtain ⟨g8, hg8, e8⟩ := setECoeffI8_mul h.I8
  obtain ⟨g9, hg9, e9⟩ := setECoeffI9_mul h.I9
  obtain ⟨g10, hg10, e10⟩ := setECoeffI10_mul h.I10
  obtain ⟨g12, hg12, e12⟩ := setECoeffI12_mul h.I12
  obtain ⟨g13, hg13, e13⟩ := setECoeffI13_mul h.I13
  obtain ⟨g14, hg14, e14⟩ := setECoeffI14_mul h.I14
  obtain ⟨g15, hg15, e15⟩ := setECoeffI15_mul h.I15
  obtain ⟨g16, hg16, e16⟩ := setECoeffI16_mul h.I16
  obtain ⟨g17, hg17, e17⟩ := setECoeffI17_mul h.I17
  obtain ⟨g18, hg18, e18⟩ := setECoeffI18_mul h.I18
  refine ⟨fun ε => (a1SixSetE : ℂ) + ε * (
      -g1 ε + g2 ε + g3 ε + g4 ε + g5 ε + g6 ε + g7 ε - g8 ε - g9 ε - g10 ε + g12 ε + g13 ε + g14 ε
        + g15 ε + g16 ε + g17 ε - g18 ε), by fun_prop, by simp, ?_⟩
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e12, e13, e14, e15, e16, e17, e18]
    with ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12 h13 h14 h15 h16 h17 h18
  rw [setECombination]
  linear_combination (-1 : ℂ) * h1 + h2 + h3 + h4 + h5 + h6 + h7 - h8 - h9 - h10 + h12 + h13 + h14
    + h15 + h16 + h17 - h18 + setELaurentSum_eq ε

/-- **Set (e) from master inputs, as a limit**: `setECombination M ε → a1SixSetE` as `ε → 0`,
`ε ≠ 0`. -/
theorem SetEMasters.Expansions.tendsto {M : SetEMasters} (h : M.Expansions) :
    Tendsto (setECombination M) (𝓝[≠] (0 : ℂ)) (𝓝 (a1SixSetE : ℂ)) := by
  obtain ⟨g, hg, hg0, he⟩ := h.exists_analyticAt
  have hgt : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (a1SixSetE : ℂ)) :=
    hg0 ▸ hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact hgt.congr' (he.mono fun _ h => h.symm)

/-- The same limit after multiplying by a normalization factor `N` continuous at `0` with
`N 0 = 1` (for instance `Γ(1 + ε)³`, which relates the survey's master basis to LR96's). -/
theorem SetEMasters.Expansions.tendsto_mul {M : SetEMasters} (h : M.Expansions) {N : ℂ → ℂ}
    (hN : ContinuousAt N 0) (hN0 : N 0 = 1) :
    Tendsto (fun ε => N ε * setECombination M ε) (𝓝[≠] (0 : ℂ)) (𝓝 (a1SixSetE : ℂ)) := by
  simpa [hN0] using (hN.tendsto.mono_left nhdsWithin_le_nhds).mul h.tendsto

/-- The truncated expansions themselves, as masters. -/
noncomputable def SetEMasters.ofLaurent : SetEMasters :=
  { I2 := setDLaurentI2, I3 := setELaurentI3, I5 := setDLaurentI5, I8 := setDLaurentI8,
    I9 := setDLaurentI9, I12 := setDLaurentI12, I13 := setDLaurentI13, I14 := setDLaurentI14,
    I15 := setDLaurentI15, I16 := setDLaurentI16, I18 := setDLaurentI18, I1 := setELaurentI1,
    I4 := setELaurentI4, I6 := setELaurentI6, I7 := setELaurentI7, I10 := setELaurentI10,
    I17 := setELaurentI17 }

/-- The inputs are consistent: the truncated expansions satisfy them. -/
theorem SetEMasters.ofLaurent_expansions : SetEMasters.ofLaurent.Expansions where
  I1 := hasTruncLaurent_self _ _
  I2 := hasTruncLaurent_self _ _
  I3 := hasTruncLaurent_self _ _
  I4 := hasTruncLaurent_self _ _
  I5 := hasTruncLaurent_self _ _
  I6 := hasTruncLaurent_self _ _
  I7 := hasTruncLaurent_self _ _
  I8 := hasTruncLaurent_self _ _
  I9 := hasTruncLaurent_self _ _
  I10 := hasTruncLaurent_self _ _
  I12 := hasTruncLaurent_self _ _
  I13 := hasTruncLaurent_self _ _
  I14 := hasTruncLaurent_self _ _
  I15 := hasTruncLaurent_self _ _
  I16 := hasTruncLaurent_self _ _
  I17 := hasTruncLaurent_self _ _
  I18 := hasTruncLaurent_self _ _

end QED.ThreeLoopE
