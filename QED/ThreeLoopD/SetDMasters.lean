/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersLaurent
public import QED.ThreeLoopD.SetDMastersPoles
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (d) of `A₁⁽⁶⁾` from the master inputs

Under the eleven master expansions `QED.ThreeLoopD.SetDMasters.Expansions`, the set (d)
combination `QED.ThreeLoopD.setDCombination M ε = ∑ⱼ (-1) ^ (lines j) cⱼ(4 - 2ε) Mⱼ(ε)` has no
pole at `ε = 0`, and its value there is the Jegerlehner–Nyffeler closed form
`QED.ThreeLoopD.a1SixSetDJN`.

## Main results

* `QED.ThreeLoopD.setDCombination_eq_of`: the exact pointwise identity. For `ε ≠ 0` with
  `setDDen ε ≠ 0`, if `Mⱼ(ε) = Lⱼ(ε) + ε ^ (kⱼ + 1) rⱼ` for each master, then
  `setDCombination M ε = a1SixSetDJN + ε (setDRegular ε + setDRemainder ε r…)`.
* `QED.ThreeLoopD.SetDMasters.Expansions.exists_analyticAt`: the combination agrees, on a
  punctured neighbourhood of `0`, with a function analytic at `0` whose value at `0` is
  `a1SixSetDJN` (no poles, and the value).
* `QED.ThreeLoopD.SetDMasters.Expansions.tendsto`: `setDCombination M ε → a1SixSetDJN` as
  `ε → 0`, `ε ≠ 0`.
* `QED.ThreeLoopD.SetDMasters.Expansions.tendsto_mul`: the same after multiplying by any
  normalization factor continuous at `0` with value `1` (such as `Γ(1 + ε)³`, between the
  survey's master basis and LR96's).
* `QED.ThreeLoopD.SetDMasters.ofLaurent_expansions`: the inputs are consistent (the truncated
  expansions themselves satisfy them).

## Proof

Each coefficient is brought to the common denominator `ε ^ pⱼ setDDen ε`
(`QED.ThreeLoopD.setDCoeffIj_eq`). Then, with `ε ≠ 0`, the combination is
`(∑_κ κ P_κ(ε)) / (ε⁵ setDDen ε) + ε setDRemainder` (`field_simp`, `ring`), the sum running over
the ten constants. The pole cancellation and the value are the ten univariate identities
`P_κ = ε⁵ (v_κ setDDen + ε G_κ)` of `QED.ThreeLoopD.SetDMastersPoles`. Since every remainder
enters as `ε ^ (kⱼ + 1 - pⱼ) = ε` times an analytic function, the remainders do not affect the
value.
-/

@[expose] public section

open Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- The numerator of the truncated combination: `∑_κ κ P_κ(ε)` over the ten constants. -/
noncomputable def setDNumer (ε : ℂ) : ℂ :=
  setDPOne ε + (π : ℂ) ^ (2 : ℕ) * setDPPi2 ε + (zeta3 : ℂ) * setDPZ3 ε +
    (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) * setDPPi2L2 ε + (π : ℂ) ^ (4 : ℕ) * setDPPi4 ε +
    (Li 4 (1 / 2) : ℂ) * setDPA4 ε + (Real.log 2 : ℂ) ^ (4 : ℕ) * setDPL24 ε +
    (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) ^ (2 : ℕ) * setDPPi2L22 ε + (zeta5 : ℂ) * setDPZ5 ε +
    (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ) * setDPPi2Z3 ε

/-- The master-independent regular part: `(∑_κ κ G_κ(ε)) / setDDen ε`. -/
noncomputable def setDRegular (ε : ℂ) : ℂ :=
  (setDGOne ε + (π : ℂ) ^ (2 : ℕ) * setDGPi2 ε + (zeta3 : ℂ) * setDGZ3 ε +
    (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) * setDGPi2L2 ε + (π : ℂ) ^ (4 : ℕ) * setDGPi4 ε +
    (Li 4 (1 / 2) : ℂ) * setDGA4 ε + (Real.log 2 : ℂ) ^ (4 : ℕ) * setDGL24 ε +
    (π : ℂ) ^ (2 : ℕ) * (Real.log 2 : ℂ) ^ (2 : ℕ) * setDGPi2L22 ε + (zeta5 : ℂ) * setDGZ5 ε +
    (π : ℂ) ^ (2 : ℕ) * (zeta3 : ℂ) * setDGPi2Z3 ε) / setDDen ε

/-- The contribution of the remainders `rⱼ`: `(∑ⱼ (-1) ^ (lines j) setDAIj(ε) rⱼ) / setDDen ε`
(every remainder enters with exactly one power of `ε`, factored out). -/
noncomputable def setDRemainder (ε r2 r3 r5 r8 r9 r12 r13 r14 r15 r16 r18 : ℂ) : ℂ :=
  (setDAI2 ε * r2 + setDAI3 ε * r3 + setDAI5 ε * r5 - setDAI8 ε * r8 - setDAI9 ε * r9 +
    setDAI12 ε * r12 + setDAI13 ε * r13 + setDAI14 ε * r14 + setDAI15 ε * r15 +
    setDAI16 ε * r16 - setDAI18 ε * r18) / setDDen ε

/-- **Pole cancellation and value**, all constants together:
`(∑_κ κ P_κ) / (ε⁵ setDDen) = a1SixSetDJN + ε setDRegular`. -/
theorem setDNumer_div_eq {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0) :
    setDNumer ε / (ε ^ (5 : ℕ) * setDDen ε) = (a1SixSetDJN : ℂ) + ε * setDRegular ε := by
  rw [setDNumer, setDPOne_eq, setDPPi2_eq, setDPZ3_eq, setDPPi2L2_eq, setDPPi4_eq, setDPA4_eq,
    setDPL24_eq, setDPPi2L22_eq, setDPZ5_eq, setDPPi2Z3_eq, setDRegular, a1SixSetDJN]
  push_cast
  field_simp
  ring

/-- The truncated combination, with the remainders split off. -/
theorem setDCombination_eq_numer {M : SetDMasters} {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0)
    {r2 r3 r5 r8 r9 r12 r13 r14 r15 r16 r18 : ℂ}
    (h2 : M.I2 ε = setDLaurentI2 ε + ε ^ 2 * r2) (h3 : M.I3 ε = setDLaurentI3 ε + ε ^ 1 * r3)
    (h5 : M.I5 ε = setDLaurentI5 ε + ε ^ 2 * r5) (h8 : M.I8 ε = setDLaurentI8 ε + ε ^ 3 * r8)
    (h9 : M.I9 ε = setDLaurentI9 ε + ε ^ 2 * r9)
    (h12 : M.I12 ε = setDLaurentI12 ε + ε ^ 3 * r12)
    (h13 : M.I13 ε = setDLaurentI13 ε + ε ^ 3 * r13)
    (h14 : M.I14 ε = setDLaurentI14 ε + ε ^ 3 * r14)
    (h15 : M.I15 ε = setDLaurentI15 ε + ε ^ 3 * r15)
    (h16 : M.I16 ε = setDLaurentI16 ε + ε ^ 2 * r16)
    (h18 : M.I18 ε = setDLaurentI18 ε + ε ^ 3 * r18) :
    setDCombination M ε = setDNumer ε / (ε ^ (5 : ℕ) * setDDen ε) +
      ε * setDRemainder ε r2 r3 r5 r8 r9 r12 r13 r14 r15 r16 r18 := by
  rw [setDCombination, h2, h3, h5, h8, h9, h12, h13, h14, h15, h16, h18, setDCoeffI2_eq hε hq,
    setDCoeffI3_eq hε hq, setDCoeffI5_eq hε hq, setDCoeffI8_eq hε hq, setDCoeffI9_eq hε hq,
    setDCoeffI12_eq hε hq, setDCoeffI13_eq hε hq, setDCoeffI14_eq hε hq, setDCoeffI15_eq hε hq,
    setDCoeffI16_eq hε hq, setDCoeffI18_eq hε hq]
  simp only [setDLaurentI2, setDLaurentI3, setDLaurentI5, setDLaurentI8, setDLaurentI9,
    setDLaurentI12, setDLaurentI13, setDLaurentI14, setDLaurentI15, setDLaurentI16,
    setDLaurentI18, laportaC1, laportaC2, setDNumer, setDPOne, setDPPi2, setDPZ3, setDPPi2L2,
    setDPPi4, setDPA4, setDPL24, setDPPi2L22, setDPZ5, setDPPi2Z3, setDRemainder]
  field_simp
  ring

/-- **Set (d) from master inputs, pointwise.** For `ε ≠ 0` with `setDDen ε ≠ 0`, if each master
equals its truncated expansion plus `ε ^ (kⱼ + 1) rⱼ`, then
`setDCombination M ε = a1SixSetDJN + ε (setDRegular ε + setDRemainder ε r…)`. -/
theorem setDCombination_eq_of {M : SetDMasters} {ε : ℂ} (hε : ε ≠ 0) (hq : setDDen ε ≠ 0)
    {r2 r3 r5 r8 r9 r12 r13 r14 r15 r16 r18 : ℂ}
    (h2 : M.I2 ε = setDLaurentI2 ε + ε ^ 2 * r2) (h3 : M.I3 ε = setDLaurentI3 ε + ε ^ 1 * r3)
    (h5 : M.I5 ε = setDLaurentI5 ε + ε ^ 2 * r5) (h8 : M.I8 ε = setDLaurentI8 ε + ε ^ 3 * r8)
    (h9 : M.I9 ε = setDLaurentI9 ε + ε ^ 2 * r9)
    (h12 : M.I12 ε = setDLaurentI12 ε + ε ^ 3 * r12)
    (h13 : M.I13 ε = setDLaurentI13 ε + ε ^ 3 * r13)
    (h14 : M.I14 ε = setDLaurentI14 ε + ε ^ 3 * r14)
    (h15 : M.I15 ε = setDLaurentI15 ε + ε ^ 3 * r15)
    (h16 : M.I16 ε = setDLaurentI16 ε + ε ^ 2 * r16)
    (h18 : M.I18 ε = setDLaurentI18 ε + ε ^ 3 * r18) :
    setDCombination M ε = (a1SixSetDJN : ℂ) +
      ε * (setDRegular ε + setDRemainder ε r2 r3 r5 r8 r9 r12 r13 r14 r15 r16 r18) := by
  rw [setDCombination_eq_numer hε hq h2 h3 h5 h8 h9 h12 h13 h14 h15 h16 h18,
    setDNumer_div_eq hε hq]
  ring

theorem analyticAt_setDDen (z : ℂ) : AnalyticAt ℂ setDDen z := by
  unfold setDDen; fun_prop

theorem setDDen_zero : setDDen 0 = 1 := by
  norm_num [setDDen]

theorem analyticAt_setDRegular : AnalyticAt ℂ setDRegular 0 := by
  unfold setDRegular
  refine AnalyticAt.div ?_ (analyticAt_setDDen 0) (by rw [setDDen_zero]; exact one_ne_zero)
  simp only [setDGOne, setDGPi2, setDGZ3, setDGPi2L2, setDGPi4, setDGA4, setDGL24, setDGPi2L22,
    setDGZ5, setDGPi2Z3]
  fun_prop

theorem analyticAt_setDRemainder {R2 R3 R5 R8 R9 R12 R13 R14 R15 R16 R18 : ℂ → ℂ}
    (h2 : AnalyticAt ℂ R2 0) (h3 : AnalyticAt ℂ R3 0) (h5 : AnalyticAt ℂ R5 0)
    (h8 : AnalyticAt ℂ R8 0) (h9 : AnalyticAt ℂ R9 0) (h12 : AnalyticAt ℂ R12 0)
    (h13 : AnalyticAt ℂ R13 0) (h14 : AnalyticAt ℂ R14 0) (h15 : AnalyticAt ℂ R15 0)
    (h16 : AnalyticAt ℂ R16 0) (h18 : AnalyticAt ℂ R18 0) :
    AnalyticAt ℂ (fun ε => setDRemainder ε (R2 ε) (R3 ε) (R5 ε) (R8 ε) (R9 ε) (R12 ε) (R13 ε)
      (R14 ε) (R15 ε) (R16 ε) (R18 ε)) 0 := by
  unfold setDRemainder
  refine AnalyticAt.div ?_ (analyticAt_setDDen 0) (by rw [setDDen_zero]; exact one_ne_zero)
  simp only [setDAI2, setDAI3, setDAI5, setDAI8, setDAI9, setDAI12, setDAI13, setDAI14,
    setDAI15, setDAI16, setDAI18, setDNumI2, setDNumI3, setDNumI5, setDNumI8, setDNumI9,
    setDNumI12, setDNumI13, setDNumI14, setDNumI15, setDNumI16, setDNumI18]
  fun_prop

/-- **Set (d) from master inputs: no poles, and the value.** Under the eleven master
expansions, the set (d) combination agrees on a punctured neighbourhood of `ε = 0` with a
function analytic at `0`, whose value at `0` is the Jegerlehner–Nyffeler closed form. -/
theorem SetDMasters.Expansions.exists_analyticAt {M : SetDMasters} (h : M.Expansions) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = (a1SixSetDJN : ℂ) ∧
      ∀ᶠ ε in 𝓝[≠] (0 : ℂ), setDCombination M ε = g ε := by
  obtain ⟨R2, hR2, e2⟩ := h.I2
  obtain ⟨R3, hR3, e3⟩ := h.I3
  obtain ⟨R5, hR5, e5⟩ := h.I5
  obtain ⟨R8, hR8, e8⟩ := h.I8
  obtain ⟨R9, hR9, e9⟩ := h.I9
  obtain ⟨R12, hR12, e12⟩ := h.I12
  obtain ⟨R13, hR13, e13⟩ := h.I13
  obtain ⟨R14, hR14, e14⟩ := h.I14
  obtain ⟨R15, hR15, e15⟩ := h.I15
  obtain ⟨R16, hR16, e16⟩ := h.I16
  obtain ⟨R18, hR18, e18⟩ := h.I18
  refine ⟨fun ε => (a1SixSetDJN : ℂ) + ε * (setDRegular ε + setDRemainder ε (R2 ε) (R3 ε)
    (R5 ε) (R8 ε) (R9 ε) (R12 ε) (R13 ε) (R14 ε) (R15 ε) (R16 ε) (R18 ε)), ?_, by simp, ?_⟩
  · have hreg := analyticAt_setDRegular
    have hrem := analyticAt_setDRemainder hR2 hR3 hR5 hR8 hR9 hR12 hR13 hR14 hR15 hR16 hR18
    fun_prop
  · have hq : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), setDDen ε ≠ 0 :=
      nhdsWithin_le_nhds ((analyticAt_setDDen 0).continuousAt.eventually_ne
        (by rw [setDDen_zero]; exact one_ne_zero))
    filter_upwards [e2, e3, e5, e8, e9, e12, e13, e14, e15, e16, e18, hq, self_mem_nhdsWithin]
      with ε h2 h3 h5 h8 h9 h12 h13 h14 h15 h16 h18 hq hε
    exact setDCombination_eq_of hε hq h2 h3 h5 h8 h9 h12 h13 h14 h15 h16 h18

/-- **Set (d) from master inputs, as a limit**: `setDCombination M ε → a1SixSetDJN` as `ε → 0`,
`ε ≠ 0`. -/
theorem SetDMasters.Expansions.tendsto {M : SetDMasters} (h : M.Expansions) :
    Tendsto (setDCombination M) (𝓝[≠] (0 : ℂ)) (𝓝 (a1SixSetDJN : ℂ)) := by
  obtain ⟨g, hg, hg0, he⟩ := h.exists_analyticAt
  have hgt : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (a1SixSetDJN : ℂ)) :=
    hg0 ▸ hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact hgt.congr' (he.mono fun _ h => h.symm)

/-- The same limit after multiplying by a normalization factor `N` continuous at `0` with
`N 0 = 1` (for instance `Γ(1 + ε)³`, which relates the survey's master basis to LR96's). -/
theorem SetDMasters.Expansions.tendsto_mul {M : SetDMasters} (h : M.Expansions) {N : ℂ → ℂ}
    (hN : ContinuousAt N 0) (hN0 : N 0 = 1) :
    Tendsto (fun ε => N ε * setDCombination M ε) (𝓝[≠] (0 : ℂ)) (𝓝 (a1SixSetDJN : ℂ)) := by
  simpa [hN0] using (hN.tendsto.mono_left nhdsWithin_le_nhds).mul h.tendsto

/-- Any function has itself as truncated expansion. -/
theorem hasTruncLaurent_self (L : ℂ → ℂ) (n : ℕ) : HasTruncLaurent L L n :=
  ⟨0, analyticAt_const, Eventually.of_forall fun ε => by simp⟩

/-- The truncated expansions themselves, as masters. -/
noncomputable def SetDMasters.ofLaurent : SetDMasters :=
  ⟨setDLaurentI2, setDLaurentI3, setDLaurentI5, setDLaurentI8, setDLaurentI9, setDLaurentI12,
    setDLaurentI13, setDLaurentI14, setDLaurentI15, setDLaurentI16, setDLaurentI18⟩

/-- The inputs are consistent: the truncated expansions satisfy them. -/
theorem SetDMasters.ofLaurent_expansions : SetDMasters.ofLaurent.Expansions :=
  ⟨hasTruncLaurent_self _ _, hasTruncLaurent_self _ _, hasTruncLaurent_self _ _,
    hasTruncLaurent_self _ _, hasTruncLaurent_self _ _, hasTruncLaurent_self _ _,
    hasTruncLaurent_self _ _, hasTruncLaurent_self _ _, hasTruncLaurent_self _ _,
    hasTruncLaurent_self _ _, hasTruncLaurent_self _ _⟩

end QED.ThreeLoopD
