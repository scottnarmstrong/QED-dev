/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersLaurent
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₃`: the input from one IBP relation and a finite integral

LR96's `I₃ = ∫ 1 / (D₁ D₂ D₄ D₅ D₆ D₈)` (Kira master `lbl[1,0,1,1,1,0,1,1,0]`, normalization as
in `QED.DimReg.LR96Family`) is not finite: `I₃ C⁻¹ = ε⁻³/3 + 7ε⁻²/3 + 31ε⁻¹/3 + O(1)`
(`QED.ThreeLoopD.setDLaurentI3`). The integral with one dot on a line of its massive bubble,
Kira `lbl[1,0,1,1,1,0,1,2,0]`, is finite at `d = 4`, and the Kira reduction (survey PD1,
`data/reduction_table.m`) gives, with Kira's sign `(-1) ^ (Σ ν)` and `d = 4 - 2ε`,

  `(3d - 10)/4 · I₃ = F_K - Σⱼ βⱼ(d) Mⱼ`, `Mⱼ ∈ {I₁₃, I₁₂, I₁₈, I₁₄}`,

with coefficients regular at `ε = 0`. In LR96's normalization, with `F(ε)` the dotted integral
divided by `C(ε)` (positive integrand, Euclidean), this is the relation
`QED.ThreeLoopD.SetDMasters.I3Rel` (cleared of the denominators `2` and `32 (1 - 2ε)²`):

  `16 (1 - 2ε)² (1 - 3ε) I₃ = -32 (1 - 2ε)² F + 4 (1 - ε)(2 - 3ε)(1 - 2ε)(I₁₃ - I₁₄)
    - (3 - 4ε)(2 - 3ε)(1 - 2ε) I₁₂ + 2 (1 - ε)³ I₁₈`.

So only `F(0)` enters: if `F` is analytic at `0` with `F(0) = π⁴/15`, the published expansions
of `I₁₂, I₁₃, I₁₄, I₁₈` give that of `I₃` (`QED.ThreeLoopD.hasTruncLaurent_I3_of_rel`; the
orders `ε⁻³` to `ε⁰` match by a polynomial identity checked by `ring`). The value
`F(0) = π⁴/15` is a numerical identification (25 digits from the L01 masters; independently
`6.4939424` by quadrature of the `d = 4` parametric integral). The relation, the analyticity of
`F` and its value are the hypotheses that remain.

## Main results

* `QED.ThreeLoopD.hasTruncLaurent_I3_of_rel`.
* `QED.ThreeLoopD.SetDMasters.Expansions.of_I3Rel`: the eleven inputs with `I₃` replaced by the
  relation and the value of `F`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- **The IBP relation of `I₃`** with the finite dotted integral `F` (Kira
`lbl[1,0,1,1,1,0,1,2,0]`, divided by `C(ε)`), cleared of denominators, near `ε = 0`. -/
def SetDMasters.I3Rel (M : SetDMasters) (F : ℂ → ℂ) : Prop :=
  ∀ᶠ ε in 𝓝[≠] (0 : ℂ), 16 * (1 - 2 * ε) ^ 2 * (1 - 3 * ε) * M.I3 ε =
    -32 * (1 - 2 * ε) ^ 2 * F ε + 4 * (1 - ε) * (2 - 3 * ε) * (1 - 2 * ε) * (M.I13 ε - M.I14 ε)
      - (3 - 4 * ε) * (2 - 3 * ε) * (1 - 2 * ε) * M.I12 ε + 2 * (1 - ε) ^ 3 * M.I18 ε

/-- The polynomial `(LHS - 16 (1 - 2ε)² (1 - 3ε) L₃) / ε` of the relation at the Laurent
polynomials, `F = π⁴/15` (generated with sympy). -/
noncomputable def i3WireP (ε : ℂ) : ℂ :=
    (3760 / 3 - 16 / 3 * (π : ℂ) ^ (4 : ℕ) + 128 / 3 * (π : ℂ) ^ (2 : ℕ) + 512 / 3 * (zeta3 : ℂ)) +
    (-8672 - 384 * (zeta5 : ℂ) + 2048 * (Li 4 (1 / 2) : ℂ) + 2496 * (zeta3 : ℂ) +
    16 / 45 * (π : ℂ) ^ (4 : ℕ) + 256 / 3 * (Real.log 2 : ℂ) ^ (4 : ℕ) + 896 / 3 * (π : ℂ) ^ (2 : ℕ)
    - 512 * (Real.log 2 : ℂ) * (π : ℂ) ^ (2 : ℕ) -
    256 / 3 * (Real.log 2 : ℂ) ^ (2 : ℕ) * (π : ℂ) ^ (2 : ℕ)) * ε + (170169625 / 7776 -
    9216 * (Li 4 (1 / 2) : ℂ) - 384 * (Real.log 2 : ℂ) ^ (4 : ℕ) + 1728 * (zeta5 : ℂ) -
    125912 / 9 * (zeta3 : ℂ) - 57056 / 27 * (π : ℂ) ^ (2 : ℕ) + 220 / 3 * (π : ℂ) ^ (4 : ℕ) +
    384 * (Real.log 2 : ℂ) ^ (2 : ℕ) * (π : ℂ) ^ (2 : ℕ) +
    7424 / 3 * (Real.log 2 : ℂ) * (π : ℂ) ^ (2 : ℕ)) * ε ^ (2 : ℕ) + (-101607493 / 3888 -
    2496 * (zeta5 : ℂ) + 13312 * (Li 4 (1 / 2) : ℂ) - 6124 / 45 * (π : ℂ) ^ (4 : ℕ) +
    1664 / 3 * (Real.log 2 : ℂ) ^ (4 : ℕ) + 99904 / 27 * (π : ℂ) ^ (2 : ℕ) +
    199624 / 9 * (zeta3 : ℂ) - 11776 / 3 * (Real.log 2 : ℂ) * (π : ℂ) ^ (2 : ℕ) -
    1664 / 3 * (Real.log 2 : ℂ) ^ (2 : ℕ) * (π : ℂ) ^ (2 : ℕ)) * ε ^ (3 : ℕ) + (2205805 / 162 -
    6144 * (Li 4 (1 / 2) : ℂ) - 256 * (Real.log 2 : ℂ) ^ (4 : ℕ) + 1152 * (zeta5 : ℂ) -
    33296 / 3 * (zeta3 : ℂ) - 18176 / 9 * (π : ℂ) ^ (2 : ℕ) + 184 / 3 * (π : ℂ) ^ (4 : ℕ) +
    256 * (Real.log 2 : ℂ) ^ (2 : ℕ) * (π : ℂ) ^ (2 : ℕ) +
    2048 * (Real.log 2 : ℂ) * (π : ℂ) ^ (2 : ℕ)) * ε ^ (4 : ℕ)

/-- The polynomial identity behind the expansion of `I₃`: the orders `ε⁻³` to `ε⁰` of the
relation at the Laurent polynomials match. -/
theorem i3Wire_key {ε : ℂ} (h : ε ≠ 0) :
    -32 * (1 - 2 * ε) ^ 2 * ((π : ℂ) ^ 4 / 15) +
      4 * (1 - ε) * (2 - 3 * ε) * (1 - 2 * ε) * (setDLaurentI13 ε - setDLaurentI14 ε)
      - (3 - 4 * ε) * (2 - 3 * ε) * (1 - 2 * ε) * setDLaurentI12 ε
      + 2 * (1 - ε) ^ 3 * setDLaurentI18 ε =
    16 * (1 - 2 * ε) ^ 2 * (1 - 3 * ε) * setDLaurentI3 ε + ε * i3WireP ε := by
  simp only [setDLaurentI3, setDLaurentI12, setDLaurentI13, setDLaurentI14, setDLaurentI18,
    i3WireP]
  field_simp
  ring

/-- **The set (d) input for `I₃` from its IBP relation**: if `F` is analytic at `0` with
`F(0) = π⁴/15`, the relation `QED.ThreeLoopD.SetDMasters.I3Rel` and the expansions of
`I₁₂, I₁₃, I₁₄, I₁₈` give `I₃ C⁻¹ = L₃ + ε R₃` with `R₃` analytic at `0`. -/
theorem hasTruncLaurent_I3_of_rel {M : SetDMasters} {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hF0 : F 0 = (π : ℂ) ^ 4 / 15) (hrel : M.I3Rel F)
    (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h14 : HasTruncLaurent M.I14 setDLaurentI14 3)
    (h18 : HasTruncLaurent M.I18 setDLaurentI18 3) :
    HasTruncLaurent M.I3 setDLaurentI3 1 := by
  obtain ⟨R12, hR12, e12⟩ := h12
  obtain ⟨R13, hR13, e13⟩ := h13
  obtain ⟨R14, hR14, e14⟩ := h14
  obtain ⟨R18, hR18, e18⟩ := h18
  obtain ⟨p, hp⟩ := hF
  have hS : AnalyticAt ℂ (dslope F 0) 0 := ⟨_, hp.has_fpower_series_dslope_fslope⟩
  set S := dslope F 0 with hSdef
  refine ⟨fun ε => (i3WireP ε - 32 * (1 - 2 * ε) ^ 2 * S ε +
    ε ^ 2 * (4 * (1 - ε) * (2 - 3 * ε) * (1 - 2 * ε) * (R13 ε - R14 ε)
      - (3 - 4 * ε) * (2 - 3 * ε) * (1 - 2 * ε) * R12 ε + 2 * (1 - ε) ^ 3 * R18 ε)) /
    (16 * (1 - 2 * ε) ^ 2 * (1 - 3 * ε)), ?_, ?_⟩
  · have hP : AnalyticAt ℂ i3WireP 0 := by unfold i3WireP; fun_prop
    refine AnalyticAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have hDev : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), (16 * (1 - 2 * ε) ^ 2 * (1 - 3 * ε) : ℂ) ≠ 0 :=
    nhdsWithin_le_nhds (ContinuousAt.eventually_ne (by fun_prop) (by norm_num))
  filter_upwards [hrel, e12, e13, e14, e18, hDev, self_mem_nhdsWithin] with
    ε hr h12 h13 h14 h18 hD h0
  have h0 : ε ≠ 0 := h0
  have hFe : F ε = (π : ℂ) ^ 4 / 15 + ε * S ε := by
    have := sub_smul_dslope F 0 ε
    rw [sub_zero, smul_eq_mul, hF0] at this
    linear_combination -this
  have key := i3Wire_key h0
  have hc : ∀ a : ℂ, 16 * (1 - 2 * ε) ^ 2 * (1 - 3 * ε) *
      (ε ^ 1 * (a / (16 * (1 - 2 * ε) ^ 2 * (1 - 3 * ε)))) = ε * a := fun a => by
    rw [pow_one, mul_left_comm, mul_div_cancel₀ _ hD]
  rw [h12, h13, h14, h18, hFe] at hr
  apply mul_left_cancel₀ hD
  rw [hr]
  conv_rhs => rw [mul_add, hc]
  linear_combination key

/-- The set (d) inputs with `I₃` replaced by its IBP relation and the value of `F`. -/
theorem SetDMasters.Expansions.of_I3Rel {M : SetDMasters} {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hF0 : F 0 = (π : ℂ) ^ 4 / 15) (hrel : M.I3Rel F)
    (h2 : HasTruncLaurent M.I2 setDLaurentI2 2) (h5 : HasTruncLaurent M.I5 setDLaurentI5 2)
    (h8 : HasTruncLaurent M.I8 setDLaurentI8 3) (h9 : HasTruncLaurent M.I9 setDLaurentI9 2)
    (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h14 : HasTruncLaurent M.I14 setDLaurentI14 3)
    (h15 : HasTruncLaurent M.I15 setDLaurentI15 3)
    (h16 : HasTruncLaurent M.I16 setDLaurentI16 2)
    (h18 : HasTruncLaurent M.I18 setDLaurentI18 3) : M.Expansions where
  I2 := h2
  I3 := hasTruncLaurent_I3_of_rel hF hF0 hrel h12 h13 h14 h18
  I5 := h5
  I8 := h8
  I9 := h9
  I12 := h12
  I13 := h13
  I14 := h14
  I15 := h15
  I16 := h16
  I18 := h18

end QED.ThreeLoopD
