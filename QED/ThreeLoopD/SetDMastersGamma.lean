/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersLaurent
public import QED.DimReg.LR96Family
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Set (d) of `A₁⁽⁶⁾`: the master `I₁₈` is proved

The factorized three-loop vacuum master `I₁₈` of Laporta–Remiddi (1996) is the cube of the
unit one-loop tadpole, in LR96's normalization `QED.DimReg.lr96I18`; LR96 eq. (14) holds
exactly (`QED.DimReg.lr96I18_laurent`). Dividing by `C(ε) = (π ^ ε Γ(1 + ε))³`
(`QED.ThreeLoopD.lr96C`) gives the master `QED.ThreeLoopD.setDMasterI18` of the set (d)
interface, and we prove its input `HasTruncLaurent setDMasterI18 setDLaurentI18 3`
(`QED.ThreeLoopD.hasTruncLaurent_setDMasterI18`). This discharges one of the eleven inputs
(`QED.ThreeLoopD.SetDMasters.Expansions.of_I18`).

The two other Γ-function masters, `I₁₄` and `I₁₆`, need the Taylor coefficients of
`log Γ(1 + ε)` through `ε⁵` (values `ζ(2), …, ζ(5)`), which the campaign does not have yet.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.ThreeLoopD

/-- LR96's normalization factor `C(ε) = (π ^ ε Γ(1 + ε))³`. -/
noncomputable def lr96C (ε : ℂ) : ℂ := ((Real.pi : ℂ) ^ ε * Gamma (1 + ε)) ^ 3

/-- The master `I₁₈ C⁻¹`: the LR96-normalized cube of the unit tadpole, divided by `C(ε)`. -/
noncomputable def setDMasterI18 (ε : ℂ) : ℂ := QED.DimReg.lr96I18 ε / lr96C ε

theorem lr96C_ne_zero {ε : ℂ} (hε : ‖ε‖ < 1) : lr96C ε ≠ 0 := by
  have hpi : (Real.pi : ℂ) ^ ε ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hre : 0 < (1 + ε).re := by
    have := abs_re_le_norm ε
    rw [add_re, one_re]
    linarith [abs_le.mp this]
  exact pow_ne_zero 3 (mul_ne_zero hpi (Gamma_ne_zero_of_re_pos hre))

/-- **The input for `I₁₈`, proved**: `I₁₈ C⁻¹ = -ε⁻³ - 3ε⁻² - 6ε⁻¹ - 10 - 15ε - 21ε² + O(ε³)`,
with remainder `-28 + ε R(ε)` analytic at `0`. -/
theorem hasTruncLaurent_setDMasterI18 : HasTruncLaurent setDMasterI18 setDLaurentI18 3 := by
  refine ⟨fun ε => -28 + ε * QED.DimReg.vacuumRemainder ε, ?_, ?_⟩
  · have := QED.DimReg.analyticAt_vacuumRemainder (ω := 0) (by simp)
    fun_prop
  · have hb : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ‖ε‖ < 1 :=
      nhdsWithin_le_nhds (Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) one_pos)
        fun x hx => by simpa using hx)
    filter_upwards [hb, self_mem_nhdsWithin] with ε hb h0
    have h0 : ε ≠ 0 := h0
    have h1 : ε ≠ 1 := by
      rintro rfl
      simp at hb
    rw [setDMasterI18, QED.DimReg.lr96I18_laurent h0 h1, ← lr96C,
      mul_div_cancel_left₀ _ (lr96C_ne_zero hb)]
    simp only [QED.DimReg.vacuumLaurentPoly, setDLaurentI18]
    ring

/-- The set (d) inputs with `I₁₈` discharged: if `M.I18` is the proved master and the other ten
inputs hold, then all eleven hold. -/
theorem SetDMasters.Expansions.of_I18 {M : SetDMasters} (h18 : M.I18 = setDMasterI18)
    (h2 : HasTruncLaurent M.I2 setDLaurentI2 2) (h3 : HasTruncLaurent M.I3 setDLaurentI3 1)
    (h5 : HasTruncLaurent M.I5 setDLaurentI5 2) (h8 : HasTruncLaurent M.I8 setDLaurentI8 3)
    (h9 : HasTruncLaurent M.I9 setDLaurentI9 2) (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h14 : HasTruncLaurent M.I14 setDLaurentI14 3)
    (h15 : HasTruncLaurent M.I15 setDLaurentI15 3)
    (h16 : HasTruncLaurent M.I16 setDLaurentI16 2) : M.Expansions :=
  ⟨h2, h3, h5, h8, h9, h12, h13, h14, h15, h16, h18 ▸ hasTruncLaurent_setDMasterI18⟩

end QED.ThreeLoopD
