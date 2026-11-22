/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2Def
public import QED.ThreeLoopD.SetDMastersI12Gamma
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₂`: the input from the Taylor expansion of the parametric integral

`I₂ C⁻¹ = K₀(ε) P(ε) / (3ε)` with `K₀ = Γ(1 + 3ε) / Γ(1 + ε)³`
(`QED.ThreeLoopD.setDMasterI2_eq`, `QED.ThreeLoopD.i12K0`). Since
`K₀ = exp(ε² (π²/2 - 8ζ₃ ε + O(ε²))) = 1 + π²/2 ε² + O(ε³)`
(`QED.ThreeLoopD.i12K0_eq`), the expansion

  `P = 6ζ₃ + (-13π⁴/30 + 30ζ₃ - π²) ε
    + (-12π² ln 2 - 91/2 π²ζ₃ - 7/5 π⁴ + 18 C₂ - 6 C₁ + 1155/2 ζ₅ - 246ζ₃ + 48π²) ε² + O(ε³)`
  (`QED.ThreeLoopD.i2PLaurent`)

gives `HasTruncLaurent setDMasterI2 setDLaurentI2 2`
(`QED.ThreeLoopD.hasTruncLaurent_setDMasterI2_of_P`): the orders `ε⁻¹, ε⁰, ε¹` are
`P₀ / 3`, `P₁ / 3` and `(P₂ + π²/2 P₀) / 3`. Here `C₁, C₂` are Laporta's constants
(`QED.ThreeLoopD.laportaC1`, `QED.ThreeLoopD.laportaC2`), and with their values the `ε²`
coefficient is `12π² ln 2 + 43/2 π²ζ₃ - 13/6 π⁴ - 255/2 ζ₅ + 72ζ₃ - 4π²`
(`QED.ThreeLoopD.i2P2_eq`). The expansion of `P` is the hypothesis that remains: analyticity of
`P` at `0` and its three Taylor coefficients.

## Main results

* `QED.ThreeLoopD.setDMasterI2_eq`, `QED.ThreeLoopD.i2P2_eq`.
* `QED.ThreeLoopD.hasTruncLaurent_setDMasterI2_of_P`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- `P(0) = 6ζ₃`, the period of the tetrahedron. -/
noncomputable def i2P0 : ℂ := 6 * (zeta3 : ℂ)

/-- `P'(0) = -13π⁴/30 + 30ζ₃ - π²`. -/
noncomputable def i2P1 : ℂ := -13 / 30 * (π : ℂ) ^ 4 + 30 * (zeta3 : ℂ) - (π : ℂ) ^ 2

/-- `P''(0)/2`, in terms of Laporta's constants `C₁, C₂`. -/
noncomputable def i2P2 : ℂ :=
  -12 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 91 / 2 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    - 7 / 5 * (π : ℂ) ^ 4 + 18 * laportaC2 - 6 * laportaC1 + 1155 / 2 * (zeta5 : ℂ)
    - 246 * (zeta3 : ℂ) + 48 * (π : ℂ) ^ 2

/-- **The target expansion of `P`** through `ε²`. -/
noncomputable def i2PLaurent (ε : ℂ) : ℂ := i2P0 + i2P1 * ε + i2P2 * ε ^ 2

/-- `P''(0)/2` with the values of `C₁, C₂`. -/
theorem i2P2_eq : i2P2 = 12 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) + 43 / 2 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    - 13 / 6 * (π : ℂ) ^ 4 - 255 / 2 * (zeta5 : ℂ) + 72 * (zeta3 : ℂ) - 4 * (π : ℂ) ^ 2 := by
  simp only [i2P2, laportaC1, laportaC2]
  ring

/-! ### The master in terms of `P` -/

/-- **`I₂ C⁻¹ = K₀ P / (3ε)`**, `K₀ = Γ(1 + 3ε) / Γ(1 + ε)³`. -/
theorem setDMasterI2_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setDMasterI2 ε = i12K0 ε * i2PInt ε / (3 * ε) := by
  have h3 : 3 * ε ≠ 0 := setDGamma_mul_ne_zero h0 3 (by norm_num) rfl
  have hG1 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  simp only [setDMasterI2, lr96I2, lr96C, QED.DimReg.lr96LoopFactor_four_sub, i12K0]
  rw [Gamma_eq_div_one (s := 3 * ε) (t := 1 + 3 * ε) (p := 3 * ε) h3 (by ring) rfl,
    show (1 : ℂ) + ε = 1 + 1 * ε by ring]
  generalize Gamma (1 + 1 * ε) = A at *
  generalize Gamma (1 + 3 * ε) = B at *
  generalize (π : ℂ) ^ ε = Q at *
  field_simp

/-! ### The expansion -/

/-- The exponent `X₀ = π²/2 - 8ζ₃ ε + 13/60 π⁴ ε² - 48ζ₅ ε³` of `K₀` over `ε²`. -/
noncomputable def i2X (ε : ℂ) : ℂ := i12PolyX0 (π : ℂ) (zeta3 : ℂ) (zeta5 : ℂ) ε

/-- `T` with `K₀ = 1 + ε² X₀ + ε⁴ X₀² / 2 + ε⁶ T`. -/
noncomputable def i2T (ε : ℂ) : ℂ := i12ExpT ε (i2X ε) (i12V0 ε)

/-- The polynomial `Q` with `(1 + ε² X₀ + ε⁴ X₀²/2) P_L - 3ε L₂ = ε³ Q`. -/
noncomputable def i2Q (ε : ℂ) : ℂ :=
  (π : ℂ) ^ 2 / 2 * (i2P1 + i2P2 * ε) +
    (-8 * (zeta3 : ℂ) + 13 / 60 * (π : ℂ) ^ 4 * ε - 48 * (zeta5 : ℂ) * ε ^ 2) * i2PLaurent ε +
    ε * i2X ε ^ 2 * i2PLaurent ε / 2

/-- The remainder `R₂` with `I₂ C⁻¹ = L₂ + ε² R₂`, given `P = P_L + ε³ R`. -/
noncomputable def i2R (ε R : ℂ) : ℂ :=
  (i2Q ε + ε ^ 3 * i2T ε * i2PLaurent ε + (i12PolyKH (i2X ε) ε + ε ^ 6 * i2T ε) * R) / 3

theorem analyticAt_i2R {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0) :
    AnalyticAt ℂ (fun ε => i2R ε (R ε)) 0 := by
  have hX : AnalyticAt ℂ i2X 0 := by unfold i2X i12PolyX0; fun_prop
  have hV : AnalyticAt ℂ i12V0 0 := by
    have h1 := analyticAt_i12_logGammaRem 3
    have h2 := analyticAt_i12_logGammaRem 1
    unfold i12V0
    fun_prop
  have hT : AnalyticAt ℂ i2T 0 := analyticAt_i12ExpT hX hV
  have hL : AnalyticAt ℂ i2PLaurent 0 := by unfold i2PLaurent; fun_prop
  have hQ : AnalyticAt ℂ i2Q 0 := by unfold i2Q; fun_prop
  unfold i2R i12PolyKH
  fun_prop

/-- **The set (d) input for `I₂` from the expansion of `P`**: if `P = P_L + ε³ R` with `R`
analytic at `0`, then `I₂ C⁻¹ = L₂ + ε² R₂` with `R₂` analytic at `0`. -/
theorem hasTruncLaurent_setDMasterI2_of_P (hP : HasTruncLaurent i2PInt i2PLaurent 3) :
    HasTruncLaurent setDMasterI2 setDLaurentI2 2 := by
  obtain ⟨RR, hRR, hRe⟩ := hP
  refine ⟨fun ε => i2R ε (RR ε), analyticAt_i2R hRR, ?_⟩
  filter_upwards [setDGamma_eventually_small, hRe, self_mem_nhdsWithin] with ε hε hRε h0
  have h0 : ε ≠ 0 := h0
  have hK : i12K0 ε = i12PolyKH (i2X ε) ε + ε ^ 6 * i2T ε := by
    rw [i12K0_eq hε, exp_eq_i12ExpT]
    rfl
  rw [setDMasterI2_eq h0 hε, hRε, hK, i2R, i2Q]
  simp only [setDLaurentI2, i2PLaurent, i2P0, i2P1, i2P2, i12PolyKH, i2X, i12PolyX0]
  generalize i2T ε = T
  generalize RR ε = R
  generalize laportaC1 = C1
  generalize laportaC2 = C2
  field_simp
  ring

end QED.ThreeLoopD
