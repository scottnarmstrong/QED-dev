/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2PDeriv
public import QED.ThreeLoopD.SetDMastersI2Wire
public import QED.ThreeLoopD.SetDMastersI2P1UTot

/-!
# Set (d), master `I₂`: `P'(0)` reduced to the `ℱ`-part

`P'(0) = ∫ (1 - w) L / 𝒰²` with `L = 4 log 𝒰 - 3 log ℱ = log 𝒰 - 3 log (ℱ / 𝒰)`
(`QED.ThreeLoopD.iteratedDeriv_i2PInt`). The integrand is integrable by the Cauchy estimates
behind the differentiation under the integral sign, and the `𝒰`-part is
`QED.ThreeLoopD.i2P1U_value`, so

  `P'(0) = -3 π⁴ / 10 + 18 ζ(3) - 3 ∫ (1 - w) log (ℱ / 𝒰) / 𝒰²`,

and the first coefficient `P'(0) = i2P1` follows from the value
`∫ (1 - w) log (ℱ / 𝒰) / 𝒰² = 2 π⁴ / 45 - 4 ζ(3) + π² / 3` of the `ℱ`-part alone.

## Main results

* `QED.ThreeLoopD.integrableOn_i2P1L`.
* `QED.ThreeLoopD.i2P1_reduction`.
* `QED.ThreeLoopD.iteratedDeriv_i2PInt_one_of_F`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.ThreeLoopD

/-- **`(1 - w) L / 𝒰²` is integrable** on the domain of `I₂`. -/
theorem integrableOn_i2P1L :
    IntegrableOn (fun z : ℝ × ℝ × ℝ × ℝ × ℝ => (1 - z.2.1) * i2PL z /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) i2Dom := by
  have hS : MeasurableSet i2Dom :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod (measurableSet_Ioi.prod
      (measurableSet_Ioi.prod measurableSet_Ioi)))
  have hbd : ∀ z ∈ i2Dom, ‖i2PD 1 0 z‖ ≤ i2Maj z / (1 / 60) ^ 1 := fun z hz =>
    norm_le_of_hasDerivAt_chain (D := fun k e => i2PD k e z) (R := 1 / 20) (ρ := 1 / 60)
      (by norm_num) (fun k ε => (hasDerivAt_i9KExp k _ _ ε).const_mul _)
      (fun ε hε => by rw [i2PD_zero_eq hz]; exact norm_i2Integrand_le hε hz) 1 0
      (by norm_num)
  have hm : Measurable (i2PD 1 0) := by
    unfold i2PD i9KExp i2PL i2F i2U i2LineA i2LineB i2LineC; fun_prop
  have hI : Integrable (i2PD 1 0) (volume.restrict i2Dom) :=
    (integrable_i2Maj.div_const _).mono' hm.aestronglyMeasurable
      (ae_restrict_of_forall_mem hS hbd)
  refine IntegrableOn.congr_fun hI.re (fun z hz => ?_) hS
  simp only [i2PD_at_zero hz 1, pow_one]
  exact RCLike.ofReal_re _

/-- **`P'(0) = -3 π⁴ / 10 + 18 ζ(3) - 3 ∫ (1 - w) log (ℱ / 𝒰) / 𝒰²`**, with the `ℱ`-part
integrable. -/
theorem i2P1_reduction :
    IntegrableOn (fun z : ℝ × ℝ × ℝ × ℝ × ℝ => (1 - z.2.1) *
        Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) i2Dom ∧
      iteratedDeriv 1 i2PInt 0 = ((-(3 * Real.pi ^ 4 / 10) + 18 * QED.Polylog.zeta3 -
        3 * ∫ z in i2Dom, (1 - z.2.1) *
          Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
            i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
            i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 : ℝ) : ℂ) := by
  have hS : MeasurableSet i2Dom :=
    measurableSet_Ioo.prod (measurableSet_Ioo.prod (measurableSet_Ioi.prod
      (measurableSet_Ioi.prod measurableSet_Ioi)))
  obtain ⟨hU, vU⟩ := i2P1U_value
  have hL := integrableOn_i2P1L
  have eq : EqOn (fun z : ℝ × ℝ × ℝ × ℝ × ℝ =>
      ((1 - z.2.1) * Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 -
        (1 - z.2.1) * i2PL z / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) / 3)
      (fun z : ℝ × ℝ × ℝ × ℝ × ℝ => (1 - z.2.1) *
        Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) i2Dom := fun z hz => by
    obtain ⟨hUp, hFp⟩ := i2UF_pos hz
    simp only [i2PL]
    rw [Real.log_div hFp.ne' hUp.ne']
    ring
  have hF : IntegrableOn (fun z : ℝ × ℝ × ℝ × ℝ × ℝ => (1 - z.2.1) *
      Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
        i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2) i2Dom :=
    IntegrableOn.congr_fun ((hU.sub hL).div_const 3) eq hS
  refine ⟨hF, ?_⟩
  rw [iteratedDeriv_i2PInt (k := 1) (by norm_num)]
  congr 1
  have eq2 : EqOn (fun z : ℝ × ℝ × ℝ × ℝ × ℝ => (1 - z.2.1) * i2PL z ^ 1 /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2)
      (fun z : ℝ × ℝ × ℝ × ℝ × ℝ => (1 - z.2.1) *
          Real.log (i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 - 3 * ((1 - z.2.1) *
        Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) /
          i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2)) i2Dom := fun z hz => by
    obtain ⟨hUp, hFp⟩ := i2UF_pos hz
    simp only [i2PL, pow_one]
    rw [Real.log_div hFp.ne' hUp.ne']
    ring
  rw [setIntegral_congr_fun hS eq2, integral_sub hU (hF.const_mul 3), integral_const_mul, vU]

/-- **`P'(0) = i2P1` from the `ℱ`-part**:
`∫ (1 - w) log (ℱ / 𝒰) / 𝒰² = 2 π⁴ / 45 - 4 ζ(3) + π² / 3` gives the first coefficient. -/
theorem iteratedDeriv_i2PInt_one_of_F
    (h : ∫ z in i2Dom, (1 - z.2.1) * Real.log (i2F z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 /
      i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) / i2U z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2 ^ 2 =
      2 * Real.pi ^ 4 / 45 - 4 * QED.Polylog.zeta3 + Real.pi ^ 2 / 3) :
    iteratedDeriv 1 i2PInt 0 = i2P1 := by
  rw [i2P1_reduction.2, h, i2P1]
  push_cast
  ring

end QED.ThreeLoopD
