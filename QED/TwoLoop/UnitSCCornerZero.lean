/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerXiKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The corner unit C at `λ = 0`: the chain (6.5) → (6.8) → (6.10)

Sections 6.6.1–6.6.2 of `docs/TWO-LOOP-UNITS.md`, assembled. For the two-loop part
`G_C = cornerGm 0 0` of the corner graph at `λ = 0`,

`∫_{y₃,y₄} ∫₀¹ G_C dx = ∫₀¹ K_C = -31/48 + ζ(2)/6 + ζ(2) log 2 - ζ(3)/4`
(`integral_cornerZero`),

provided `(y₃, y₄) ↦ ∫₀¹ G_C dx` is integrable on the triangle: the substitution
`(y₃, y₄) = (Y ξ, Y (1 - ξ))` (`QED.TwoLoop.UnitXClose.integral_triangle_eq_yxi`), the
`x`-integration
`QED.TwoLoop.UnitSCCorner.integral_cornerGm_zero` (`= Φ_C`, for `ξ ≠ 1/2`), the `ξ`-integration
`QED.TwoLoop.UnitSCCornerXi.integral_cornerPhi_eq_cornerKernel` (`∫₀¹ Y Φ_C dξ = K_C(Y)` for
`Y ≠ 1/2`, its integrability from Fubini) and the value of `∫₀¹ K_C`
(`QED.TwoLoop.Units.intervalIntegrable_and_integral_cornerKernel`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.TwoLoop.UnitSCCorner

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitXClose QED.TwoLoop.UnitSCCornerXi
open QED.TwoLoop.UnitXGraph

/-- The `x`-integral of the corner integrand at `λ = 0`, as a function on the triangle. -/
noncomputable def cornerZeroInt (p : ℝ × ℝ) : ℝ := ∫ x in Ioo (0 : ℝ) 1, cornerGm 0 0 p.1 p.2 x

theorem ae_ne_half : ∀ᵐ Y ∂(volume.restrict (Ioo (0 : ℝ) 1)), Y ≠ 1 / 2 :=
  ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (1 / 2 : ℝ)))

/-- **The chain (6.5) → (6.10)**: if the `x`-integral of `G_C` is integrable on the triangle, then
`∫_{y₃,y₄} ∫₀¹ G_C = -31/48 + π²/36 + (π²/6) log 2 - ζ(3)/4`. -/
theorem integral_cornerZero (hI : IntegrableOn cornerZeroInt innerTriangle) :
    ∫ p in innerTriangle, cornerZeroInt p =
      -(31 / 48) + π ^ 2 / 36 + π ^ 2 / 6 * log 2 - zeta3 / 4 := by
  have hsq := (integrableOn_triangle_iff cornerZeroInt).mp hI
  rw [unitSquare, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at hsq
  have hae : ∀ᵐ Y ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ ξ in Ioo (0 : ℝ) 1, Y * cornerZeroInt (Y * ξ, Y * (1 - ξ)) =
        QED.TwoLoop.Units.cornerKernel Y := by
    filter_upwards [hsq.prod_right_ae, ae_ne_half, ae_restrict_mem measurableSet_Ioo] with
      Y hY hY2 hYm
    have e : ∀ᵐ ξ ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        Y * cornerZeroInt (Y * ξ, Y * (1 - ξ)) = Y * cornerPhi Y ξ := by
      filter_upwards [ae_ne_half, ae_restrict_mem measurableSet_Ioo] with ξ hξ2 hξ
      rw [cornerZeroInt, (integral_cornerGm_zero hYm hξ hξ2).2]
    have hY' : IntegrableOn (fun ξ => Y * cornerZeroInt (Y * ξ, Y * (1 - ξ))) (Ioo 0 1) := by
      refine hY.congr (Eventually.of_forall fun ξ => ?_)
      simp only [yxiMap]
      rw [show Y - Y * ξ = Y * (1 - ξ) by ring]
    rw [integral_congr_ae e,
      integral_cornerPhi_eq_cornerKernel hYm hY2 (hY'.congr_fun_ae e)]
  rw [integral_triangle_eq_yxi hI, integral_congr_ae hae, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    QED.TwoLoop.Units.intervalIntegrable_and_integral_cornerKernel.2]

end QED.TwoLoop.UnitSCCorner

end
