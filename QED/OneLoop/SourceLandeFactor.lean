/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.SourceMagneticMoment
public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import QED.Frozen.OneLoop.IsChargeNormalized
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
import QED.Frozen.OneLoop.ResponseMagneticMomentExistsUnique
import QED.Frozen.OneLoop.LandeFactorLimit
import Mathlib.Analysis.Complex.Basic

/-!
# The Landé factor of the source magnetic moment, from the packet limit

A conditional helper for packet 4b's headline (W₅)
`QED.OneLoop.landeFactor_sourceMagneticMoment_limit`. It derives the regulator limit of the
Landé factor of the source magnetic moment from the packet limit
`sourceMagneticMoment → μ` (the second conjunct of (W₄)), the existence of the response
magnetic moment (R), and the regulator limit (R′) of its Landé factor. The packet-limit
hypothesis is discharged by the sealed theorem (W₄) when (W₅) is assembled; this lemma does not
replace (W₅).
-/

public section

open Filter Topology

namespace QED.OneLoop

/-- **Conditional helper for (W₅).** If, at every regulator and counterterm, the source magnetic
moment tends to every response magnetic moment as the packet narrows, then its Landé factor
approaches `2 (1 + e²/(8π²))` in the sense of (W₅). -/
theorem landeFactor_sourceMagneticMoment_limit_of_tendsto (e m : ℝ) (he : e ≠ 0) (hm : 0 < m)
    (φ : ℝ → ℝ) (η : ℝ) (hη : 0 < η)
    (hT : ∀ (Z₁ mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ) (μ : ℝ),
      IsResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ μ →
        Tendsto (fun lam => sourceMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ φ lam) (𝓝[>] 0)
          (𝓝 (μ : ℂ))) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ), mγ < δ → R < Λ →
      (∃ Z₁ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ) ∧
      ∀ Z₁ : ℝ, IsChargeNormalized e Z₁ m mγ Λ hm hmγ hΛ →
        ∃ lam₀ > 0, ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ‖4 * (m : ℂ) * sourceMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ φ lam / e
            - 2 * (1 + e ^ 2 / (8 * Real.pi ^ 2))‖ < η := by
  obtain ⟨δ, hδ, R, hR⟩ := landeFactor_isResponseMagneticMoment_limit e m he hm η hη
  refine ⟨δ, hδ, R, fun mγ Λ hmγ hΛ hmγδ hΛR => ?_⟩
  obtain ⟨⟨Z₀, -, hZ₀, -⟩, hall⟩ := hR mγ Λ hmγ hΛ hmγδ hΛR
  refine ⟨⟨Z₀, hZ₀⟩, fun Z₁ hZ₁ => ?_⟩
  obtain ⟨μ, hμ, -⟩ := existsUnique_isResponseMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ
  have hlt := hall Z₁ μ hZ₁ hμ
  set c : ℂ := 2 * (1 + e ^ 2 / (8 * Real.pi ^ 2))
  have hlim : Tendsto (fun lam => ‖4 * (m : ℂ) * sourceMagneticMoment e Z₁ m mγ Λ hm hmγ hΛ φ lam
      / e - c‖) (𝓝[>] 0) (𝓝 ‖4 * (m : ℂ) * (μ : ℂ) / e - c‖) :=
    ((((hT Z₁ mγ Λ hmγ hΛ μ hμ).const_mul (4 * (m : ℂ))).div_const (e : ℂ)).sub_const c).norm
  have hval : ‖4 * (m : ℂ) * (μ : ℂ) / e - c‖ < η := by
    have : 4 * (m : ℂ) * (μ : ℂ) / e - c =
        ((4 * m * μ / e - 2 * (1 + e ^ 2 / (8 * Real.pi ^ 2)) : ℝ) : ℂ) := by
      simp only [c]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hlt
  have hev := (hlim.eventually (gt_mem_nhds hval))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨ε, hε, fun lam hlam hlamε => hball ?_ hlam⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hlam]
  exact hlamε

end QED.OneLoop

end
