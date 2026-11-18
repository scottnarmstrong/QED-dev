/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassLimitParametric

/-!
# Continuity of the parametric value in the line masses

A tool for the nested-form identity of the VP unit (`QED.TwoLoop.UnitVPLink.VPUnitNested`). The
coefficients `T₁, T₂, T₃` of the parametric integrand at `ε = 0`
(`QED.TwoLoop.ClassLimit.paramIntegrand_eq`) do not involve the masses, which enter only through
`V`. So under a lower bound `V ≥ c > 0` uniform in the masses, the integrand is dominated by
`|T₁| c^{-(n+2)} + |T₂| c^{-(n+1)} + |T₃| c^{-n}` (integrable, `integrableOn_coeff`), and the
parametric integral is continuous in the masses (dominated convergence).

## Main statements

* `tendsto_integral_paramIntegrand_of_masses`: if `M t → M₀` along a countably generated filter,
  with the uniform positivity bound, then `∫_Δ paramIntegrand Q α p (M t) 0 → ∫_Δ paramIntegrand
  Q α p M₀ 0`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.VPUnitNested

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)

theorem tendsto_symanzikV_of_masses {ι : Type*} {l : Filter ι} (M : ι → Fin (m + 1) → ℝ)
    (M₀ : Fin (m + 1) → ℝ) (hM : ∀ i, Tendsto (fun t => M t i) l (𝓝 (M₀ i)))
    (z : Fin (m + 1) → ℝ) :
    Tendsto (fun t => symanzikV α p (M t) z) l (𝓝 (symanzikV α p M₀ z)) := by
  unfold symanzikV
  refine Tendsto.sub_const ?_ _
  exact tendsto_finsetSum _ fun i _ =>
    (((hM i).pow 2).add_const _).const_mul _

/-- **The parametric integral is continuous in the masses**, under a positivity bound uniform in
the masses. -/
theorem tendsto_integral_paramIntegrand_of_masses {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (M : ι → Fin (m + 1) → ℝ) (M₀ : Fin (m + 1) → ℝ)
    (hM : ∀ i, Tendsto (fun t => M t i) l (𝓝 (M₀ i))) (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ᶠ t in l, ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α p (M t) z)
    (hV₀ : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M₀ z) :
    Tendsto (fun t => ∫ x in simplexSet m, paramIntegrand Q α p (M t) 0 x) l
      (𝓝 (∫ x in simplexSet m, paramIntegrand Q α p M₀ 0 x)) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  obtain ⟨hT₁, hT₂, hT₃⟩ := integrableOn_coeff Q α p hm hcrit hB
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖coeffOne Q α p x‖ * (c ^ (m - 3))⁻¹ + ‖coeffTwo Q α p x‖ * (c ^ (m - 4))⁻¹ +
      ‖coeffThree Q α x‖ * (c ^ (m - 5))⁻¹) ?_ ?_ ?_ ?_
  · filter_upwards [hV] with t ht
    exact (integrableOn_paramIntegrand_zero Q α p (M t) hm hcrit hB hc ht).aestronglyMeasurable
  · filter_upwards [hV] with t ht
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    exact norm_paramIntegrand_le Q α p (M t) hc 0 (ht _ hz.1 hz.2 hPD.det_pos.ne')
  · exact ((hT₁.norm.mul_const _).add (hT₂.norm.mul_const _)).add (hT₃.norm.mul_const _)
  · filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    have hV0 : symanzikV α p M₀ (simplexPoint x) ≠ 0 :=
      (lt_of_lt_of_le hc (hV₀ _ hz.1 hz.2 hPD.det_pos.ne')).ne'
    have hW : Tendsto (fun t => wBase α p (M t) 0 x) l (𝓝 (wBase α p M₀ 0 x)) := by
      unfold wBase
      exact ((Complex.continuous_ofReal.tendsto _).comp
        (tendsto_symanzikV_of_masses α p M M₀ hM _)).sub_const _
    have hW0 : wBase α p M₀ 0 x ≠ 0 := by simpa [wBase] using hV0
    have hpow : ∀ k : ℕ, Tendsto (fun t => (wBase α p (M t) 0 x ^ k)⁻¹) l
        (𝓝 ((wBase α p M₀ 0 x ^ k)⁻¹)) := fun k =>
      (hW.pow k).inv₀ (pow_ne_zero k hW0)
    simp only [paramIntegrand_eq]
    exact (((hpow _).const_mul _).add ((hpow _).const_mul _)).add ((hpow _).const_mul _)

end QED.TwoLoop.VPUnitNested

end
