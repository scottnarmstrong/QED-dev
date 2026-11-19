/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassLimitParametric
public import QED.Integration.TwoLoopRefinedBoundCubic

/-!
# The `ε → 0⁺` limit of the parametric representation for seven lines and a cubic numerator

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2. The variant of `QED/TwoLoop/ClassLimitParametric.lean` for
`N = m + 1 ≥ 7` propagators and a numerator of degree at most three (`P.quart = 0`), as needed by
the rainbow and crossed self-energy classes (seven lines). The proofs are those of the eight-line
file; the only input that changes is the integrability of the spatial integrand,
`QED.Integration.TwoLoop.integrable_numEnergyValueQuartic_of_cubic`
(`QED/Integration/TwoLoopRefinedBoundCubic.lean`), and the representation at `ε > 0` is
`jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_integrable` (`N ≥ 7`).

## Main statements

* `tendsto_jointEnergyFirstIntegral_of_cubic`: under `V ≥ c > 0` the joint integral converges to
  `-π⁴ ∫_Δ paramIntegrand P α p M 0`.
* `integrableOn_paramIntegrand_zero_cubic`: the limit integrand is integrable.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.ClassLimit

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

section AnalysisCubic

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ)

/-- **The parametric integrand is integrable at every `ε > 0`**, under the pointwise bound and the
criterion. -/
theorem integrableOn_paramIntegrand_cubic (hq : P.quart = 0) (hm : 6 ≤ m)
    {ε : ℝ} (hε : 0 < ε) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 P.eval) :
    IntegrableOn (paramIntegrand P α p M ε) (simplexSet m) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  have hW := integrableOn_refinedWeight_of_criterion α 2 E hcrit
  have hS := integrable_numEnergyValueQuartic_of_cubic P α p M hq hm hε hspan hB hW
  have h1 := hS.integral_prod_left
  have hπ : -((π : ℂ) ^ 4) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (ofReal_ne_zero.mpr
    Real.pi_ne_zero))
  refine (h1.const_mul ((-((π : ℂ) ^ 4))⁻¹ * (m.factorial : ℂ))).congr ?_
  filter_upwards [ae_posDef α hm0 hspan] with x ⟨_, hPD⟩
  have h := factorial_mul_integral_numEnergyValueQuartic P α p M (by omega) hε hPD
  calc (-((π : ℂ) ^ 4))⁻¹ * (m.factorial : ℂ) *
        ∫ v : Fin 2 → Fin 3 → ℝ, numEnergyValueQuartic P α p M ε (x, v).1 (x, v).2
      = (-((π : ℂ) ^ 4))⁻¹ * ((m.factorial : ℂ) *
          ∫ v : Fin 2 → Fin 3 → ℝ, numEnergyValueQuartic P α p M ε x v) := by rw [mul_assoc]
    _ = paramIntegrand P α p M ε x := by
        rw [h, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
        rfl


/-- **The coefficients are integrable** on the simplex, under the pointwise bound and the
criterion: from the integrability at `ε = 1, 2, 3` by interpolation at the three nodes
`V - i`, `V - 2i`, `V - 3i`. -/
theorem integrableOn_coeff_cubic (hq : P.quart = 0) (hm : 6 ≤ m)
    {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 P.eval) :
    IntegrableOn (coeffOne P α p) (simplexSet m) ∧ IntegrableOn (coeffTwo P α p) (simplexSet m) ∧
      IntegrableOn (coeffThree P α) (simplexSet m) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  -- the coefficients do not depend on the masses; any masses serve for the interpolation
  obtain ⟨M, -⟩ : ∃ M : Fin (m + 1) → ℝ, True := ⟨0, trivial⟩
  set K := ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2)
  have hK := ae_abs_symanzikV_le α p M hm0 hspan
  obtain ⟨n, hn⟩ : ∃ n, m - 5 = n := ⟨_, rfl⟩
  have h3 : m - 3 = n + 2 := by omega
  have h4 : m - 4 = n + 1 := by omega
  -- the products `Rⱼ = paramIntegrand j · Wⱼ^{n+2}` at the three nodes
  have hR : ∀ j : ℝ, 0 < j → |j| ≤ 3 →
      IntegrableOn (fun x => paramIntegrand P α p M j x * wBase α p M j x ^ (n + 2))
        (simplexSet m) := fun j hj hj3 =>
    (integrableOn_paramIntegrand_cubic P α p M hq hm hj hcrit hB).mul_bdd
      ((measurable_wBase α p M j).pow_const _).aestronglyMeasurable (by
        filter_upwards [hK] with x hx
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_wBase_le α p M j x).trans
          (add_le_add hx hj3)) _)
  have hR₁ := hR 1 one_pos (by norm_num)
  have hR₂ := hR 2 two_pos (by norm_num)
  have hR₃ := hR 3 (by norm_num) (by norm_num)
  have he : ∀ j : ℝ, j ≠ 0 → ∀ x, paramIntegrand P α p M j x * wBase α p M j x ^ (n + 2) =
      coeffOne P α p x + coeffTwo P α p x * wBase α p M j x +
        coeffThree P α x * wBase α p M j x ^ 2 := fun j hj x => by
    rw [paramIntegrand_eq, h3, h4, hn]
    exact three_term_mul_pow (wBase_ne_zero α p M hj x)
  have hW₂ : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ‖wBase α p M 2 x‖ ≤ K + 2 := by
    filter_upwards [hK] with x hx
    exact (norm_wBase_le α p M 2 x).trans (add_le_add hx (by norm_num))
  have hW₂sq : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ‖wBase α p M 2 x ^ 2‖ ≤ (K + 2) ^ 2 := by
    filter_upwards [hW₂] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx _
  have hT₃ : IntegrableOn (coeffThree P α) (simplexSet m) := by
    refine (((hR₁.sub (hR₂.const_mul 2)).add hR₃).neg.div_const 2).congr
      (Eventually.of_forall fun x => ?_)
    exact (coeff_three_eq (he 1 one_ne_zero x) (he 2 two_ne_zero x)
      (he 3 (by norm_num) x)).symm
  have hT₂ : IntegrableOn (coeffTwo P α p) (simplexSet m) := by
    refine (((hR₁.sub hR₃).div_const (2 * I)).sub
      ((hT₃.bdd_mul ((measurable_wBase α p M 2).aestronglyMeasurable) hW₂).const_mul 2)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [coeff_two_eq (he 1 one_ne_zero x) (he 3 (by norm_num) x)]
    simp only [wBase]
    ring
  have hT₁ : IntegrableOn (coeffOne P α p) (simplexSet m) := by
    refine ((hR₂.sub (hT₂.bdd_mul ((measurable_wBase α p M 2).aestronglyMeasurable) hW₂)).sub
      (hT₃.bdd_mul (((measurable_wBase α p M 2).pow_const 2).aestronglyMeasurable)
        hW₂sq)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [coeff_one_eq (he 2 two_ne_zero x)]
    simp only [wBase]
  exact ⟨hT₁, hT₂, hT₃⟩

/-! ### The limit `ε → 0⁺` -/


/-- **The `ε → 0⁺` limit of the parametric representation.** For `N = m + 1 ≥ 7` propagators, a
cubic numerator with the pointwise bound `RefinedBound α E 4 P.eval`, the criterion
`NoSubdivergenceRefined 2 E α`, and `V ≥ c > 0` at every point of the simplex where `U ≠ 0`: the
joint energy-first integral of `P ∏ᵢ Dᵢ⁻¹`, `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε`, converges as `ε → 0⁺` to
`-π⁴ ∫_Δ paramIntegrand P α p M 0`, the parametric integral with `W = V`. -/
theorem tendsto_jointEnergyFirstIntegral_of_cubic (hq : P.quart = 0) (hm : 6 ≤ m)
    {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 P.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹)) (𝓝[>] 0)
      (𝓝 (-((π : ℂ) ^ 4) * ∫ x in simplexSet m, paramIntegrand P α p M 0 x)) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  obtain ⟨hT₁, hT₂, hT₃⟩ := integrableOn_coeff_cubic P α p hq hm hcrit hB
  have hVae : ∀ᵐ x ∂(volume.restrict (simplexSet m)), c ≤ symanzikV α p M (simplexPoint x) := by
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    exact hV _ hz.1 hz.2 hPD.det_pos.ne'
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hlim : Tendsto (fun ε => ∫ x in simplexSet m, paramIntegrand P α p M ε x) (𝓝[>] 0)
      (𝓝 (∫ x in simplexSet m, paramIntegrand P α p M 0 x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖coeffOne P α p x‖ * (c ^ (m - 3))⁻¹ + ‖coeffTwo P α p x‖ * (c ^ (m - 4))⁻¹ +
        ‖coeffThree P α x‖ * (c ^ (m - 5))⁻¹) ?_ ?_ ?_ ?_
    · filter_upwards [hpos] with ε hε
      exact (integrableOn_paramIntegrand_cubic P α p M hq hm hε hcrit hB).aestronglyMeasurable
    · refine Eventually.of_forall fun ε => ?_
      filter_upwards [hVae] with x hx
      exact norm_paramIntegrand_le P α p M hc ε hx
    · exact ((hT₁.norm.mul_const _).add (hT₂.norm.mul_const _)).add (hT₃.norm.mul_const _)
    · filter_upwards [hVae] with x hx
      exact (tendsto_paramIntegrand P α p M (hc.trans_le hx).ne').mono_left nhdsWithin_le_nhds
  refine (hlim.const_mul (-((π : ℂ) ^ 4))).congr' ?_
  filter_upwards [hpos] with ε hε
  have hW := integrableOn_refinedWeight_of_criterion α 2 E hcrit
  exact ((jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_integrable P α p M hm hε
    hspan (integrable_eval_mul_paramDenom_prod_of_refined P α p M (by omega) hε hspan hB hW)
    (integrable_numEnergyValueQuartic_of_cubic P α p M hq hm hε hspan hB hW)).2.2).symm

/-- The limit integrand is integrable on the simplex, under the hypotheses of
`tendsto_jointEnergyFirstIntegral_of_refined`. -/
theorem integrableOn_paramIntegrand_zero_cubic (hq : P.quart = 0) (hm : 6 ≤ m)
    {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 P.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) :
    IntegrableOn (paramIntegrand P α p M 0) (simplexSet m) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  obtain ⟨hT₁, hT₂, hT₃⟩ := integrableOn_coeff_cubic P α p hq hm hcrit hB
  have hmeas : AEStronglyMeasurable (paramIntegrand P α p M 0)
      (volume.restrict (simplexSet m)) := by
    have h : paramIntegrand P α p M 0 = fun x =>
        coeffOne P α p x * (wBase α p M 0 x ^ (m - 3))⁻¹ +
          coeffTwo P α p x * (wBase α p M 0 x ^ (m - 4))⁻¹ +
          coeffThree P α x * (wBase α p M 0 x ^ (m - 5))⁻¹ :=
      funext fun x => paramIntegrand_eq P α p M 0 x
    rw [h]
    have hw : ∀ k : ℕ, AEStronglyMeasurable (fun x => (wBase α p M 0 x ^ k)⁻¹)
        (volume.restrict (simplexSet m)) := fun k =>
      ((measurable_wBase α p M 0).pow_const k).inv.aestronglyMeasurable
    exact ((hT₁.aestronglyMeasurable.mul (hw _)).add (hT₂.aestronglyMeasurable.mul (hw _))).add
      (hT₃.aestronglyMeasurable.mul (hw _))
  refine Integrable.mono' (((hT₁.norm.mul_const ((c ^ (m - 3))⁻¹)).add
    (hT₂.norm.mul_const ((c ^ (m - 4))⁻¹))).add (hT₃.norm.mul_const ((c ^ (m - 5))⁻¹))) hmeas ?_
  filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  exact norm_paramIntegrand_le P α p M hc 0 (hV _ hz.1 hz.2 hPD.det_pos.ne')


end AnalysisCubic

end QED.TwoLoop.ClassLimit

end
