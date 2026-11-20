/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1DInterp
public import QED.GradedProof.X1DParamPoly
public import QED.TwoLoop.LimitCovarianceQuartic
public import QED.TwoLoop.ClassIntegrableLoopPoly

/-!
# (X₁) piece D: the `ε → 0⁺` limit of a parametric family, continuous in the momenta

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D. Consider the joint energy-first integrals

`I_ε(y) = ∫ N_y(ℓ) ∏ᵢ (kᵢ(ℓ, y)² + Mᵢ² - iε)⁻¹`

with line momenta `mom y` affine in external four-vectors `y`, and numerators `N_y` of degree at
most four in the loop momenta, polynomial in `y` at fixed `ℓ`, with the refined bound and the
refined criterion. If `V ≥ c > 0` at `mom y` for `y` near `y₀`, then (`exists_tendsto_cont`)
there is `G` with `I_ε(y) → G(y)` as `ε → 0⁺` for `y` near `y₀`, and `G` is continuous at `y₀`.

## Proof

* By tensor interpolation (`QED.GradedProof.X1D.IsLoopPoly.eq_grid`)
  `N_y = ∑_κ w_κ(y) N_{y_κ}` at every `ℓ`; with quartics `Q_κ` of `N_{y_κ}` the combination
  `Q(y) = ∑_κ w_κ(y) Q_κ` is a quartic of `N_y`, and `G(y) = -π⁴ ∫_Δ paramIntegrand Q(y) … 0`
  is the limit (`QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined`).
* `paramIntegrand` is linear in the quartic (`QED.TwoLoop.LimitCovariance.paramIntegrand_qsum`),
  so `G(y) = -π⁴ ∑_κ w_κ(y) ∫_Δ paramNum(Q_κ, mom y) / V^{m-3}`.
* Each `paramNum(Q_κ, mom y, x)` is polynomial in `y`
  (`QED.GradedProof.X1D.isLoopPoly_paramNum`), integrable at every `y`; interpolating again
  bounds it by integrable functions uniformly near `y₀`, and dominated convergence gives the
  continuity (`tendsto_integral_poly_div`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.TwoLoop.PauliZeroLimit (paramNum paramIntegrand_zero_eq integrableOn_paramNum)
open QED.TwoLoop.LimitCovariance (qsum eval_qsum paramIntegrand_qsum)

namespace QED.GradedProof.X1D

variable {L : ℕ}

/-! ### Dominated convergence for polynomial families -/

section Poly

variable {ι : Type*} [MeasurableSpace ι] {μ : Measure ι}

/-- **Continuity of `∫ A(·, y) / V(·, y)ᴺ`** at `y₀` for families `A(x, ·)` polynomial in the
four-vectors `y` with integrable values at the grid points, and `V ≥ c > 0` near `y₀`. -/
theorem tendsto_integral_poly_div {n N : ℕ} {A : ι → (Fin L → Fin 4 → ℝ) → ℂ}
    {V : ι → (Fin L → Fin 4 → ℝ) → ℝ} {c : ℝ} {y₀ : Fin L → Fin 4 → ℝ}
    (hA : ∀ x, IsLoopPoly L n (A x))
    (hAi : ∀ κ : Fin L × Fin 4 → Fin (n + 1), Integrable (fun x => A x (gridPt n κ)) μ)
    (hc : 0 < c) (hV : ∀ᶠ y in 𝓝 y₀, ∀ᵐ x ∂μ, c ≤ V x y)
    (hVc : ∀ᵐ x ∂μ, ContinuousAt (V x) y₀)
    (hVm : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (fun x => ((V x y : ℝ) : ℂ)) μ) :
    Tendsto (fun y => ∫ x, A x y / ((V x y : ℝ) : ℂ) ^ N ∂μ) (𝓝 y₀)
      (𝓝 (∫ x, A x y₀ / ((V x y₀ : ℝ) : ℂ) ^ N ∂μ)) := by
  have hrep : ∀ x y, A x y = ∑ κ, gridWt n κ y * A x (gridPt n κ) := fun x y =>
    IsLoopPoly.eq_grid (hA x) y
  have hW : ∀ᶠ y in 𝓝 y₀, ∀ κ : Fin L × Fin 4 → Fin (n + 1),
      ‖gridWt n κ y‖ < ‖gridWt n κ y₀‖ + 1 := by
    refine Filter.eventually_all.mpr fun κ => ?_
    have h := ((continuous_gridWt n κ).norm.tendsto y₀).eventually
      (Iio_mem_nhds (lt_add_one ‖gridWt n κ y₀‖))
    exact h
  set g : ι → ℝ := fun x => (∑ κ, (‖gridWt n κ y₀‖ + 1) * ‖A x (gridPt n κ)‖) / c ^ N
  have hg : Integrable g μ :=
    (integrable_finsetSum _ fun κ _ => (hAi κ).norm.const_mul _).div_const _
  have hmeasA : ∀ y, AEStronglyMeasurable (fun x => A x y) μ := fun y => by
    have : (fun x => A x y) = fun x => ∑ κ, gridWt n κ y * A x (gridPt n κ) :=
      funext fun x => hrep x y
    rw [this]
    exact (integrable_finsetSum _ fun κ _ => (hAi κ).const_mul _).aestronglyMeasurable
  refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hg ?_
  · filter_upwards [hVm] with y hy
    exact (hmeasA y).div₀ (hy.pow N)
  · filter_upwards [hV, hW] with y hy hw
    filter_upwards [hy] with x hx
    have hVpos : 0 < V x y := hc.trans_le hx
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hVpos, hrep x y]
    refine div_le_div₀ (Finset.sum_nonneg fun κ _ => by positivity) ?_ (pow_pos hc N)
      (pow_le_pow_left₀ hc.le hx N)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hw κ).le (norm_nonneg _)
  · have hV0 : ∀ᵐ x ∂μ, c ≤ V x y₀ := hV.self_of_nhds
    filter_upwards [hV0, hVc] with x hx hxc
    have hne : ((V x y₀ : ℝ) : ℂ) ^ N ≠ 0 :=
      pow_ne_zero _ (ofReal_ne_zero.mpr (hc.trans_le hx).ne')
    have h1 : ContinuousAt (A x) y₀ := (IsLoopPoly.continuous (hA x)).continuousAt
    have h2 : ContinuousAt (fun y => ((V x y : ℝ) : ℂ) ^ N) y₀ :=
      (continuous_ofReal.continuousAt.comp hxc).pow N
    exact (h1.div h2 hne).tendsto

end Poly

/-! ### The parametric family -/

section Family

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (M : Fin (m + 1) → ℝ)

/-- `V ≥ c` at every point of the simplex with `U ≠ 0` gives `V ≥ c` a.e. on the simplex. -/
theorem ae_le_symanzikV (hm : 0 < m) (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    {p : Fin (m + 1) → Fin 4 → ℝ} {c : ℝ}
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) :
    ∀ᵐ x ∂(volume.restrict (simplexSet m)), c ≤ symanzikV α p M (simplexPoint x) := by
  filter_upwards [ae_posDef α hm hspan] with x ⟨hxS, hPD⟩
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  exact hV _ hz.1 hz.2 hPD.det_pos.ne'

/-- **The parametric limit of a fixed quartic is continuous in the momenta.** -/
theorem tendsto_integral_paramIntegrand (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) {Q : LoopQuartic} (hB : RefinedBound α E 4 Q.eval)
    {mom : (Fin L → Fin 4 → ℝ) → Fin (m + 1) → Fin 4 → ℝ}
    (hmom : ∀ i μ, IsLoopPoly L 1 fun y => ((mom y i μ : ℝ) : ℂ)) {y₀ : Fin L → Fin 4 → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hV : ∀ᶠ y in 𝓝 y₀, ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α (mom y) M z) :
    Tendsto (fun y => ∫ x in simplexSet m, paramIntegrand Q α (mom y) M 0 x) (𝓝 y₀)
      (𝓝 (∫ x in simplexSet m, paramIntegrand Q α (mom y₀) M 0 x)) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  have hVae : ∀ᶠ y in 𝓝 y₀, ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      c ≤ symanzikV α (mom y) M (simplexPoint x) := by
    filter_upwards [hV] with y hy
    exact ae_le_symanzikV α M hm0 hspan hy
  have heq : ∀ y, (∀ᵐ x ∂(volume.restrict (simplexSet m)),
      c ≤ symanzikV α (mom y) M (simplexPoint x)) →
      ∫ x in simplexSet m, paramIntegrand Q α (mom y) M 0 x =
        ∫ x in simplexSet m, paramNum Q α (mom y) M x /
          ((symanzikV α (mom y) M (simplexPoint x) : ℝ) : ℂ) ^ (m - 3) := fun y hy => by
    refine integral_congr_ae ?_
    filter_upwards [hy] with x hx
    exact paramIntegrand_zero_eq Q α (mom y) M (by omega) (hc.trans_le hx).ne'
  have hlim := tendsto_integral_poly_div (μ := volume.restrict (simplexSet m)) (N := m - 3)
    (A := fun x y => paramNum Q α (mom y) M x)
    (V := fun x y => symanzikV α (mom y) M (simplexPoint x))
    (fun x => isLoopPoly_paramNum Q α mom M hmom x)
    (fun κ => integrableOn_paramNum Q α (mom (gridPt 4 κ)) M hm hcrit hB) hc hVae
    (Eventually.of_forall fun x => by
      have h := IsLoopPoly.continuous (isLoopPoly_symanzikV α mom M (simplexPoint x) hmom)
      have h' : Continuous fun y => symanzikV α (mom y) M (simplexPoint x) := by
        have := continuous_re.comp h
        simpa [Function.comp_def] using this
      exact h'.continuousAt)
    (Eventually.of_forall fun y => (continuous_ofReal.measurable.comp
      ((measurable_symanzikV α (mom y) M).comp
        continuous_simplexPoint'.measurable)).aestronglyMeasurable)
  rw [heq y₀ hVae.self_of_nhds]
  refine hlim.congr' ?_
  filter_upwards [hVae] with y hy
  exact (heq y hy).symm

/-- **The `ε → 0⁺` limit of a parametric family, continuous in the momenta.** For line momenta
`mom y` with affine coordinates, numerators `N y` polynomial in `y` at every loop momentum, each
of degree at most four in the loop momenta with the refined bound, the refined criterion, and
`V ≥ c > 0` at `mom y` for `y` near `y₀`: there is `G` such that for `y` near `y₀` the joint
energy-first integral of `N y ∏ᵢ Dᵢ⁻¹` converges to `G y` as `ε → 0⁺`, and `G` is continuous at
`y₀`. -/
theorem exists_tendsto_cont (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) {mom : (Fin L → Fin 4 → ℝ) → Fin (m + 1) → Fin 4 → ℝ}
    (hmom : ∀ i μ, IsLoopPoly L 1 fun y => ((mom y i μ : ℝ) : ℂ)) {n : ℕ}
    {N : (Fin L → Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hN : ∀ ℓ, IsLoopPoly L n fun y => N y ℓ) (hNq : ∀ y, IsLoopPoly 2 4 (N y))
    (hNB : ∀ y, RefinedBound α E 4 (N y)) {y₀ : Fin L → Fin 4 → ℝ} {c : ℝ} (hc : 0 < c)
    (hV : ∀ᶠ y in 𝓝 y₀, ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c ≤ symanzikV α (mom y) M z) :
    ∃ G : (Fin L → Fin 4 → ℝ) → ℂ,
      (∀ᶠ y in 𝓝 y₀, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
          (fun ℓ => N y ℓ * ∏ i, (lineDenom α (mom y) M ε i ℓ)⁻¹)) (𝓝[>] 0) (𝓝 (G y))) ∧
        ContinuousAt G y₀ := by
  choose Q hQ using fun κ : Fin L × Fin 4 → Fin (n + 1) => (hNq (gridPt n κ)).exists_loopQuartic
  set Qy : (Fin L → Fin 4 → ℝ) → LoopQuartic := fun y =>
    qsum Finset.univ (fun κ => gridWt n κ y) Q with hQy
  have hQyeval : ∀ y, (Qy y).eval = N y := fun y => by
    funext ℓ
    rw [hQy, eval_qsum, IsLoopPoly.eq_grid (hN ℓ) y]
    exact Finset.sum_congr rfl fun κ _ => by rw [hQ κ]
  have hBκ : ∀ κ, RefinedBound α E 4 (Q κ).eval := fun κ => by
    rw [hQ κ]
    exact hNB _
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  refine ⟨fun y => -((π : ℂ) ^ 4) * ∫ x in simplexSet m, paramIntegrand (Qy y) α (mom y) M 0 x,
    ?_, ?_⟩
  · filter_upwards [hV] with y hy
    have h := tendsto_jointEnergyFirstIntegral_of_refined (Qy y) α (mom y) M hm hcrit
      (by rw [hQyeval]; exact hNB y) hc hy
    simpa only [hQyeval] using h
  · -- the linear decomposition, near `y₀`
    have hdec : ∀ᶠ y in 𝓝 y₀, -((π : ℂ) ^ 4) *
        ∫ x in simplexSet m, paramIntegrand (Qy y) α (mom y) M 0 x =
        -((π : ℂ) ^ 4) * ∑ κ, gridWt n κ y *
          ∫ x in simplexSet m, paramIntegrand (Q κ) α (mom y) M 0 x := by
      filter_upwards [hV] with y hy
      congr 1
      simp only [hQy, paramIntegrand_qsum]
      rw [integral_finsetSum _ fun κ _ =>
        (integrableOn_paramIntegrand_zero (Q κ) α (mom y) M hm hcrit (hBκ κ) hc hy).const_mul _]
      exact Finset.sum_congr rfl fun κ _ => integral_const_mul _ _
    have hcont : Tendsto (fun y => -((π : ℂ) ^ 4) * ∑ κ, gridWt n κ y *
        ∫ x in simplexSet m, paramIntegrand (Q κ) α (mom y) M 0 x) (𝓝 y₀)
        (𝓝 (-((π : ℂ) ^ 4) * ∑ κ, gridWt n κ y₀ *
          ∫ x in simplexSet m, paramIntegrand (Q κ) α (mom y₀) M 0 x)) := by
      refine Tendsto.const_mul _ (tendsto_finsetSum _ fun κ _ => ?_)
      exact ((continuous_gridWt n κ).tendsto y₀).mul
        (tendsto_integral_paramIntegrand α M hm hcrit (hBκ κ) hmom hc hV)
    have h0 := hdec.self_of_nhds
    show Tendsto _ (𝓝 y₀) (𝓝 _)
    simp only [h0]
    exact hcont.congr' (hdec.mono fun y hy => hy.symm)

end Family

end QED.GradedProof.X1D

end
