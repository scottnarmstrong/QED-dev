/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopRefinedBoundFubini

/-!
# The `ε → 0⁺` limit of the parametric representation under a positivity bound

Part of obligations O2-7 and O2-12 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.3–4.4). For
`N = m + 1 ≥ 8` propagators, a numerator `P` of degree at most four with the pointwise bound
`RefinedBound α E 4 P.eval`, and the criterion `NoSubdivergenceRefined 2 E α`, the joint
energy-first integral at `ε > 0` is `-π⁴ ∫_Δ paramIntegrand P α p M ε`
(`jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined`), where

`paramIntegrand ε = U⁻² ((N-5)! W^{4-N} P(-S) + (N-6)!/2 W^{5-N} H(-S)·G`
`+ (N-7)!/4 W^{6-N} R·Π(G))`,
`W = V - iε`.

If moreover `V ≥ c > 0` at every point of the simplex with `U ≠ 0`, the joint integral converges
as `ε → 0⁺` to `-π⁴ ∫_Δ paramIntegrand P α p M 0`, and the limit integrand is integrable
(`tendsto_jointEnergyFirstIntegral_of_refined`, `integrableOn_paramIntegrand_zero`).

## Proof

* The integrand is `T₁ W^{-(n+2)} + T₂ W^{-(n+1)} + T₃ W^{-n}` with `n = m - 5` and coefficients
  `Tₖ` independent of `ε` (`paramIntegrand_eq`).
* At every `ε > 0` the integrand is integrable on the simplex (`integrableOn_paramIntegrand`): it
  is a.e. a multiple of the spatial integral of `numEnergyValueQuartic`, which is integrable on
  simplex × space (`integrable_numEnergyValueQuartic_of_refined`).
* **The coefficients are integrable** (`integrableOn_coeff`). At `ε = 1, 2, 3` the products
  `Rⱼ = paramIntegrand j · Wⱼ^{n+2} = T₁ + T₂ Wⱼ + T₃ Wⱼ²` are integrable, since `|V|` is bounded
  on the simplex (`abs_symanzikV_le`). The nodes `Wⱼ = V - ij` are equally spaced, so
  `T₃ = -(R₁ - 2R₂ + R₃)/2`, `T₂ = (R₁ - R₃)/(2i) - 2W₂T₃`, `T₁ = R₂ - W₂T₂ - W₂²T₃`
  (`coeff_three_eq`, …), each integrable.
* **Dominated convergence.** Off the null set `U = 0`, `|V - iε| ≥ V ≥ c`, so
  `|paramIntegrand ε| ≤ |T₁| c^{-(n+2)} + |T₂| c^{-(n+1)} + |T₃| c^{-n}`, integrable, and
  `paramIntegrand ε → paramIntegrand 0` pointwise since `V ≠ 0`.

The positivity hypothesis is supplied for the classes by `QED/Integration/SymanzikPositivity*.lean`
(see `QED/TwoLoop/ClassLimit.lean`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.ClassLimit

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The parametric integrand and its coefficients -/

section Integrand

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ)

/-- The integrand of the parametric representation at `ε`:
`U⁻² ((m-4)! W^{3-m} P(-S) + (m-5)!/2 W^{4-m} H(-S)·G + (m-6)!/4 W^{5-m} R·Π(G))`, `W = V - iε`,
as in `jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined`. -/
noncomputable def paramIntegrand (ε : ℝ) (x : Fin m → ℝ) : ℂ :=
  ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
    (((m - 4).factorial : ℂ) *
        ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 3))⁻¹ *
        P.eval (-loopShift α p (simplexPoint x)) +
      ((m - 5).factorial : ℂ) / 2 *
        ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 4))⁻¹ *
        P.contractTwo (symanzikMatrix α (simplexPoint x))
          (loopComp (-loopShift α p (simplexPoint x))) +
      ((m - 6).factorial : ℂ) / 4 *
        ((((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) ^ (m - 5))⁻¹ *
        P.contractFour (symanzikMatrix α (simplexPoint x)))

/-- The coefficient of `W^{3-m}`. -/
noncomputable def coeffOne (x : Fin m → ℝ) : ℂ :=
  ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
    (((m - 4).factorial : ℂ) * P.eval (-loopShift α p (simplexPoint x)))

/-- The coefficient of `W^{4-m}`. -/
noncomputable def coeffTwo (x : Fin m → ℝ) : ℂ :=
  ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
    (((m - 5).factorial : ℂ) / 2 * P.contractTwo (symanzikMatrix α (simplexPoint x))
      (loopComp (-loopShift α p (simplexPoint x))))

/-- The coefficient of `W^{5-m}`. -/
noncomputable def coeffThree (x : Fin m → ℝ) : ℂ :=
  ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
    (((m - 6).factorial : ℂ) / 4 * P.contractFour (symanzikMatrix α (simplexPoint x)))

/-- The complex denominator base `W = V - iε`. -/
noncomputable def wBase (ε : ℝ) (x : Fin m → ℝ) : ℂ :=
  ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I

theorem paramIntegrand_eq (ε : ℝ) (x : Fin m → ℝ) :
    paramIntegrand P α p M ε x =
      coeffOne P α p x * (wBase α p M ε x ^ (m - 3))⁻¹ +
        coeffTwo P α p x * (wBase α p M ε x ^ (m - 4))⁻¹ +
        coeffThree P α x * (wBase α p M ε x ^ (m - 5))⁻¹ := by
  simp only [paramIntegrand, coeffOne, coeffTwo, coeffThree, wBase]
  ring

theorem wBase_ne_zero {ε : ℝ} (hε : ε ≠ 0) (x : Fin m → ℝ) : wBase α p M ε x ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [wBase] at this
  exact hε this

theorem norm_wBase_ge (ε : ℝ) (x : Fin m → ℝ) :
    symanzikV α p M (simplexPoint x) ≤ ‖wBase α p M ε x‖ := by
  have h := Complex.abs_re_le_norm (wBase α p M ε x)
  simp only [wBase, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    sub_zero] at h
  exact (le_abs_self _).trans h

theorem norm_wBase_le (ε : ℝ) (x : Fin m → ℝ) :
    ‖wBase α p M ε x‖ ≤ |symanzikV α p M (simplexPoint x)| + |ε| := by
  refine (norm_sub_le _ _).trans ?_
  simp [Complex.norm_real]

theorem measurable_wBase (ε : ℝ) : Measurable (wBase α p M ε) :=
  (Complex.measurable_ofReal.comp ((measurable_symanzikV α p M).comp
    continuous_simplexPoint'.measurable)).sub measurable_const

end Integrand

/-! ### Interpolation at three equally spaced nodes -/

section Interpolation

variable {n : ℕ} {v : ℝ} {T₁ T₂ T₃ : ℂ}

/-- The three-term sum at a node, multiplied out. -/
theorem three_term_mul_pow {W : ℂ} (hW : W ≠ 0) :
    (T₁ * (W ^ (n + 2))⁻¹ + T₂ * (W ^ (n + 1))⁻¹ + T₃ * (W ^ n)⁻¹) * W ^ (n + 2) =
      T₁ + T₂ * W + T₃ * W ^ 2 := by
  field_simp
  ring

theorem coeff_three_eq {R₁ R₂ R₃ : ℂ}
    (e₁ : R₁ = T₁ + T₂ * ((v : ℂ) - (1 : ℝ) * I) + T₃ * ((v : ℂ) - (1 : ℝ) * I) ^ 2)
    (e₂ : R₂ = T₁ + T₂ * ((v : ℂ) - (2 : ℝ) * I) + T₃ * ((v : ℂ) - (2 : ℝ) * I) ^ 2)
    (e₃ : R₃ = T₁ + T₂ * ((v : ℂ) - (3 : ℝ) * I) + T₃ * ((v : ℂ) - (3 : ℝ) * I) ^ 2) :
    T₃ = -(R₁ - 2 * R₂ + R₃) / 2 := by
  rw [e₁, e₂, e₃]
  push_cast
  linear_combination T₃ * I_sq

theorem coeff_two_eq {R₁ R₃ : ℂ}
    (e₁ : R₁ = T₁ + T₂ * ((v : ℂ) - (1 : ℝ) * I) + T₃ * ((v : ℂ) - (1 : ℝ) * I) ^ 2)
    (e₃ : R₃ = T₁ + T₂ * ((v : ℂ) - (3 : ℝ) * I) + T₃ * ((v : ℂ) - (3 : ℝ) * I) ^ 2) :
    T₂ = (R₁ - R₃) / (2 * I) - 2 * ((v : ℂ) - (2 : ℝ) * I) * T₃ := by
  rw [e₁, e₃, div_eq_mul_inv, mul_inv, Complex.inv_I]
  push_cast
  linear_combination (T₂ + 2 * (v : ℂ) * T₃ - 4 * I * T₃) * I_sq

theorem coeff_one_eq {R₂ : ℂ}
    (e₂ : R₂ = T₁ + T₂ * ((v : ℂ) - (2 : ℝ) * I) + T₃ * ((v : ℂ) - (2 : ℝ) * I) ^ 2) :
    T₁ = R₂ - ((v : ℂ) - (2 : ℝ) * I) * T₂ - ((v : ℂ) - (2 : ℝ) * I) ^ 2 * T₃ := by
  rw [e₂]
  ring

end Interpolation

/-! ### Integrability at fixed `ε > 0` -/

section Analysis

variable {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ)

/-- **The parametric integrand is integrable at every `ε > 0`**, under the pointwise bound and the
criterion. -/
theorem integrableOn_paramIntegrand (hm : 7 ≤ m) {ε : ℝ} (hε : 0 < ε) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 P.eval) :
    IntegrableOn (paramIntegrand P α p M ε) (simplexSet m) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  have hW := integrableOn_refinedWeight_of_criterion α 2 E hcrit
  have hS := integrable_numEnergyValueQuartic_of_refined P α p M hm hε hspan hB hW
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

/-- On the simplex, off the null set `U = 0`, `|V| ≤ K` for a constant `K`. -/
theorem ae_abs_symanzikV_le (hm : 0 < m) (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) :
    ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      |symanzikV α p M (simplexPoint x)| ≤ ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2) := by
  filter_upwards [ae_posDef α hm hspan] with x ⟨hxS, hPD⟩
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  exact abs_symanzikV_le α p M hz.1 hz.2 hPD.det_pos.ne'

/-- **The coefficients are integrable** on the simplex, under the pointwise bound and the
criterion: from the integrability at `ε = 1, 2, 3` by interpolation at the three nodes
`V - i`, `V - 2i`, `V - 3i`. -/
theorem integrableOn_coeff (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
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
    (integrableOn_paramIntegrand P α p M hm hj hcrit hB).mul_bdd
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

/-- The dominating bound at an interior point with `V ≥ c > 0`. -/
theorem norm_paramIntegrand_le {c : ℝ} (hc : 0 < c) (ε : ℝ) {x : Fin m → ℝ}
    (hV : c ≤ symanzikV α p M (simplexPoint x)) :
    ‖paramIntegrand P α p M ε x‖ ≤
      ‖coeffOne P α p x‖ * (c ^ (m - 3))⁻¹ + ‖coeffTwo P α p x‖ * (c ^ (m - 4))⁻¹ +
        ‖coeffThree P α x‖ * (c ^ (m - 5))⁻¹ := by
  have hW : c ≤ ‖wBase α p M ε x‖ := hV.trans (norm_wBase_ge α p M ε x)
  have hk : ∀ k : ℕ, ‖(wBase α p M ε x ^ k)⁻¹‖ ≤ (c ^ k)⁻¹ := fun k => by
    rw [norm_inv, norm_pow]
    exact inv_anti₀ (pow_pos hc k) (pow_le_pow_left₀ hc.le hW k)
  rw [paramIntegrand_eq]
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_) <;>
    rw [norm_mul] <;> exact mul_le_mul_of_nonneg_left (hk _) (norm_nonneg _)

/-- Pointwise continuity in `ε` at `0` where `V ≠ 0`. -/
theorem tendsto_paramIntegrand {x : Fin m → ℝ} (hV : symanzikV α p M (simplexPoint x) ≠ 0) :
    Tendsto (fun ε => paramIntegrand P α p M ε x) (𝓝 0) (𝓝 (paramIntegrand P α p M 0 x)) := by
  have hW0 : wBase α p M 0 x ≠ 0 := by
    simpa [wBase] using hV
  have hcont : Continuous fun ε : ℝ => wBase α p M ε x := by
    unfold wBase
    fun_prop
  have hpow : ∀ k : ℕ, ContinuousAt (fun ε : ℝ => (wBase α p M ε x ^ k)⁻¹) 0 := fun k =>
    (hcont.continuousAt.pow k).inv₀ (pow_ne_zero k hW0)
  have h : ContinuousAt (fun ε => paramIntegrand P α p M ε x) 0 := by
    simp only [paramIntegrand_eq]
    exact ((continuousAt_const.mul (hpow _)).add (continuousAt_const.mul (hpow _))).add
      (continuousAt_const.mul (hpow _))
  exact h.tendsto

/-- **The `ε → 0⁺` limit of the parametric representation.** For `N = m + 1 ≥ 8` propagators, a
numerator with the pointwise bound `RefinedBound α E 4 P.eval`, the criterion
`NoSubdivergenceRefined 2 E α`, and `V ≥ c > 0` at every point of the simplex where `U ≠ 0`: the
joint energy-first integral of `P ∏ᵢ Dᵢ⁻¹`, `Dᵢ = kᵢ·kᵢ + Mᵢ² - iε`, converges as `ε → 0⁺` to
`-π⁴ ∫_Δ paramIntegrand P α p M 0`, the parametric integral with `W = V`. -/
theorem tendsto_jointEnergyFirstIntegral_of_refined (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 P.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.eval ℓ * ∏ i, (lineDenom α p M ε i ℓ)⁻¹)) (𝓝[>] 0)
      (𝓝 (-((π : ℂ) ^ 4) * ∫ x in simplexSet m, paramIntegrand P α p M 0 x)) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  obtain ⟨hT₁, hT₂, hT₃⟩ := integrableOn_coeff P α p hm hcrit hB
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
      exact (integrableOn_paramIntegrand P α p M hm hε hcrit hB).aestronglyMeasurable
    · refine Eventually.of_forall fun ε => ?_
      filter_upwards [hVae] with x hx
      exact norm_paramIntegrand_le P α p M hc ε hx
    · exact ((hT₁.norm.mul_const _).add (hT₂.norm.mul_const _)).add (hT₃.norm.mul_const _)
    · filter_upwards [hVae] with x hx
      exact (tendsto_paramIntegrand P α p M (hc.trans_le hx).ne').mono_left nhdsWithin_le_nhds
  refine (hlim.const_mul (-((π : ℂ) ^ 4))).congr' ?_
  filter_upwards [hpos] with ε hε
  exact ((jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined P α p M hm hε
    hcrit hB).2.2).symm

/-- The limit integrand is integrable on the simplex, under the hypotheses of
`tendsto_jointEnergyFirstIntegral_of_refined`. -/
theorem integrableOn_paramIntegrand_zero (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 P.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) :
    IntegrableOn (paramIntegrand P α p M 0) (simplexSet m) := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by have := hcrit.noSubdivergenceOfOrder i; omega
  obtain ⟨hT₁, hT₂, hT₃⟩ := integrableOn_coeff P α p hm hcrit hB
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

end Analysis

end QED.TwoLoop.ClassLimit

end
