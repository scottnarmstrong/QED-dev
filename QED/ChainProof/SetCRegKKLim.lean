/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKFeyn

/-!
# Set (c): the `ε → 0⁺` limit of the scalar Källén–Lehmann integral

By `QED/ChainProof/SetCRegKKFeyn.lean`, at `ε > 0` the energy integral of `kkScl` at
spatial momentum `v` is `96 ∫_{Δ₄} kkPhi(ε, x, v) dx`. Here we let `ε → 0⁺`:

* at fixed `v`, dominated convergence on the (finite-measure) simplex, using the
  continuity of the one-loop closed forms `kkSp4`, `kkSp5` at `δ = 0`;
* over `v`, dominated convergence with the bound
  `C₄ (|v|² + μ₀)^{-7/2} + C₅ (|v|² + μ₀)^{-9/2}`, `μ₀ = min(c, a, b)`;
* at `ε = 0`, Fubini and the spatial values `i π²/(6 A²)`, `i π²/(12 A³)` of
  `QED/ChainProof/SetCRegKKRad.lean`, which combine to `i π²/(12 M(x)²)`.

## Main result

* `tendsto_energyFirstIntegral_kkScl`:
  `energyFirstIntegral (kkScl mγ Λ τ ε) → 8 i π² ∫_{Δ₄} M(x)⁻² dx` as `ε → 0⁺`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.Integration QED.Integration.Feynman

/-- The dominating function in `v`. -/
noncomputable def kkBnd (c a b : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  5 * π / 16 * (∑ k, v k ^ 2 + min c (min a b)) ^ (-(7 / 2 : ℝ)) +
    (c + a + b + 4) * (35 * π / 128) * (∑ k, v k ^ 2 + min c (min a b)) ^ (-(9 / 2 : ℝ))

theorem integrable_kkBnd {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    Integrable (kkBnd c a b) := by
  have hμ : 0 < min c (min a b) := lt_min hc (lt_min ha hb)
  exact ((integrable_sum_sq_add_rpow hμ (by norm_num)).const_mul _).add
    ((integrable_sum_sq_add_rpow hμ (by norm_num)).const_mul _)

theorem measurable_kkPhi (c a b ε : ℝ) :
    Measurable fun p : (Fin 3 → ℝ) × (Fin 4 → ℝ) => kkPhi c a b ε p.2 p.1 := by
  unfold kkPhi kkSp4 kkSp5 kkW kkM kkE
  fun_prop

theorem norm_kkPhi_le {c a b ε : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {x : Fin 4 → ℝ} (hx : x ∈ simplexSet 4) (v : Fin 3 → ℝ) :
    ‖kkPhi c a b ε x v‖ ≤ kkBnd c a b v := by
  have hμ : 0 < min c (min a b) := lt_min hc (lt_min ha hb)
  obtain ⟨hM0, hM1⟩ := kkM_bounds hc ha hb hx
  obtain ⟨hE0, hE1⟩ := kkE_bounds hx
  set A := kkM c a b x
  set δ := ε * kkE x
  have hA : 0 < A := hμ.trans_le hM0
  have hR : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h7 : (∑ k, v k ^ 2 + A) ^ (-(7 / 2 : ℝ)) ≤
      (∑ k, v k ^ 2 + min c (min a b)) ^ (-(7 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have h9 : (∑ k, v k ^ 2 + A) ^ (-(9 / 2 : ℝ)) ≤
      (∑ k, v k ^ 2 + min c (min a b)) ^ (-(9 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hAδ : ‖((A : ℝ) : ℂ) - ((δ : ℝ) : ℂ) * I‖ ≤ c + a + b + 4 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hA, abs_of_nonneg (by positivity)]
    nlinarith
  have h4 := norm_kkSp4_le hA δ v
  have h5 := norm_kkSp5_le hA δ v
  calc ‖kkPhi c a b ε x v‖
      ≤ ‖kkSp4 A δ v‖ + ‖((A : ℝ) : ℂ) - ((δ : ℝ) : ℂ) * I‖ * ‖kkSp5 A δ v‖ := by
        rw [kkPhi, ← norm_mul]
        exact norm_sub_le _ _
    _ ≤ 5 * π / 16 * (∑ k, v k ^ 2 + A) ^ (-(7 / 2 : ℝ)) +
        (c + a + b + 4) * (35 * π / 128 * (∑ k, v k ^ 2 + A) ^ (-(9 / 2 : ℝ))) := by
        gcongr
    _ ≤ kkBnd c a b v := by
        rw [kkBnd]
        have hp : 0 ≤ π := Real.pi_pos.le
        nlinarith [mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ 5 * π / 16),
          mul_le_mul_of_nonneg_left h9
            (by positivity : (0 : ℝ) ≤ (c + a + b + 4) * (35 * π / 128))]

/-- At `x` in the simplex, `kkPhi(ε, x, v) → kkPhi(0, x, v)` as `ε → 0⁺`. -/
theorem tendsto_kkPhi {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    {x : Fin 4 → ℝ} (hx : x ∈ simplexSet 4) (v : Fin 3 → ℝ) :
    Tendsto (fun ε => kkPhi c a b ε x v) (𝓝[>] 0) (𝓝 (kkPhi c a b 0 x v)) := by
  have hA : 0 < kkM c a b x :=
    (lt_min hc (lt_min ha hb)).trans_le (kkM_bounds hc ha hb hx).1
  have hE : 0 ≤ kkE x := by linarith [(kkE_bounds hx).1]
  have h0 : Tendsto (fun ε : ℝ => ε * kkE x) (𝓝[>] 0) (𝓝 0) := by
    have := (Continuous.tendsto (f := fun ε : ℝ => ε * kkE x) (by fun_prop) 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hδ : Tendsto (fun ε : ℝ => ε * kkE x) (𝓝[>] 0) (𝓝[≥] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0
      (eventually_nhdsWithin_of_forall fun ε hε => mul_nonneg (le_of_lt hε) hE)
  have hcont : Continuous fun ε : ℝ =>
      ((kkM c a b x : ℝ) : ℂ) - ((ε * kkE x : ℝ) : ℂ) * I := by fun_prop
  have h := ((tendsto_kkSp4 hA v).comp hδ).sub
    ((hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      ((tendsto_kkSp5 hA v).comp hδ))
  simpa only [kkPhi, zero_mul, Function.comp_def] using h

/-- Dominated convergence on the simplex at fixed `v`. -/
theorem tendsto_integral_kkPhi {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (v : Fin 3 → ℝ) :
    Tendsto (fun ε => ∫ x in simplexSet 4, kkPhi c a b ε x v) (𝓝[>] 0)
      (𝓝 (∫ x in simplexSet 4, kkPhi c a b 0 x v)) := by
  have := isFiniteMeasure_simplex
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => kkBnd c a b v)
    (Eventually.of_forall fun ε =>
      ((measurable_kkPhi c a b ε).comp measurable_prodMk_left).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    exact ae_restrict_of_forall_mem (measurableSet_simplexSet 4) fun x hx =>
      norm_kkPhi_le hc ha hb hε.1.le hε.2.le hx v
  · exact ae_restrict_of_forall_mem (measurableSet_simplexSet 4) fun x hx =>
      tendsto_kkPhi hc ha hb hx v

/-- Dominated convergence over the spatial momentum. -/
theorem tendsto_integral_kkH {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun ε => ∫ v : Fin 3 → ℝ, 96 * ∫ x in simplexSet 4, kkPhi c a b ε x v)
      (𝓝[>] 0) (𝓝 (∫ v : Fin 3 → ℝ, 96 * ∫ x in simplexSet 4, kkPhi c a b 0 x v)) := by
  have hfin : volume (simplexSet 4) < ⊤ := (isCompact_simplexSet 4).measure_lt_top
  refine tendsto_integral_filter_of_dominated_convergence
    (fun v => 96 * (kkBnd c a b v * volume.real (simplexSet 4)))
    (Eventually.of_forall fun ε =>
      (((measurable_kkPhi c a b ε).stronglyMeasurable.integral_prod_right
        (f := fun v x => kkPhi c a b ε x v)
        (ν := volume.restrict (simplexSet 4))).aestronglyMeasurable.const_mul 96)) ?_
    (((integrable_kkBnd hc ha hb).mul_const _).const_mul _)
    (Eventually.of_forall fun v => (tendsto_integral_kkPhi hc ha hb v).const_mul 96)
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  refine Eventually.of_forall fun v => ?_
  rw [norm_mul, show ‖(96 : ℂ)‖ = 96 by norm_num]
  gcongr
  exact norm_setIntegral_le_of_norm_le_const hfin fun x hx =>
    norm_kkPhi_le hc ha hb hε.1.le hε.2.le hx v

theorem integrable_kkSp4_zero {A : ℝ} (hA : 0 < A) : Integrable fun v => kkSp4 A 0 v := by
  simp_rw [kkSp4_zero hA]
  exact (((integrable_sum_sq_add_rpow hA (by norm_num)).const_mul _).ofReal).const_mul I

theorem integrable_kkSp5_zero {A : ℝ} (hA : 0 < A) : Integrable fun v => kkSp5 A 0 v := by
  simp_rw [kkSp5_zero hA]
  exact (((integrable_sum_sq_add_rpow hA (by norm_num)).const_mul _).ofReal).const_mul I

/-- The spatial integral of `kkPhi` at `ε = 0`: `i π²/(12 A²)`. -/
theorem integral_kkPhi_zero {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    {x : Fin 4 → ℝ} (hx : x ∈ simplexSet 4) :
    ∫ v : Fin 3 → ℝ, kkPhi c a b 0 x v =
      ((π ^ 2 / 12 * (kkM c a b x ^ 2)⁻¹ : ℝ) : ℂ) * I := by
  have hA : 0 < kkM c a b x :=
    (lt_min hc (lt_min ha hb)).trans_le (kkM_bounds hc ha hb hx).1
  simp only [kkPhi, zero_mul, ofReal_zero, sub_zero]
  rw [integral_sub (integrable_kkSp4_zero hA) ((integrable_kkSp5_zero hA).const_mul _),
    integral_const_mul, integral_kkSp4_zero hA, integral_kkSp5_zero hA]
  have hA' : (kkM c a b x : ℂ) ≠ 0 := ofReal_ne_zero.2 hA.ne'
  push_cast
  field_simp
  ring

/-- Fubini at `ε = 0`. -/
theorem integral_kkH_zero {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    ∫ v : Fin 3 → ℝ, 96 * ∫ x in simplexSet 4, kkPhi c a b 0 x v =
      ((8 * π ^ 2 * ∫ x in simplexSet 4, (kkM c a b x ^ 2)⁻¹ : ℝ) : ℂ) * I := by
  have := isFiniteMeasure_simplex
  have hae : ∀ᵐ p ∂((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (simplexSet 4))),
      p ∈ univ ×ˢ simplexSet 4 := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Fin 3 → ℝ))), Measure.prod_restrict]
    exact ae_restrict_mem (MeasurableSet.univ.prod (measurableSet_simplexSet 4))
  have hint : Integrable (Function.uncurry fun v x => kkPhi c a b 0 x v)
      ((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (simplexSet 4))) := by
    refine Integrable.mono' ((integrable_kkBnd hc ha hb).mul_prod (integrable_const (1 : ℝ)))
      (measurable_kkPhi c a b 0).aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    rw [mul_one]
    exact norm_kkPhi_le hc ha hb le_rfl zero_le_one hp.2 p.1
  rw [integral_const_mul, integral_integral_swap hint,
    setIntegral_congr_fun (measurableSet_simplexSet 4) fun x hx =>
      integral_kkPhi_zero hc ha hb hx,
    integral_mul_const, integral_complex_ofReal, integral_const_mul]
  push_cast
  ring

/-- **The `ε → 0⁺` limit of the scalar integral**: `8 i π² ∫_{Δ₄} M(x)⁻² dx`. -/
theorem tendsto_energyFirstIntegral_kkScl {mγ Λ τ : ℝ} (hτ : 0 < τ) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (kkScl mγ Λ τ ε)) (𝓝[>] 0)
      (𝓝 (((8 * π ^ 2 * ∫ x in simplexSet 4,
        (kkM (4 * τ ^ 2) (mγ ^ 2) (Λ ^ 2) x ^ 2)⁻¹ : ℝ) : ℂ) * I)) := by
  have hc : 0 < 4 * τ ^ 2 := by positivity
  have ha : 0 < mγ ^ 2 := by positivity
  have hb : 0 < Λ ^ 2 := by positivity
  rw [← integral_kkH_zero hc ha hb]
  refine (tendsto_integral_kkH hc ha hb).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [QED.OneLoop.energyFirstIntegral]
  exact integral_congr_ae (Eventually.of_forall fun v =>
    (integral_kkScl_cons hτ hmγ hΛ hε v).symm)

end QED.ChainProof.SetCRegDisp
