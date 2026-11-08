/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.ChargeRenormalization
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Limits of the Pauli coefficient for the magnetic moment

Facts about the normalized Pauli coefficient `∫ pauliIntegrand m (a, Λ, s)` used for the
magnetic moment:

* `tendsto_integral_pauliIntegrand_of`: the limit `1` along any family with `a → 0`, `Λ → ∞`,
  `s → 0` and `s ≥ 0`, which includes `s = 0` exactly;
* `exists_abs_integral_pauliIntegrand_zero_sub_one_lt`: at `q² = 0`, the joint regulator limit in
  `ε`–`δ` form;
* `exists_abs_integral_pauliIntegrand_sub_lt`: continuity at `q² = 0⁺` at fixed regulators.

These are internal helpers.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

/-- Pointwise limit of the Pauli integrand along any family with `a → 0`, `Λ → ∞`, `s → 0`,
`s ≥ 0`. -/
theorem tendsto_pauliIntegrand_of {ι : Type*} {l : Filter ι} {r : ι → ℝ × ℝ × ℝ} {m : ℝ}
    (hm : 0 < m) (ha : Tendsto (fun i => (r i).1) l (𝓝 0))
    (hΛ : Tendsto (fun i => (r i).2.1) l atTop) (hs : Tendsto (fun i => (r i).2.2) l (𝓝 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ (r i).2.2) {z : ℝ × ℝ} (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    Tendsto (fun i => pauliIntegrand m (r i) z) l (𝓝 (2 * (1 - z.2))) := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
  set x := z.1
  set y := z.2
  have hcont : ContinuousAt (fun q : ℝ × ℝ =>
      ((1 - y) * q.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * q.2))⁻¹) (0, 0) := by
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    have h0 : (1 - y) * (0 : ℝ) ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * 0) = y ^ 2 * m ^ 2 := by ring
    show (1 - y) * (0 : ℝ) ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * 0) ≠ 0
    rw [h0]; positivity
  have hγ : Tendsto (fun i => ((1 - y) * (r i).1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * (r i).2.2))⁻¹)
      l (𝓝 ((y ^ 2 * m ^ 2)⁻¹)) := by
    have h := hcont.tendsto.comp (ha.prodMk_nhds hs)
    simp only [Function.comp_def] at h
    convert h using 2
    simp
  have hPV : Tendsto (fun i => 2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 *
      ((1 - y) * (r i).2.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * (r i).2.2))⁻¹) l (𝓝 0) := by
    have hbound : ∀ᶠ i in l,
        |2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 *
          ((1 - y) * (r i).2.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * (r i).2.2))⁻¹|
          ≤ 2 * m ^ 2 * ((r i).2.1 ^ 2)⁻¹ := by
      refine ((hΛ.eventually_gt_atTop 0).and hs0).mono fun i hi => ?_
      have hc : 0 ≤ y ^ 2 * (m ^ 2 + x * (1 - x) * (r i).2.2) := by
        have hxx : 0 ≤ x * (1 - x) := mul_nonneg hx0.le (by linarith)
        exact mul_nonneg (sq_nonneg y) (add_nonneg (sq_nonneg m) (mul_nonneg hxx hi.2))
      have h1 := mul_inv_mul_sq_add_le (t := 1 - y) (by linarith) hc hi.1.ne'
      have hfac : 2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 = 2 * y ^ 2 * m ^ 2 * (1 - y) := by ring
      have h1y : 0 ≤ 1 - y := by linarith
      have hinv : 0 ≤ ((1 - y) * (r i).2.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * (r i).2.2))⁻¹ :=
        inv_nonneg.2 (add_nonneg (mul_nonneg h1y (sq_nonneg _)) hc)
      rw [hfac, abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) h1y) hinv)]
      calc 2 * y ^ 2 * m ^ 2 * (1 - y) *
            ((1 - y) * (r i).2.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * (r i).2.2))⁻¹
          = 2 * y ^ 2 * m ^ 2 *
            ((1 - y) * ((1 - y) * (r i).2.1 ^ 2
              + y ^ 2 * (m ^ 2 + x * (1 - x) * (r i).2.2))⁻¹) := by ring
        _ ≤ 2 * 1 * m ^ 2 * ((r i).2.1 ^ 2)⁻¹ := by
            gcongr
            exact pow_le_one₀ hy0.le hy1
        _ = 2 * m ^ 2 * ((r i).2.1 ^ 2)⁻¹ := by ring
    have hlim : Tendsto (fun i => 2 * m ^ 2 * ((r i).2.1 ^ 2)⁻¹) l (𝓝 0) := by
      have := ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n := 2) two_ne_zero)).comp hΛ)
      simpa using this.const_mul (2 * m ^ 2)
    exact squeeze_zero_norm' (hbound.mono fun i hi => by simpa [Real.norm_eq_abs] using hi) hlim
  have hval : 2 * (1 - y) = 2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 * (y ^ 2 * m ^ 2)⁻¹ - 0 := by
    field_simp
    ring
  rw [hval]
  have h := (hγ.const_mul (2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2)).sub hPV
  refine h.congr fun i => ?_
  simp only [pauliIntegrand, x, y]
  ring

/-- The limit `1` of the normalized Pauli coefficient along any countably generated family with
`a → 0`, `Λ → ∞`, `s → 0`, `s ≥ 0`. -/
theorem tendsto_integral_pauliIntegrand_of {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {r : ι → ℝ × ℝ × ℝ} {m : ℝ} (hm : 0 < m) (ha : Tendsto (fun i => (r i).1) l (𝓝 0))
    (hΛ : Tendsto (fun i => (r i).2.1) l atTop) (hs : Tendsto (fun i => (r i).2.2) l (𝓝 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ (r i).2.2) :
    Tendsto (fun i => ∫ z, pauliIntegrand m (r i) z ∂feynmanMeasure) l (𝓝 1) := by
  rw [← integral_two_mul_one_sub]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ)) ?_ ?_
    (integrable_const _)
    (ae_feynmanMeasure.mono fun z hz => tendsto_pauliIntegrand_of hm ha hΛ hs hs0 hz)
  · refine Eventually.of_forall fun i => ?_
    have : Measurable (pauliIntegrand m (r i)) := by unfold pauliIntegrand; fun_prop
    exact this.aestronglyMeasurable
  · refine hs0.mono fun i hi => ae_feynmanMeasure.mono fun z hz => ?_
    rw [Real.norm_eq_abs]
    exact pauliIntegrand_abs_le hm hi (Ioc_prod_subset hz)

/-- At `q² = 0`, the normalized Pauli coefficient tends to `1` jointly as `m_γ → 0⁺` and
`Λ → ∞`. -/
theorem exists_abs_integral_pauliIntegrand_zero_sub_one_lt {m : ℝ} (hm : 0 < m) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ a Λ : ℝ, 0 < a → a < δ → R < Λ →
      |∫ z, pauliIntegrand m (a, Λ, 0) z ∂feynmanMeasure - 1| < η := by
  have h := (tendsto_integral_pauliIntegrand_of (l := 𝓝[>] (0 : ℝ) ×ˢ atTop)
    (r := fun q : ℝ × ℝ => (q.1, q.2, (0 : ℝ))) hm
    (tendsto_fst.mono_right nhdsWithin_le_nhds) tendsto_snd tendsto_const_nhds
    (Eventually.of_forall fun _ => le_rfl)).eventually (Metric.ball_mem_nhds 1 hη)
  rw [eventually_prod_iff] at h
  obtain ⟨pa, hpa, pΛ, hpΛ, hall⟩ := h
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpa)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hpΛ
  refine ⟨δ, hδ, R, fun a Λ ha haδ hΛ => ?_⟩
  have h1 : pa a := hδ' (by rw [Real.dist_eq, sub_zero, abs_of_pos ha]; exact haδ) ha
  have h3 := hall h1 (hR Λ hΛ.le)
  simpa [Metric.mem_ball, Real.dist_eq] using h3

/-- Continuity of the normalized Pauli coefficient at `q² = 0⁺`, at fixed regulators. -/
theorem exists_abs_integral_pauliIntegrand_sub_lt {m a Λ : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hΛ : 0 < Λ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      |∫ z, pauliIntegrand m (a, Λ, s) z ∂feynmanMeasure
        - ∫ z, pauliIntegrand m (a, Λ, 0) z ∂feynmanMeasure| < η := by
  have hpt : ∀ z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1,
      ContinuousAt (fun s => pauliIntegrand m (a, Λ, s) z) 0 := by
    intro z hz
    have hzI := Ioc_prod_subset hz
    have hD : ∀ M : ℝ, 0 < M → (1 - z.2) * M ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * 0) ≠ 0 :=
      fun M hM => by
        have := massDq_pos hm hM le_rfl hzI
        simpa [massDq] using this.ne'
    have h1 : ContinuousAt (fun s : ℝ =>
        ((1 - z.2) * a ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * s))⁻¹) 0 :=
      ContinuousAt.inv₀ (by fun_prop) (hD a ha)
    have h2 : ContinuousAt (fun s : ℝ =>
        ((1 - z.2) * Λ ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * s))⁻¹) 0 :=
      ContinuousAt.inv₀ (by fun_prop) (hD Λ hΛ)
    simp only [pauliIntegrand]
    exact continuousAt_const.mul (h1.sub h2)
  have hlim : Tendsto (fun s => ∫ z, pauliIntegrand m (a, Λ, s) z ∂feynmanMeasure) (𝓝[>] 0)
      (𝓝 (∫ z, pauliIntegrand m (a, Λ, 0) z ∂feynmanMeasure)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ)) ?_ ?_
      (integrable_const _) (ae_feynmanMeasure.mono fun z hz =>
        tendsto_nhdsWithin_of_tendsto_nhds (hpt z hz).tendsto)
    · refine Eventually.of_forall fun s => ?_
      have : Measurable (pauliIntegrand m (a, Λ, s)) := by unfold pauliIntegrand; fun_prop
      exact this.aestronglyMeasurable
    · refine (eventually_nhdsWithin_of_forall fun s (hs : 0 < s) => hs.le).mono
        fun s hs => ae_feynmanMeasure.mono fun z hz => ?_
      rw [Real.norm_eq_abs]
      exact pauliIntegrand_abs_le hm hs (Ioc_prod_subset hz)
  have h := hlim.eventually (Metric.ball_mem_nhds _ hη)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h)
  refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
  have := hδ' (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; exact hsδ) hs
  simpa [Metric.mem_ball, Real.dist_eq] using this

end QED.OneLoop.VertexLimit

end
