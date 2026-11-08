/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.VertexFormFactors
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The limit of the one-loop Pauli coefficient

On shell the Pauli coefficient is `B = (e²/8π²) ∫ dF₃ (x₃ - x₃²) m² (1/D_{m_γ} - 1/D_Λ)`
(`QED.OneLoop.VertexLimit.formFactorB`), and it depends on the momenta only through `q²`. This
module shows that the normalized integral tends to `1` jointly as `m_γ → 0⁺`, `Λ → ∞`, and
`q² → 0⁺`, by dominated convergence: the integrand is bounded by `4`, and it tends pointwise to
`2(1 - y)`, whose Feynman-parameter integral is `1`.

## Main statements

* `QED.OneLoop.VertexLimit.tendsto_integral_pauliIntegrand`: the joint limit.
* `QED.OneLoop.VertexLimit.exists_abs_integral_pauliIntegrand_sub_one_lt`: its `ε`–`δ` form.
* `QED.OneLoop.VertexLimit.formFactorB_eq`: on shell, `B` is `e²/(8π²)` times the integral.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

/-- The Pauli integrand at regulator data `r = (a, Λ, s)`, with `a` the photon mass and `s` the
momentum transfer `q²`. -/
noncomputable def pauliIntegrand (m : ℝ) (r : ℝ × ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2 *
    (((1 - z.2) * r.1 ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * r.2.2))⁻¹
      - ((1 - z.2) * r.2.1 ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * r.2.2))⁻¹)

theorem formIntegrandB_eq_pauliIntegrand {m mγ Λ : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (z : ℝ × ℝ) :
    formIntegrandB m mγ Λ p' p z
      = pauliIntegrand m (mγ, Λ, Minkowski.dot (p' - p) (p' - p)) z := by
  simp only [formIntegrandB, pauliIntegrand, feynmanMass_onShell hp' hp]

/-- On shell, `B = (e²/8π²) ∫ pauliIntegrand`. -/
theorem formFactorB_eq {e m mγ Λ : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) :
    formFactorB e m mγ Λ p' p = e ^ 2 / (8 * π ^ 2) *
      ∫ z, pauliIntegrand m (mγ, Λ, Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure := by
  simp only [formFactorB, formIntegrandB_eq_pauliIntegrand hp' hp]

/-! ### Elementary bounds -/

/-- `2 y² (1 - y) m² / D ≤ 2` whenever `D ≥ y² m²`. -/
theorem pauli_term_le {m y D : ℝ} (hm : 0 < m) (hy : y ∈ Icc (0 : ℝ) 1)
    (hD : y ^ 2 * m ^ 2 ≤ D) :
    |2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 * D⁻¹| ≤ 2 := by
  have h1y : 0 ≤ 1 - y := by linarith [hy.2]
  have hfac : 2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 = 2 * (1 - y) * (y ^ 2 * m ^ 2) := by ring
  rw [hfac]
  rcases eq_or_lt_of_le hy.1 with h0 | hpos
  · subst h0; simp
  have hym : 0 < y ^ 2 * m ^ 2 := by positivity
  have hDpos : 0 < D := hym.trans_le hD
  rw [abs_of_nonneg (by positivity)]
  calc 2 * (1 - y) * (y ^ 2 * m ^ 2) * D⁻¹ ≤ 2 * 1 * (y ^ 2 * m ^ 2) * (y ^ 2 * m ^ 2)⁻¹ := by
        gcongr
        linarith [hy.1]
    _ = 2 := by field_simp

/-- `t / (t Λ² + c) ≤ 1/Λ²` for `t ≥ 0`, `c ≥ 0`, `Λ ≠ 0`. -/
theorem mul_inv_mul_sq_add_le {t c Λ : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) (hΛ : Λ ≠ 0) :
    t * (t * Λ ^ 2 + c)⁻¹ ≤ (Λ ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0; simp; positivity
  have hΛ2 : 0 < Λ ^ 2 := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  rw [inv_mul_eq_div, le_div_iff₀ hΛ2]
  nlinarith

theorem pauliIntegrand_abs_le {m : ℝ} (hm : 0 < m) {r : ℝ × ℝ × ℝ} (hs : 0 ≤ r.2.2)
    {z : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    |pauliIntegrand m r z| ≤ 4 := by
  obtain ⟨⟨hx0, hx1⟩, hy⟩ := hz
  have hxx : 0 ≤ z.1 * (1 - z.1) := mul_nonneg hx0 (by linarith)
  have hD : ∀ M : ℝ, z.2 ^ 2 * m ^ 2
      ≤ (1 - z.2) * M ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * r.2.2) := by
    intro M
    have h1 : 0 ≤ (1 - z.2) * M ^ 2 := mul_nonneg (by linarith [hy.2]) (sq_nonneg M)
    have h2 : 0 ≤ z.2 ^ 2 * (z.1 * (1 - z.1) * r.2.2) := by positivity
    nlinarith
  have e : pauliIntegrand m r z
      = 2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2 *
          ((1 - z.2) * r.1 ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * r.2.2))⁻¹
        - 2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2 *
          ((1 - z.2) * r.2.1 ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * r.2.2))⁻¹ := by
    simp only [pauliIntegrand]; ring
  rw [e]
  calc _ ≤ |2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2 *
          ((1 - z.2) * r.1 ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * r.2.2))⁻¹|
        + |2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) * m ^ 2 *
          ((1 - z.2) * r.2.1 ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * r.2.2))⁻¹| :=
        abs_sub _ _
    _ ≤ 2 + 2 := add_le_add (pauli_term_le hm hy (hD _)) (pauli_term_le hm hy (hD _))
    _ = 4 := by norm_num

/-! ### The limit -/

/-- The joint regulator filter: `a → 0⁺`, `Λ → ∞`, `s → 0⁺`. -/
abbrev regulatorFilter : Filter (ℝ × ℝ × ℝ) := 𝓝[>] (0 : ℝ) ×ˢ (atTop ×ˢ 𝓝[>] (0 : ℝ))

theorem integral_two_mul_one_sub : ∫ z, 2 * (1 - z.2) ∂feynmanMeasure = 1 := by
  have h := integral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := volume.restrict (Ioc (0 : ℝ) 1)) (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => 2 * (1 - y))
  simp only [one_mul] at h
  rw [feynmanMeasure, h, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  have hhalf : ∫ x in (0 : ℝ)..1, (1 - x) = 1 / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (continuous_id'.intervalIntegrable _ _)]
    simp [integral_id]
    norm_num
  rw [intervalIntegral.integral_const_mul, hhalf]
  norm_num

theorem tendsto_pauliIntegrand {m : ℝ} (hm : 0 < m) {z : ℝ × ℝ}
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    Tendsto (fun r => pauliIntegrand m r z) regulatorFilter (𝓝 (2 * (1 - z.2))) := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
  set x := z.1
  set y := z.2
  -- the photon-mass term converges by continuity
  have hfst : Tendsto (fun r : ℝ × ℝ × ℝ => r.1) regulatorFilter (𝓝 0) :=
    tendsto_fst.mono_right nhdsWithin_le_nhds
  have hsnd : Tendsto (fun r : ℝ × ℝ × ℝ => r.2.2) regulatorFilter (𝓝 0) :=
    (tendsto_snd.comp tendsto_snd).mono_right nhdsWithin_le_nhds
  have hcont : ContinuousAt (fun q : ℝ × ℝ =>
      ((1 - y) * q.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * q.2))⁻¹) (0, 0) := by
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    have h0 : (1 - y) * (0 : ℝ) ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * 0) = y ^ 2 * m ^ 2 := by ring
    show (1 - y) * (0 : ℝ) ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * 0) ≠ 0
    rw [h0]; positivity
  have hγ : Tendsto (fun r : ℝ × ℝ × ℝ =>
      ((1 - y) * r.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * r.2.2))⁻¹) regulatorFilter
      (𝓝 ((y ^ 2 * m ^ 2)⁻¹)) := by
    have h := hcont.tendsto.comp (hfst.prodMk_nhds hsnd)
    simp only [Function.comp_def] at h
    convert h using 2
    simp
  -- the Pauli–Villars term tends to zero
  have hΛ : Tendsto (fun r : ℝ × ℝ × ℝ => r.2.1) regulatorFilter atTop :=
    tendsto_fst.comp tendsto_snd
  have hPV : Tendsto (fun r : ℝ × ℝ × ℝ => 2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 *
      ((1 - y) * r.2.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * r.2.2))⁻¹) regulatorFilter (𝓝 0) := by
    have hbound : ∀ᶠ r : ℝ × ℝ × ℝ in regulatorFilter,
        |2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 *
          ((1 - y) * r.2.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * r.2.2))⁻¹|
          ≤ 2 * m ^ 2 * (r.2.1 ^ 2)⁻¹ := by
      have hpos : ∀ᶠ r : ℝ × ℝ × ℝ in regulatorFilter, 0 < r.2.1 ∧ 0 < r.2.2 :=
        ((hΛ.eventually_gt_atTop 0)).and
          ((tendsto_snd.comp tendsto_snd).eventually self_mem_nhdsWithin)
      refine hpos.mono fun r hr => ?_
      have hc : 0 ≤ y ^ 2 * (m ^ 2 + x * (1 - x) * r.2.2) := by
        have hxx : 0 ≤ x * (1 - x) := mul_nonneg hx0.le (by linarith)
        exact mul_nonneg (sq_nonneg y) (add_nonneg (sq_nonneg m) (mul_nonneg hxx hr.2.le))
      have h1 := mul_inv_mul_sq_add_le (t := 1 - y) (by linarith) hc hr.1.ne'
      have hfac : 2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 = 2 * y ^ 2 * m ^ 2 * (1 - y) := by ring
      have h1y : 0 ≤ 1 - y := by linarith
      have hinv : 0 ≤ ((1 - y) * r.2.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * r.2.2))⁻¹ :=
        inv_nonneg.2 (add_nonneg (mul_nonneg h1y (sq_nonneg _)) hc)
      rw [hfac, abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) h1y) hinv)]
      calc 2 * y ^ 2 * m ^ 2 * (1 - y) *
            ((1 - y) * r.2.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * r.2.2))⁻¹
          = 2 * y ^ 2 * m ^ 2 *
            ((1 - y) * ((1 - y) * r.2.1 ^ 2 + y ^ 2 * (m ^ 2 + x * (1 - x) * r.2.2))⁻¹) := by
            ring
        _ ≤ 2 * 1 * m ^ 2 * (r.2.1 ^ 2)⁻¹ := by
            gcongr
            exact pow_le_one₀ hy0.le hy1
        _ = 2 * m ^ 2 * (r.2.1 ^ 2)⁻¹ := by ring
    have hlim : Tendsto (fun r : ℝ × ℝ × ℝ => 2 * m ^ 2 * (r.2.1 ^ 2)⁻¹) regulatorFilter
        (𝓝 0) := by
      have := ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n := 2) two_ne_zero)).comp hΛ)
      simpa using this.const_mul (2 * m ^ 2)
    exact squeeze_zero_norm' (hbound.mono fun r hr => by simpa [Real.norm_eq_abs] using hr) hlim
  have hval : 2 * (1 - y) = 2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2 * (y ^ 2 * m ^ 2)⁻¹ - 0 := by
    field_simp
    ring
  rw [hval]
  have h := (hγ.const_mul (2 * y * ((1 - y) - (1 - y) ^ 2) * m ^ 2)).sub hPV
  refine h.congr fun r => ?_
  simp only [pauliIntegrand, x, y]
  ring

/-- **The joint limit of the normalized Pauli coefficient.** -/
theorem tendsto_integral_pauliIntegrand {m : ℝ} (hm : 0 < m) :
    Tendsto (fun r => ∫ z, pauliIntegrand m r z ∂feynmanMeasure) regulatorFilter (𝓝 1) := by
  rw [← integral_two_mul_one_sub]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ)) ?_ ?_
    (integrable_const _) (ae_feynmanMeasure.mono fun z hz => tendsto_pauliIntegrand hm hz)
  · refine Eventually.of_forall fun r => ?_
    have : Measurable (pauliIntegrand m r) := by unfold pauliIntegrand; fun_prop
    exact this.aestronglyMeasurable
  · have hs : ∀ᶠ r : ℝ × ℝ × ℝ in regulatorFilter, 0 < r.2.2 :=
      (tendsto_snd.comp tendsto_snd).eventually self_mem_nhdsWithin
    refine hs.mono fun r hr => ae_feynmanMeasure.mono fun z hz => ?_
    rw [Real.norm_eq_abs]
    exact pauliIntegrand_abs_le hm hr.le (Ioc_prod_subset hz)

/-- The `ε`–`δ` form of the joint limit. -/
theorem exists_abs_integral_pauliIntegrand_sub_one_lt {m : ℝ} (hm : 0 < m) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ a Λ s : ℝ, 0 < a → a < δ → R < Λ → 0 < s → s < δ →
      |∫ z, pauliIntegrand m (a, Λ, s) z ∂feynmanMeasure - 1| < η := by
  have h := (tendsto_integral_pauliIntegrand hm).eventually (Metric.ball_mem_nhds 1 hη)
  rw [regulatorFilter, eventually_prod_iff] at h
  obtain ⟨pa, hpa, pq, hpq, hall⟩ := h
  rw [eventually_prod_iff] at hpq
  obtain ⟨pΛ, hpΛ, ps, hps, hall2⟩ := hpq
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpa)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hps)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hpΛ
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, R, fun a Λ s ha haδ hΛ hs hsδ => ?_⟩
  have h1 : pa a := hδ₁' (by
    rw [Real.dist_eq, sub_zero, abs_of_pos ha]; exact haδ.trans_le (min_le_left _ _)) ha
  have h2 : ps s := hδ₂' (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs]; exact hsδ.trans_le (min_le_right _ _)) hs
  have h3 := hall h1 (hall2 (hR Λ hΛ.le) h2)
  simpa [Metric.mem_ball, Real.dist_eq] using h3

end QED.OneLoop.VertexLimit

end
