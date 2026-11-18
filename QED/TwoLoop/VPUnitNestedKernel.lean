/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.PauliLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Feynman-parameter kernel of the one-loop vertex with photon factor `k² d(k)²`

A tool for the nested-form identity of the VP unit (`QED.TwoLoop.UnitVPLink.VPUnitNested`), `δ₃`
half. On the unit square `z = (x, y)` let `C = y² (m² + x(1-x) s)` and
`D_M = (1 - y) M² + C` (the denominators of the one-loop Pauli integrand
`QED.OneLoop.VertexLimit.pauliIntegrand`, `s = q²`). The kernel of the photon factor
`k²/((k² + a²)(k² + b²)(k² + c²)(k² + d²))` is

`kern4 m a b c d s z = 2 y² (1 - y) m² · C (1 - y)² / (D_a D_b D_c D_d)`.

* `sum_mul_pauliIntegrand_eq_kern4`: for distinct squared masses it is the partial-fraction
  combination `∑_{x ∈ {b, c, d}} c_x x² pauliIntegrand m (a, x, s)` of one-loop Pauli integrands,
  `c_x = 1/∏_{y ≠ x} (y² - x²)`.
* `kern4_le`, `integrable_kern4`: `0 ≤ kern4 ≤ 2/(a² b²)` on the square for `s ≥ 0`.
* `tendsto_integral_kern4`: `∫ kern4 m a b c d s → ∫ kernD3 m a b s` as `(c, d) → (a, b)`, with
  `kernD3 m a b = kern4 m a b a b` (dominated convergence).
* `tendsto_integral_kernD3_zero`: `∫ kernD3 m a b s → ∫ kernD3 m a b 0` as `s → 0⁺`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.VPUnitNested

open QED.Integration QED.OneLoop.VertexLimit

/-- `C = y² (m² + x(1-x) s)`. -/
noncomputable def kC (m s : ℝ) (z : ℝ × ℝ) : ℝ := z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * s)

/-- `D_M = (1 - y) M² + C`. -/
noncomputable def kDen (m M s : ℝ) (z : ℝ × ℝ) : ℝ := (1 - z.2) * M ^ 2 + kC m s z

/-- **The kernel of the photon factor `k² ∏ (k² + M²)⁻¹` over four masses.** -/
noncomputable def kern4 (m a b c d s : ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 * kC m s z * (1 - z.2) ^ 2 /
    (kDen m a s z * kDen m b s z * kDen m c s z * kDen m d s z)

/-- **The kernel of the `δ₃` photon factor** `k² (k² + a²)⁻² (k² + b²)⁻²`. -/
noncomputable def kernD3 (m a b s : ℝ) (z : ℝ × ℝ) : ℝ := kern4 m a b a b s z

theorem pauliIntegrand_eq_kDen (m M Λ s : ℝ) (z : ℝ × ℝ) :
    pauliIntegrand m (M, Λ, s) z =
      2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 * ((kDen m M s z)⁻¹ - (kDen m Λ s z)⁻¹) := by
  simp only [pauliIntegrand, kDen, kC]
  ring

/-- The partial-fraction identity behind `sum_mul_pauliIntegrand_eq_kern4`, with the
denominators `D_x = B t_x + C` as atoms. -/
theorem pf_kernel {A B C ta tb tc td Da Db Dc Dd : ℝ} (ha : Da ≠ 0) (hb : Db ≠ 0)
    (hc : Dc ≠ 0) (hd : Dd ≠ 0) (hab : ta - tb ≠ 0) (hac : ta - tc ≠ 0)
    (had : ta - td ≠ 0) (hcb : tc - tb ≠ 0) (hdb : td - tb ≠ 0) (hdc : td - tc ≠ 0)
    (ea : Da = B * ta + C) (eb : Db = B * tb + C) (ec : Dc = B * tc + C) (ed : Dd = B * td + C) :
    ((ta - tb) * (tc - tb) * (td - tb))⁻¹ * tb * (A * (Da⁻¹ - Db⁻¹)) +
        ((ta - tc) * (tb - tc) * (td - tc))⁻¹ * tc * (A * (Da⁻¹ - Dc⁻¹)) +
        ((ta - td) * (tb - td) * (tc - td))⁻¹ * td * (A * (Da⁻¹ - Dd⁻¹)) =
      A * C * B ^ 2 / (Da * Db * Dc * Dd) := by
  have hbc : tb - tc ≠ 0 := fun h => hcb (by linear_combination -h)
  have hbd : tb - td ≠ 0 := fun h => hdb (by linear_combination -h)
  have hcd : tc - td ≠ 0 := fun h => hdc (by linear_combination -h)
  field_simp
  subst ea eb ec ed
  ring

/-- **The partial-fraction combination of one-loop Pauli integrands.** -/
theorem sum_mul_pauliIntegrand_eq_kern4 {m a b c d s : ℝ} {z : ℝ × ℝ}
    (ha : kDen m a s z ≠ 0) (hb : kDen m b s z ≠ 0) (hc : kDen m c s z ≠ 0)
    (hd : kDen m d s z ≠ 0) (hab : a ^ 2 ≠ b ^ 2) (hac : a ^ 2 ≠ c ^ 2) (had : a ^ 2 ≠ d ^ 2)
    (hbc : b ^ 2 ≠ c ^ 2) (hbd : b ^ 2 ≠ d ^ 2) (hcd : c ^ 2 ≠ d ^ 2) :
    ((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2))⁻¹ * b ^ 2 *
          pauliIntegrand m (a, b, s) z +
        ((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2))⁻¹ * c ^ 2 *
          pauliIntegrand m (a, c, s) z +
        ((a ^ 2 - d ^ 2) * (b ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2))⁻¹ * d ^ 2 *
          pauliIntegrand m (a, d, s) z =
      kern4 m a b c d s z := by
  simp only [pauliIntegrand_eq_kDen, kern4]
  exact pf_kernel ha hb hc hd (sub_ne_zero.2 hab) (sub_ne_zero.2 hac) (sub_ne_zero.2 had)
    (sub_ne_zero.2 (Ne.symm hbc)) (sub_ne_zero.2 (Ne.symm hbd)) (sub_ne_zero.2 (Ne.symm hcd))
    rfl rfl rfl rfl

/-! ### Positivity and bounds on the square -/

section Bounds

variable {m s : ℝ} {z : ℝ × ℝ}

theorem kC_ge (hs : 0 ≤ s) (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    z.2 ^ 2 * m ^ 2 ≤ kC m s z := by
  obtain ⟨⟨hx0, hx1⟩, -⟩ := hz
  have : 0 ≤ z.2 ^ 2 * (z.1 * (1 - z.1) * s) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hx0 (by linarith)) hs)
  unfold kC
  nlinarith

theorem kC_pos' (hm : 0 < m) (hs : 0 ≤ s) (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    0 < kC m s z := by
  have hz' : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ⟨Ioc_subset_Icc_self hz.1, Ioc_subset_Icc_self hz.2⟩
  have hy : 0 < z.2 := hz.2.1
  exact lt_of_lt_of_le (by positivity) (kC_ge hs hz')

theorem kDen_pos (M : ℝ) (hm : 0 < m) (hs : 0 ≤ s) (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    0 < kDen m M s z := by
  have h1 : 0 ≤ (1 - z.2) * M ^ 2 := mul_nonneg (by linarith [hz.2.2]) (sq_nonneg M)
  have := kC_pos' hm hs hz
  unfold kDen
  linarith

theorem kern4_eq_mul (m a b c d s : ℝ) (z : ℝ × ℝ) :
    kern4 m a b c d s z =
      (2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 / kDen m d s z) * (kC m s z / kDen m c s z) *
        ((1 - z.2) / kDen m a s z) * ((1 - z.2) / kDen m b s z) := by
  unfold kern4
  ring

theorem one_sub_div_kDen_le {M : ℝ} (hM : 0 < M) (hm : 0 < m) (hs : 0 ≤ s)
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) : (1 - z.2) / kDen m M s z ≤ (M ^ 2)⁻¹ := by
  have hD := kDen_pos M hm hs hz
  have hC := kC_pos' hm hs hz
  rw [div_le_iff₀ hD, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  unfold kDen
  nlinarith

theorem kern4_nonneg {a b c d : ℝ} (hm : 0 < m) (hs : 0 ≤ s)
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) : 0 ≤ kern4 m a b c d s z := by
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have := hz.2.1
  rw [kern4_eq_mul]
  have := kDen_pos a hm hs hz
  have := kDen_pos b hm hs hz
  have := kDen_pos c hm hs hz
  have := kDen_pos d hm hs hz
  have := kC_pos' hm hs hz
  positivity

/-- `kern4 ≤ 2/(a² b²)` on the square, for `s ≥ 0`. -/
theorem kern4_le {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hs : 0 ≤ s)
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    kern4 m a b c d s z ≤ 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹) := by
  have hz' : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ⟨Ioc_subset_Icc_self hz.1, Ioc_subset_Icc_self hz.2⟩
  have hy : 0 < z.2 := hz.2.1
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have hDa := kDen_pos a hm hs hz
  have hDb := kDen_pos b hm hs hz
  have hDc := kDen_pos c hm hs hz
  have hDd := kDen_pos d hm hs hz
  have hC := kC_pos' hm hs hz
  have f1 : 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 / kDen m d s z ≤ 2 := by
    rw [div_le_iff₀ hDd]
    have hCge := kC_ge (m := m) hs hz'
    have : (1 - z.2) * d ^ 2 ≥ 0 := mul_nonneg h1 (sq_nonneg _)
    have hle : z.2 ^ 2 * m ^ 2 ≤ kDen m d s z := by unfold kDen; linarith
    have : 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 ≤ 2 * (z.2 ^ 2 * m ^ 2) := by
      have : 0 ≤ z.2 ^ 2 * m ^ 2 * z.2 := by positivity
      nlinarith
    linarith
  have f2 : kC m s z / kDen m c s z ≤ 1 := by
    rw [div_le_one hDc]
    have : (1 - z.2) * c ^ 2 ≥ 0 := mul_nonneg h1 (sq_nonneg _)
    unfold kDen; linarith
  have f3 := one_sub_div_kDen_le ha hm hs hz
  have f4 := one_sub_div_kDen_le hb hm hs hz
  rw [kern4_eq_mul]
  have g1 : 0 ≤ 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 / kDen m d s z := by positivity
  have g2 : 0 ≤ kC m s z / kDen m c s z := by positivity
  have g3 : 0 ≤ (1 - z.2) / kDen m a s z := by positivity
  have g4 : 0 ≤ (1 - z.2) / kDen m b s z := by positivity
  calc _ ≤ 2 * 1 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ := by gcongr
    _ = 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹) := by ring

end Bounds

theorem measurable_kern4 (m a b c d s : ℝ) : Measurable (kern4 m a b c d s) := by
  unfold kern4 kDen kC
  fun_prop

theorem measurable_pauliIntegrand (m : ℝ) (r : ℝ × ℝ × ℝ) : Measurable (pauliIntegrand m r) := by
  unfold pauliIntegrand
  fun_prop

theorem integrable_kern4 {m a b c d s : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hs : 0 ≤ s) :
    Integrable (kern4 m a b c d s) feynmanMeasure := by
  refine Integrable.mono' (integrable_const (2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹)))
    (measurable_kern4 m a b c d s).aestronglyMeasurable ?_
  filter_upwards [ae_feynmanMeasure] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (kern4_nonneg hm hs hz)]
  exact kern4_le ha hb hm hs hz

theorem integrable_pauliIntegrand {m M Λ s : ℝ} (hm : 0 < m) (hs : 0 ≤ s) :
    Integrable (pauliIntegrand m (M, Λ, s)) feynmanMeasure := by
  refine Integrable.mono' (integrable_const 4)
    (measurable_pauliIntegrand m _).aestronglyMeasurable ?_
  filter_upwards [ae_feynmanMeasure] with z hz
  rw [Real.norm_eq_abs]
  exact pauliIntegrand_abs_le hm (r := (M, Λ, s)) hs (Ioc_prod_subset hz)

/-- **The integrated partial-fraction combination.** -/
theorem sum_mul_integral_pauliIntegrand_eq {m a b c d s : ℝ} (hm : 0 < m) (hs : 0 ≤ s)
    (hab : a ^ 2 ≠ b ^ 2) (hac : a ^ 2 ≠ c ^ 2) (had : a ^ 2 ≠ d ^ 2)
    (hbc : b ^ 2 ≠ c ^ 2) (hbd : b ^ 2 ≠ d ^ 2) (hcd : c ^ 2 ≠ d ^ 2) :
    ((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2))⁻¹ * b ^ 2 *
          ∫ z, pauliIntegrand m (a, b, s) z ∂feynmanMeasure +
        ((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2))⁻¹ * c ^ 2 *
          ∫ z, pauliIntegrand m (a, c, s) z ∂feynmanMeasure +
        ((a ^ 2 - d ^ 2) * (b ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2))⁻¹ * d ^ 2 *
          ∫ z, pauliIntegrand m (a, d, s) z ∂feynmanMeasure =
      ∫ z, kern4 m a b c d s z ∂feynmanMeasure := by
  have h : ∫ z, kern4 m a b c d s z ∂feynmanMeasure = ∫ z,
      (((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2))⁻¹ * b ^ 2 *
          pauliIntegrand m (a, b, s) z +
        ((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2))⁻¹ * c ^ 2 *
          pauliIntegrand m (a, c, s) z) +
        ((a ^ 2 - d ^ 2) * (b ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2))⁻¹ * d ^ 2 *
          pauliIntegrand m (a, d, s) z ∂feynmanMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [ae_feynmanMeasure] with z hz
    exact (sum_mul_pauliIntegrand_eq_kern4 (kDen_pos a hm hs hz).ne' (kDen_pos b hm hs hz).ne'
      (kDen_pos c hm hs hz).ne' (kDen_pos d hm hs hz).ne' hab hac had hbc hbd hcd).symm
  have i1 : Integrable (fun z => ((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2))⁻¹ * b ^ 2 *
      pauliIntegrand m (a, b, s) z) feynmanMeasure := (integrable_pauliIntegrand hm hs).const_mul _
  have i2 : Integrable (fun z => ((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2))⁻¹ * c ^ 2 *
      pauliIntegrand m (a, c, s) z) feynmanMeasure := (integrable_pauliIntegrand hm hs).const_mul _
  have i3 : Integrable (fun z => ((a ^ 2 - d ^ 2) * (b ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2))⁻¹ * d ^ 2 *
      pauliIntegrand m (a, d, s) z) feynmanMeasure := (integrable_pauliIntegrand hm hs).const_mul _
  have i12 : Integrable (fun z => ((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2))⁻¹ * b ^ 2 *
      pauliIntegrand m (a, b, s) z + ((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2))⁻¹ *
        c ^ 2 * pauliIntegrand m (a, c, s) z) feynmanMeasure := i1.add i2
  rw [h, integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-! ### Limits -/

theorem continuousAt_kDen_mass (m s : ℝ) (z : ℝ × ℝ) :
    Continuous fun M => kDen m M s z := by
  unfold kDen
  fun_prop

/-- **`(c, d) → (a, b)`**: the four-mass kernel tends to the `δ₃` kernel, in integral. -/
theorem tendsto_integral_kern4 {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {m a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hs : 0 ≤ s) (c d : ι → ℝ)
    (hc : Tendsto c l (𝓝 a)) (hd : Tendsto d l (𝓝 b)) :
    Tendsto (fun t => ∫ z, kern4 m a b (c t) (d t) s z ∂feynmanMeasure) l
      (𝓝 (∫ z, kernD3 m a b s z ∂feynmanMeasure)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))
    (Eventually.of_forall fun t => (measurable_kern4 m a b _ _ s).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_) (integrable_const _) ?_
  · filter_upwards [ae_feynmanMeasure] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (kern4_nonneg hm hs hz)]
    exact kern4_le ha hb hm hs hz
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hDa := kDen_pos a hm hs hz
    have hDb := kDen_pos b hm hs hz
    have hcd : Tendsto (fun t => kDen m (c t) s z * kDen m (d t) s z) l
        (𝓝 (kDen m a s z * kDen m b s z)) :=
      (((continuousAt_kDen_mass m s z).tendsto a).comp hc).mul
        (((continuousAt_kDen_mass m s z).tendsto b).comp hd)
    have hden : Tendsto (fun t => kDen m a s z * kDen m b s z * kDen m (c t) s z *
        kDen m (d t) s z) l (𝓝 (kDen m a s z * kDen m b s z * kDen m a s z * kDen m b s z)) := by
      have := hcd.const_mul (kDen m a s z * kDen m b s z)
      simpa only [mul_assoc] using this
    have hne : kDen m a s z * kDen m b s z * kDen m a s z * kDen m b s z ≠ 0 := by positivity
    simp only [kernD3, kern4]
    exact tendsto_const_nhds.div hden hne

/-- **`s → 0⁺`**: continuity of the integrated `δ₃` kernel at `s = 0` from the right. -/
theorem tendsto_integral_kernD3_zero {m a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) :
    Tendsto (fun s => ∫ z, kernD3 m a b s z ∂feynmanMeasure) (𝓝[≥] 0)
      (𝓝 (∫ z, kernD3 m a b 0 z ∂feynmanMeasure)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))
    (Eventually.of_forall fun s => (measurable_kern4 m a b a b s).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
    filter_upwards [ae_feynmanMeasure] with z hz
    rw [Real.norm_eq_abs, kernD3, abs_of_nonneg (kern4_nonneg hm hs hz)]
    exact kern4_le ha hb hm hs hz
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hc : Continuous fun s => kC m s z := by unfold kC; fun_prop
    have hD : ∀ M, Continuous fun s => kDen m M s z := fun M => by unfold kDen; fun_prop
    have hne : kDen m a 0 z * kDen m b 0 z * kDen m a 0 z * kDen m b 0 z ≠ 0 := by
      have := kDen_pos a hm le_rfl hz
      have := kDen_pos b hm le_rfl hz
      positivity
    have hcont : ContinuousAt (fun s => kernD3 m a b s z) 0 := by
      simp only [kernD3, kern4]
      exact ((continuous_const.mul hc).mul continuous_const).continuousAt.div
        ((((hD a).mul (hD b)).mul (hD a)).mul (hD b)).continuousAt hne
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

end QED.TwoLoop.VPUnitNested

end
