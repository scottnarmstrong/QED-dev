/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPUnitNestedKernel
public import QED.TwoLoop.VacuumPolarizationUnitLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Feynman-parameter kernel of the one-loop vertex with five photon masses

A tool for the bubble half `QED.TwoLoop.VPUnitNested.VPHalf` of the nested form of the VP unit.
After the Pauli projection, one spectral component (spectral mass `μ`) of the vacuum-polarization
insertion turns the photon factor of the one-loop vertex into
`(Λ² - m_γ²)² k⁴ / ((k² + m_γ²)² (k² + Λ²)² (k² + μ²))`: the `δ₃` factor of
`QED/TwoLoop/VPUnitNestedKernel.lean` times `k²/(k² + μ²)`. This file is the five-mass extension
of that kernel. With `C = y² (m² + x(1-x) s)` and `D_M = (1 - y) M² + C` on the unit square, the
kernel of `k⁴ / ∏_{M ∈ {a, b, c, d, μ}} (k² + M²)` is

`kern5 m a b c d μ s z = 2 y² (1 - y) m² · C² (1 - y)² / (D_a D_b D_c D_d D_μ)`.

* `sum_mul_pauliIntegrand_eq_kern5`: for distinct squared masses it is the partial-fraction
  combination `∑_{x ∈ {b, c, d, μ}} κ_x pauliIntegrand m (a, x, s)` of one-loop Pauli integrands,
  `κ_x = -x⁴/∏_{y ≠ x} (y² - x²)`.
* `kern5_le`, `integrable_kern5`: `0 ≤ kern5 ≤ 2/(a² b²)` on the square for `s ≥ 0`.
* `tendsto_integral_kern5`: `∫ kern5 m a b c d μ s → ∫ kernVP m a b μ s` as `(c, d) → (a, b)`,
  with `kernVP m a b μ = kern5 m a b a b μ` (dominated convergence).
* `tendsto_integral_kernVP_zero`, `tendsto_integral_kern5_zero`: continuity of the kernel
  integrals at `s = 0` from the right.
* `kernVPOne_mul`, `integral_kernVP_one_zero_mul`: at `m = 1`, `s = 0`,
  `(b² - a²)² ∫ kernVP 1 a b μ 0 = 2 ∫₀¹ regKernel μ² a² b²`, the outer integrand of the photon
  function `s D(s)² · s/(s + μ²)` (`QED.TwoLoop.VPUnit.regKernel`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.VPHalf

open QED.Integration QED.OneLoop.VertexLimit QED.TwoLoop.VPUnitNested

/-- **The kernel of the photon factor `k⁴ ∏ (k² + M²)⁻¹` over five masses.** -/
noncomputable def kern5 (m a b c d μ s : ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 * kC m s z ^ 2 * (1 - z.2) ^ 2 /
    (kDen m a s z * kDen m b s z * kDen m c s z * kDen m d s z * kDen m μ s z)

/-- **The kernel of one spectral component of the VP insertion**:
`k⁴ (k² + a²)⁻² (k² + b²)⁻² (k² + μ²)⁻¹`. -/
noncomputable def kernVP (m a b μ s : ℝ) (z : ℝ × ℝ) : ℝ := kern5 m a b a b μ s z

/-- The partial-fraction identity behind `sum_mul_pauliIntegrand_eq_kern5`, with the
denominators `D_x = B t_x + C` as atoms, in any field. -/
theorem pf_kernel5 {K : Type*} [Field K] {A B C ta tb tc td te Da Db Dc Dd De : K}
    (ha : Da ≠ 0) (hb : Db ≠ 0) (hc : Dc ≠ 0) (hd : Dd ≠ 0) (he : De ≠ 0) (hab : ta - tb ≠ 0)
    (hac : ta - tc ≠ 0) (had : ta - td ≠ 0) (hae : ta - te ≠ 0) (hcb : tc - tb ≠ 0) (hdb : td - tb ≠ 0)
    (heb : te - tb ≠ 0) (hdc : td - tc ≠ 0) (hec : te - tc ≠ 0) (hed : te - td ≠ 0)
    (ea : Da = B * ta + C) (eb : Db = B * tb + C) (ec : Dc = B * tc + C) (ed : Dd = B * td + C)
    (ee : De = B * te + C) :
    -((ta - tb) * (tc - tb) * (td - tb) * (te - tb))⁻¹ * tb ^ 2 * (A * (Da⁻¹ - Db⁻¹)) +
        -((ta - tc) * (tb - tc) * (td - tc) * (te - tc))⁻¹ * tc ^ 2 * (A * (Da⁻¹ - Dc⁻¹)) +
        -((ta - td) * (tb - td) * (tc - td) * (te - td))⁻¹ * td ^ 2 * (A * (Da⁻¹ - Dd⁻¹)) +
        -((ta - te) * (tb - te) * (tc - te) * (td - te))⁻¹ * te ^ 2 * (A * (Da⁻¹ - De⁻¹)) =
      A * C ^ 2 * B ^ 2 / (Da * Db * Dc * Dd * De) := by
  have hbc : tb - tc ≠ 0 := fun h => hcb (by linear_combination -h)
  have hbd : tb - td ≠ 0 := fun h => hdb (by linear_combination -h)
  have hbe : tb - te ≠ 0 := fun h => heb (by linear_combination -h)
  have hcd : tc - td ≠ 0 := fun h => hdc (by linear_combination -h)
  have hce : tc - te ≠ 0 := fun h => hec (by linear_combination -h)
  have hde : td - te ≠ 0 := fun h => hed (by linear_combination -h)
  field_simp
  subst ea eb ec ed ee
  ring

/-- **The partial-fraction combination of one-loop Pauli integrands.** -/
theorem sum_mul_pauliIntegrand_eq_kern5 {m a b c d μ s : ℝ} {z : ℝ × ℝ}
    (ha : kDen m a s z ≠ 0) (hb : kDen m b s z ≠ 0) (hc : kDen m c s z ≠ 0)
    (hd : kDen m d s z ≠ 0) (hμ : kDen m μ s z ≠ 0) (hab : a ^ 2 ≠ b ^ 2) (hac : a ^ 2 ≠ c ^ 2)
    (had : a ^ 2 ≠ d ^ 2) (haμ : a ^ 2 ≠ μ ^ 2) (hbc : b ^ 2 ≠ c ^ 2) (hbd : b ^ 2 ≠ d ^ 2)
    (hbμ : b ^ 2 ≠ μ ^ 2) (hcd : c ^ 2 ≠ d ^ 2) (hcμ : c ^ 2 ≠ μ ^ 2) (hdμ : d ^ 2 ≠ μ ^ 2) :
    -((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2) * (μ ^ 2 - b ^ 2))⁻¹ * (b ^ 2) ^ 2 *
          pauliIntegrand m (a, b, s) z +
        -((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2) * (μ ^ 2 - c ^ 2))⁻¹ * (c ^ 2) ^ 2 *
          pauliIntegrand m (a, c, s) z +
        -((a ^ 2 - d ^ 2) * (b ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2) * (μ ^ 2 - d ^ 2))⁻¹ * (d ^ 2) ^ 2 *
          pauliIntegrand m (a, d, s) z +
        -((a ^ 2 - μ ^ 2) * (b ^ 2 - μ ^ 2) * (c ^ 2 - μ ^ 2) * (d ^ 2 - μ ^ 2))⁻¹ * (μ ^ 2) ^ 2 *
          pauliIntegrand m (a, μ, s) z =
      kern5 m a b c d μ s z := by
  simp only [pauliIntegrand_eq_kDen, kern5]
  rw [pf_kernel5 (A := 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2) ha hb hc hd hμ (sub_ne_zero.2 hab)
    (sub_ne_zero.2 hac) (sub_ne_zero.2 had) (sub_ne_zero.2 haμ) (sub_ne_zero.2 (Ne.symm hbc))
    (sub_ne_zero.2 (Ne.symm hbd)) (sub_ne_zero.2 (Ne.symm hbμ)) (sub_ne_zero.2 (Ne.symm hcd))
    (sub_ne_zero.2 (Ne.symm hcμ)) (sub_ne_zero.2 (Ne.symm hdμ)) rfl rfl rfl rfl rfl]

/-! ### Positivity and bounds on the square -/

section Bounds

variable {m s : ℝ} {z : ℝ × ℝ}

theorem kern5_eq_mul (m a b c d μ s : ℝ) (z : ℝ × ℝ) :
    kern5 m a b c d μ s z =
      (2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 / kDen m μ s z) * (kC m s z / kDen m d s z) *
        (kC m s z / kDen m c s z) * ((1 - z.2) / kDen m a s z) * ((1 - z.2) / kDen m b s z) := by
  unfold kern5
  ring

theorem kern5_nonneg {a b c d μ : ℝ} (hm : 0 < m) (hs : 0 ≤ s)
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) : 0 ≤ kern5 m a b c d μ s z := by
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have := hz.2.1
  rw [kern5_eq_mul]
  have := kDen_pos a hm hs hz
  have := kDen_pos b hm hs hz
  have := kDen_pos c hm hs hz
  have := kDen_pos d hm hs hz
  have := kDen_pos μ hm hs hz
  have := kC_pos' hm hs hz
  positivity

/-- `kern5 ≤ 2/(a² b²)` on the square, for `s ≥ 0`. -/
theorem kern5_le {a b c d μ : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hs : 0 ≤ s)
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :
    kern5 m a b c d μ s z ≤ 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹) := by
  have hz' : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ⟨Ioc_subset_Icc_self hz.1, Ioc_subset_Icc_self hz.2⟩
  have hy : 0 < z.2 := hz.2.1
  have h1 : 0 ≤ 1 - z.2 := by linarith [hz.2.2]
  have hDa := kDen_pos a hm hs hz
  have hDb := kDen_pos b hm hs hz
  have hDc := kDen_pos c hm hs hz
  have hDd := kDen_pos d hm hs hz
  have hDμ := kDen_pos μ hm hs hz
  have hC := kC_pos' hm hs hz
  have f1 : 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 / kDen m μ s z ≤ 2 := by
    rw [div_le_iff₀ hDμ]
    have hCge := kC_ge (m := m) hs hz'
    have : (1 - z.2) * μ ^ 2 ≥ 0 := mul_nonneg h1 (sq_nonneg _)
    have hle : z.2 ^ 2 * m ^ 2 ≤ kDen m μ s z := by unfold kDen; linarith
    have : 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 ≤ 2 * (z.2 ^ 2 * m ^ 2) := by
      have : 0 ≤ z.2 ^ 2 * m ^ 2 * z.2 := by positivity
      nlinarith
    linarith
  have f2 : ∀ M : ℝ, kC m s z / kDen m M s z ≤ 1 := fun M => by
    rw [div_le_one (kDen_pos M hm hs hz)]
    have : (1 - z.2) * M ^ 2 ≥ 0 := mul_nonneg h1 (sq_nonneg _)
    unfold kDen; linarith
  have f3 := one_sub_div_kDen_le ha hm hs hz
  have f4 := one_sub_div_kDen_le hb hm hs hz
  rw [kern5_eq_mul]
  have g1 : 0 ≤ 2 * z.2 ^ 2 * (1 - z.2) * m ^ 2 / kDen m μ s z := by positivity
  have g2 : 0 ≤ kC m s z / kDen m d s z := by positivity
  have g2' : 0 ≤ kC m s z / kDen m c s z := by positivity
  have g3 : 0 ≤ (1 - z.2) / kDen m a s z := by positivity
  have g4 : 0 ≤ (1 - z.2) / kDen m b s z := by positivity
  have f2d := f2 d
  have f2c := f2 c
  calc _ ≤ 2 * 1 * 1 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ := by gcongr
    _ = 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹) := by ring

end Bounds

theorem measurable_kern5 (m a b c d μ s : ℝ) : Measurable (kern5 m a b c d μ s) := by
  unfold kern5 kDen kC
  fun_prop

theorem integrable_kern5 {m a b c d μ s : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (hs : 0 ≤ s) : Integrable (kern5 m a b c d μ s) feynmanMeasure := by
  refine Integrable.mono' (integrable_const (2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹)))
    (measurable_kern5 m a b c d μ s).aestronglyMeasurable ?_
  filter_upwards [ae_feynmanMeasure] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (kern5_nonneg hm hs hz)]
  exact kern5_le ha hb hm hs hz

/-- **The integrated partial-fraction combination.** -/
theorem sum_mul_integral_pauliIntegrand_eq_kern5 {m a b c d μ s : ℝ} (hm : 0 < m) (hs : 0 ≤ s)
    (hab : a ^ 2 ≠ b ^ 2) (hac : a ^ 2 ≠ c ^ 2) (had : a ^ 2 ≠ d ^ 2) (haμ : a ^ 2 ≠ μ ^ 2)
    (hbc : b ^ 2 ≠ c ^ 2) (hbd : b ^ 2 ≠ d ^ 2) (hbμ : b ^ 2 ≠ μ ^ 2) (hcd : c ^ 2 ≠ d ^ 2)
    (hcμ : c ^ 2 ≠ μ ^ 2) (hdμ : d ^ 2 ≠ μ ^ 2) :
    -((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2) * (μ ^ 2 - b ^ 2))⁻¹ * (b ^ 2) ^ 2 *
          ∫ z, pauliIntegrand m (a, b, s) z ∂feynmanMeasure +
        -((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2) * (μ ^ 2 - c ^ 2))⁻¹ * (c ^ 2) ^ 2 *
          ∫ z, pauliIntegrand m (a, c, s) z ∂feynmanMeasure +
        -((a ^ 2 - d ^ 2) * (b ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2) * (μ ^ 2 - d ^ 2))⁻¹ * (d ^ 2) ^ 2 *
          ∫ z, pauliIntegrand m (a, d, s) z ∂feynmanMeasure +
        -((a ^ 2 - μ ^ 2) * (b ^ 2 - μ ^ 2) * (c ^ 2 - μ ^ 2) * (d ^ 2 - μ ^ 2))⁻¹ * (μ ^ 2) ^ 2 *
          ∫ z, pauliIntegrand m (a, μ, s) z ∂feynmanMeasure =
      ∫ z, kern5 m a b c d μ s z ∂feynmanMeasure := by
  set κb := -((a ^ 2 - b ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2) * (μ ^ 2 - b ^ 2))⁻¹ *
    (b ^ 2) ^ 2
  set κc := -((a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) * (d ^ 2 - c ^ 2) * (μ ^ 2 - c ^ 2))⁻¹ *
    (c ^ 2) ^ 2
  set κd := -((a ^ 2 - d ^ 2) * (b ^ 2 - d ^ 2) * (c ^ 2 - d ^ 2) * (μ ^ 2 - d ^ 2))⁻¹ *
    (d ^ 2) ^ 2
  set κμ := -((a ^ 2 - μ ^ 2) * (b ^ 2 - μ ^ 2) * (c ^ 2 - μ ^ 2) * (d ^ 2 - μ ^ 2))⁻¹ *
    (μ ^ 2) ^ 2
  have h : ∫ z, kern5 m a b c d μ s z ∂feynmanMeasure = ∫ z,
      ((κb * pauliIntegrand m (a, b, s) z + κc * pauliIntegrand m (a, c, s) z) +
        κd * pauliIntegrand m (a, d, s) z) + κμ * pauliIntegrand m (a, μ, s) z
        ∂feynmanMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [ae_feynmanMeasure] with z hz
    exact (sum_mul_pauliIntegrand_eq_kern5 (kDen_pos a hm hs hz).ne' (kDen_pos b hm hs hz).ne'
      (kDen_pos c hm hs hz).ne' (kDen_pos d hm hs hz).ne' (kDen_pos μ hm hs hz).ne' hab hac had
      haμ hbc hbd hbμ hcd hcμ hdμ).symm
  have i1 : Integrable (fun z => κb * pauliIntegrand m (a, b, s) z) feynmanMeasure :=
    (integrable_pauliIntegrand hm hs).const_mul _
  have i2 : Integrable (fun z => κc * pauliIntegrand m (a, c, s) z) feynmanMeasure :=
    (integrable_pauliIntegrand hm hs).const_mul _
  have i3 : Integrable (fun z => κd * pauliIntegrand m (a, d, s) z) feynmanMeasure :=
    (integrable_pauliIntegrand hm hs).const_mul _
  have i4 : Integrable (fun z => κμ * pauliIntegrand m (a, μ, s) z) feynmanMeasure :=
    (integrable_pauliIntegrand hm hs).const_mul _
  have i12 : Integrable (fun z => κb * pauliIntegrand m (a, b, s) z +
      κc * pauliIntegrand m (a, c, s) z) feynmanMeasure := i1.add i2
  have i123 : Integrable (fun z => κb * pauliIntegrand m (a, b, s) z +
      κc * pauliIntegrand m (a, c, s) z + κd * pauliIntegrand m (a, d, s) z) feynmanMeasure :=
    i12.add i3
  rw [h, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-! ### Limits -/

/-- **`(c, d) → (a, b)`**: the five-mass kernel tends to the spectral-component kernel, in
integral. -/
theorem tendsto_integral_kern5 {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {m a b μ s : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hs : 0 ≤ s) (c d : ι → ℝ)
    (hc : Tendsto c l (𝓝 a)) (hd : Tendsto d l (𝓝 b)) :
    Tendsto (fun t => ∫ z, kern5 m a b (c t) (d t) μ s z ∂feynmanMeasure) l
      (𝓝 (∫ z, kernVP m a b μ s z ∂feynmanMeasure)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))
    (Eventually.of_forall fun t => (measurable_kern5 m a b _ _ μ s).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_) (integrable_const _) ?_
  · filter_upwards [ae_feynmanMeasure] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (kern5_nonneg hm hs hz)]
    exact kern5_le ha hb hm hs hz
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hDa := kDen_pos a hm hs hz
    have hDb := kDen_pos b hm hs hz
    have hDμ := kDen_pos μ hm hs hz
    have hcd : Tendsto (fun t => kDen m (c t) s z * kDen m (d t) s z) l
        (𝓝 (kDen m a s z * kDen m b s z)) :=
      (((continuousAt_kDen_mass m s z).tendsto a).comp hc).mul
        (((continuousAt_kDen_mass m s z).tendsto b).comp hd)
    have hden : Tendsto (fun t => kDen m a s z * kDen m b s z * kDen m (c t) s z *
        kDen m (d t) s z * kDen m μ s z) l
        (𝓝 (kDen m a s z * kDen m b s z * kDen m a s z * kDen m b s z * kDen m μ s z)) := by
      have := (hcd.const_mul (kDen m a s z * kDen m b s z)).mul_const (kDen m μ s z)
      simpa only [mul_assoc] using this
    have hne : kDen m a s z * kDen m b s z * kDen m a s z * kDen m b s z * kDen m μ s z ≠ 0 := by
      positivity
    simp only [kernVP, kern5]
    exact tendsto_const_nhds.div hden hne

/-- **`s → 0⁺`**: continuity of the integrated spectral-component kernel at `s = 0` from the
right. -/
theorem tendsto_integral_kernVP_zero {m a b μ : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) :
    Tendsto (fun s => ∫ z, kernVP m a b μ s z ∂feynmanMeasure) (𝓝[≥] 0)
      (𝓝 (∫ z, kernVP m a b μ 0 z ∂feynmanMeasure)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))
    (Eventually.of_forall fun s => (measurable_kern5 m a b a b μ s).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
    filter_upwards [ae_feynmanMeasure] with z hz
    rw [Real.norm_eq_abs, kernVP, abs_of_nonneg (kern5_nonneg hm hs hz)]
    exact kern5_le ha hb hm hs hz
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hc : Continuous fun s => kC m s z := by unfold kC; fun_prop
    have hD : ∀ M, Continuous fun s => kDen m M s z := fun M => by unfold kDen; fun_prop
    have hne : kDen m a 0 z * kDen m b 0 z * kDen m a 0 z * kDen m b 0 z * kDen m μ 0 z ≠ 0 := by
      have := kDen_pos a hm le_rfl hz
      have := kDen_pos b hm le_rfl hz
      have := kDen_pos μ hm le_rfl hz
      positivity
    have hcont : ContinuousAt (fun s => kernVP m a b μ s z) 0 := by
      simp only [kernVP, kern5]
      exact ((continuous_const.mul (hc.pow 2)).mul continuous_const).continuousAt.div
        (((((hD a).mul (hD b)).mul (hD a)).mul (hD b)).mul (hD μ)).continuousAt hne
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- **`s → 0⁺` with five masses**: continuity of the integrated five-mass kernel at `s = 0` from
the right. -/
theorem tendsto_integral_kern5_zero {m a b c d μ : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) :
    Tendsto (fun s => ∫ z, kern5 m a b c d μ s z ∂feynmanMeasure) (𝓝[≥] 0)
      (𝓝 (∫ z, kern5 m a b c d μ 0 z ∂feynmanMeasure)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))
    (Eventually.of_forall fun s => (measurable_kern5 m a b c d μ s).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
    filter_upwards [ae_feynmanMeasure] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (kern5_nonneg hm hs hz)]
    exact kern5_le ha hb hm hs hz
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hc : Continuous fun s => kC m s z := by unfold kC; fun_prop
    have hD : ∀ M, Continuous fun s => kDen m M s z := fun M => by unfold kDen; fun_prop
    have hne : kDen m a 0 z * kDen m b 0 z * kDen m c 0 z * kDen m d 0 z * kDen m μ 0 z ≠ 0 := by
      have := kDen_pos a hm le_rfl hz
      have := kDen_pos b hm le_rfl hz
      have := kDen_pos c hm le_rfl hz
      have := kDen_pos d hm le_rfl hz
      have := kDen_pos μ hm le_rfl hz
      positivity
    have hcont : ContinuousAt (fun s => kern5 m a b c d μ s z) 0 := by
      simp only [kern5]
      exact ((continuous_const.mul (hc.pow 2)).mul continuous_const).continuousAt.div
        (((((hD a).mul (hD b)).mul (hD c)).mul (hD d)).mul (hD μ)).continuousAt hne
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-! ### At `m = 1`, `s = 0`: the outer integrand -/

/-- The spectral-component kernel at `q² = 0`, `m = 1`, as a function of `y`. -/
noncomputable def kernVPOne (a b μ y : ℝ) : ℝ :=
  2 * y ^ 6 * (1 - y) ^ 3 /
    (((1 - y) * a ^ 2 + y ^ 2) ^ 2 * ((1 - y) * b ^ 2 + y ^ 2) ^ 2 * ((1 - y) * μ ^ 2 + y ^ 2))

theorem kernVP_one_zero (a b μ : ℝ) (z : ℝ × ℝ) : kernVP 1 a b μ 0 z = kernVPOne a b μ z.2 := by
  simp only [kernVP, kern5, kDen, kC, kernVPOne]
  ring

theorem integral_kernVP_one_zero (a b μ : ℝ) :
    ∫ z, kernVP 1 a b μ 0 z ∂feynmanMeasure = ∫ y in (0 : ℝ)..1, kernVPOne a b μ y := by
  simp_rw [kernVP_one_zero]
  unfold QED.Integration.feynmanMeasure
  rw [integral_fun_snd (f := fun y => kernVPOne a b μ y)]
  have h1 : (volume.restrict (Ioc (0 : ℝ) 1)).real univ = 1 := by
    simp [Measure.real]
  rw [h1, one_smul, ← intervalIntegral.integral_of_le zero_le_one]

/-- **The spectral-component kernel at `q² = 0` is the outer integrand**: for `0 < y < 1` and
all `a, b, μ`, `(b² - a²)² kernVPOne a b μ y = 2 regKernel μ² a² b² y`, the outer integrand of
the photon function `s (1/(s + a²) - 1/(s + b²))² · s/(s + μ²)`
(`QED.TwoLoop.UnitVPLink.regKernel_eq_photon`). -/
theorem kernVPOne_mul {a b μ y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (b ^ 2 - a ^ 2) ^ 2 * kernVPOne a b μ y =
      2 * QED.TwoLoop.VPUnit.regKernel (μ ^ 2) (a ^ 2) (b ^ 2) y := by
  obtain ⟨hy0, hy1⟩ := hy
  have h1' : 0 < 1 - y := by linarith
  have hA : (1 - y) * a ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hB : (1 - y) * b ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hM : (1 - y) * μ ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hA' : y ^ 2 + (1 - y) * a ^ 2 ≠ 0 := by positivity
  have hB' : y ^ 2 + (1 - y) * b ^ 2 ≠ 0 := by positivity
  have hM' : y ^ 2 + (1 - y) * μ ^ 2 ≠ 0 := by positivity
  simp only [kernVPOne, QED.TwoLoop.VPUnit.regKernel, QED.TwoLoop.VPUnit.f2Kernel]
  field_simp
  ring

/-- **The integrated kernel at `q² = 0`, `m = 1`**:
`(b² - a²)² ∫ kernVP 1 a b μ 0 = 2 ∫₀¹ regKernel μ² a² b²`. -/
theorem integral_kernVP_one_zero_mul (a b μ : ℝ) :
    (b ^ 2 - a ^ 2) ^ 2 * ∫ z, kernVP 1 a b μ 0 z ∂feynmanMeasure =
      2 * ∫ y in (0 : ℝ)..1, QED.TwoLoop.VPUnit.regKernel (μ ^ 2) (a ^ 2) (b ^ 2) y := by
  rw [integral_kernVP_one_zero, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 1 := by simp [ae_iff, measure_singleton]
  filter_upwards [hne] with y hy hy01
  rw [uIoc_of_le zero_le_one] at hy01
  exact kernVPOne_mul ⟨hy01.1, lt_of_le_of_ne hy01.2 hy⟩

end QED.TwoLoop.VPHalf

end
